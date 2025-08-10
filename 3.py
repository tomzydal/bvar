import hashlib
import os
import sys
import json
import base58
import multiprocessing
import time
import math
import random
import argparse
from typing import List, Dict, Any, Optional, Tuple
from queue import Empty
import struct

from Crypto.Hash import keccak, RIPEMD160
from coincurve.keys import PrivateKey

try:
    from tqdm import tqdm
except ImportError:
    print("WARNING: 'tqdm' library not found. Progress bars will not be displayed.")
    def tqdm(iterable, *args, **kwargs): return iterable

# --- Constants & Configuration ---
C_GREEN, C_RESET, C_YELLOW, C_BLUE = '\033[92m', '\033[0m', '\033[93m', '\033[94m'
SECP256K1_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
DISPLAY_SIZE = 100000
CPU_USAGE_LIMIT = 0.8  # Default CPU usage limit (80%)
AUTO_MODE_DELAY = 1.0  # Default delay in seconds for auto-hunt modes
HUNT_BATCH_SIZE = 1000 # Number of keys for each worker to process in a batch

# --- Bitcoin Puzzle Data ---
# Programmatically generate puzzles from #71 to #160
PUZZLES = {
    str(i): {
        'name': f"Bitcoin Puzzle #{i}",
        'start': 2**(i-1),
        'end': 2**i - 1,
        'ctype': 'bitcoin_legacy'
    } for i in range(71, 161)
}

# --- Bech32 Implementation ---
BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
def bech32_polymod(values: List[int]) -> int:
    generator = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for value in values:
        top = chk >> 25
        chk = (chk & 0x1ffffff) << 5 ^ value
        for i in range(5):
            chk ^= generator[i] if ((top >> i) & 1) else 0
    return chk

def bech32_hrp_expand(hrp: str) -> List[int]:
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def bech32_create_checksum(hrp: str, data: List[int]) -> List[int]:
    values = bech32_hrp_expand(hrp) + data
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ 1
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]

def bech32_encode(hrp: str, data: List[int]) -> str:
    combined = data + bech32_create_checksum(hrp, data)
    return hrp + '1' + ''.join([BECH32_CHARSET[d] for d in combined])

def convertbits(data: bytes, frombits: int, tobits: int, pad: bool = True) -> List[int]:
    acc, bits, ret, maxv = 0, 0, [], (1 << tobits) - 1
    for value in data:
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad and bits:
        ret.append((acc << (tobits - bits)) & maxv)
    return ret

# --- Address Derivation and Reconstruction ---
def get_pkh_from_pk(pk_bytes: bytes, compressed: bool) -> bytes:
    """Gets the Public Key Hash (PKH) from a private key."""
    private_key = PrivateKey(pk_bytes)
    public_key_bytes = private_key.public_key.format(compressed=compressed)
    return RIPEMD160.new(hashlib.sha256(public_key_bytes).digest()).digest()

def pkh_to_p2pkh(pkh: bytes) -> str:
    """Converts a PKH to a P2PKH (legacy) address."""
    versioned = b'\x00' + pkh
    checksum = hashlib.sha256(hashlib.sha256(versioned).digest()).digest()[:4]
    return base58.b58encode(versioned + checksum).decode('utf-8')

def pkh_to_p2wpkh(pkh: bytes) -> str:
    """Converts a PKH to a P2WPKH (native SegWit) address."""
    return bech32_encode('bc', [0x00] + convertbits(pkh, 8, 5))

def pkh_to_p2sh_p2wpkh(pkh: bytes) -> str:
    """Converts a PKH to a P2SH-P2WPKH (wrapped SegWit) address."""
    redeem_script = b'\x00\x14' + pkh
    script_hash = RIPEMD160.new(hashlib.sha256(redeem_script).digest()).digest()
    versioned = b'\x05' + script_hash
    checksum = hashlib.sha256(hashlib.sha256(versioned).digest()).digest()[:4]
    return base58.b58encode(versioned + checksum).decode('utf-8')

def binary_to_eth_addr(blob: bytes) -> str:
    """Converts a raw hash to a checksummed Ethereum address."""
    addr_hex = blob.hex()
    cs_hash = keccak.new(digest_bits=256, data=addr_hex.encode('utf-8')).hexdigest()
    return "0x" + "".join(c.upper() if int(cs_hash[i], 16) >= 8 else c for i, c in enumerate(addr_hex))

def derive_ethereum_address(pk_bytes: bytes) -> str:
    """Derives an Ethereum address from a private key."""
    uncompressed_pub = PrivateKey(pk_bytes).public_key.format(compressed=False)[1:]
    addr_hash = keccak.new(digest_bits=256, data=uncompressed_pub).digest()[-20:]
    return binary_to_eth_addr(addr_hash)

DERIVATION_FUNCS = {
    'bitcoin_legacy': lambda pk: pkh_to_p2pkh(get_pkh_from_pk(pk, compressed=False)),
    'bitcoin_segwit': lambda pk: pkh_to_p2wpkh(get_pkh_from_pk(pk, compressed=True)),
    'bitcoin_segwit_p2sh': lambda pk: pkh_to_p2sh_p2wpkh(get_pkh_from_pk(pk, compressed=True)),
    'ethereum': derive_ethereum_address,
}

# --- Core System Setup and Utilities ---
def load_watchlist(filename="hunt/watchlist.txt"):
    hunt_dir = os.path.dirname(filename)
    if hunt_dir and not os.path.exists(hunt_dir):
        os.makedirs(hunt_dir)
    if not os.path.exists(filename):
        print(f"{C_YELLOW}INFO: No `{filename}` found. To hunt for specific addresses, create one.{C_RESET}")
        return set()
    with open(filename, 'r') as f:
        addresses = {line.strip().lower() for line in f if line.strip()}
    print(f"Loaded {len(addresses)} addresses from `{filename}`.")
    return addresses

def save_found_key(lock, address, pk_hex, filename="found.txt"):
    with lock:
        with open(filename, 'a') as f:
            f.write(f"Address: {address}\nPrivate Key: {pk_hex}\n\n")

def check_and_save(watchlist, lock, address, pk_hex):
    if address.lower() in watchlist:
        print(f"\n{C_GREEN}>> HIT FOUND! << Address: {address}{C_RESET}")
        save_found_key(lock, address, pk_hex)
        return True
    return False

# --- High-Performance Hunting ---
def _hunt_worker(task_id, start, end, c_type, watchlist, lock, stop_event, progress_counter, found_flag):
    """Worker process for hunting keys in a given range, using batch processing."""
    derive_func = DERIVATION_FUNCS[c_type]
    key_iterator = (i for i in range(start, end + 1)) if end is not None else (random.randint(1, SECP256K1_ORDER - 1) for _ in range(start))

    batch = []
    try:
        for pk_int in key_iterator:
            if stop_event.is_set():
                break

            batch.append(pk_int)

            if len(batch) >= HUNT_BATCH_SIZE:
                for key in batch:
                    pk_bytes = key.to_bytes(32, 'big')
                    address_str = derive_func(pk_bytes)
                    if check_and_save(watchlist, lock, address_str, pk_bytes.hex()):
                        found_flag.set()

                with progress_counter.get_lock():
                    progress_counter.value += len(batch)
                batch = []

    except KeyboardInterrupt:
        pass
    finally:
        # Process any remaining keys in the last batch
        if batch:
            for key in batch:
                pk_bytes = key.to_bytes(32, 'big')
                address_str = derive_func(pk_bytes)
                if check_and_save(watchlist, lock, address_str, pk_bytes.hex()):
                    found_flag.set()
            with progress_counter.get_lock():
                progress_counter.value += len(batch)


def start_hunt(total_keys, c_type, tasks, watchlist, lock):
    """
    Manages the multiprocessing hunt for a given set of key ranges or random keys.
    """
    num_procs = len(tasks)
    print(f"Starting hunt with {num_procs} cores...")

    manager = multiprocessing.Manager()
    stop_event = manager.Event()
    found_flag = manager.Event()
    progress_counter = manager.Value('L', 0)

    pool = multiprocessing.Pool(processes=num_procs)

    try:
        full_tasks = [(i,) + task_params + (c_type, watchlist, lock, stop_event, progress_counter, found_flag) for i, task_params in enumerate(tasks)]

        pbar = tqdm(total=total_keys, desc=f"Hunting {c_type.replace('_',' ')}", unit="key")
        result = pool.starmap_async(_hunt_worker, full_tasks)

        while not result.ready():
            pbar.n = progress_counter.value
            pbar.refresh()
            time.sleep(0.5)
            if found_flag.is_set(): pass

        pbar.n = progress_counter.value
        pbar.refresh()
        pbar.close()

    except KeyboardInterrupt:
        print(f"\n{C_YELLOW}Keyboard interrupt detected. Stopping workers...{C_RESET}")
        stop_event.set()
    finally:
        pool.close()
        pool.join()

    print(f"\nFinished hunting.")


# --- UI Features & Smart Hunt ---
def display_page_map(current_page, total_pages, map_width=80, map_height=1, hunt_range=None):
    header = f" PUZZLE #{hunt_range['puzzle_key']} KEY SPACE MAP " if hunt_range else " SECP256k1 KEY SPACE MAP "
    print("\n" + header.center(map_width + 2, "="))
    if total_pages == 0: return
    total_cells = map_width * map_height
    if total_cells == 0: return
    pages_per_cell = total_pages / total_cells
    if pages_per_cell == 0: return
    current_cell_abs = int((current_page - 1) / pages_per_cell)
    current_y = min(map_height - 1, int(current_cell_abs / map_width))
    current_x = min(map_width - 1, int(current_cell_abs % map_width))
    map_grid = [['.' for _ in range(map_width)] for _ in range(map_height)]
    if 0 <= current_y < map_height and 0 <= current_x < map_width:
        map_grid[current_y][current_x] = f'{C_GREEN}@{C_RESET}'
    for row in map_grid: print(" " + "".join(row) + " ")
    progress_percent = (current_page / total_pages) * 100
    stats_line = f" Page {current_page:,} of {total_pages:,} ({progress_percent:.8f}%) "
    print(stats_line.center(map_width + 2, "="))

def browse_virtual_keys(c_type, watchlist, lock, hunt_range: Optional[Dict] = None, start_page: Optional[int] = None, conceptual_page_size: Optional[int] = None):
    title_ctype = hunt_range['name'] if hunt_range else c_type.upper().replace('_', ' ')
    print(f"\n--- Browsing Virtual Keys for: {title_ctype} (Sorted by Address) ---")
    derive_func = DERIVATION_FUNCS[c_type]

    if conceptual_page_size is None:
        try:
            page_size_str = input(f"Enter Page Size (e.g., 10000, press Enter for {DISPLAY_SIZE}): ").strip()
            conceptual_page_size = int(page_size_str) if page_size_str and page_size_str.isdigit() else DISPLAY_SIZE
        except ValueError: conceptual_page_size = DISPLAY_SIZE

    if hunt_range:
        key_space_start, key_space_end = hunt_range['start'], hunt_range['end']
    else:
        key_space_start, key_space_end = 1, SECP256K1_ORDER - 1

    total_conceptual_pages, total_views_per_page = 0, 0

    def recalculate_pages():
        nonlocal total_conceptual_pages, total_views_per_page
        key_space_size = key_space_end - key_space_start + 1
        total_conceptual_pages = math.ceil(key_space_size / conceptual_page_size)
        total_views_per_page = math.ceil(conceptual_page_size / DISPLAY_SIZE)

    recalculate_pages()
    page = start_page if start_page is not None else 1
    view = 0

    def display_current_view(current_page, current_view):
        start_offset = (current_page - 1) * conceptual_page_size
        start_of_page = key_space_start + start_offset
        start_of_view = start_of_page + (current_view * DISPLAY_SIZE)
        end_of_view = min(start_of_view + DISPLAY_SIZE - 1, key_space_end, start_of_page + conceptual_page_size - 1)
        print(f"\n--- Displaying Keys (Page {current_page:,}, View {current_view+1}/{total_views_per_page}) ---")
        print(f"--- Keys from {start_of_view:x} to {end_of_view:x} ---")
        print("Generating and sorting view... this may take a moment.")
        view_data = []
        for i in tqdm(range(start_of_view, end_of_view + 1), desc="Generating keys for view", leave=False):
            pk_bytes = i.to_bytes(32, 'big')
            address = derive_func(pk_bytes)
            view_data.append({'pk_hex': pk_bytes.hex(), 'addr': address})
        view_data.sort(key=lambda x: x['addr'])
        for item in view_data:
            address, pk_hex = item['addr'], item['pk_hex']
            output = f"  Addr: {address} | PK: {pk_hex}"
            if check_and_save(watchlist, lock, address, pk_hex):
                print(C_GREEN + output + C_RESET)
            else: print(output)

    def run_auto_scroll(start_page, start_view):
        nonlocal page, view
        page, view = start_page, start_view
        try:
            while True:
                display_current_view(page, view)
                display_page_map(page, total_conceptual_pages, hunt_range=hunt_range)
                time.sleep(AUTO_MODE_DELAY)
                view += 1
                if view >= total_views_per_page: page += 1; view = 0
                if page > total_conceptual_pages: print("\nEnd of key space reached."); break
        except KeyboardInterrupt: print(f"\n{C_YELLOW}Auto-scroll stopped.{C_RESET}")

    while True:
        print(f"{C_YELLOW}Using Page Size of {conceptual_page_size:,} keys.{C_RESET}")
        display_current_view(page, view)
        display_page_map(page, total_conceptual_pages, hunt_range=hunt_range)
        print("\n--- Navigation & Hunting ---")
        print(f" < >: View  |  N/P: Page  |  G: Goto Page  |  S: Set Page Size | R: Random Page")
        print(f" J: Jump PK | A: Auto-Hunt | ++C: Scroll | ++S: Scroll from PK | Q: Quit")
        action = input("Action: ").lower()
        if action == '>': view += 1
        elif action == '<': view -= 1
        elif action == 'n': page += 1; view = 0
        elif action == 'p': page = max(1, page - 1); view = 0
        elif action == 'g':
            try: page = max(1, min(total_conceptual_pages, int(input("Goto Page: ")))); view = 0
            except: print("Invalid number.")
        elif action == 's':
            try:
                # Store the starting key of the current page before we change the size
                start_offset = (page - 1) * conceptual_page_size
                start_of_current_page = key_space_start + start_offset

                new_size_str = input(f"Enter New Page Size (current: {conceptual_page_size:,}): ").strip()
                new_size = int(new_size_str)
                if new_size > 0:
                    conceptual_page_size = new_size
                    recalculate_pages() # Recalculate total pages based on new size

                    # Calculate the new page number that contains the old starting key
                    new_offset = start_of_current_page - key_space_start
                    page = (new_offset // conceptual_page_size) + 1
                    view = 0 # Reset view to the start of the new page's first view

                    # Add a clarification message for the user
                    if conceptual_page_size > DISPLAY_SIZE:
                        print(f"{C_YELLOW}Page size set. Note: Each page now has multiple 'views'. Use < and > to navigate them.{C_RESET}")

                else:
                    print(f"{C_YELLOW}Page size must be positive.{C_RESET}")
            except ValueError:
                print(f"{C_YELLOW}Invalid number.{C_RESET}")
        elif action == 'r': page = random.randint(1, total_conceptual_pages); view = 0
        elif action == 'a':
            print(f"\n{C_YELLOW}Entering random auto-hunt mode. Press CTRL+C to stop.{C_RESET}")
            try:
                while True:
                    rand_key = random.randint(key_space_start, key_space_end)
                    pk_bytes = rand_key.to_bytes(32,'big')
                    address = derive_func(pk_bytes)
                    print(f"\r{C_YELLOW}Hunting random key {rand_key:x} -> {address}{C_RESET}", end="")
                    if check_and_save(watchlist, lock, address, pk_bytes.hex()):
                        print(f"\r{C_GREEN}HIT! Address: {address} | Key: {pk_bytes.hex()}{C_RESET}")
                    time.sleep(AUTO_MODE_DELAY)
            except KeyboardInterrupt: print(f"\n{C_YELLOW}Auto-hunt stopped.{C_RESET}")
        elif action == '++c':
            print(f"\n{C_YELLOW}Entering auto-scroll mode. Press CTRL+C to stop.{C_RESET}")
            run_auto_scroll(page, view)
        elif action == '++s' or action == 'j':
            prompt_text = "Enter starting PK (hex)" if action == '++s' else "Jump to PK (dec or 0x... hex)"
            try:
                pk_str = input(f"{prompt_text} within range: ")
                pk_int = int(pk_str, 16) if '0x' in pk_str.lower() or len(pk_str) == 64 else int(pk_str)
                if not (key_space_start <= pk_int <= key_space_end):
                    print(f"{C_YELLOW}Key is outside the current hunting range.{C_RESET}"); continue
                offset = pk_int - key_space_start
                jump_page = offset // conceptual_page_size + 1
                jump_view = (offset % conceptual_page_size) // DISPLAY_SIZE
                if action == '++s':
                    print(f"\n{C_YELLOW}Starting auto-scroll from key. Press CTRL+C to stop.{C_RESET}")
                    run_auto_scroll(jump_page, jump_view)
                else:
                    page, view = jump_page, jump_view
            except (ValueError, TypeError): print(f"{C_YELLOW}Invalid key format.{C_RESET}")
        elif action == 'q': break
        if view >= total_views_per_page: page += 1; view = 0
        if view < 0: page = max(1, page - 1); view = total_views_per_page - 1
        page = max(1, min(total_conceptual_pages, page))

def _page_sampler(page_num, conceptual_page_size, key_space_start, c_type, watchlist):
    """Worker function for the Smart Hunt mode."""
    derive_func = DERIVATION_FUNCS[c_type]
    hit_count = 0
    start_offset = (page_num - 1) * conceptual_page_size
    start_of_page = key_space_start + start_offset
    end_of_page = start_of_page + conceptual_page_size
    for i in range(start_of_page, end_of_page):
        address = derive_func(i.to_bytes(32, 'big'))
        if address.lower() in watchlist:
            hit_count += 1
    return (page_num, hit_count)

def smart_hunt(c_type, watchlist, lock, hunt_range: Optional[Dict] = None):
    """Launches the Smart Hunt reconnaissance mode."""
    print(f"\n--- {C_BLUE}Smart Hunt Reconnaissance Mode{C_RESET} ---")
    title_ctype = hunt_range['name'] if hunt_range else c_type.upper().replace('_', ' ')
    try:
        page_size_str = input(f"Enter Page Size for sampling (e.g., 10000, press Enter for {DISPLAY_SIZE}): ").strip()
        conceptual_page_size = int(page_size_str) if page_size_str and page_size_str.isdigit() else DISPLAY_SIZE
        num_samples = int(input("How many random pages to sample in parallel? (e.g., 12): "))
        if num_samples <= 0: return None
    except (ValueError, TypeError):
        print(f"{C_YELLOW}Invalid number.{C_RESET}"); return None

    if hunt_range:
        key_space_start, key_space_end = hunt_range['start'], hunt_range['end']
    else:
        key_space_start, key_space_end = 1, SECP256K1_ORDER - 1
    key_space_size = key_space_end - key_space_start + 1
    total_conceptual_pages = math.ceil(key_space_size / conceptual_page_size)

    print(f"Scanning {num_samples} random pages for {title_ctype}...")

    random_pages = set()
    with tqdm(total=num_samples, desc="Generating Random Pages") as pbar:
        while len(random_pages) < min(num_samples, total_conceptual_pages):
            page_num = random.randint(1, total_conceptual_pages)
            if page_num not in random_pages:
                random_pages.add(page_num)
                pbar.update(1)

    tasks = [(p, conceptual_page_size, key_space_start, c_type, watchlist) for p in random_pages]

    results = []
    num_procs = max(1, int(math.ceil(multiprocessing.cpu_count() * CPU_USAGE_LIMIT)))
    with multiprocessing.Pool(processes=num_procs) as pool:
        with tqdm(total=len(tasks), desc="Sampling Pages") as pbar:
            for result in pool.starmap(_page_sampler, tasks):
                results.append(result)
                pbar.update(1)

    hot_pages = sorted([res for res in results if res[1] > 0], key=lambda x: x[1], reverse=True)

    if not hot_pages:
        print(f"\n{C_YELLOW}Reconnaissance complete. No watchlist hits found in the sampled pages.{C_RESET}")
        return None

    print(f"\n{C_GREEN}--- Hot Pages Found! ---{C_RESET}")
    for page_num, hits in hot_pages:
        print(f"  - Page {page_num:,} contained {C_GREEN}{hits}{C_RESET} address(es) from your watchlist.")

    try:
        if input(f"\nJump to the hottest page ({hot_pages[0][0]:,}) for exploration? (y/n): ").lower() == 'y':
            return hot_pages[0][0], conceptual_page_size
    except (ValueError, IndexError): pass
    return None

# --- CLI Handlers ---
def get_tasks_for_range(start, end, num_procs):
    total = end - start + 1
    if num_procs == 1 or total < num_procs: return [(start, end)]
    chunk = total // num_procs
    tasks, current = [], start
    for i in range(num_procs):
        r_end = current + chunk - 1 if i < num_procs - 1 else end
        if current <= r_end: tasks.append((current, r_end)); current = r_end + 1
    return tasks

def get_tasks_for_random(total, num_procs):
    if num_procs == 1 or total < num_procs: return [(total, None)]
    chunk = total // num_procs
    tasks = [(chunk, None)] * (num_procs - 1)
    tasks.append((total - chunk * (num_procs - 1), None))
    return tasks

def run_cli():
    """The main interactive command-line interface menu."""
    if os.name == 'nt': os.system('')
    print("\n" + "="*6 + " Universal Crypto Hunter (v15.3 - ArgParse) " + "="*6)

    watchlist, lock = load_watchlist(), multiprocessing.Manager().Lock()

    def select_puzzle_and_get_range() -> Optional[Dict]:
        print("\n--- Bitcoin Puzzle Hunter (Puzzles 71-160) ---")
        puzzle_keys = sorted(PUZZLES.keys(), key=int)
        for key in puzzle_keys: print(f"{key}. {PUZZLES[key]['name']}")
        choice = input("Choose a puzzle to hunt: ")
        puzzle = PUZZLES.get(choice)
        if not puzzle: print(f"{C_YELLOW}Invalid puzzle choice.{C_RESET}"); return None
        puzzle['puzzle_key'] = choice
        print(f"\nSelected: {C_GREEN}{puzzle['name']}{C_RESET}")
        print("1. Start from the beginning\n2. Start from a random point\n3. Start from a specific percentage")
        start_choice = input("Enter choice (1-3): ")
        start_key, end_key = puzzle['start'], puzzle['end']
        if start_choice == '2':
            puzzle['start'] = random.randint(start_key, end_key)
            print(f"Starting at random key: {puzzle['start']:x}")
        elif start_choice == '3':
            try:
                percent = float(input("Enter percentage (0.0 to 100.0): "))
                if not (0.0 <= percent <= 100.0): print(f"{C_YELLOW}Percentage out of range.{C_RESET}"); return None
                puzzle['start'] += int((end_key - start_key) * (percent / 100.0))
                print(f"Starting at {percent}%: key {puzzle['start']:x}")
            except ValueError: print(f"{C_YELLOW}Invalid percentage.{C_RESET}"); return None
        else: print("Starting from the beginning.")
        return puzzle

    def get_currency_type():
        print("\nSelect Address / Currency Type:")
        print("1. Ethereum\n2. Bitcoin (Legacy '1...')")
        print("3. Bitcoin (Native SegWit 'bc1q...')\n4. Bitcoin (Wrapped SegWit '3...')")
        return {'1': 'ethereum', '2': 'bitcoin_legacy', '3': 'bitcoin_segwit', '4': 'bitcoin_segwit_p2sh'}.get(input("Enter choice: "))

    while True:
        print("\n" + "-"*23 + " MAIN MENU " + "-"*23)
        print("--- Interactive Exploration ---")
        print("1. Explore Universal Key Space (SECP256k1)")
        print(f"2. {C_GREEN}Explore Bitcoin Puzzles (71-160){C_RESET}")
        print("\n--- Automated Watchlist Hunting ---")
        print("3. Hunt in a Specific Key Range")
        print(f"4. {C_GREEN}Hunt a Specific Bitcoin Puzzle{C_RESET}")
        print("5. Hunt Random Keys (Full Space)")
        print(f"6. {C_BLUE}Hybrid Hunt (Random Jumps + Sequential Scan){C_RESET}")
        print(f"7. {C_BLUE}Smart Hunt Recon (Find Hot Pages){C_RESET}")
        print("\n--- Utilities ---")
        print("8. Reload Watchlist")
        print("9. Exit")

        choice = input("Enter your choice: ")

        if choice == '9': print("Exiting."); break
        if choice == '8': watchlist = load_watchlist(); continue

        if choice == '1':
            ctype = get_currency_type()
            if ctype: browse_virtual_keys(ctype, watchlist, lock)
        elif choice == '2':
            hunt_range = select_puzzle_and_get_range()
            if hunt_range: browse_virtual_keys(hunt_range['ctype'], watchlist, lock, hunt_range=hunt_range)
        elif choice in ['3', '4', '5', '6', '7']:
            num_procs = max(1, int(math.ceil(multiprocessing.cpu_count() * CPU_USAGE_LIMIT)))

            if choice == '3': # Hunt Range
                ctype = get_currency_type()
                if not ctype: continue
                try:
                    start, end = int(input("Start Key (hex): "), 16), int(input("End Key (hex): "), 16)
                    if not (1 <= start <= end < SECP256K1_ORDER): print("Invalid range."); continue
                    tasks = get_tasks_for_range(start, end, num_procs)
                    if tasks: start_hunt(end - start + 1, ctype, tasks, watchlist, lock)
                except (ValueError, TypeError): print(f"{C_YELLOW}Invalid number entered.{C_RESET}")
            elif choice == '4': # Hunt Puzzle
                hunt_range = select_puzzle_and_get_range()
                if hunt_range:
                    start, end, ctype = hunt_range['start'], hunt_range['end'], hunt_range['ctype']
                    tasks = get_tasks_for_range(start, end, num_procs)
                    if tasks: start_hunt(end - start + 1, ctype, tasks, watchlist, lock)
            elif choice == '5': # Hunt Random
                ctype = get_currency_type()
                if not ctype: continue
                try:
                    num_keys = int(input("How many RANDOM keys to hunt?: "))
                    if num_keys <= 0: continue
                    tasks = get_tasks_for_random(num_keys, num_procs)
                    if tasks: start_hunt(num_keys, ctype, tasks, watchlist, lock)
                except (ValueError, TypeError): print(f"{C_YELLOW}Invalid number entered.{C_RESET}")
            elif choice == '6': # Hybrid Hunt
                ctype = get_currency_type()
                if not ctype: continue
                try:
                    total_to_hunt = int(input("Total keys to hunt in this session: "))
                    scan_block_size = int(input("Sequential scan block size per jump (e.g., 100000): "))
                    if total_to_hunt <= 0 or scan_block_size <= 0: continue

                    hunted_count = 0
                    with tqdm(total=total_to_hunt, desc="Hybrid Hunt Progress", unit="key") as pbar:
                        while hunted_count < total_to_hunt:
                            keys_in_this_run = min(scan_block_size, total_to_hunt - hunted_count)
                            start_key = random.randint(1, SECP256K1_ORDER - keys_in_this_run)
                            end_key = start_key + keys_in_this_run - 1

                            tasks = get_tasks_for_range(start_key, end_key, num_procs)
                            print(f"\n{C_BLUE}Jumping to range {start_key:x} - {end_key:x}{C_RESET}")
                            start_hunt(keys_in_this_run, ctype, tasks, watchlist, lock)

                            hunted_count += keys_in_this_run
                            pbar.update(keys_in_this_run)

                except (ValueError, TypeError): print(f"{C_YELLOW}Invalid number entered.{C_RESET}")
            elif choice == '7': # Smart Hunt
                ctype = get_currency_type()
                if not ctype: continue
                hunt_result = smart_hunt(ctype, watchlist, lock)
                if hunt_result:
                    target_page, page_size = hunt_result
                    print(f"\nJumping to hot page {target_page:,} with page size {page_size:,}...")
                    browse_virtual_keys(ctype, watchlist, lock, start_page=target_page, conceptual_page_size=page_size)
        else:
            print(f"{C_YELLOW}Invalid choice. Please try again.{C_RESET}")

def main():
    """
    Main function to parse command-line arguments and dispatch the correct hunter mode.
    """
    parser = argparse.ArgumentParser(
        description="Universal Crypto Hunter - Explore and hunt for crypto keys.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    # --- Mode Selection ---
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument('--browse', action='store_true', help='Enter interactive browsing mode.')
    mode_group.add_argument('--hunt', action='store_true', help='Start an automated hunt.')

    # --- Target Selection ---
    target_group = parser.add_mutually_exclusive_group(required=False)
    target_group.add_argument('--ctype', type=str, choices=DERIVATION_FUNCS.keys(), help='The currency/address type to target.')
    target_group.add_argument('--puzzle', type=str, choices=PUZZLES.keys(), help='Target a specific Bitcoin puzzle number (71-160).')

    # --- Browsing Options ---
    parser.add_argument('--page', type=int, default=1, help='The page number to start browsing from.')
    parser.add_argument('--pagesize', type=int, default=DISPLAY_SIZE, help='The number of keys per conceptual page.')

    # --- Hunting Options ---
    hunt_type_group = parser.add_mutually_exclusive_group()
    hunt_type_group.add_argument('--range', type=lambda x: int(x, 0), nargs=2, metavar=('START', 'END'), help='The key range to hunt (start and end, decimal or 0x-prefixed hex).')
    hunt_type_group.add_argument('--random', type=int, metavar='N', help='Hunt N random keys from the entire keyspace.')

    args = parser.parse_args()

    # If no specific mode is chosen via args, run the interactive CLI
    if not (args.browse or args.hunt):
        run_cli()
        return

    # --- Setup common variables ---
    watchlist, lock = load_watchlist(), multiprocessing.Manager().Lock()
    ctype = args.ctype
    hunt_range = None

    # --- Handle Puzzle Target ---
    if args.puzzle:
        hunt_range = PUZZLES[args.puzzle]
        hunt_range['puzzle_key'] = args.puzzle
        ctype = hunt_range['ctype']
        print(f"{C_GREEN}Targeting Puzzle: {hunt_range['name']}{C_RESET}")

    if not ctype:
        print(f"{C_YELLOW}Error: A target is required. Use --ctype or --puzzle.{C_RESET}")
        parser.print_help()
        return

    # --- Dispatch to correct function based on mode ---
    if args.browse:
        browse_virtual_keys(
            c_type=ctype,
            watchlist=watchlist,
            lock=lock,
            hunt_range=hunt_range,
            start_page=args.page,
            conceptual_page_size=args.pagesize
        )
    elif args.hunt:
        num_procs = max(1, int(math.ceil(multiprocessing.cpu_count() * CPU_USAGE_LIMIT)))
        tasks = []
        total_keys = 0

        if args.range:
            start, end = args.range
            if not (1 <= start <= end < SECP256K1_ORDER):
                print(f"{C_YELLOW}Error: Invalid key range provided.{C_RESET}")
                return
            tasks = get_tasks_for_range(start, end, num_procs)
            total_keys = end - start + 1
        elif args.random:
            total_keys = args.random
            tasks = get_tasks_for_random(total_keys, num_procs)
        elif hunt_range: # Hunt entire puzzle range
            start, end = hunt_range['start'], hunt_range['end']
            tasks = get_tasks_for_range(start, end, num_procs)
            total_keys = end - start + 1
        else:
            print(f"{C_YELLOW}Error: Hunt mode requires a target range. Use --range, --random, or --puzzle.{C_RESET}")
            return

        if tasks:
            start_hunt(total_keys, ctype, tasks, watchlist, lock)

if __name__ == "__main__":
    multiprocessing.freeze_support()
    main()

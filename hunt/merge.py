input_files = ['watchlist_000001.txt', 'watchlist_000002.txt']
output_file = 'watchlist.txt'

with open(output_file, 'w') as outfile:
    for fname in input_files:
        with open(fname, 'r') as infile:
            outfile.write(infile.read())
            outfile.write('\n')  # Add a newline after each file's content
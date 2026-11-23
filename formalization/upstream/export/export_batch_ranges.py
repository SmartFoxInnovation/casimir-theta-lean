"""Partition the selected declarations in their original export order."""

import argparse
from array import array
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("declarations", type=Path)
    parser.add_argument("bytes_per_batch", type=int)
    args = parser.parse_args()
    if args.bytes_per_batch < 1:
        parser.error("bytes_per_batch must be positive")
    offsets = array("Q")
    offsets.frombytes(args.declarations.read_bytes())
    if not offsets or any(left >= right for left, right in zip(offsets, offsets[1:])):
        raise ValueError("Expected ascending, unique declaration offsets")
    first = offsets[0]
    for offset in offsets:
        if offset - first >= args.bytes_per_batch:
            print(first, offset)
            first = offset
    print(first, offsets[-1] + 1)


if __name__ == "__main__":
    main()

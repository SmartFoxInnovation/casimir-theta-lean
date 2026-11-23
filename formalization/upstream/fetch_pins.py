"""Fetch the source archive and import index required by replay_windows.py."""

import argparse
from pathlib import Path
import shutil
from urllib.request import Request, urlopen

from replay_windows import ARCHIVE_SHA256, INDEX_COMMIT, INDEX_SHA256, SOURCE_COMMIT, digest


INPUTS = (
    ("alpoge-source.tar.gz",
     f"https://codeload.github.com/Deicyde/riemann-hypothesis/tar.gz/{SOURCE_COMMIT}",
     ARCHIVE_SHA256),
    ("modules.jsonl.gz",
     f"https://raw.githubusercontent.com/rohanarun/alpoge-rh-replay/{INDEX_COMMIT}/tracker/modules.jsonl.gz",
     INDEX_SHA256),
)


def fetch(destination, url, expected):
    if destination.is_file():
        if digest(destination) != expected:
            raise ValueError(f"Existing file does not match the pinned digest: {destination}")
        return
    temporary = destination.with_suffix(destination.suffix + ".part")
    request = Request(url, headers={"User-Agent": "RH01-Casimir-replay"})
    try:
        with urlopen(request, timeout=45) as source, temporary.open("wb") as output:
            shutil.copyfileobj(source, output, length=1024 * 1024)
        if digest(temporary) != expected:
            raise ValueError(f"Downloaded file does not match the pinned digest: {destination.name}")
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    for name, url, expected in INPUTS:
        path = args.directory / name
        print(f"Checking {name}", flush=True)
        fetch(path, url, expected)
        print(f"{expected}  {path}", flush=True)


if __name__ == "__main__":
    main()

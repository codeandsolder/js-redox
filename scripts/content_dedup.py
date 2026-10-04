#!/usr/bin/env python3
import hashlib
import os
import shutil
from pathlib import Path


def sha256_path(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def default_jobs(cap: int = 8) -> int:
    return max(1, min(cap, os.cpu_count() or 1))


def link_or_copy(source: Path, dest: Path) -> str:
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists() or dest.is_symlink():
        dest.unlink()
    try:
        os.link(source, dest)
        return "hardlink"
    except OSError:
        shutil.copyfile(source, dest)
        return "copy"


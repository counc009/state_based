#!/usr/bin/env python3
"""Trusted argv adapter for the existing symbolic query interpreter; no shell/globs."""
from pathlib import Path
import subprocess
import sys

REPO = Path(__file__).resolve().parents[2]
if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('Usage: check_query.py QUERY_FILE')
    modules = sorted(str(p) for p in (REPO / 'modules').glob('*.type'))
    if not modules:
        raise SystemExit('No module definitions found')
    raise SystemExit(subprocess.run(['dune','exec','--root',str(REPO),'query-interp','--',
                                     str(Path(sys.argv[1]).resolve()),'--',*modules]).returncode)

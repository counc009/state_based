#!/usr/bin/env python3
"""Import only NL-to-FQL message records, never judge labels or candidate code."""
import argparse
from pathlib import Path
from evaluate import digest, load, write_new


def convert(source):
    rows = [t for t in source['tasks'] if t.get('mode') == 'fql' and t.get('repeat') == 0]
    assert rows, 'No repetition-zero FQL records'
    ids = [t['task_id'] for t in rows]
    assert len(set(ids)) == len(ids), 'Duplicate task'
    return [{'task_id':t['task_id'], 'demonstration_ids':t['demonstration_ids'],
             'messages':t['messages']} for t in rows]


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path, help='Use a *-private.json filename; never overwrite source')
    a = p.parse_args()
    assert a.output.name.endswith('-private.json'), 'Use an ignored private dataset path'
    write_new(a.output, {'tasks':convert(load(a.source)), 'source_sha256':digest(a.source.read_bytes())})
    print('Imported frozen FQL inputs without labels; original unchanged')

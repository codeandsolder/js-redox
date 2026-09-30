#!/usr/bin/env python3
import argparse, json
from collections import Counter
from pathlib import Path

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('jsonl')
    ap.add_argument('--top-score-slack', type=int, default=0)
    args=ap.parse_args()

    for line in Path(args.jsonl).read_text().splitlines():
        if not line.strip():
            continue
        r=json.loads(line)
        votes=Counter()
        weighted=Counter()
        streams=0
        for b in r.get('push_builders', []):
            hints=b.get('width_hints', [])
            if not hints:
                continue
            best=max(h['score'] for h in hints)
            accepted=[h for h in hints if h['score'] >= best-args.top_score_slack]
            # Harmonic-resistant vote: smallest width among equally best candidates.
            chosen=min(accepted, key=lambda h:h['width'])
            votes[chosen['width']]+=1
            weighted[chosen['width']]+=max(1, b.get('arguments',0))
            streams+=1

        name=Path(r['file']).name
        if not votes:
            print(f'{name}: no width consensus')
            continue
        best=min(
            (w for w,c in votes.items() if c==max(votes.values())),
            key=lambda w:(-weighted[w], w),
        )
        print(f'{name}: width={best} streams={streams} votes={dict(sorted(votes.items()))} weighted={dict(sorted(weighted.items()))}')

if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Stage trusted dependencies plus only Entrant artifacts into an empty sealed root."""
import argparse
from pathlib import Path
from artifacts import stage

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--overlay', type=Path, required=True)
    parser.add_argument('--trusted-lib', type=Path, required=True)
    args = parser.parse_args()
    try:
        print(f'staged {stage(args.candidate, args.overlay, args.trusted_lib)} entrant artifacts')
    except (ValueError, OSError) as error:
        parser.exit(1, f'REJECT: {error}\n')

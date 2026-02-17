# SAYCBridge z3b

Minimal checkout of the [SAYCBridge](https://github.com/eseidel/saycbridge) z3b bidding engine, used as a reference implementation by [yarborough](https://github.com/eseidel/yarborough).

## Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install z3-solver==4.12.6.0 networkx
```

## Usage

The `z3b_cli.py` script provides a CLI interface to the z3b bidder:

```bash
# Auto-bid a deal
python z3b_cli.py autobid \
  --dealer N --vulnerability None \
  --north "AK.J.T8753.JT432" \
  --east "Q.KT9876.QJ.AK98" \
  --south "JT9876.A5432.6.7" \
  --west "5432.Q.AK942.Q65"

# Interpret a bidding sequence
python z3b_cli.py interpret \
  --calls "1H,P,2H,P" \
  --dealer N --vulnerability None
```

## Code Layout

- `src/core/` — Basic Python objects for bridge hands, boards, calls
- `src/z3b/` — Z3 Bidder (constraint-based bidder using Z3 theorem prover)
- `src/third_party/` — Custom memoization decorator
- `z3b_cli.py` — CLI entry point for yarborough integration

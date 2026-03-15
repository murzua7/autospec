"""
autospec CLI entry point.

Usage:
    python -m autospec --target ./target/example
    python -m autospec --target /path/to/codebase --model claude-opus-4-20250514 --max-iters 500
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

# Ensure project root is on path
ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from autospec import run_loop


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="autospec",
        description=(
            "Self-supervising TLA+ formal verification loop. "
            "An LLM agent iteratively writes TLA+ specs and fixes code, "
            "using the TLC model checker as a fixed evaluator."
        ),
    )
    parser.add_argument(
        "--target", "-t",
        type=str,
        required=True,
        help="Path to the target codebase to verify",
    )
    parser.add_argument(
        "--model", "-m",
        type=str,
        default=None,
        help="Anthropic model ID for the agent (default: claude-sonnet-4-20250514)",
    )
    parser.add_argument(
        "--max-iters", "-n",
        type=int,
        default=1000,
        help="Maximum number of iterations (default: 1000)",
    )
    parser.add_argument(
        "--tag",
        type=str,
        default="",
        help="Optional tag for the git branch name",
    )
    parser.add_argument(
        "--check",
        type=str,
        default=None,
        help="Just run TLC on a single spec file and exit (no agent loop)",
    )

    args = parser.parse_args()

    if args.check:
        # Direct TLC check mode (no agent)
        from prepare import evaluate_spec_quality, format_result_for_agent, run_tlc

        result = run_tlc(args.check)
        print(format_result_for_agent(result))
        quality = evaluate_spec_quality(result, args.check)
        print(f"\nSpec Quality: {quality.invariant_count} invariants, "
              f"{quality.temporal_count} temporal props, "
              f"{quality.spec_lines} lines")
        sys.exit(0 if result.passed else 1)

    kwargs = {}
    if args.model:
        kwargs["model"] = args.model

    run_loop(
        target_dir=args.target,
        **kwargs,
        max_iterations=args.max_iters,
        tag=args.tag,
    )


if __name__ == "__main__":
    main()

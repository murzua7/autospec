#!/usr/bin/env python3
"""Subscription-backed queue responder for autospec (no API).

Polls llm_queue/requests/*.json, answers each via headless `claude -p`
(which bills the Claude Code Max subscription, not the Anthropic API),
and writes llm_queue/responses/<id>.json. Stops when STOP_RESPONDER exists.
"""
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REQ = ROOT / "llm_queue" / "requests"
RES = ROOT / "llm_queue" / "responses"
STOP = ROOT / "STOP_RESPONDER"
LOG = ROOT / "responder.log"
CALL_TIMEOUT = 480  # under autospec's 600s per-request timeout

REQ.mkdir(parents=True, exist_ok=True)
RES.mkdir(parents=True, exist_ok=True)

PREAMBLE = (
    "You are operating as a headless formal-verification agent. Follow the system "
    "instructions below exactly and respond DIRECTLY with the required output "
    "(the ```json action block). Do not use any tools, do not ask questions, "
    "do not add commentary outside the required format.\n\n"
)


def log(msg: str) -> None:
    stamp = time.strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{stamp}] {msg}"
    print(line, flush=True)
    with LOG.open("a", encoding="utf-8") as fh:
        fh.write(line + "\n")


def answer(combined: str) -> str:
    proc = subprocess.run(
        ["claude", "-p"],
        input=combined,
        capture_output=True,
        text=True,
        # Without an explicit codec, text=True encodes stdin with the Windows
        # ANSI codepage (cp1252), which cannot represent the arrows, warning
        # signs and comparison operators that program.md carries. Every request
        # then failed with 'charmap' codec can't encode ... and was retried
        # forever. responder.sh never hit this because it writes the prompt to
        # a UTF-8 file and pipes bytes.
        encoding="utf-8",
        errors="replace",
        timeout=CALL_TIMEOUT,
    )
    return proc.stdout or ""


def main() -> None:
    log(f"responder started; polling {REQ}")
    n = 0
    while not STOP.exists():
        reqs = sorted(REQ.glob("*.json"), key=lambda p: p.stat().st_mtime)
        if not reqs:
            time.sleep(2.0)
            continue
        for rf in reqs:
            if STOP.exists():
                break
            try:
                data = json.loads(rf.read_text(encoding="utf-8"))
            except Exception as e:
                log(f"skip unreadable {rf.name}: {e}")
                continue
            rid = data.get("id", rf.stem)
            combined = PREAMBLE + data.get("system", "") + "\n\n===== TASK =====\n\n" + data.get("user", "")
            t0 = time.time()
            try:
                out = answer(combined)
            except subprocess.TimeoutExpired:
                log(f"TIMEOUT on {rid} after {CALL_TIMEOUT}s; leaving request for retry")
                continue
            except Exception as e:
                log(f"ERROR on {rid}: {e}; leaving request")
                continue
            dt = time.time() - t0
            if not out.strip():
                log(f"EMPTY response for {rid} ({dt:.0f}s); leaving request for retry")
                continue
            tmp = RES / f"{rid}.json.tmp"
            tmp.write_text(out, encoding="utf-8")
            tmp.rename(RES / f"{rid}.json")
            rf.unlink(missing_ok=True)
            n += 1
            log(f"answered {rid} in {dt:.0f}s ({len(out)} chars); total={n}")
    log(f"STOP_RESPONDER found; responder exiting after {n} answers")


if __name__ == "__main__":
    main()

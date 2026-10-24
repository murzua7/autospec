#!/bin/bash
# Subscription-backed queue responder for autospec (no API).
# Answers each llm_queue request via headless `claude -p` (Claude Code Max
# subscription, not the Anthropic API). Stops when STOP_RESPONDER exists.
A="/c/Users/matzua/Desktop/Repos/autospec"
REQ="$A/llm_queue/requests"
RES="$A/llm_queue/responses"
LOG="$A/responder.log"
mkdir -p "$REQ" "$RES"
echo "[$(date +%H:%M:%S)] responder.sh started" >> "$LOG"
shopt -s nullglob
n=0
while [ ! -f "$A/STOP_RESPONDER" ]; do
  got=0
  for rf in "$REQ"/*.json; do
    [ -f "$A/STOP_RESPONDER" ] && break
    got=1
    id="$(basename "$rf" .json)"
    pf="$A/_prompt_$id.txt"
    # Extract system+user into a single prompt file (python = reliable JSON+utf8)
    python - "$rf" "$pf" <<'PY'
import json,sys
d=json.load(open(sys.argv[1],encoding="utf-8"))
txt=("Respond DIRECTLY with the required ```json action block. "
     "Do not use any tools, do not ask questions.\n\n"
     + d.get("system","") + "\n\n===== TASK =====\n\n" + d.get("user",""))
open(sys.argv[2],"w",encoding="utf-8").write(txt)
PY
    t0=$(date +%s)
    out="$(timeout 500 claude -p < "$pf")"
    dt=$(( $(date +%s) - t0 ))
    if [ -n "$out" ]; then
      printf '%s' "$out" > "$RES/$id.json"
      rm -f "$rf"
      n=$((n+1))
      echo "[$(date +%H:%M:%S)] answered $id in ${dt}s (${#out} chars) total=$n" >> "$LOG"
    else
      echo "[$(date +%H:%M:%S)] EMPTY $id in ${dt}s (leaving for retry)" >> "$LOG"
    fi
    rm -f "$pf"
  done
  [ "$got" -eq 0 ] && sleep 2
done
echo "[$(date +%H:%M:%S)] STOP_RESPONDER found; exiting after $n answers" >> "$LOG"

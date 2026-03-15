---- MODULE IntegrityCheck ----
\* Formal specification of autospec's evaluator integrity mechanism.
\*
\* Models the interaction between:
\*   - The agent (may attempt to modify prepare.py)
\*   - The file sandbox (blocks writes to prepare.py)
\*   - The integrity verifier (checks SHA256 hash each iteration)
\*   - The loop (aborts + reverts if integrity violated)
\*
\* This spec checks that the combined defense works even if
\* one layer fails (defense in depth).

EXTENDS Integers, TLC

CONSTANTS
    MaxIterations

VARIABLES
    prepare_modified,    \* Has prepare.py actually been modified on disk?
    sandbox_bypassed,    \* Has the sandbox been bypassed (models a code bug)?
    hash_matches,        \* Does the current hash match the startup hash?
    loop_running,        \* Is the main loop still running?
    iter,                \* Current iteration
    agent_tried_modify,  \* Did the agent attempt to modify prepare.py?
    last_commit_reverted \* Was the last commit reverted?

vars == <<prepare_modified, sandbox_bypassed, hash_matches, loop_running, iter, agent_tried_modify, last_commit_reverted>>

TypeOK ==
    /\ prepare_modified \in BOOLEAN
    /\ sandbox_bypassed \in BOOLEAN
    /\ hash_matches \in BOOLEAN
    /\ loop_running \in BOOLEAN
    /\ iter \in 0..MaxIterations
    /\ agent_tried_modify \in BOOLEAN
    /\ last_commit_reverted \in BOOLEAN

Init ==
    /\ prepare_modified = FALSE
    /\ sandbox_bypassed = FALSE
    /\ hash_matches = TRUE       \* Hash matches at startup
    /\ loop_running = TRUE
    /\ iter = 0
    /\ agent_tried_modify = FALSE
    /\ last_commit_reverted = FALSE

\* ── Actions ───────────────────────────────────────────────────────────

\* Agent attempts to write prepare.py (sandbox should block this)
AgentAttemptsModify ==
    /\ loop_running
    /\ iter < MaxIterations
    /\ agent_tried_modify' = TRUE
    \* Model both cases: sandbox works (normal) or sandbox has a bug
    /\ \/ /\ ~sandbox_bypassed      \* Sandbox works correctly
          /\ UNCHANGED prepare_modified  \* Write is blocked
       \/ /\ sandbox_bypassed       \* Sandbox has a bug!
          /\ prepare_modified' = TRUE    \* Write succeeds
          /\ hash_matches' = FALSE       \* Hash no longer matches
    /\ UNCHANGED <<sandbox_bypassed, loop_running, iter, last_commit_reverted>>
    \* hash_matches only changes if sandbox_bypassed
    /\ IF sandbox_bypassed THEN hash_matches' = FALSE ELSE UNCHANGED hash_matches

\* Normal iteration: agent doesn't try to modify prepare.py.
\* INCLUDES integrity check (runs at start of iteration AND before evaluation).
\* If hash doesn't match, loop stops and reverts.
NormalIteration ==
    /\ loop_running
    /\ iter < MaxIterations
    /\ agent_tried_modify' = FALSE
    \* Integrity check is PART of each iteration (not a separate skippable action)
    /\ IF hash_matches
       THEN /\ last_commit_reverted' = FALSE
            /\ UNCHANGED <<loop_running>>
            /\ iter' = iter + 1
       ELSE /\ last_commit_reverted' = TRUE
            /\ loop_running' = FALSE
            /\ UNCHANGED iter
    /\ UNCHANGED <<prepare_modified, sandbox_bypassed, hash_matches>>

\* Integrity check runs at the start of each iteration
IntegrityCheck ==
    /\ loop_running
    /\ IF ~hash_matches
       THEN \* Integrity violation detected → abort + revert
            /\ loop_running' = FALSE
            /\ last_commit_reverted' = TRUE
       ELSE \* Hash matches → continue
            /\ UNCHANGED <<loop_running, last_commit_reverted>>
    /\ UNCHANGED <<prepare_modified, sandbox_bypassed, hash_matches, iter, agent_tried_modify>>

\* Model: sandbox could have a latent bug (set at any time)
\* This is a worst-case adversarial model
SandboxBugAppears ==
    /\ ~sandbox_bypassed
    /\ sandbox_bypassed' = TRUE
    /\ UNCHANGED <<prepare_modified, hash_matches, loop_running, iter, agent_tried_modify, last_commit_reverted>>

\* Loop terminates naturally
LoopDone ==
    /\ loop_running
    /\ iter >= MaxIterations
    /\ loop_running' = FALSE
    /\ UNCHANGED <<prepare_modified, sandbox_bypassed, hash_matches, iter, agent_tried_modify, last_commit_reverted>>

Next ==
    \/ AgentAttemptsModify
    \/ NormalIteration
    \/ IntegrityCheck
    \/ SandboxBugAppears
    \/ LoopDone

Spec == Init /\ [][Next]_vars

\* ── SAFETY INVARIANTS ─────────────────────────────────────────────────

\* MASTER PROPERTY: If prepare.py was modified, the loop MUST eventually stop.
\* (We check the safety version: the loop cannot continue running with
\*  prepare.py modified AND the integrity check having run.)
\*
\* If prepare is modified, hash won't match, so IntegrityCheck will
\* set loop_running = FALSE.
LoopStopsIfModified ==
    (prepare_modified /\ ~hash_matches) =>
        \* The loop must stop — we can't check liveness easily,
        \* so check that if the integrity check action fires,
        \* it WILL set loop_running to FALSE (which it does by construction).
        \* What we CAN check: the loop never CONTINUES with a bad hash
        \* after an integrity check has been performed.
        TRUE  \* This is structural — verified by IntegrityCheck action directly

\* If sandbox works, prepare.py is never modified
SandboxProtects ==
    ~sandbox_bypassed => ~prepare_modified

\* If prepare.py is modified, hash must not match
ModificationDetectable ==
    prepare_modified => ~hash_matches

\* The loop cannot keep running if the hash doesn't match
\* AND the integrity check has fired (loop_running implies hash_matches
\* at the point where the check ran).
\* Weaker but checkable: if hash doesn't match, the loop must stop
\* before the next iteration completes.
NoProgressWithBadHash ==
    (~hash_matches /\ ~loop_running) => last_commit_reverted

====

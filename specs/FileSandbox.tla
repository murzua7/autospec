---- MODULE FileSandbox ----
\* Formal specification of autospec's file-writing sandbox.
\*
\* Models the security checks in apply_changes():
\*   1. Path traversal check: resolved path must be under ROOT
\*   2. Forbidden names: prepare.py, autospec.py, __main__.py, program.md, pyproject.toml
\*   3. Directory allowlist: only specs/, mappings/, target/ are writable
\*
\* Properties to verify:
\*   - The evaluator (prepare.py) is NEVER written
\*   - The orchestrator (autospec.py) is NEVER written
\*   - No file outside ROOT is EVER written
\*   - Only files in allowed directories are written

EXTENDS Integers, TLC, FiniteSets

CONSTANTS
    Files,          \* Set of possible file paths the agent might request
    AllowedDirs,    \* Set of allowed directory prefixes {"specs", "mappings", "target"}
    ForbiddenNames, \* Set of forbidden filenames {"prepare.py", "autospec.py", ...}
    InRoot,         \* Set of Files that resolve inside ROOT
    EscapesRoot     \* Set of Files that resolve outside ROOT (path traversal)

VARIABLES
    requested,      \* File the agent is trying to write this step
    written,        \* Set of files that have been written so far
    blocked,        \* Set of files that were blocked
    phase           \* "request" | "check" | "done"

vars == <<requested, written, blocked, phase>>

\* ── Helper operators ──────────────────────────────────────────────────

\* Extract the "directory" of a file (simplified: the file IS its category)
DirOf(f) == f  \* In this abstract model, files are tagged with their directory

\* Check if a file's name is forbidden
IsForbiddenName(f) == f \in ForbiddenNames

\* Check if a file escapes ROOT
EscapesProject(f) == f \in EscapesRoot

\* Check if a file is in an allowed directory
InAllowedDir(f) == f \in AllowedDirs

\* A file is WRITABLE iff:
\*   1. It resolves inside ROOT (not path traversal)
\*   2. Its name is not forbidden
\*   3. It is in an allowed directory
IsWritable(f) ==
    /\ ~EscapesProject(f)
    /\ ~IsForbiddenName(f)
    /\ InAllowedDir(f)

\* ── Type Invariant ────────────────────────────────────────────────────
TypeOK ==
    /\ requested \in Files \union {"none"}
    /\ written \subseteq Files
    /\ blocked \subseteq Files
    /\ phase \in {"idle", "check", "done"}

\* ── Initial State ─────────────────────────────────────────────────────
Init ==
    /\ requested = "none"
    /\ written = {}
    /\ blocked = {}
    /\ phase = "idle"

\* ── Actions ───────────────────────────────────────────────────────────

\* Agent requests to write a file
Request(f) ==
    /\ phase = "idle"
    /\ f \in Files
    /\ requested' = f
    /\ phase' = "check"
    /\ UNCHANGED <<written, blocked>>

\* Sandbox checks the request and either writes or blocks
Check ==
    /\ phase = "check"
    /\ requested # "none"
    /\ IF IsWritable(requested)
       THEN /\ written' = written \union {requested}
            /\ UNCHANGED blocked
       ELSE /\ blocked' = blocked \union {requested}
            /\ UNCHANGED written
    /\ requested' = "none"
    /\ phase' = "idle"

Next ==
    \/ \E f \in Files: Request(f)
    \/ Check

Spec == Init /\ [][Next]_vars

\* ── SAFETY INVARIANTS ─────────────────────────────────────────────────

\* 1. CRITICAL: Forbidden files are NEVER written
ForbiddenNeverWritten ==
    \A f \in ForbiddenNames: f \notin written

\* 2. CRITICAL: Path-traversal files are NEVER written
PathTraversalBlocked ==
    \A f \in EscapesRoot: f \notin written

\* 3. Only files in allowed directories can be written
OnlyAllowedDirsWritten ==
    \A f \in written: InAllowedDir(f)

\* 4. A file is either written or blocked, never both
WrittenOrBlocked ==
    written \intersect blocked = {}

\* 5. Every checked file ends up in exactly one set
\*    (if it passed through Check, it's in written XOR blocked)
NoFileLost ==
    \A f \in Files:
        (f \in written) => ~(f \in blocked)

\* 6. COMBINED: only writable files are ever written
\*    This is the master safety property
OnlyWritableFilesWritten ==
    \A f \in written: IsWritable(f)

====

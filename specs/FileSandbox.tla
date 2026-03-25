---- MODULE FileSandbox ----
EXTENDS Naturals, FiniteSets

CONSTANTS AllowedDirs, ForbiddenFiles, AllFiles

VARIABLES written, blocked

vars == <<written, blocked>>

TypeOK ==
    /\ written \subseteq AllFiles
    /\ blocked \subseteq AllFiles

ForbiddenNeverWritten ==
    \A f \in ForbiddenFiles: f \notin written

OnlyAllowedDirsWritten ==
    \A f \in written: f \in AllowedDirs

BlockedNeverWritten ==
    written \cap blocked = {}

Init ==
    /\ written = {}
    /\ blocked = {}

WriteAllowed(f) ==
    /\ f \in AllFiles
    /\ f \notin ForbiddenFiles
    /\ f \in AllowedDirs
    /\ written' = written \union {f}
    /\ UNCHANGED blocked

WriteBlocked(f) ==
    /\ f \in AllFiles
    /\ (f \in ForbiddenFiles \/ f \notin AllowedDirs)
    /\ blocked' = blocked \union {f}
    /\ UNCHANGED written

Done == UNCHANGED vars

Next ==
    \/ \E f \in AllFiles: WriteAllowed(f)
    \/ \E f \in AllFiles: WriteBlocked(f)
    \/ Done

Spec == Init /\ [][Next]_vars
====

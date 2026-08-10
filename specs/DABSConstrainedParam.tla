---- MODULE DABSConstrainedParam ----
\* PARAM-1: the constrained-parameter write path.
\*
\* Target: dabs/config_constrained.py. At the pinned commit the machinery is
\* complete -- _constrain_softplus (268), _constrain_sigmoid (301),
\* _constrain_anchored_logit (321), set_constrained (370) -- while the
\* ENROLMENT lists are all but empty:
\*     _SOFTPLUS_CONSTRAINED = ("firm_wage_markup",)   line 168
\*     _SIGMOID_CONSTRAINED  = ()                      line 169
\*
\* Enrolling a name replaces the plain attribute with a registered
\* <name>_raw parameter plus a reconstructing property. That creates two
\* write paths with very different behaviour:
\*
\*   set_constrained(name, v)  -- inverts the transform and writes the raw
\*                                parameter; the reconstruction then returns v.
\*   config.<name>.data = v    -- writes into the tensor the property just
\*                                COMPUTED and returned. Nothing holds a
\*                                reference to it, so the assignment is
\*                                discarded. No exception is raised.
\*
\* The second path is the hazard: a calibration that never lands and never
\* complains. It is modelled here as a shadow ledger carrying what the caller
\* BELIEVES was applied, in the same idiom the accounting specs use, so the
\* divergence is pinned as an invariant rather than surfacing as a violation.

EXTENDS Integers

CONSTANTS MaxVal, MaxWrites

ASSUME /\ MaxVal    \in Nat
       /\ MaxWrites \in Nat

\* Two parameters: one enrolled (the firm_wage_markup case), one not
\* (every other trainable coefficient at this commit).
Params   == {"enrolled", "plain"}
Enrolled == {"enrolled"}

\* The domain a softplus-constrained parameter must stay inside: strictly
\* positive. Represented as 1..MaxVal, with 0 standing for the excluded bound.
InDomain(v) == v \in 1..MaxVal

VARIABLES
    effective,   \* the value the MODEL actually reads for each parameter
    believed,    \* the value the CALLER believes it applied (shadow ledger)
    raised,      \* TRUE once a write was rejected loudly
    silentDrop,  \* TRUE once a write was discarded with no error at all
    writes       \* number of write attempts

vars == <<effective, believed, raised, silentDrop, writes>>

TypeOK ==
    /\ effective  \in [Params -> 0..MaxVal]
    /\ believed   \in [Params -> 0..MaxVal]
    /\ raised     \in BOOLEAN
    /\ silentDrop \in BOOLEAN
    /\ writes     \in 0..MaxWrites

Init ==
    /\ effective  = [p \in Params |-> 1]
    /\ believed   = [p \in Params |-> 1]
    /\ raised     = FALSE
    /\ silentDrop = FALSE
    /\ writes     = 0

\* -- Write path 1: set_constrained -----------------------------------------
\* On an enrolled name it inverts the transform and the reconstruction
\* returns exactly v, so effective and believed move together. On a name in
\* neither enrolment list the code raises rather than guessing a transform.
SetConstrained(p, v) ==
    /\ writes < MaxWrites
    /\ writes' = writes + 1
    /\ IF p \in Enrolled
         THEN /\ effective'  = [effective  EXCEPT ![p] = v]
              /\ believed'   = [believed   EXCEPT ![p] = v]
              /\ UNCHANGED <<raised, silentDrop>>
         ELSE /\ raised' = TRUE
              /\ UNCHANGED <<effective, believed, silentDrop>>

\* -- Write path 2: direct .data assignment ---------------------------------
\* On a PLAIN attribute this is the ordinary in-place write and it lands.
\* On an ENROLLED name it writes into a freshly computed tensor that nothing
\* retains: the caller believes v was applied, the model still reads the old
\* value, and no exception is raised. That is the silent drop.
DataAssign(p, v) ==
    /\ writes < MaxWrites
    /\ writes' = writes + 1
    /\ IF p \in Enrolled
         THEN /\ believed'   = [believed EXCEPT ![p] = v]
              /\ silentDrop' = (silentDrop \/ (v # effective[p]))
              /\ UNCHANGED <<effective, raised>>
         ELSE /\ effective' = [effective EXCEPT ![p] = v]
              /\ believed'  = [believed  EXCEPT ![p] = v]
              /\ UNCHANGED <<raised, silentDrop>>

Terminal == /\ writes = MaxWrites
            /\ UNCHANGED vars

Next ==
    \/ \E p \in Params, v \in 1..MaxVal : SetConstrained(p, v)
    \/ \E p \in Params, v \in 1..MaxVal : DataAssign(p, v)
    \/ Terminal

\* -- Domain containment ----------------------------------------------------
\* An enrolled parameter is reachable only through the transform, so its
\* reconstructed value never leaves the open domain however it is written.
\* This is the property enrolment BUYS.
EnrolledStaysInDomain == \A p \in Enrolled : InDomain(effective[p])

\* -- The unenrolled parameter has no such guard ---------------------------
\* Nothing here constrains "plain": it is written directly and no transform
\* stands between the optimiser and its value. At the pinned commit that is
\* every trainable coefficient except firm_wage_markup, which is why training
\* carries them outside their economic ranges with nothing to stop it.
PlainIsUnguarded == believed["plain"] = effective["plain"]

\* -- set_constrained always lands ------------------------------------------
\* On an enrolled name the intended value is the value the model reads.
\* Fails if the inversion were wrong, or the reconstruction disagreed with it.
SetConstrainedLands ==
    (~silentDrop) => (\A p \in Enrolled : believed[p] = effective[p])

\* -- The silent-drop hazard, pinned ----------------------------------------
\* Every divergence between what the caller believes it applied and what the
\* model actually reads is attributable to the silent .data path -- nothing
\* else in the write surface can produce one. Equivalently: set_constrained
\* is sound, and the ONLY way a calibration goes missing is the assignment
\* that raises nothing.
\*
\* This is the falsifiable form. It fails the moment any other path starts
\* dropping writes, and the flag becomes unreachable if the property grows a
\* setter (the write would land) or raises on assignment (it would fail
\* loudly) -- either repair empties the antecedent, which is how a spec
\* should react to the defect being fixed.
\*
\* Note the direction. The converse -- silentDrop => divergence -- is NOT an
\* invariant, because a later set_constrained on the same name reconverges
\* belief and effect while the flag stays set. Asserting it was a spec error
\* caught on the first run.
DivergenceOnlyFromSilentDrop ==
    (\E p \in Enrolled : believed[p] # effective[p]) => silentDrop

Spec == Init /\ [][Next]_vars

====

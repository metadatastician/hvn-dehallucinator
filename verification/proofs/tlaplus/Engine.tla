------------------------------- MODULE Engine -------------------------------
(* SPDX-License-Identifier: MPL-2.0                                        *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell                       *)
(*                                                                         *)
(* The engine (engine/Engine.hs) against a world it does not control,      *)
(* model-checked by TLC (scripts/check-tla.sh). HD-1, re-derived           *)
(* 2026-10-14.                                                              *)
(*                                                                         *)
(* The world: `remaining` artefacts survive, and the agent (or anything     *)
(* else) may change that number at any time without telling the engine.   *)
(* The verifier, when it runs, reports `remaining` exactly; it may also    *)
(* fail. The engine never sees `remaining` except through a measurement.  *)
(*                                                                         *)
(* `lastCount` is a ghost: the count the most recent successful update     *)
(* obtained from the verifier as {n}, or {} since the last init. It is    *)
(* what THE GUARANTEE is about: COMPLETE stands only on a measured zero.  *)
(*                                                                         *)
(* `lastWorld` is a second ghost: what the bound target actually held when *)
(* that count was taken. MeasuresTheTarget says the two agree, and         *)
(* GuaranteeBound that COMPLETE stands on the target itself measuring zero.*)
(* With OtherTarget = TRUE the model also has the engine before 2026-11-09,*)
(* whose `update <dir>` measured a directory the caller chose; TLC must    *)
(* refute GuaranteeBound in that model (OtherTarget.cfg), which Guarantee  *)
(* alone cannot see.                                                       *)
(*                                                                         *)
(* With Original = TRUE the model also has the root-commit engine's        *)
(* `update <remaining>` (commit 4c91e71): the caller types the number, no  *)
(* attempt is charged and no measurement is taken. TLC must find the       *)
(* Incident as a violation of Guarantee in that model (Original.cfg); the  *)
(* gate fails if it does not.                                              *)
(*                                                                         *)
(* PROOF-POLICY section 4 exception (metadatastician/standards,            *)
(* 3-practice/PROOF-POLICY.adoc). Obligation: HD-1T, the engine against a  *)
(* world that changes freely and a verifier that may fail. Tool: TLA+ and  *)
(* TLC, instead of Idris2, the mapped prover for an engineering property.  *)
(* Why: the property is about every interleaving of an environment the     *)
(* engine does not control; a model checker explores those exhaustively    *)
(* at fixed bounds, and stating them in Idris2 would take far longer.      *)
(* A finite model check is TESTED at its bounds (MaxTotal = 3,             *)
(* MaxRemaining = 4), not PROVEN. Recorded in the ledger, row HD-1T.       *)
EXTENDS Naturals

CONSTANTS
    MaxTotal,      \* largest baseline modelled
    MaxRemaining,  \* largest surviving count modelled
    MinRemaining,  \* smallest surviving count at the start (Original.cfg: 1, as in the Incident)
    Slack,         \* attemptSlack in Engine.hs (5)
    Original,      \* TRUE: add the original, caller-asserted update
    OtherTarget    \* TRUE: add `update <dir>` measuring a directory the caller chose

VARIABLES total, completed, attempts, status, remaining, lastCount, lastWorld

vars == <<total, completed, attempts, status, remaining, lastCount, lastWorld>>

Running  == "RUNNING"
Complete == "COMPLETE"
Stop     == "EMERGENCY_STOP"

Counts == 0 .. MaxRemaining

TypeOK ==
    /\ total \in 0 .. MaxTotal \cup Counts
    /\ completed \in Nat
    /\ attempts \in Nat
    /\ status \in {Running, Complete, Stop}
    /\ remaining \in Counts
    /\ lastCount \in {{}} \cup {{n} : n \in Counts}
    /\ lastWorld \in {{}} \cup {{n} : n \in Counts}

Done(t, r) == IF r >= t THEN 0 ELSE t - r   \* max 0 (totalItems - remaining)

(* --- resets: init <n> and init-from <target> ----------------------------- *)

Reset(t) ==
    /\ total' = t /\ completed' = 0 /\ attempts' = 0 /\ status' = Running
    /\ lastCount' = {} /\ lastWorld' = {} /\ UNCHANGED remaining

InitN    == \E n \in 0 .. MaxTotal : Reset(n)
InitFrom == Reset(remaining)          \* a failed init-from changes nothing

Init == /\ remaining \in MinRemaining .. MaxRemaining
        /\ total \in 0 .. MaxTotal /\ completed = 0 /\ attempts = 0
        /\ status = Running /\ lastCount = {} /\ lastWorld = {}

(* --- the world moves on its own ------------------------------------------ *)

World == /\ remaining' \in Counts
         /\ UNCHANGED <<total, completed, attempts, status, lastCount, lastWorld>>

(* --- refuseIfStopped, then bumpOrTrip ------------------------------------ *)

Trips == attempts + 1 > total + Slack

Trip == /\ status' = Stop /\ attempts' = attempts + 1
        /\ UNCHANGED <<total, completed, remaining, lastCount, lastWorld>>

Attempt ==
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE /\ attempts' = attempts + 1
            /\ UNCHANGED <<total, completed, status, remaining, lastCount, lastWorld>>

\* update: the verifier runs on the bound target and reports its `remaining`.
UpdateMeasured ==
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE /\ attempts' = attempts + 1
            /\ completed' = Done(total, remaining)
            /\ status' = IF remaining = 0 THEN Complete ELSE Running
            /\ lastCount' = {remaining}
            /\ lastWorld' = {remaining}
            /\ UNCHANGED <<total, remaining>>

\* update: the verifier fails, so there is no count; COMPLETE is demoted.
UpdateFailed ==
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE /\ attempts' = attempts + 1
            /\ status' = IF status = Complete THEN Running ELSE status
            /\ UNCHANGED <<total, completed, remaining, lastCount, lastWorld>>

\* The original engine: `update <remaining>` with the number typed by the caller.
UpdateAsserted ==
    /\ Original
    /\ \E n \in Counts :
        /\ completed' = Done(total, n)
        /\ status' = IF n = 0 THEN Complete ELSE status
        /\ UNCHANGED <<total, attempts, remaining, lastCount, lastWorld>>

\* The engine before 2026-11-09: `update <dir>` measured whatever directory the
\* caller named, so the verifier's count c need not be the bound target's. The
\* attempt is charged and the count is real; it is just not the target's.
UpdateOtherTarget ==
    /\ OtherTarget
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE \E c \in Counts :
            /\ attempts' = attempts + 1
            /\ completed' = Done(total, c)
            /\ status' = IF c = 0 THEN Complete ELSE Running
            /\ lastCount' = {c}
            /\ lastWorld' = {remaining}
            /\ UNCHANGED <<total, remaining>>

Next == InitN \/ InitFrom \/ World \/ Attempt
        \/ UpdateMeasured \/ UpdateFailed \/ UpdateAsserted \/ UpdateOtherTarget

Spec == Init /\ [][Next]_vars

(* --- what is checked ----------------------------------------------------- *)

\* THE GUARANTEE: COMPLETE stands only on a measured zero.
Guarantee == status = Complete => lastCount = {0}

\* ... and that zero was the bound target's: the count the engine acted on is
\* what the target held when it was measured.
MeasuresTheTarget == lastCount = lastWorld
GuaranteeBound == status = Complete => lastWorld = {0}

\* The budget bounds every run.
Budget == status # Stop => attempts <= total + Slack

CompletedBounded == completed <= total

\* COMPLETE is introduced only together with a measured zero.
CompleteOnlyFromZeroCount ==
    [][(status' = Complete /\ status # Complete) => lastCount' = {0}]_vars

\* EMERGENCY_STOP is left only by a deliberate reset (attempts back to 0).
StopTerminal ==
    [][status = Stop => (status' = Stop \/ attempts' = 0)]_vars

=============================================================================

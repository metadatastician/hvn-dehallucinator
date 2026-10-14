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
(* With Original = TRUE the model also has the root-commit engine's        *)
(* `update <remaining>` (commit 4c91e71): the caller types the number, no  *)
(* attempt is charged and no measurement is taken. TLC must find the       *)
(* Incident as a violation of Guarantee in that model (Original.cfg); the  *)
(* gate fails if it does not.                                              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    MaxTotal,      \* largest baseline modelled
    MaxRemaining,  \* largest surviving count modelled
    MinRemaining,  \* smallest surviving count at the start (Original.cfg: 1, as in the Incident)
    Slack,         \* attemptSlack in Engine.hs (5)
    Original       \* TRUE: add the original, caller-asserted update

VARIABLES total, completed, attempts, status, remaining, lastCount

vars == <<total, completed, attempts, status, remaining, lastCount>>

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

Done(t, r) == IF r >= t THEN 0 ELSE t - r   \* max 0 (totalItems - remaining)

(* --- resets: init <n> and init-from <target> ----------------------------- *)

Reset(t) ==
    /\ total' = t /\ completed' = 0 /\ attempts' = 0 /\ status' = Running
    /\ lastCount' = {} /\ UNCHANGED remaining

InitN    == \E n \in 0 .. MaxTotal : Reset(n)
InitFrom == Reset(remaining)          \* a failed init-from changes nothing

Init == /\ remaining \in MinRemaining .. MaxRemaining
        /\ total \in 0 .. MaxTotal /\ completed = 0 /\ attempts = 0
        /\ status = Running /\ lastCount = {}

(* --- the world moves on its own ------------------------------------------ *)

World == /\ remaining' \in Counts
         /\ UNCHANGED <<total, completed, attempts, status, lastCount>>

(* --- refuseIfStopped, then bumpOrTrip ------------------------------------ *)

Trips == attempts + 1 > total + Slack

Trip == /\ status' = Stop /\ attempts' = attempts + 1
        /\ UNCHANGED <<total, completed, remaining, lastCount>>

Attempt ==
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE /\ attempts' = attempts + 1
            /\ UNCHANGED <<total, completed, status, remaining, lastCount>>

\* update <target>, the verifier runs and reports `remaining`.
UpdateMeasured ==
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE /\ attempts' = attempts + 1
            /\ completed' = Done(total, remaining)
            /\ status' = IF remaining = 0 THEN Complete ELSE Running
            /\ lastCount' = {remaining}
            /\ UNCHANGED <<total, remaining>>

\* update <target>, the verifier fails: no count; COMPLETE is demoted.
UpdateFailed ==
    /\ status # Stop
    /\ IF Trips THEN Trip
       ELSE /\ attempts' = attempts + 1
            /\ status' = IF status = Complete THEN Running ELSE status
            /\ UNCHANGED <<total, completed, remaining, lastCount>>

\* The original engine: `update <remaining>` with the number typed by the caller.
UpdateAsserted ==
    /\ Original
    /\ \E n \in Counts :
        /\ completed' = Done(total, n)
        /\ status' = IF n = 0 THEN Complete ELSE status
        /\ UNCHANGED <<total, attempts, remaining, lastCount>>

Next == InitN \/ InitFrom \/ World \/ Attempt
        \/ UpdateMeasured \/ UpdateFailed \/ UpdateAsserted

Spec == Init /\ [][Next]_vars

(* --- what is checked ----------------------------------------------------- *)

\* THE GUARANTEE: COMPLETE stands only on a measured zero.
Guarantee == status = Complete => lastCount = {0}

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

{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- A hallucinated completion is a claim over an empty fibre.
--
-- Consumes residual-evidence-types by pin, never by re-declaration:
--   hyperpolymath/residual-evidence-types @ 97244f5cb63bd6697caff261b187b62e9788b692
--   (scripts/fetch-siblings.sh puts it in _build/dependencies).
--
-- Its Core is instantiated for the engine (engine/Engine.hs):
--
--   world        a recorded task state paired with the number of artefacts
--                that actually survive, i.e. what engine/verify_register.sh
--                would count;
--   observation  the recorded task state, i.e. state/state.txt (`recorded`);
--   claim        Complete: nothing survives;
--   evidence     Unmeasured (the record alone) or Measured m (the verifier
--                reported m).
--
-- The record does not identify the claim. Over any recorded state, a reading
-- with an asserted count and a reading with a different measured count both
-- fit it (asserted-not-identified): that pair is the blind-spot witness the
-- engine prints when it regresses. The engine writes COMPLETE only from an
-- inhabited measured case in which every candidate has nothing remaining
-- (complete-needs-case). Asserting "done" against a non-zero measurement leaves
-- no world at all (hallucinated-complete-has-no-case).
--
-- tests/reject/AssertedComplete.agda is the 2026-08-23/24 Incident as a
-- refused derivation: COMPLETE from the record 16/16/0/COMPLETE alone.
--
-- Checked by scripts/check-agda-kernel.sh with Agda 2.6.3 under
-- --safe --without-K --no-libraries --ignore-interfaces --double-check.

module Fibre where

open import Agda.Builtin.Nat using (_-_)
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
  using (Candidate; Case; inhabited; Holds; Identified)
open import ResidualEvidence.Revision
  using (Refuted; Disagreeing; refuted-not-holds; disagreeing-not-identified)

------------------------------------------------------------------------
-- The engine's state, as engine/Engine.hs writes it to state/state.txt

data Status : Set where
  running complete emergency-stop : Status

record TaskState : Set where
  constructor task
  field
    totalItems completed attempts : Nat
    status : Status
open TaskState public

-- updateFromVerifier on a measured count m, after bumpOrTrip has charged the
-- attempt: completed = max 0 (totalItems - m); COMPLETE exactly when m is 0.
derive : Nat → Status
derive zero    = complete
derive (suc _) = running

update : TaskState → Nat → TaskState
update s m = task (totalItems s) (totalItems s - m) (suc (attempts s)) (derive m)

------------------------------------------------------------------------
-- Worlds, the observation, the claim, the evidence

World : Set
World = TaskState × Nat

recorded : World → TaskState
recorded = fst

remaining : World → Nat
remaining = snd

Complete : World → Set
Complete w = remaining w ≡ 0

Unmeasured : World → Set
Unmeasured _ = ⊤

Measured : Nat → World → Set
Measured m w = remaining w ≡ m

suc≢zero : ∀ {k} → ¬ (suc k ≡ 0)
suc≢zero ()

------------------------------------------------------------------------
-- The record alone: every count is a reading of it

reading : (s : TaskState) (n : Nat) → Candidate recorded s Unmeasured
reading s n = (s , n) , refl , tt

unmeasured : (s : TaskState) → Case recorded s Unmeasured
unmeasured s = inhabited (reading s 0)

-- An asserted count and a measured count that differ are two readings of the
-- same record that disagree on what remains: the record does not identify it.
-- The disagreement is positive data, and ¬ Identified follows from it.
asserted-not-identified : (s : TaskState) (asserted measured : Nat) →
  ¬ (asserted ≡ measured) →
  Disagreeing (unmeasured s) remaining × (¬ Identified (unmeasured s) remaining)
asserted-not-identified s asserted measured differ =
  witness , disagreeing-not-identified (unmeasured s) remaining witness
  where
  witness : Disagreeing (unmeasured s) remaining
  witness = reading s asserted , reading s measured , differ

-- On regress the record says COMPLETE (nothing remains) and the verifier
-- counts suc k: the measured reading refutes the recorded claim.
regress-refutes : (s : TaskState) (k : Nat) → Refuted (unmeasured s) Complete
regress-refutes s k = reading s (suc k) , suc≢zero

record-does-not-hold-complete : (s : TaskState) → ¬ Holds (unmeasured s) Complete
record-does-not-hold-complete s = refuted-not-holds (unmeasured s) (regress-refutes s 0)

------------------------------------------------------------------------
-- A measurement: the only route to COMPLETE

measured : (s : TaskState) (m : Nat) → Case recorded (update s m) (Measured m)
measured s m = inhabited ((update s m , m) , refl , refl)

-- If the engine writes COMPLETE, there is an inhabited measured case and every
-- candidate in it has nothing remaining.
complete-needs-case : (s : TaskState) (m : Nat) →
  status (update s m) ≡ complete →
  Σ (Case recorded (update s m) (Measured m)) (λ c → Holds c Complete)
complete-needs-case s zero    _  = measured s zero , λ { (w , _ , counted) → counted }
complete-needs-case s (suc m) ()

-- A non-zero measurement refutes COMPLETE at a witness world of its own case.
measured-nonzero-refutes : (s : TaskState) (k : Nat) →
  Refuted (measured s (suc k)) Complete
measured-nonzero-refutes s k = ((update s (suc k) , suc k) , refl , refl) , suc≢zero

-- "Done" asserted against a non-zero measurement is a claim over an empty
-- fibre: no world fits the record, the measurement and the claim together, so
-- no case can be formed (compare Presence.conflict-has-no-case).
hallucinated-complete-is-empty : (s : TaskState) (k : Nat) →
  ¬ Candidate recorded s (λ w → Measured (suc k) w × Complete w)
hallucinated-complete-is-empty s k (w , observed , counted , done) =
  suc≢zero (trans (sym counted) done)

hallucinated-complete-has-no-case : (s : TaskState) (k : Nat) →
  ¬ Case recorded s (λ w → Measured (suc k) w × Complete w)
hallucinated-complete-has-no-case s k c =
  hallucinated-complete-is-empty s k (Case.witness c)

------------------------------------------------------------------------
-- The Incident, 2026-08-23/24, at its literal numbers

-- state/state.txt was written 16 / 16 / 0 / COMPLETE at 19:22:46 on
-- 2026-08-23 and never measured; the first measurement (init-from, 2026-08-25)
-- counted 15272 surviving artefacts.
incident : TaskState
incident = task 16 16 0 complete

incident-measured : Nat
incident-measured = 15272

-- The two readings the engine now prints: as recorded (0) and as measured.
incident-witness : Disagreeing (unmeasured incident) remaining
incident-witness = fst (asserted-not-identified incident 0 incident-measured (λ ()))

incident-not-complete : ¬ Holds (unmeasured incident) Complete
incident-not-complete =
  refuted-not-holds (unmeasured incident) (regress-refutes incident 15271)

-- At the measured count the engine writes RUNNING, with nothing completed.
incident-regresses : update incident incident-measured ≡ task 16 0 1 running
incident-regresses = refl

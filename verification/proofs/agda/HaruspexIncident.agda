{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- The worked example of docs/proposals/HARUSPEX.adoc: the 2026-08-23/24
-- Incident, as a pre-flight check.
--
-- The author declares the context the agent had: the record it could hold
-- (Fibre.incident, 16 / 16 / 0 / COMPLETE, or the record the engine writes
-- after the measurement, 16 / 0 / 1 / RUNNING) and the counts that could
-- remain (none, or the 15272 the first measurement found). A reading is a
-- Fibre world; it shows its record. Then, by normalisation:
--
--   confirm      "confirm the migration is COMPLETE", record only:
--                Epi, with the pair (incident, 0) / (incident, 15272), the
--                same two readings as Fibre.incident-witness, delivered
--                before the prompt is sent;
--   refuted      the same claim with the measurement stated: Empty, with the
--                refuting reading (incident, 15272);
--   how-many     "how many artefacts remain?" with the measurement: Sound,
--                with the value 15272;
--   asserted     "done" asserted on top of the measurement: Empty, no reading
--                at all (compare Fibre.hallucinated-complete-has-no-case).
--
-- The counts are a declaration, not a fact: Sound transfers to the actual
-- context only with the listing as a premise (Haruspex.Check.actual-sound).
-- The Epi pair and the refuting reading are positive data and need no such
-- premise to exhibit; pre-flight-witness re-reads the pair as Fibre
-- candidates under the record alone.

module HaruspexIncident where

open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core using (Candidate)
open import ResidualEvidence.Revision using (Disagreeing)
open import ResidualEvidence.Finite.Int using (==-sound; ==-refl; bool-clash)
open import ResidualEvidence.Finite.Row
  using (Verdict; entailed; refuted; unresolved; inconsistent;
         IdStatus; identified; unidentified; no-candidate)
open import ResidualEvidence.Finite.Checker using (_∧_)
open import ResidualEvidence.Finite.Soundness using (∧-sound; ∧-complete)
open import Fibre
  using (Status; running; complete; emergency-stop; TaskState; task;
         World; recorded; remaining; Unmeasured; unmeasured;
         incident; incident-measured; incident-witness)
open import Haruspex

------------------------------------------------------------------------
-- Decidable equality on records

_==ₛ_ : Status → Status → Bool
running        ==ₛ running        = true
running        ==ₛ complete       = false
running        ==ₛ emergency-stop = false
complete       ==ₛ running        = false
complete       ==ₛ complete       = true
complete       ==ₛ emergency-stop = false
emergency-stop ==ₛ running        = false
emergency-stop ==ₛ complete       = false
emergency-stop ==ₛ emergency-stop = true

==ₛ-sound : ∀ a b → (a ==ₛ b) ≡ true → a ≡ b
==ₛ-sound running        running        _ = refl
==ₛ-sound running        complete       ()
==ₛ-sound running        emergency-stop ()
==ₛ-sound complete       running        ()
==ₛ-sound complete       complete       _ = refl
==ₛ-sound complete       emergency-stop ()
==ₛ-sound emergency-stop running        ()
==ₛ-sound emergency-stop complete       ()
==ₛ-sound emergency-stop emergency-stop _ = refl

==ₛ-refl : ∀ a → (a ==ₛ a) ≡ true
==ₛ-refl running        = refl
==ₛ-refl complete       = refl
==ₛ-refl emergency-stop = refl

_==ₜ_ : TaskState → TaskState → Bool
task a b c s ==ₜ task a' b' c' s' = (a == a') ∧ (b == b') ∧ (c == c') ∧ (s ==ₛ s')

task-cong : ∀ {a a' b b' c c' : Nat} {s s' : Status} →
  a ≡ a' → b ≡ b' → c ≡ c' → s ≡ s' → task a b c s ≡ task a' b' c' s'
task-cong refl refl refl refl = refl

==ₜ-sound : ∀ x y → (x ==ₜ y) ≡ true → x ≡ y
==ₜ-sound (task a b c s) (task a' b' c' s') e =
  task-cong (==-sound a a' (fst e₁)) (==-sound b b' (fst e₂))
            (==-sound c c' (fst e₃)) (==ₛ-sound s s' (snd e₃))
  where
    e₁ = ∧-sound (a == a') _ e
    e₂ = ∧-sound (b == b') _ (snd e₁)
    e₃ = ∧-sound (c == c') _ (snd e₂)

==ₜ-complete : ∀ x y → x ≡ y → (x ==ₜ y) ≡ true
==ₜ-complete (task a b c s) _ refl =
  ∧-complete (==-refl a) (∧-complete (==-refl b) (∧-complete (==-refl c) (==ₛ-refl s)))

------------------------------------------------------------------------
-- The declared context

after : TaskState                       -- what the engine writes on the measurement
after = task 16 0 1 running

incidentSchema : Schema
incidentSchema = record
  { Reading    = World
  ; readings   = (incident , 0) ∷ (incident , incident-measured)
               ∷ (after , 0)    ∷ (after , incident-measured) ∷ []
  ; Shown      = TaskState
  ; shows      = recorded
  ; _≟_        = _==ₜ_
  ; ≟-sound    = ==ₜ-sound
  ; ≟-complete = ==ₜ-complete
  }

open Check incidentSchema
  using (HCandidate; HCase; presence; identity; unresolved-sound; refuted-refutes;
         refuted-case; identified-sound; identified-case; inconsistent-sound)

done measured : World → Bool
done w     = remaining w == 0
measured w = remaining w == incident-measured

remainingQ : Query World
remainingQ = record
  { Value = Nat ; value = remaining ; _==_ = _==_
  ; ==-sound = ==-sound ; ==-complete = λ a b e → ==-refl-at a b e }
  where
    ==-refl-at : ∀ a b → a ≡ b → (a == b) ≡ true
    ==-refl-at a _ refl = ==-refl a

confirm refuted-prompt how-many asserted : Prompt incidentSchema
confirm        = record { shown = incident ; assumptions = []                     ; ask = claim done }
refuted-prompt = record { shown = incident ; assumptions = measured ∷ []          ; ask = claim done }
how-many       = record { shown = incident ; assumptions = measured ∷ []          ; ask = query remainingQ }
asserted       = record { shown = incident ; assumptions = measured ∷ done ∷ []   ; ask = claim done }

------------------------------------------------------------------------
-- The four answers

confirm-is-epi : verdict incidentSchema confirm ≡ Epi
confirm-is-epi = refl

refuted-is-empty : verdict incidentSchema refuted-prompt ≡ Empty
refuted-is-empty = refl

how-many-is-sound : verdict incidentSchema how-many ≡ Sound
how-many-is-sound = refl

asserted-is-empty : verdict incidentSchema asserted ≡ Empty
asserted-is-empty = refl

-- Two readings, side by side.
both : World → World → World × World
both a b = a , b

-- confirm: the pair, and that it is the engine's blind-spot witness.
pre-flight-pair :
  Σ (HCandidate incident []) (λ x → done (fst x) ≡ true) ×
  Σ (HCandidate incident []) (λ y → done (fst y) ≡ false)
pre-flight-pair = unresolved-sound incident [] done refl

pre-flight-readings :
  both (fst (fst (fst pre-flight-pair))) (fst (fst (snd pre-flight-pair)))
  ≡ both (incident , 0) (incident , incident-measured)
pre-flight-readings = refl

to-fibre : ∀ {as} → HCandidate incident as → Candidate recorded incident Unmeasured
to-fibre (w , observed , _) = w , observed , tt

pre-flight-witness : Disagreeing (unmeasured incident) remaining
pre-flight-witness = to-fibre (fst (fst pre-flight-pair)) , to-fibre (fst (snd pre-flight-pair)) , λ ()

same-readings-as-the-engine :
  both (fst (fst pre-flight-witness)) (fst (fst (snd pre-flight-witness)))
  ≡ both (fst (fst incident-witness)) (fst (fst (snd incident-witness)))
same-readings-as-the-engine = refl

-- refuted: the measured reading refutes "done".
refuting-reading :
  fst (fst (refuted-refutes incident (measured ∷ []) done refl
             (refuted-case incident (measured ∷ []) done refl)))
  ≡ (incident , incident-measured)
refuting-reading = refl

-- how-many: the value is 15272, at every candidate.
how-many-value :
  fst (identified-sound incident (measured ∷ []) remainingQ refl
        (identified-case incident (measured ∷ []) remainingQ refl))
  ≡ incident-measured
how-many-value = refl

-- asserted: no reading fits the record, the measurement and "done" together.
asserted-has-no-case : ¬ HCase incident (measured ∷ done ∷ [])
asserted-has-no-case = inconsistent-sound incident (measured ∷ done ∷ []) done refl

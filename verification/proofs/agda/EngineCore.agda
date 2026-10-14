{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- The engine's command semantics, mechanised (HD-1, re-derived 2026-10-14).
--
-- The 2026-08-27 EngineCore.lean is in nothing pushed; this re-derives its
-- claims in the proof kernel (Agda --safe --without-K) rather than Lean, which
-- the estate keeps as provenance only. The model is engine/Engine.hs read
-- command by command:
--
--   init n            write n / 0 / 0 / RUNNING                      exit 0
--   init-from r       a counted baseline as init; a failed one       exit 1
--   attempt           refuseIfStopped; bumpOrTrip                    exit 0 / 1 / 3
--   update r          refuseIfStopped; bumpOrTrip; then a count m
--                     derives completed and status (Fibre.update), and
--                     a failed count demotes COMPLETE (Fibre.refuse) exit 0 / 1 / 3 / 4
--   verify, status    read only                                      exit 0
--
-- The verifier's output is a Reading: a count, or a failure. Nothing a caller
-- types is a Reading; the engine obtains it by running the verifier. The state,
-- `update` and `refuse` are Fibre's, so the two models cannot drift apart.
--
-- Proved here:
--   guarantee              COMPLETE is introduced by no command except an
--                          update whose reading is a counted zero
--   update-complete-only-from-zero, init-never-complete
--   regress, refuse-demotes, nonzero-not-complete
--   attempt-charges, update-charges
--   attempt-trips, update-trips, stop-refuses-attempt, stop-refuses-update
--   stop-absorbs           a stopped engine stays stopped under any run of
--                          non-reset commands
--   verify-read-only, show-read-only, init-resets, init-from-measures,
--   init-from-failed-unchanged
--   within-preserved       the attempt budget bounds every run: a state that
--                          is not stopped has attempts <= total + 5
--   bounded-preserved      completed <= total
--   agrees-update, agrees-refuse   the update branches are Fibre's
--   incident               the Incident replayed; incident-original, the
--                          original engine writing COMPLETE from a typed 0
--
-- Checked by scripts/check-agda-kernel.sh (residual-evidence-types pinned, via
-- Fibre). That this model matches Engine.hs is by inspection, not by proof.

module EngineCore where

open import Agda.Builtin.Nat using (_-_; _<_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import ResidualEvidence.Prelude
open import Fibre
  using (Status; running; complete; emergency-stop;
         TaskState; task; totalItems; completed; attempts; status;
         derive; demote; refuse)
  renaming (update to fibre-update)

------------------------------------------------------------------------
-- Small facts

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

absurd : {A : Set} → ⊥ → A
absurd ()

≤-refl : (n : Nat) → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-step : {m n : Nat} → m ≤ n → m ≤ suc n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

-- The builtin `<` answering false is a `≤` the other way.
<-false : (m n : Nat) → (m < n) ≡ false → n ≤ m
<-false m       zero    _ = z≤n
<-false zero    (suc n) ()
<-false (suc m) (suc n) e = s≤s (<-false m n e)

monus-≤ : (t m : Nat) → (t - m) ≤ t
monus-≤ zero    zero    = z≤n
monus-≤ zero    (suc m) = z≤n
monus-≤ (suc t) zero    = ≤-refl (suc t)
monus-≤ (suc t) (suc m) = ≤-step (monus-≤ t m)

------------------------------------------------------------------------
-- Commands, readings, exits

data Reading : Set where
  counted : Nat → Reading
  failed  : Reading

data Command : Set where
  init      : Nat → Command
  init-from : Reading → Command
  attempt   : Command
  update    : Reading → Command
  verify    : Command
  show      : Command

-- Exit codes 0, 1, 3, 4 (2 is a usage error, outside the model).
data Exit : Set where
  ok refused tripped unmeasured : Exit

------------------------------------------------------------------------
-- The step function

-- bumpOrTrip: every attempt and update is charged first.
charge : TaskState → TaskState
charge (task t c a st) = task t c (suc a) st

-- The breaker trips when the charged count exceeds totalItems + attemptSlack (5).
trips : TaskState → Bool
trips (task t c a st) = (t + 5) < suc a

stop : TaskState → TaskState
stop (task t c a st) = task t c a emergency-stop

Continue : Set
Continue = TaskState → TaskState × Exit

tripOr : Bool → TaskState → Continue → TaskState × Exit
tripOr true  s′ k = stop s′ , tripped
tripOr false s′ k = k s′

-- refuseIfStopped, then bumpOrTrip, then the command's own work.
guarded : Status → TaskState → Continue → TaskState × Exit
guarded emergency-stop s k = s , refused
guarded running        s k = tripOr (trips s) (charge s) k
guarded complete       s k = tripOr (trips s) (charge s) k

charged : Continue
charged s′ = s′ , ok

measured : Nat → Continue
measured m (task t c a st) = task t (t - m) a (derive m) , ok

unconfirmed : Continue
unconfirmed (task t c a st) = task t c a (demote st) , unmeasured

-- What an update does once charged, by reading.
continuation : Reading → Continue
continuation (counted m) = measured m
continuation failed      = unconfirmed

step : Command → TaskState → TaskState × Exit
step (init n)                s = task n 0 0 running , ok
step (init-from (counted n)) s = task n 0 0 running , ok
step (init-from failed)      s = s , refused
step attempt                 s = guarded (status s) s charged
step (update (counted m))    s = guarded (status s) s (measured m)
step (update failed)         s = guarded (status s) s unconfirmed
step verify                  s = s , ok
step show                    s = s , ok

after : Command → TaskState → TaskState
after cmd s = fst (step cmd s)

------------------------------------------------------------------------
-- THE GUARANTEE

running≢complete : ¬ (running ≡ complete)
running≢complete ()

stop≢complete : ¬ (emergency-stop ≡ complete)
stop≢complete ()

demote-not-complete : (st : Status) → ¬ (demote st ≡ complete)
demote-not-complete running        ()
demote-not-complete complete       ()
demote-not-complete emergency-stop ()

-- An update writes COMPLETE only when its reading is a counted zero.
update-complete-from : (b : Bool) (t c a : Nat) (st : Status) (r : Reading) →
  status (fst (tripOr b (task t c (suc a) st) (continuation r))) ≡ complete →
  r ≡ counted 0
update-complete-from true  t c a st r ()
update-complete-from false t c a st (counted zero)    e = refl
update-complete-from false t c a st (counted (suc m)) ()
update-complete-from false t c a st failed            e = absurd (demote-not-complete st e)

update-complete-only-from-zero : (r : Reading) (s : TaskState) →
  status (after (update r) s) ≡ complete → r ≡ counted 0
update-complete-only-from-zero (counted m) (task t c a emergency-stop) ()
update-complete-only-from-zero (counted m) (task t c a running)  e =
  update-complete-from ((t + 5) < suc a) t c a running (counted m) e
update-complete-only-from-zero (counted m) (task t c a complete) e =
  update-complete-from ((t + 5) < suc a) t c a complete (counted m) e
update-complete-only-from-zero failed (task t c a emergency-stop) ()
update-complete-only-from-zero failed (task t c a running)  e =
  update-complete-from ((t + 5) < suc a) t c a running failed e
update-complete-only-from-zero failed (task t c a complete) e =
  update-complete-from ((t + 5) < suc a) t c a complete failed e

init-never-complete : (n : Nat) (s : TaskState) → status (after (init n) s) ≡ running
init-never-complete n s = refl

-- An attempt never introduces COMPLETE: it keeps the status, or stops.
attempt-keeps : (b : Bool) (t c a : Nat) (st : Status) →
  status (fst (tripOr b (task t c (suc a) st) charged)) ≡ complete → st ≡ complete
attempt-keeps true  t c a st ()
attempt-keeps false t c a st e = e

-- THE GUARANTEE: no command introduces COMPLETE except an update whose
-- reading is a counted zero. Everything else either finds COMPLETE already
-- there or does not write it.
guarantee : (cmd : Command) (s : TaskState) → status (after cmd s) ≡ complete →
  (status s ≡ complete) ⊎ (cmd ≡ update (counted 0))
guarantee (init n)                s ()
guarantee (init-from (counted n)) s ()
guarantee (init-from failed)      s e = inl e
guarantee attempt (task t c a emergency-stop) e = inl e
guarantee attempt (task t c a running)  e =
  inl (attempt-keeps ((t + 5) < suc a) t c a running e)
guarantee attempt (task t c a complete) e = inl refl
guarantee (update r) s e = inr (cong update (update-complete-only-from-zero r s e))
guarantee verify s e = inl e
guarantee show   s e = inl e

------------------------------------------------------------------------
-- Regress and refuse

-- A recorded COMPLETE and a non-zero count: the engine writes RUNNING.
regress : (t c a k : Nat) → ((t + 5) < suc a) ≡ false →
  status (after (update (counted (suc k))) (task t c a complete)) ≡ running
regress t c a k e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false →
       status (fst (tripOr b (task t c (suc a) complete) (measured (suc k)))) ≡ running
  go false refl = refl

-- A recorded COMPLETE and no count: demoted, attempt charged, nothing derived.
refuse-demotes : (t c a : Nat) → ((t + 5) < suc a) ≡ false →
  step (update failed) (task t c a complete) ≡ (task t c (suc a) running , unmeasured)
refuse-demotes t c a e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false →
       tripOr b (task t c (suc a) complete) unconfirmed ≡ (task t c (suc a) running , unmeasured)
  go false refl = refl

nonzero-not-complete : (k : Nat) (s : TaskState) →
  ¬ (status (after (update (counted (suc k))) s) ≡ complete)
nonzero-not-complete k s e with update-complete-only-from-zero (counted (suc k)) s e
... | ()

------------------------------------------------------------------------
-- The attempt budget

attempt-charges : (t c a : Nat) (st : Status) → ¬ (st ≡ emergency-stop) →
  ((t + 5) < suc a) ≡ false → attempts (after attempt (task t c a st)) ≡ suc a
attempt-charges t c a emergency-stop ns e = absurd (ns refl)
attempt-charges t c a running  ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → attempts (fst (tripOr b (task t c (suc a) running) charged)) ≡ suc a
  go false refl = refl
attempt-charges t c a complete ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → attempts (fst (tripOr b (task t c (suc a) complete) charged)) ≡ suc a
  go false refl = refl

update-charges : (r : Reading) (t c a : Nat) (st : Status) → ¬ (st ≡ emergency-stop) →
  ((t + 5) < suc a) ≡ false → attempts (after (update r) (task t c a st)) ≡ suc a
update-charges r t c a emergency-stop ns e = absurd (ns refl)
update-charges (counted m) t c a running  ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → attempts (fst (tripOr b (task t c (suc a) running) (measured m))) ≡ suc a
  go false refl = refl
update-charges (counted m) t c a complete ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → attempts (fst (tripOr b (task t c (suc a) complete) (measured m))) ≡ suc a
  go false refl = refl
update-charges failed t c a running  ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → attempts (fst (tripOr b (task t c (suc a) running) unconfirmed)) ≡ suc a
  go false refl = refl
update-charges failed t c a complete ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → attempts (fst (tripOr b (task t c (suc a) complete) unconfirmed)) ≡ suc a
  go false refl = refl

-- Past totalItems + 5 the breaker writes EMERGENCY_STOP (exit 3).
trip-on : (t c a : Nat) (st : Status) (k : Continue) → ((t + 5) < suc a) ≡ true →
  tripOr ((t + 5) < suc a) (task t c (suc a) st) k ≡ (task t c (suc a) emergency-stop , tripped)
trip-on t c a st k e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ true → tripOr b (task t c (suc a) st) k ≡ (task t c (suc a) emergency-stop , tripped)
  go true refl = refl

attempt-trips : (t c a : Nat) → ((t + 5) < suc a) ≡ true →
  step attempt (task t c a running) ≡ (task t c (suc a) emergency-stop , tripped)
attempt-trips t c a = trip-on t c a running charged

update-trips : (t c a m : Nat) → ((t + 5) < suc a) ≡ true →
  step (update (counted m)) (task t c a complete) ≡ (task t c (suc a) emergency-stop , tripped)
update-trips t c a m = trip-on t c a complete (measured m)

-- EMERGENCY_STOP is terminal for work: attempt and update are refused (exit 1).
stop-refuses-attempt : (t c a : Nat) →
  step attempt (task t c a emergency-stop) ≡ (task t c a emergency-stop , refused)
stop-refuses-attempt t c a = refl

stop-refuses-update : (r : Reading) (t c a : Nat) →
  step (update r) (task t c a emergency-stop) ≡ (task t c a emergency-stop , refused)
stop-refuses-update (counted m) t c a = refl
stop-refuses-update failed      t c a = refl

-- Commands that are not a deliberate reset (init, a counted init-from).
data Work : Command → Set where
  w-attempt : Work attempt
  w-update  : (r : Reading) → Work (update r)
  w-verify  : Work verify
  w-show    : Work show

data AllWork : List Command → Set where
  []  : AllWork []
  _∷_ : {c : Command} {cs : List Command} → Work c → AllWork cs → AllWork (c ∷ cs)

run : List Command → TaskState → TaskState
run []         s = s
run (c ∷ cs)   s = run cs (after c s)

stopped-fixed : {c : Command} → Work c → (t d a : Nat) →
  after c (task t d a emergency-stop) ≡ task t d a emergency-stop
stopped-fixed w-attempt             t d a = refl
stopped-fixed (w-update (counted m)) t d a = refl
stopped-fixed (w-update failed)     t d a = refl
stopped-fixed w-verify              t d a = refl
stopped-fixed w-show                t d a = refl

stop-absorbs : (cs : List Command) → AllWork cs → (t d a : Nat) →
  run cs (task t d a emergency-stop) ≡ task t d a emergency-stop
stop-absorbs []       []       t d a = refl
stop-absorbs (c ∷ cs) (w ∷ ws) t d a =
  trans (cong (run cs) (stopped-fixed w t d a)) (stop-absorbs cs ws t d a)

------------------------------------------------------------------------
-- Read-only commands and resets

verify-read-only : (s : TaskState) → step verify s ≡ (s , ok)
verify-read-only s = refl

show-read-only : (s : TaskState) → step show s ≡ (s , ok)
show-read-only s = refl

init-resets : (n : Nat) (s : TaskState) → step (init n) s ≡ (task n 0 0 running , ok)
init-resets n s = refl

init-from-measures : (n : Nat) (s : TaskState) →
  step (init-from (counted n)) s ≡ (task n 0 0 running , ok)
init-from-measures n s = refl

init-from-failed-unchanged : (s : TaskState) → step (init-from failed) s ≡ (s , refused)
init-from-failed-unchanged s = refl

------------------------------------------------------------------------
-- Invariants preserved by every command

-- The budget: a state that is not stopped has attempts <= totalItems + 5.
Within : TaskState → Set
Within s = (status s ≡ emergency-stop) ⊎ (attempts s ≤ totalItems s + 5)

within-charged : (t c a : Nat) (st : Status) (k : Continue) →
  ((s′ : TaskState) → totalItems (fst (k s′)) ≡ totalItems s′) →
  ((s′ : TaskState) → attempts (fst (k s′)) ≡ attempts s′) →
  (b : Bool) → ((t + 5) < suc a) ≡ b → Within (fst (tripOr b (task t c (suc a) st) k))
within-charged t c a st k tot att true  e = inl refl
within-charged t c a st k tot att false e =
  inr (subst2 (λ x y → x ≤ y + 5)
              (sym (att (task t c (suc a) st)))
              (sym (tot (task t c (suc a) st)))
              (<-false (t + 5) (suc a) e))
  where
  subst2 : {A B : Set} (P : A → B → Set) {x x′ : A} {y y′ : B} →
           x ≡ x′ → y ≡ y′ → P x y → P x′ y′
  subst2 P refl refl p = p

charged-tot : (s′ : TaskState) → totalItems (fst (charged s′)) ≡ totalItems s′
charged-tot s′ = refl
charged-att : (s′ : TaskState) → attempts (fst (charged s′)) ≡ attempts s′
charged-att s′ = refl
measured-tot : (m : Nat) (s′ : TaskState) → totalItems (fst (measured m s′)) ≡ totalItems s′
measured-tot m (task t c a st) = refl
measured-att : (m : Nat) (s′ : TaskState) → attempts (fst (measured m s′)) ≡ attempts s′
measured-att m (task t c a st) = refl
unconfirmed-tot : (s′ : TaskState) → totalItems (fst (unconfirmed s′)) ≡ totalItems s′
unconfirmed-tot (task t c a st) = refl
unconfirmed-att : (s′ : TaskState) → attempts (fst (unconfirmed s′)) ≡ attempts s′
unconfirmed-att (task t c a st) = refl

within-guarded : (t c a : Nat) (st : Status) (k : Continue) →
  ((s′ : TaskState) → totalItems (fst (k s′)) ≡ totalItems s′) →
  ((s′ : TaskState) → attempts (fst (k s′)) ≡ attempts s′) →
  Within (task t c a st) → Within (fst (guarded st (task t c a st) k))
within-guarded t c a emergency-stop k tot att w = w
within-guarded t c a running  k tot att w = within-charged t c a running  k tot att ((t + 5) < suc a) refl
within-guarded t c a complete k tot att w = within-charged t c a complete k tot att ((t + 5) < suc a) refl

within-preserved : (cmd : Command) (s : TaskState) → Within s → Within (after cmd s)
within-preserved (init n)                s w = inr z≤n
within-preserved (init-from (counted n)) s w = inr z≤n
within-preserved (init-from failed)      s w = w
within-preserved attempt (task t c a st) w =
  within-guarded t c a st charged charged-tot charged-att w
within-preserved (update (counted m)) (task t c a st) w =
  within-guarded t c a st (measured m) (measured-tot m) (measured-att m) w
within-preserved (update failed) (task t c a st) w =
  within-guarded t c a st unconfirmed unconfirmed-tot unconfirmed-att w
within-preserved verify s w = w
within-preserved show   s w = w

-- completed never exceeds totalItems.
Bounded : TaskState → Set
Bounded s = completed s ≤ totalItems s

bounded-tripOr : (b : Bool) (t c a : Nat) (st : Status) (k : Continue) →
  Bounded (task t c (suc a) st) → Bounded (fst (k (task t c (suc a) st))) →
  Bounded (fst (tripOr b (task t c (suc a) st) k))
bounded-tripOr true  t c a st k p q = p
bounded-tripOr false t c a st k p q = q

bounded-preserved : (cmd : Command) (s : TaskState) → Bounded s → Bounded (after cmd s)
bounded-preserved (init n)                s p = z≤n
bounded-preserved (init-from (counted n)) s p = z≤n
bounded-preserved (init-from failed)      s p = p
bounded-preserved attempt (task t c a emergency-stop) p = p
bounded-preserved attempt (task t c a running)  p = bounded-tripOr ((t + 5) < suc a) t c a running  charged p p
bounded-preserved attempt (task t c a complete) p = bounded-tripOr ((t + 5) < suc a) t c a complete charged p p
bounded-preserved (update (counted m)) (task t c a emergency-stop) p = p
bounded-preserved (update (counted m)) (task t c a running)  p =
  bounded-tripOr ((t + 5) < suc a) t c a running  (measured m) p (monus-≤ t m)
bounded-preserved (update (counted m)) (task t c a complete) p =
  bounded-tripOr ((t + 5) < suc a) t c a complete (measured m) p (monus-≤ t m)
bounded-preserved (update failed) (task t c a emergency-stop) p = p
bounded-preserved (update failed) (task t c a running)  p = bounded-tripOr ((t + 5) < suc a) t c a running  unconfirmed p p
bounded-preserved (update failed) (task t c a complete) p = bounded-tripOr ((t + 5) < suc a) t c a complete unconfirmed p p
bounded-preserved verify s p = p
bounded-preserved show   s p = p

------------------------------------------------------------------------
-- The update branches are Fibre's

agrees-update : (t c a m : Nat) (st : Status) → ¬ (st ≡ emergency-stop) →
  ((t + 5) < suc a) ≡ false → after (update (counted m)) (task t c a st) ≡ fibre-update (task t c a st) m
agrees-update t c a m emergency-stop ns e = absurd (ns refl)
agrees-update t c a m running  ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → fst (tripOr b (task t c (suc a) running) (measured m)) ≡ fibre-update (task t c a running) m
  go false refl = refl
agrees-update t c a m complete ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → fst (tripOr b (task t c (suc a) complete) (measured m)) ≡ fibre-update (task t c a complete) m
  go false refl = refl

agrees-refuse : (t c a : Nat) (st : Status) → ¬ (st ≡ emergency-stop) →
  ((t + 5) < suc a) ≡ false → after (update failed) (task t c a st) ≡ refuse (task t c a st)
agrees-refuse t c a emergency-stop ns e = absurd (ns refl)
agrees-refuse t c a running  ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → fst (tripOr b (task t c (suc a) running) unconfirmed) ≡ refuse (task t c a running)
  go false refl = refl
agrees-refuse t c a complete ns e = go ((t + 5) < suc a) e
  where
  go : (b : Bool) → b ≡ false → fst (tripOr b (task t c (suc a) complete) unconfirmed) ≡ refuse (task t c a complete)
  go false refl = refl

------------------------------------------------------------------------
-- The Incident

-- Today's engine on the Incident record: measured 15272, RUNNING, nothing done.
incident : step (update (counted 15272)) (task 16 16 0 complete) ≡ (task 16 0 1 running , ok)
incident = refl

-- The original engine (root commit 4c91e71): `update <remaining>` took the
-- number from the caller, charged no attempt, and wrote COMPLETE when it was 0.
original-update : Nat → TaskState → TaskState
original-update zero    (task t c a st) = task t t a complete
original-update (suc r) (task t c a st) = task t (t - suc r) a st

-- A typed 0 was enough: the original engine wrote 16 / 16 / 0 / COMPLETE with
-- no measurement at all, which no command of the model above can do
-- (guarantee).
incident-original : original-update 0 (task 16 0 0 running) ≡ task 16 16 0 complete
incident-original = refl

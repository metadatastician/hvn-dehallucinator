{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Haruspex: the dehallucinator's check, run before a prompt is sent
-- (docs/proposals/HARUSPEX.adoc, ledger row HD-H).
--
-- Consumes residual-evidence-types by pin, never by re-declaration:
--   hyperpolymath/residual-evidence-types @ 97244f5cb63bd6697caff261b187b62e9788b692
--   (scripts/fetch-siblings.sh puts it in _build/dependencies).
--
-- A prompt asks a question of a context. The author declares the context as a
-- finite Schema: the readings it could have, what each reading shows, and a
-- decidable equality on what is shown. The Prompt says what the context will
-- show, the assumptions it states (decidable predicates on readings) and what
-- it asks: a yes/no claim or a value. `haruspex` is a total function with no
-- model call. It answers with one of three outputs:
--
--   sound  a certificate: a case exists and every candidate satisfies the
--          claim (entailed) or has one value (identified);
--   epi    a witness pair: two candidates that both fit and disagree on what
--          was asked (unresolved / unidentified);
--   empty  a refutation: every candidate refutes the claim (refuted), or no
--          reading fits the context at all (inconsistent / no-candidate).
--
-- Each output carries its proof, stated in the Core vocabulary of
-- residual-evidence-types (Candidate, Case, Holds, Identified, Refuted,
-- Disagreeing). The checker generalises the certified finite checker
-- (ResidualEvidence.Finite.Checker) from its fixed explorer model to a declared
-- schema; HaruspexExplorer shows that on the explorer's own model the two
-- decide the same candidates and the same verdicts on all 546 configurations.
--
-- As in the certified checker, the enumeration's scope is the first assumption
-- of the evidence (`Listed`): a candidate is a reading the schema lists. A
-- verdict transfers to an actual reading only with every assumption supplied,
-- the listing included (actual-sound); for a schema whose listing is complete,
-- that premise is discharged once (listing-complete-sound).
--
-- Checked by scripts/check-agda-kernel.sh with Agda 2.6.3 under
-- --safe --without-K --no-libraries --ignore-interfaces --double-check.

module Haruspex where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
  using (Candidate; Case; inhabited; Holds; Identified; actual-world-sound)
open import ResidualEvidence.Context using (Ctx; ⟦_⟧)
open import ResidualEvidence.Revision
  using (Refuted; Disagreeing; refuted-not-holds; disagreeing-not-identified)
open import ResidualEvidence.Finite.Int using (_∈_; here; there; bool-clash)
open import ResidualEvidence.Finite.Row
  using (Verdict; entailed; refuted; unresolved; inconsistent;
         IdStatus; identified; unidentified; no-candidate)
open import ResidualEvidence.Finite.Checker using (not; _∧_; _∨_; classify)
open import ResidualEvidence.Finite.Soundness
  using (absurd; _⊎_; inl; inr; ∧-sound; ∧-complete; ∨-left; ∨-right; ∨-false;
         not-true; not-false;
         classify-entailed; classify-refuted; classify-unresolved;
         classify-consistent; classify-false)

------------------------------------------------------------------------
-- The declared context and the prompt

record Schema : Set₁ where
  field
    Reading    : Set
    readings   : List Reading                  -- the declared enumeration
    Shown      : Set
    shows      : Reading → Shown               -- the observation
    _≟_        : Shown → Shown → Bool
    ≟-sound    : ∀ a b → (a ≟ b) ≡ true → a ≡ b
    ≟-complete : ∀ a b → a ≡ b → (a ≟ b) ≡ true

-- A value query with a decidable equality on its values.
record Query (R : Set) : Set₁ where
  field
    Value       : Set
    value       : R → Value
    _==_        : Value → Value → Bool
    ==-sound    : ∀ a b → (a == b) ≡ true → a ≡ b
    ==-complete : ∀ a b → a ≡ b → (a == b) ≡ true

data Ask (R : Set) : Set₁ where
  claim : (R → Bool) → Ask R      -- "confirm that ..."
  query : Query R → Ask R         -- "report the value of ..."

record Prompt (S : Schema) : Set₁ where
  field
    shown       : Schema.Shown S                      -- what the prompt carries
    assumptions : List (Schema.Reading S → Bool)      -- Γ, decidable
    ask         : Ask (Schema.Reading S)

data Kind : Set where
  Sound Epi Empty : Kind

------------------------------------------------------------------------
-- Lists (generic; the certified checker's versions are fixed to its worlds)

keepIf : ∀ {A : Set} → Bool → A → List A → List A
keepIf true  x xs = x ∷ xs
keepIf false x xs = xs

filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = keepIf (p x) x (filter p xs)

anyOf : ∀ {A : Set} → (A → Bool) → List A → Bool
anyOf p [] = false
anyOf p (x ∷ xs) = p x ∨ anyOf p xs

allOf : ∀ {A : Set} → (A → Bool) → List A → Bool
allOf p [] = true
allOf p (x ∷ xs) = p x ∧ allOf p xs

∈-head : ∀ {A : Set} {x y : A} {xs} → x ≡ y → x ∈ (y ∷ xs)
∈-head refl = here

∈-nil : ∀ {A : Set} {x : A} {xs} → xs ≡ [] → x ∈ xs → ⊥
∈-nil refl ()

not-of-true : ∀ b → b ≡ true → not b ≡ false
not-of-true true refl = refl

keepIf-∈ : ∀ {A : Set} b (y : A) ys x → x ∈ keepIf b y ys →
  ((b ≡ true) × (x ≡ y)) ⊎ (x ∈ ys)
keepIf-∈ true  y ys _ here      = inl (refl , refl)
keepIf-∈ true  y ys x (there m) = inr m
keepIf-∈ false y ys x m         = inr m

keepIf-here : ∀ {A : Set} b (y : A) ys → b ≡ true → y ∈ keepIf b y ys
keepIf-here true y ys refl = here

keepIf-there : ∀ {A : Set} b (y : A) ys x → x ∈ ys → x ∈ keepIf b y ys
keepIf-there true  y ys x m = there m
keepIf-there false y ys x m = m

filter-sound : ∀ {A : Set} (p : A → Bool) xs x → x ∈ filter p xs → (x ∈ xs) × (p x ≡ true)
filter-step : ∀ {A : Set} (p : A → Bool) y ys x →
  ((p y ≡ true) × (x ≡ y)) ⊎ (x ∈ filter p ys) → (x ∈ (y ∷ ys)) × (p x ≡ true)
filter-sound p []       x ()
filter-sound p (y ∷ ys) x m = filter-step p y ys x (keepIf-∈ (p y) y (filter p ys) x m)
filter-step p y ys x (inl (e , eq)) = ∈-head eq , trans (cong p eq) e
filter-step p y ys x (inr m) = there (fst r) , snd r
  where r = filter-sound p ys x m

filter-complete : ∀ {A : Set} (p : A → Bool) xs x → x ∈ xs → p x ≡ true → x ∈ filter p xs
filter-complete p (y ∷ ys) _ here      e = keepIf-here (p y) y (filter p ys) e
filter-complete p (y ∷ ys) x (there m) e =
  keepIf-there (p y) y (filter p ys) x (filter-complete p ys x m e)

any-true : ∀ {A : Set} (p : A → Bool) xs → anyOf p xs ≡ true → Σ A (λ x → (x ∈ xs) × (p x ≡ true))
any-step : ∀ {A : Set} (p : A → Bool) x xs b → p x ≡ b → (b ∨ anyOf p xs) ≡ true →
  Σ A (λ y → (y ∈ (x ∷ xs)) × (p y ≡ true))
any-true p []       ()
any-true p (x ∷ xs) e = any-step p x xs (p x) refl e
any-step p x xs true  e _ = x , here , e
any-step p x xs false _ e = fst r , there (fst (snd r)) , snd (snd r)
  where r = any-true p xs e

any-false : ∀ {A : Set} (p : A → Bool) xs x → anyOf p xs ≡ false → x ∈ xs → p x ≡ false
any-false p (y ∷ ys) _ e here      = ∨-left (p y) (anyOf p ys) e
any-false p (y ∷ ys) x e (there m) = any-false p ys x (∨-right (p y) (anyOf p ys) e) m

none-any : ∀ {A : Set} (p : A → Bool) xs → (∀ x → x ∈ xs → p x ≡ false) → anyOf p xs ≡ false
none-any p []       h = refl
none-any p (x ∷ xs) h = ∨-false (h x here) (none-any p xs (λ y m → h y (there m)))

all-true : ∀ {A : Set} (p : A → Bool) xs x → allOf p xs ≡ true → x ∈ xs → p x ≡ true
all-true p (y ∷ ys) _ e here      = fst (∧-sound (p y) (allOf p ys) e)
all-true p (y ∷ ys) x e (there m) = all-true p ys x (snd (∧-sound (p y) (allOf p ys) e)) m

all-complete : ∀ {A : Set} (p : A → Bool) xs → (∀ x → x ∈ xs → p x ≡ true) → allOf p xs ≡ true
all-complete p []       h = refl
all-complete p (x ∷ xs) h = ∧-complete (h x here) (all-complete p xs (λ y m → h y (there m)))

all-false : ∀ {A : Set} (p : A → Bool) xs → allOf p xs ≡ false → Σ A (λ x → (x ∈ xs) × (p x ≡ false))
all-step : ∀ {A : Set} (p : A → Bool) x xs b → p x ≡ b → (b ∧ allOf p xs) ≡ false →
  Σ A (λ y → (y ∈ (x ∷ xs)) × (p y ≡ false))
all-false p []       ()
all-false p (x ∷ xs) e = all-step p x xs (p x) refl e
all-step p x xs false e _ = x , here , e
all-step p x xs true  _ e = fst r , there (fst (snd r)) , snd (snd r)
  where r = all-false p xs e

------------------------------------------------------------------------
-- Verdicts on a list of candidates

presenceOf : ∀ {A : Set} → (A → Bool) → List A → Verdict
presenceOf P [] = inconsistent
presenceOf P (x ∷ xs) = classify (anyOf P (x ∷ xs)) (anyOf (λ y → not (P y)) (x ∷ xs))

sameAs : Bool → IdStatus
sameAs true  = identified
sameAs false = unidentified

identityOf : ∀ {A : Set} → Query A → List A → IdStatus
identityOf q [] = no-candidate
identityOf q (x ∷ xs) = sameAs (allOf (λ y → Query._==_ q (Query.value q y) (Query.value q x)) xs)

presenceOf-entailed : ∀ {A : Set} (P : A → Bool) ws → presenceOf P ws ≡ entailed →
  anyOf (λ y → not (P y)) ws ≡ false
presenceOf-entailed P []       ()
presenceOf-entailed P (w ∷ ws) e =
  classify-entailed (anyOf P (w ∷ ws)) (anyOf (λ y → not (P y)) (w ∷ ws)) e

presenceOf-refuted : ∀ {A : Set} (P : A → Bool) ws → presenceOf P ws ≡ refuted → anyOf P ws ≡ false
presenceOf-refuted P []       ()
presenceOf-refuted P (w ∷ ws) e =
  fst (classify-refuted (anyOf P (w ∷ ws)) (anyOf (λ y → not (P y)) (w ∷ ws)) e)

presenceOf-unresolved : ∀ {A : Set} (P : A → Bool) ws → presenceOf P ws ≡ unresolved →
  (anyOf P ws ≡ true) × (anyOf (λ y → not (P y)) ws ≡ true)
presenceOf-unresolved P []       ()
presenceOf-unresolved P (w ∷ ws) e =
  classify-unresolved (anyOf P (w ∷ ws)) (anyOf (λ y → not (P y)) (w ∷ ws)) e

presenceOf-inconsistent : ∀ {A : Set} (P : A → Bool) ws → presenceOf P ws ≡ inconsistent → ws ≡ []
presenceOf-inconsistent P []       _ = refl
presenceOf-inconsistent P (w ∷ ws) e =
  absurd (classify-consistent (anyOf P (w ∷ ws)) (anyOf (λ y → not (P y)) (w ∷ ws)) e)

-- entailed and refuted are only ever decided over at least one candidate.
presenceOf-entailed-some : ∀ {A : Set} (P : A → Bool) ws → presenceOf P ws ≡ entailed → Σ A (λ x → x ∈ ws)
presenceOf-entailed-some P []       ()
presenceOf-entailed-some P (w ∷ ws) _ = w , here

presenceOf-refuted-some : ∀ {A : Set} (P : A → Bool) ws → presenceOf P ws ≡ refuted → Σ A (λ x → x ∈ ws)
presenceOf-refuted-some P []       ()
presenceOf-refuted-some P (w ∷ ws) _ = w , here

presenceOf-complete : ∀ {A : Set} (P : A → Bool) ws → Σ A (λ x → x ∈ ws) →
  anyOf (λ y → not (P y)) ws ≡ false → presenceOf P ws ≡ entailed
presenceOf-complete P []       (x , ()) _
presenceOf-complete P (w ∷ ws) _        e = classify-false (anyOf P (w ∷ ws)) e

sameAs-identified : ∀ b → sameAs b ≡ identified → b ≡ true
sameAs-identified true  _ = refl
sameAs-identified false ()

sameAs-unidentified : ∀ b → sameAs b ≡ unidentified → b ≡ false
sameAs-unidentified true  ()
sameAs-unidentified false _ = refl

sameAs-some : ∀ b → ¬ (sameAs b ≡ no-candidate)
sameAs-some true  ()
sameAs-some false ()

-- Every candidate agrees with the first on the queried value.
head-agrees : ∀ {A : Set} (q : Query A) x xs →
  allOf (λ y → Query._==_ q (Query.value q y) (Query.value q x)) xs ≡ true →
  ∀ y → y ∈ (x ∷ xs) → Query.value q y ≡ Query.value q x
head-agrees q x xs e _ here      = refl
head-agrees q x xs e y (there m) =
  Query.==-sound q (Query.value q y) (Query.value q x)
    (all-true (λ z → Query._==_ q (Query.value q z) (Query.value q x)) xs y e m)

identityOf-identified : ∀ {A : Set} (q : Query A) ws → identityOf q ws ≡ identified →
  Σ A (λ x → (x ∈ ws) × (∀ y → y ∈ ws → Query.value q y ≡ Query.value q x))
identityOf-identified q []       ()
identityOf-identified q (x ∷ xs) e =
  x , here ,
  head-agrees q x xs
    (sameAs-identified (allOf (λ y → Query._==_ q (Query.value q y) (Query.value q x)) xs) e)

identityOf-unidentified : ∀ {A : Set} (q : Query A) ws → identityOf q ws ≡ unidentified →
  Σ A (λ x → Σ A (λ y → (x ∈ ws) × (y ∈ ws) × (¬ (Query.value q x ≡ Query.value q y))))
identityOf-unidentified q []       ()
identityOf-unidentified q (x ∷ xs) e =
  x , fst d , here , there (fst (snd d)) ,
  λ eq → bool-clash (snd (snd d)) (Query.==-complete q (Query.value q (fst d)) (Query.value q x) (sym eq))
  where
    agree = λ y → Query._==_ q (Query.value q y) (Query.value q x)
    d = all-false agree xs (sameAs-unidentified (allOf agree xs) e)

identityOf-none : ∀ {A : Set} (q : Query A) ws → identityOf q ws ≡ no-candidate → ws ≡ []
identityOf-none q []       _ = refl
identityOf-none q (x ∷ xs) e =
  absurd (sameAs-some (allOf (λ y → Query._==_ q (Query.value q y) (Query.value q x)) xs) e)

identityOf-complete : ∀ {A : Set} (q : Query A) ws v → (∀ y → y ∈ ws → Query.value q y ≡ v) →
  Σ A (λ x → x ∈ ws) → identityOf q ws ≡ identified
identityOf-complete q []       v h (x , ())
identityOf-complete q (x ∷ xs) v h _ =
  cong sameAs
    (all-complete (λ y → Query._==_ q (Query.value q y) (Query.value q x)) xs
      (λ y m → Query.==-complete q (Query.value q y) (Query.value q x)
                 (trans (h y (there m)) (sym (h x here)))))

------------------------------------------------------------------------
-- The check, for one declared schema

module Check (S : Schema) where
  open Schema S

  -- The enumeration's scope, stated as the first assumption (as InRange is
  -- for the certified checker).
  Listed : Reading → Set
  Listed x = x ∈ readings

  Assumed : List (Reading → Bool) → Ctx Reading
  Assumed [] = []
  Assumed (a ∷ as) = (λ x → a x ≡ true) ∷ Assumed as

  Evidence : List (Reading → Bool) → Ctx Reading
  Evidence as = Listed ∷ Assumed as

  HCandidate : Shown → List (Reading → Bool) → Set
  HCandidate r as = Candidate shows r ⟦ Evidence as ⟧

  HCase : Shown → List (Reading → Bool) → Set
  HCase r as = Case shows r ⟦ Evidence as ⟧

  -- A claim, and its refutation, as predicates on readings.
  Yes No : (Reading → Bool) → Reading → Set
  Yes P x = P x ≡ true
  No  P x = P x ≡ false

  ----------------------------------------------------------------------
  -- Enumeration

  holdsAll : List (Reading → Bool) → Reading → Bool
  holdsAll [] x = true
  holdsAll (a ∷ as) x = a x ∧ holdsAll as x

  fits : Shown → List (Reading → Bool) → Reading → Bool
  fits r as x = (shows x ≟ r) ∧ holdsAll as x

  candidates : Shown → List (Reading → Bool) → List Reading
  candidates r as = filter (fits r as) readings

  holdsAll-sound : ∀ as x → holdsAll as x ≡ true → ⟦ Assumed as ⟧ x
  holdsAll-sound []       x _ = tt
  holdsAll-sound (a ∷ as) x e = fst h , holdsAll-sound as x (snd h)
    where h = ∧-sound (a x) (holdsAll as x) e

  holdsAll-complete : ∀ as x → ⟦ Assumed as ⟧ x → holdsAll as x ≡ true
  holdsAll-complete []       x _          = refl
  holdsAll-complete (a ∷ as) x (p , rest) = ∧-complete p (holdsAll-complete as x rest)

  -- Obligation 1: a reading is a Core candidate for the prompt exactly when
  -- the enumeration produces it.
  candidate-∈ : ∀ r as (x : HCandidate r as) → fst x ∈ candidates r as
  candidate-∈ r as (x , observed , listed , assumed) =
    filter-complete (fits r as) readings x listed
      (∧-complete (≟-complete (shows x) r observed) (holdsAll-complete as x assumed))

  ∈-candidate : ∀ r as x → x ∈ candidates r as → HCandidate r as
  ∈-candidate r as x m =
    x , ≟-sound (shows x) r (fst f) , fst s , holdsAll-sound as x (snd f)
    where
      s = filter-sound (fits r as) readings x m
      f = ∧-sound (shows x ≟ r) (holdsAll as x) (snd s)

  ----------------------------------------------------------------------
  -- Verdicts

  presence : Shown → List (Reading → Bool) → (Reading → Bool) → Verdict
  presence r as P = presenceOf P (candidates r as)

  identity : Shown → List (Reading → Bool) → Query Reading → IdStatus
  identity r as q = identityOf q (candidates r as)

  ----------------------------------------------------------------------
  -- Obligation 2: each verdict is sound in the Core vocabulary

  entailed-sound : ∀ r as P → presence r as P ≡ entailed → (c : HCase r as) → Holds c (Yes P)
  entailed-sound r as P e c x =
    not-false (P (fst x))
      (any-false (λ y → not (P y)) (candidates r as) (fst x)
        (presenceOf-entailed P (candidates r as) e) (candidate-∈ r as x))

  entailed-case : ∀ r as P → presence r as P ≡ entailed → HCase r as
  entailed-case r as P e = inhabited (∈-candidate r as (fst h) (snd h))
    where h = presenceOf-entailed-some P (candidates r as) e

  refuted-sound : ∀ r as P → presence r as P ≡ refuted → (c : HCase r as) → Holds c (No P)
  refuted-sound r as P e c x =
    any-false P (candidates r as) (fst x) (presenceOf-refuted P (candidates r as) e) (candidate-∈ r as x)

  refuted-case : ∀ r as P → presence r as P ≡ refuted → HCase r as
  refuted-case r as P e = inhabited (∈-candidate r as (fst h) (snd h))
    where h = presenceOf-refuted-some P (candidates r as) e

  -- The refuting reading is positive data (Revision.Refuted), and ¬ Holds follows.
  refuted-refutes : ∀ r as P (e : presence r as P ≡ refuted) (c : HCase r as) → Refuted c (Yes P)
  refuted-refutes r as P e c =
    Case.witness c , λ yes → bool-clash (refuted-sound r as P e c (Case.witness c)) yes

  refuted-not-entailed : ∀ r as P → presence r as P ≡ refuted → (c : HCase r as) → ¬ Holds c (Yes P)
  refuted-not-entailed r as P e c = refuted-not-holds c (refuted-refutes r as P e c)

  unresolved-sound : ∀ r as P → presence r as P ≡ unresolved →
    Σ (HCandidate r as) (λ x → Yes P (fst x)) × Σ (HCandidate r as) (λ y → No P (fst y))
  unresolved-sound r as P e = supporting , counterexample
    where
      u = presenceOf-unresolved P (candidates r as) e
      s = any-true P (candidates r as) (fst u)
      a = any-true (λ y → not (P y)) (candidates r as) (snd u)
      supporting : Σ (HCandidate r as) (λ x → Yes P (fst x))
      supporting = ∈-candidate r as (fst s) (fst (snd s)) , snd (snd s)
      counterexample : Σ (HCandidate r as) (λ y → No P (fst y))
      counterexample = ∈-candidate r as (fst a) (fst (snd a)) , not-true (P (fst a)) (snd (snd a))

  inconsistent-sound : ∀ r as P → presence r as P ≡ inconsistent → ¬ HCase r as
  inconsistent-sound r as P e c =
    ∈-nil (presenceOf-inconsistent P (candidates r as) e) (candidate-∈ r as (Case.witness c))

  -- Completeness for Sound: whenever a certificate exists, Haruspex finds it.
  entailed-complete : ∀ r as P (c : HCase r as) → Holds c (Yes P) → presence r as P ≡ entailed
  entailed-complete r as P c holds =
    presenceOf-complete P (candidates r as)
      (fst (Case.witness c) , candidate-∈ r as (Case.witness c))
      (none-any (λ y → not (P y)) (candidates r as)
        (λ x m → not-of-true (P x) (holds (∈-candidate r as x m))))

  identified-sound : ∀ r as q → identity r as q ≡ identified →
    (c : HCase r as) → Identified c (Query.value q)
  identified-sound r as q e c = Query.value q (fst h) , λ x → snd (snd h) (fst x) (candidate-∈ r as x)
    where h = identityOf-identified q (candidates r as) e

  identified-case : ∀ r as q → identity r as q ≡ identified → HCase r as
  identified-case r as q e = inhabited (∈-candidate r as (fst h) (fst (snd h)))
    where h = identityOf-identified q (candidates r as) e

  unidentified-sound : ∀ r as q → identity r as q ≡ unidentified →
    Σ (HCase r as) (λ c → Disagreeing c (Query.value q))
  unidentified-sound r as q e =
    inhabited x , x , ∈-candidate r as (fst (snd d)) (fst (snd (snd (snd d)))) , snd (snd (snd (snd d)))
    where
      d = identityOf-unidentified q (candidates r as) e
      x = ∈-candidate r as (fst d) (fst (snd (snd d)))

  -- An Epi pair refutes identification for every case of the prompt.
  unidentified-refutes : ∀ r as q → identity r as q ≡ unidentified →
    (c : HCase r as) → ¬ Identified c (Query.value q)
  unidentified-refutes r as q e c =
    disagreeing-not-identified c (Query.value q) (snd (unidentified-sound r as q e))

  no-candidate-sound : ∀ r as q → identity r as q ≡ no-candidate → ¬ HCase r as
  no-candidate-sound r as q e c =
    ∈-nil (identityOf-none q (candidates r as) e) (candidate-∈ r as (Case.witness c))

  identified-complete : ∀ r as q (c : HCase r as) → Identified c (Query.value q) →
    identity r as q ≡ identified
  identified-complete r as q c (v , holds) =
    identityOf-complete q (candidates r as) v
      (λ y m → holds (∈-candidate r as y m))
      (fst (Case.witness c) , candidate-∈ r as (Case.witness c))

  ----------------------------------------------------------------------
  -- Applying a verdict to the actual context needs every assumption

  actual-sound : ∀ r as (c : HCase r as) (Q : Reading → Set) → Holds c Q →
    (actual : Reading) → shows actual ≡ r → Listed actual → ⟦ Assumed as ⟧ actual → Q actual
  actual-sound r as c Q holds actual observed listed assumed =
    actual-world-sound c holds actual observed (listed , assumed)

  -- When the declared listing is complete, the scope premise is discharged once.
  listing-complete-sound : ((x : Reading) → Listed x) →
    ∀ r as (c : HCase r as) (Q : Reading → Set) → Holds c Q →
    (actual : Reading) → shows actual ≡ r → ⟦ Assumed as ⟧ actual → Q actual
  listing-complete-sound complete r as c Q holds actual observed assumed =
    actual-sound r as c Q holds actual observed (complete actual) assumed

  ----------------------------------------------------------------------
  -- The three outputs

  Certificate Pair Refutation : Shown → List (Reading → Bool) → Ask Reading → Set
  Certificate r as (claim P) = Σ (HCase r as) (λ c → Holds c (Yes P))
  Certificate r as (query q) = Σ (HCase r as) (λ c → Identified c (Query.value q))
  Pair r as (claim P) = Σ (HCandidate r as) (λ x → Yes P (fst x)) × Σ (HCandidate r as) (λ y → No P (fst y))
  Pair r as (query q) = Σ (HCase r as) (λ c → Disagreeing c (Query.value q))
  Refutation r as (claim P) = Σ (HCase r as) (λ c → Holds c (No P)) ⊎ (¬ HCase r as)
  Refutation r as (query q) = ¬ HCase r as

  data Output (r : Shown) (as : List (Reading → Bool)) (a : Ask Reading) : Set where
    sound : Certificate r as a → Output r as a
    epi   : Pair r as a        → Output r as a
    empty : Refutation r as a  → Output r as a

  kind : ∀ {r as a} → Output r as a → Kind
  kind (sound _) = Sound
  kind (epi _)   = Epi
  kind (empty _) = Empty

  -- Total, and no model call: every branch is a verdict and its lemma.
  decide : (r : Shown) (as : List (Reading → Bool)) (a : Ask Reading) → Output r as a
  decide r as (claim P) with presence r as P in e
  ... | entailed     = sound (entailed-case r as P e , entailed-sound r as P e (entailed-case r as P e))
  ... | refuted      = empty (inl (refuted-case r as P e , refuted-sound r as P e (refuted-case r as P e)))
  ... | unresolved   = epi (unresolved-sound r as P e)
  ... | inconsistent = empty (inr (inconsistent-sound r as P e))
  decide r as (query q) with identity r as q in e
  ... | identified   = sound (identified-case r as q e , identified-sound r as q e (identified-case r as q e))
  ... | unidentified = epi (unidentified-sound r as q e)
  ... | no-candidate = empty (no-candidate-sound r as q e)

------------------------------------------------------------------------
-- The pre-flight check

Output : (S : Schema) → Prompt S → Set
Output S p = Check.Output S (Prompt.shown p) (Prompt.assumptions p) (Prompt.ask p)

haruspex : (S : Schema) (p : Prompt S) → Output S p
haruspex S p = Check.decide S (Prompt.shown p) (Prompt.assumptions p) (Prompt.ask p)

verdict : (S : Schema) → Prompt S → Kind
verdict S p = Check.kind S (haruspex S p)

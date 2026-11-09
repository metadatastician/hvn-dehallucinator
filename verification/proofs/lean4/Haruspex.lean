/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

The Lean recheck leg (standards PROOF-POLICY section 2) of the Haruspex
checker: verification/proofs/agda/Haruspex.agda, module Haruspex.Check.

Route: re-proved. The pinned Lambdapi release has no Lean exporter, so no
transport was possible. Each statement below restates the Agda statement of
the same name ('-' becomes '_'), over definitions that restate Agda's clause
for clause. The Core vocabulary of residual-evidence-types (Candidate, Case,
Holds, Identified, Refuted, Disagreeing, Ctx) is restated first, at the pin
97244f5cb63bd6697caff261b187b62e9788b692. The translation choices, and how
each statement was compared with Agda's, are recorded in
docs/status/RECHECK-CORRESPONDENCE.adoc.

Lean core only: no Mathlib, no Batteries, no axiom. The end of this file
prints the axioms of every theorem; scripts/check-recheck-legs.sh fails
unless each depends on none.

Checked with Lean 4.15.0.
-/

namespace Haruspex

/-! ResidualEvidence.Prelude, Finite.Int, Finite.Row, Finite.Checker -/

inductive Mem {α : Type} (x : α) : List α → Type where
  | here {xs : List α} : Mem x (x :: xs)
  | there {y : α} {xs : List α} : Mem x xs → Mem x (y :: xs)

inductive Verdict : Type where
  | entailed | refuted | unresolved | inconsistent
  deriving DecidableEq

inductive IdStatus : Type where
  | identified | unidentified | no_candidate
  deriving DecidableEq

def classify : Bool → Bool → Verdict
  | _,     false => .entailed
  | false, true  => .refuted
  | true,  true  => .unresolved

theorem bool_clash {b : Bool} (p : b = false) (q : b = true) : False := by
  cases p; cases q

def memNil {α : Type} {x : α} : Mem x [] → False := fun m => nomatch m

def memCons {α : Type} {x y : α} {ys : List α} : Mem x (y :: ys) → PSum (x = y) (Mem x ys)
  | .here => .inl rfl
  | .there m => .inr m

/-! ResidualEvidence.Core, Context, Revision -/

abbrev Candidate {W O : Type} (observe : W → O) (r : O) (E : W → Type) : Type :=
  (world : W) × PProd (observe world = r) (E world)

structure Case {W O : Type} (observe : W → O) (r : O) (E : W → Type) : Type where
  inhabited ::
  witness : Candidate observe r E

abbrev Holds {W O : Type} {observe : W → O} {r : O} {E : W → Type}
    (_c : Case observe r E) (P : W → Sort u) : Sort (imax 1 u) :=
  (x : Candidate observe r E) → P x.1

abbrev Identified {W O Q : Type} {observe : W → O} {r : O} {E : W → Type}
    (c : Case observe r E) (query : W → Q) : Type :=
  (value : Q) ×' Holds c (fun world => query world = value)

abbrev Refuted {W O : Type} {observe : W → O} {r : O} {E : W → Type}
    (_c : Case observe r E) (P : W → Sort u) : Type :=
  (x : Candidate observe r E) ×' (P x.1 → False)

abbrev Disagreeing {W O Q : Type} {observe : W → O} {r : O} {E : W → Type}
    (_c : Case observe r E) (query : W → Q) : Type :=
  (x : Candidate observe r E) ×' (y : Candidate observe r E) ×' (query x.1 = query y.1 → False)

def actual_world_sound {W O : Type} {observe : W → O} {r : O} {E : W → Type}
    {P : W → Sort u} (c : Case observe r E) (claim : Holds c P)
    (actual : W) (observed : observe actual = r) (evidence : E actual) : P actual :=
  claim ⟨actual, observed, evidence⟩

theorem refuted_not_holds {W O : Type} {observe : W → O} {r : O} {E : W → Type}
    {P : W → Sort u} (c : Case observe r E) (ref : Refuted c P) : Holds c P → False :=
  fun h => ref.2 (h ref.1)

theorem disagreeing_not_identified {W O Q : Type} {observe : W → O} {r : O}
    {E : W → Type} (c : Case observe r E) (query : W → Q)
    (d : Disagreeing c query) : Identified c query → False :=
  fun i => d.2.2 ((i.2 d.1).trans (i.2 d.2.1).symm)

abbrev Ctx (W : Type) : Type 1 := List (W → Type)

def denote {W : Type} : Ctx W → W → Type
  | [],     _     => Unit
  | P :: G, world => P world × denote G world

/-! Haruspex: the declared context and the prompt -/

structure Schema : Type 1 where
  Reading : Type
  readings : List Reading
  Shown : Type
  shows : Reading → Shown
  eqbShown : Shown → Shown → Bool
  eqbShown_sound : ∀ a b, eqbShown a b = true → a = b
  eqbShown_complete : ∀ a b, a = b → eqbShown a b = true

structure Query (R : Type) : Type 1 where
  Value : Type
  value : R → Value
  eqbValue : Value → Value → Bool
  eqbValue_sound : ∀ a b, eqbValue a b = true → a = b
  eqbValue_complete : ∀ a b, a = b → eqbValue a b = true

inductive Ask (R : Type) : Type 1 where
  | claim : (R → Bool) → Ask R
  | query : Query R → Ask R

inductive Kind : Type where
  | Sound | Epi | Empty
  deriving DecidableEq

/-! Lists -/

def keepIf {α : Type} : Bool → α → List α → List α
  | true,  x, xs => x :: xs
  | false, _, xs => xs

def filter {α : Type} (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => keepIf (p x) x (filter p xs)

def anyOf {α : Type} (p : α → Bool) : List α → Bool
  | []      => false
  | x :: xs => p x || anyOf p xs

def allOf {α : Type} (p : α → Bool) : List α → Bool
  | []      => true
  | x :: xs => p x && allOf p xs

theorem andb_sound : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true
  | true,  _, e => ⟨rfl, e⟩
  | false, _, e => by cases e

theorem andb_complete : ∀ {a b : Bool}, a = true → b = true → (a && b) = true
  | _, _, rfl, rfl => rfl

theorem orb_false : ∀ {a b : Bool}, a = false → b = false → (a || b) = false
  | _, _, rfl, rfl => rfl

theorem orb_left : ∀ a b : Bool, (a || b) = false → a = false
  | true,  _, e => by cases e
  | false, _, _ => rfl

theorem orb_right : ∀ a b : Bool, (a || b) = false → b = false
  | true,  _, e => by cases e
  | false, _, e => e

theorem not_true : ∀ b : Bool, (!b) = true → b = false
  | true,  e => by cases e
  | false, _ => rfl

theorem not_false : ∀ b : Bool, (!b) = false → b = true
  | true,  _ => rfl
  | false, e => by cases e

theorem not_of_true : ∀ b : Bool, b = true → (!b) = false
  | _, rfl => rfl

def keepIf_mem {α : Type} : (b : Bool) → (y : α) → (ys : List α) → (x : α) →
    Mem x (keepIf b y ys) → PSum (PProd (b = true) (x = y)) (Mem x ys)
  | true,  _, _, _, m => match memCons m with
    | .inl e  => .inl ⟨rfl, e⟩
    | .inr m' => .inr m'
  | false, _, _, _, m => .inr m

def keepIf_here {α : Type} : (b : Bool) → (y : α) → (ys : List α) → b = true → Mem y (keepIf b y ys)
  | true, _, _, _ => .here

def keepIf_there {α : Type} : (b : Bool) → (y : α) → (ys : List α) → (x : α) → Mem x ys →
    Mem x (keepIf b y ys)
  | true,  _, _, _, m => .there m
  | false, _, _, _, m => m

def filter_sound {α : Type} (p : α → Bool) : (xs : List α) → (x : α) →
    Mem x (filter p xs) → PProd (Mem x xs) (p x = true)
  | [],      _, m => (memNil m).elim
  | y :: ys, x, m =>
    match keepIf_mem (p y) y (filter p ys) x m with
    | .inl ⟨e, ex⟩ => by subst ex; exact ⟨.here, e⟩
    | .inr m' => let r := filter_sound p ys x m'; ⟨.there r.1, r.2⟩

def filter_complete {α : Type} (p : α → Bool) : (xs : List α) → (x : α) →
    Mem x xs → p x = true → Mem x (filter p xs)
  | y :: ys, _, .here,    e => keepIf_here (p y) y (filter p ys) e
  | y :: ys, x, .there m, e => keepIf_there (p y) y (filter p ys) x (filter_complete p ys x m e)

def any_true {α : Type} (p : α → Bool) : (xs : List α) →
    anyOf p xs = true → (x : α) × PProd (Mem x xs) (p x = true)
  | [],      e => by cases e
  | y :: ys, e =>
    match h : p y with
    | true  => ⟨y, .here, h⟩
    | false =>
      have e' : anyOf p ys = true := by
        have e0 : (p y || anyOf p ys) = true := e
        rw [h] at e0; exact e0
      let r := any_true p ys e'
      ⟨r.1, .there r.2.1, r.2.2⟩

theorem any_false {α : Type} (p : α → Bool) : (xs : List α) → (x : α) →
    anyOf p xs = false → Mem x xs → p x = false
  | y :: ys, _, e, .here    => orb_left (p y) (anyOf p ys) e
  | y :: ys, x, e, .there m => any_false p ys x (orb_right (p y) (anyOf p ys) e) m

theorem none_any {α : Type} (p : α → Bool) : (xs : List α) →
    ((x : α) → Mem x xs → p x = false) → anyOf p xs = false
  | [],      _ => rfl
  | y :: ys, h => orb_false (h y .here) (none_any p ys (fun z m => h z (.there m)))

theorem all_true {α : Type} (p : α → Bool) : (xs : List α) → (x : α) →
    allOf p xs = true → Mem x xs → p x = true
  | y :: ys, _, e, .here    => (andb_sound (p y) (allOf p ys) e).1
  | y :: ys, x, e, .there m => all_true p ys x (andb_sound (p y) (allOf p ys) e).2 m

theorem all_complete {α : Type} (p : α → Bool) : (xs : List α) →
    ((x : α) → Mem x xs → p x = true) → allOf p xs = true
  | [],      _ => rfl
  | y :: ys, h => andb_complete (h y .here) (all_complete p ys (fun z m => h z (.there m)))

def all_false {α : Type} (p : α → Bool) : (xs : List α) →
    allOf p xs = false → (x : α) × PProd (Mem x xs) (p x = false)
  | [],      e => by cases e
  | y :: ys, e =>
    match h : p y with
    | false => ⟨y, .here, h⟩
    | true  =>
      have e' : allOf p ys = false := by
        have e0 : (p y && allOf p ys) = false := e
        rw [h] at e0; exact e0
      let r := all_false p ys e'
      ⟨r.1, .there r.2.1, r.2.2⟩

/-! Verdicts on a list of candidates -/

def presenceOf {α : Type} (P : α → Bool) : List α → Verdict
  | []      => .inconsistent
  | x :: xs => classify (anyOf P (x :: xs)) (anyOf (fun y => !(P y)) (x :: xs))

def sameAs : Bool → IdStatus
  | true  => .identified
  | false => .unidentified

def agreesWith {α : Type} (q : Query α) (x : α) : α → Bool :=
  fun y => q.eqbValue (q.value y) (q.value x)

def identityOf {α : Type} (q : Query α) : List α → IdStatus
  | []      => .no_candidate
  | x :: xs => sameAs (allOf (agreesWith q x) xs)

theorem classify_entailed : ∀ a b, classify a b = .entailed → b = false
  | true,  false, _ => rfl
  | false, false, _ => rfl
  | false, true,  e => by cases e
  | true,  true,  e => by cases e

theorem classify_refuted : ∀ a b, classify a b = .refuted → a = false ∧ b = true
  | true,  false, e => by cases e
  | false, false, e => by cases e
  | false, true,  _ => ⟨rfl, rfl⟩
  | true,  true,  e => by cases e

theorem classify_unresolved : ∀ a b, classify a b = .unresolved → a = true ∧ b = true
  | true,  false, e => by cases e
  | false, false, e => by cases e
  | false, true,  e => by cases e
  | true,  true,  _ => ⟨rfl, rfl⟩

theorem classify_consistent : ∀ a b, classify a b = .inconsistent → False
  | true,  false, e => by cases e
  | false, false, e => by cases e
  | false, true,  e => by cases e
  | true,  true,  e => by cases e

theorem classify_false : ∀ a {b}, b = false → classify a b = .entailed
  | true,  _, rfl => rfl
  | false, _, rfl => rfl

theorem presenceOf_entailed {α : Type} (P : α → Bool) : ∀ ws,
    presenceOf P ws = .entailed → anyOf (fun y => !(P y)) ws = false
  | [],      e => by cases e
  | _ :: _, e => classify_entailed _ _ e

theorem presenceOf_refuted {α : Type} (P : α → Bool) : ∀ ws,
    presenceOf P ws = .refuted → anyOf P ws = false
  | [],      e => by cases e
  | _ :: _, e => (classify_refuted _ _ e).1

theorem presenceOf_unresolved {α : Type} (P : α → Bool) : ∀ ws,
    presenceOf P ws = .unresolved → anyOf P ws = true ∧ anyOf (fun y => !(P y)) ws = true
  | [],      e => by cases e
  | _ :: _, e => classify_unresolved _ _ e

theorem presenceOf_inconsistent {α : Type} (P : α → Bool) : ∀ ws,
    presenceOf P ws = .inconsistent → ws = []
  | [],      _ => rfl
  | _ :: _, e => (classify_consistent _ _ e).elim

def presenceOf_entailed_some {α : Type} (P : α → Bool) : ∀ ws,
    presenceOf P ws = .entailed → (x : α) × Mem x ws
  | [],      e => by cases e
  | w :: _,  _ => ⟨w, .here⟩

def presenceOf_refuted_some {α : Type} (P : α → Bool) : ∀ ws,
    presenceOf P ws = .refuted → (x : α) × Mem x ws
  | [],      e => by cases e
  | w :: _,  _ => ⟨w, .here⟩

theorem presenceOf_complete {α : Type} (P : α → Bool) : ∀ ws,
    (x : α) × Mem x ws → anyOf (fun y => !(P y)) ws = false → presenceOf P ws = .entailed
  | [],      ⟨_, m⟩, _ => (memNil m).elim
  | _ :: _, _,      e => classify_false _ e

theorem head_agrees {α : Type} (q : Query α) (x : α) (xs : List α)
    (e : allOf (agreesWith q x) xs = true) : ∀ y, Mem y (x :: xs) → q.value y = q.value x
  | _, .here    => rfl
  | y, .there m => q.eqbValue_sound _ _ (all_true _ xs y e m)

def identityOf_identified {α : Type} (q : Query α) : ∀ ws,
    identityOf q ws = .identified →
    (x : α) × PProd (Mem x ws) (∀ y, Mem y ws → q.value y = q.value x)
  | [],      e => by cases e
  | x :: xs, e =>
    match h : allOf (agreesWith q x) xs with
    | true  => ⟨x, .here, head_agrees q x xs h⟩
    | false => by
        have e0 : sameAs (allOf (agreesWith q x) xs) = .identified := e
        rw [h] at e0; cases e0

def identityOf_unidentified {α : Type} (q : Query α) : ∀ ws,
    identityOf q ws = .unidentified →
    (x : α) × (y : α) × PProd (Mem x ws) (PProd (Mem y ws) (q.value x = q.value y → False))
  | [],      e => by cases e
  | x :: xs, e =>
    match h : allOf (agreesWith q x) xs with
    | false =>
      let d := all_false (agreesWith q x) xs h
      ⟨x, d.1, .here, .there d.2.1,
        fun eq => bool_clash d.2.2 (q.eqbValue_complete _ _ eq.symm)⟩
    | true => by
        have e0 : sameAs (allOf (agreesWith q x) xs) = .unidentified := e
        rw [h] at e0; cases e0

theorem identityOf_none {α : Type} (q : Query α) : ∀ ws,
    identityOf q ws = .no_candidate → ws = []
  | [],      _ => rfl
  | x :: xs, e => by
      have e0 : sameAs (allOf (agreesWith q x) xs) = .no_candidate := e
      revert e0; cases allOf (agreesWith q x) xs <;> intro e0 <;> cases e0

theorem identityOf_complete {α : Type} (q : Query α) : ∀ ws (v : q.Value),
    (∀ y, Mem y ws → q.value y = v) → (x : α) × Mem x ws → identityOf q ws = .identified
  | [],      _, _, ⟨_, m⟩ => (memNil m).elim
  | x :: xs, _, h, _ =>
    have all : allOf (agreesWith q x) xs = true :=
      all_complete (agreesWith q x) xs
        (fun y m => q.eqbValue_complete _ _ ((h y (.there m)).trans (h x .here).symm))
    show sameAs (allOf (agreesWith q x) xs) = .identified by rw [all]; rfl

/-! The check, for one declared schema -/

namespace Check
variable (S : Schema)

abbrev Listed (x : S.Reading) : Type := Mem x S.readings

def Assumed : List (S.Reading → Bool) → Ctx S.Reading
  | []         => []
  | a :: asm'  => (fun x => PLift (a x = true)) :: Assumed asm'

abbrev Evidence (asm : List (S.Reading → Bool)) : Ctx S.Reading := Listed S :: Assumed S asm

abbrev HCandidate (r : S.Shown) (asm : List (S.Reading → Bool)) : Type :=
  Candidate S.shows r (denote (Evidence S asm))

abbrev HCase (r : S.Shown) (asm : List (S.Reading → Bool)) : Type :=
  Case S.shows r (denote (Evidence S asm))

abbrev Yes (P : S.Reading → Bool) (x : S.Reading) : Prop := P x = true
abbrev No (P : S.Reading → Bool) (x : S.Reading) : Prop := P x = false

def holdsAll : List (S.Reading → Bool) → S.Reading → Bool
  | [],        _ => true
  | a :: asm', x => a x && holdsAll asm' x

def fits (r : S.Shown) (asm : List (S.Reading → Bool)) (x : S.Reading) : Bool :=
  S.eqbShown (S.shows x) r && holdsAll S asm x

def candidates (r : S.Shown) (asm : List (S.Reading → Bool)) : List S.Reading :=
  filter (fits S r asm) S.readings

def holdsAll_sound : ∀ asm (x : S.Reading), holdsAll S asm x = true → denote (Assumed S asm) x
  | [],        _, _ => ()
  | _ :: asm', x, e =>
    let h := andb_sound _ _ e
    (⟨h.1⟩, holdsAll_sound asm' x h.2)

theorem holdsAll_complete : ∀ asm (x : S.Reading), denote (Assumed S asm) x → holdsAll S asm x = true
  | [],        _, _          => rfl
  | _ :: asm', x, (p, rest)  => andb_complete p.down (holdsAll_complete asm' x rest)

def candidate_mem (r : S.Shown) (asm : List (S.Reading → Bool)) :
    (x : HCandidate S r asm) → Mem x.1 (candidates S r asm)
  | ⟨x, observed, listed, assumed⟩ =>
    filter_complete (fits S r asm) S.readings x listed
      (andb_complete (S.eqbShown_complete _ _ observed) (holdsAll_complete S asm x assumed))

def mem_candidate (r : S.Shown) (asm : List (S.Reading → Bool)) (x : S.Reading)
    (m : Mem x (candidates S r asm)) : HCandidate S r asm :=
  let s := filter_sound (fits S r asm) S.readings x m
  let f := andb_sound _ _ s.2
  ⟨x, S.eqbShown_sound _ _ f.1, s.1, holdsAll_sound S asm x f.2⟩

def presence (r : S.Shown) (asm : List (S.Reading → Bool)) (P : S.Reading → Bool) : Verdict :=
  presenceOf P (candidates S r asm)

def identity (r : S.Shown) (asm : List (S.Reading → Bool)) (q : Query S.Reading) : IdStatus :=
  identityOf q (candidates S r asm)

theorem entailed_sound (r asm P) (e : presence S r asm P = .entailed) :
    ∀ c : HCase S r asm, Holds c (Yes S P) :=
  fun _ x => not_false _ (any_false _ (candidates S r asm) x.1
    (presenceOf_entailed P _ e) (candidate_mem S r asm x))

def entailed_case (r asm P) (e : presence S r asm P = .entailed) : HCase S r asm :=
  let h := presenceOf_entailed_some P (candidates S r asm) e
  ⟨mem_candidate S r asm h.1 h.2⟩

theorem refuted_sound (r asm P) (e : presence S r asm P = .refuted) :
    ∀ c : HCase S r asm, Holds c (No S P) :=
  fun _ x => any_false P (candidates S r asm) x.1 (presenceOf_refuted P _ e) (candidate_mem S r asm x)

def refuted_case (r asm P) (e : presence S r asm P = .refuted) : HCase S r asm :=
  let h := presenceOf_refuted_some P (candidates S r asm) e
  ⟨mem_candidate S r asm h.1 h.2⟩

def refuted_refutes (r asm P) (e : presence S r asm P = .refuted) (c : HCase S r asm) :
    Refuted c (Yes S P) :=
  ⟨c.witness, fun yes => bool_clash (refuted_sound S r asm P e c c.witness) yes⟩

theorem refuted_not_entailed (r asm P) (e : presence S r asm P = .refuted) (c : HCase S r asm) :
    Holds c (Yes S P) → False :=
  refuted_not_holds c (refuted_refutes S r asm P e c)

def unresolved_sound (r asm P) (e : presence S r asm P = .unresolved) :
    PProd ((x : HCandidate S r asm) ×' Yes S P x.1) ((y : HCandidate S r asm) ×' No S P y.1) :=
  let u := presenceOf_unresolved P (candidates S r asm) e
  let s := any_true P (candidates S r asm) u.1
  let a := any_true (fun y => !(P y)) (candidates S r asm) u.2
  ⟨⟨mem_candidate S r asm s.1 s.2.1, s.2.2⟩,
   ⟨mem_candidate S r asm a.1 a.2.1, not_true (P a.1) a.2.2⟩⟩

theorem inconsistent_sound (r asm P) (e : presence S r asm P = .inconsistent) :
    HCase S r asm → False := fun c => by
  have m := candidate_mem S r asm c.witness
  have z : candidates S r asm = [] := presenceOf_inconsistent P _ e
  rw [z] at m; exact memNil m

theorem entailed_complete (r asm P) (c : HCase S r asm) (holds : Holds c (Yes S P)) :
    presence S r asm P = .entailed :=
  presenceOf_complete P (candidates S r asm) ⟨c.witness.1, candidate_mem S r asm c.witness⟩
    (none_any (fun y => !(P y)) (candidates S r asm)
      (fun x m => not_of_true (P x) (holds (mem_candidate S r asm x m))))

def identified_sound (r asm q) (e : identity S r asm q = .identified) (c : HCase S r asm) :
    Identified c q.value :=
  let h := identityOf_identified q (candidates S r asm) e
  ⟨q.value h.1, fun x => h.2.2 x.1 (candidate_mem S r asm x)⟩

def identified_case (r asm q) (e : identity S r asm q = .identified) : HCase S r asm :=
  let h := identityOf_identified q (candidates S r asm) e
  ⟨mem_candidate S r asm h.1 h.2.1⟩

def unidentified_sound (r asm q) (e : identity S r asm q = .unidentified) :
    (c : HCase S r asm) ×' Disagreeing c q.value :=
  let d := identityOf_unidentified q (candidates S r asm) e
  let x := mem_candidate S r asm d.1 d.2.2.1
  ⟨⟨x⟩, x, mem_candidate S r asm d.2.1 d.2.2.2.1, d.2.2.2.2⟩

theorem unidentified_refutes (r asm q) (e : identity S r asm q = .unidentified) (c : HCase S r asm) :
    Identified c q.value → False :=
  disagreeing_not_identified c q.value (unidentified_sound S r asm q e).2

theorem no_candidate_sound (r asm q) (e : identity S r asm q = .no_candidate) :
    HCase S r asm → False := fun c => by
  have m := candidate_mem S r asm c.witness
  have z : candidates S r asm = [] := identityOf_none q _ e
  rw [z] at m; exact memNil m

theorem identified_complete (r asm q) (c : HCase S r asm) (i : Identified c q.value) :
    identity S r asm q = .identified :=
  identityOf_complete q (candidates S r asm) i.1
    (fun y m => i.2 (mem_candidate S r asm y m))
    ⟨c.witness.1, candidate_mem S r asm c.witness⟩

def actual_sound (r asm) (c : HCase S r asm) (Q : S.Reading → Sort u) (holds : Holds c Q)
    (actual : S.Reading) (observed : S.shows actual = r) (listed : Listed S actual)
    (assumed : denote (Assumed S asm) actual) : Q actual :=
  actual_world_sound c holds actual observed (listed, assumed)

def listing_complete_sound (complete : (x : S.Reading) → Listed S x)
    (r asm) (c : HCase S r asm) (Q : S.Reading → Sort u) (holds : Holds c Q)
    (actual : S.Reading) (observed : S.shows actual = r)
    (assumed : denote (Assumed S asm) actual) : Q actual :=
  actual_sound S r asm c Q holds actual observed (complete actual) assumed

/-! The three outputs -/

abbrev Certificate (r : S.Shown) (asm : List (S.Reading → Bool)) : Ask S.Reading → Type
  | .claim P => (c : HCase S r asm) ×' Holds c (Yes S P)
  | .query q => (c : HCase S r asm) ×' Identified c q.value

abbrev Pair (r : S.Shown) (asm : List (S.Reading → Bool)) : Ask S.Reading → Type
  | .claim P => PProd ((x : HCandidate S r asm) ×' Yes S P x.1) ((y : HCandidate S r asm) ×' No S P y.1)
  | .query q => (c : HCase S r asm) ×' Disagreeing c q.value

abbrev Refutation (r : S.Shown) (asm : List (S.Reading → Bool)) : Ask S.Reading → Type
  | .claim P => PSum ((c : HCase S r asm) ×' Holds c (No S P)) (HCase S r asm → False)
  | .query _ => PLift (HCase S r asm → False)

inductive Output (r : S.Shown) (asm : List (S.Reading → Bool)) (a : Ask S.Reading) : Type where
  | sound : Certificate S r asm a → Output r asm a
  | epi   : Pair S r asm a        → Output r asm a
  | empty : Refutation S r asm a  → Output r asm a

def kind {r asm a} : Output S r asm a → Kind
  | .sound _ => .Sound
  | .epi _   => .Epi
  | .empty _ => .Empty

/-- Total, and no model call: every branch is a verdict and its lemma. -/
def decide (r : S.Shown) (asm : List (S.Reading → Bool)) : (a : Ask S.Reading) → Output S r asm a
  | .claim P =>
    match e : presence S r asm P with
    | .entailed     => .sound ⟨entailed_case S r asm P e, entailed_sound S r asm P e _⟩
    | .refuted      => .empty (.inl ⟨refuted_case S r asm P e, refuted_sound S r asm P e _⟩)
    | .unresolved   => .epi (unresolved_sound S r asm P e)
    | .inconsistent => .empty (.inr (inconsistent_sound S r asm P e))
  | .query q =>
    match e : identity S r asm q with
    | .identified   => .sound ⟨identified_case S r asm q e, identified_sound S r asm q e _⟩
    | .unidentified => .epi (unidentified_sound S r asm q e)
    | .no_candidate => .empty ⟨no_candidate_sound S r asm q e⟩

/-! Completeness of the output: whenever a certificate exists, decide answers Sound. -/

theorem sound_given (r asm P) (cert : Certificate S r asm (.claim P)) :
    kind S (decide S r asm (.claim P)) = .Sound := by
  have c := cert.1
  have holds := cert.2
  generalize decide S r asm (.claim P) = o
  cases o with
  | sound _ => rfl
  | epi pr => exact (bool_clash pr.2.2 (holds pr.2.1)).elim
  | empty rf =>
    cases rf with
    | inl cn => exact (bool_clash (cn.2 cert.1.witness) (holds cert.1.witness)).elim
    | inr none => exact (none cert.1).elim

theorem sound_given_query (r asm q) (cert : Certificate S r asm (.query q)) :
    kind S (decide S r asm (.query q)) = .Sound := by
  generalize decide S r asm (.query q) = o
  cases o with
  | sound _ => rfl
  | epi pr => exact (disagreeing_not_identified pr.1 q.value pr.2 cert.2).elim
  | empty none => exact (none.down cert.1).elim

end Check

/-! The pre-flight check -/

structure Prompt (S : Schema) : Type 1 where
  shown : S.Shown
  assumptions : List (S.Reading → Bool)
  ask : Ask S.Reading

def haruspex (S : Schema) (p : Prompt S) : Check.Output S p.shown p.assumptions p.ask :=
  Check.decide S p.shown p.assumptions p.ask


def verdict (S : Schema) (p : Prompt S) : Kind := Check.kind S (haruspex S p)

/-! The explorer correspondence: verification/proofs/agda/HaruspexExplorer.agda,
over residual-evidence-types' ResidualEvidence.Finite.Int and Finite.Checker,
restated here. -/

/-! Agda.Builtin.Int, Nat's `_==_` and `_<_`, and Finite.Int -/

inductive ZInt : Type where
  | pos : Nat → ZInt
  | negsuc : Nat → ZInt
  deriving DecidableEq

def natEqb : Nat → Nat → Bool
  | 0,     0     => true
  | m + 1, n + 1 => natEqb m n
  | 0,     _ + 1 => false
  | _ + 1, 0     => false

def natLtb : Nat → Nat → Bool
  | _,     0     => false
  | 0,     _ + 1 => true
  | m + 1, n + 1 => natLtb m n

def minusZ : Nat → Nat → ZInt
  | m,     0     => .pos m
  | 0,     n + 1 => .negsuc n
  | m + 1, n + 1 => minusZ m n

def addZ : ZInt → ZInt → ZInt
  | .pos m,    .pos n    => .pos (m + n)
  | .pos m,    .negsuc n => minusZ m (n + 1)
  | .negsuc m, .pos n    => minusZ n (m + 1)
  | .negsuc m, .negsuc n => .negsuc ((m + n) + 1)

def absZ : ZInt → ZInt
  | .pos n    => .pos n
  | .negsuc n => .pos (n + 1)

def signZ : ZInt → ZInt
  | .pos 0       => .pos 0
  | .pos (_ + 1) => .pos 1
  | .negsuc _    => .negsuc 0

def eqZ : ZInt → ZInt → Bool
  | .pos m,    .pos n    => natEqb m n
  | .negsuc m, .negsuc n => natEqb m n
  | .pos _,    .negsuc _ => false
  | .negsuc _, .pos _    => false

theorem natEqb_sound : ∀ m n, natEqb m n = true → m = n
  | 0,     0,     _ => rfl
  | m + 1, n + 1, e => congrArg Nat.succ (natEqb_sound m n e)
  | 0,     _ + 1, e => by cases e
  | _ + 1, 0,     e => by cases e

theorem natEqb_refl : ∀ n, natEqb n n = true
  | 0     => rfl
  | n + 1 => natEqb_refl n

theorem eqZ_sound : ∀ a b, eqZ a b = true → a = b
  | .pos m,    .pos n,    e => congrArg ZInt.pos (natEqb_sound m n e)
  | .negsuc m, .negsuc n, e => congrArg ZInt.negsuc (natEqb_sound m n e)
  | .pos _,    .negsuc _, e => by cases e
  | .negsuc _, .pos _,    e => by cases e

theorem eqZ_complete : ∀ a b, a = b → eqZ a b = true
  | .pos n,    _, rfl => natEqb_refl n
  | .negsuc n, _, rfl => natEqb_refl n

def range : List ZInt :=
  [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0,
   .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]

/-- Prelude's `_≤_`. -/
inductive Leq : Nat → Nat → Type where
  | z_le_n (n : Nat) : Leq 0 n
  | s_le_s {m n : Nat} : Leq m n → Leq (m + 1) (n + 1)

/-! Finite.Row and Finite.Checker -/

inductive View : Type where
  | exact | sign | magnitude
  deriving DecidableEq

abbrev World : Type := ZInt × ZInt
def latent (w : World) : ZInt := w.1
def noise (w : World) : ZInt := w.2

def natAbs : ZInt → Nat
  | .pos n    => n
  | .negsuc n => n + 1

def through : View → ZInt → ZInt
  | .exact,     x => x
  | .sign,      x => signZ x
  | .magnitude, x => absZ x

structure Config : Type where
  config ::
  residual : ZInt
  noiseBound : Nat
  view : View
  assumeZero : Bool
  deriving DecidableEq

def observeF (cfg : Config) (w : World) : ZInt := through cfg.view (addZ (latent w) (noise w))

def target (cfg : Config) : ZInt := through cfg.view cfg.residual

abbrev InRange (w : World) : Type := Mem (latent w) range × Mem (noise w) range

abbrev Bounded (cfg : Config) (w : World) : Type := Leq (natAbs (noise w)) cfg.noiseBound

abbrev AssumedZ : Bool → ZInt → Type
  | false, _ => Unit
  | true,  l => PLift (l = .pos 0)

abbrev Zero (cfg : Config) (w : World) : Type := AssumedZ cfg.assumeZero (latent w)

abbrev FEvidence (cfg : Config) : Ctx World := [InRange, Bounded cfg, Zero cfg]

abbrev FiniteCandidate (cfg : Config) : Type :=
  Candidate (observeF cfg) (target cfg) (denote (FEvidence cfg))

def zeroCheck : Bool → ZInt → Bool
  | false, _ => true
  | true,  l => eqZ l (.pos 0)

def admits (cfg : Config) (w : World) : Bool :=
  natLtb (natAbs (noise w)) (cfg.noiseBound + 1) &&
  (zeroCheck cfg.assumeZero (latent w) && eqZ (observeF cfg w) (target cfg))

def consIf : Bool → World → List World → List World
  | true,  w, ws => w :: ws
  | false, _, ws => ws

def noiseLoop (cfg : Config) (l : ZInt) : List ZInt → List World → List World
  | [],      rest => rest
  | n :: ns, rest => consIf (admits cfg (l, n)) (l, n) (noiseLoop cfg l ns rest)

def latentLoop (cfg : Config) : List ZInt → List World
  | []      => []
  | l :: ls => noiseLoop cfg l range (latentLoop cfg ls)

def enumerate (cfg : Config) : List World := latentLoop cfg range

def present (w : World) : Bool := !(eqZ (latent w) (.pos 0))
def absent (w : World) : Bool := eqZ (latent w) (.pos 0)

def anyW (p : World → Bool) : List World → Bool
  | []      => false
  | w :: ws => p w || anyW p ws

def presenceOfW : List World → Verdict
  | []      => .inconsistent
  | w :: ws => classify (anyW present (w :: ws)) (anyW absent (w :: ws))

/-- `latentsFrom` and `latentsStep`, the latter inlined as the `if` on the same
test: a `mutual` pair would be compiled by well-founded recursion, which
brings in `propext` and `Quot.sound` and does not reduce well in the kernel. -/
def latentsFrom (x : ZInt) : List World → List ZInt
  | []      => []
  | w :: ws => if eqZ x (latent w) = true then latentsFrom x ws else latent w :: latentsFrom (latent w) ws

def latents : List World → List ZInt
  | []      => []
  | w :: ws => latent w :: latentsFrom (latent w) ws

def identityOfL : List ZInt → IdStatus
  | []          => .no_candidate
  | [_]         => .identified
  | _ :: _ :: _ => .unidentified

def presenceC (cfg : Config) : Verdict := presenceOfW (enumerate cfg)
def identityC (cfg : Config) : IdStatus := identityOfL (latents (enumerate cfg))

def mapL {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: mapL f xs

def forEach {α β : Type} : List α → (α → List β → List β) → List β → List β
  | [],      _,    rest => rest
  | x :: xs, body, rest => body x (forEach xs body rest)

def bounds : List Nat := [0, 1, 2, 3, 4, 5, 6]
def views : List View := [.exact, .sign, .magnitude]
def flags : List Bool := [false, true]

def allConfigs : List Config :=
  forEach range (fun r =>
  forEach bounds (fun b =>
  forEach views (fun v =>
  forEach flags (fun z rest => Config.config r b v z :: rest)))) []

def lengthL {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => lengthL xs + 1

theorem allConfigs_length : lengthL allConfigs = 546 := by decide +kernel

/-! Finite.Soundness: the bridges to_finite and from_finite use -/

def lt_sound : ∀ m n, natLtb m (n + 1) = true → Leq m n
  | 0,     n,     _ => .z_le_n n
  | m + 1, 0,     e => by cases m <;> cases e
  | m + 1, n + 1, e => .s_le_s (lt_sound m n e)

theorem lt_complete : ∀ {m n}, Leq m n → natLtb m (n + 1) = true
  | _, _, .z_le_n _ => rfl
  | _, _, @Leq.s_le_s m n p => (lt_complete p : natLtb m (n + 1) = true)

def zero_sound : ∀ z l, zeroCheck z l = true → AssumedZ z l
  | false, _, _ => ()
  | true,  l, e => ⟨eqZ_sound l (.pos 0) e⟩

theorem zero_complete : ∀ z l, AssumedZ z l → zeroCheck z l = true
  | false, _, _ => rfl
  | true,  l, e => eqZ_complete l (.pos 0) e.down

/-! HaruspexExplorer: the explorer's worlds, latent outer and noise inner -/

def pairsRow (l : ZInt) : List ZInt → List World → List World
  | [],      rest => rest
  | n :: ns, rest => (l, n) :: pairsRow l ns rest

def pairs : List ZInt → List ZInt → List World
  | [],      _  => []
  | l :: ls, ns => pairsRow l ns (pairs ls ns)

def worlds : List World := pairs range range

def pairsRow_here (l : ZInt) : ∀ ns rest n, Mem n ns → Mem (l, n) (pairsRow l ns rest)
  | _ :: _,  _,    _, .here    => .here
  | _ :: ns, rest, n, .there m => .there (pairsRow_here l ns rest n m)

def pairsRow_rest (l : ZInt) : ∀ ns rest w, Mem w rest → Mem w (pairsRow l ns rest)
  | [],      _,    _, m => m
  | _ :: ns, rest, w, m => .there (pairsRow_rest l ns rest w m)

def mem_pairs : ∀ ls ns l n, Mem l ls → Mem n ns → Mem (l, n) (pairs ls ns)
  | _ :: ls,  ns, l, n, .here,     mn => pairsRow_here l ns (pairs ls ns) n mn
  | l' :: ls, ns, l, n, .there ml, mn =>
    pairsRow_rest l' ns (pairs ls ns) (l, n) (mem_pairs ls ns l n ml mn)

def pairsRow_mem (l : ZInt) : ∀ ns rest w, Mem w (pairsRow l ns rest) →
    PSum (PProd (latent w = l) (Mem (noise w) ns)) (Mem w rest)
  | [],      _,    _, m        => .inr m
  | _ :: _,  _,    _, .here    => .inl ⟨rfl, .here⟩
  | _ :: ns, rest, w, .there m =>
    match pairsRow_mem l ns rest w m with
    | .inl ⟨e, mn⟩ => .inl ⟨e, .there mn⟩
    | .inr mr      => .inr mr

def pairs_mem : ∀ ls ns w, Mem w (pairs ls ns) → Mem (latent w) ls × Mem (noise w) ns
  | [],      _,  _, m => (memNil m).elim
  | l :: ls, ns, w, m =>
    match pairsRow_mem l ns (pairs ls ns) w m with
    | .inl ⟨e, mn⟩ => (e ▸ .here, mn)
    | .inr mr      => let r := pairs_mem ls ns w mr; (.there r.1, r.2)

/-! A configuration, declared as a schema and two prompts -/

def explorer (cfg : Config) : Schema where
  Reading := World
  readings := worlds
  Shown := ZInt
  shows := observeF cfg
  eqbShown := eqZ
  eqbShown_sound := eqZ_sound
  eqbShown_complete := eqZ_complete

def bounded (cfg : Config) (w : World) : Bool := natLtb (natAbs (noise w)) (cfg.noiseBound + 1)
def zeroed (cfg : Config) (w : World) : Bool := zeroCheck cfg.assumeZero (latent w)

def stated (cfg : Config) : List (World → Bool) := [bounded cfg, zeroed cfg]

def latentQ : Query World where
  Value := ZInt
  value := latent
  eqbValue := eqZ
  eqbValue_sound := eqZ_sound
  eqbValue_complete := eqZ_complete

def presencePrompt (cfg : Config) : Prompt (explorer cfg) :=
  ⟨target cfg, stated cfg, .claim present⟩
def identityPrompt (cfg : Config) : Prompt (explorer cfg) :=
  ⟨target cfg, stated cfg, .query latentQ⟩

/-! The evidence contexts admit the same worlds -/

def to_finite (cfg : Config) :
    Check.HCandidate (explorer cfg) (target cfg) (stated cfg) → FiniteCandidate cfg
  | ⟨w, observed, listed, b, z, _⟩ =>
    ⟨w, observed, pairs_mem range range w listed, lt_sound _ _ b.down, zero_sound _ _ z.down, ()⟩

def from_finite (cfg : Config) :
    FiniteCandidate cfg → Check.HCandidate (explorer cfg) (target cfg) (stated cfg)
  | ⟨(l, n), observed, (ml, mn), b, z, _⟩ =>
    ⟨(l, n), observed, mem_pairs range range l n ml mn, ⟨lt_complete b⟩, ⟨zero_complete _ _ z⟩, ()⟩

/-! The correspondence, decided by normalisation over all 546 configurations.

The Agda module decides each statement by one `refl` over `allConfigs`. Here a
single declaration over all 546 configurations was killed for memory when tried
(at 13.8 GB, with an earlier, well-founded `latentsFrom`). So each statement is decided per residual
(42 configurations, one declaration each, by kernel reduction), and
`chunks_cons` reassembles the statement over `allConfigs` unchanged. -/

def configsFor (r : ZInt) : List Config :=
  forEach bounds (fun b => forEach views (fun v =>
    forEach flags (fun z rest => Config.config r b v z :: rest))) []

def concatChunks : List ZInt → List Config
  | []      => []
  | r :: rs => configsFor r ++ concatChunks rs

theorem allConfigs_chunks : allConfigs = concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6] := by decide +kernel

theorem mapL_append {α β : Type} (f : α → β) : ∀ xs ys : List α,
    mapL f (xs ++ ys) = mapL f xs ++ mapL f ys
  | [],      _  => rfl
  | x :: xs, ys => congrArg (f x :: ·) (mapL_append f xs ys)

theorem chunks_nil {β : Type} (f g : Config → β) :
    mapL f (concatChunks []) = mapL g (concatChunks []) := rfl

theorem chunks_cons {β : Type} (f g : Config → β) (r : ZInt) (rs : List ZInt)
    (h : mapL f (configsFor r) = mapL g (configsFor r))
    (t : mapL f (concatChunks rs) = mapL g (concatChunks rs)) :
    mapL f (concatChunks (r :: rs)) = mapL g (concatChunks (r :: rs)) := by
  show mapL f (configsFor r ++ concatChunks rs) = mapL g (configsFor r ++ concatChunks rs)
  rw [mapL_append, mapL_append, h, t]

theorem mapL_all {β : Type} (f g : Config → β)
    (h : mapL f (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) = mapL g (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6])) :
    mapL f allConfigs = mapL g allConfigs := by
  rw [allConfigs_chunks]; exact h

def candidatesH (cfg : Config) : List World := Check.candidates (explorer cfg) (target cfg) (stated cfg)
def presenceH (cfg : Config) : Verdict := Check.presence (explorer cfg) (target cfg) (stated cfg) present
def identityH (cfg : Config) : IdStatus := Check.identity (explorer cfg) (target cfg) (stated cfg) latentQ

/-- The design's verdict table (docs/proposals/HARUSPEX.adoc). -/
def presenceKind : Verdict → Kind
  | .entailed => .Sound | .refuted => .Empty | .unresolved => .Epi | .inconsistent => .Empty

def identityKind : IdStatus → Kind
  | .identified => .Sound | .unidentified => .Epi | .no_candidate => .Empty

def verdictP (cfg : Config) : Kind := verdict (explorer cfg) (presencePrompt cfg)
def verdictI (cfg : Config) : Kind := verdict (explorer cfg) (identityPrompt cfg)
def kindP (cfg : Config) : Kind := presenceKind (presenceC cfg)
def kindI (cfg : Config) : Kind := identityKind (identityC cfg)

theorem cand_0 : mapL candidatesH (configsFor (.negsuc 5)) = mapL enumerate (configsFor (.negsuc 5)) := by decide +kernel
theorem cand_1 : mapL candidatesH (configsFor (.negsuc 4)) = mapL enumerate (configsFor (.negsuc 4)) := by decide +kernel
theorem cand_2 : mapL candidatesH (configsFor (.negsuc 3)) = mapL enumerate (configsFor (.negsuc 3)) := by decide +kernel
theorem cand_3 : mapL candidatesH (configsFor (.negsuc 2)) = mapL enumerate (configsFor (.negsuc 2)) := by decide +kernel
theorem cand_4 : mapL candidatesH (configsFor (.negsuc 1)) = mapL enumerate (configsFor (.negsuc 1)) := by decide +kernel
theorem cand_5 : mapL candidatesH (configsFor (.negsuc 0)) = mapL enumerate (configsFor (.negsuc 0)) := by decide +kernel
theorem cand_6 : mapL candidatesH (configsFor (.pos 0)) = mapL enumerate (configsFor (.pos 0)) := by decide +kernel
theorem cand_7 : mapL candidatesH (configsFor (.pos 1)) = mapL enumerate (configsFor (.pos 1)) := by decide +kernel
theorem cand_8 : mapL candidatesH (configsFor (.pos 2)) = mapL enumerate (configsFor (.pos 2)) := by decide +kernel
theorem cand_9 : mapL candidatesH (configsFor (.pos 3)) = mapL enumerate (configsFor (.pos 3)) := by decide +kernel
theorem cand_10 : mapL candidatesH (configsFor (.pos 4)) = mapL enumerate (configsFor (.pos 4)) := by decide +kernel
theorem cand_11 : mapL candidatesH (configsFor (.pos 5)) = mapL enumerate (configsFor (.pos 5)) := by decide +kernel
theorem cand_12 : mapL candidatesH (configsFor (.pos 6)) = mapL enumerate (configsFor (.pos 6)) := by decide +kernel

theorem pres_0 : mapL presenceH (configsFor (.negsuc 5)) = mapL presenceC (configsFor (.negsuc 5)) := by decide +kernel
theorem pres_1 : mapL presenceH (configsFor (.negsuc 4)) = mapL presenceC (configsFor (.negsuc 4)) := by decide +kernel
theorem pres_2 : mapL presenceH (configsFor (.negsuc 3)) = mapL presenceC (configsFor (.negsuc 3)) := by decide +kernel
theorem pres_3 : mapL presenceH (configsFor (.negsuc 2)) = mapL presenceC (configsFor (.negsuc 2)) := by decide +kernel
theorem pres_4 : mapL presenceH (configsFor (.negsuc 1)) = mapL presenceC (configsFor (.negsuc 1)) := by decide +kernel
theorem pres_5 : mapL presenceH (configsFor (.negsuc 0)) = mapL presenceC (configsFor (.negsuc 0)) := by decide +kernel
theorem pres_6 : mapL presenceH (configsFor (.pos 0)) = mapL presenceC (configsFor (.pos 0)) := by decide +kernel
theorem pres_7 : mapL presenceH (configsFor (.pos 1)) = mapL presenceC (configsFor (.pos 1)) := by decide +kernel
theorem pres_8 : mapL presenceH (configsFor (.pos 2)) = mapL presenceC (configsFor (.pos 2)) := by decide +kernel
theorem pres_9 : mapL presenceH (configsFor (.pos 3)) = mapL presenceC (configsFor (.pos 3)) := by decide +kernel
theorem pres_10 : mapL presenceH (configsFor (.pos 4)) = mapL presenceC (configsFor (.pos 4)) := by decide +kernel
theorem pres_11 : mapL presenceH (configsFor (.pos 5)) = mapL presenceC (configsFor (.pos 5)) := by decide +kernel
theorem pres_12 : mapL presenceH (configsFor (.pos 6)) = mapL presenceC (configsFor (.pos 6)) := by decide +kernel

theorem iden_0 : mapL identityH (configsFor (.negsuc 5)) = mapL identityC (configsFor (.negsuc 5)) := by decide +kernel
theorem iden_1 : mapL identityH (configsFor (.negsuc 4)) = mapL identityC (configsFor (.negsuc 4)) := by decide +kernel
theorem iden_2 : mapL identityH (configsFor (.negsuc 3)) = mapL identityC (configsFor (.negsuc 3)) := by decide +kernel
theorem iden_3 : mapL identityH (configsFor (.negsuc 2)) = mapL identityC (configsFor (.negsuc 2)) := by decide +kernel
theorem iden_4 : mapL identityH (configsFor (.negsuc 1)) = mapL identityC (configsFor (.negsuc 1)) := by decide +kernel
theorem iden_5 : mapL identityH (configsFor (.negsuc 0)) = mapL identityC (configsFor (.negsuc 0)) := by decide +kernel
theorem iden_6 : mapL identityH (configsFor (.pos 0)) = mapL identityC (configsFor (.pos 0)) := by decide +kernel
theorem iden_7 : mapL identityH (configsFor (.pos 1)) = mapL identityC (configsFor (.pos 1)) := by decide +kernel
theorem iden_8 : mapL identityH (configsFor (.pos 2)) = mapL identityC (configsFor (.pos 2)) := by decide +kernel
theorem iden_9 : mapL identityH (configsFor (.pos 3)) = mapL identityC (configsFor (.pos 3)) := by decide +kernel
theorem iden_10 : mapL identityH (configsFor (.pos 4)) = mapL identityC (configsFor (.pos 4)) := by decide +kernel
theorem iden_11 : mapL identityH (configsFor (.pos 5)) = mapL identityC (configsFor (.pos 5)) := by decide +kernel
theorem iden_12 : mapL identityH (configsFor (.pos 6)) = mapL identityC (configsFor (.pos 6)) := by decide +kernel

theorem outp_0 : mapL verdictP (configsFor (.negsuc 5)) = mapL kindP (configsFor (.negsuc 5)) := by decide +kernel
theorem outp_1 : mapL verdictP (configsFor (.negsuc 4)) = mapL kindP (configsFor (.negsuc 4)) := by decide +kernel
theorem outp_2 : mapL verdictP (configsFor (.negsuc 3)) = mapL kindP (configsFor (.negsuc 3)) := by decide +kernel
theorem outp_3 : mapL verdictP (configsFor (.negsuc 2)) = mapL kindP (configsFor (.negsuc 2)) := by decide +kernel
theorem outp_4 : mapL verdictP (configsFor (.negsuc 1)) = mapL kindP (configsFor (.negsuc 1)) := by decide +kernel
theorem outp_5 : mapL verdictP (configsFor (.negsuc 0)) = mapL kindP (configsFor (.negsuc 0)) := by decide +kernel
theorem outp_6 : mapL verdictP (configsFor (.pos 0)) = mapL kindP (configsFor (.pos 0)) := by decide +kernel
theorem outp_7 : mapL verdictP (configsFor (.pos 1)) = mapL kindP (configsFor (.pos 1)) := by decide +kernel
theorem outp_8 : mapL verdictP (configsFor (.pos 2)) = mapL kindP (configsFor (.pos 2)) := by decide +kernel
theorem outp_9 : mapL verdictP (configsFor (.pos 3)) = mapL kindP (configsFor (.pos 3)) := by decide +kernel
theorem outp_10 : mapL verdictP (configsFor (.pos 4)) = mapL kindP (configsFor (.pos 4)) := by decide +kernel
theorem outp_11 : mapL verdictP (configsFor (.pos 5)) = mapL kindP (configsFor (.pos 5)) := by decide +kernel
theorem outp_12 : mapL verdictP (configsFor (.pos 6)) = mapL kindP (configsFor (.pos 6)) := by decide +kernel

theorem outi_0 : mapL verdictI (configsFor (.negsuc 5)) = mapL kindI (configsFor (.negsuc 5)) := by decide +kernel
theorem outi_1 : mapL verdictI (configsFor (.negsuc 4)) = mapL kindI (configsFor (.negsuc 4)) := by decide +kernel
theorem outi_2 : mapL verdictI (configsFor (.negsuc 3)) = mapL kindI (configsFor (.negsuc 3)) := by decide +kernel
theorem outi_3 : mapL verdictI (configsFor (.negsuc 2)) = mapL kindI (configsFor (.negsuc 2)) := by decide +kernel
theorem outi_4 : mapL verdictI (configsFor (.negsuc 1)) = mapL kindI (configsFor (.negsuc 1)) := by decide +kernel
theorem outi_5 : mapL verdictI (configsFor (.negsuc 0)) = mapL kindI (configsFor (.negsuc 0)) := by decide +kernel
theorem outi_6 : mapL verdictI (configsFor (.pos 0)) = mapL kindI (configsFor (.pos 0)) := by decide +kernel
theorem outi_7 : mapL verdictI (configsFor (.pos 1)) = mapL kindI (configsFor (.pos 1)) := by decide +kernel
theorem outi_8 : mapL verdictI (configsFor (.pos 2)) = mapL kindI (configsFor (.pos 2)) := by decide +kernel
theorem outi_9 : mapL verdictI (configsFor (.pos 3)) = mapL kindI (configsFor (.pos 3)) := by decide +kernel
theorem outi_10 : mapL verdictI (configsFor (.pos 4)) = mapL kindI (configsFor (.pos 4)) := by decide +kernel
theorem outi_11 : mapL verdictI (configsFor (.pos 5)) = mapL kindI (configsFor (.pos 5)) := by decide +kernel
theorem outi_12 : mapL verdictI (configsFor (.pos 6)) = mapL kindI (configsFor (.pos 6)) := by decide +kernel

theorem cand_all : mapL candidatesH (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) = mapL enumerate (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) :=
  chunks_cons _ _ (.negsuc 5) _ cand_0 (chunks_cons _ _ (.negsuc 4) _ cand_1 (chunks_cons _ _ (.negsuc 3) _ cand_2 (chunks_cons _ _ (.negsuc 2) _ cand_3 (chunks_cons _ _ (.negsuc 1) _ cand_4 (chunks_cons _ _ (.negsuc 0) _ cand_5 (chunks_cons _ _ (.pos 0) _ cand_6 (chunks_cons _ _ (.pos 1) _ cand_7 (chunks_cons _ _ (.pos 2) _ cand_8 (chunks_cons _ _ (.pos 3) _ cand_9 (chunks_cons _ _ (.pos 4) _ cand_10 (chunks_cons _ _ (.pos 5) _ cand_11 (chunks_cons _ _ (.pos 6) _ cand_12 (chunks_nil _ _)))))))))))))

theorem pres_all : mapL presenceH (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) = mapL presenceC (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) :=
  chunks_cons _ _ (.negsuc 5) _ pres_0 (chunks_cons _ _ (.negsuc 4) _ pres_1 (chunks_cons _ _ (.negsuc 3) _ pres_2 (chunks_cons _ _ (.negsuc 2) _ pres_3 (chunks_cons _ _ (.negsuc 1) _ pres_4 (chunks_cons _ _ (.negsuc 0) _ pres_5 (chunks_cons _ _ (.pos 0) _ pres_6 (chunks_cons _ _ (.pos 1) _ pres_7 (chunks_cons _ _ (.pos 2) _ pres_8 (chunks_cons _ _ (.pos 3) _ pres_9 (chunks_cons _ _ (.pos 4) _ pres_10 (chunks_cons _ _ (.pos 5) _ pres_11 (chunks_cons _ _ (.pos 6) _ pres_12 (chunks_nil _ _)))))))))))))

theorem iden_all : mapL identityH (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) = mapL identityC (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) :=
  chunks_cons _ _ (.negsuc 5) _ iden_0 (chunks_cons _ _ (.negsuc 4) _ iden_1 (chunks_cons _ _ (.negsuc 3) _ iden_2 (chunks_cons _ _ (.negsuc 2) _ iden_3 (chunks_cons _ _ (.negsuc 1) _ iden_4 (chunks_cons _ _ (.negsuc 0) _ iden_5 (chunks_cons _ _ (.pos 0) _ iden_6 (chunks_cons _ _ (.pos 1) _ iden_7 (chunks_cons _ _ (.pos 2) _ iden_8 (chunks_cons _ _ (.pos 3) _ iden_9 (chunks_cons _ _ (.pos 4) _ iden_10 (chunks_cons _ _ (.pos 5) _ iden_11 (chunks_cons _ _ (.pos 6) _ iden_12 (chunks_nil _ _)))))))))))))

theorem outp_all : mapL verdictP (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) = mapL kindP (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) :=
  chunks_cons _ _ (.negsuc 5) _ outp_0 (chunks_cons _ _ (.negsuc 4) _ outp_1 (chunks_cons _ _ (.negsuc 3) _ outp_2 (chunks_cons _ _ (.negsuc 2) _ outp_3 (chunks_cons _ _ (.negsuc 1) _ outp_4 (chunks_cons _ _ (.negsuc 0) _ outp_5 (chunks_cons _ _ (.pos 0) _ outp_6 (chunks_cons _ _ (.pos 1) _ outp_7 (chunks_cons _ _ (.pos 2) _ outp_8 (chunks_cons _ _ (.pos 3) _ outp_9 (chunks_cons _ _ (.pos 4) _ outp_10 (chunks_cons _ _ (.pos 5) _ outp_11 (chunks_cons _ _ (.pos 6) _ outp_12 (chunks_nil _ _)))))))))))))

theorem outi_all : mapL verdictI (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) = mapL kindI (concatChunks [.negsuc 5, .negsuc 4, .negsuc 3, .negsuc 2, .negsuc 1, .negsuc 0, .pos 0, .pos 1, .pos 2, .pos 3, .pos 4, .pos 5, .pos 6]) :=
  chunks_cons _ _ (.negsuc 5) _ outi_0 (chunks_cons _ _ (.negsuc 4) _ outi_1 (chunks_cons _ _ (.negsuc 3) _ outi_2 (chunks_cons _ _ (.negsuc 2) _ outi_3 (chunks_cons _ _ (.negsuc 1) _ outi_4 (chunks_cons _ _ (.negsuc 0) _ outi_5 (chunks_cons _ _ (.pos 0) _ outi_6 (chunks_cons _ _ (.pos 1) _ outi_7 (chunks_cons _ _ (.pos 2) _ outi_8 (chunks_cons _ _ (.pos 3) _ outi_9 (chunks_cons _ _ (.pos 4) _ outi_10 (chunks_cons _ _ (.pos 5) _ outi_11 (chunks_cons _ _ (.pos 6) _ outi_12 (chunks_nil _ _)))))))))))))

theorem candidates_match :
    mapL (fun cfg => (Check.candidates (explorer cfg) (target cfg) (stated cfg) : List World)) allConfigs
    = mapL enumerate allConfigs :=
  mapL_all candidatesH enumerate cand_all

theorem presence_match :
    mapL (fun cfg => Check.presence (explorer cfg) (target cfg) (stated cfg) present) allConfigs
    = mapL presenceC allConfigs :=
  mapL_all presenceH presenceC pres_all

theorem identity_match :
    mapL (fun cfg => Check.identity (explorer cfg) (target cfg) (stated cfg) latentQ) allConfigs
    = mapL identityC allConfigs :=
  mapL_all identityH identityC iden_all

theorem outputs_match :
    mapL (fun cfg => verdict (explorer cfg) (presencePrompt cfg)) allConfigs
      = mapL (fun cfg => presenceKind (presenceC cfg)) allConfigs ∧
    mapL (fun cfg => verdict (explorer cfg) (identityPrompt cfg)) allConfigs
      = mapL (fun cfg => identityKind (identityC cfg)) allConfigs :=
  ⟨mapL_all verdictP kindP outp_all, mapL_all verdictI kindI outi_all⟩

end Haruspex

/-! Axioms: each must depend on none. -/

#print axioms Haruspex.Check.holdsAll_sound
#print axioms Haruspex.Check.holdsAll_complete
#print axioms Haruspex.Check.candidate_mem
#print axioms Haruspex.Check.mem_candidate
#print axioms Haruspex.Check.entailed_sound
#print axioms Haruspex.Check.refuted_sound
#print axioms Haruspex.Check.refuted_refutes
#print axioms Haruspex.Check.unresolved_sound
#print axioms Haruspex.Check.inconsistent_sound
#print axioms Haruspex.Check.entailed_complete
#print axioms Haruspex.Check.identified_sound
#print axioms Haruspex.Check.unidentified_sound
#print axioms Haruspex.Check.unidentified_refutes
#print axioms Haruspex.Check.no_candidate_sound
#print axioms Haruspex.Check.identified_complete
#print axioms Haruspex.Check.actual_sound
#print axioms Haruspex.Check.listing_complete_sound
#print axioms Haruspex.Check.sound_given
#print axioms Haruspex.Check.sound_given_query
#print axioms Haruspex.haruspex
#print axioms Haruspex.allConfigs_length
#print axioms Haruspex.to_finite
#print axioms Haruspex.from_finite
#print axioms Haruspex.candidates_match
#print axioms Haruspex.presence_match
#print axioms Haruspex.identity_match
#print axioms Haruspex.outputs_match

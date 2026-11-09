(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(* The Rocq recheck leg (standards PROOF-POLICY section 2) of the Haruspex
   checker: verification/proofs/agda/Haruspex.agda, module Haruspex.Check.

   Route: re-proved. No Agda-to-Dedukti-to-Rocq transport was tried. Each
   statement below restates the Agda statement of the same name ('-' becomes
   '_'), over definitions that restate Agda's clause for clause. The Core
   vocabulary of residual-evidence-types (Candidate, Case, Holds, Identified,
   Refuted, Disagreeing, Ctx) is restated first, at the pin
   97244f5cb63bd6697caff261b187b62e9788b692. The translation choices, and how
   each statement was compared with Agda's, are recorded in
   docs/status/RECHECK-CORRESPONDENCE.adoc.

   Core library only: no Mathlib analogue, no axiom. The end of this file
   prints the assumptions of every theorem; scripts/check-recheck-legs.sh
   fails unless each is closed under the global context.

   Checked with coqc 8.18.0. *)

From Coq Require Import List Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* ResidualEvidence.Prelude, Finite.Int, Finite.Row, Finite.Checker    *)

Inductive mem {A : Type} (x : A) : list A -> Type :=
| here : forall xs, mem x (x :: xs)
| there : forall y xs, mem x xs -> mem x (y :: xs).
Arguments here {A x xs}.
Arguments there {A x y xs} _.

Inductive Verdict : Type := entailed | refuted | unresolved | inconsistent.
Inductive IdStatus : Type := identified | unidentified | no_candidate.

Definition classify (a b : bool) : Verdict :=
  match a, b with
  | _, false => entailed
  | false, true => refuted
  | true, true => unresolved
  end.

Definition bool_clash {b : bool} (p : b = false) (q : b = true) : False :=
  match eq_trans (eq_sym p) q in _ = c return (if c then False else True) with
  | eq_refl => I
  end.

Definition mem_nil {A : Type} {x : A} (m : mem x []) : False :=
  match m in mem _ l return (match l with [] => False | _ => True end) with
  | here => I
  | there _ => I
  end.

Definition mem_cons {A : Type} {x y : A} {ys : list A} (m : mem x (y :: ys))
  : ((x = y) + mem x ys)%type :=
  match m in mem _ l
    return (match l with [] => unit | z :: zs => ((x = z) + mem x zs)%type end) with
  | here => inl eq_refl
  | there m' => inr m'
  end.

(* ------------------------------------------------------------------ *)
(* ResidualEvidence.Core, Context, Revision                            *)

Definition Candidate {W O : Type} (observe : W -> O) (r : O) (E : W -> Type) : Type :=
  { world : W & ((observe world = r) * E world)%type }.

Record Case {W O : Type} (observe : W -> O) (r : O) (E : W -> Type) : Type :=
  inhabited { witness : Candidate observe r E }.
Arguments inhabited {W O observe r E} _.
Arguments witness {W O observe r E} _.

Definition Holds {W O : Type} {observe : W -> O} {r : O} {E : W -> Type}
  (c : Case observe r E) (P : W -> Type) : Type :=
  forall x : Candidate observe r E, P (projT1 x).

Definition Identified {W O Q : Type} {observe : W -> O} {r : O} {E : W -> Type}
  (c : Case observe r E) (query : W -> Q) : Type :=
  { value : Q & Holds c (fun world => query world = value) }.

Definition Refuted {W O : Type} {observe : W -> O} {r : O} {E : W -> Type}
  (c : Case observe r E) (P : W -> Type) : Type :=
  { x : Candidate observe r E & (P (projT1 x) -> False) }.

Definition Disagreeing {W O Q : Type} {observe : W -> O} {r : O} {E : W -> Type}
  (c : Case observe r E) (query : W -> Q) : Type :=
  { x : Candidate observe r E & { y : Candidate observe r E &
      (query (projT1 x) = query (projT1 y) -> False) } }.

Definition actual_world_sound {W O : Type} {observe : W -> O} {r : O} {E : W -> Type}
  {P : W -> Type} (c : Case observe r E) (claim : Holds c P)
  (actual : W) (observed : observe actual = r) (evidence : E actual) : P actual :=
  claim (existT _ actual (observed, evidence)).

Definition refuted_not_holds {W O : Type} {observe : W -> O} {r : O} {E : W -> Type}
  {P : W -> Type} (c : Case observe r E) (ref : Refuted c P) : Holds c P -> False :=
  fun h => projT2 ref (h (projT1 ref)).

Definition disagreeing_not_identified {W O Q : Type} {observe : W -> O} {r : O}
  {E : W -> Type} (c : Case observe r E) (query : W -> Q)
  (d : Disagreeing c query) : Identified c query -> False :=
  fun i =>
    projT2 (projT2 d)
      (eq_trans (projT2 i (projT1 d)) (eq_sym (projT2 i (projT1 (projT2 d))))).

Definition Ctx (W : Type) : Type := list (W -> Type).

Fixpoint denote {W : Type} (G : Ctx W) (world : W) : Type :=
  match G with
  | [] => unit
  | P :: G' => (P world * denote G' world)%type
  end.

(* ------------------------------------------------------------------ *)
(* Haruspex: the declared context and the prompt                      *)

Record Schema : Type := {
  Reading : Type;
  readings : list Reading;
  Shown : Type;
  shows : Reading -> Shown;
  eqb_shown : Shown -> Shown -> bool;
  eqb_shown_sound : forall a b, eqb_shown a b = true -> a = b;
  eqb_shown_complete : forall a b, a = b -> eqb_shown a b = true
}.

Record Query (R : Type) : Type := {
  Value : Type;
  value : R -> Value;
  eqb_value : Value -> Value -> bool;
  eqb_value_sound : forall a b, eqb_value a b = true -> a = b;
  eqb_value_complete : forall a b, a = b -> eqb_value a b = true
}.
Arguments Value {R} _.
Arguments value {R} _ _.
Arguments eqb_value {R} _ _ _.
Arguments eqb_value_sound {R} _ _ _ _.
Arguments eqb_value_complete {R} _ _ _ _.

Inductive Ask (R : Type) : Type :=
| claim : (R -> bool) -> Ask R
| query : Query R -> Ask R.
Arguments claim {R} _.
Arguments query {R} _.

Inductive Kind : Type := Sound | Epi | Empty.

(* ------------------------------------------------------------------ *)
(* Lists                                                               *)

Definition keepIf {A : Type} (b : bool) (x : A) (xs : list A) : list A :=
  if b then x :: xs else xs.

Fixpoint filter {A : Type} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => keepIf (p x) x (filter p xs')
  end.

Fixpoint anyOf {A : Type} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => false
  | x :: xs' => p x || anyOf p xs'
  end.

Fixpoint allOf {A : Type} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: xs' => p x && allOf p xs'
  end.

Lemma andb_sound : forall a b, a && b = true -> ((a = true) * (b = true))%type.
Proof. intros [] b e; simpl in e; [ exact (eq_refl, e) | discriminate e ]. Defined.

Lemma andb_complete : forall a b, a = true -> b = true -> a && b = true.
Proof. intros a b -> ->; reflexivity. Defined.

Lemma orb_false : forall a b, a = false -> b = false -> a || b = false.
Proof. intros a b -> ->; reflexivity. Defined.

Lemma orb_left : forall a b, a || b = false -> a = false.
Proof. intros [] b e; [ discriminate e | reflexivity ]. Defined.

Lemma orb_right : forall a b, a || b = false -> b = false.
Proof. intros [] b e; [ discriminate e | exact e ]. Defined.

Lemma not_true : forall b, negb b = true -> b = false.
Proof. intros [] e; [ discriminate e | reflexivity ]. Defined.

Lemma not_false : forall b, negb b = false -> b = true.
Proof. intros [] e; [ reflexivity | discriminate e ]. Defined.

Lemma not_of_true : forall b, b = true -> negb b = false.
Proof. intros b ->; reflexivity. Defined.

Lemma filter_sound : forall {A : Type} (p : A -> bool) xs x,
  mem x (filter p xs) -> (mem x xs * (p x = true))%type.
Proof.
  intros A p xs x; induction xs as [| y ys IH]; simpl; intro m.
  - destruct (mem_nil m).
  - destruct (p y) eqn:E; simpl in m.
    + destruct (mem_cons m) as [eq | m'].
      * subst x; exact (here, E).
      * destruct (IH m') as [m'' e]; exact (there m'', e).
    + destruct (IH m) as [m'' e]; exact (there m'', e).
Defined.

Lemma filter_complete : forall {A : Type} (p : A -> bool) xs x,
  mem x xs -> p x = true -> mem x (filter p xs).
Proof.
  intros A p xs x m e; induction m as [ys | y ys m IH]; simpl.
  - rewrite e; exact here.
  - destruct (p y); [ exact (there IH) | exact IH ].
Defined.

Lemma any_true : forall {A : Type} (p : A -> bool) xs,
  anyOf p xs = true -> { x : A & (mem x xs * (p x = true))%type }.
Proof.
  intros A p xs; induction xs as [| y ys IH]; simpl; intro e.
  - discriminate e.
  - destruct (p y) eqn:E.
    + exact (existT _ y (here, E)).
    + destruct (IH e) as [x [m h]]; exact (existT _ x (there m, h)).
Defined.

Lemma any_false : forall {A : Type} (p : A -> bool) xs x,
  anyOf p xs = false -> mem x xs -> p x = false.
Proof.
  intros A p xs x e m; induction m as [ys | y ys m IH]; simpl in e.
  - exact (orb_left _ _ e).
  - exact (IH (orb_right _ _ e)).
Defined.

Lemma none_any : forall {A : Type} (p : A -> bool) xs,
  (forall x, mem x xs -> p x = false) -> anyOf p xs = false.
Proof.
  intros A p xs; induction xs as [| y ys IH]; simpl; intro h.
  - reflexivity.
  - exact (orb_false _ _ (h y here) (IH (fun z m => h z (there m)))).
Defined.

Lemma all_true : forall {A : Type} (p : A -> bool) xs x,
  allOf p xs = true -> mem x xs -> p x = true.
Proof.
  intros A p xs x e m; induction m as [ys | y ys m IH]; simpl in e.
  - exact (fst (andb_sound _ _ e)).
  - exact (IH (snd (andb_sound _ _ e))).
Defined.

Lemma all_complete : forall {A : Type} (p : A -> bool) xs,
  (forall x, mem x xs -> p x = true) -> allOf p xs = true.
Proof.
  intros A p xs; induction xs as [| y ys IH]; simpl; intro h.
  - reflexivity.
  - exact (andb_complete _ _ (h y here) (IH (fun z m => h z (there m)))).
Defined.

Lemma all_false : forall {A : Type} (p : A -> bool) xs,
  allOf p xs = false -> { x : A & (mem x xs * (p x = false))%type }.
Proof.
  intros A p xs; induction xs as [| y ys IH]; simpl; intro e.
  - discriminate e.
  - destruct (p y) eqn:E; simpl in e.
    + destruct (IH e) as [x [m h]]; exact (existT _ x (there m, h)).
    + exact (existT _ y (here, E)).
Defined.

(* ------------------------------------------------------------------ *)
(* Verdicts on a list of candidates                                    *)

Definition presenceOf {A : Type} (P : A -> bool) (ws : list A) : Verdict :=
  match ws with
  | [] => inconsistent
  | _ :: _ => classify (anyOf P ws) (anyOf (fun y => negb (P y)) ws)
  end.

Definition sameAs (b : bool) : IdStatus := if b then identified else unidentified.

Definition agreesWith {A : Type} (q : Query A) (x : A) : A -> bool :=
  fun y => eqb_value q (value q y) (value q x).

Definition identityOf {A : Type} (q : Query A) (ws : list A) : IdStatus :=
  match ws with
  | [] => no_candidate
  | x :: xs => sameAs (allOf (agreesWith q x) xs)
  end.

Lemma classify_entailed : forall a b, classify a b = entailed -> b = false.
Proof. intros [] [] e; first [ reflexivity | discriminate e ]. Defined.

Lemma classify_refuted : forall a b, classify a b = refuted -> ((a = false) * (b = true))%type.
Proof. intros [] [] e; first [ exact (eq_refl, eq_refl) | discriminate e ]. Defined.

Lemma classify_unresolved : forall a b, classify a b = unresolved -> ((a = true) * (b = true))%type.
Proof. intros [] [] e; first [ exact (eq_refl, eq_refl) | discriminate e ]. Defined.

Lemma classify_consistent : forall a b, classify a b = inconsistent -> False.
Proof. intros [] [] e; discriminate e. Defined.

Lemma classify_false : forall a b, b = false -> classify a b = entailed.
Proof. intros a b ->; destruct a; reflexivity. Defined.

Lemma presenceOf_entailed : forall {A : Type} (P : A -> bool) ws,
  presenceOf P ws = entailed -> anyOf (fun y => negb (P y)) ws = false.
Proof.
  intros A P [| w ws] e; [ discriminate e | exact (classify_entailed _ _ e) ].
Defined.

Lemma presenceOf_refuted : forall {A : Type} (P : A -> bool) ws,
  presenceOf P ws = refuted -> anyOf P ws = false.
Proof.
  intros A P [| w ws] e; [ discriminate e | exact (fst (classify_refuted _ _ e)) ].
Defined.

Lemma presenceOf_unresolved : forall {A : Type} (P : A -> bool) ws,
  presenceOf P ws = unresolved ->
  ((anyOf P ws = true) * (anyOf (fun y => negb (P y)) ws = true))%type.
Proof.
  intros A P [| w ws] e; [ discriminate e | exact (classify_unresolved _ _ e) ].
Defined.

Lemma presenceOf_inconsistent : forall {A : Type} (P : A -> bool) ws,
  presenceOf P ws = inconsistent -> ws = [].
Proof.
  intros A P [| w ws] e; [ reflexivity | destruct (classify_consistent _ _ e) ].
Defined.

Lemma presenceOf_entailed_some : forall {A : Type} (P : A -> bool) ws,
  presenceOf P ws = entailed -> { x : A & mem x ws }.
Proof. intros A P [| w ws] e; [ discriminate e | exact (existT _ w here) ]. Defined.

Lemma presenceOf_refuted_some : forall {A : Type} (P : A -> bool) ws,
  presenceOf P ws = refuted -> { x : A & mem x ws }.
Proof. intros A P [| w ws] e; [ discriminate e | exact (existT _ w here) ]. Defined.

Lemma presenceOf_complete : forall {A : Type} (P : A -> bool) ws,
  { x : A & mem x ws } -> anyOf (fun y => negb (P y)) ws = false ->
  presenceOf P ws = entailed.
Proof.
  intros A P [| w ws] [x m] e; [ destruct (mem_nil m) | exact (classify_false _ _ e) ].
Defined.

Lemma head_agrees : forall {A : Type} (q : Query A) x xs,
  allOf (agreesWith q x) xs = true ->
  forall y, mem y (x :: xs) -> value q y = value q x.
Proof.
  intros A q x xs e y m; destruct (mem_cons m) as [eq | m'].
  - rewrite eq; reflexivity.
  - exact (eqb_value_sound q _ _ (all_true _ xs y e m')).
Defined.

Lemma identityOf_identified : forall {A : Type} (q : Query A) ws,
  identityOf q ws = identified ->
  { x : A & (mem x ws * (forall y, mem y ws -> value q y = value q x))%type }.
Proof.
  intros A q [| x xs] e; simpl in e.
  - discriminate e.
  - destruct (allOf (agreesWith q x) xs) eqn:E.
    + exact (existT _ x (here, head_agrees q x xs E)).
    + discriminate e.
Defined.

Lemma identityOf_unidentified : forall {A : Type} (q : Query A) ws,
  identityOf q ws = unidentified ->
  { x : A & { y : A & (mem x ws * mem y ws * (value q x = value q y -> False))%type } }.
Proof.
  intros A q [| x xs] e; simpl in e.
  - discriminate e.
  - destruct (allOf (agreesWith q x) xs) eqn:E.
    + discriminate e.
    + destruct (all_false _ xs E) as [y [m no]].
      refine (existT _ x (existT _ y (here, there m, _))).
      intro eq; exact (bool_clash no (eqb_value_complete q _ _ (eq_sym eq))).
Defined.

Lemma identityOf_none : forall {A : Type} (q : Query A) ws,
  identityOf q ws = no_candidate -> ws = [].
Proof.
  intros A q [| x xs] e; simpl in e.
  - reflexivity.
  - destruct (allOf (agreesWith q x) xs); discriminate e.
Defined.

Lemma identityOf_complete : forall {A : Type} (q : Query A) ws v,
  (forall y, mem y ws -> value q y = v) -> { x : A & mem x ws } ->
  identityOf q ws = identified.
Proof.
  intros A q [| x xs] v h [z m]; simpl.
  - destruct (mem_nil m).
  - rewrite (all_complete (agreesWith q x) xs
      (fun y m' => eqb_value_complete q _ _
         (eq_trans (h y (there m')) (eq_sym (h x here))))).
    reflexivity.
Defined.

(* ------------------------------------------------------------------ *)
(* The check, for one declared schema                                  *)

Section Check.
  Variable S : Schema.

  Definition Listed (x : Reading S) : Type := mem x (readings S).

  Fixpoint Assumed (asm : list (Reading S -> bool)) : Ctx (Reading S) :=
    match asm with
    | [] => []
    | a :: asm' => (fun x => (a x = true : Type)) :: Assumed asm'
    end.

  Definition Evidence (asm : list (Reading S -> bool)) : Ctx (Reading S) :=
    Listed :: Assumed asm.

  Definition HCandidate (r : Shown S) (asm : list (Reading S -> bool)) : Type :=
    Candidate (shows S) r (denote (Evidence asm)).

  Definition HCase (r : Shown S) (asm : list (Reading S -> bool)) : Type :=
    Case (shows S) r (denote (Evidence asm)).

  Definition Yes (P : Reading S -> bool) (x : Reading S) : Type := P x = true.
  Definition No (P : Reading S -> bool) (x : Reading S) : Type := P x = false.

  Fixpoint holdsAll (asm : list (Reading S -> bool)) (x : Reading S) : bool :=
    match asm with
    | [] => true
    | a :: asm' => a x && holdsAll asm' x
    end.

  Definition fits r asm x : bool := eqb_shown S (shows S x) r && holdsAll asm x.

  Definition candidates r asm : list (Reading S) := filter (fits r asm) (readings S).

  Lemma holdsAll_sound : forall asm x, holdsAll asm x = true -> denote (Assumed asm) x.
  Proof.
    intros asm x; induction asm as [| a asm' IH]; simpl; intro e.
    - exact tt.
    - destruct (andb_sound _ _ e) as [h t]; exact (h, IH t).
  Defined.

  Lemma holdsAll_complete : forall asm x, denote (Assumed asm) x -> holdsAll asm x = true.
  Proof.
    intros asm x; induction asm as [| a asm' IH]; simpl; intro d.
    - reflexivity.
    - destruct d as [p rest]; exact (andb_complete _ _ p (IH rest)).
  Defined.

  Lemma candidate_mem : forall r asm (x : HCandidate r asm), mem (projT1 x) (candidates r asm).
  Proof.
    intros r asm [x [observed [listed assumed]]]; simpl.
    exact (filter_complete (fits r asm) (readings S) x listed
      (andb_complete _ _ (eqb_shown_complete S _ _ observed) (holdsAll_complete asm x assumed))).
  Defined.

  Lemma mem_candidate : forall r asm x, mem x (candidates r asm) -> HCandidate r asm.
  Proof.
    intros r asm x m.
    destruct (filter_sound (fits r asm) (readings S) x m) as [listed e].
    destruct (andb_sound _ _ e) as [o h].
    exact (existT _ x (eqb_shown_sound S _ _ o, (listed, holdsAll_sound asm x h))).
  Defined.

  Lemma mem_candidate_fst : forall r asm x (m : mem x (candidates r asm)),
    projT1 (mem_candidate r asm x m) = x.
  Proof.
    intros r asm x m; unfold mem_candidate.
    destruct (filter_sound _ _ x m) as [listed e]; destruct (andb_sound _ _ e); reflexivity.
  Defined.

  Definition presence r asm (P : Reading S -> bool) : Verdict := presenceOf P (candidates r asm).
  Definition identity r asm (q : Query (Reading S)) : IdStatus := identityOf q (candidates r asm).

  Lemma entailed_sound : forall r asm P, presence r asm P = entailed ->
    forall c : HCase r asm, Holds c (Yes P).
  Proof.
    intros r asm P e c x.
    exact (not_false _ (any_false _ (candidates r asm) (projT1 x)
      (presenceOf_entailed P _ e) (candidate_mem r asm x))).
  Defined.

  Lemma entailed_case : forall r asm P, presence r asm P = entailed -> HCase r asm.
  Proof.
    intros r asm P e; destruct (presenceOf_entailed_some P _ e) as [x m].
    exact (inhabited (mem_candidate r asm x m)).
  Defined.

  Lemma refuted_sound : forall r asm P, presence r asm P = refuted ->
    forall c : HCase r asm, Holds c (No P).
  Proof.
    intros r asm P e c x.
    exact (any_false P _ (projT1 x) (presenceOf_refuted P _ e) (candidate_mem r asm x)).
  Defined.

  Lemma refuted_case : forall r asm P, presence r asm P = refuted -> HCase r asm.
  Proof.
    intros r asm P e; destruct (presenceOf_refuted_some P _ e) as [x m].
    exact (inhabited (mem_candidate r asm x m)).
  Defined.

  Lemma refuted_refutes : forall r asm P (e : presence r asm P = refuted) (c : HCase r asm),
    Refuted c (Yes P).
  Proof.
    intros r asm P e c.
    exists (witness c); intro yes.
    exact (bool_clash (refuted_sound r asm P e c (witness c)) yes).
  Defined.

  Lemma refuted_not_entailed : forall r asm P, presence r asm P = refuted ->
    forall c : HCase r asm, Holds c (Yes P) -> False.
  Proof. intros r asm P e c; exact (refuted_not_holds c (refuted_refutes r asm P e c)). Defined.

  Lemma unresolved_sound : forall r asm P, presence r asm P = unresolved ->
    ({ x : HCandidate r asm & Yes P (projT1 x) } *
     { y : HCandidate r asm & No P (projT1 y) })%type.
  Proof.
    intros r asm P e.
    destruct (presenceOf_unresolved P _ e) as [s a].
    destruct (any_true P _ s) as [x [mx hx]].
    destruct (any_true (fun y => negb (P y)) _ a) as [y [my hy]].
    split.
    - exists (mem_candidate r asm x mx). rewrite mem_candidate_fst. exact hx.
    - exists (mem_candidate r asm y my). rewrite mem_candidate_fst. exact (not_true _ hy).
  Defined.

  Lemma inconsistent_sound : forall r asm P, presence r asm P = inconsistent ->
    HCase r asm -> False.
  Proof.
    intros r asm P e c.
    pose proof (candidate_mem r asm (witness c)) as m.
    unfold presence in e; rewrite (presenceOf_inconsistent P _ e) in m.
    exact (mem_nil m).
  Defined.

  Lemma entailed_complete : forall r asm P (c : HCase r asm), Holds c (Yes P) ->
    presence r asm P = entailed.
  Proof.
    intros r asm P c holds.
    apply (presenceOf_complete P _ (existT _ (projT1 (witness c)) (candidate_mem r asm (witness c)))).
    apply none_any; intros x m.
    apply not_of_true.
    pose proof (holds (mem_candidate r asm x m)) as h.
    rewrite mem_candidate_fst in h; exact h.
  Defined.

  Lemma identified_sound : forall r asm q, identity r asm q = identified ->
    forall c : HCase r asm, Identified c (value q).
  Proof.
    intros r asm q e c.
    destruct (identityOf_identified q _ e) as [x [_ agree]].
    exists (value q x); intro y.
    exact (agree (projT1 y) (candidate_mem r asm y)).
  Defined.

  Lemma identified_case : forall r asm q, identity r asm q = identified -> HCase r asm.
  Proof.
    intros r asm q e; destruct (identityOf_identified q _ e) as [x [m _]].
    exact (inhabited (mem_candidate r asm x m)).
  Defined.

  Lemma unidentified_sound : forall r asm q, identity r asm q = unidentified ->
    { c : HCase r asm & Disagreeing c (value q) }.
  Proof.
    intros r asm q e.
    destruct (identityOf_unidentified q _ e) as [x [y [[mx my] no]]].
    exists (inhabited (mem_candidate r asm x mx)).
    exists (mem_candidate r asm x mx). exists (mem_candidate r asm y my).
    rewrite !mem_candidate_fst. exact no.
  Defined.

  Lemma unidentified_refutes : forall r asm q, identity r asm q = unidentified ->
    forall c : HCase r asm, Identified c (value q) -> False.
  Proof.
    intros r asm q e c.
    (* Disagreeing and Identified do not depend on the case itself, so the
       pair refutes identification for every case of the prompt, as in Agda. *)
    exact (disagreeing_not_identified c (value q) (projT2 (unidentified_sound r asm q e))).
  Defined.

  Lemma no_candidate_sound : forall r asm q, identity r asm q = no_candidate ->
    HCase r asm -> False.
  Proof.
    intros r asm q e c.
    pose proof (candidate_mem r asm (witness c)) as m.
    unfold identity in e; rewrite (identityOf_none q _ e) in m.
    exact (mem_nil m).
  Defined.

  Lemma identified_complete : forall r asm q (c : HCase r asm), Identified c (value q) ->
    identity r asm q = identified.
  Proof.
    intros r asm q c [v holds].
    apply (identityOf_complete q _ v).
    - intros y m. pose proof (holds (mem_candidate r asm y m)) as h.
      rewrite mem_candidate_fst in h; exact h.
    - exact (existT _ (projT1 (witness c)) (candidate_mem r asm (witness c))).
  Defined.

  Lemma actual_sound : forall r asm (c : HCase r asm) (Q : Reading S -> Type), Holds c Q ->
    forall actual, shows S actual = r -> Listed actual -> denote (Assumed asm) actual -> Q actual.
  Proof.
    intros r asm c Q holds actual observed listed assumed.
    exact (actual_world_sound c holds actual observed (listed, assumed)).
  Defined.

  Lemma listing_complete_sound : (forall x : Reading S, Listed x) ->
    forall r asm (c : HCase r asm) (Q : Reading S -> Type), Holds c Q ->
    forall actual, shows S actual = r -> denote (Assumed asm) actual -> Q actual.
  Proof.
    intros complete r asm c Q holds actual observed assumed.
    exact (actual_sound r asm c Q holds actual observed (complete actual) assumed).
  Defined.

  (* The three outputs *)

  Definition Certificate r asm (a : Ask (Reading S)) : Type :=
    match a with
    | claim P => { c : HCase r asm & Holds c (Yes P) }
    | query q => { c : HCase r asm & Identified c (value q) }
    end.

  Definition Pair r asm (a : Ask (Reading S)) : Type :=
    match a with
    | claim P => ({ x : HCandidate r asm & Yes P (projT1 x) } *
                  { y : HCandidate r asm & No P (projT1 y) })%type
    | query q => { c : HCase r asm & Disagreeing c (value q) }
    end.

  Definition Refutation r asm (a : Ask (Reading S)) : Type :=
    match a with
    | claim P => ({ c : HCase r asm & Holds c (No P) } + (HCase r asm -> False))%type
    | query q => HCase r asm -> False
    end.

  Inductive Output r asm (a : Ask (Reading S)) : Type :=
  | sound : Certificate r asm a -> Output r asm a
  | epi : Pair r asm a -> Output r asm a
  | empty : Refutation r asm a -> Output r asm a.

  Definition kind {r asm a} (o : Output r asm a) : Kind :=
    match o with sound _ _ _ _ => Sound | epi _ _ _ _ => Epi | empty _ _ _ _ => Empty end.

  (* Total, and no model call: every branch is a verdict and its lemma. *)
  Definition decide r asm (a : Ask (Reading S)) : Output r asm a :=
    match a as a0 return Output r asm a0 with
    | claim P =>
        match presence r asm P as v return presence r asm P = v -> Output r asm (claim P) with
        | entailed => fun e =>
            sound r asm (claim P)
              (existT _ (entailed_case r asm P e) (entailed_sound r asm P e (entailed_case r asm P e)))
        | refuted => fun e =>
            empty r asm (claim P)
              (inl (existT _ (refuted_case r asm P e) (refuted_sound r asm P e (refuted_case r asm P e))))
        | unresolved => fun e => epi r asm (claim P) (unresolved_sound r asm P e)
        | inconsistent => fun e => empty r asm (claim P) (inr (inconsistent_sound r asm P e))
        end eq_refl
    | query q =>
        match identity r asm q as v return identity r asm q = v -> Output r asm (query q) with
        | identified => fun e =>
            sound r asm (query q)
              (existT _ (identified_case r asm q e) (identified_sound r asm q e (identified_case r asm q e)))
        | unidentified => fun e => epi r asm (query q) (unidentified_sound r asm q e)
        | no_candidate => fun e => empty r asm (query q) (no_candidate_sound r asm q e)
        end eq_refl
    end.

  (* Completeness of the output: whenever a certificate exists, decide
     answers Sound. *)

  Lemma sound_given : forall r asm P, Certificate r asm (claim P) ->
    kind (decide r asm (claim P)) = Sound.
  Proof.
    intros r asm P [c holds].
    destruct (decide r asm (claim P)) as [s0 | [s1 [y no]] | [[c' nos] | none]]; simpl.
    - reflexivity.
    - destruct (bool_clash no (holds y)).
    - destruct (bool_clash (nos (witness c)) (holds (witness c))).
    - destruct (none c).
  Defined.

  Lemma sound_given_query : forall r asm q, Certificate r asm (query q) ->
    kind (decide r asm (query q)) = Sound.
  Proof.
    intros r asm q [c ident].
    destruct (decide r asm (query q)) as [s0 | [c' pair] | none]; simpl.
    - reflexivity.
    - destruct (disagreeing_not_identified c' (value q) pair ident).
    - destruct (none c).
  Defined.

End Check.

(* The pre-flight check *)

Record Prompt (S : Schema) : Type := {
  shown : Shown S;
  assumptions : list (Reading S -> bool);
  ask : Ask (Reading S)
}.

Definition haruspex (S : Schema) (p : Prompt S) : Output S (shown S p) (assumptions S p) (ask S p) :=
  decide S (shown S p) (assumptions S p) (ask S p).


Definition verdict (S : Schema) (p : Prompt S) : Kind := kind S (haruspex S p).

(* ================================================================== *)
(* The explorer correspondence: verification/proofs/agda/              *)
(* HaruspexExplorer.agda, over residual-evidence-types'                *)
(* ResidualEvidence.Finite.Int and Finite.Checker, restated here.     *)

(* Agda.Builtin.Int, Nat's _==_ and _<_, and Finite.Int *)

Inductive ZInt : Type := pos (n : nat) | negsuc (n : nat).

Fixpoint natEqb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => natEqb m' n'
  | _, _ => false
  end.

Fixpoint natLtb (m n : nat) : bool :=
  match m, n with
  | _, O => false
  | O, S _ => true
  | S m', S n' => natLtb m' n'
  end.

Fixpoint minusZ (m n : nat) : ZInt :=
  match m, n with
  | _, O => pos m
  | O, S n' => negsuc n'
  | S m', S n' => minusZ m' n'
  end.

Definition addZ (a b : ZInt) : ZInt :=
  match a, b with
  | pos m, pos n => pos (m + n)
  | pos m, negsuc n => minusZ m (S n)
  | negsuc m, pos n => minusZ n (S m)
  | negsuc m, negsuc n => negsuc (S (m + n))
  end.

Definition absZ (x : ZInt) : ZInt :=
  match x with pos n => pos n | negsuc n => pos (S n) end.

Definition signZ (x : ZInt) : ZInt :=
  match x with
  | pos O => pos 0
  | pos (S _) => pos 1
  | negsuc _ => negsuc 0
  end.

Definition eqZ (a b : ZInt) : bool :=
  match a, b with
  | pos m, pos n => natEqb m n
  | negsuc m, negsuc n => natEqb m n
  | _, _ => false
  end.

Lemma natEqb_sound : forall m n, natEqb m n = true -> m = n.
Proof.
  induction m as [| m IH]; destruct n as [| n]; simpl; intro e;
    first [ reflexivity | discriminate e | exact (f_equal S (IH n e)) ].
Defined.

Lemma natEqb_refl : forall n, natEqb n n = true.
Proof. induction n as [| n IH]; [ reflexivity | exact IH ]. Defined.

Lemma eqZ_sound : forall a b, eqZ a b = true -> a = b.
Proof.
  intros [m | m] [n | n] e; simpl in e; first
    [ discriminate e | exact (f_equal pos (natEqb_sound m n e))
    | exact (f_equal negsuc (natEqb_sound m n e)) ].
Defined.

Lemma eqZ_complete : forall a b, a = b -> eqZ a b = true.
Proof. intros a b <-; destruct a as [n | n]; exact (natEqb_refl n). Defined.

Definition range : list ZInt :=
  [negsuc 5; negsuc 4; negsuc 3; negsuc 2; negsuc 1; negsuc 0;
   pos 0; pos 1; pos 2; pos 3; pos 4; pos 5; pos 6].

(* Prelude's _≤_ *)
Inductive leq : nat -> nat -> Type :=
| z_le_n : forall n, leq O n
| s_le_s : forall m n, leq m n -> leq (S m) (S n).

(* Finite.Row and Finite.Checker *)

Inductive View : Type := vexact | vsign | vmagnitude.  (* exact, sign, magnitude *)

Definition World : Type := (ZInt * ZInt)%type.
Definition latent (w : World) : ZInt := fst w.
Definition noise (w : World) : ZInt := snd w.

Definition natAbs (x : ZInt) : nat := match x with pos n => n | negsuc n => S n end.

Definition through (v : View) (x : ZInt) : ZInt :=
  match v with vexact => x | vsign => signZ x | vmagnitude => absZ x end.

Record Config : Type := config {
  residual : ZInt;
  noiseBound : nat;
  view : View;
  assumeZero : bool
}.

Definition observeF (cfg : Config) (w : World) : ZInt :=
  through (view cfg) (addZ (latent w) (noise w)).

Definition target (cfg : Config) : ZInt := through (view cfg) (residual cfg).

Definition InRange (w : World) : Type := (mem (latent w) range * mem (noise w) range)%type.

Definition Bounded (cfg : Config) (w : World) : Type := leq (natAbs (noise w)) (noiseBound cfg).

Definition AssumedZ (z : bool) (l : ZInt) : Type :=
  if z then (l = pos 0 : Type) else unit.

Definition Zero (cfg : Config) (w : World) : Type := AssumedZ (assumeZero cfg) (latent w).

Definition FEvidence (cfg : Config) : Ctx World := [InRange; Bounded cfg; Zero cfg].

Definition FiniteCandidate (cfg : Config) : Type :=
  Candidate (observeF cfg) (target cfg) (denote (FEvidence cfg)).

Definition zeroCheck (z : bool) (l : ZInt) : bool := if z then eqZ l (pos 0) else true.

Definition admits (cfg : Config) (w : World) : bool :=
  natLtb (natAbs (noise w)) (S (noiseBound cfg)) &&
  (zeroCheck (assumeZero cfg) (latent w) && eqZ (observeF cfg w) (target cfg)).

Definition consIf (b : bool) (w : World) (ws : list World) : list World :=
  if b then w :: ws else ws.

Fixpoint noiseLoop (cfg : Config) (l : ZInt) (ns : list ZInt) (rest : list World) : list World :=
  match ns with
  | [] => rest
  | n :: ns' => consIf (admits cfg (l, n)) (l, n) (noiseLoop cfg l ns' rest)
  end.

Fixpoint latentLoop (cfg : Config) (ls : list ZInt) : list World :=
  match ls with
  | [] => []
  | l :: ls' => noiseLoop cfg l range (latentLoop cfg ls')
  end.

Definition enumerate (cfg : Config) : list World := latentLoop cfg range.

Definition present (w : World) : bool := negb (eqZ (latent w) (pos 0)).
Definition absent (w : World) : bool := eqZ (latent w) (pos 0).

Fixpoint anyW (p : World -> bool) (ws : list World) : bool :=
  match ws with [] => false | w :: ws' => p w || anyW p ws' end.

Definition presenceOfW (ws : list World) : Verdict :=
  match ws with
  | [] => inconsistent
  | _ :: _ => classify (anyW present ws) (anyW absent ws)
  end.

(* latentsFrom and latentsStep, the latter inlined as the `if`. *)
Fixpoint latentsFrom (x : ZInt) (ws : list World) : list ZInt :=
  match ws with
  | [] => []
  | w :: ws' => if eqZ x (latent w) then latentsFrom x ws' else latent w :: latentsFrom (latent w) ws'
  end.

Definition latents (ws : list World) : list ZInt :=
  match ws with [] => [] | w :: ws' => latent w :: latentsFrom (latent w) ws' end.

Definition identityOfL (ls : list ZInt) : IdStatus :=
  match ls with [] => no_candidate | [_] => identified | _ :: _ :: _ => unidentified end.

Definition presenceC (cfg : Config) : Verdict := presenceOfW (enumerate cfg).
Definition identityC (cfg : Config) : IdStatus := identityOfL (latents (enumerate cfg)).

Fixpoint forEach {A B : Type} (xs : list A) (body : A -> list B -> list B) (rest : list B) : list B :=
  match xs with [] => rest | x :: xs' => body x (forEach xs' body rest) end.

Definition bounds : list nat := [0; 1; 2; 3; 4; 5; 6].
Definition views : list View := [vexact; vsign; vmagnitude].
Definition flags : list bool := [false; true].

Definition allConfigs : list Config :=
  forEach range (fun r =>
  forEach bounds (fun b =>
  forEach views (fun v =>
  forEach flags (fun z rest => config r b v z :: rest)))) [].

Lemma allConfigs_length : length allConfigs = 546.
Proof. reflexivity. Qed.

(* Finite.Soundness: the bridges to_finite and from_finite use *)

Lemma lt_sound : forall m n, natLtb m (S n) = true -> leq m n.
Proof.
  induction m as [| m IH]; intros [| n] e; simpl in e.
  - exact (z_le_n 0).
  - exact (z_le_n (S n)).
  - destruct m; discriminate e.
  - exact (s_le_s m n (IH n e)).
Defined.

Lemma lt_complete : forall m n, leq m n -> natLtb m (S n) = true.
Proof. intros m n p; induction p as [n | m n p IH]; [ reflexivity | exact IH ]. Defined.

Lemma zero_sound : forall z l, zeroCheck z l = true -> AssumedZ z l.
Proof. intros [] l e; simpl in *; [ exact (eqZ_sound l (pos 0) e) | exact tt ]. Defined.

Lemma zero_complete : forall z l, AssumedZ z l -> zeroCheck z l = true.
Proof. intros [] l e; simpl in *; [ exact (eqZ_complete l (pos 0) e) | reflexivity ]. Defined.

(* HaruspexExplorer: the explorer's worlds, latent outer and noise inner *)

Fixpoint pairsRow (l : ZInt) (ns : list ZInt) (rest : list World) : list World :=
  match ns with [] => rest | n :: ns' => (l, n) :: pairsRow l ns' rest end.

Fixpoint pairs (ls ns : list ZInt) : list World :=
  match ls with [] => [] | l :: ls' => pairsRow l ns (pairs ls' ns) end.

Definition worlds : list World := pairs range range.

Lemma pairsRow_here : forall l ns rest n, mem n ns -> mem (l, n) (pairsRow l ns rest).
Proof.
  intros l ns rest n m; induction m as [ns' | y ns' m IH]; simpl; [ exact here | exact (there IH) ].
Defined.

Lemma pairsRow_rest : forall l ns rest w, mem w rest -> mem w (pairsRow l ns rest).
Proof.
  intros l ns rest w m; induction ns as [| n ns IH]; simpl; [ exact m | exact (there IH) ].
Defined.

Lemma mem_pairs : forall ls ns l n, mem l ls -> mem n ns -> mem (l, n) (pairs ls ns).
Proof.
  intros ls ns l n ml mn; induction ml as [ls' | l' ls' ml IH]; simpl.
  - exact (pairsRow_here l ns _ n mn).
  - exact (pairsRow_rest l' ns _ (l, n) IH).
Defined.

Lemma pairsRow_mem : forall l ns rest w, mem w (pairsRow l ns rest) ->
  (((latent w = l) * mem (noise w) ns) + mem w rest)%type.
Proof.
  intros l ns rest w; induction ns as [| n ns IH]; simpl; intro m.
  - exact (inr m).
  - destruct (mem_cons m) as [e | m'].
    + subst w; exact (inl (eq_refl, here)).
    + destruct (IH m') as [[e mn] | mr]; [ exact (inl (e, there mn)) | exact (inr mr) ].
Defined.

Lemma pairs_mem : forall ls ns w, mem w (pairs ls ns) -> (mem (latent w) ls * mem (noise w) ns)%type.
Proof.
  intros ls ns w; induction ls as [| l ls IH]; simpl; intro m.
  - destruct (mem_nil m).
  - destruct (pairsRow_mem l ns _ w m) as [[e mn] | mr].
    + rewrite e; exact (here, mn).
    + destruct (IH mr) as [ml mn]; exact (there ml, mn).
Defined.

(* A configuration, declared as a schema and two prompts *)

Definition explorer (cfg : Config) : Schema := {|
  Reading := World;
  readings := worlds;
  Shown := ZInt;
  shows := observeF cfg;
  eqb_shown := eqZ;
  eqb_shown_sound := eqZ_sound;
  eqb_shown_complete := eqZ_complete
|}.

Definition bounded (cfg : Config) (w : World) : bool := natLtb (natAbs (noise w)) (S (noiseBound cfg)).
Definition zeroed (cfg : Config) (w : World) : bool := zeroCheck (assumeZero cfg) (latent w).

Definition stated (cfg : Config) : list (World -> bool) := [bounded cfg; zeroed cfg].

Definition latentQ : Query World := {|
  Value := ZInt;
  value := latent;
  eqb_value := eqZ;
  eqb_value_sound := eqZ_sound;
  eqb_value_complete := eqZ_complete
|}.

Definition presencePrompt (cfg : Config) : Prompt (explorer cfg) :=
  Build_Prompt (explorer cfg) (target cfg) (stated cfg) (claim present).
Definition identityPrompt (cfg : Config) : Prompt (explorer cfg) :=
  Build_Prompt (explorer cfg) (target cfg) (stated cfg) (query latentQ).

(* The evidence contexts admit the same worlds *)

Definition to_finite (cfg : Config) :
  HCandidate (explorer cfg) (target cfg) (stated cfg) -> FiniteCandidate cfg.
Proof.
  intros [w [observed [listed [b [z t]]]]].
  exists w.
  exact (observed, (pairs_mem range range w listed, (lt_sound _ _ b, (zero_sound _ _ z, tt)))).
Defined.

Definition from_finite (cfg : Config) :
  FiniteCandidate cfg -> HCandidate (explorer cfg) (target cfg) (stated cfg).
Proof.
  intros [[l n] [observed [[ml mn] [b [z t]]]]].
  exists (l, n).
  exact (observed, (mem_pairs range range l n ml mn, (lt_complete _ _ b, (zero_complete _ _ z, tt)))).
Defined.

(* The correspondence, decided by normalisation over all 546 configurations *)

Lemma candidates_match :
  map (fun cfg => (candidates (explorer cfg) (target cfg) (stated cfg) : list World)) allConfigs
  = map enumerate allConfigs.
Proof. vm_compute. reflexivity. Qed.

Lemma presence_match :
  map (fun cfg => presence (explorer cfg) (target cfg) (stated cfg) present) allConfigs
  = map presenceC allConfigs.
Proof. vm_compute. reflexivity. Qed.

Lemma identity_match :
  map (fun cfg => identity (explorer cfg) (target cfg) (stated cfg) latentQ) allConfigs
  = map identityC allConfigs.
Proof. vm_compute. reflexivity. Qed.

(* The design's verdict table (docs/proposals/HARUSPEX.adoc). *)
Definition presenceKind (v : Verdict) : Kind :=
  match v with entailed => Sound | refuted => Empty | unresolved => Epi | inconsistent => Empty end.

Definition identityKind (s : IdStatus) : Kind :=
  match s with identified => Sound | unidentified => Epi | no_candidate => Empty end.

Lemma outputs_match :
  ((map (fun cfg => verdict (explorer cfg) (presencePrompt cfg)) allConfigs
    = map (fun cfg => presenceKind (presenceC cfg)) allConfigs) *
   (map (fun cfg => verdict (explorer cfg) (identityPrompt cfg)) allConfigs
    = map (fun cfg => identityKind (identityC cfg)) allConfigs))%type.
Proof. split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Assumptions: each must be closed under the global context.          *)

Print Assumptions holdsAll_sound.
Print Assumptions holdsAll_complete.
Print Assumptions candidate_mem.
Print Assumptions mem_candidate.
Print Assumptions entailed_sound.
Print Assumptions refuted_sound.
Print Assumptions refuted_refutes.
Print Assumptions unresolved_sound.
Print Assumptions inconsistent_sound.
Print Assumptions entailed_complete.
Print Assumptions identified_sound.
Print Assumptions unidentified_sound.
Print Assumptions unidentified_refutes.
Print Assumptions no_candidate_sound.
Print Assumptions identified_complete.
Print Assumptions actual_sound.
Print Assumptions listing_complete_sound.
Print Assumptions sound_given.
Print Assumptions sound_given_query.
Print Assumptions haruspex.
Print Assumptions allConfigs_length.
Print Assumptions to_finite.
Print Assumptions from_finite.
Print Assumptions candidates_match.
Print Assumptions presence_match.
Print Assumptions identity_match.
Print Assumptions outputs_match.

{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Obligation 3 of docs/proposals/HARUSPEX.adoc: Haruspex, run on the certified
-- finite checker's own model, decides exactly what that checker decides.
--
-- Consumes residual-evidence-types by pin:
--   hyperpolymath/residual-evidence-types @ 97244f5cb63bd6697caff261b187b62e9788b692
--
-- Each of the explorer's 546 configurations (ResidualEvidence.Finite.Checker,
-- `allConfigs`) is declared as a Haruspex schema: a reading is a
-- (latent, noise) world in −6..6 × −6..6, it shows the observed sum through
-- the configuration's view, and the prompt states the noise bound and the
-- zero assumption. Then, by `refl` over all 546 configurations:
--
--   candidates-match  Haruspex's candidates are the checker's `enumerate`:
--                     the same worlds, in the same order;
--   presence-match    its claim verdicts are the checker's `presence`;
--   identity-match    its value verdicts are the checker's `identity`;
--   outputs-match     `haruspex` itself answers Sound / Epi / Empty exactly
--                     as those verdicts map in the design's table.
--
-- For every configuration, a Haruspex candidate is a FiniteCandidate and back
-- (to-finite / from-finite): the listing assumption is the checker's InRange,
-- so the two evidence contexts admit the same worlds, and the certified
-- checker's own lemmas (ResidualEvidence.Finite.Soundness) apply to them.

module HaruspexExplorer where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; suc; _<_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import ResidualEvidence.Prelude
open import ResidualEvidence.Finite.Int using (_==ᵢ_; ==ᵢ-sound; ==ᵢ-complete; _∈_; here; there; range)
open import ResidualEvidence.Finite.Row
  using (Verdict; entailed; refuted; unresolved; inconsistent;
         IdStatus; identified; unidentified; no-candidate)
open import ResidualEvidence.Finite.Checker
  using (Config; World; latent; noise; ∣_∣; observe; target; noiseBound; assumeZero;
         zeroCheck; present; enumerate; presence; identity; allConfigs; map;
         InRange; Bounded; Zero; FiniteCandidate)
open import ResidualEvidence.Finite.Soundness
  using (_⊎_; inl; inr; <-sound; <-complete; zero-sound; zero-complete)
open import Haruspex

------------------------------------------------------------------------
-- The explorer's worlds, latent outer and noise inner: the checker's loop order

pairsRow : Int → List Int → List World → List World
pairsRow l []       rest = rest
pairsRow l (n ∷ ns) rest = (l , n) ∷ pairsRow l ns rest

pairs : List Int → List Int → List World
pairs []       ns = []
pairs (l ∷ ls) ns = pairsRow l ns (pairs ls ns)

worlds : List World
worlds = pairs range range

pairsRow-here : ∀ l ns rest n → n ∈ ns → (l , n) ∈ pairsRow l ns rest
pairsRow-here l (_ ∷ ns) rest n here      = here
pairsRow-here l (_ ∷ ns) rest n (there m) = there (pairsRow-here l ns rest n m)

pairsRow-rest : ∀ l ns rest w → w ∈ rest → w ∈ pairsRow l ns rest
pairsRow-rest l []       rest w m = m
pairsRow-rest l (_ ∷ ns) rest w m = there (pairsRow-rest l ns rest w m)

∈-pairs : ∀ ls ns l n → l ∈ ls → n ∈ ns → (l , n) ∈ pairs ls ns
∈-pairs (_ ∷ ls)  ns l n here       mn = pairsRow-here l ns (pairs ls ns) n mn
∈-pairs (l' ∷ ls) ns l n (there ml) mn =
  pairsRow-rest l' ns (pairs ls ns) (l , n) (∈-pairs ls ns l n ml mn)

pairsRow-∈ : ∀ l ns rest w → w ∈ pairsRow l ns rest → ((latent w ≡ l) × (noise w ∈ ns)) ⊎ (w ∈ rest)
pairsRow-extend : ∀ l n ns rest w → ((latent w ≡ l) × (noise w ∈ ns)) ⊎ (w ∈ rest) →
  ((latent w ≡ l) × (noise w ∈ (n ∷ ns))) ⊎ (w ∈ rest)
pairsRow-∈ l []       rest w m         = inr m
pairsRow-∈ l (n ∷ ns) rest _ here      = inl (refl , here)
pairsRow-∈ l (n ∷ ns) rest w (there m) = pairsRow-extend l n ns rest w (pairsRow-∈ l ns rest w m)
pairsRow-extend l n ns rest w (inl (e , mn)) = inl (e , there mn)
pairsRow-extend l n ns rest w (inr m)        = inr m

pairs-∈ : ∀ ls ns w → w ∈ pairs ls ns → (latent w ∈ ls) × (noise w ∈ ns)
pairs-step : ∀ l ls ns w → ((latent w ≡ l) × (noise w ∈ ns)) ⊎ (w ∈ pairs ls ns) →
  (latent w ∈ (l ∷ ls)) × (noise w ∈ ns)
pairs-∈ []       ns w ()
pairs-∈ (l ∷ ls) ns w m = pairs-step l ls ns w (pairsRow-∈ l ns (pairs ls ns) w m)
pairs-step l ls ns w (inl (e , mn)) = ∈-head e , mn
pairs-step l ls ns w (inr m)        = there (fst r) , snd r
  where r = pairs-∈ ls ns w m

------------------------------------------------------------------------
-- A configuration, declared as a schema and two prompts

explorer : Config → Schema
explorer cfg = record
  { Reading    = World
  ; readings   = worlds
  ; Shown      = Int
  ; shows      = observe cfg
  ; _≟_        = _==ᵢ_
  ; ≟-sound    = ==ᵢ-sound
  ; ≟-complete = ==ᵢ-complete
  }

bounded zeroed : Config → World → Bool
bounded cfg w = ∣ noise w ∣ < suc (noiseBound cfg)
zeroed  cfg w = zeroCheck (assumeZero cfg) (latent w)

stated : Config → List (World → Bool)
stated cfg = bounded cfg ∷ zeroed cfg ∷ []

latentQ : Query World
latentQ = record
  { Value = Int ; value = latent ; _==_ = _==ᵢ_
  ; ==-sound = ==ᵢ-sound ; ==-complete = ==ᵢ-complete }

presencePrompt identityPrompt : (cfg : Config) → Prompt (explorer cfg)
presencePrompt cfg = record { shown = target cfg ; assumptions = stated cfg ; ask = claim present }
identityPrompt cfg = record { shown = target cfg ; assumptions = stated cfg ; ask = query latentQ }

------------------------------------------------------------------------
-- The evidence contexts admit the same worlds

module _ (cfg : Config) where
  open Check (explorer cfg) using (HCandidate)

  to-finite : HCandidate (target cfg) (stated cfg) → FiniteCandidate cfg
  to-finite (w , observed , listed , b , z , tt) =
    w , observed , pairs-∈ range range w listed ,
    <-sound (∣ noise w ∣) (noiseBound cfg) b , zero-sound (assumeZero cfg) (latent w) z , tt

  from-finite : FiniteCandidate cfg → HCandidate (target cfg) (stated cfg)
  from-finite ((l , n) , observed , (ml , mn) , b , z , tt) =
    (l , n) , observed , ∈-pairs range range l n ml mn ,
    <-complete (∣ n ∣) (noiseBound cfg) b , zero-complete (assumeZero cfg) l z , tt

------------------------------------------------------------------------
-- The correspondence, decided by normalisation over all 546 configurations

candidates-match :
  map (λ cfg → Check.candidates (explorer cfg) (target cfg) (stated cfg)) allConfigs
  ≡ map enumerate allConfigs
candidates-match = refl

presence-match :
  map (λ cfg → Check.presence (explorer cfg) (target cfg) (stated cfg) present) allConfigs
  ≡ map presence allConfigs
presence-match = refl

identity-match :
  map (λ cfg → Check.identity (explorer cfg) (target cfg) (stated cfg) latentQ) allConfigs
  ≡ map identity allConfigs
identity-match = refl

-- The design's verdict table (docs/proposals/HARUSPEX.adoc).
presenceKind : Verdict → Kind
presenceKind entailed     = Sound
presenceKind refuted      = Empty
presenceKind unresolved   = Epi
presenceKind inconsistent = Empty

identityKind : IdStatus → Kind
identityKind identified   = Sound
identityKind unidentified = Epi
identityKind no-candidate = Empty

outputs-match :
  (map (λ cfg → verdict (explorer cfg) (presencePrompt cfg)) allConfigs
   ≡ map (λ cfg → presenceKind (presence cfg)) allConfigs)
  × (map (λ cfg → verdict (explorer cfg) (identityPrompt cfg)) allConfigs
   ≡ map (λ cfg → identityKind (identity cfg)) allConfigs)
outputs-match = refl , refl

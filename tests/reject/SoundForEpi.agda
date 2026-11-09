{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SoundForEpi where

open import ResidualEvidence.Prelude
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.List using ([]; _∷_)
open import ResidualEvidence.Core
open import ResidualEvidence.Finite.Int using (here; there)
open import Fibre using (incident)
open import Haruspex
open import HaruspexIncident

-- Must fail, and only at the counterexample. A Sound certificate claimed for
-- an Epi prompt: "confirm the migration is COMPLETE" from the record
-- 16 / 16 / 0 / COMPLETE alone. Haruspex answers Epi
-- (HaruspexIncident.confirm-is-epi). The certificate needs every candidate
-- done; split over the listing: (incident, 0) is done and its clause is
-- accepted, the two readings of the other record are not candidates at all,
-- and (incident, 15272) fits the record and is not done, so that clause is
-- refused. The kernel gate requires the error on the marked line.
every : (x : Check.HCandidate incidentSchema incident []) → done (fst x) ≡ true
every (_ , observed , here , tt)                             = refl
every (_ , observed , there here , tt)                       = refl   -- refused here
every (_ , ()       , there (there here) , tt)
every (_ , ()       , there (there (there here)) , tt)
every (_ , _        , there (there (there (there ()))) , tt)

invalid : Check.Certificate incidentSchema incident [] (claim done)
invalid = inhabited ((incident , 0) , refl , here , tt) , every

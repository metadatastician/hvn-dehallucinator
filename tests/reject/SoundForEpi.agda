{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SoundForEpi where

open import ResidualEvidence.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import ResidualEvidence.Core
open import ResidualEvidence.Finite.Int using (here)
open import Fibre using (incident)
open import Haruspex
open import HaruspexIncident

-- Must fail. A Sound certificate claimed for an Epi prompt: "confirm the
-- migration is COMPLETE" from the record 16 / 16 / 0 / COMPLETE alone.
-- Haruspex answers Epi (HaruspexIncident.confirm-is-epi): the reading with
-- 15272 artefacts left fits the record as well as the reading with none, so
-- no certificate that every candidate is done can be given.
invalid : Check.Certificate incidentSchema incident [] (claim done)
invalid = inhabited ((incident , 0) , refl , here , tt) , λ x → refl

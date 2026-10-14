{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module NonZeroComplete where

open import ResidualEvidence.Prelude
open import Fibre using (complete; task; status; running)
open import EngineCore

-- Must fail. A measurement that counts one surviving artefact cannot write
-- COMPLETE (EngineCore.nonzero-not-complete).
invalid : status (after (update (counted 1)) (task 1 0 0 running)) ≡ complete
invalid = refl

{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module AssertedComplete where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import Fibre

-- Must fail. The Incident: state/state.txt was written 16 / 16 / 0 / COMPLETE
-- and never measured. Over that record alone a reading with 15272 survivors
-- fits as well as one with none (Fibre.incident-witness), so COMPLETE cannot
-- be derived from it. Fibre.incident-not-complete proves the negation.
invalid : Holds (unmeasured incident) Complete
invalid (world , observed , unmeasured-evidence) = refl

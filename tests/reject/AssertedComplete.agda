{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module AssertedComplete where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import Fibre

-- Must fail, and only at the counterexample. The Incident: state/state.txt was
-- written 16 / 16 / 0 / COMPLETE and never measured. Split on what remains:
-- the reading with nothing left satisfies COMPLETE and its clause is accepted;
-- every reading with suc n left (15272 is one) fits the same record and
-- refutes it, so that clause is refused. Fibre.incident-not-complete proves
-- the negation. The kernel gate requires the error on the marked line.
invalid : Holds (unmeasured incident) Complete
invalid ((s , zero)  , observed , tt) = refl
invalid ((s , suc n) , observed , tt) = refl   -- refused here

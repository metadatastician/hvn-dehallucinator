{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module TypedZeroComplete where

open import ResidualEvidence.Prelude
open import Fibre using (complete; task; status; running)
open import EngineCore

-- Must fail. The original attack was a typed 0: `update 0` wrote COMPLETE
-- (EngineCore.incident-original). In today's engine the only command that
-- carries a number from the caller is `init`, and it writes RUNNING.
invalid : status (after (init 0) (task 16 16 0 running)) ≡ complete
invalid = refl

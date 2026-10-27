{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EpiForInconsistent where

open import ResidualEvidence.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import ResidualEvidence.Finite.Int using (here; there)
open import Fibre using (incident; incident-measured)
open import Haruspex
open import HaruspexIncident

-- Must fail. An Epi pair claimed for an inconsistent context: "done" asserted
-- on top of the measurement of 15272. Haruspex answers Empty with no case at
-- all (HaruspexIncident.asserted-has-no-case), so there is no reading to put
-- in a pair. The supporting reading below is listed and shows the record, but
-- it cannot satisfy both stated assumptions: 15272 is not 0.
invalid : Check.Pair incidentSchema incident (measured ∷ done ∷ []) (claim done)
invalid =
  (((incident , incident-measured) , refl , there here , refl , refl , tt) , refl) ,
  (((incident , incident-measured) , refl , there here , refl , refl , tt) , refl)

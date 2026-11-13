/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIQuadOpt25.MainResults.Source.AlgorithmModel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DQI state preparation headline

**Statement only — not proved in Qatlib.**

Theorem 1 is recorded as a proposition using explicit two-level operation
lists and executable decoder contracts. No preparation list is constructed.
The resource count is the number of two-level operations, with no local gate
synthesis or preprocessing bound. The exponent is pointwise, not uniform in
the input family. The paper reports a flaw in Algorithm 1 Step 7.

The proved lemma only transfers an assumed preparation contract to the
definitionally equal amplitude vector `dqiState`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults

open Qatlib.Papers.DQIQuadOpt25.MainResults.Source

/-- **Statement only — not proved in Qatlib.**
Numerical preparation contract inspired by Theorem 1. Construction of the
operation list, a uniform polynomial bound and a repair of Step 7 are not
provided. Decoder correctness alone does not imply this proposition. -/
def theorem1_maxQUADSAT_statePrep_statement
    {p n m ℓ : ℕ} [Fact p.Prime]
    (inst : QUADSATInstance p n m) (hinst : IsDiagonalInstance inst)
    (hdec : HasEfficientDecoder (m := m) (n := n) (ℓ := ℓ) (diagVector inst))
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ ℓ) : Prop := ∃ c : ℕ, PreparesIn (dqiAmplitude inst P) ((m + n + p) ^ c + 1)

/-- Transfers an explicitly assumed preparation contract to the definitionally
equal vector `dqiState`. This does not establish state preparation. -/
theorem theorem1_prepares_dqiState
    {p n m ℓ : ℕ} [Fact p.Prime]
    (inst : QUADSATInstance p n m) (hinst : IsDiagonalInstance inst)
    (hdec : HasEfficientDecoder (m := m) (n := n) (ℓ := ℓ) (diagVector inst))
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ ℓ)
    (hprep : theorem1_maxQUADSAT_statePrep_statement inst hinst hdec P hdeg) :
    ∃ c : ℕ, PreparesIn (dqiState inst P) ((m + n + p) ^ c + 1) :=
  hprep

end Qatlib.Papers.DQIQuadOpt25.MainResults

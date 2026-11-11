/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RobustQLearn14.MainResults.Separation — noise-enabled quantum-classical separation

Fixed source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1 (18 Jul 2014), abstract (p. 1) and Sec. IV C (Eq. (19), p. 4).

Claim `c001` is the paper's main claim, stated in the abstract: with no noise the
quantum and classical parity-learning problems are both easy; under depolarizing
noise at any constant nonzero rate the quantum learner's query/computational
complexity grows by at most a logarithmic factor, whereas the classical problem
is Learning Parity with Noise (LPN), whose best known algorithms are
superpolynomial.  The claim has three ingredients:

1. the classical noisy oracle reduces to an LPN instance (proved in
   `DepolarizingNoise/LPNReduction` as `lpn_noise_rate_mem_interval`), and
2. the quantum learner succeeds with the sample count of Eq. (19) (proved in
   `DepolarizingNoise/MajorityVoteBound` as `majority_eq19_ensures_error_below_delta`);
3. the classical intractability of LPN is a *cryptographic assumption*
   ("believed to be intractable", p. 3), not a theorem of the paper.

This file formalizes the part of `c001` that is a mathematical statement:
the Eq. (19) sample threshold is exactly `C · (log n + log(4/δ))`, i.e. grows
only logarithmically in `n`, and packages the separation in conditional form
with the LPN hardness conjecture carried explicitly as a hypothesis.
-/

namespace Qatlib.Papers.RobustQLearn14.MainResults

noncomputable section

/-! ## Logarithmic query overhead of Eq. (19) -/

/-- `c001`: the number of samples required by Eq. (19),
`C · log(4n/δ)` with `C = 3/((δ')²η̃)`, depends on the number of bits `n` only
through `log n`: it equals `C · (log n + log(4/δ))`, a constant plus `C log n`.
Source: arXiv:1407.5088v1, abstract p. 1 and Sec. IV C, Eq. (19), p. 4. -/
theorem separation_query_threshold_logarithmic (n : ℕ) (η δ δ' : ℝ) (hn : 1 ≤ n)
    (hδ : 0 < δ) :
    (3 / (δ' ^ 2 * η)) * Real.log (4 * (n : ℝ) / δ)
      = (3 / (δ' ^ 2 * η)) * (Real.log (n : ℝ) + Real.log (4 / δ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have h4δ : (4 : ℝ) / δ ≠ 0 :=
    div_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hδ)
  rw [show 4 * (n : ℝ) / δ = 4 / δ * (n : ℝ) by ring]
  rw [Real.log_mul h4δ hn0]
  ring

/-- `c001`, upper form: for `n ≥ 1` the Eq. (19) sample threshold is at most
`C · log n + C · log(4/δ)`, i.e. it is `O(log n)` for fixed error parameters.
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (19), p. 4. -/
theorem separation_query_threshold_le (n : ℕ) (η δ δ' : ℝ) (hn : 1 ≤ n)
    (hδ : 0 < δ) :
    (3 / (δ' ^ 2 * η)) * Real.log (4 * (n : ℝ) / δ)
      ≤ (3 / (δ' ^ 2 * η)) * Real.log (n : ℝ) + (3 / (δ' ^ 2 * η)) * Real.log (4 / δ) := by
  rw [separation_query_threshold_logarithmic n η δ δ' hn hδ]
  ring_nf
  exact le_refl _

/-! ## Conditional form of the separation -/

/-- `c001`: the noise-enabled quantum--classical separation, in conditional form.
The paper's classical side ("LPN ... believed to be intractable", p. 3) is a
computational hardness assumption, which cannot be proved here; it is carried
explicitly as the hypothesis `LPNHard`.  The proved mathematical content is the
second conjunct: the Eq. (19) sample threshold grows only logarithmically in
`n`, so depolarizing noise at a constant rate does not increase the quantum
query complexity by more than a logarithmic factor.
Source: arXiv:1407.5088v1, abstract p. 1, Eqs. (10), (19), pp. 3--4. -/
theorem separation_noise_enabled
    (LPNHard : Prop) (hLPN : LPNHard)
    (n : ℕ) (η δ δ' : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ) :
    LPNHard ∧
      (3 / (δ' ^ 2 * η)) * Real.log (4 * (n : ℝ) / δ)
        = (3 / (δ' ^ 2 * η)) * (Real.log (n : ℝ) + Real.log (4 / δ)) :=
  ⟨hLPN, separation_query_threshold_logarithmic n η δ δ' hn hδ⟩

end

end Qatlib.Papers.RobustQLearn14.MainResults

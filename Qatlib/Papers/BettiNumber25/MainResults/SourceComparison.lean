/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BettiNumber25.MainResults.Estimators.SourceComplexity

@[expose] public section


/-!
# Comparison — the paper's main result (Table 1)

Akhalwaya–Bhayat–Connolly–Herbert–Horesh–Sorci–Ubaru,
*Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes*, fixed arXiv:2408.16934v3
(Quantum 9, 1901, 2025), PDF SHA-256
`dcf534a47e98fb6bb6bc34039e64bac6e7ba07fdb7d9b17f781dae1a01fe7848`.

Source main result, Table 1 (p. 3) and the abstract: the four algorithms
QBNE-Chebyshev (Algorithm 3), CBNE-Power (Algorithm 4), CBNE-Chebyshev
(Algorithm 5) and QBNE-Power (Algorithm 6) all yield `(ε, η)`-estimators of
`β_k/|S_k|`, with the following sample (`S`) and query (`Q`) complexities:

| algorithm      | degree `d`          | sample complexity                     | query complexity                       |
|----------------|---------------------|---------------------------------------|----------------------------------------|
| QBNE-Chebyshev | `log(4/ε)/√δ`       | `log(2/η)·d·2^{10d}`                  | `log(2/η)·d²(d+1)·2^{10d}`             |
| CBNE-Power     | `log(2/ε)/δ`        | `(1/ε²)·log(2/η)·2^{2d+1}`            | `d·S`                                  |
| CBNE-Chebyshev | `log(4/ε)/√δ`       | `d³·2^{8d−1}·log(2/η)`                | `d⁴·2^{8d−1}·log(2/η)`                 |
| QBNE-Power     | `log(2/ε)/δ`        | `2·log(2/η)/ε²`  (no `δ`-dependence)  | `d·S`                                  |

The main qualitative conclusion — the point of the paper — is that the
quantum power algorithm (Algorithm 6) has sample complexity `2 log(2/η)/ε²`
independent of the spectral gap `δ`, whereas the classical power algorithm and
both Chebyshev algorithms pay a factor exponential in `d = (1/δ)·log(1/ε)` or
`(1/√δ)·log(1/ε)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BettiNumber25.MainResults.Comparison

open Qatlib.Papers.BettiNumber25.MainResults.Complexity

/-- **Source main result** (Table 1, p. 3; Theorems 4.5, 5.3, 5.7 and 6.3).
All four algorithms of the paper meet the sample and query complexity bounds of
Table 1 simultaneously.  This is the paper's main comparison: the conjunction
of the four complexity theorems, each of which is stated in its own section of
the paper. -/
theorem main_result_comparison (ε η δ : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hη1 : η < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    QBNE_Chebyshev_bounds ε η δ ∧ CBNE_Power_bounds ε η δ ∧
      CBNE_Chebyshev_bounds ε η δ ∧ QBNE_Power_bounds ε η δ :=
  ⟨theorem_4_5_complexity ε η δ hε hη hη1 hδ0 hδ1,
   theorem_5_3_complexity ε η δ hε hη hη1 hδ0 hδ1,
   theorem_5_7_complexity ε η δ hε hη hη1 hδ0 hδ1,
   theorem_6_3_complexity ε η δ hε hη hη1 hδ0 hδ1⟩

/-- **The paper's qualitative main result** (abstract and Table 1, p. 3): the
sample complexity of the quantum power algorithm (Algorithm 6) is
`2 log(2/η)/ε²` and does not depend on the spectral gap `δ`.  This is extracted
from `QBNE_Power_bounds` (Theorem 6.3). -/
theorem qbne_power_sample_complexity_independent_of_delta
    (ε η δ : ℝ) (hε : 0 < ε) (hη : 0 < η) (hη1 : η < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hreg : 1 ≤ Real.log (2 / ε) / δ) :
    ∃ S : ℝ, 0 < S ∧ S = 2 * Real.log (2 / η) / ε ^ 2 ∧
      ∀ δ' : ℝ, 0 < δ' → S = 2 * Real.log (2 / η) / ε ^ 2 := by
  obtain ⟨d, S, Q, _hd0, hS0, _hd, hS, _hQ, hdelta, _hQform⟩ :=
    theorem_6_3_complexity ε η δ hε hη hη1 hδ0 hδ1 hreg
  exact ⟨S, hS0, hS, hdelta⟩

end Qatlib.Papers.BettiNumber25.MainResults.Comparison

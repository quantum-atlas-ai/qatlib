/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
public import Qatlib.Concepts.ShadowModels.ShadowVariance.SparsePauliCovariance
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

@[expose] public section

/-!
# Tensor-Pauli snapshot variance in Euclidean operator-norm form

See [HuangKuengPreskill2020], supplementary Lemma 1 (variance), Theorem 1
(median of means), and Lemma 4 (Pauli second moments) in
[arXiv:2002.08953v2](https://arxiv.org/abs/2002.08953v2).

The frozen tensor-Pauli statistics already give the exact single-word moments
`E[v_w] = re tr(W_w ρ)` and `E[v_w^2] = 3^(|w|)` together with the median-of-means
concentration inequality. The variance estimate uses the operator norm induced by
the Euclidean vector norm.

* `tensor_pauli_word_snapshot_variance_le_opNorm_sq` — the snapshot variance of a
  Pauli-word observable `W_w` is at most `3^(|w|) * ‖W_w‖^2`. Because every tensor
  Pauli word is unitary (`sparsePauliWord_unitary`) and a unitary has Euclidean
  operator norm one (`l2_norm_unitary_eq_one`), the factor `3^(|w|)` from the
  diagonal case of the source's Eq. (S52) gives the same upper bound.
  The constant `3^(|w|)` is exhibited before the universal quantifier over states.
* `tensor_pauli_word_single_median_failure` — for one Pauli-word observable, the
  median-of-means estimator with block size `L`, block count `K`, tolerance `ε` and
  budget hypothesis `4 * 3^(|w|) ≤ L * ε^2` misses the true expectation by more than
  `ε` with probability at most `3^(K/2) / 2^K`, with natural-number division in the
  exponent. This uses the single-observable median-of-means step underlying Theorem 1
  with its own block-size and failure constants.

Both statements are restricted to the tensor-Pauli primitive and to a single Pauli
word; global Clifford observables, quadratic two-copy targets and the multi-observable
`log M` union bound are not re-derived here.
-/

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ClassShadows20.ShadowVariance

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.ReferenceError.RefTraceError

set_option autoImplicit false

/-- The tensor-Pauli snapshot variance of a Pauli-word observable `W_w` on `n` qubits
is at most `3 ^ (tensorPauliWeight w) * ‖W_w‖ ^ 2`, where `‖·‖` denotes the
Euclidean operator norm. Every tensor Pauli word is
unitary, so `‖W_w‖ = 1` and the bound equals the Pauli second moment `3 ^ (|w|)`,
uniformly over all density states `ρ` on a non-degenerate (`0 < n`) system. -/
theorem tensor_pauli_word_snapshot_variance_le_opNorm_sq (n : ℕ) (_hn : 0 < n)
    (w : Fin n → Option (Fin 3)) :
    let bound := (3 : ℝ) ^ tensorPauliWeight w * ‖tensorPauliWord n w‖ ^ 2
    ∀ (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ),
      (tensorPauliLaw n ρ hρ).variance (tensorPauliValue w) ≤ bound := by
  dsimp only
  intro ρ hρ
  have hv := (tensor_pauli_word_exact_moments n ρ hρ w).2.2.2
  have : Nonempty (Fin (2 ^ n)) := ⟨⟨0, Nat.two_pow_pos n⟩⟩
  have hnorm : ‖tensorPauliWord n w‖ = 1 :=
    l2_norm_unitary_eq_one (sparsePauliWord_unitary n w)
  rw [hv, hnorm, one_pow, mul_one]
  linarith [sq_nonneg (Matrix.trace (tensorPauliWord n w * ρ)).re]

/-- For a single Pauli-word observable `W_w` on a non-degenerate (`0 < n`) system, the
median-of-means estimator over `K` blocks of `L` fresh tensor-Pauli records deviates
from the true expectation `re tr(W_w ρ)` by more than `ε > 0` with probability at most
`3 ^ (K / 2) / 2 ^ K`, provided the budget hypothesis `4 * 3 ^ (|w|) ≤ L * ε ^ 2` holds.
This is a single-observable bound using the median-of-means step of Theorem 1. -/
theorem tensor_pauli_word_single_median_failure (n : ℕ) (_hn : 0 < n)
    (w : Fin n → Option (Fin 3))
    (L K : ℕ) (ε : ℝ) (hL : 0 < L) (hK : 0 < K) (hε : 0 < ε)
    (hbud : 4 * (3 : ℝ) ^ tensorPauliWeight w ≤ (L : ℝ) * ε ^ 2) :
    let bound := (3 : ℝ) ^ (K / 2) / 2 ^ K
    ∀ (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ),
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → (Fin n → Fin 3 × Bool) =>
          ε < |(tensorPauliLaw n ρ hρ).medianOfMeans (tensorPauliValue w) ω -
            (Matrix.trace (tensorPauliWord n w * ρ)).re|),
        ∏ k, (tensorPauliLaw n ρ hρ).probOf (ω k)) ≤ bound := by
  dsimp only
  intro ρ hρ
  have hv := (tensor_pauli_word_exact_moments n ρ hρ w).2.2.2
  have hvle : (tensorPauliLaw n ρ hρ).variance (tensorPauliValue w)
      ≤ (3 : ℝ) ^ tensorPauliWeight w := by
    rw [hv]
    linarith [sq_nonneg (Matrix.trace (tensorPauliWord n w * ρ)).re]
  have hvar : 4 * (tensorPauliLaw n ρ hρ).variance (tensorPauliValue w)
      ≤ (L : ℝ) * ε ^ 2 :=
    (mul_le_mul_of_nonneg_left hvle (by norm_num : (0 : ℝ) ≤ 4)).trans hbud
  have h := (tensorPauliLaw n ρ hρ).median_of_means_concentration (tensorPauliValue w)
    hL hK ε hε hvar
  have hmean := (tensor_pauli_word_exact_moments n ρ hρ w).2.1
  rw [hmean] at h
  exact h

end Qatlib.Papers.ClassShadows20.ShadowVariance

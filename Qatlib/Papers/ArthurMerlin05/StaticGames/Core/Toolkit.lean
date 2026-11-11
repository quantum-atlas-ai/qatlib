/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Channels.Dual
import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel

/-!
# Toolkit — acceptance operators, traces, and spectral bounds

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
§3 (Definition 3.1, proofs of Theorems 3.3/3.4/3.6).

This file collects the finite-dimensional linear-algebra facts that the paper
uses repeatedly when it passes from a verification circuit `A_x` to its
acceptance operator `Q_x = (I_m ⊗ ⟨0^k|) A_x† Π₁ A_x (I_m ⊗ |0^k⟩)`:

* `acceptProb_eq_trace`: the Born probability `⟨ψ|Q|ψ⟩` equals
  `tr(Q |ψ⟩⟨ψ|)`;
* `trace_re_nonneg_of_posSemidef`: a positive semidefinite operator has
  nonnegative trace (real part);
* `expectation_le_trace`: for a positive semidefinite `Q` every unit vector
  satisfies `⟨ψ|Q|ψ⟩ ≤ tr Q` (the operator trace dominates its largest
  eigenvalue, which is the `tr Q ≥ 3/4` step in the proof of Theorem 3.4);
* `trace_le_dim_mul_bound`: if `Q ≤ b • 1` then `tr Q ≤ dim · b` (the
  `tr Q ≤ 2^m · 2^{−m−2} ≤ 1/4` step of the same proof);
* `trace_totally_mixed`: `tr(Q · 2^{−m} I) = 2^{−m} tr Q`, the acceptance
  identity for the totally mixed witness of Theorem 3.6;
* `average_basis_acceptance`: averaging `⟨i|Q|i⟩` over the computational basis
  gives `tr Q / dim`.

None of these are definitions restating a paper conclusion: each is a genuine
matrix identity or inequality, proved from positivity and trace cyclicity.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Core

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- The cyclic form `tr(Q |ψ⟩⟨ψ|) = ⟨ψ|Q|ψ⟩` used throughout §3 of the
paper. -/
theorem trace_mul_outerProduct {D : ℕ} (Q : Operator D) (ψ : QState (Fin D)) :
    Matrix.trace (Q * outerProduct ψ) =
      Qatlib.Foundations.PureStateMath.Inner ψ (Q *ᵥ ψ) := by
  unfold Qatlib.Foundations.PureStateMath.Inner Matrix.mulVec
    outerProduct Matrix.trace
  simp only [dotProduct, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [starRingEnd_apply, Pi.star_apply]
  ring

/-- The Born acceptance probability `⟨ψ|Q|ψ⟩` of an acceptance operator `Q`
equals `tr(Q |ψ⟩⟨ψ|)` (the cyclic form used throughout §3 of the paper). -/
theorem acceptProb_eq_trace {m : ℕ} (Q : Operator (Qdim m))
    (ψ : QState (Fin (Qdim m))) :
    acceptProb Q ψ = (Matrix.trace (Q * outerProduct ψ)).re := by
  unfold acceptProb
  rw [trace_mul_outerProduct]

/-- The real part of the trace of a positive semidefinite operator is
nonnegative. -/
theorem trace_re_nonneg_of_posSemidef {D : ℕ} {A : Operator D}
    (hA : A.PosSemidef) : 0 ≤ (Matrix.trace A).re :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

/-- A unit vector's expectation against a positive semidefinite operator is at
most the operator's trace: the `tr Q ≥ ⟨ψ|Q|ψ⟩` step of Theorem 3.4. -/
theorem expectation_le_trace {D : ℕ} {Q : Operator D} (hQ : Q.PosSemidef)
    {ψ : QState (Fin D)} (hψ : Normalized ψ) :
    (Qatlib.Foundations.PureStateMath.Inner ψ (Q *ᵥ ψ)).re ≤ (Matrix.trace Q).re := by
  have hP : (outerProduct ψ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (isOrthogonalProjector_outerProduct hψ).nonneg
  have hIP : ((1 : Operator D) - outerProduct ψ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (isOrthogonalProjector_outerProduct hψ).one_sub_nonneg
  have htr : 0 ≤ (Q * (1 - outerProduct ψ)).trace :=
    Matrix.PosSemidef.trace_mul_nonneg hQ hIP
  have hre : 0 ≤ ((Q * (1 - outerProduct ψ)).trace).re :=
    (Complex.nonneg_iff.mp htr).1
  have hsplit : Q * (1 - outerProduct ψ) = Q - Q * outerProduct ψ := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  have hQP : (Q * outerProduct ψ).trace =
      Qatlib.Foundations.PureStateMath.Inner ψ (Q *ᵥ ψ) :=
    trace_mul_outerProduct Q ψ
  rw [hsplit, Matrix.trace_sub, Complex.sub_re, hQP] at hre
  linarith

/-- If `Q ≤ b • 1` then `tr Q ≤ dim Q · b`: the eigenvalue-counting step
`tr Q_x ≤ 2^m · 2^{−m−2}` in the proof of Theorem 3.4. -/
theorem trace_le_dim_mul_bound {D : ℕ} {Q : Operator D} {b : ℝ}
    (hQ : Q ≤ (b : ℂ) • (1 : Operator D)) :
    (Matrix.trace Q).re ≤ D * b := by
  have hpsd : ((b : ℂ) • (1 : Operator D) - Q).PosSemidef :=
    Matrix.le_iff.mp hQ
  have htr : 0 ≤ (((b : ℂ) • (1 : Operator D) - Q).trace).re :=
    trace_re_nonneg_of_posSemidef hpsd
  have htrace : ((b : ℂ) • (1 : Operator D) - Q).trace
      = b * (D : ℂ) - Matrix.trace Q := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp [Fintype.card_fin]
  rw [htrace, Complex.sub_re, Complex.mul_re] at htr
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at htr
  have hDre : ((D : ℂ)).re = (D : ℝ) := by simp
  rw [hDre] at htr
  linarith

/-- Accepting on the totally mixed witness `2^{−m} I` yields exactly
`2^{−m} tr Q`; this is the acceptance identity in the proof of Theorem 3.6. -/
theorem trace_totally_mixed {m : ℕ} (Q : Operator (Qdim m)) :
    Matrix.trace (Q * (((1 / (Qdim m : ℝ) : ℂ)) • (1 : Operator (Qdim m))))
      = (1 / (Qdim m : ℝ) : ℂ) * Matrix.trace Q := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- Averaging the diagonal Born probabilities `⟨i|Q|i⟩` over the computational
basis gives `(tr Q) / dim`: the `2^{−m} tr(Q_x)` average acceptance of the
totally mixed witness in Theorem 3.6. -/
theorem average_basis_acceptance {D : ℕ} [NeZero D] (Q : Operator D) :
    (∑ i : Fin D, Q i i) = Matrix.trace Q := rfl

/-- Dividing that basis average by the dimension returns `tr Q / dim`. -/
theorem average_basis_acceptance_div {D : ℕ} [NeZero D] (Q : Operator D) :
    (∑ i : Fin D, Q i i) / (D : ℂ) = Matrix.trace Q / (D : ℂ) := by
  rw [average_basis_acceptance]

end Qatlib.Papers.ArthurMerlin05.StaticGames.Core

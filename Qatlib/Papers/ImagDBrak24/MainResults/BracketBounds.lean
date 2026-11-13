/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Qatlib.Papers.ImagDBrak24.MainResults.SourceDynamics
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace

set_option backward.isDefEq.respectTransparency false

/-!
# Double-Bracket Commutator and Remainder Bounds (Lemmas 7--10)

This module formalizes Lemmas 7, 8, 9, and 10 (pp. 17--18) of Gluza, Son, Tiang,
and Ng, proving the operator-norm second-moment bound, the exact
Hilbert--Schmidt bracket-variance duality `‖[Ĥ, Ω]‖_HS^2 = 2 V(Ω)`, the
exponential perturbation bound `‖1 - e^{[Ĥ, Ω]}‖_HS ≤ 2 √V(Ω)`, and the
second-order linear-approximation remainder bound `‖R_r‖_HS ≤ r^2 V(Ω)`.

## Main statements

* `lemma7_secondMomentBound`: Lemma 7, `Re ⟨φ| Ĥ Â Ĥ |φ⟩ ≤ Re ⟨φ| Ĥ^2 |φ⟩ c`
  under operator-norm bound `c`.
* `lemma8_bracketPerturbation`: Lemma 8,
  `hsNorm (1 - exp [Ĥ, Ω]) ≤ 2 √(energyVariance lam ψ)`.
* `lemma9_bracketVarianceDuality`: Lemma 9, Equation (71),
  `hsNormSq [Ĥ, Ω] = 2 * energyVariance lam ψ`.
* `lemma10_linearApproxRemainder`: Lemma 10, Equations (73)--(77),
  `hsNorm (exp (-r [Ĥ, Ω]) - 1 + r [Ĥ, Ω]) ≤ r^2 * energyVariance lam ψ`.

## References

* [Gluza, Son, Tiang, and Ng, 2024][GluzaEtAl2024ImagDBrak], Lemmas 7--10,
  pp. 17--18.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Matrix
open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Frobenius

omit [DecidableEq ι] in
private lemma vdot_re_le (x y : ι → ℂ) :
    (vdot x y).re ≤ twoNorm x * twoNorm y := by
  calc
    (vdot x y).re = ∑ i, (star (x i) * y i).re := by simp [vdot]
    _ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul, norm_star] using Complex.re_le_norm (star (x i) * y i)
    _ ≤ twoNorm x * twoNorm y := by
      simpa only [twoNorm, normSq, Complex.normSq_eq_norm_sq] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖x i‖) (fun i => ‖y i‖)

private lemma bracket_entry (lam : ι → ℝ) (ψ : ι → ℂ) (i j : ι) :
    commutator (diagHam lam) (pureState ψ) i j =
      ((lam i - lam j : ℝ) : ℂ) * (ψ i * star (ψ j)) := by
  simp [commutator, diagHam, diagonal_mul, mul_diagonal, pureState]
  ring

private lemma bracket_variance (lam : ι → ℝ) (ψ : ι → ℂ) (hψ : IsState ψ) :
    hsNormSq (commutator (diagHam lam) (pureState ψ)) = 2 * energyVariance lam ψ := by
  have hw : ∑ i, weight ψ i = 1 := hψ
  have he : ∀ i j,
      Complex.normSq (commutator (diagHam lam) (pureState ψ) i j) =
        lam i ^ 2 * weight ψ i * weight ψ j -
          2 * (lam i * weight ψ i) * (lam j * weight ψ j) +
          weight ψ i * (lam j ^ 2 * weight ψ j) := by
    intro i j
    rw [bracket_entry]
    simp only [Complex.star_def, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_conj, weight]
    ring
  unfold hsNormSq
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hw]
  unfold energyVariance secondMoment expectedEnergy
  ring_nf
  rw [← Finset.sum_mul]
  ring

private lemma hsNorm_eq_frobenius (A : Matrix ι ι ℂ) : hsNorm A = ‖A‖ := by
  simp only [hsNorm, hsNormSq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.rpow_two, Complex.normSq_eq_norm_sq]

omit [DecidableEq ι] in
private lemma trace_adj_mul (A : Matrix ι ι ℂ) :
    Matrix.trace (Aᴴ * A) = (hsNormSq A : ℂ) := by
  unfold Matrix.trace hsNormSq
  simp only [diag_apply, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => star_mul_self_eq_normSq (A i j)

private lemma frobenius_mul_unitary (U A : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) :
    ‖U * A‖ = ‖A‖ := by
  rw [← hsNorm_eq_frobenius, ← hsNorm_eq_frobenius]
  unfold hsNorm
  congr 1
  apply Complex.ofReal_injective
  rw [← trace_adj_mul, ← trace_adj_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, one_mul]

private lemma skew_exp_unitary (K : Matrix ι ι ℂ) (hK : Kᴴ = -K) (t : ℝ) :
    (NormedSpace.exp (t • K))ᴴ * NormedSpace.exp (t • K) = 1 := by
  have ht : (t • K)ᴴ = -(t • K) := by
    simp [conjTranspose_smul, hK]
  rw [← Matrix.exp_conjTranspose, ht, ← Matrix.exp_add_of_commute _ _
    ((Commute.refl (t • K)).neg_left)]
  simp

private lemma skew_exp_mul_bound (K A : Matrix ι ι ℂ) (hK : Kᴴ = -K)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • K) * A - A‖ ≤ ‖K * A‖ * t := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • K) * A)
      (NormedSpace.exp (s • K) * (K * A)) s := by
    simpa only [Matrix.mul_assoc] using
      (hasDerivAt_exp_smul_const K s).mul_const A
  have hb (s : ℝ) : ‖NormedSpace.exp (s • K) * (K * A)‖ ≤ ‖K * A‖ :=
    (frobenius_mul_unitary _ _ (skew_exp_unitary K hK s)).le
  simpa using norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := t) (fun s _ => (hd s).hasDerivWithinAt)
    (fun s _ => hb s) t ⟨ht, le_rfl⟩

-- Compare the remainder with the quadratic function whose derivative bounds its norm.
private lemma skew_exp_remainder (K : Matrix ι ι ℂ) (hK : Kᴴ = -K) :
    ‖NormedSpace.exp K - 1 - K‖ ≤ ‖K‖ ^ 2 / 2 := by
  let f : ℝ → Matrix ι ι ℂ := fun t => NormedSpace.exp (t • K) - 1 - t • K
  have hd (t : ℝ) : HasDerivAt f (NormedSpace.exp (t • K) * K - K) t := by
    convert! ((hasDerivAt_exp_smul_const K t).sub_const 1).sub
      ((hasDerivAt_id t).smul_const K) using 1
    simp only [one_smul]
  have hB (t : ℝ) : HasDerivAt (fun t : ℝ => ‖K * K‖ * t ^ 2 / 2)
      (‖K * K‖ * t) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul ‖K * K‖).div_const 2 using 1
    simp only [id_eq]
    ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) (by simp [f]) hB
    (fun t ht => skew_exp_mul_bound K K hK t ht.1) (x := 1) ⟨zero_le_one, le_rfl⟩
  have hm := Matrix.frobenius_norm_mul K K
  simp only [f, one_smul, one_pow, mul_one] at h
  nlinarith

private lemma bracket_skew (lam : ι → ℝ) (ψ : ι → ℂ) :
    (commutator (diagHam lam) (pureState ψ))ᴴ =
      -commutator (diagHam lam) (pureState ψ) := by
  have hH : (diagHam lam)ᴴ = diagHam lam := by simp [diagHam]
  have hP : (pureState ψ)ᴴ = pureState ψ := pureState_isHermitian ψ
  simp only [commutator, conjTranspose_sub, conjTranspose_mul, hH,
    hP, neg_sub]

/-- **Lemma 7** (Second moment bound, p.17). Let `Â` be Hermitian with operator
norm at most `c`, i.e. `‖Â x‖ ≤ c ‖x‖` for all `x` (`hcop`). Then for any state
vector `φ`

`⟨φ| Ĥ Â Ĥ |φ⟩ ≤ ⟨φ| Ĥ² |φ⟩ · c`

(the real expectation values; `Ĥ = diag λ` in its eigen-basis). -/
theorem lemma7_secondMomentBound
    (lam : ι → ℝ) (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c) (hcop : ∀ x : ι → ℂ, twoNorm (A *ᵥ x) ≤ c * twoNorm x)
    (φ : ι → ℂ) (hφ : IsState φ) :
    (expVal (diagHam lam * A * diagHam lam) φ).re
      ≤ (expVal (diagHam lam * diagHam lam) φ).re * c := by
  by_cases _htriv : A.IsHermitian ∧ 0 ≤ c ∧ IsState φ
  swap
  · exact False.elim (_htriv ⟨hA, hc, hφ⟩)
  let x := diagHam lam *ᵥ φ
  have hmove (y : ι → ℂ) : vdot φ (diagHam lam *ᵥ y) = vdot x y := by
    simp [x, vdot, diagHam, mulVec_diagonal, mul_assoc, mul_comm]
  have hsecond : (expVal (diagHam lam * diagHam lam) φ).re = twoNorm x ^ 2 := by
    rw [expVal, ← Matrix.mulVec_mulVec, hmove, vdot_self]
    exact (Real.sq_sqrt (normSq_nonneg x)).symm
  rw [hsecond, expVal, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmove]
  calc
    (vdot x (A *ᵥ x)).re ≤ twoNorm x * twoNorm (A *ᵥ x) := vdot_re_le _ _
    _ ≤ twoNorm x * (c * twoNorm x) :=
      mul_le_mul_of_nonneg_left (hcop x) (Real.sqrt_nonneg _)
    _ = twoNorm x ^ 2 * c := by ring

/-- **Lemma 8** (Bracket perturbation, p.17). Let `Ĥ = diag λ` be Hermitian and
`Ω = |ψ⟩⟨ψ|` a pure state. Then
`‖1 - e^{[Ĥ,Ω]}‖_HS ≤ 2 √(V(Ω))`, where `V(Ω)` is the energy variance.
(The paper states the bound for the operator norm; the Hilbert–Schmidt norm
used here makes the bound stronger, see the module note.) -/
theorem lemma8_bracketPerturbation
    (lam : ι → ℝ) (ψ : ι → ℂ) (hψ : IsState ψ) :
    hsNorm ((1 : Matrix ι ι ℂ) - NormedSpace.exp (commutator (diagHam lam) (pureState ψ)))
      ≤ 2 * Real.sqrt (energyVariance lam ψ) := by
  have hv := bracket_variance lam ψ hψ
  have hn : 0 ≤ energyVariance lam ψ := by
    have : 0 ≤ hsNormSq (commutator (diagHam lam) (pureState ψ)) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    linarith
  have hb := skew_exp_mul_bound (commutator (diagHam lam) (pureState ψ)) 1
    (bracket_skew lam ψ) 1 zero_le_one
  simp only [one_smul, mul_one] at hb
  rw [← norm_sub_rev, ← hsNorm_eq_frobenius, ← hsNorm_eq_frobenius] at hb
  refine hb.trans ?_
  rw [hsNorm, hv]
  have hs := Real.sq_sqrt hn
  have hs2 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn)
  nlinarith [Real.sqrt_nonneg (energyVariance lam ψ),
    Real.sqrt_nonneg (2 * energyVariance lam ψ)]

/-- **Lemma 9** (Bracket–variance duality, Eq. (71), p.17). For a Hamiltonian
`Ĥ = diag λ` and a pure state `Ω = |ψ⟩⟨ψ|`,

`‖[Ĥ, Ω]‖_HS² = 2 V(Ω) = 2⟨Ω|Ĥ²|Ω⟩ - 2⟨Ω|Ĥ|Ω⟩²`. -/
theorem lemma9_bracketVarianceDuality
    (lam : ι → ℝ) (ψ : ι → ℂ) (hψ : IsState ψ) :
    hsNormSq (commutator (diagHam lam) (pureState ψ)) = 2 * energyVariance lam ψ := by
  exact bracket_variance lam ψ hψ

/-- **Lemma 10** (Linear-approximation remainder of the QITE DBR, Eq. (73)-(77),
p.18). For `R_r := e^{-r[Ĥ,Ω]} - 1 + r[Ĥ,Ω]` with `Ω = |ψ⟩⟨ψ|` pure,
`‖R_r‖_HS ≤ r² V(Ω)`. -/
theorem lemma10_linearApproxRemainder
    (lam : ι → ℝ) (ψ : ι → ℂ) (hψ : IsState ψ) (r : ℝ) :
    hsNorm (NormedSpace.exp (((-(r : ℝ)) : ℂ) • commutator (diagHam lam) (pureState ψ))
        - 1 + ((r : ℝ) : ℂ) • commutator (diagHam lam) (pureState ψ))
      ≤ r ^ 2 * energyVariance lam ψ := by
  let K := commutator (diagHam lam) (pureState ψ)
  have hK : Kᴴ = -K := bracket_skew lam ψ
  have hrK : (((-r : ℝ) : ℂ) • K)ᴴ = -(((-r : ℝ) : ℂ) • K) := by
    simp [conjTranspose_smul, hK]
  have hb := skew_exp_remainder (((-r : ℝ) : ℂ) • K) hrK
  have he : NormedSpace.exp (((-r : ℝ) : ℂ) • K) - 1 - (((-r : ℝ) : ℂ) • K) =
      NormedSpace.exp (((-r : ℝ) : ℂ) • K) - 1 + (r : ℂ) • K := by
    simp
  rw [he, ← hsNorm_eq_frobenius] at hb
  simp only [Complex.ofReal_neg] at hb
  refine hb.trans_eq ?_
  rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← hsNorm_eq_frobenius, hsNorm, Real.sq_sqrt]
  · rw [show hsNormSq K = 2 * energyVariance lam ψ from bracket_variance lam ψ hψ]
    ring
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

end Qatlib.Papers.ImagDBrak24.MainResults

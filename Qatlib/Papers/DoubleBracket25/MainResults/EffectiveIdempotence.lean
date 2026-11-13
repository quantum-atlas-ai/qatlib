/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket25.MainResults.Definitions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option backward.isDefEq.respectTransparency false

/-!
# Effective Idempotence of Pure-State Commutator Exponentials

This module formalizes Proposition B.2 and Lemma B.3 (Appendix B.2,
Equations (61)--(73), pp. 22--23) of Suzuki et al., proving the exact rank-two
trigonometric closed form `e^{s[Ψ, H]} = I + A(s)[Ψ, H] + B(s)([Ψ, H])^2` and
the linear-polynomial state-synthesis identity for `(x I + y H)|ψ⟩ / ‖(x I + y H)|ψ⟩‖`.

## Main definitions

* `durationB3`: Duration parameter `s_Ψ` of Equation (70) implementing a real
  linear combination `(x I + y H)|ψ⟩`.

## Main statements

* `SourcePropositionB2`: Proposition B.2, Equations (61)--(62), closed-form
  expansion of `bracketExp s (pureDM ψ) H`.
* `SourceLemmaB3`: Lemma B.3, Equations (70)--(73), normalized linear-polynomial
  action via `aCoeff` and `bCoeff` at `durationB3`.

## References

* [Suzuki et al., 2025][SuzukiEtAl2025DoubleBracket], Appendix B.2,
  Proposition B.2 and Lemma B.3, pp. 22--23.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.DoubleBracket25.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private instance realMatrixNormedAlgebra : NormedAlgebra ℝ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Matrix ι ι ℂ)

omit [DecidableEq ι] in
private lemma inner_conj (u v : ι → ℂ) : star (vecInner u v) = vecInner v u := by
  simp [vecInner, mul_comm]

omit [DecidableEq ι] in
private lemma inner_adjoint (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (u v : ι → ℂ) : vecInner (H.mulVec u) v = vecInner u (H.mulVec v) := by
  change star (H *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (H *ᵥ v)
  rw [star_mulVec, hH.eq, dotProduct_mulVec]

omit [DecidableEq ι] in
private lemma inner_combination (u v : ι → ℂ) (a b : ℂ) :
    vecInner (a • u + b • v) (a • u + b • v) =
      (star a * a) * vecInner u u + (star a * b) * vecInner u v +
      (star b * a) * vecInner v u + (star b * b) * vecInner v v := by
  simp only [vecInner, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [DecidableEq ι] in
private lemma inner_self_sum (u : ι → ℂ) :
    vecInner u u = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
  simp [vecInner, Complex.normSq_eq_conj_mul_self]

omit [DecidableEq ι] in
private lemma state_moments (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ψ : ι → ℂ) (hψ : vecInner ψ ψ = 1) :
    vecInner ψ (H.mulVec ψ) = (energy H ψ : ℂ) ∧
    vecInner (H.mulVec ψ) (H.mulVec ψ) =
      ((energyVariance H ψ + energy H ψ ^ 2 : ℝ) : ℂ) ∧
    vecInner (H.mulVec ψ - (energy H ψ : ℂ) • ψ)
      (H.mulVec ψ - (energy H ψ : ℂ) • ψ) = (energyVariance H ψ : ℂ) := by
  have hreal : ∀ u : ι → ℂ, vecInner u (H.mulVec u) = (energy H u : ℂ) := by
    intro u
    have hc := hH.star_dotProduct_mulVec_comm u u
    change star (vecInner u (H.mulVec u)) = vecInner u (H.mulVec u) at hc
    apply Complex.ext
    · rfl
    · have hi := congrArg Complex.im hc
      simp only [Complex.star_def, Complex.conj_im] at hi
      simp only [Complex.ofReal_im]
      linarith
  have hsecond : vecInner (H.mulVec ψ) (H.mulVec ψ) =
      ((energyVariance H ψ + energy H ψ ^ 2 : ℝ) : ℂ) := by
    rw [inner_adjoint H hH, Matrix.mulVec_mulVec]
    have hr := inner_self_sum (H.mulVec ψ)
    rw [inner_adjoint H hH, Matrix.mulVec_mulVec] at hr
    apply Complex.ext
    · simp [energyVariance]
    · simpa only [Complex.ofReal_im] using congrArg Complex.im hr
  refine ⟨hreal ψ, hsecond, ?_⟩
  have hc := inner_conj ψ (H.mulVec ψ)
  rw [hreal ψ] at hc
  rw [show H.mulVec ψ - (energy H ψ : ℂ) • ψ =
      (-(energy H ψ : ℂ)) • ψ + (1 : ℂ) • H.mulVec ψ by module]
  rw [inner_combination, hψ, hreal ψ, ← hc, hsecond]
  simp only [star_neg, star_one, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

omit [DecidableEq ι] in
private lemma variance_nonneg (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ψ : ι → ℂ) (hψ : vecInner ψ ψ = 1) : 0 ≤ energyVariance H ψ := by
  have hm := (state_moments H hH ψ hψ).2.2
  rw [inner_self_sum] at hm
  have hr := congrArg Complex.re hm
  simp only [Complex.ofReal_re] at hr
  rw [← hr]
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

omit [DecidableEq ι] in
private lemma rank_mul (u v w z : ι → ℂ) :
    vecMulVec u (star v) * vecMulVec w (star z) =
      vecInner v w • vecMulVec u (star z) := by
  rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  rfl

omit [DecidableEq ι] in
private lemma comm_rank (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (ψ : ι → ℂ) :
    comm (pureDM ψ) H =
      vecMulVec ψ (star (H.mulVec ψ)) - vecMulVec (H.mulVec ψ) (star ψ) := by
  change vecMulVec ψ (star ψ) * H - H * vecMulVec ψ (star ψ) = _
  rw [vecMulVec_mul, mul_vecMulVec, star_mulVec, hH.eq]

omit [DecidableEq ι] in
private lemma comm_cube (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (ψ : ι → ℂ) (hψ : vecInner ψ ψ = 1) :
    comm (pureDM ψ) H * comm (pureDM ψ) H * comm (pureDM ψ) H =
      -(energyVariance H ψ : ℂ) • comm (pureDM ψ) H := by
  obtain ⟨hE, hHH, _⟩ := state_moments H hH ψ hψ
  have hE' := inner_conj ψ (H.mulVec ψ)
  rw [hE] at hE'
  rw [comm_rank H hH ψ]
  simp only [sub_mul, mul_sub, smul_mul_assoc, rank_mul,
    hψ, hE, ← hE', hHH, Complex.star_def, Complex.conj_ofReal, one_smul, smul_smul]
  push_cast
  module

private lemma exp_of_cube (K : Matrix ι ι ℂ) (V s : ℝ) (hV : 0 < V)
    (hK : K * K * K = -(V : ℂ) • K) :
    NormedSpace.exp ((s : ℂ) • K) = 1 +
      ((Real.sin (s * Real.sqrt V) / Real.sqrt V : ℝ) : ℂ) • K +
      (((1 - Real.cos (s * Real.sqrt V)) / V : ℝ) : ℂ) • K ^ 2 := by
  -- The cubic relation makes the quadratic expression solve F' = K * F.
  -- Multiplication by exp (-tK) then gives a function with zero derivative.
  let v := Real.sqrt V
  have hv : 0 < v := Real.sqrt_pos.2 hV
  have hv2 : v * v = V := by simpa [v, pow_two] using Real.sq_sqrt hV.le
  let F : ℝ → Matrix ι ι ℂ := fun t =>
    1 + (Real.sin (t * v) / v) • K + ((1 - Real.cos (t * v)) / V) • K ^ 2
  have hcast (r : ℝ) (A : Matrix ι ι ℂ) : (r : ℂ) • A = r • A := by
    exact IsScalarTower.algebraMap_smul ℂ r A
  have hKr : K * K * K = -V • K := by
    rw [← hcast]
    simpa only [Complex.ofReal_neg] using hK
  have hF (t : ℝ) : HasDerivAt F (K * F t) t := by
    have hd := (hasDerivAt_id t).mul_const v
    have ha := (hd.sin.div_const v).smul_const K
    have hb := (((hasDerivAt_const t (1 : ℝ)).sub hd.cos).div_const V).smul_const
      (K ^ 2)
    convert ((hasDerivAt_const t (1 : Matrix ι ι ℂ)).add ha).add hb using 1
    · rfl
    · dsimp [F]
      simp only [one_mul, zero_add, mul_one, mul_add, mul_smul_comm, pow_two,
        ← mul_assoc, hKr, smul_smul]
      have h1 : Real.cos (t * v) * v / v = 1 - (1 - Real.cos (t * v)) / V * V := by
        field_simp
        ring
      have h2 : (0 - -(Real.sin (t * v)) * v) / V = Real.sin (t * v) / v := by
        rw [← hv2]
        field_simp
        ring
      rw [h1, h2]
      module
  let G : ℝ → Matrix ι ι ℂ := fun t => NormedSpace.exp (t • (-K)) * F t
  have hG (t : ℝ) : HasDerivAt G 0 t := by
    convert (hasDerivAt_exp_smul_const (-K) t).mul (hF t) using 1
    simp only [mul_neg, neg_mul, Matrix.mul_assoc, neg_add_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun t => (hG t).differentiableAt)
    (fun t => (hG t).deriv) s 0
  have he : NormedSpace.exp (s • (-K)) * F s = 1 := by
    simpa [G, F] using hconst
  have hinv : NormedSpace.exp (s • K) * NormedSpace.exp (s • (-K)) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (s • K)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have hh := congrArg (NormedSpace.exp (s • K) * ·) he
  rw [← Matrix.mul_assoc, hinv, one_mul, mul_one] at hh
  rw [hcast, hcast, hcast]
  exact hh.symm

/-- The duration `s_Ψ` of Lemma B.3, Eq. (70):
`-(sgn y)/√V_Ψ · arccos((x + y E_Ψ)/‖(xI+yH)|ψ⟩‖)`. -/
def durationB3 (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (x y : ℝ) : ℝ :=
  -(Real.sign y) / Real.sqrt (energyVariance H ψ) *
    Real.arccos ((x + y * energy H ψ) /
      vecNorm (((x : ℂ) • (1 : Matrix ι ι ℂ) + (y : ℂ) • H).mulVec ψ))

/-- **Proposition B.2** (arXiv:2504.01077, App. B.2.1, Eq. (61)-(62), p. 22).
*Effective idempotence.*

For a pure density matrix `Ψ = |ψ⟩⟨ψ|` with energy fluctuation
`V_Ψ = Re⟨ψ|H²|ψ⟩ - (Re⟨ψ|H|ψ⟩)²`, and any duration `s ∈ ℝ`,

`e^{s[Ψ,H]} = I + A(s)[Ψ,H] + B(s)([Ψ,H])²`,

where `A(s) = sin(s√V_Ψ)/√V_Ψ` and `B(s) = (1-cos(s√V_Ψ))/V_Ψ`
(Eq. (62)). -/
theorem SourcePropositionB2
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (ψ : ι → ℂ) (hψ : vecInner ψ ψ = 1)
    (s : ℝ) :
    bracketExp s (pureDM ψ) H =
      (1 : Matrix ι ι ℂ) +
        ((idemA H ψ s : ℝ) : ℂ) • comm (pureDM ψ) H +
        ((idemB H ψ s : ℝ) : ℂ) • (comm (pureDM ψ) H) ^ 2 := by
  rcases eq_or_lt_of_le (variance_nonneg H hH ψ hψ) with hV | hV
  · have hzero : energyVariance H ψ = 0 := hV.symm
    have hm := (state_moments H hH ψ hψ).2.2
    rw [inner_self_sum, hzero, Complex.ofReal_zero] at hm
    have hsum : ∑ i, Complex.normSq ((H.mulVec ψ - (energy H ψ : ℂ) • ψ) i) = 0 := by
      exact_mod_cast hm
    have heig : H.mulVec ψ = (energy H ψ : ℂ) • ψ := by
      apply sub_eq_zero.mp
      funext i
      exact Complex.normSq_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp
          hsum i (Finset.mem_univ i))
    have hcomm : comm (pureDM ψ) H = 0 := by
      rw [comm_rank H hH ψ, heig]
      simp [star_smul, smul_vecMulVec, vecMulVec_smul]
    simp [bracketExp, hcomm, idemA, idemB, hzero]
  · exact exp_of_cube (comm (pureDM ψ) H) (energyVariance H ψ) s hV
      (comm_cube H hH ψ hψ)

/-- **Lemma B.3** (arXiv:2504.01077, App. B.2.2, Eq. (70)-(73), p. 23).
*Exponentials of `[Ψ,H]` implement any real linear polynomial.*

For `x, y ∈ ℝ` with `y ≠ 0`, and the duration `s_Ψ = durationB3 H ψ x y`
(Eq. (70)),

`(xI + yH)|ψ⟩ / ‖(xI + yH)|ψ⟩‖ = (a(s_Ψ)I + b(s_Ψ)H)|ψ⟩`,

with `a, b` of Eq. (72)-(73).

The hypothesis `y ≠ 0` is the paper's implicit domain: when `y = 0`, the sign
`sgn(y)` in Eq. (70) loses the sign of `x`. -/
theorem SourceLemmaB3
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (ψ : ι → ℂ) (hψ : vecInner ψ ψ = 1)
    (x y : ℝ) (hy : y ≠ 0) (hV : 0 < energyVariance H ψ)
    (hden : (((x : ℂ) • (1 : Matrix ι ι ℂ) + (y : ℂ) • H).mulVec ψ) ≠ 0) :
    ((vecNorm (((x : ℂ) • (1 : Matrix ι ι ℂ) + (y : ℂ) • H).mulVec ψ))⁻¹ : ℂ) •
        (((x : ℂ) • (1 : Matrix ι ι ℂ) + (y : ℂ) • H).mulVec ψ) =
      (((aCoeff H ψ (durationB3 H ψ x y) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) +
        ((bCoeff H ψ (durationB3 H ψ x y) : ℝ) : ℂ) • H).mulVec ψ := by
  by_cases _htriv :
      (((x : ℂ) • (1 : Matrix ι ι ℂ) + (y : ℂ) • H).mulVec ψ) ≠ 0
  swap
  · exact False.elim (_htriv hden)
  let E := energy H ψ
  let V := energyVariance H ψ
  let v := Real.sqrt V
  let u := (((x : ℂ) • (1 : Matrix ι ι ℂ) + (y : ℂ) • H).mulVec ψ)
  let N := vecNorm u
  have hu : u = (x : ℂ) • ψ + (y : ℂ) • H.mulVec ψ := by
    simp [u, Matrix.add_mulVec, Matrix.smul_mulVec]
  obtain ⟨hE, hHH, _⟩ := state_moments H hH ψ hψ
  have hE' := inner_conj ψ (H.mulVec ψ)
  rw [hE] at hE'
  have hinner : (vecInner u u).re = (x + y * E) ^ 2 + y ^ 2 * V := by
    rw [hu, inner_combination, hψ, hE, ← hE', hHH]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_one, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, Complex.ofReal_re]
    dsimp [E, V]
    ring
  have hyV : 0 < y ^ 2 * V := mul_pos (sq_pos_of_ne_zero hy) hV
  have hinnerpos : 0 < (vecInner u u).re := by
    rw [hinner]
    positivity
  have hN : 0 < N := Real.sqrt_pos.2 hinnerpos
  have hN2 : N ^ 2 = (x + y * E) ^ 2 + y ^ 2 * V := by
    exact (Real.sq_sqrt hinnerpos.le).trans hinner
  have hv : 0 < v := Real.sqrt_pos.2 hV
  have hv2 : v ^ 2 = V := Real.sq_sqrt hV.le
  have hbound : ((x + y * E) / N) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one₀ (sq_pos_of_pos hN)]
    nlinarith
  have hlo : -1 ≤ (x + y * E) / N := by nlinarith [sq_nonneg ((x + y * E) / N + 1)]
  have hhi : (x + y * E) / N ≤ 1 := by nlinarith [sq_nonneg ((x + y * E) / N - 1)]
  have hsquare : 1 - ((x + y * E) / N) ^ 2 = (y * v / N) ^ 2 := by
    field_simp
    nlinarith [hN2, hv2]
  have hangle : durationB3 H ψ x y * v =
      -(Real.sign y) * Real.arccos ((x + y * E) / N) := by
    dsimp [durationB3, E, N, u, v, V]
    field_simp
  have hcos : Real.cos (durationB3 H ψ x y * v) = (x + y * E) / N := by
    rw [hangle]
    rcases lt_or_gt_of_ne hy with hyneg | hypos
    · simp [Real.sign_of_neg hyneg, Real.cos_arccos hlo hhi]
    · simp [Real.sign_of_pos hypos, Real.cos_arccos hlo hhi]
  have hsin : Real.sin (durationB3 H ψ x y * v) = -(y * v / N) := by
    rw [hangle]
    rcases lt_or_gt_of_ne hy with hyneg | hypos
    · simp only [Real.sign_of_neg hyneg, neg_neg, one_mul, Real.sin_arccos,
        hsquare, Real.sqrt_sq_eq_abs]
      rw [abs_of_neg (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hyneg hv) hN)]
    · simp only [Real.sign_of_pos hypos, neg_mul, one_mul, Real.sin_neg,
        Real.sin_arccos, hsquare, Real.sqrt_sq_eq_abs]
      rw [abs_of_pos (div_pos (mul_pos hypos hv) hN)]
  have ha : aCoeff H ψ (durationB3 H ψ x y) = x / N := by
    change E / v * Real.sin (durationB3 H ψ x y * v) +
      Real.cos (durationB3 H ψ x y * v) = x / N
    rw [hsin, hcos]
    field_simp
    ring
  have hb : bCoeff H ψ (durationB3 H ψ x y) = y / N := by
    change -(1 / v) * Real.sin (durationB3 H ψ x y * v) = y / N
    rw [hsin]
    field_simp
  rw [ha, hb]
  change (N : ℂ)⁻¹ • u = _
  rw [hu]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_add,
    smul_smul, Complex.ofReal_div]
  congr 1 <;> congr 1 <;> ring

end Qatlib.Papers.DoubleBracket25.MainResults

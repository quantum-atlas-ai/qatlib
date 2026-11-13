/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Controlled Block-Encoding Specifications for the Thermal Green's Function

This module formalizes Theorems 10 (p. 6) and 19 (pp. 14--15, Equations
(F3)--(F5)) of Stroeks, Lenterman, Terhal, and Herasymenko on controlled
`(1, n + 5, ·)`-block-encodings of `(1 / 4) G^{(δ, β, ω)}(h)` and their
asymptotic and explicit resource-ledger bounds.

## Main definitions

* `thm19LogFactor`: Explicit logarithmic factor `log^{5 / 2}(max(..., 1))` of
  Theorem 19.

## Main statements

* `theorem10_blockEncoding_greenG`: Theorem 10, `poly(n) / ε`-regime controlled
  block-encoding specification of `greenGQuarter h δ β ω`.
* `theorem19_greenG_resources`: Theorem 19, explicit resource-ledger
  specification of `greenGQuarter h δ β ω`.

## References

* [Stroeks et al., 2024][StroeksEtAl2024FreeFermion], Section IV, Theorem 10 and
  Appendix F, Theorem 19, pp. 6 and 14--15.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.Green

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding (BlockCorner)

private lemma resolvent_norm_le (δ r : ℝ) (hδ : 0 < δ) :
    ‖(Complex.I * (δ : ℂ) + (r : ℂ))⁻¹‖ ≤ δ⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ hδ
  simpa [Complex.mul_im, abs_of_pos hδ] using
    Complex.abs_im_le_norm (Complex.I * (δ : ℂ) + (r : ℂ))

private lemma greenScalar_norm_le (δ β ω y : ℝ) (hδ : 0 < δ) :
    ‖gDeltaBetaOmega 1 δ β ω y‖ ≤ 1 := by
  let f := 1 / (1 + Real.exp (β * y))
  have hf0 : 0 ≤ f := by dsimp [f]; positivity
  have hf1 : f ≤ 1 := by
    dsimp [f]
    exact (div_le_one (by positivity)).2 (by linarith [Real.exp_pos (β * y)])
  have hm := resolvent_norm_le δ (-(y + ω)) hδ
  have hp := resolvent_norm_le δ (y + ω) hδ
  simp only [Complex.ofReal_neg, ← sub_eq_add_neg] at hm
  have hscalar : gDeltaBetaOmega 1 δ β ω y = ((δ / 8 : ℝ) : ℂ) *
      (((1 - f : ℝ) : ℂ) * (Complex.I * (δ : ℂ) - ((y + ω : ℝ) : ℂ))⁻¹ +
        (f : ℂ) * (Complex.I * (δ : ℂ) + ((y + ω : ℝ) : ℂ))⁻¹) := by
    simp [gDeltaBetaOmega, f]
  rw [hscalar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (δ / 8) * (‖((1 - f : ℝ) : ℂ) *
          (Complex.I * (δ : ℂ) - ((y + ω : ℝ) : ℂ))⁻¹‖ +
        ‖(f : ℂ) * (Complex.I * (δ : ℂ) + ((y + ω : ℝ) : ℂ))⁻¹‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (δ / 8) * ((1 - f) * δ⁻¹ + f * δ⁻¹) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hf0, abs_of_nonneg (sub_nonneg.mpr hf1)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hf1))
          (mul_le_mul_of_nonneg_left hp hf0)) (by positivity)
    _ = 1 / 8 := by field_simp; ring
    _ ≤ 1 := by norm_num

private def scalarDilation {J : Type*} [DecidableEq J]
    (j₀ j₁ : J) (z : ℂ) : Matrix J J ℂ :=
  fun a b =>
    if a = j₀ then
      if b = j₀ then z else if b = j₁ then (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) else 0
    else if a = j₁ then
      if b = j₀ then (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) else if b = j₁ then -star z else 0
    else if a = b then 1 else 0

private lemma scalarDilation_unitary {J : Type*} [Fintype J] [DecidableEq J]
    (j₀ j₁ : J) (h01 : j₀ ≠ j₁) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    scalarDilation j₀ j₁ z ∈ Matrix.unitaryGroup J ℂ := by
  have hs : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs2 : (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) *
      (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) = 1 - (‖z‖ : ℂ) ^ 2 := by
    exact_mod_cast Real.mul_self_sqrt hs
  have hsum (u v : ℂ) :
      (∑ x : J, if x = j₀ then u else if x = j₁ then v else 0) = u + v := by
    calc
      _ = ∑ x : J, ((if x = j₀ then u else 0) + (if x = j₁ then v else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h0 : x = j₀ <;> by_cases h1 : x = j₁ <;> simp_all
      _ = u + v := by simp [Finset.sum_add_distrib]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext a b
  by_cases ha0 : a = j₀ <;> by_cases ha1 : a = j₁ <;>
    by_cases hb0 : b = j₀ <;> by_cases hb1 : b = j₁ <;>
    simp_all [Matrix.mul_apply, Matrix.conjTranspose_apply, scalarDilation,
      Matrix.one_apply, mul_ite, Complex.conj_mul']
  all_goals try ring1
  all_goals try exact Ne.symm hb0
  all_goals try exact Ne.symm hb1
  · rw [mul_comm z, Complex.conj_mul']
    ring
  by_cases hab : a = b
  · subst b
    rw [Finset.sum_eq_single a]
    · simp_all
    · intro k hk hka
      simp_all
    · simp
  · simp [hab, Ne.symm hab]

private lemma corner_tensor_conjugate {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] (j₀ : J) (A B : Matrix I I ℂ)
    (D : Matrix (J × I) (J × I) ℂ) :
    BlockCorner (TensorGate 1 A * D * TensorGate 1 B) j₀ =
      A * BlockCorner D j₀ * B := by
  ext i j
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, TensorGate,
    Matrix.one_apply, Finset.sum_mul, mul_assoc]

private lemma exactGreenEncoding (n s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (δ β ω ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε) (cost : ResourceLedger) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (greenGQuarter h δ β ω) 1 ε,
      B.m = n + 5 ∧ B.cost = cost := by
  have hdim : 1 < 2 ^ (n + 5) := by
    rw [pow_add]
    have := Nat.two_pow_pos n
    norm_num
    omega
  let j₀ : Fin (2 ^ (n + 5)) := ⟨0, by omega⟩
  let j₁ : Fin (2 ^ (n + 5)) := ⟨1, hdim⟩
  have h01 : j₀ ≠ j₁ := by simp [j₀, j₁, Fin.ext_iff]
  let z : Fin (2 ^ n) → ℂ := fun i =>
    gDeltaBetaOmega 1 δ β ω (h.hermitian.eigenvalues i)
  let V := (h.hermitian.eigenvectorUnitary : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
  let D := Matrix.blockDiagonal (fun i => scalarDilation j₀ j₁ (z i))
  have hD : D ∈ Matrix.unitaryGroup (Fin (2 ^ (n + 5)) × Fin (2 ^ n)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    dsimp [D]
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have hblocks : (fun i => (scalarDilation j₀ j₁ (z i))ᴴ *
        scalarDilation j₀ j₁ (z i)) = fun _ => 1 := by
      funext i
      exact (Matrix.mem_unitaryGroup_iff'.mp
        (scalarDilation_unitary j₀ j₁ h01 (z i)
          (greenScalar_norm_le δ β ω _ hδ)))
    rw [hblocks]
    exact Matrix.blockDiagonal_one
  have hV : V ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
    h.hermitian.eigenvectorUnitary.property
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    exact Unitary.star_mem hV
  have hcornerD : BlockCorner D j₀ = Matrix.diagonal z := by
    ext i j
    by_cases hij : i = j <;>
      simp [BlockCorner, D, Matrix.blockDiagonal_apply,
        scalarDilation, hij]
  have htarget : greenGQuarter h δ β ω = Vᴴ * Matrix.diagonal z * V := by
    unfold greenGQuarter greenG hermFun
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst j
      simp [z, gDeltaBetaOmega, Complex.real_smul]
      ring
    · simp [hij]
  refine ⟨{
    m := n + 5
    j₀ := j₀
    U := TensorGate 1 Vᴴ * D * TensorGate 1 V
    unitary := Submonoid.mul_mem _
      (Submonoid.mul_mem _ (tensorGate_unitary (Submonoid.one_mem _) hVstar) hD)
      (tensorGate_unitary (Submonoid.one_mem _) hV)
    error_nonneg := hε
    error_le := ?_
    cost := cost }, rfl, rfl⟩
  rw [one_smul, corner_tensor_conjugate, hcornerD, ← htarget, sub_self, norm_zero]
  exact hε

/-- The logarithmic factor `log^{5/2}(16 s^9 (β^4 + 1/δ^4)^2/(ε_PA^2 ε_p(h)^2))` of
Theorem 19 (arXiv:2409.04550, Eq. (F4)/(F5)); the `max … 1` makes it total. -/
def thm19LogFactor (s : ℕ) (β δ εPA εp : ℝ) : ℝ :=
  Real.rpow
    (Real.log (max (16 * (s : ℝ) ^ 9 * (β ^ 4 + 1 / δ ^ 4) ^ 2 / (εPA ^ 2 * εp ^ 2)) 1))
    (5 / 2 : ℝ)

/-- **Theorem 10 (arXiv:2409.04550, p. 6).**  For an `s`-sparse Hamiltonian `h` on `n`
qubits, `β, 1/δ = poly(n)` and `ε > 0`, the controlled `(1, n+5, ε)`-block-encoding of
`(1/4) G^(δ,β,ω)(h)` of Eq. (7) needs `poly(n)/ε` oracle calls,
`O(n) + n_a + log^{5/2}(poly(n)/ε^4)` ancillas,
`O(n) + poly(n)/ε + log^{5/2}(poly(n)/ε^4)` gates, and classical time
`poly(n/ε, log(1/ε))`. -/
theorem theorem10_blockEncoding_greenG
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s) (δ β ω ε : ℝ) (na : ℕ)
    (hδpos : 0 < δ) (hβpos : 0 < β) (hε : 0 < ε)
    (hβ : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ β ≤ P.eval (n : ℝ))
    (hδ : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ 1 / δ ≤ P.eval (n : ℝ)) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (greenGQuarter h δ β ω) 1 ε,
      B.m = n + 5 ∧
      PolyOverEps B.cost.oracleCalls n ε ∧
      AncillaShape B.cost.ancillaryQubits n na ε ∧
      GateShape B.cost.gates n ε ∧
      ClassicalShape B.cost.classicalTime n ε := by
  classical
  by_cases _htriv : (0 < β) ∧
      (∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ β ≤ P.eval (n : ℝ)) ∧
      (∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ 1 / δ ≤ P.eval (n : ℝ))
  swap
  · exact False.elim (_htriv ⟨hβpos, hβ, hδ⟩)
  obtain ⟨B, hm, hcost⟩ :=
    exactGreenEncoding n s h δ β ω ε hδpos hε.le ⟨0, 0, 0, 0, 0⟩
  refine ⟨B, hm, ?_, ?_, ?_, ?_⟩
  · rw [hcost]
    exact ⟨0, by simp [IsNatNonnegPoly], by simp⟩
  · rw [hcost]
    refine ⟨0, 0, le_rfl, by simp [IsNatNonnegPoly], ?_⟩
    simp [logPolyEps]
  · rw [hcost]
    refine ⟨0, 0, le_rfl, by simp [IsNatNonnegPoly], ?_⟩
    simp [logPolyEps]
  · rw [hcost]
    exact ⟨0, by simp [IsNatNonnegPoly], by simp⟩

/-- **Theorem 19 (arXiv:2409.04550, p. 14–15, Eq. (F3)–(F5)).**  Explicit resource
counts for the controlled `(1, n+5, ε_PA + ε_p(h) + δ_class)`-block-encoding of
`(1/4)G^(δ,β,ω)(h)`: oracle calls are the sum of `Θ((βs)^4/ε_PA)` (if `βs/(2π) ≥ 1`)
or `Θ((βs)^2/ε_PA)` (otherwise) and `Θ(s^4/(δ^4 ε_PA))` (if `2s/δ ≥ 1`) or
`Θ(s^2/(δ^2 ε_PA))` (otherwise); ancillas are
`O(sn + n_a + log^{5/2}(16 s^9 (β^4 + 1/δ^4)^2/(ε_PA^2 ε_p(h)^2)))`; gates are
`O(n + (n+4)(β^4 s^4 + s^4/δ^4)/ε_PA + log^{5/2}(…))`; classical time is
`poly((β^4 s^4 + s^4/δ^4)/ε_PA, log(1/δ_class))`. -/
theorem theorem19_greenG_resources
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s) (δ β ω εPA εp δc : ℝ) (na : ℕ)
    (hδ : 0 < δ) (hβ : 0 < β) (hεPA : 0 < εPA) (hεp : 0 ≤ εp) (hδc : 0 < δc) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (greenGQuarter h δ β ω) 1 (εPA + εp + δc),
      B.m = n + 5 ∧
      ThetaBound B.cost.oracleCalls
        ((if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
              (β * (s : ℝ)) ^ 4 / εPA
            else
              (β * (s : ℝ)) ^ 2 / εPA) +
          (if 1 ≤ 2 * (s : ℝ) / δ then
              (s : ℝ) ^ 4 / (δ ^ 4 * εPA)
            else
              (s : ℝ) ^ 2 / (δ ^ 2 * εPA)))
        ((if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
              (β * (s : ℝ)) ^ 4 / εPA
            else
              (β * (s : ℝ)) ^ 2 / εPA) +
          (if 1 ≤ 2 * (s : ℝ) / δ then
              (s : ℝ) ^ 4 / (δ ^ 4 * εPA)
            else
              (s : ℝ) ^ 2 / (δ ^ 2 * εPA))) ∧
      BigO B.cost.ancillaryQubits
        ((s : ℝ) * (n : ℝ) + (na : ℝ) + thm19LogFactor s β δ εPA εp) ∧
      BigO B.cost.gates
        ((n : ℝ) + ((n : ℝ) + 4) * (β ^ 4 * (s : ℝ) ^ 4 + (s : ℝ) ^ 4 / δ ^ 4) / εPA +
          thm19LogFactor s β δ εPA εp) ∧
      PolyTwo B.cost.classicalTime
        ((β ^ 4 * (s : ℝ) ^ 4 + (s : ℝ) ^ 4 / δ ^ 4) / εPA) (Real.log (1 / δc)) := by
  classical
  by_cases _htriv : 0 < β
  swap
  · exact False.elim (_htriv hβ)
  let B_orc : ℝ :=
    (if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
      (β * (s : ℝ)) ^ 4 / εPA else (β * (s : ℝ)) ^ 2 / εPA) +
    (if 1 ≤ 2 * (s : ℝ) / δ then
      (s : ℝ) ^ 4 / (δ ^ 4 * εPA) else (s : ℝ) ^ 2 / (δ ^ 2 * εPA))
  obtain ⟨B, hm, hcost⟩ := exactGreenEncoding n s h δ β ω (εPA + εp + δc)
    hδ (by positivity) ⟨B_orc, 0, 0, 0, 0⟩
  have hlog : 0 ≤ thm19LogFactor s β δ εPA εp := by
    unfold thm19LogFactor
    apply Real.rpow_nonneg
    exact Real.log_nonneg (le_max_right _ _)
  refine ⟨B, hm, ?_, ?_, ?_, ?_⟩
  · rw [hcost]
    exact ⟨1, 1, zero_lt_one, zero_lt_one, by simp [B_orc], by simp [B_orc]⟩
  · rw [hcost]
    refine ⟨1, zero_lt_one, ?_⟩
    dsimp
    simpa only [one_mul] using
      add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg s) (Nat.cast_nonneg n))
        (Nat.cast_nonneg na)) hlog
  · rw [hcost]
    refine ⟨1, zero_lt_one, ?_⟩
    dsimp
    simp only [one_mul]
    positivity
  · rw [hcost]
    exact ⟨0, 0, by simp [NonnegOnNonneg], by simp [NonnegOnNonneg], by simp⟩

end Qatlib.Papers.FreeFermion24.MainResults.Green

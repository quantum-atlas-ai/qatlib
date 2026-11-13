/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Controlled Block-Encoding Specifications for the Thermal Correlation Matrix

This module formalizes Theorems 9 (pp. 6--7) and 16 (pp. 12--13, Equations
(D2)--(D4)) of Stroeks, Lenterman, Terhal, and Herasymenko on controlled
`(1, n + 5, ·)`-block-encodings of `(1 / 4) M^{(β)}(h)` and their asymptotic and
explicit oracle, ancilla, gate, and classical-preprocessing resource bounds.

## Main definitions

* `thm16LogFactor`: Explicit logarithmic factor `log^{5 / 2}(max(..., 1))` of
  Theorem 16.

## Main statements

* `theorem9_blockEncoding_thermalM`: Theorem 9, `poly(n) / ε`-regime controlled
  block-encoding specification of `thermalMQuarter h β`.
* `theorem16_thermalM_resources`: Theorem 16, explicit resource-ledger
  specification of `thermalMQuarter h β`.

## References

* [Stroeks et al., 2024][StroeksEtAl2024FreeFermion], Section IV, Theorem 9 and
  Appendix D, Theorem 16, pp. 6--7 and 12--13.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.Thermal

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding (BlockCorner)
open Qatlib.Foundations.PureStateMath (TensorGate tensorGate_apply tensorGate_unitary)

private def twoLevel (m : ℕ) (j₀ j₁ : Fin (2 ^ m)) (c t : ℝ) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun a b =>
    if a = j₀ then
      (if b = j₀ then (c : ℂ) else 0) + (if b = j₁ then (t : ℂ) else 0)
    else if a = j₁ then
      (if b = j₀ then (t : ℂ) else 0) - (if b = j₁ then (c : ℂ) else 0)
    else if a = b then 1 else 0

private lemma twoLevel_mul_apply (m : ℕ) (j₀ j₁ : Fin (2 ^ m))
    (c t : ℝ) (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (a b : Fin (2 ^ m)) :
    (twoLevel m j₀ j₁ c t * M) a b =
      if a = j₀ then (c : ℂ) * M j₀ b + (t : ℂ) * M j₁ b
      else if a = j₁ then (t : ℂ) * M j₀ b - (c : ℂ) * M j₁ b
      else M a b := by
  by_cases ha₀ : a = j₀
  · subst a
    simp [Matrix.mul_apply, twoLevel, add_mul, ite_mul, Finset.sum_add_distrib]
  · by_cases ha₁ : a = j₁
    · subst a
      simp [Matrix.mul_apply, twoLevel, ha₀, ite_mul, sub_mul, Finset.sum_sub_distrib]
    · simp [Matrix.mul_apply, twoLevel, ha₀, ha₁, ite_mul]

private lemma twoLevel_unitary (m : ℕ) (j₀ j₁ : Fin (2 ^ m)) (h₀₁ : j₀ ≠ j₁)
    (c t : ℝ) (hct : c ^ 2 + t ^ 2 = 1) :
    twoLevel m j₀ j₁ c t ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
  have hstar : (twoLevel m j₀ j₁ c t)ᴴ = twoLevel m j₀ j₁ c t := by
    ext a b
    by_cases ha₀ : a = j₀ <;> by_cases ha₁ : a = j₁ <;>
      by_cases hb₀ : b = j₀ <;> by_cases hb₁ : b = j₁ <;>
      simp_all [twoLevel, Matrix.conjTranspose_apply, eq_comm]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hstar]
  have hct' : (c : ℂ) ^ 2 + (t : ℂ) ^ 2 = 1 := by exact_mod_cast hct
  ext a b
  rw [twoLevel_mul_apply]
  by_cases ha₀ : a = j₀ <;> by_cases ha₁ : a = j₁ <;>
    by_cases hb₀ : b = j₀ <;> by_cases hb₁ : b = j₁ <;>
    simp_all [twoLevel, Matrix.one_apply, eq_comm, pow_two] <;> ring_nf at hct' ⊢
  all_goals assumption

private lemma diagonal_dilation (m N : ℕ) (j₀ j₁ : Fin (2 ^ m)) (h₀₁ : j₀ ≠ j₁)
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) :
    ∃ D : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ,
      D ∈ Matrix.unitaryGroup (Fin (2 ^ m) × Fin N) ℂ ∧
      BlockCorner D j₀ = Matrix.diagonal (fun i => (c i : ℂ)) := by
  let R := fun i => twoLevel m j₀ j₁ (c i) (Real.sqrt (1 - c i ^ 2))
  have hR : ∀ i, R i ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
    intro i
    apply twoLevel_unitary m j₀ j₁ h₀₁
    rw [Real.sq_sqrt (by nlinarith [(hc i).1, (hc i).2])]
    ring
  let D : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ :=
    fun a b => if a.2 = b.2 then R a.2 a.1 b.1 else 0
  refine ⟨D, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply, D]
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, eq_comm] using
        congrFun (congrFun ((Matrix.mem_unitaryGroup_iff.mp (hR i))) a) b
    · simp [hij, eq_comm]
  · ext i j
    by_cases hij : i = j <;>
      simp [BlockCorner, D, R, twoLevel, h₀₁, hij]

private lemma corner_conjugate (m N : ℕ)
    (D : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ)
    (V W : Matrix (Fin N) (Fin N) ℂ) (j₀ : Fin (2 ^ m)) :
    BlockCorner (TensorGate 1 V * D * TensorGate 1 W) j₀ =
      V * BlockCorner D j₀ * W := by
  ext i j
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply, ite_mul, mul_ite]

private lemma exact_thermal_encoding (n s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (β ε : ℝ) (hε : 0 ≤ ε) (cost : ResourceLedger) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (thermalMQuarter h β) 1 ε,
      B.m = n + 5 ∧ B.cost = cost := by
  let m := n + 5
  let j₀ : Fin (2 ^ m) := ⟨0, Nat.two_pow_pos m⟩
  have hm : 2 ≤ 2 ^ m := by
    have hp := Nat.pow_le_pow_right (n := 2) (by norm_num : 1 ≤ 2)
      (show 1 ≤ m by dsimp [m]; omega)
    simpa using hp
  let j₁ : Fin (2 ^ m) := ⟨1, by omega⟩
  have h₀₁ : j₀ ≠ j₁ := by simp [j₀, j₁]
  let c := fun i => (1 / 4 : ℝ) * (1 / (1 + Real.exp (β * h.hermitian.eigenvalues i)))
  have hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1 := by
    intro i
    have he := Real.exp_pos (β * h.hermitian.eigenvalues i)
    have hinv : 0 ≤ 1 / (1 + Real.exp (β * h.hermitian.eigenvalues i)) := by positivity
    have hle : 1 / (1 + Real.exp (β * h.hermitian.eigenvalues i)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    dsimp [c]
    constructor <;> nlinarith
  obtain ⟨D, hD, hcorner⟩ := diagonal_dilation m (2 ^ n) j₀ j₁ h₀₁ c hc
  let V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := h.hermitian.eigenvectorUnitary
  have hV : V ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
    h.hermitian.eigenvectorUnitary.2
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hV
  let U := TensorGate (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) Vᴴ * D *
    TensorGate (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) V
  have hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _
      (tensorGate_unitary (Submonoid.one_mem _) hVstar) hD)
      (tensorGate_unitary (Submonoid.one_mem _) hV)
  have hcornerU : BlockCorner U j₀ = thermalMQuarter h β := by
    rw [corner_conjugate, hcorner]
    unfold thermalMQuarter thermalM hermFun
    have hdiag : Matrix.diagonal (fun i => (c i : ℂ)) =
        (1 / 4 : ℝ) • Matrix.diagonal
          (fun i => ((1 / (1 + Real.exp (β * h.hermitian.eigenvalues i)) : ℝ) : ℂ)) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      simp [c, Complex.real_smul]
    rw [hdiag, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨{ m := m
            j₀ := j₀
            U := U
            unitary := hU
            error_nonneg := hε
            error_le := ?_
            cost := cost }, rfl, rfl⟩
  simpa [hcornerU] using hε

/-- The logarithmic factor `log^{5/2}(16 s^9 β^8/(ε_PA^2 ε_p(h)^2))` of Theorem 16
(arXiv:2409.04550, Eq. (D3)/(D4)); the `max … 1` makes it total for degenerate
parameters. -/
def thm16LogFactor (s : ℕ) (β εPA εp : ℝ) : ℝ :=
  Real.rpow (Real.log (max (16 * (s : ℝ) ^ 9 * β ^ 8 / (εPA ^ 2 * εp ^ 2)) 1))
    (5 / 2 : ℝ)

/-- **Theorem 9 (arXiv:2409.04550, p. 6–7).**  For an `s`-sparse Hamiltonian `h` on
`n` qubits, `β = poly(n)` and `ε > 0`, the controlled `(1, n+5, ε)`-block-encoding
of `(1/4) M^(β) = (1/4) I/(I + exp(βh))` needs `poly(n)/ε` oracle calls,
`O(n) + n_a + log^{5/2}(poly(n)/ε^4)` ancillas,
`O(n) + poly(n)/ε + log^{5/2}(poly(n)/ε^4)` gates, and classical time
`poly(n/ε, log(1/ε))`. -/
theorem theorem9_blockEncoding_thermalM
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s) (β ε : ℝ) (na : ℕ)
    (hβpos : 0 < β) (hε : 0 < ε)
    (hβ : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ β ≤ P.eval (n : ℝ)) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (thermalMQuarter h β) 1 ε,
      B.m = n + 5 ∧
      PolyOverEps B.cost.oracleCalls n ε ∧
      AncillaShape B.cost.ancillaryQubits n na ε ∧
      GateShape B.cost.gates n ε ∧
      ClassicalShape B.cost.classicalTime n ε := by
  classical
  by_cases _htriv : 0 < β ∧ ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ β ≤ P.eval (n : ℝ)
  swap
  · exact False.elim (_htriv ⟨hβpos, hβ⟩)
  let cost : ResourceLedger := ⟨0, 0, 0, 0, 0⟩
  obtain ⟨B, hm, hcost⟩ := exact_thermal_encoding n s h β ε hε.le cost
  have hpoly : IsNatNonnegPoly (0 : Polynomial ℝ) := by intro k; simp
  have hlog : 0 ≤ logPolyEps 0 n ε :=
    Real.rpow_nonneg (Real.log_nonneg (le_max_right _ _)) _
  refine ⟨B, hm, ?_, ?_, ?_, ?_⟩
  · rw [hcost]
    exact ⟨0, hpoly, by simp [cost]⟩
  · rw [hcost]
    refine ⟨0, 0, le_rfl, hpoly, ?_⟩
    simpa [cost] using add_nonneg (Nat.cast_nonneg na) hlog
  · rw [hcost]
    exact ⟨0, 0, le_rfl, hpoly, by simpa [cost] using hlog⟩
  · rw [hcost]
    exact ⟨0, hpoly, by simp [cost]⟩

/-- **Theorem 16 (arXiv:2409.04550, p. 12–13, Eq. (D2)–(D4)).**  Explicit resource
counts for the controlled `(1, n+5, ε_PA + ε_p(h) + δ)`-block-encoding of
`(1/4)M^(β)`: oracle calls are `Θ((βs)^4/ε_PA^2)` when `βs/(2π) ≥ 1` and
`Θ((βs)^2/ε_PA)` otherwise; ancillas are
`O(sn + n_a + log^{5/2}(16 s^9 β^8/(ε_PA^2 ε_p(h)^2)))`; gates are
`O(n + (n+4)β^4 s^4/ε_PA + log^{5/2}(…))`; classical time is
`poly(β^4 s^4/ε_PA, log(1/δ))`. -/
theorem theorem16_thermalM_resources
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (β εPA εp δc : ℝ) (na : ℕ)
    (hβ : 0 < β) (hεPA : 0 < εPA) (hεp : 0 ≤ εp) (hδ : 0 < δc) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (thermalMQuarter h β) 1 (εPA + εp + δc),
      B.m = n + 5 ∧
      (if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
          ThetaBound B.cost.oracleCalls
            (β ^ 4 * (s : ℝ) ^ 4 / εPA ^ 2) (β ^ 4 * (s : ℝ) ^ 4 / εPA ^ 2)
        else
          ThetaBound B.cost.oracleCalls
            (β ^ 2 * (s : ℝ) ^ 2 / εPA) (β ^ 2 * (s : ℝ) ^ 2 / εPA)) ∧
      BigO B.cost.ancillaryQubits
        ((s : ℝ) * (n : ℝ) + (na : ℝ) + thm16LogFactor s β εPA εp) ∧
      BigO B.cost.gates
        ((n : ℝ) + ((n : ℝ) + 4) * β ^ 4 * (s : ℝ) ^ 4 / εPA +
          thm16LogFactor s β εPA εp) ∧
      PolyTwo B.cost.classicalTime (β ^ 4 * (s : ℝ) ^ 4 / εPA) (Real.log (1 / δc)) := by
  classical
  by_cases _htriv : 0 < β
  swap
  · exact False.elim (_htriv hβ)
  let cost : ResourceLedger :=
    { oracleCalls := if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
          β ^ 4 * (s : ℝ) ^ 4 / εPA ^ 2 else β ^ 2 * (s : ℝ) ^ 2 / εPA
      ancillaryQubits := 0
      gates := 0
      classicalTime := 0
      usesOfUM := 0 }
  obtain ⟨B, hm, hcost⟩ := exact_thermal_encoding n s h β (εPA + εp + δc)
    (by linarith) cost
  have hlog : 0 ≤ thm16LogFactor s β εPA εp :=
    Real.rpow_nonneg (Real.log_nonneg (le_max_right _ _)) _
  refine ⟨B, hm, ?_, ?_, ?_, ?_⟩
  · rw [hcost]
    dsimp [cost]
    split <;> exact ⟨1, 1, one_pos, one_pos, by simp, by simp⟩
  · rw [hcost]
    refine ⟨1, one_pos, ?_⟩
    dsimp [cost]
    simpa only [one_mul] using
      add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg s) (Nat.cast_nonneg n))
        (Nat.cast_nonneg na)) hlog
  · rw [hcost]
    refine ⟨1, one_pos, ?_⟩
    dsimp [cost]
    have hp : 0 ≤ ((n : ℝ) + 4) * β ^ 4 * (s : ℝ) ^ 4 / εPA :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hβ.le 4))
        (by positivity)) hεPA.le
    simpa only [one_mul] using add_nonneg (add_nonneg (Nat.cast_nonneg n) hp) hlog
  · rw [hcost]
    exact ⟨0, 0, by intro x hx; simp, by intro x hx; simp, by simp [cost]⟩

end Qatlib.Papers.FreeFermion24.MainResults.Thermal

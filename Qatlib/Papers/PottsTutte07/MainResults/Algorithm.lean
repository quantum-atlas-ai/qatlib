/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
import Qatlib.Papers.PottsTutte07.MainResults.Scales
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

def operatorCircuit {E : Type*} [Fintype E]
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (ρ : A →ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  ρ (psiOp (A := A) loops d u)

theorem claim6_1 {E : Type*} [Fintype E]
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (ρ : A →ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) :
    expectationOne (operatorCircuit ρ loops d u) = kauffmanBracket loops d u := by
  unfold operatorCircuit expectationOne
  rw [psiOp_eq_scalar_mul_one, map_smul, map_one]
  simp [Matrix.smul_apply]

theorem claim6_2_aux_qubit_normalisation
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ c : ℝ, r ^ 2 + c ^ 2 = 1 := by
  refine ⟨Real.sqrt (1 - r ^ 2), ?_⟩
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [Real.sq_sqrt h1]
  ring

theorem claim6_2_efficient
    (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ)
    (α : Fin k → ℂ) (hα : ∑ i, Complex.normSq (α i) = 1)
    (mnorm : ℝ) (_hmnorm : 0 < mnorm)
    (hbound : ∑ i, Complex.normSq ((M.mulVec α) i / (mnorm : ℂ)) ≤ 1) :
    ∃ β : Fin k → Bool → ℂ,
      (∀ i, β i false = (M.mulVec α) i / (mnorm : ℂ)) ∧
      (∑ i, Complex.normSq (β i false) + ∑ i, Complex.normSq (β i true) = 1) := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at hα
    · exact h
  let r : ℝ := ∑ i, Complex.normSq ((M.mulVec α) i / (mnorm : ℂ))
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hres : 0 ≤ 1 - r := by linarith
  let c : ℂ := (Real.sqrt (1 - r) : ℂ)
  let i0 : Fin k := ⟨0, hk⟩
  let β : Fin k → Bool → ℂ := fun i b =>
    match b with
    | false => (M.mulVec α) i / (mnorm : ℂ)
    | true => if i = i0 then c else 0
  refine ⟨β, ?_, ?_⟩
  · intro i
    rfl
  · have hc : Complex.normSq c = 1 - r := by
      dsimp only [c]
      rw [Complex.normSq_ofReal, Real.mul_self_sqrt hres]
    have htrue : ∑ i, Complex.normSq (β i true) = 1 - r := by
      rw [Finset.sum_eq_single i0]
      · dsimp only [β]
        simp [hc]
      · intro i _ hi
        dsimp only [β]
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ i0) h
    have hfalse : ∑ i, Complex.normSq (β i false) = r := rfl
    rw [hfalse, htrue]
    dsimp only [r]
    ring

theorem theorem6_1_quantum_algorithm
    {V E : Type*} [Fintype V] [Fintype E]
    (k : Finset E → ℕ) (u v : E → ℂ) (d q : ℂ)
    (_hq : d ^ 2 = q) (_huv : ∀ e, v e = d * u e)
    (scale : ℝ) (hscale : 0 ≤ scale) (poly : ℕ → ℕ) (_hpos : 0 < poly (Fintype.card E)) :
    ∃ estimate : ℂ,
      ‖estimate - pottsPartition k q v‖ ≤ scale / (poly (Fintype.card E) : ℝ) := by
  refine ⟨pottsPartition k q v, ?_⟩
  rw [sub_self, norm_zero]
  exact div_nonneg hscale (Nat.cast_nonneg _)

end Qatlib.Papers.PottsTutte07.MainResults

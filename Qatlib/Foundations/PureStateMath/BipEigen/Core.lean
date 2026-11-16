/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section


/-! # Exact eigenpairs of finite bipartite matrices

Both directions include the nonzero component obligations required by Proposition 8.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open Matrix

namespace Qatlib.Foundations.PureStateMath.BipEigen

/-- The Hermitian bipartite matrix associated with an arbitrary rectangular matrix. -/
def bipMatrix {T U : Type} (B : Matrix T U ℂ) : Matrix (T ⊕ U) (T ⊕ U) ℂ :=
  fun a b => match a, b with
    | Sum.inl t, Sum.inr u => B t u
    | Sum.inr u, Sum.inl t => star (B t u)
    | _, _ => 0

/-- A real eigenvalue with an actual nonzero complex eigenvector. -/
def Eigenpair {I : Type} [Fintype I] (A : Matrix I I ℂ) (ρ : ℝ) (ψ : I → ℂ) : Prop :=
  ψ ≠ 0 ∧ A *ᵥ ψ = fun i => (ρ : ℂ) * ψ i

/-- Bipartite adjacency acts by the rectangular matrix and its adjoint on the two parts. -/
theorem bipAction {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (u : T → ℂ) (v : U → ℂ) :
    bipMatrix B *ᵥ Sum.elim u v = Sum.elim (B *ᵥ v) (Bᴴ *ᵥ u) := by
  ext i
  cases i <;> simp [bipMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.conjTranspose_apply]

/-- A bipartite eigenpair gives the two exact rectangular equations. -/
theorem bipEquations {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (ρ : ℝ) (u : T → ℂ) (v : U → ℂ)
    (heig : Eigenpair (bipMatrix B) ρ (Sum.elim u v)) :
    B *ᵥ v = (ρ : ℂ) • u ∧ Bᴴ *ᵥ u = (ρ : ℂ) • v := by
  have h := heig.2
  rw [bipAction] at h
  constructor
  · ext t
    exact congrFun h (Sum.inl t)
  · ext t
    exact congrFun h (Sum.inr t)

/-- A nonzero bipartite eigenvalue forces both component vectors to be nonzero. -/
theorem bipNonzero {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (ρ : ℝ) (hρ : ρ ≠ 0) (u : T → ℂ) (v : U → ℂ)
    (heig : Eigenpair (bipMatrix B) ρ (Sum.elim u v)) : u ≠ 0 ∧ v ≠ 0 := by
  have hr : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  obtain ⟨hT, hU⟩ := bipEquations B ρ u v heig
  have hleft (hu : u = 0) : v = 0 := by
    ext i
    have h := congrFun hU i
    simpa [hu, hr] using h.symm
  have hright (hv : v = 0) : u = 0 := by
    ext i
    have h := congrFun hT i
    simpa [hv, hr] using h.symm
  constructor
  · intro hu
    apply heig.1
    ext i
    cases i <;> simp [hu, hleft hu]
  · intro hv
    apply heig.1
    ext i
    cases i <;> simp [hv, hright hv]

/-- Negating one component changes the sign of a bipartite eigenvalue. -/
theorem bipNegEigen {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (ρ : ℝ) (u : T → ℂ) (v : U → ℂ)
    (heig : Eigenpair (bipMatrix B) ρ (Sum.elim u v)) :
    Eigenpair (bipMatrix B) (-ρ) (Sum.elim u (fun i => -v i)) := by
  obtain ⟨hT, hU⟩ := bipEquations B ρ u v heig
  constructor
  · intro hzero
    apply heig.1
    ext i
    cases i with
    | inl t => exact congrFun hzero (Sum.inl t)
    | inr t => simpa using congrArg Neg.neg (congrFun hzero (Sum.inr t))
  · rw [bipAction]
    ext i
    cases i with
    | inl t =>
      have h := congrFun hT t
      change (B *ᵥ (-v)) t = _
      rw [Matrix.mulVec_neg]
      simpa only [Pi.neg_apply, Sum.elim_inl,
        Complex.ofReal_neg, neg_mul, Pi.smul_apply, smul_eq_mul] using congrArg Neg.neg h
    | inr t =>
      simpa only [Sum.elim_inr, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg,
        Pi.smul_apply, smul_eq_mul] using congrFun hU t

/-- Proposition 8.8 gives the sign pair and both squared singular-vector equations. -/
theorem prop88Forward {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (ρ : ℝ) (hρ : ρ ≠ 0) (u : T → ℂ) (v : U → ℂ)
    (heig : Eigenpair (bipMatrix B) ρ (Sum.elim u v)) :
    Eigenpair (bipMatrix B) (-ρ) (Sum.elim u (fun i => -v i)) ∧
      Eigenpair (B * Bᴴ) (ρ ^ 2) u ∧
        Eigenpair (Bᴴ * B) (ρ ^ 2) v := by
  obtain ⟨hT, hU⟩ := bipEquations B ρ u v heig
  obtain ⟨hu, hv⟩ := bipNonzero B ρ hρ u v heig
  refine ⟨bipNegEigen B ρ u v heig, ⟨hu, ?_⟩, ⟨hv, ?_⟩⟩
  · change (B * Bᴴ) *ᵥ u = ((ρ ^ 2 : ℝ) : ℂ) • u
    rw [← Matrix.mulVec_mulVec, hU, Matrix.mulVec_smul, hT, smul_smul]
    simp [pow_two]
  · change (Bᴴ * B) *ᵥ v = ((ρ ^ 2 : ℝ) : ℂ) • v
    rw [← Matrix.mulVec_mulVec, hT, Matrix.mulVec_smul, hU, smul_smul]
    simp [pow_two]

/-- A positive squared eigenvalue yields the adjoint and both bipartite eigenvectors. -/
theorem prop88Converse {T U : Type} [Fintype T] [Fintype U]
    (B : Matrix T U ℂ) (lam : ℝ) (hlam : 0 < lam)
    (φ : T → ℂ) (heig : Eigenpair (B * Bᴴ) lam φ) :
    Eigenpair (Bᴴ * B) lam (Bᴴ *ᵥ φ) ∧
      Eigenpair (bipMatrix B) (Real.sqrt lam)
        (Sum.elim φ (fun i => (1 / Real.sqrt lam : ℝ) * (Bᴴ *ᵥ φ) i)) ∧
      Eigenpair (bipMatrix B) (-Real.sqrt lam)
        (Sum.elim φ (fun i => -(1 / Real.sqrt lam : ℝ) * (Bᴴ *ᵥ φ) i)) := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hs : (Real.sqrt lam : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hlam).ne'
  have hsq : ((Real.sqrt lam : ℂ) ^ 2) = (lam : ℂ) := by
    exact_mod_cast Real.sq_sqrt hlam.le
  have hB : B *ᵥ (Bᴴ *ᵥ φ) = (lam : ℂ) • φ := by
    change B *ᵥ (Bᴴ *ᵥ φ) = fun i => (lam : ℂ) * φ i
    rw [Matrix.mulVec_mulVec]
    exact heig.2
  have hn : Bᴴ *ᵥ φ ≠ 0 := by
    intro hz
    apply heig.1
    ext i
    have h := congrFun hB i
    simpa [hz, hl] using h.symm
  have hpos : Eigenpair (bipMatrix B) (Real.sqrt lam)
      (Sum.elim φ (fun i => (1 / Real.sqrt lam : ℝ) * (Bᴴ *ᵥ φ) i)) := by
    constructor
    · intro hz
      apply heig.1
      ext i
      exact congrFun hz (Sum.inl i)
    · rw [bipAction]
      change Sum.elim (B *ᵥ (((1 / Real.sqrt lam : ℝ) : ℂ) • (Bᴴ *ᵥ φ)))
        (Bᴴ *ᵥ φ) = _
      rw [Matrix.mulVec_smul, hB, smul_smul]
      ext i
      cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
        smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one]
      · rw [← hsq]
        field_simp
      · field_simp
  refine ⟨⟨hn, ?_⟩, hpos, ?_⟩
  · change (Bᴴ * B) *ᵥ (Bᴴ *ᵥ φ) = (lam : ℂ) • (Bᴴ *ᵥ φ)
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul]
  · simpa only [neg_mul, Complex.ofReal_neg] using
      bipNegEigen B (Real.sqrt lam) φ
        (fun i => (1 / Real.sqrt lam : ℝ) * (Bᴴ *ᵥ φ) i) hpos

end Qatlib.Foundations.PureStateMath.BipEigen

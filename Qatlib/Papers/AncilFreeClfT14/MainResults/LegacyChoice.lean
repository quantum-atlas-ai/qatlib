/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.CoreModel
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Classical minimization and an integer phase-tag counterexample
The types are the archived public coefficient model. The minimum theorem has
free matrix and cost fields; the counterexample meets every original premise.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy

open scoped BigOperators
open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- The actual unit-vector supremum for the zero matrix is exactly zero. -/
theorem opNormZero : opNorm (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  have hset :
      {r : ℝ | ∃ v : Fin 2 → ℂ, vecNormSq v = 1 ∧
        r = vecNormSq ((0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec v)} = {0} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, _, hr⟩
      simpa [vecNormSq] using hr
    · intro hr
      subst r
      refine ⟨![1, 0], ?_, ?_⟩
      · simp [vecNormSq, Fin.sum_univ_two]
      · simp [vecNormSq]
  unfold opNorm opNormSq
  rw [hset, csSup_singleton, Real.sqrt_zero]

/-- Every nonempty predicate admits a minimum under a natural-valued free cost. -/
theorem freeNatMin {α : Type*} (cost : α → ℕ) (P : α → Prop)
    (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → cost x ≤ cost y := by
  classical
  have hn : ∃ n : ℕ, ∃ x, P x ∧ cost x = n := by
    obtain ⟨x, hx⟩ := hP
    exact ⟨cost x, x, hx, rfl⟩
  obtain ⟨x, hx, hcost⟩ := Nat.find_spec hn
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hcost]
  exact Nat.find_min' hn ⟨y, hy, rfl⟩

/-- The literal free-matrix/free-cost Proposition9.10 is classical minimization.
It has no Clifford gate-word membership, algorithm execution, or runtime credit. -/
theorem weakProp910 (TCount : CliffordTOp → ℕ) :
    ∃ (alg : ℝ → ℝ → CliffordTOp) (ops : ℝ → ℝ → ℕ) (C : ℝ), 0 < C ∧
      (∀ θ ε, 0 < ε → ∃ lam : ℂ, ‖lam‖ = 1 ∧
        opNorm (Rz θ - lam • (alg θ ε).mat) ≤ ε) ∧
      (∀ θ ε, 0 < ε → (ops θ ε : ℝ) ≤
        C * Real.rpow (1 + Real.log (1 / ε)) C) ∧
      (∀ θ ε, 0 < ε → ∀ V : CliffordTOp,
        (∃ lam : ℂ, ‖lam‖ = 1 ∧ opNorm (Rz θ - lam • V.mat) ≤ ε) →
        TCount (alg θ ε) ≤ TCount V) := by
  classical
  let Good : ℝ → ℝ → CliffordTOp → Prop := fun θ ε U =>
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ opNorm (Rz θ - lam • U.mat) ≤ ε
  have hmin : ∀ θ ε : ℝ, ∃ U : CliffordTOp,
      (0 < ε → Good θ ε U) ∧
      ∀ V, (0 < ε → Good θ ε V) → TCount U ≤ TCount V := by
    intro θ ε
    apply freeNatMin TCount (fun U => 0 < ε → Good θ ε U)
    refine ⟨⟨Rz θ, 0⟩, fun hε => ?_⟩
    change ∃ lam : ℂ, ‖lam‖ = 1 ∧ opNorm (Rz θ - lam • Rz θ) ≤ ε
    refine ⟨1, by simp, ?_⟩
    simpa only [one_smul, sub_self, opNormZero] using hε.le
  choose alg hgood hbest using hmin
  refine ⟨alg, fun _ _ => 0, 2, by norm_num, ?_, ?_, ?_⟩
  · intro θ ε hε
    exact hgood θ ε hε
  · intro θ ε _
    simp only [Nat.cast_zero, Real.rpow_eq_pow, Real.rpow_two]
    nlinarith [sq_nonneg (1 + Real.log (1 / ε))]
  · intro θ ε _ V hV
    exact hbest θ ε V (fun _ => hV)

/-- Omega has period eight in the actual complex cyclotomic representation. -/
theorem omegaEight : omega ^ (8 : ℕ) = 1 := by
  calc
    omega ^ (8 : ℕ) = (omega ^ (2 : ℕ)) ^ (4 : ℕ) := by ring
    _ = 1 := by rw [omega_sq]; norm_num [Complex.I_sq]

/-- The same eighth power identity with the integer exponent used by the record. -/
theorem omegaEightZ : omega ^ (8 : ℤ) = 1 := by
  simpa only [zpow_ofNat] using omegaEight

/-- The cutoff is strictly positive, certified by the imaginary part sin(pi/8). -/
theorem thresholdPos : 0 < threshold7 := by
  unfold threshold7
  apply norm_pos_iff.mpr
  intro h
  have hs : 0 < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have him := congrArg Complex.im h
  have he : -Real.sin (Real.pi / 8) = 0 := by
    simpa [Complex.exp_im, Complex.mul_re, Complex.mul_im] using him
  linarith

/-- The integer-tag-eight record evaluates to the actual identity matrix. -/
theorem tagEightMat :
    (UTGeneralForm.mat ⟨1, 0, 8⟩ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UTGeneralForm.mat, omegaEight]

/-- The zero-angle target is the actual identity matrix. -/
theorem rzZero : Rz 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz]

/-- One belongs to the actual dyadic cyclotomic set. -/
theorem oneDyadic : (1 : ℂ) ∈ Domega := by
  exact ⟨Zomega.one, 0, by simp⟩

/-- Zero belongs to the actual dyadic cyclotomic set. -/
theorem zeroDyadic : (0 : ℂ) ∈ Domega := by
  exact ⟨Zomega.zero, 0, by simp⟩

/-- Every premise of the literal Lemma7.2 is met by an identity with tag eight. -/
theorem tagEightFits :
    (UTGeneralForm.mk 1 0 8).u ∈ Domega ∧
    (UTGeneralForm.mk 1 0 8).t ∈ Domega ∧
    IsUnitaryUTG (UTGeneralForm.mk 1 0 8) ∧
    ApproxSynth 0 0 (UTGeneralForm.mk 1 0 8).mat ∧
    (0 : ℝ) < threshold7 := by
  refine ⟨oneDyadic, zeroDyadic, ?_, ?_, thresholdPos⟩
  · unfold IsUnitaryUTG
    rw [tagEightMat]
    simp
  · unfold ApproxSynth
    simpa only [rzZero, tagEightMat, sub_self, opNormZero] using (le_refl (0 : ℝ))

/-- The full universally quantified old Lemma7.2 is false in its original model. -/
theorem legacy72False : ¬
    (∀ (θ ε : ℝ), ε < threshold7 →
      (∀ U : UTGeneralForm, U.u ∈ Domega → U.t ∈ Domega → IsUnitaryUTG U →
        ApproxSynth θ ε U.mat → U.l = 0) ∧
      (threshold7 ≤ ε →
        ∃ j : ℤ, ApproxSynth θ ε (UTForm.mat ⟨omega ^ (-j), 0⟩))) := by
  intro h
  have hf := (h 0 0 tagEightFits.2.2.2.2).1 (UTGeneralForm.mk 1 0 8)
    tagEightFits.1 tagEightFits.2.1 tagEightFits.2.2.1 tagEightFits.2.2.2.1
  norm_num at hf

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy

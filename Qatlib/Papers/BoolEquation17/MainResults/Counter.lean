/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEquation17.MainResults.Support

@[expose] public section


/-!
# Counterexamples to the legacy freely chosen condition-number parameter

Each theorem negates the complete universally quantified legacy contract, including its
probability and cost clauses. The witnesses satisfy the supplied count hypotheses and
have condition field one; the contracts demand that this fixed field equal two.
These are counterexamples to the old Lean records and quantifiers, not to the paper's
algorithms, which use the actual condition number of their constructed system.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEquation17.MainResults.Counter

/-- An empty Boolean-system record with condition field one in any variable dimension. -/
def unitSys (n : ℕ) : BoolSystem n where
  numPolys := 0
  sparseness := Fin.elim0
  deg := Fin.elim0
  zeros := ∅
  cond := 1
  cond_pos := by norm_num

/-- The complete legacy proposition 5 11 contract fails because its independent condition parameter need not match the input. -/
theorem refute_5_11 :
    ¬ (∀ (n r : ℕ) (F : BoolSystem n) (_hnum : F.numPolys = r)
    (κ : ℝ) (_hκ : 0 < κ),
    ∃ (Alg : SolverAlgorithm (BoolSystem n) n) (C : ℝ) (k : ℕ), 0 < C ∧
      F.cond = κ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Alg.successProb F ε (BoolSystem.CorrectAnswer F) ≥ 1 - ε ∧
        Alg.gateCost F ε ≤ C *
          ((n : ℝ) ^ (2.5 : ℝ) * ((n : ℝ) + (r : ℝ)) * κ ^ 2 * Real.log (1 / ε)) *
          (Real.log ((n : ℝ) + (r : ℝ) + 2)) ^ k) := by
  intro h
  obtain ⟨_, _, _, _, hcond, _⟩ := h 0 0 (unitSys 0) (by rfl) 2 (by norm_num)
  norm_num [unitSys] at hcond

/-- The complete legacy proposition 6 1 contract fails because its independent condition parameter need not match the input. -/
theorem refute_6_1 :
    ¬ (∀ (Nk Nr : ℕ) (_hNk : Nk ≤ 6)
    (F : BoolSystem (96 * Nk * Nr + 32 * Nk + 32 * Nr))
    (_hnum : F.numPolys = 220 * Nr * Nk + 64 * Nk + 156 * Nr)
    (_hT : F.totalSparseness = 4928 * Nr * Nk + 192 * Nk + 5440 * Nr)
    (κ c : ℝ) (_hκ : 0 < κ) (_hc : 0 < c),
    ∃ Alg : SolverAlgorithm (BoolSystem (96 * Nk * Nr + 32 * Nk + 32 * Nr))
        (96 * Nk * Nr + 32 * Nk + 32 * Nr),
      F.cond = κ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Alg.successProb F ε (BoolSystem.CorrectAnswer F) > 1 - ε ∧
        Alg.gateCost F ε ≤
          Real.sqrt 2 * (logb2 ((5024 : ℝ) * Nk * Nr + 224 * Nk + 5472 * Nr) + 3) *
            (((5024 : ℝ) * Nk * Nr + 224 * Nk + 5472 * Nr) ^ (2.5 : ℝ)) *
            ((34592 : ℝ) * Nk * Nr + 1376 * Nk + 38112 * Nr) * c * κ ^ 2 * logb2 (1 / ε)) := by
  intro h
  obtain ⟨_, hcond, _⟩ := h 0 0 (by norm_num) (unitSys 0) (by rfl) (by simp [unitSys, BoolSystem.totalSparseness]) 2 1 (by norm_num) (by norm_num)
  norm_num [unitSys] at hcond

/-- The complete legacy proposition 6 2 contract fails because its independent condition parameter need not match the input. -/
theorem refute_6_2 :
    ¬ (∀ (Nr : ℕ) (F : BoolSystem (3 * Nr + 87))
    (_hnum : F.numPolys = 22 * Nr - 1005) (_hT : F.totalSparseness = 22 * Nr - 1005)
    (κ c : ℝ) (_hκ : 0 < κ) (_hc : 0 < c),
    ∃ Alg : SolverAlgorithm (BoolSystem (3 * Nr + 87)) (3 * Nr + 87),
      F.cond = κ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Alg.successProb F ε (BoolSystem.CorrectAnswer F) > 1 - ε ∧
        Alg.gateCost F ε ≤
          (2 : ℝ) ^ (20.46 : ℝ) * logb2 (Nr : ℝ) * ((Nr : ℝ) ^ (3.5 : ℝ)) * c * κ ^ 2 *
            logb2 (1 / ε)) := by
  intro h
  obtain ⟨_, hcond, _⟩ := h 0 (unitSys 87) (by norm_num [unitSys]) (by norm_num [unitSys, BoolSystem.totalSparseness]) 2 1 (by norm_num) (by norm_num)
  norm_num [unitSys] at hcond

/-- The complete legacy proposition 6 3 contract fails because its independent condition parameter need not match the input. -/
theorem refute_6_3 :
    ¬ (∀ (Nh b Nr w : ℕ) (F : BoolSystem (2 * b * Nr))
    (_hnum : F.numPolys = (2 * b - 1) * Nr + Nh)
    (_hT : F.totalSparseness = 401 * Nr * w + 101 * Nh / 25 - 101 * w)
    (κ c : ℝ) (_hκ : 0 < κ) (_hc : 0 < c),
    ∃ Alg : SolverAlgorithm (BoolSystem (2 * b * Nr)) (2 * b * Nr),
      F.cond = κ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Alg.successProb F ε (BoolSystem.CorrectAnswer F) > 1 - ε ∧
        Alg.gateCost F ε ≤
          (2 : ℝ) ^ (18.83 : ℝ) * logb2 ((Nr : ℝ) * (b : ℝ)) *
            ((Nr : ℝ) ^ (3.5 : ℝ)) * ((b : ℝ) ^ (3.5 : ℝ)) * c * κ ^ 2 * logb2 (1 / ε)) := by
  intro h
  obtain ⟨_, hcond, _⟩ := h 0 0 0 0 (unitSys 0) (by norm_num [unitSys]) (by norm_num [unitSys, BoolSystem.totalSparseness]) 2 1 (by norm_num) (by norm_num)
  norm_num [unitSys] at hcond

/-- The complete legacy proposition 6 4 contract fails because its independent condition parameter need not match the input. -/
theorem refute_6_4 :
    ¬ (∀ (n r : ℕ) (F : BoolSystem n) (_hnum : F.numPolys = r)
    (_hT : F.totalSparseness = (n + 1) * (n + 2) * r / 2)
    (κ c : ℝ) (_hκ : 0 < κ) (_hc : 0 < c),
    ∃ Alg : SolverAlgorithm (BoolSystem n) n,
      F.cond = κ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Alg.successProb F ε (BoolSystem.CorrectAnswer F) > 1 - ε ∧
        IsTildeO (Alg.gateCost F ε)
          ((n : ℝ) ^ 7 * (r : ℝ) ^ (3.5 : ℝ) * κ ^ 2 * Real.log (1 / ε))
          ((n : ℝ) + (r : ℝ))) := by
  intro h
  obtain ⟨_, hcond, _⟩ := h 0 0 (unitSys 0) (by rfl) (by simp [unitSys, BoolSystem.totalSparseness]) 2 1 (by norm_num) (by norm_num)
  norm_num [unitSys] at hcond

/-- The complete legacy corollary 6 5 contract fails because its independent condition parameter need not match the input. -/
theorem refute_6_5 :
    ¬ (∀ (n r : ℕ) (γ : ℝ) (_hγ : (r : ℝ) = γ * (n : ℝ))
    (F : BoolSystem n) (_hnum : F.numPolys = r) (κ c : ℝ) (_hκ : 0 < κ) (_hc : 0 < c),
    ∃ Alg : SolverAlgorithm (BoolSystem n) n,
      F.cond = κ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Alg.successProb F ε (BoolSystem.CorrectAnswer F) > 1 - ε ∧
        IsTildeO (Alg.gateCost F ε)
          (γ * (n : ℝ) ^ (10.5 : ℝ) * κ ^ 2 * Real.log (1 / ε))
          ((n : ℝ) + (r : ℝ))) := by
  intro h
  obtain ⟨_, hcond, _⟩ := h 0 0 0 (by norm_num) (unitSys 0) (by rfl) 2 1 (by norm_num) (by norm_num)
  norm_num [unitSys] at hcond

end Qatlib.Papers.BoolEquation17.MainResults.Counter

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyAlgebra
public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyState

@[expose] public section


/-! # Counterexamples and a repaired grid-image contract
These probes concern literal archived formal statements. They do not refute
the paper's algorithms, candidate-generation promises, or conjugate operators.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- The norm-factorization equation alone does not force a nonnegative exponent. -/
theorem bad84 :
    let α : Zsqrt2 := ⟨0, 0⟩
    (α.toComplex / (2 : ℂ) ^ (0 : ℕ)) *
      (α.bullet.toComplex / (2 : ℂ) ^ (0 : ℕ)) = (2 : ℂ) ^ (-1 : ℤ) * (0 : ℂ) ∧
    ¬ (0 ≤ (-1 : ℤ) ∧ ((-1 : ℤ) = 0 ∨ (-1 : ℤ) % 8 = 1)) := by
  norm_num [Zsqrt2.toComplex, Zsqrt2.bullet]

/-- A vanishing residual makes the archived exponent bound false. -/
theorem bad85 :
    let v : Zomega := Zomega.one
    let α : Zsqrt2 := ⟨0, 0⟩
    let ξ : ℂ := 0
    ξ = 1 - (starRingEnd ℂ (v.toComplex / (Real.sqrt 2 : ℂ) ^ (0 : ℕ))) *
      (v.toComplex / (Real.sqrt 2 : ℂ) ^ (0 : ℕ)) ∧
    ξ = α.toComplex / (2 : ℂ) ^ (0 : ℕ) ∧
    0 ≤ ξ.re ∧ ξ.re ≤ 1 ∧
    (α.toComplex / (2 : ℂ) ^ (0 : ℕ)) *
      (α.bullet.toComplex / (2 : ℂ) ^ (0 : ℕ)) = (2 : ℂ) ^ (2 : ℤ) * (0 : ℂ) ∧
    ¬ ((2 : ℤ) ≤ (4 : ℤ) ^ (0 : ℕ)) := by
  norm_num [Zomega.toComplex_one, Zsqrt2.toComplex, Zsqrt2.bullet]

/-- A nonsingular real plane matrix acts injectively on complex coordinates. -/
theorem matInjective (M : Mat2) (hd : M.det ≠ 0) : Function.Injective M.apply := by
  intro x y h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [Mat2.apply] at hr hi
  apply Complex.ext
  · apply mul_left_cancel₀ hd
    dsimp [Mat2.det]
    linear_combination M.m22 * hr - M.m12 * hi
  · apply mul_left_cancel₀ hd
    dsimp [Mat2.det]
    linear_combination M.m11 * hi - M.m21 * hr

/-- Grid-image equivalence holds when both actual coordinate maps are nonsingular. -/
theorem gridImageEquiv (G Gb : Mat2) (hG : G.det ≠ 0) (hb : Gb.det ≠ 0)
    (A B : Set ℂ) (u v : Zomega)
    (hv : v.toComplex = G.apply u.toComplex)
    (hvb : v.bullet.toComplex = Gb.apply u.bullet.toComplex) :
    TwoDimGridProblem A B u ↔
      TwoDimGridProblem (matImage G A) (matImage Gb B) v := by
  constructor
  · rintro ⟨ha, hb'⟩
    exact ⟨⟨u.toComplex, ha, hv⟩, ⟨u.bullet.toComplex, hb', hvb⟩⟩
  · rintro ⟨⟨x, hx, hxeq⟩, ⟨y, hy, hyeq⟩⟩
    have hx' : u.toComplex = x := matInjective G hG (hv.symm.trans hxeq)
    have hy' : u.bullet.toComplex = y := matInjective Gb hb (hvb.symm.trans hyeq)
    exact ⟨hx'.symm ▸ hx, hy'.symm ▸ hy⟩

/-- An identity first map and zero second map satisfy the old premises but lose membership. -/
theorem bad513 :
    let G : FormGridOperator := ⟨1, 0, 0, 1, 0, 0, 0, 0⟩
    let Gb : FormGridOperator := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
    G.valid ∧ Gb.valid ∧ G.special ∧
      Zomega.zero.toComplex = G.mat.apply Zomega.zero.toComplex ∧
      Zomega.zero.bullet.toComplex = Gb.mat.apply Zomega.zero.bullet.toComplex ∧
      ¬ TwoDimGridProblem (Set.univ : Set ℂ) ({1} : Set ℂ) Zomega.zero ∧
      TwoDimGridProblem (matImage G.mat Set.univ) (matImage Gb.mat {1}) Zomega.zero := by
  dsimp
  refine ⟨by norm_num [FormGridOperator.valid], by norm_num [FormGridOperator.valid],
    Or.inl (by norm_num [FormGridOperator.mat, Mat2.det]), ?_, ?_, ?_, ?_⟩
  · simp [FormGridOperator.mat, Mat2.apply]
  · simp [FormGridOperator.mat, Mat2.apply, Zomega.bullet, Zomega.zero, Zomega.toComplex]
  · simp [TwoDimGridProblem, Zomega.bullet, Zomega.zero, Zomega.toComplex]
  · constructor
    · exact ⟨0, Set.mem_univ _, by simp [FormGridOperator.mat, Mat2.apply]⟩
    · exact ⟨1, Set.mem_singleton _, by
        simp [FormGridOperator.mat, Mat2.apply, Zomega.bullet, Zomega.zero, Zomega.toComplex]⟩

/-- Specialness cannot be preserved under conjugation by an arbitrary singular matrix. -/
theorem singularShift :
    ¬ ∃ M : Mat2, (M.det = 1 ∨ M.det = -1) ∧
      M = (⟨0, 0, 0, 0⟩ : Mat2).mul (Mat2.one.mul ⟨0, 0, 0, 0⟩) := by
  rintro ⟨M, h, rfl⟩
  norm_num [Mat2.mul, Mat2.one, Mat2.det] at h

/-- The empty-set conclusion of the old near-optimality contract fails at epsilon two. -/
theorem bad88 : ¬ ∃ C : ℝ, 0 < C ∧
    ((∅ : Finset ℂ).card : ℝ) ≤ C * Real.log (1 / (2 : ℝ)) := by
  rintro ⟨C, hC, hempty⟩
  have hlog : Real.log (1 / (2 : ℝ)) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hneg := mul_neg_of_pos_of_neg hC hlog
  norm_num at hempty
  linarith

/-- Every state has a strictly positive first diagonal entry in its second form. -/
theorem deltaPositive (S : State) : 0 < S.matDelta.m11 := by
  exact mul_pos S.eps_pos (Real.rpow_pos_of_pos lam_pos _)

/-- A zero second operator cannot produce a state after the archived inverse action. -/
theorem zeroConjugate (S : State) : ¬ ∃ S' : State,
    S'.matDelta = (Mat2.transpose (Mat2.inv (⟨0, 0, 0, 0⟩ : Mat2))).mul
      (S.matDelta.mul (Mat2.inv ⟨0, 0, 0, 0⟩)) := by
  rintro ⟨S', h⟩
  have hz := congrArg Mat2.m11 h
  norm_num [Mat2.transpose, Mat2.inv, Mat2.det, Mat2.mul] at hz
  have hp := deltaPositive S'
  linarith

/-- The identity really preserves every archived cyclotomic point. -/
def identityGrid : GridOperator where
  mat := Mat2.one
  mapsZomega u := ⟨u, by apply Complex.ext <;> simp [Mat2.one, Mat2.apply]⟩

/-- The zero map also satisfies the archived grid-preservation predicate. -/
def zeroGrid : GridOperator where
  mat := ⟨0, 0, 0, 0⟩
  mapsZomega u := ⟨Zomega.zero, by simp [Mat2.apply]⟩

/-- The identity satisfies the original specialness premise. -/
theorem identitySpecial : GridOperator.special identityGrid := by
  exact Or.inl (by norm_num [identityGrid, Mat2.one, Mat2.det])

/-- The original inverse-action existence conclusion fails for genuine grid operators. -/
theorem badA4 (S : State) :
    GridOperator.special identityGrid ∧ ¬ ∃ S' : State,
      S'.matD = (Mat2.transpose (Mat2.inv identityGrid.mat)).mul
        (S.matD.mul (Mat2.inv identityGrid.mat)) ∧
      S'.matDelta = (Mat2.transpose (Mat2.inv zeroGrid.mat)).mul
        (S.matDelta.mul (Mat2.inv zeroGrid.mat)) := by
  refine ⟨identitySpecial, ?_⟩
  rintro ⟨S', _, h⟩
  exact zeroConjugate S ⟨S', h⟩

/-- The old specialness conclusion fails for k one and an unconstrained zero shift matrix. -/
theorem badA9 : GridOperator.special identityGrid ∧
    ¬ ∃ G' : GridOperator, GridOperator.special G' ∧
      G'.mat = (Mat2.pow (⟨0, 0, 0, 0⟩ : Mat2) 1).mul
        (identityGrid.mat.mul (Mat2.pow (⟨0, 0, 0, 0⟩ : Mat2) 1)) := by
  refine ⟨identitySpecial, ?_⟩
  rintro ⟨G', hs, heq⟩
  have hd := congrArg Mat2.det heq
  norm_num [Mat2.pow, Mat2.mul, Mat2.one, identityGrid, Mat2.det] at hd
  change G'.mat.det = 0 at hd
  rcases hs with hs | hs <;> rw [hd] at hs <;> norm_num at hs

/-- An arbitrary natural cost can violate the proposed unshifted denominator formula. -/
theorem freeCount73 (U : UTForm) (k : ℕ) :
    ∃ TCount : UTForm → ℕ, ¬ (TCount U = 2 * k - 2 ∨ TCount U = 2 * k) := by
  refine ⟨fun _ => 2 * k + 1, ?_⟩
  change ¬ (2 * k + 1 = 2 * k - 2 ∨ 2 * k + 1 = 2 * k)
  omega

/-- An arbitrary natural cost can also violate the phase-shifted denominator formula. -/
theorem freeCount97 (U : UTOmegaForm) (k : ℕ) :
    ∃ TCount : UTOmegaForm → ℕ, ¬ (TCount U = 2 * k - 1 ∨ TCount U = 2 * k + 1) := by
  refine ⟨fun _ => 2 * k + 2, ?_⟩
  change ¬ (2 * k + 2 = 2 * k - 1 ∨ 2 * k + 2 = 2 * k + 1)
  omega

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy

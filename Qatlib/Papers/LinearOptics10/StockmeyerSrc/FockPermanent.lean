/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.FunctionFibers
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Defs

@[expose] public section


/-! # The actual collision-free Fock coefficient equals the permanent

Fixed 1011.3245v1 Lemma 21. The proof constructs the precise equivalence
between admissible assignment functions and permutations, including n=0.
No amplitude/permanent equality is supplied as an assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix ComplexConjugate
open ComplexConjugate
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockPermanent
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock.BosonOperators.FunctionFibers

/-- Every factorial in the collision-free initial occupation is one. -/
theorem oneFactorial {m n : ℕ} (h : n ≤ m) : occFactorial (oneOccupation m n h) = 1 := by
  unfold occFactorial
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : i.val < n <;> simp [oneOccupation, hi]

/-- The actual factorial-weighted pairing reads the collision-free coefficient unchanged. -/
theorem oneRead {m n : ℕ} (h : n ≤ m) (a : FockCoeff m n) :
    fockInner (oneMonomialCoeff h) a = a (oneOccupation m n h) := by
  simp [fockInner, oneMonomialCoeff, oneFactorial]

/-- The entire original Lemma 21 holds for every actual matrix and n<=m, including n=0. -/
theorem permanentCoeff {m n : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (h : n ≤ m) :
    Matrix.permanent (topLeft V n h) =
      fockInner (oneMonomialCoeff h) (polyActCoeffVec V n h) := by
  rw [oneRead]
  have hs := weightedSum h (fun f : Fin n → Fin m => ∏ k, V (Fin.castLE h k) (f k))
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  calc
    _ = ∑ f : Fin n → Fin m,
        if SingleFibers f then ∏ k, V (Fin.castLE h k) (f k) else 0 := by
      simpa only [Matrix.transpose_apply, topLeft] using hs
    _ = _ := by
      unfold polyActCoeffVec polyActCoeff
      apply Finset.sum_congr rfl
      intro f _
      dsimp only [oneOccupation]
      by_cases hf : SingleFibers f
      · have hh : ∀ i : Fin m,
            (Finset.univ.filter (fun k => f k = i)).card = if i.val < n then 1 else 0 := hf
        rw [ite_eq_left hf]
        exact (ite_eq_left hh).symm
      · have hh : ¬(∀ i : Fin m,
            (Finset.univ.filter (fun k => f k = i)).card = if i.val < n then 1 else 0) := hf
        rw [ite_eq_right hf]
        exact (ite_eq_right hh).symm

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockPermanent

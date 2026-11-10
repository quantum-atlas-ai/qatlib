/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.QuboForms.Quadratic
import Qatlib.Foundations.BooleanEnergy.PenaltyExact.Global
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.QuboForms
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact

def rowAffine {M N : ℕ} (r : Fin M) (p : ColumnPair N) : Affine (Variable M N) :=
  one - (2:ℝ) • coordinate (.inl (r,left p)) - (2:ℝ) • coordinate (.inl (r,right p)) +
    (4:ℝ) • coordinate (.inr (r,p))

theorem rowAffine_eval {M N : ℕ} (x : Configuration M N) (r : Fin M) (p : ColumnPair N) :
    affineEval x (rowAffine r p) =
      rowLinear (main x r (left p)) (main x r (right p)) (ancilla x r p) := by
  simp only [rowAffine,map_add,map_sub,map_smul,affineEval_one,affineEval_variable,
    smul_eq_mul]
  rfl

def penaltyQuadratic {M N : ℕ} (r : Fin M) (p : ColumnPair N) : Quadratic (Variable M N) :=
  (3:ℝ) • multiply one (coordinate (.inr (r,p))) +
    multiply (coordinate (.inl (r,left p))) (coordinate (.inl (r,right p))) -
    (2:ℝ) • multiply (coordinate (.inl (r,left p))) (coordinate (.inr (r,p))) -
    (2:ℝ) • multiply (coordinate (.inl (r,right p))) (coordinate (.inr (r,p)))

theorem penaltyQuadratic_eval {M N : ℕ} (x : Configuration M N) (r : Fin M)
    (p : ColumnPair N) : quadraticEval x (penaltyQuadratic r p) =
    andPenalty (main x r (left p)) (main x r (right p)) (ancilla x r p) := by
  simp only [penaltyQuadratic,map_sub,map_add,map_smul,quadraticEval_multiply,
    affineEval_one,affineEval_variable,smul_eq_mul,one_mul]
  dsimp [andPenalty,main,ancilla]
  ring

def pairQuadratic {M N : ℕ} (δ : ℝ) (p : ColumnPair N) : Quadratic (Variable M N) :=
  multiply (∑ r : Fin M, rowAffine r p) (∑ r : Fin M, rowAffine r p) +
    (δ-8) • ∑ r : Fin M, penaltyQuadratic r p

theorem pairQuadratic_eval {M N : ℕ} (δ : ℝ) (x : Configuration M N) (p : ColumnPair N) :
    quadraticEval x (pairQuadratic δ p) = paperPair δ x p := by
  rw [paperPair_eq_squarePair]
  simp only [pairQuadratic,map_add,map_smul,map_sum,quadraticEval_multiply,
    rowAffine_eval,penaltyQuadratic_eval,smul_eq_mul,squarePair,pairLinear,pairPenalty,pow_two]

def hadamardQuadratic {M N : ℕ} (δ : ℝ) : Quadratic (Variable M N) :=
  ∑ p : ColumnPair N, pairQuadratic δ p

theorem hadamardQuadratic_eval {M N : ℕ} (δ : ℝ) (x : Configuration M N) :
    quadraticEval x (hadamardQuadratic δ) = paperEnergy δ x := by
  simp only [hadamardQuadratic,map_sum,pairQuadratic_eval,paperEnergy]

theorem compiled_ground_iff {M N : ℕ} (hM : 2 ≤ M) (x : Configuration M N) :
    IsGround (fun y => quadraticEval y (hadamardQuadratic (4*(M:ℝ)^2))) x ↔
      Valid x ∧ IsGround energy (main x) := by
  have hfun : (fun y : Configuration M N =>
      quadraticEval y (hadamardQuadratic (4*(M:ℝ)^2))) = paperEnergy (4*(M:ℝ)^2) :=
    funext (hadamardQuadratic_eval _)
  rw [hfun]
  exact source_ground_iff hM x

end Qatlib.Foundations.BooleanEnergy.QuboForms

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Field

namespace Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator

open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def closedNbhd (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  insert u (G.neighborFinset u)

@[simp]
theorem mem_closedNbhd {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ closedNbhd G u ↔ v = u ∨ G.Adj u v := by
  simp [closedNbhd]

@[simp]
theorem self_mem_closedNbhd (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    u ∈ closedNbhd G u := mem_closedNbhd.mpr (Or.inl rfl)

theorem closedNbhd_comm {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ closedNbhd G u ↔ u ∈ closedNbhd G v := by
  rw [mem_closedNbhd, mem_closedNbhd]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h.symm
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h.symm

def diagLift (x : V → ℝ) : V × V → ℝ :=
  fun p => if p.1 = p.2 then x p.1 else 0

@[simp]
theorem diagLift_apply (x : V → ℝ) (p : V × V) :
    diagLift x p = if p.1 = p.2 then x p.1 else 0 := rfl

def walkF (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix (V × V) (V × V) ℝ :=
  Matrix.of fun p q =>
    if q.1 = p.1 then
      (if p.2 ∈ closedNbhd G p.1 then
        ((if q.2 = p.2 then 1 else 0) -
          (if q.2 ∈ closedNbhd G p.1 then 2 / (d + 1) else 0))
      else (if q.2 = p.2 then 1 else 0))
    else 0

def walkX : Matrix (V × V) (V × V) ℝ :=
  Matrix.of fun p q => if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

def walkP : Matrix (V × V) (V × V) ℝ :=
  Matrix.of fun p q => if p = q ∧ p.1 = p.2 then 1 else 0

def walkQ (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix (V × V) (V × V) ℝ :=
  walkP * walkF G d * walkX * walkF G d * walkP

def adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of fun u v => if G.Adj u v then 1 else 0

def walkA (d : ℝ) : ℝ := (1 - 2 / (d + 1)) ^ 2

def walkB (d : ℝ) : ℝ := (2 / (d + 1)) ^ 2

def walkM (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix V V ℝ :=
  walkA d • (1 : Matrix V V ℝ) + walkB d • adjMatrix G

def compSet (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.Reachable u v

def compSize (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : ℕ := (compSet G u).card

@[simp]
theorem mem_compSet {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ compSet G u ↔ G.Reachable u v := by
  simp [compSet]

theorem self_mem_compSet (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    u ∈ compSet G u := by
  simp

theorem compSet_pos (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : 0 < compSize G u := by
  unfold compSize
  exact Finset.card_pos.mpr ⟨u, self_mem_compSet G u⟩

theorem compSize_pos (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (0 : ℝ) < (compSize G u : ℝ) := by
  exact_mod_cast compSet_pos G u

def uniformOn (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : V → ℝ := by
  classical
  exact fun v => if G.Reachable u v then 1 / (compSize G u : ℝ) else 0

def l2norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

theorem l2norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ l2norm x :=
  Real.sqrt_nonneg _

theorem l2norm_sq_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2norm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem l2norm_diagLift (x : V → ℝ) : l2norm (diagLift x) = l2norm x := by
  unfold l2norm
  congr 1
  rw [Fintype.sum_prod_type]
  have : ∀ a : V, (∑ b : V, diagLift x (a, b) ^ 2) = x a ^ 2 := by
    intro a
    simp [diagLift_apply]
  simp only [this]

theorem reachable_of_adj {G : SimpleGraph V} {u v w : V}
    (huv : G.Reachable u v) (hvw : G.Adj v w) : G.Reachable u w := by
  exact huv.trans hvw.reachable

theorem not_reachable_adj {G : SimpleGraph V} {u v w : V}
    (hv : ¬ G.Reachable u v) (hvw : G.Adj v w) : ¬ G.Reachable u w := by
  intro hw
  exact hv (hw.trans hvw.symm.reachable)

def basisVec (u : V) : V → ℝ := fun v => if v = u then 1 else 0

@[simp]
theorem basisVec_apply_self (u : V) : basisVec u u = 1 := by
  simp [basisVec]

theorem basisVec_apply_of_ne {u v : V} (h : v ≠ u) : basisVec u v = 0 := by
  simp [basisVec, h]

theorem diagLift_basisVec (u : V) :
    diagLift (basisVec u) = fun p : V × V => if p = (u, u) then 1 else 0 := by
  funext p
  by_cases hp : p = (u, u)
  · subst hp
    simp [diagLift_apply, basisVec]
  · have hzero : (if p = (u, u) then (1 : ℝ) else 0) = 0 := by simp [hp]
    rw [hzero]
    by_cases h1 : p.1 = p.2
    · by_cases h2 : p.1 = u
      · exfalso
        apply hp
        ext
        · exact h2
        · rw [← h1]; exact h2
      · have h2' : ¬ p.2 = u := by rw [← h1]; exact h2
        simp [diagLift_apply, basisVec, h1, h2, h2']
    · simp [diagLift_apply, h1]

end

end Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator

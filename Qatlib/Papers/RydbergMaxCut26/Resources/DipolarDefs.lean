/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Resources.MomentCounts
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar
open Qatlib.Papers.RydbergMaxCut26.Resources.Counts
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation

def endpoints {n : ℕ} (s : SitePair n) : Fin n×Fin n := (s.1.inf,s.1.sup)

theorem endpoints_distinct {n : ℕ} (s : SitePair n) : (endpoints s).1 ≠ (endpoints s).2 := by
  intro h
  have hs : s.1=Sym2.mk (endpoints s).1 (endpoints s).2 := (Sym2.sortEquiv.left_inv s.1).symm
  apply s.2
  rw [hs,Sym2.mk_isDiag_iff]
  exact h

noncomputable def coupling {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (i j : Fin n) : ℝ := C3/(2*dist (position i) (position j)^3)

theorem coupling_positive {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (hinj : Function.Injective position)
    (i j : Fin n) (hij : i≠j) : 0 < coupling C3 position i j := by
  have hd : 0 < dist (position i) (position j) := dist_pos.mpr (fun h => hij (hinj h))
  exact div_pos hC3 (mul_pos (by norm_num) (pow_pos hd 3))

theorem coupling_symmetric {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (i j : Fin n) : coupling C3 position i j=coupling C3 position j i := by
  simp only [coupling,dist_comm]

def ExactCouplingMatch {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (w : SitePair n → ℝ) : Prop := ∀ s,coupling C3 position (endpoints s).1 (endpoints s).2=w s

theorem zero_nonedge_obstruction {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (hinj : Function.Injective position)
    (w : SitePair n → ℝ) (s : SitePair n) (hzero : w s=0) :
    ¬ExactCouplingMatch C3 position w := by
  intro hmatch
  have hp := coupling_positive C3 hC3 position hinj _ _ (endpoints_distinct s)
  rw [hmatch s,hzero] at hp
  exact lt_irrefl 0 hp

theorem no_exact_placement {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3) (w : SitePair n → ℝ)
    (hmissing : ∃ s,w s=0) :
    ¬∃ position : Fin n → EuclideanSpace ℝ (Fin 3),
      Function.Injective position ∧ ExactCouplingMatch C3 position w := by
  rintro ⟨position,hinj,hmatch⟩
  obtain ⟨s,hs⟩ := hmissing
  exact zero_nonedge_obstruction C3 hC3 position hinj w s hs hmatch

noncomputable def rydbergHamiltonian {n : ℕ} (C3 : ℝ)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (Ω : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  (∑ s : SitePair n,coupling C3 position (endpoints s).1 (endpoints s).2 •
    (pairPauli (endpoints s).1 (endpoints s).2 0+pairPauli (endpoints s).1 (endpoints s).2 1))+
    (Ω/2) • ∑ i : Fin n,sitePauli n i 0

theorem actual_static_model {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (Ω : ℝ) (hΩ : Ω=0) (w : SitePair n → ℝ) (hmatch : ExactCouplingMatch C3 position w) :
    rydbergHamiltonian C3 position Ω=secondaryHamiltonian endpoints w := by
  simp only [rydbergHamiltonian,hΩ,zero_div,zero_smul,add_zero,secondaryHamiltonian]
  apply Finset.sum_congr rfl
  intro s _
  rw [hmatch s]
end Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar

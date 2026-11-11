/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Resources.MomentCounts
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dipolar couplings and exact static realizations

`coupling` models inverse-cube dipolar interactions between sites in three-dimensional Euclidean
space, and `rydbergHamiltonian` adds the transverse drive. `ExactCouplingMatch` records exact
realization of all target pair weights; positive interaction strength and distinct positions
obstruct any target containing a zero pair weight.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `actual_static_model`: identifies the zero-drive Hamiltonian under exact coupling matching.
* `no_exact_placement`: rules out an injective exact placement when a target pair weight
  vanishes.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

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

/-- The ordered pair of minimum and maximum site indices representing an unordered distinct-site
pair. -/
def endpoints {n : ℕ} (s : SitePair n) : Fin n×Fin n := (s.1.inf,s.1.sup)

/-- The two chosen endpoints of a `SitePair` are distinct. -/
theorem endpoints_distinct {n : ℕ} (s : SitePair n) : (endpoints s).1 ≠ (endpoints s).2 := by
  intro h
  have hs : s.1=Sym2.mk (endpoints s).1 (endpoints s).2 := (Sym2.sortEquiv.left_inv s.1).symm
  apply s.2
  rw [hs,Sym2.mk_isDiag_iff]
  exact h

/-- The dipolar coefficient `C3 / (2 * dist (position i) (position j)^3)`. -/
noncomputable def coupling {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (i j : Fin n) : ℝ := C3/(2*dist (position i) (position j)^3)

/-- For positive `C3` and an injective placement, the dipolar coupling between distinct sites is
strictly positive. -/
theorem coupling_positive {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (hinj : Function.Injective position)
    (i j : Fin n) (hij : i≠j) : 0 < coupling C3 position i j := by
  have hd : 0 < dist (position i) (position j) := dist_pos.mpr (fun h => hij (hinj h))
  exact div_pos hC3 (mul_pos (by norm_num) (pow_pos hd 3))

/-- Exchanging the two sites preserves their dipolar coupling. -/
theorem coupling_symmetric {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (i j : Fin n) : coupling C3 position i j=coupling C3 position j i := by
  simp only [coupling,dist_comm]

/-- The condition that every dipolar pair coupling equals the corresponding target weight `w s`. -/
def ExactCouplingMatch {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (w : SitePair n → ℝ) : Prop := ∀ s,coupling C3 position (endpoints s).1 (endpoints s).2=w s

/-- For positive `C3` and an injective placement, a zero target pair weight prevents exact
coupling matching. -/
theorem zero_nonedge_obstruction {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (hinj : Function.Injective position)
    (w : SitePair n → ℝ) (s : SitePair n) (hzero : w s=0) :
    ¬ExactCouplingMatch C3 position w := by
  intro hmatch
  have hp := coupling_positive C3 hC3 position hinj _ _ (endpoints_distinct s)
  rw [hmatch s,hzero] at hp
  exact lt_irrefl 0 hp

/-- If `C3 > 0` and some target pair weight is zero, no injective three-dimensional placement
exactly matches all target couplings. -/
theorem no_exact_placement {n : ℕ} (C3 : ℝ) (hC3 : 0 < C3) (w : SitePair n → ℝ)
    (hmissing : ∃ s,w s=0) :
    ¬∃ position : Fin n → EuclideanSpace ℝ (Fin 3),
      Function.Injective position ∧ ExactCouplingMatch C3 position w := by
  rintro ⟨position,hinj,hmatch⟩
  obtain ⟨s,hs⟩ := hmissing
  exact zero_nonedge_obstruction C3 hC3 position hinj w s hs hmatch

/-- The sum of dipolar XX+YY pair interactions and the drive term `(Ω/2) * Σ_i X_i`. -/
noncomputable def rydbergHamiltonian {n : ℕ} (C3 : ℝ)
    (position : Fin n → EuclideanSpace ℝ (Fin 3)) (Ω : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  (∑ s : SitePair n,coupling C3 position (endpoints s).1 (endpoints s).2 •
    (pairPauli (endpoints s).1 (endpoints s).2 0+pairPauli (endpoints s).1 (endpoints s).2 1))+
    (Ω/2) • ∑ i : Fin n,sitePauli n i 0

/-- With zero drive and exact pairwise coupling matching, the Rydberg Hamiltonian equals the
target secondary XX+YY Hamiltonian. This records the geometric realization condition for the
resource in [CrostaSaubanereHuber2026]. -/
theorem actual_static_model {n : ℕ} (C3 : ℝ) (position : Fin n → EuclideanSpace ℝ (Fin 3))
    (Ω : ℝ) (hΩ : Ω=0) (w : SitePair n → ℝ) (hmatch : ExactCouplingMatch C3 position w) :
    rydbergHamiltonian C3 position Ω=secondaryHamiltonian endpoints w := by
  simp only [rydbergHamiltonian,hΩ,zero_div,zero_smul,add_zero,secondaryHamiltonian]
  apply Finset.sum_congr rfl
  intro s _
  rw [hmatch s]
end Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar

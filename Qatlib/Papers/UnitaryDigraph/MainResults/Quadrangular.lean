/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.Finite.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Insert
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.UnitaryDigraph.MainResults.Defs

/-!
# Quadrangularity conditions for unitary digraphs

This module derives necessary neighborhood conditions for digraphs supporting unitary matrices,
including Lemma 1 of [Severini2003]. Orthogonality of unitary rows yields outgoing strong
quadrangularity; reversal supplies the incoming version, and unitarity also ensures nonempty
neighborhoods.

## Main statements

* `lemma1`: Every unitary digraph is strongly quadrangular.
* `inStronglyQuadrangular_of_isUnitaryDigraph`: Derive incoming strong quadrangularity.
* `isUnitaryDigraph_reverse`: Reversing a unitary digraph preserves unitary realizability.

## References

* [Severini, 2003][Severini2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph
open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The Hermitian inner product of two rows of a unitary matrix is one when their indices agree
and zero otherwise. -/
theorem unitary_row_inner {U : Matrix V V ℂ} (hU : U ∈ Matrix.unitaryGroup V ℂ)
    (a c : V) : ∑ j : V, U a j * star (U c j) = if a = c then 1 else 0 := by
  have h1 : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  have h2 := congrFun (congrFun h1 a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  simpa only [Matrix.star_apply] using h2

/-- The row of `U` indexed by `i`, restricted to the column set `T`. -/
def rowOn (U : Matrix V V ℂ) (T : Set V) (i : V) : ↥T → ℂ := fun c => U i c.1

omit [Fintype V] [DecidableEq V] in

/-- Evaluating a restricted row at a column in `T` returns the corresponding entry of `U`. -/
@[simp] theorem rowOn_apply (U : Matrix V V ℂ) (T : Set V) (i : V) (c : ↥T) :
    rowOn U T i c = U i c.1 := rfl

/-- A unitary digraph is outgoing strongly quadrangular. -/
theorem outStronglyQuadrangular_of_isUnitaryDigraph (D : Defs.Digraph V)
    (hD : IsUnitaryDigraph D) : OutStronglyQuadrangular D := by
  classical
  rintro ⟨S, T, hcard, hmeet, hsub⟩
  obtain ⟨U, hU, hpat⟩ := hD
  have hSfin : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  have hTfin : T.Finite := Set.finite_univ.subset (Set.subset_univ T)
  let : Fintype ↥S := hSfin.fintype
  let : Fintype ↥T := hTfin.fintype
  have hsupp : ∀ i c : V, U i c ≠ 0 ↔ D.Adj i c := hpat

  have hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ c : V, c ∉ T → U i c = 0 ∨ U j c = 0 := by
    intro i hi j hj hij c hc
    by_contra h
    simp only [not_or] at h
    have hmem : c ∈ D.outNbrs i ∩ D.outNbrs j := by
      refine Set.mem_inter ?_ ?_
      · rw [mem_outNbrs]; exact (hsupp i c).mp h.1
      · rw [mem_outNbrs]; exact (hsupp j c).mp h.2
    exact hc (hsub i hi j hj hij hmem)

  have horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ∑ c : ↥T, rowOn U T i c * star (rowOn U T j c) = 0 := by
    intro i hi j hj hij
    have hfull : ∑ c : V, U i c * star (U j c) = 0 := by
      rw [unitary_row_inner hU i j]
      simp [hij]
    have hTs : ∑ c : ↥T, rowOn U T i c * star (rowOn U T j c)
        = ∑ c ∈ hTfin.toFinset, U i c * star (U j c) := by
      simp only [rowOn]
      exact (Finset.sum_subtype (p := fun c => c ∈ T) hTfin.toFinset
        (fun x => hTfin.mem_toFinset) (fun c => U i c * star (U j c))).symm
    have hsubsum : ∑ c ∈ hTfin.toFinset, U i c * star (U j c)
        = ∑ c : V, U i c * star (U j c) := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro x _ hx
      have hxT : x ∉ T := fun h => hx (hTfin.mem_toFinset.mpr h)
      rcases hoff i hi j hj hij x hxT with h | h <;> simp [h]
    rw [hTs, hsubsum, hfull]

  have hne : ∀ i : ↥S, rowOn U T i.1 ≠ 0 := by
    intro i
    obtain ⟨c, hc⟩ := hmeet i.1 i.2
    rw [Set.mem_inter_iff, mem_outNbrs] at hc
    obtain ⟨hci, hco⟩ := hc
    simp only [outNbrsOthers, Set.mem_iUnion, exists_prop] at hco
    obtain ⟨j, hjS, hjne, hcj⟩ := hco
    rw [mem_outNbrs] at hcj
    have hcT : c ∈ T := by
      refine hsub i.1 i.2 j hjS (fun h => hjne h.symm) ?_
      refine Set.mem_inter ?_ ?_
      · rwa [mem_outNbrs]
      · rwa [mem_outNbrs]
    intro hzero
    have hU0 : U i.1 c = 0 := by
      have hcc := congrFun hzero ⟨c, hcT⟩
      simpa [rowOn] using hcc
    exact ((hsupp i.1 c).mpr hci) hU0

  have hLI : LinearIndependent ℂ (fun i : ↥S => rowOn U T i.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hvan : ∀ c : ↥T, ∑ i : ↥S, g i * rowOn U T i.1 c = 0 := by
      intro c
      have hcon := congrFun hg c
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hcon
    have h1 : ∑ i : ↥S, g i * (∑ c : ↥T, rowOn U T i.1 c * star (rowOn U T k.1 c)) = 0 := by
      have hcomm : ∑ i : ↥S, g i * (∑ c : ↥T, rowOn U T i.1 c * star (rowOn U T k.1 c))
          = ∑ c : ↥T, (∑ i : ↥S, g i * rowOn U T i.1 c) * star (rowOn U T k.1 c) := by
        calc ∑ i : ↥S, g i * (∑ c : ↥T, rowOn U T i.1 c * star (rowOn U T k.1 c))
            = ∑ i : ↥S, ∑ c : ↥T, g i * (rowOn U T i.1 c * star (rowOn U T k.1 c)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
          _ = ∑ c : ↥T, ∑ i : ↥S, g i * (rowOn U T i.1 c * star (rowOn U T k.1 c)) :=
              Finset.sum_comm
          _ = ∑ c : ↥T, (∑ i : ↥S, g i * rowOn U T i.1 c) * star (rowOn U T k.1 c) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
      rw [hcomm]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hvan c, zero_mul]
    have h2 : ∑ i : ↥S, g i * (∑ c : ↥T, rowOn U T i.1 c * star (rowOn U T k.1 c))
        = g k * (∑ c : ↥T, rowOn U T k.1 c * star (rowOn U T k.1 c)) := by
      refine Finset.sum_eq_single k ?_ ?_
      · intro b _ hbk
        have hbk' : b.1 ≠ k.1 := fun h => hbk (Subtype.ext h)
        rw [horth b.1 b.2 k.1 k.2 hbk', mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [h2] at h1
    have hdiag : (∑ c : ↥T, rowOn U T k.1 c * star (rowOn U T k.1 c)) ≠ 0 := by
      intro hz
      have hcast : ((∑ c : ↥T, Complex.normSq (rowOn U T k.1 c) : ℝ) : ℂ) = 0 := by
        rw [Complex.ofReal_sum Finset.univ, ← hz]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp [Complex.mul_conj]
      have hzero : ∑ c : ↥T, Complex.normSq (rowOn U T k.1 c) = 0 := by
        exact_mod_cast hcast
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => Complex.normSq_nonneg (rowOn U T k.1 c))).mp hzero
      apply hne k
      funext c
      exact Complex.normSq_eq_zero.mp (hall c (Finset.mem_univ c))
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hdiag

  have hle : Fintype.card ↥S ≤ Fintype.card ↥T := by
    have h := LinearIndependent.fintype_card_le_finrank hLI
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hS : Fintype.card ↥S = S.ncard := by
    rw [Set.ncard_eq_toFinset_card S hSfin, ← hSfin.card_toFinset]
  have hT' : Fintype.card ↥T = T.ncard := by
    rw [Set.ncard_eq_toFinset_card T hTfin, ← hTfin.card_toFinset]
  rw [hS, hT'] at hle
  omega

omit [Fintype V] [DecidableEq V] in

/-- Outgoing strong quadrangularity implies `StronglyQuadrangular`. -/
theorem stronglyQuadrangular_of_outSQ (D : Defs.Digraph V) (h : OutStronglyQuadrangular D) :
    StronglyQuadrangular D := by
  rintro ⟨S, T, _T', hcard, _hcard', hmeet, hsub, _hmeet', _hsub'⟩
  exact h ⟨S, T, hcard, hmeet, hsub⟩

omit [Fintype V] [DecidableEq V] in

/-- Outgoing strong quadrangularity implies outgoing quadrangularity. -/
theorem outQuadrangular_of_outSQ (D : Defs.Digraph V) (h : OutStronglyQuadrangular D) :
    OutQuadrangular D := by
  classical
  intro i j hij hcard1
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp hcard1
  have hmem : c ∈ D.outNbrs i ∩ D.outNbrs j := by
    rw [hc]; exact Set.mem_singleton c
  have hcard : ({c} : Set V).ncard < ({i, j} : Set V).ncard := by
    rw [Set.ncard_singleton, Set.ncard_pair hij]
    norm_num
  refine h ⟨{i, j}, {c}, hcard, ?_, ?_⟩
  · intro k hk
    have hk' : k = i ∨ k = j := by simpa using hk
    rcases hk' with hki | hkj
    · rw [hki]
      exact ⟨c, hmem.1, mem_outNbrsOthers (D := D) (S := {i, j}) (i := i) (j := j)
        (by simp) (fun h => hij h.symm) hmem.2⟩
    · rw [hkj]
      exact ⟨c, hmem.2, mem_outNbrsOthers (D := D) (S := {i, j}) (i := j) (j := i)
        (by simp) (fun h => hij h) hmem.1⟩
  · intro a ha b hb hab x hx
    have ha' : a = i ∨ a = j := by simpa using ha
    have hb' : b = i ∨ b = j := by simpa using hb
    rcases ha' with hai | haj <;> rcases hb' with hbi | hbj
    · exact absurd (hai.trans hbi.symm) hab
    · rw [hai, hbj] at hx; rw [hc] at hx; exact hx
    · rw [haj, hbi, Set.inter_comm] at hx; rw [hc] at hx; exact hx
    · exact absurd (haj.trans hbj.symm) hab

/-- Every unitary digraph is strongly quadrangular [Severini2003]. -/
theorem lemma1 (D : Defs.Digraph V) : IsUnitaryDigraph D → StronglyQuadrangular D := fun hD =>
  stronglyQuadrangular_of_outSQ D (outStronglyQuadrangular_of_isUnitaryDigraph D hD)

/-- A unitary digraph is outgoing quadrangular [Severini2003]. -/
theorem outQuadrangular_of_isUnitaryDigraph (D : Defs.Digraph V) (hD : IsUnitaryDigraph D) :
    OutQuadrangular D :=
  outQuadrangular_of_outSQ D (outStronglyQuadrangular_of_isUnitaryDigraph D hD)

end Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph
open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The reverse of a unitary digraph is a unitary digraph. -/
theorem isUnitaryDigraph_reverse (D : Defs.Digraph V) (hD : IsUnitaryDigraph D) :
    IsUnitaryDigraph (reverse D) := by
  obtain ⟨U, hU, hpat⟩ := hD
  refine ⟨fun a b => star (U b a), ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_apply, star_star]
    have hUU : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
    have h2 := congrFun (congrFun hUU a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    simpa [Matrix.star_apply] using h2
  · intro a b
    simp only [star_ne_zero]
    exact hpat b a

/-- A unitary digraph is incoming strongly quadrangular [Severini2003]. -/
theorem inStronglyQuadrangular_of_isUnitaryDigraph (D : Defs.Digraph V)
    (hD : IsUnitaryDigraph D) : InStronglyQuadrangular D := by
  have h := outStronglyQuadrangular_of_isUnitaryDigraph (reverse D) (isUnitaryDigraph_reverse D hD)
  simpa [InStronglyQuadrangular, OutStronglyQuadrangular] using h

/-- Every vertex of a unitary digraph has an outgoing neighbor [Severini2003]. -/
theorem outNbrs_nonempty_of_isUnitaryDigraph (D : Defs.Digraph V) (hD : IsUnitaryDigraph D)
    (i : V) : (D.outNbrs i).Nonempty := by
  obtain ⟨U, hU, hpat⟩ := hD
  have hrow : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  have hdiag := congrFun (congrFun hrow i) i
  rw [Matrix.mul_apply, Matrix.one_apply] at hdiag
  simp only [ite_true] at hdiag
  have hne : ∑ j : V, U i j * star U j i ≠ 0 := by rw [hdiag]; norm_num
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨j, mem_outNbrs.mpr ((hpat i j).mp (left_ne_zero_of_mul hj))⟩

/-- Every vertex of a unitary digraph has an incoming neighbor [Severini2003]. -/
theorem inNbrs_nonempty_of_isUnitaryDigraph (D : Defs.Digraph V)
    (hD : IsUnitaryDigraph D) (i : V) : (D.inNbrs i).Nonempty := by
  have h := outNbrs_nonempty_of_isUnitaryDigraph (reverse D) (isUnitaryDigraph_reverse D hD) i
  simpa using h

end Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular

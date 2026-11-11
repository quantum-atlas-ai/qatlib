/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Invariant tensors and the Wigner–Eckart expansion

`IsTensorOperator` expresses covariance of a matrix-valued family, and `assocTensor` rearranges
its indices into a three-index tensor. Under the stated right-unitarity condition on `ρn`, this
tensor belongs to `invariantSubmodule`; a finite spanning family then yields a Wigner–Eckart
coefficient expansion through `cgCoeff`. See [BaconChuangHarrow2005] for the mathematical
setting.

## Main statements

* `assocTensor_invariant`: turns a covariant tensor operator into an invariant tensor.
* `exists_spanning_invariant`: constructs a spanning family indexed by the invariant submodule
  dimension.
* `source_wigner_eckart_unconditional`: constructs a spanning family and reduced coefficients
  under covariance and right-unitarity.

## References

* [Bacon et al., 2005][BaconChuangHarrow2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SchurTrans06.MainResults

open scoped BigOperators Classical
open Finset

variable {G QM QN QL : Type*}
  [Fintype QM] [Fintype QN] [DecidableEq QN]
  [Fintype QL]

/-- The covariance identity relating the matrix family `T` to the three given matrix actions. -/
def IsTensorOperator (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ)
    (ρl : G → Matrix QL QL ℂ) (T : QN → Matrix QL QM ℂ) : Prop :=
  ∀ (U : G) (qn : QN) (ql : QL) (qm : QM),
    (∑ ql', ∑ qm', (ρl U) ql ql' * (T qn) ql' qm' * star (ρm U) qm' qm)
      = ∑ qn', (ρn U) qn' qn * (T qn') ql qm

/-- Reorders a matrix-valued family's entries as a tensor with indices `ql`, `qm`, and `qn`. -/
def assocTensor (T : QN → Matrix QL QM ℂ) : QL → QM → QN → ℂ :=
  fun ql qm qn => T qn ql qm

/-- The tensor is fixed by the componentwise action of `ρl`, the adjoint of `ρm`, and the
adjoint of `ρn`. -/
def IsInvariantOperator (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ)
    (ρl : G → Matrix QL QL ℂ) (A : QL → QM → QN → ℂ) : Prop :=
  ∀ (U : G) (ql : QL) (qm : QM) (qn : QN),
    A ql qm qn
      = ∑ ql', ∑ qm', ∑ qn', (ρl U) ql ql' * star (ρm U) qm' qm *
          star (ρn U) qn' qn * A ql' qm' qn'

/-- Moves the innermost of three finite complex sums to the outside while preserving the other
index order. -/
private lemma sum_comm_three {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-- Moves the innermost of four finite complex sums to the outside while preserving the other
index order. -/
private lemma sum_comm_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  rw [Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-- A covariant tensor operator yields an invariant associated tensor when each `ρn U` times its
adjoint is the identity. See [Bacon et al., 2005, Theorem 1
(Wigner-Eckart)][BaconChuangHarrow2005]. -/
theorem assocTensor_invariant
    (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ) (ρl : G → Matrix QL QL ℂ)
    (T : QN → Matrix QL QM ℂ) (hT : IsTensorOperator ρm ρn ρl T)
    (hn : ∀ U : G, ρn U * star (ρn U) = 1) :
    IsInvariantOperator ρm ρn ρl (assocTensor T) := by
  intro U ql qm qn
  have hnentry : ∀ a b : QN,
      (∑ qn', (ρn U) a qn' * star (ρn U) qn' b) = if a = b then 1 else 0 := by
    intro a b
    have h := congrArg (fun M : Matrix QN QN ℂ => M a b) (hn U)
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  have hTred : ∀ qn' : QN,
      (∑ ql', ∑ qm', (ρl U) ql ql' * star (ρm U) qm' qm * T qn' ql' qm')
        = ∑ qn'', (ρn U) qn'' qn' * T qn'' ql qm := by
    intro qn'
    have h1 : (∑ ql', ∑ qm', (ρl U) ql ql' * star (ρm U) qm' qm * T qn' ql' qm')
        = ∑ ql', ∑ qm', (ρl U) ql ql' * T qn' ql' qm' * star (ρm U) qm' qm := by
      refine Finset.sum_congr rfl (fun ql' _ => Finset.sum_congr rfl (fun qm' _ => ?_))
      ring
    rw [h1]
    exact hT U qn' ql qm
  have hperm :
      (∑ ql', ∑ qm', ∑ qn', (ρl U) ql ql' * star (ρm U) qm' qm *
          star (ρn U) qn' qn * T qn' ql' qm')
        = ∑ qn', star (ρn U) qn' qn *
            (∑ ql', ∑ qm', (ρl U) ql ql' * star (ρm U) qm' qm * T qn' ql' qm') := by
    rw [sum_comm_three]
    refine Finset.sum_congr rfl (fun qn' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ql' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun qm' _ => ?_)
    ring
  have hstep2 :
      (∑ qn', star (ρn U) qn' qn *
          (∑ ql', ∑ qm', (ρl U) ql ql' * star (ρm U) qm' qm * T qn' ql' qm'))
        = ∑ qn', star (ρn U) qn' qn * ∑ qn'', (ρn U) qn'' qn' * T qn'' ql qm := by
    refine Finset.sum_congr rfl (fun qn' _ => ?_)
    rw [hTred qn']
  have hstep3 :
      (∑ qn', star (ρn U) qn' qn * ∑ qn'', (ρn U) qn'' qn' * T qn'' ql qm)
        = ∑ qn'', (∑ qn', (ρn U) qn'' qn' * star (ρn U) qn' qn) *
            T qn'' ql qm := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun qn'' _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun qn' _ => ?_)
    ring
  have hstep4 :
      (∑ qn'', (∑ qn', (ρn U) qn'' qn' * star (ρn U) qn' qn) * T qn'' ql qm)
        = T qn ql qm := by
    rw [Finset.sum_congr rfl (fun qn'' _ => by rw [hnentry qn'' qn])]
    simp
  simp only [assocTensor]
  exact (hperm.trans (hstep2.trans (hstep3.trans hstep4))).symm

/-- The complex submodule of tensors satisfying `IsInvariantOperator` for the three matrix
actions. See [Bacon et al., 2005, Theorem 1 (Wigner-Eckart)][BaconChuangHarrow2005]. -/
def invariantSubmodule (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ)
    (ρl : G → Matrix QL QL ℂ) : Submodule ℂ (QL → QM → QN → ℂ) where
  carrier := {A | IsInvariantOperator ρm ρn ρl A}
  zero_mem' := by
    intro U ql qm qn
    simp
  add_mem' := by
    intro A B hA hB U ql qm qn
    simp only [Set.mem_setOf_eq, IsInvariantOperator] at hA hB
    simp only [Pi.add_apply]
    rw [hA U ql qm qn, hB U ql qm qn]
    simp only [mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    intro c A hA U ql qm qn
    simp only [Set.mem_setOf_eq, IsInvariantOperator] at hA ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hA U ql qm qn]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ql' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun qm' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun qn' _ => ?_)
    ring

/-- Every invariant tensor is a finite linear combination of the specified tensor family. -/
def SpansInvariant (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ)
    (ρl : G → Matrix QL QL ℂ) {Alpha : Type*}
    (B : Alpha → QL → QM → QN → ℂ) [Fintype Alpha] : Prop :=
  ∀ A : QL → QM → QN → ℂ, IsInvariantOperator ρm ρn ρl A →
    ∃ c : Alpha → ℂ, ∀ (ql : QL) (qm : QM) (qn : QN),
      A ql qm qn = ∑ α, c α * B α ql qm qn

omit [DecidableEq QN] in

/-- There is a spanning tensor family indexed by the finite dimension of the invariant
submodule. See [Bacon et al., 2005, Theorem 1 (Wigner-Eckart)][BaconChuangHarrow2005]. -/
theorem exists_spanning_invariant
    (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ) (ρl : G → Matrix QL QL ℂ) :
    ∃ B : Fin (Module.finrank ℂ (invariantSubmodule ρm ρn ρl)) →
        (QL → QM → QN → ℂ),
      SpansInvariant ρm ρn ρl B := by
  classical
  let W := invariantSubmodule ρm ρn ρl
  let b := Module.finBasis ℂ W
  refine ⟨fun i => ((b i : W) : QL → QM → QN → ℂ), ?_⟩
  intro A hA
  refine ⟨fun i => (b.repr ⟨A, hA⟩) i, ?_⟩
  intro ql qm qn
  have h := Module.Basis.sum_repr b ⟨A, hA⟩
  have h' : (∑ i, (b.repr ⟨A, hA⟩) i • ((b i : W) : QL → QM → QN → ℂ)) = A := by
    have hc := congrArg (fun z : W => (z : QL → QM → QN → ℂ)) h
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hc
  have hpt :
      (∑ i, (b.repr ⟨A, hA⟩) i * ((b i : W) : QL → QM → QN → ℂ) ql qm qn)
        = A ql qm qn := by
    have hc := congrFun (congrFun (congrFun h' ql) qm) qn
    simpa [Pi.smul_apply, smul_eq_mul] using hc
  exact hpt.symm

/-- The entry of the specified tensor family with the indices arranged as a Clebsch–Gordan
coefficient. -/
def cgCoeff {Alpha : Type*} (B : Alpha → QL → QM → QN → ℂ)
    (ql : QL) (α : Alpha) (qm : QM) (qn : QN) : ℂ :=
  B α ql qm qn

/-- Under covariance and right-unitarity of `ρn`, each entry of `T` expands in a specified
invariant-spanning family with reduced coefficients. See [BaconChuangHarrow2005] for the
mathematical setting. -/
theorem source_wigner_eckart
    (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ) (ρl : G → Matrix QL QL ℂ)
    (T : QN → Matrix QL QM ℂ) {Alpha : Type*} [Fintype Alpha]
    (B : Alpha → QL → QM → QN → ℂ)
    (hT : IsTensorOperator ρm ρn ρl T)
    (hn : ∀ U : G, ρn U * star (ρn U) = 1)
    (hspan : SpansInvariant ρm ρn ρl B) :
    ∃ Tred : Alpha → ℂ, ∀ (ql : QL) (qm : QM) (qn : QN),
      T qn ql qm = ∑ α, Tred α * cgCoeff B ql α qm qn := by
  obtain ⟨c, hc⟩ := hspan (assocTensor T) (assocTensor_invariant ρm ρn ρl T hT hn)
  refine ⟨c, fun ql qm qn => ?_⟩
  simpa only [cgCoeff, assocTensor] using hc ql qm qn

/-- Under covariance and right-unitarity of `ρn`, there exist a finite invariant-spanning family
and reduced coefficients giving the Wigner–Eckart expansion. See [Bacon et al., 2005,
Theorem 1 (Wigner-Eckart)][BaconChuangHarrow2005]. -/
theorem source_wigner_eckart_unconditional
    (ρm : G → Matrix QM QM ℂ) (ρn : G → Matrix QN QN ℂ) (ρl : G → Matrix QL QL ℂ)
    (T : QN → Matrix QL QM ℂ)
    (hT : IsTensorOperator ρm ρn ρl T)
    (hn : ∀ U : G, ρn U * star (ρn U) = 1) :
    ∃ B : Fin (Module.finrank ℂ (invariantSubmodule ρm ρn ρl)) →
        (QL → QM → QN → ℂ),
      SpansInvariant ρm ρn ρl B ∧
      ∃ Tred : Fin (Module.finrank ℂ (invariantSubmodule ρm ρn ρl)) → ℂ,
        ∀ (ql : QL) (qm : QM) (qn : QN),
          T qn ql qm = ∑ α, Tred α * cgCoeff B ql α qm qn := by
  obtain ⟨B, hB⟩ := exists_spanning_invariant ρm ρn ρl
  obtain ⟨Tred, hTred⟩ := source_wigner_eckart ρm ρn ρl T B hT hn hB
  exact ⟨B, hB, Tred, hTred⟩

end Qatlib.Papers.SchurTrans06.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Prod.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Volume-preserving coordinate shears on L2

`coordinateShift` translates one coordinate of real three-dimensional space by a measurable
function of the other two. The measurable equivalence `coordinateEquiv` preserves volume, and
`control` specializes the shift to a polynomial in another coordinate.

`pullbackEquiv` transports a measure-preserving measurable equivalence to a complex L2 isometry
equivalence; `shiftL2` applies this to coordinate shears. Such operations occur in the
continuous-variable algorithmic setting of [ArrazolaEtAl2019].

## Main statements

* `coordinateShift_preserving`: Volume preservation of measurable coordinate shears.
* `coordinateShift_control`: Polynomial controlled-coordinate update.
* `shiftL2_repr`: Almost-everywhere pullback formula on L2.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.L2Dynamics.PhaseShears.Shear
/-- The two real coordinates complementary to a selected coordinate in three-dimensional space. -/
abbrev Rest := Fin 2 → ℝ
/-- Three-dimensional real coordinate space. -/
abbrev Pos := Fin 3 → ℝ

/-- Translates the final coordinate by `g` evaluated at the unchanged pair of coordinates. -/
def fiberShift (g : Rest→ℝ) (p : Rest×ℝ) : Rest×ℝ := (p.1,p.2+g p.1)

/-- The measurable equivalence given by a fiber translation, with inverse translation by `-g`. -/
def fiberEquiv (g : Rest→ℝ) (hg : Measurable g) : (Rest×ℝ) ≃ᵐ (Rest×ℝ) where
  toFun := fiberShift g
  invFun := fiberShift (fun r=>-g r)
  left_inv := by intro p;ext <;> simp [fiberShift]
  right_inv := by intro p;ext <;> simp [fiberShift]
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add (hg.comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.add ((hg.comp measurable_fst).neg))

/-- Every measurable fiber translation preserves product Lebesgue volume. -/
theorem fiberShift_preserving (g : Rest→ℝ) (hg : Measurable g) :
    MeasurePreserving (fiberShift g) (volume : Measure (Rest×ℝ)) volume := by
  exact (MeasurePreserving.id (volume : Measure Rest)).skew_product
    (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall fun r=>(measurePreserving_add_right (volume : Measure ℝ) (g r)).map_eq)

/-- The measurable equivalence separating coordinate `i` from the other two coordinates. -/
def split (i : Fin 3) : Pos ≃ᵐ Rest×ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _:Fin 3=>ℝ) i).trans (MeasurableEquiv.prodComm : (ℝ×Rest) ≃ᵐ Rest×ℝ)

/-- The first component of `split i` lists the coordinates other than `i` using `i.succAbove`. -/
theorem split_fst (i : Fin 3) (x : Pos) : (split i x).1=(fun k=>x (i.succAbove k)) := rfl

/-- The second component of `split i` is coordinate `i`. -/
theorem split_snd (i : Fin 3) (x : Pos) : (split i x).2=x i := rfl

/-- Separating a coordinate with `split` preserves Lebesgue volume. -/
theorem split_preserving (i : Fin 3) : MeasurePreserving (split i) volume volume :=
  (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure Rest))).comp
    (volume_preserving_piFinSuccAbove (fun _:Fin 3=>ℝ) i)

/-- Reassembling a split point places the supplied scalar in coordinate `i`. -/
theorem split_symm_self (i : Fin 3) (r : Rest) (a : ℝ) : (split i).symm (r,a) i=a := by
  simpa only [split_snd] using congrArg Prod.snd ((split i).apply_symm_apply (r,a))

/-- Reassembling a split point restores each complementary coordinate from `r`. -/
theorem split_symm_other (i : Fin 3) (r : Rest) (a : ℝ) (k : Fin 2) :
    (split i).symm (r,a) (i.succAbove k)=r k := by
  simpa only [split_fst] using congrArg (fun p:Rest×ℝ=>p.1 k) ((split i).apply_symm_apply (r,a))

/-- Adds a function of the complementary coordinates to coordinate `i`, keeping those
complementary coordinates fixed. -/
def coordinateShift (i : Fin 3) (g : Rest→ℝ) (x : Pos) : Pos :=
  (split i).symm (fiberShift g (split i x))

/-- The shifted coordinate equals its original value plus `g` of the complementary coordinates. -/
theorem coordinateShift_self (i : Fin 3) (g : Rest→ℝ) (x : Pos) :
    coordinateShift i g x i=x i+g (fun k=>x (i.succAbove k)) := by
  simp only [coordinateShift,fiberShift,split_symm_self,split_snd,split_fst]

/-- A coordinate shear leaves every complementary coordinate unchanged. -/
theorem coordinateShift_other (i : Fin 3) (g : Rest→ℝ) (x : Pos) (k : Fin 2) :
    coordinateShift i g x (i.succAbove k)=x (i.succAbove k) := by
  simp only [coordinateShift,fiberShift,split_symm_other,split_fst]

/-- The measurable equivalence associated with a measurable coordinate shear. -/
def coordinateEquiv (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g) : Pos ≃ᵐ Pos :=
  (split i).trans ((fiberEquiv g hg).trans (split i).symm)

/-- The coordinate measurable equivalence acts by `coordinateShift`. -/
theorem coordinateEquiv_apply (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g) (x : Pos) :
    coordinateEquiv i g hg x=coordinateShift i g x := rfl

/-- A coordinate shear with measurable control function preserves Lebesgue volume. -/
theorem coordinateShift_preserving (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g) :
    MeasurePreserving (coordinateShift i g) volume volume :=
  ((split_preserving i).symm (split i)).comp ((fiberShift_preserving g hg).comp (split_preserving i))

/-- Replacing the selected split coordinate by zero leaves all other coordinates unchanged. -/
theorem split_reset_other (i : Fin 3) (x : Pos) :
    ∀ j : Fin 3,j≠i→(split i).symm ((split i x).1,0) j=x j := by
  refine i.forall_iff_succAbove.2 ⟨?_,?_⟩
  · intro h;exact False.elim (h rfl)
  · intro k _
    rw [split_symm_other,split_fst]

/-- The polynomial control obtained by reconstructing the complementary coordinates with
coordinate `i` set to zero and taking `s` times coordinate `j` to power `d`. -/
def control (i j : Fin 3) (d : ℕ) (s : ℝ) (r : Rest) : ℝ :=
  s*((split i).symm (r,0) j)^d

/-- The polynomial control function is measurable. -/
theorem control_measurable (i j : Fin 3) (d : ℕ) (s : ℝ) : Measurable (control i j d s) :=
  (((measurable_pi_apply j).comp (split i).symm.measurable).comp
    (measurable_id.prodMk measurable_const)).pow_const d |>.const_mul s

/-- When `j ≠ i`, the polynomial control shear updates coordinate `i` to `x i + s * (x j)^d`. -/
theorem coordinateShift_control (i j : Fin 3) (h : j≠i) (d : ℕ) (s : ℝ) (x : Pos) :
    coordinateShift i (control i j d s) x=Function.update x i (x i+s*(x j)^d) := by
  apply funext
  refine i.forall_iff_succAbove.2 ⟨?_,?_⟩
  · rw [coordinateShift_self]
    simp only [control]
    rw [← split_fst,split_reset_other i x j h]
    simp
  · intro k
    rw [coordinateShift_other]
    simp [Fin.succAbove_ne]
section Native
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Pullback by a measure-preserving measurable equivalence, bundled as a complex linear
isometry equivalence on L2. -/
def pullbackEquiv (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ e he)
    (Lp.compMeasurePreservingₗ ℂ e.symm (he.symm e))
    (by
      apply LinearMap.ext
      intro ψ
      change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) ψ)=ψ
      rw [← Lp.compMeasurePreserving_comp_apply ψ (he.symm e) he]
      have hi : (e.symm:X→X) ∘ (e:X→X)=id := by funext x;exact e.symm_apply_apply x
      simp only [hi,Lp.compMeasurePreserving_id_apply])
    (by
      apply LinearMap.ext
      intro ψ
      change Lp.compMeasurePreserving e.symm (he.symm e) (Lp.compMeasurePreserving e he ψ)=ψ
      rw [← Lp.compMeasurePreserving_comp_apply ψ he (he.symm e)]
      have hi : (e:X→X) ∘ (e.symm:X→X)=id := by funext x;exact e.apply_symm_apply x
      simp only [hi,Lp.compMeasurePreserving_id_apply])

/-- The L2 pullback agrees almost everywhere with composition by the measurable equivalence. -/
theorem pullbackEquiv_repr (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (ψ : Lp ℂ 2 μ) :
    pullbackEquiv μ e he ψ =ᵐ[μ] fun x=>ψ (e x) :=
  Lp.coeFn_compMeasurePreserving ψ he
end Native

/-- The complex linear isometry equivalence on L2 induced by a measurable coordinate shear. -/
def shiftL2 (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g) :
    Lp ℂ 2 (volume : Measure Pos) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure Pos) :=
  pullbackEquiv volume (coordinateEquiv i g hg) (coordinateShift_preserving i g hg)

/-- The L2 shear agrees almost everywhere with composition by `coordinateShift`. -/
theorem shiftL2_repr (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g)
    (ψ : Lp ℂ 2 (volume : Measure Pos)) :
    shiftL2 i g hg ψ =ᵐ[volume] fun x=>ψ (coordinateShift i g x) :=
  pullbackEquiv_repr volume (coordinateEquiv i g hg) (coordinateShift_preserving i g hg) ψ
end Qatlib.Foundations.L2Dynamics.PhaseShears.Shear

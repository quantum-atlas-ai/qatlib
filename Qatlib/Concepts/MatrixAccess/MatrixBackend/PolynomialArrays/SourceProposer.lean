/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Find
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Basic
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourcePosterior
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCheckedWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDecodedCertificate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootReturnedCompleteness
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceBitPrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerList
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.Nodup
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerPolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.List.Sort
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootProjectionBudget
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Data.List.Induction
import Mathlib.Data.List.ToFinsupp
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeSourceIntegerization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRootCount
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! Numerical root production, checked factor records and complete QSP packet generation.
Canonical PolynomialArrays algorithms and verifier are imported once; only the
remaining producer namespaces from OQ #132 are defined here.
All original bounds, finite searches, guards and same-word contracts are retained. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
namespace RootYunInternal


namespace ActualYunOriginalTarget
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualYunPrimitiveContent ActualYunContentSupply ActualYunProductArrays ActualYunArrayLoop
open ActualYunContentGuard
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `original_target_preconditions` under the displayed hypotheses. -/
private theorem original_target_preconditions (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    let H := sourceIntegerComplement cs N E
    integerPoly H≠0 ∧ (integerPoly H).natDegree=2*sourceDegree cs N E ∧
      Canonical (H.map (fun z : ℤ => (z : ℚ))) := by
  let H := sourceIntegerComplement cs N E
  have hcdeg : (rootIntegerListPolynomial H).natDegree=2*sourceDegree cs N E := by
    dsimp only [H]
    rw [sourceIntegerComplement_polynomial cs N E hparity hd,
      Polynomial.natDegree_C_mul (sourceIntegerComplement_scalar_ne_zero cs N E hparity hd)]
    exact sourceF_natDegree_eq cs N E hd
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hZdeg : (integerPoly H).natDegree=2*sourceDegree cs N E := by
    rw [← Polynomial.natDegree_map_eq_of_injective hinj (integerPoly H)]
    exact hcdeg
  have hnz : integerPoly H≠0 := by
    intro hz
    rw [hz,Polynomial.natDegree_zero] at hZdeg
    omega
  have hlen : H.length=2*sourceDegree cs N E+1 := by
    dsimp only [H,sourceIntegerComplement,sourceIntegerTarget,sourceRawIntegers,sourceRationalComplement]
    simp only [List.length_map,List.length_ofFn]
    omega
  let A := H.map (fun z : ℤ => (z : ℚ))
  have hAnz : poly A≠0 := by
    dsimp only [A]
    rw [castArray_poly]
    intro hz
    apply hnz
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [Polynomial.map_zero] using hz
  have hAdeg : (poly A).natDegree=2*sourceDegree cs N E := by
    dsimp only [A]
    rw [castArray_poly,Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective,hZdeg]
  refine ⟨hnz,hZdeg,canonical_of_degree_length A hAnz ?_⟩
  dsimp only [A]
  rw [List.length_map,hlen,hAdeg]

/-- The finite construction in `SourceProposer` satisfies `original_generated_guard` under the displayed hypotheses. -/
private theorem original_generated_guard (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    let H := sourceIntegerComplement cs N E
    ∃ (out : List (List ℤ×ℕ)) (c : ℤ),
      squarefreeArrays (H.map (fun z : ℤ => (z : ℚ)))=some out ∧ c≠0 ∧
      let product := factorsProduct out [1]
      let content := (H.getD (H.length-1) 0 : ℚ)/product.getD (product.length-1) 0
      content=(c : ℚ) ∧ content.den=1 ∧
      product.map (fun v => content*v)=H.map (fun z : ℤ => (z : ℚ)) := by
  obtain ⟨hnz,hdegree,hcanonical⟩ := original_target_preconditions cs N E hparity hd
  exact generated_source_content_guard _ hnz (by rw [hdegree]; omega) hcanonical

end ActualYunOriginalTarget






namespace ActualProjectionPreparedContexts
open Polynomial ActualProjectionContexts ActualRootProjectionCap
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualYunPrimitiveContent ActualYunContentSupply ActualYunProductArrays
open ActualYunArrayLoop ActualYunArrayStep ActualYunContentGuard ActualYunOriginalTarget

/-- Construction for prepare in the source proposer model. -/
private def prepare (a : List ℤ) : Option (ℤ×List Context) :=
  (squarefreeArrays (a.map (fun z : ℤ => (z : ℚ)))).bind (fun fs =>
    let product := factorsProduct fs [1]
    let content := (a.getD (a.length-1) 0 : ℚ)/product.getD (product.length-1) 0
    if content.den≠1 ∨ product.map (fun v => content*v)≠a.map (fun z : ℤ => (z : ℚ)) then none
    else (build fs).map (fun contexts => (content.num,contexts)))

/-- The finite construction in `SourceProposer` satisfies `scale_poly` under the displayed hypotheses. -/
private theorem scale_poly (a : List ℚ) (c : ℚ) : poly (a.map (fun v => c*v))=C c*poly a := by
  ext k
  rw [ActualYunRationalArray.coeff,Polynomial.coeff_C_mul,ActualYunRationalArray.coeff]
  simpa only [mul_zero] using (List.getD_map a 0 (n:=k) (fun v => c*v))

/-- The finite construction in `SourceProposer` satisfies `source_guard_product` under the displayed hypotheses. -/
private theorem source_guard_product (a : List ℤ) (fs : List (List ℤ×ℕ)) (c : ℤ)
    (hfull : (factorsProduct fs [1]).map (fun v => (c : ℚ)*v)=a.map (fun z : ℤ => (z : ℚ))) :
    integerPoly a=C c*rawProduct fs := by
  have he := congrArg poly hfull
  rw [scale_poly,factorsProduct_poly,castArray_poly] at he
  have hone : poly [1]=1 := by rw [poly_cons,poly_nil,mul_zero,add_zero,Polynomial.C_1]
  rw [hone,one_mul] at he
  apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
  rw [Polynomial.map_mul,Polynomial.map_C]
  exact he.symm

/-- The finite construction in `SourceProposer` satisfies `prepare_success` under the displayed hypotheses. -/
private theorem prepare_success (a : List ℤ) (ha : integerPoly a≠0) (hd : 0 < (integerPoly a).natDegree)
    (hcanonical : Canonical (a.map (fun z : ℤ => (z : ℚ)))) :
    ∃ fs c contexts,squarefreeArrays (a.map (fun z : ℤ => (z : ℚ)))=some fs ∧
      prepare a=some (c,contexts) ∧ c≠0 ∧ integerPoly a=C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      ∀ ctx∈contexts,ContextGood ctx ∧ ctx.exponent ≤ (integerPoly a).natDegree ∧
        (integerPoly ctx.factor).IsPrimitive := by
  obtain ⟨fs,c,hsource,hcn,hguard⟩ := generated_source_content_guard a ha hd hcanonical
  obtain ⟨fs',_,hsource',_,_,_,hg⟩ := generated_content a ha hd
  have he : fs'=fs := Option.some.inj (hsource'.symm.trans hsource)
  subst fs'
  obtain ⟨contexts,hbuild,hmap,hctx⟩ := build_success fs (fun f hf => (hg f hf).1)
  let product := factorsProduct fs [1]
  let content := (a.getD (a.length-1) 0 : ℚ)/product.getD (product.length-1) 0
  change content=(c : ℚ) ∧ content.den=1 ∧ product.map (fun v => content*v)=a.map (fun z : ℤ => (z : ℚ)) at hguard
  have hbad : ¬(content.den≠1 ∨ product.map (fun v => content*v)≠a.map (fun z : ℤ => (z : ℚ))) := by
    rw [hguard.2.1,hguard.2.2]
    simp
  have hprep : prepare a=some (c,contexts) := by
    unfold prepare
    rw [hsource,Option.bind_some]
    change (if content.den≠1 ∨ product.map (fun v => content*v)≠a.map (fun z : ℤ => (z : ℚ)) then none
      else (build fs).map (fun cs => (content.num,cs)))=some (c,contexts)
    rw [ite_eq_right hbad,hbuild,Option.map_some,hguard.1]
    simp
  have hfull : product.map (fun v => (c : ℚ)*v)=a.map (fun z : ℤ => (z : ℚ)) := by
    simpa only [hguard.1] using hguard.2.2
  refine ⟨fs,c,contexts,hsource,hprep,hcn,source_guard_product a fs c hfull,hmap,?_⟩
  intro ctx hc
  have hf : (ctx.factor,ctx.exponent)∈fs := by rw [← hmap]; exact List.mem_map.mpr ⟨ctx,hc,rfl⟩
  exact ⟨hctx ctx hc,(hg _ hf).2⟩

/-- The finite construction in `SourceProposer` satisfies `original_prepare_success` under the displayed hypotheses. -/
private theorem original_prepare_success (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E) :
    let H := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceIntegerComplement cs N E
    ∃ fs c contexts,squarefreeArrays (H.map (fun z : ℤ => (z : ℚ)))=some fs ∧
      prepare H=some (c,contexts) ∧ c≠0 ∧ integerPoly H=C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      ∀ ctx∈contexts,ContextGood ctx ∧
        ctx.exponent ≤ 2*Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E ∧
        (integerPoly ctx.factor).IsPrimitive := by
  obtain ⟨hnz,hdeg,hcan⟩ := original_target_preconditions cs N E hparity hd
  obtain ⟨fs,c,contexts,hsource,hprep,hcn,hprod,hmap,hgood⟩ := prepare_success _ hnz (by rw [hdeg]; omega) hcan
  refine ⟨fs,c,contexts,hsource,hprep,hcn,hprod,hmap,?_⟩
  intro ctx hc
  have hh := hgood ctx hc
  rw [hdeg] at hh
  exact hh

end ActualProjectionPreparedContexts


namespace ActualProjectionOriginalRetention
open Polynomial ActualProjectionAcceptedDisks ActualProjectionContexts ActualProjectionPreparedContexts
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualRootProjectionCap
open ActualYunArrayStep ActualYunPrimitiveContent ActualYunContentSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `factor_as_ofFn` under the displayed hypotheses. -/
private theorem factor_as_ofFn (f : List ℤ×ℕ) (hf : FactorGood f) :
    ∃ (n : ℕ) (a : Fin (n+2) → ℤ),f.1=List.ofFn a ∧ a (Fin.last (n+1))≠0 ∧ (rootIntegerPolynomial a).Separable := by
  obtain ⟨hs,hd,hlen,htop,_⟩ := hf
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hl : f.1.length=n+2 := by omega
  let a : Fin (n+2) → ℤ := fun i => f.1.getD i.val 0
  have hlist : List.ofFn a=f.1 := by
    apply List.ext_getElem (by rw [List.length_ofFn]; exact hl.symm)
    intro i hi hfi
    simp only [List.getElem_ofFn]
    change f.1.getD i 0=f.1[i]
    exact List.getD_eq_getElem _ _ hfi
  have ha : a (Fin.last (n+1))≠0 := by
    change f.1.getD (n+1) 0≠0
    simpa only [hl,show n+2-1=n+1 by omega] using htop
  refine ⟨n,a,hlist.symm,ha,?_⟩
  rw [← rootIntegerListPolynomial_ofFn,hlist]
  exact hs

/-- Construction for Disk Coverage in the source proposer model. -/
private def DiskCoverage (ctx : Context) (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (ix iy : List (ℚ×ℚ)) : Prop :=
  (∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 →
    ∃ c∈retained ctx.factor (radius contexts bits gap) ix iy,
      ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ)) ∧
  (∀ c∈retained ctx.factor (radius contexts bits gap) ix iy,
    ∃ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 ∧
      ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ))

/-- The finite construction in `SourceProposer` satisfies `context_cap_coverage` under the displayed hypotheses. -/
private theorem context_cap_coverage (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) :
    ∃ fx fy ix iy,isolateAxes ctx.factor (cap contexts bits gap) fx fy=some (ix,iy) ∧
      DiskCoverage ctx contexts bits gap ix iy := by
  obtain ⟨n,a,hlist,ha,hsep⟩ := factor_as_ofFn (ctx.factor,ctx.exponent) hgood.1
  change ctx.factor=List.ofFn a at hlist
  obtain ⟨fx,fy,ix,iy,hr,hcomplete,hsound⟩ := actual_cap_disks contexts bits gap hg ctx hctx n a ha hlist hsep
  refine ⟨fx,fy,ix,iy,?_,?_⟩
  · simpa only [← hlist] using hr
  · change (∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 → _) ∧ _
    rw [hlist,rootIntegerListPolynomial_ofFn]
    exact ⟨hcomplete,hsound⟩

/-- The finite construction in `SourceProposer` satisfies `raw_product_root` under the displayed hypotheses. -/
private theorem raw_product_root (fs : List (List ℤ×ℕ)) (z : ℂ)
    (hz : ((rawProduct fs).map (Int.castRingHom ℂ)).eval z=0) :
    ∃ f∈fs,(rootIntegerListPolynomial f.1).eval z=0 := by
  induction fs with
  | nil => simp [rawProduct] at hz
  | cons f fs ih =>
    rw [rawProduct,List.map_cons,List.prod_cons,Polynomial.map_mul,Polynomial.eval_mul] at hz
    rcases mul_eq_zero.mp hz with hf|hfs
    · refine ⟨f,by simp,?_⟩
      rw [Polynomial.map_pow,Polynomial.eval_pow] at hf
      exact eq_zero_of_pow_eq_zero hf
    · obtain ⟨g,hg,hgz⟩ := ih hfs
      exact ⟨g,by simp only [List.mem_cons]; exact Or.inr hg,hgz⟩

/-- The finite construction in `SourceProposer` satisfies `original_root_context` under the displayed hypotheses. -/
private theorem original_root_context (H : List ℤ) (fs : List (List ℤ×ℕ)) (c : ℤ) (contexts : List Context)
    (hc : c≠0) (hprod : integerPoly H=C c*rawProduct fs)
    (hmap : contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs)
    (z : ℂ) (hz : (rootIntegerListPolynomial H).eval z=0) :
    ∃ ctx∈contexts,(rootIntegerListPolynomial ctx.factor).eval z=0 := by
  change ((integerPoly H).map (Int.castRingHom ℂ)).eval z=0 at hz
  rw [hprod,Polynomial.map_mul,Polynomial.map_C,Polynomial.eval_mul,Polynomial.eval_C] at hz
  have hcc : (c : ℂ)≠0 := by exact_mod_cast hc
  have hp := (mul_eq_zero.mp hz).resolve_left hcc
  obtain ⟨f,hf,hfz⟩ := raw_product_root fs z hp
  have hm : f∈contexts.map (fun ctx => (ctx.factor,ctx.exponent)) := by rw [hmap]; exact hf
  obtain ⟨ctx,hctx,he⟩ := List.mem_map.mp hm
  have hfactor : ctx.factor=f.1 := congrArg Prod.fst he
  exact ⟨ctx,hctx,by rw [hfactor]; exact hfz⟩

/-- The finite construction in `SourceProposer` satisfies `original_prepared_coverage` under the displayed hypotheses. -/
private theorem original_prepared_coverage (cs : List ℚ) (N : ℕ) (E : ℚ) (bits : ℕ) (gap : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) (hg : 0 < gap) :
    let H := sourceIntegerComplement cs N E
    ∃ fs c contexts,prepare H=some (c,contexts) ∧ c≠0 ∧ integerPoly H=C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      (∀ ctx∈contexts,ContextGood ctx ∧
        ∃ fx fy ix iy,isolateAxes ctx.factor (cap contexts bits gap) fx fy=some (ix,iy) ∧
          DiskCoverage ctx contexts bits gap ix iy) ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ ctx∈contexts,∃ fx fy ix iy,isolateAxes ctx.factor (cap contexts bits gap) fx fy=some (ix,iy) ∧
          ∃ center∈retained ctx.factor (radius contexts bits gap) ix iy,
            ‖z-rootRationalCoordinate center‖ ≤ (radius contexts bits gap : ℝ)) := by
  obtain ⟨fs,c,contexts,_,hp,hcn,hprod,hmap,hgood⟩ := original_prepare_success cs N E hparity hd
  have hall : ∀ ctx∈contexts,ContextGood ctx ∧
      ∃ fx fy ix iy,isolateAxes ctx.factor (cap contexts bits gap) fx fy=some (ix,iy) ∧
        DiskCoverage ctx contexts bits gap ix iy := by
    intro ctx hc
    exact ⟨(hgood ctx hc).1,context_cap_coverage contexts bits gap hg ctx hc (hgood ctx hc).1⟩
  refine ⟨fs,c,contexts,hp,hcn,hprod,hmap,hall,?_⟩
  intro z hz
  obtain ⟨ctx,hctx,hzctx⟩ := original_root_context _ fs c contexts hcn hprod hmap z hz
  obtain ⟨fx,fy,ix,iy,hr,hcover⟩ := (hall ctx hctx).2
  exact ⟨ctx,hctx,fx,fy,ix,iy,hr,hcover.1 z hzctx⟩

end ActualProjectionOriginalRetention

namespace ActualProjectionCapRound
open ActualProjectionOriginalRetention ActualProjectionContexts ActualProjectionPreparedContexts
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualProjectionSourcePasses
open ActualRootProjectionCap ActualYunPrimitiveContent ActualYunContentSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for factor Record in the source proposer model. -/
private def factorRecord (ctx : Context) (r : ℚ) (ix iy : List (ℚ×ℚ)) : Record :=
  ⟨ctx.factor,ctx.exponent,(retained ctx.factor r ix iy).map (fun c => (c,r))⟩

/-- Construction for round in the source proposer model. -/
private def round : List Context → ℕ → ℚ → List (ℕ×ℕ) → Option (List Record)
  | [],_,_,_ => some []
  | _::_,_,_,[] => none
  | ctx::cs,P,r,(fx,fy)::fuels =>
    (isolateAxes ctx.factor P fx fy).bind (fun pair =>
      (round cs P r fuels).map (fun records => factorRecord ctx r pair.1 pair.2::records))

/-- Construction for Record Good in the source proposer model. -/
private def RecordGood (ctx : Context) (r : ℚ) (record : Record) : Prop :=
  record.factor=ctx.factor ∧ record.exponent=ctx.exponent ∧
  (∀ d∈record.disks,d.2=r ∧ sourcePasses ctx.factor d.1 r=true ∧
    ∃ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 ∧
      ‖z-rootRationalCoordinate d.1‖ ≤ (r : ℝ)) ∧
  (∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 →
    ∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖ ≤ (d.2 : ℝ))

/-- The finite construction in `SourceProposer` satisfies `factor_record_good` under the displayed hypotheses. -/
private theorem factor_record_good (ctx : Context) (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (ix iy : List (ℚ×ℚ)) (hc : DiskCoverage ctx contexts bits gap ix iy) :
    RecordGood ctx (radius contexts bits gap) (factorRecord ctx (radius contexts bits gap) ix iy) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro d hd
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
    exact ⟨rfl,((retained_mem _ _ _ _ _).mp hc').2,hc.2 c hc'⟩
  · intro z hz
    obtain ⟨c,hc',hnear⟩ := hc.1 z hz
    exact ⟨(c,radius contexts bits gap),List.mem_map.mpr ⟨c,hc',rfl⟩,hnear⟩

/-- The finite construction in `SourceProposer` satisfies `round_success` under the displayed hypotheses. -/
private theorem round_success (todo contexts : List Context) (bits : ℕ) (gap : ℚ)
    (hc : ∀ ctx∈todo,∃ fx fy ix iy,isolateAxes ctx.factor (cap contexts bits gap) fx fy=some (ix,iy) ∧
      DiskCoverage ctx contexts bits gap ix iy) :
    ∃ fuels records,fuels.length=todo.length ∧
      round todo (cap contexts bits gap) (radius contexts bits gap) fuels=some records ∧
      List.Forall₂ (fun ctx record => RecordGood ctx (radius contexts bits gap) record) todo records := by
  induction todo with
  | nil => exact ⟨[],[],rfl,rfl,List.Forall₂.nil⟩
  | cons ctx tail ih =>
    obtain ⟨fx,fy,ix,iy,hr,hcoverage⟩ := hc ctx (by simp)
    obtain ⟨fuels,records,hlen,hrun,hrecords⟩ := ih
      (fun c hc' => hc c (by simp only [List.mem_cons]; exact Or.inr hc'))
    refine ⟨(fx,fy)::fuels,factorRecord ctx (radius contexts bits gap) ix iy::records,?_,?_,?_⟩
    · simp only [List.length_cons,hlen]
    · simp only [round,hr,Option.bind_some,hrun,Option.map_some]
    · exact List.Forall₂.cons (factor_record_good ctx contexts bits gap ix iy hcoverage) hrecords

/-- The finite construction in `SourceProposer` satisfies `record_for_context` under the displayed hypotheses. -/
private theorem record_for_context (todo : List Context) (records : List Record) (r : ℚ)
    (h : List.Forall₂ (fun ctx record => RecordGood ctx r record) todo records)
    (ctx : Context) (hc : ctx∈todo) : ∃ record∈records,RecordGood ctx r record := by
  induction h with
  | nil => cases hc
  | @cons c d cs ds hhead htail ih =>
    rcases List.mem_cons.mp hc with he|he
    · subst ctx
      exact ⟨d,by simp,hhead⟩
    · obtain ⟨record,hm,hg⟩ := ih he
      exact ⟨record,by simp only [List.mem_cons]; exact Or.inr hm,hg⟩

/-- Construction for at Cap in the source proposer model. -/
private def atCap (target : List ℤ) (bits : ℕ) (gap : ℚ) (fuels : List (ℕ×ℕ)) : Option (ℤ×List Record) :=
  (prepare target).bind (fun pair =>
    (round pair.2 (cap pair.2 bits gap) (radius pair.2 bits gap) fuels).map (fun records => (pair.1,records)))

/-- The finite construction in `SourceProposer` satisfies `original_cap_round` under the displayed hypotheses. -/
private theorem original_cap_round (cs : List ℚ) (N : ℕ) (E : ℚ) (bits : ℕ) (gap : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) (hg : 0 < gap) :
    let H := sourceIntegerComplement cs N E
    ∃ fs c contexts fuels records,prepare H=some (c,contexts) ∧
      atCap H bits gap fuels=some (c,records) ∧ fuels.length=contexts.length ∧ c≠0 ∧
      ActualYunPrimitiveContent.integerPoly H=Polynomial.C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      List.Forall₂ (fun ctx record => RecordGood ctx (radius contexts bits gap) record) contexts records ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ record∈records,∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖ ≤ (d.2 : ℝ)) := by
  obtain ⟨fs,c,contexts,hprep,hcn,hprod,hmap,hcontexts,_⟩ :=
    original_prepared_coverage cs N E bits gap hparity hd hg
  obtain ⟨fuels,records,hlen,hrun,hrecords⟩ := round_success contexts contexts bits gap
    (fun ctx hc => (hcontexts ctx hc).2)
  refine ⟨fs,c,contexts,fuels,records,hprep,?_,hlen,hcn,hprod,hmap,hrecords,?_⟩
  · simp only [atCap,hprep,Option.bind_some,hrun,Option.map_some]
  · intro z hz
    obtain ⟨ctx,hctx,hzctx⟩ := original_root_context _ fs c contexts hcn hprod hmap z hz
    obtain ⟨record,hr,hgood⟩ := record_for_context contexts records _ hrecords ctx hctx
    exact ⟨record,hr,hgood.2.2.2 z hzctx⟩

end ActualProjectionCapRound

namespace ActualProjectionStoredRound
open ActualProjectionCapRound ActualProjectionContexts ActualProjectionPreparedContexts
open ActualProjectionSturmAxes ActualRootProjectionCap ActualYunPrimitiveContent ActualYunContentSupply
open ActualSturmComputedIsolation ActualSturmArrayTools
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for stored Axes in the source proposer model. -/
private def storedAxes (ctx : Context) (P fx fy : ℕ) : Option (List (ℚ×ℚ)×List (ℚ×ℚ)) :=
  (intervals (lift ctx.xProjection) P fx).bind (fun ix =>
    (intervals (lift ctx.yProjection) P fy).map (fun iy => (ix,iy)))

/-- The finite construction in `SourceProposer` satisfies `stored_axes_eq` under the displayed hypotheses. -/
private theorem stored_axes_eq (ctx : Context) (hgood : ContextGood ctx) (P fx fy : ℕ) :
    storedAxes ctx P fx fy=isolateAxes ctx.factor P fx fy := by
  simp only [storedAxes,isolateAxes,hgood.2.1]

/-- Construction for round Stored in the source proposer model. -/
private def roundStored : List Context → ℕ → ℚ → List (ℕ×ℕ) → Option (List Record)
  | [],_,_,_ => some []
  | _::_,_,_,[] => none
  | ctx::cs,P,r,(fx,fy)::fuels =>
    (storedAxes ctx P fx fy).bind (fun pair =>
      (roundStored cs P r fuels).map (fun records => factorRecord ctx r pair.1 pair.2::records))

/-- The finite construction in `SourceProposer` satisfies `stored_round_eq` under the displayed hypotheses. -/
private theorem stored_round_eq (todo : List Context) (P : ℕ) (r : ℚ) (fuels : List (ℕ×ℕ))
    (hgood : ∀ ctx∈todo,ContextGood ctx) : roundStored todo P r fuels=round todo P r fuels := by
  induction todo generalizing fuels with
  | nil => rfl
  | cons ctx cs ih =>
    cases fuels with
    | nil => rfl
    | cons pair fuels =>
      rcases pair with ⟨fx,fy⟩
      rw [roundStored,ActualProjectionCapRound.round,stored_axes_eq ctx (hgood ctx (by simp))]
      have he := ih fuels (fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc))
      rw [he]

/-- Construction for at Cap Stored in the source proposer model. -/
private def atCapStored (target : List ℤ) (bits : ℕ) (gap : ℚ) (fuels : List (ℕ×ℕ)) : Option (ℤ×List Record) :=
  (prepare target).bind (fun pair =>
    (roundStored pair.2 (cap pair.2 bits gap) (radius pair.2 bits gap) fuels).map (fun records => (pair.1,records)))

/-- The finite construction in `SourceProposer` satisfies `original_contexts_good` under the displayed hypotheses. -/
private theorem original_contexts_good (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) (c : ℤ) (contexts : List Context)
    (hprepare : prepare (sourceIntegerComplement cs N E)=some (c,contexts)) :
    ∀ ctx∈contexts,ContextGood ctx := by
  obtain ⟨_,c',contexts',_,hprepare',_,_,_,hgood⟩ := original_prepare_success cs N E hparity hd
  have he : (c',contexts')=(c,contexts) := Option.some.inj (hprepare'.symm.trans hprepare)
  have hctx : contexts'=contexts := congrArg Prod.snd he
  subst contexts'
  exact fun ctx hc => (hgood ctx hc).1

/-- The finite construction in `SourceProposer` satisfies `source_cap_value` under the displayed hypotheses. -/
private theorem source_cap_value (target : List ℤ) (c : ℤ) (contexts : List Context)
    (hprepare : prepare target=some (c,contexts)) (hgood : ∀ ctx∈contexts,ContextGood ctx)
    (bits : ℕ) (gap : ℚ) (fuels : List (ℕ×ℕ)) :
    atCapStored target bits gap fuels=atCap target bits gap fuels := by
  simp only [atCapStored,atCap,hprepare,Option.bind_some,stored_round_eq contexts _ _ fuels hgood]

/-- The finite construction in `SourceProposer` satisfies `original_stored_cap_round` under the displayed hypotheses. -/
private theorem original_stored_cap_round (cs : List ℚ) (N : ℕ) (E : ℚ) (bits : ℕ) (gap : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) (hg : 0 < gap) :
    let H := sourceIntegerComplement cs N E
    ∃ fs c contexts fuels records,prepare H=some (c,contexts) ∧
      atCapStored H bits gap fuels=some (c,records) ∧ fuels.length=contexts.length ∧ c≠0 ∧
      ActualYunPrimitiveContent.integerPoly H=Polynomial.C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      List.Forall₂ (fun ctx record => RecordGood ctx (radius contexts bits gap) record) contexts records ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ record∈records,∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖ ≤ (d.2 : ℝ)) := by
  obtain ⟨fs,c,contexts,fuels,records,hprep,hrun,hlen,hcn,hprod,hmap,hrecords,hcover⟩ :=
    original_cap_round cs N E bits gap hparity hd hg
  refine ⟨fs,c,contexts,fuels,records,hprep,?_,hlen,hcn,hprod,hmap,hrecords,hcover⟩
  rw [source_cap_value _ c contexts hprep (original_contexts_good cs N E hparity hd c contexts hprep)]
  exact hrun

end ActualProjectionStoredRound




namespace ActualProjectionAcceptedRectangle
open Polynomial ActualProjectionCapSeparationScale ActualProjectionRealSeparation
open ActualProjectionContexts ActualProjectionOriginalRetention ActualProjectionSourcePasses
open ActualProjectionAcceptedDisks ActualRootProjectionCap ActualProjectionCartesian
open ActualSturmSourceCount ActualSturmQueueCoverage ActualSturmQueueSplit ActualSturmComputedIsolation
open ActualSturmArrayTools ActualYunRationalArray
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- Construction for Inside in the source proposer model. -/
private def Inside (px py : ℚ×ℚ) (z : ℂ) : Prop :=
  (px.1 : ℝ)<z.re ∧ z.re<(px.2 : ℝ) ∧ (py.1 : ℝ)<z.im ∧ z.im<(py.2 : ℝ)

/-- The finite construction in `SourceProposer` satisfies `interval_root` under the displayed hypotheses. -/
private theorem interval_root (S : Finset ℝ) (e : ℚ) (p : ℚ×ℚ) (hp : GoodInterval S e p) :
    ∃ x∈S,(p.1 : ℝ)<x ∧ x<(p.2 : ℝ) := by
  classical
  have hpos : 0 < (rootsIn S p.1 p.2).card := by rw [hp.2.2.2.1]; norm_num
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩

/-- The finite construction in `SourceProposer` satisfies `nearby_root_in_rectangle` under the displayed hypotheses. -/
private theorem nearby_root_in_rectangle (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx)
    (px py : ℚ×ℚ)
    (hx : GoodInterval (inputRoots (lift ctx.xProjection)) (sourceWidth (cap contexts bits gap)) px)
    (hy : GoodInterval (inputRoots (lift ctx.yProjection)) (sourceWidth (cap contexts bits gap)) py)
    (z : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0)
    (hc : ‖z-rootRationalCoordinate (midpoint px,midpoint py)‖ ≤ (radius contexts bits gap : ℝ)) : Inside px py z := by
  obtain ⟨hxc,hxn,hxd,hxcoord⟩ := hgood.2.2.1
  obtain ⟨hyc,hyn,hyd,hycoord⟩ := hgood.2.2.2
  obtain ⟨xi,hxim,hxi⟩ := interval_root _ _ px hx
  obtain ⟨yi,hyim,hyi⟩ := interval_root _ _ py hy
  let z0 : ℂ := (xi : ℂ)+Complex.I*(yi : ℂ)
  have hz0r : z0.re=xi := by simp [z0]
  have hz0i : z0.im=yi := by simp [z0]
  have hmid : ‖rootRationalCoordinate (midpoint px,midpoint py)-z0‖ ≤ (midpointError contexts bits gap : ℝ) :=
    midpoint_error px.1 px.2 py.1 py.2 (midpointError contexts bits gap) z0
      (by rw [hz0r]; exact hxi.1.le) (by rw [hz0r]; exact hxi.2.le)
      (by rw [hz0i]; exact hyi.1.le) (by rw [hz0i]; exact hyi.2.le) hx.2.2.2.2 hy.2.2.2.2
  have hnear : ‖z-z0‖ ≤ (radius contexts bits gap : ℝ)+(midpointError contexts bits gap : ℝ) := by
    calc
      _ = ‖(z-rootRationalCoordinate (midpoint px,midpoint py))+
          (rootRationalCoordinate (midpoint px,midpoint py)-z0)‖ := by congr 1; ring
      _ ≤ ‖z-rootRationalCoordinate (midpoint px,midpoint py)‖+
          ‖rootRationalCoordinate (midpoint px,midpoint py)-z0‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hc hmid
  have hxr0 : |z.re-xi| ≤ ‖z-z0‖ := by
    simpa only [Complex.sub_re,hz0r] using Complex.abs_re_le_norm (z-z0)
  have hyi0 : |z.im-yi| ≤ ‖z-z0‖ := by
    simpa only [Complex.sub_im,hz0i] using Complex.abs_im_le_norm (z-z0)
  have hxr := hxr0.trans hnear
  have hyi' := hyi0.trans hnear
  have hxeq : z.re=xi := by
    by_contra hne
    have hs := lifted_real_separated ctx.xProjection hxc hxn hxd z.re xi (hxcoord z hz)
      ((member_zero_iff _ hxn xi).mp hxim) hne
    have hr := radius_error_small contexts bits gap hg ctx hctx ctx.xProjection (Or.inl rfl)
    linarith
  have hyeq : z.im=yi := by
    by_contra hne
    have hs := lifted_real_separated ctx.yProjection hyc hyn hyd z.im yi (hycoord z hz)
      ((member_zero_iff _ hyn yi).mp hyim) hne
    have hr := radius_error_small contexts bits gap hg ctx hctx ctx.yProjection (Or.inr rfl)
    linarith
  exact ⟨by rw [hxeq]; exact hxi.1,by rw [hxeq]; exact hxi.2,
    by rw [hyeq]; exact hyi.1,by rw [hyeq]; exact hyi.2⟩

/-- The finite construction in `SourceProposer` satisfies `passing_rectangle_has_root` under the displayed hypotheses. -/
private theorem passing_rectangle_has_root (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (px py : ℚ×ℚ)
    (hx : GoodInterval (inputRoots (lift ctx.xProjection)) (sourceWidth (cap contexts bits gap)) px)
    (hy : GoodInterval (inputRoots (lift ctx.yProjection)) (sourceWidth (cap contexts bits gap)) py)
    (hp : sourcePasses ctx.factor (midpoint px,midpoint py) (radius contexts bits gap)=true) :
    ∃ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 ∧ Inside px py z := by
  obtain ⟨n,a,hlist,ha,_⟩ := factor_as_ofFn (ctx.factor,ctx.exponent) hgood.1
  change ctx.factor=List.ofFn a at hlist
  have hp' : sourcePasses (List.ofFn a) (midpoint px,midpoint py) (radius contexts bits gap)=true := by rw [← hlist]; exact hp
  obtain ⟨z,hz,hnear⟩ := source_passes_disk n a ha _ _ (cap_radius_budgets contexts bits gap hg).1 hp'
  have hzf : (rootIntegerListPolynomial ctx.factor).eval z=0 := by rw [hlist,rootIntegerListPolynomial_ofFn]; exact hz
  exact ⟨z,hzf,nearby_root_in_rectangle contexts bits gap hg ctx hctx hgood px py hx hy z hzf hnear⟩

/-- The finite construction in `SourceProposer` satisfies `inside_rectangle_passes` under the displayed hypotheses. -/
private theorem inside_rectangle_passes (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (px py : ℚ×ℚ)
    (hx : GoodInterval (inputRoots (lift ctx.xProjection)) (sourceWidth (cap contexts bits gap)) px)
    (hy : GoodInterval (inputRoots (lift ctx.yProjection)) (sourceWidth (cap contexts bits gap)) py)
    (z : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0) (hi : Inside px py z) :
    sourcePasses ctx.factor (midpoint px,midpoint py) (radius contexts bits gap)=true := by
  obtain ⟨n,a,hlist,ha,hsep⟩ := factor_as_ofFn (ctx.factor,ctx.exponent) hgood.1
  change ctx.factor=List.ofFn a at hlist
  have hnear := midpoint_error px.1 px.2 py.1 py.2 (midpointError contexts bits gap) z
    hi.1.le hi.2.1.le hi.2.2.1.le hi.2.2.2.le hx.2.2.2.2 hy.2.2.2.2
  have hzf : (rootIntegerPolynomial a).eval z=0 := by
    rw [← rootIntegerListPolynomial_ofFn,← hlist]
    exact hz
  obtain ⟨hb,hl⟩ := ActualRootAnalyticSupply.cap_horner_without_analytic_answers
    contexts bits gap hg ctx hctx n a ha hlist hsep z hzf (midpoint px,midpoint py) hnear
  rw [hlist]
  exact passes_of_ofFn_bound n a ha _ _ hb hl

/-- The finite construction in `SourceProposer` satisfies `interval_root_unique` under the displayed hypotheses. -/
private theorem interval_root_unique (S : Finset ℝ) (e : ℚ) (p : ℚ×ℚ) (hp : GoodInterval S e p)
    (x y : ℝ) (hx : x∈S) (hy : y∈S)
    (hpx : (p.1 : ℝ)<x ∧ x<(p.2 : ℝ)) (hpy : (p.1 : ℝ)<y ∧ y<(p.2 : ℝ)) : x=y := by
  classical
  have hc : (rootsIn S p.1 p.2).card ≤ 1 := by rw [hp.2.2.2.1]
  exact Finset.card_le_one.mp hc x (Finset.mem_filter.mpr ⟨hx,hpx⟩) y (Finset.mem_filter.mpr ⟨hy,hpy⟩)

/-- The finite construction in `SourceProposer` satisfies `roots_same_rectangle` under the displayed hypotheses. -/
private theorem roots_same_rectangle (ctx : Context) (hgood : ContextGood ctx) (e : ℚ) (px py : ℚ×ℚ)
    (hx : GoodInterval (inputRoots (lift ctx.xProjection)) e px)
    (hy : GoodInterval (inputRoots (lift ctx.yProjection)) e py)
    (z w : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0)
    (hw : (rootIntegerListPolynomial ctx.factor).eval w=0) (hiz : Inside px py z) (hiw : Inside px py w) : z=w := by
  obtain ⟨_,hxn,_,hxcoord⟩ := hgood.2.2.1
  obtain ⟨_,hyn,_,hycoord⟩ := hgood.2.2.2
  apply Complex.ext
  · exact interval_root_unique _ e px hx z.re w.re
      ((member_zero_iff _ hxn z.re).mpr (hxcoord z hz))
      ((member_zero_iff _ hxn w.re).mpr (hxcoord w hw))
      ⟨hiz.1,hiz.2.1⟩ ⟨hiw.1,hiw.2.1⟩
  · exact interval_root_unique _ e py hy z.im w.im
      ((member_zero_iff _ hyn z.im).mpr (hycoord z hz))
      ((member_zero_iff _ hyn w.im).mpr (hycoord w hw))
      ⟨hiz.2.2.1,hiz.2.2.2⟩ ⟨hiw.2.2.1,hiw.2.2.2⟩

/-- The finite construction in `SourceProposer` satisfies `passing_rectangle_iff_unique` under the displayed hypotheses. -/
private theorem passing_rectangle_iff_unique (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (px py : ℚ×ℚ)
    (hx : GoodInterval (inputRoots (lift ctx.xProjection)) (sourceWidth (cap contexts bits gap)) px)
    (hy : GoodInterval (inputRoots (lift ctx.yProjection)) (sourceWidth (cap contexts bits gap)) py) :
    sourcePasses ctx.factor (midpoint px,midpoint py) (radius contexts bits gap)=true ↔
      ∃! z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 ∧ Inside px py z := by
  constructor
  · intro hp
    obtain ⟨z,hz,hi⟩ := passing_rectangle_has_root contexts bits gap hg ctx hctx hgood px py hx hy hp
    refine ⟨z,⟨hz,hi⟩,?_⟩
    intro w hw
    exact roots_same_rectangle ctx hgood _ px py hx hy w z hw.1 hz hw.2 hi
  · rintro ⟨z,⟨hz,hi⟩,_⟩
    exact inside_rectangle_passes contexts bits gap hg ctx hctx hgood px py hx hy z hz hi

end ActualProjectionAcceptedRectangle

namespace ActualProjectionIntervalIdentity
open ActualProjectionCartesian ActualProjectionCapRetention ActualSturmQueueGeometry

/-- The finite construction in `SourceProposer` satisfies `apart_no_shared` under the displayed hypotheses. -/
private theorem apart_no_shared (p q : ℚ×ℚ) (h : Apart p q) (x : ℝ)
    (hp : (p.1 : ℝ)<x ∧ x<(p.2 : ℝ)) (hq : (q.1 : ℝ)<x ∧ x<(q.2 : ℝ)) : False := by
  rcases h with h|h
  · have hh : (p.2 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast h
    linarith [hp.2,hq.1]
  · have hh : (q.2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast h
    linarith [hq.2,hp.1]

/-- The finite construction in `SourceProposer` satisfies `same_interval` under the displayed hypotheses. -/
private theorem same_interval (ps : List (ℚ×ℚ)) (ha : ps.Pairwise Apart) (p q : ℚ×ℚ)
    (hp : p∈ps) (hq : q∈ps) (x : ℝ)
    (hpx : (p.1 : ℝ)<x ∧ x<(p.2 : ℝ)) (hqx : (q.1 : ℝ)<x ∧ x<(q.2 : ℝ)) : p=q := by
  induction ps generalizing p q with
  | nil => cases hp
  | cons a as ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp ha
    rcases List.mem_cons.mp hp with he|hp
    · subst p
      rcases List.mem_cons.mp hq with he|hq
      · exact he.symm
      · exact (apart_no_shared a q (hhead q hq) x hpx hqx).elim
    · rcases List.mem_cons.mp hq with he|hq
      · subst q
        exact (apart_no_shared a p (hhead p hp) x hqx hpx).elim
      · exact ih htail p q hp hq hpx hqx

/-- The finite construction in `SourceProposer` satisfies `intervals_nodup` under the displayed hypotheses. -/
private theorem intervals_nodup (ps : List (ℚ×ℚ)) (ha : ps.Pairwise Apart)
    (hpos : ∀ p∈ps,p.1 < p.2) : ps.Nodup := by
  induction ps with
  | nil => exact List.nodup_nil
  | cons p ps ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp ha
    apply List.nodup_cons.mpr
    constructor
    · intro hp
      rcases hhead p hp with h|h <;> exact (not_le_of_gt (hpos p (by simp))) h
    · exact ih htail (fun q hq => hpos q (by simp only [List.mem_cons]; exact Or.inr hq))

/-- The finite construction in `SourceProposer` satisfies `midpoint_inside` under the displayed hypotheses. -/
private theorem midpoint_inside (p : ℚ×ℚ) (hp : p.1 < p.2) :
    (p.1 : ℝ)<(midpoint p : ℝ) ∧ (midpoint p : ℝ)<(p.2 : ℝ) := by
  have hR : (p.1 : ℝ)<(p.2 : ℝ) := by exact_mod_cast hp
  dsimp only [ActualProjectionCartesian.midpoint]
  push_cast
  constructor <;> linarith

/-- The finite construction in `SourceProposer` satisfies `midpoints_nodup` under the displayed hypotheses. -/
private theorem midpoints_nodup (ps : List (ℚ×ℚ)) (ha : ps.Pairwise Apart)
    (hpos : ∀ p∈ps,p.1 < p.2) : (ps.map midpoint).Nodup := by
  apply List.Nodup.map_on ?_ (intervals_nodup ps ha hpos)
  intro p hp q hq he
  apply same_interval ps ha p q hp hq (midpoint p : ℝ) (midpoint_inside p (hpos p hp))
  rw [he]
  exact midpoint_inside q (hpos q hq)

/-- The finite construction in `SourceProposer` satisfies `centers_nodup` under the displayed hypotheses. -/
private theorem centers_nodup (ix iy : List (ℚ×ℚ)) (hx : ix.Pairwise Apart) (hy : iy.Pairwise Apart)
    (hxpos : ∀ p∈ix,p.1 < p.2) (hypos : ∀ p∈iy,p.1 < p.2) : (centers ix iy).Nodup := by
  have hxn := midpoints_nodup ix hx hxpos
  have hyn := midpoints_nodup iy hy hypos
  unfold centers
  apply List.nodup_flatMap.mpr
  constructor
  · intro x _
    exact List.Nodup.map (fun a b he => (Prod.mk.inj he).2) hyn
  · apply hxn.imp
    intro x y hxy
    apply List.disjoint_left.mpr
    intro c hcx hcy
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hcx
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hcy
    have he1 : x=c.1 := congrArg Prod.fst hu
    have he2 : y=c.1 := congrArg Prod.fst hv
    exact hxy (he1.trans he2.symm)

/-- The finite construction in `SourceProposer` satisfies `retained_nodup` under the displayed hypotheses. -/
private theorem retained_nodup (cs : List ℤ) (r : ℚ) (ix iy : List (ℚ×ℚ))
    (hx : ix.Pairwise Apart) (hy : iy.Pairwise Apart)
    (hxpos : ∀ p∈ix,p.1 < p.2) (hypos : ∀ p∈iy,p.1 < p.2) : (retained cs r ix iy).Nodup :=
  (centers_nodup ix iy hx hy hxpos hypos).filter _

end ActualProjectionIntervalIdentity

namespace ActualProjectionCapRootMatching
open Polynomial ActualProjectionIntervalIdentity ActualProjectionAcceptedRectangle
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionOriginalRetention
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualProjectionProducedArrays
open ActualProjectionEntryDegrees ActualProjectionCartesian ActualProjectionSourcePasses
open ActualProjectionAcceptedDisks ActualRootProjectionCap ActualSturmQueueCoverage
open ActualSturmComputedIsolation ActualSturmArrayTools ActualYunArrayStep
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The finite construction in `SourceProposer` satisfies `stored_axes_success` under the displayed hypotheses. -/
private theorem stored_axes_success (ctx : Context) (hg : ContextGood ctx) (P : ℕ) :
    ∃ fx fy ix iy,storedAxes ctx P fx fy=some (ix,iy) ∧
      IsolationProperties ctx.factor Axis.real ctx.xProjection P ix ∧
      IsolationProperties ctx.factor Axis.imag ctx.yProjection P iy := by
  obtain ⟨fx,ix,hrx,hx⟩ := actual_axis_isolation ctx.factor Axis.real ctx.xProjection hg.2.2.1 P
  obtain ⟨fy,iy,hry,hy⟩ := actual_axis_isolation ctx.factor Axis.imag ctx.yProjection hg.2.2.2 P
  exact ⟨fx,fy,ix,iy,by simp only [storedAxes,hrx,hry,Option.bind_some,Option.map_some],hx,hy⟩

/-- The finite construction in `SourceProposer` satisfies `center_parents` under the displayed hypotheses. -/
private theorem center_parents (ix iy : List (ℚ×ℚ)) (c : ℚ×ℚ) (hc : c∈centers ix iy) :
    ∃ px∈ix,∃ py∈iy,c=(midpoint px,midpoint py) := by
  rw [centers_rectangles] at hc
  obtain ⟨⟨px,py⟩,hr,hc⟩ := List.mem_map.mp hc
  obtain ⟨p,hp,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hr
  have hpx : p=px := congrArg Prod.fst he
  have hpy : q=py := congrArg Prod.snd he
  subst p
  subst q
  exact ⟨px,hp,py,hq,hc.symm⟩

/-- The finite construction in `SourceProposer` satisfies `root_unique_for_center` under the displayed hypotheses. -/
private theorem root_unique_for_center (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy)
    (c : ℚ×ℚ) (hc : c∈retained ctx.factor (radius contexts bits gap) ix iy) :
    ∃! z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 ∧
      ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ) := by
  obtain ⟨hcm,hpass⟩ := List.mem_filter.mp hc
  obtain ⟨px,hpx,py,hpy,he⟩ := center_parents ix iy c hcm
  subst c
  obtain ⟨n,a,hlist,ha,_⟩ := factor_as_ofFn (ctx.factor,ctx.exponent) hgood.1
  change ctx.factor=List.ofFn a at hlist
  have hp' : sourcePasses (List.ofFn a) (midpoint px,midpoint py) (radius contexts bits gap)=true := by
    rw [← hlist]; exact hpass
  obtain ⟨z,hz,hnear⟩ := source_passes_disk n a ha _ _ (cap_radius_budgets contexts bits gap hg).1 hp'
  have hzf : (rootIntegerListPolynomial ctx.factor).eval z=0 := by
    rw [hlist,rootIntegerListPolynomial_ofFn]; exact hz
  refine ⟨z,⟨hzf,hnear⟩,?_⟩
  intro w hw
  exact roots_same_rectangle ctx hgood _ px py (hx.1 px hpx) (hy.1 py hpy) w z hw.1 hzf
    (nearby_root_in_rectangle contexts bits gap hg ctx hctx hgood px py (hx.1 px hpx) (hy.1 py hpy) w hw.1 hw.2)
    (nearby_root_in_rectangle contexts bits gap hg ctx hctx hgood px py (hx.1 px hpx) (hy.1 py hpy) z hzf hnear)

/-- The finite construction in `SourceProposer` satisfies `center_unique_for_root` under the displayed hypotheses. -/
private theorem center_unique_for_root (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy)
    (c d : ℚ×ℚ) (hc : c∈retained ctx.factor (radius contexts bits gap) ix iy)
    (hd : d∈retained ctx.factor (radius contexts bits gap) ix iy)
    (z : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0)
    (hzc : ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ))
    (hzd : ‖z-rootRationalCoordinate d‖ ≤ (radius contexts bits gap : ℝ)) : c=d := by
  obtain ⟨px,hpx,py,hpy,he⟩ := center_parents ix iy c (List.mem_filter.mp hc).1
  obtain ⟨qx,hqx,qy,hqy,hf⟩ := center_parents ix iy d (List.mem_filter.mp hd).1
  subst c
  subst d
  have hi := nearby_root_in_rectangle contexts bits gap hg ctx hctx hgood px py
    (hx.1 px hpx) (hy.1 py hpy) z hz hzc
  have hj := nearby_root_in_rectangle contexts bits gap hg ctx hctx hgood qx qy
    (hx.1 qx hqx) (hy.1 qy hqy) z hz hzd
  have hxe := same_interval ix hx.2.2.1 px qx hpx hqx z.re ⟨hi.1,hi.2.1⟩ ⟨hj.1,hj.2.1⟩
  have hye := same_interval iy hy.2.2.1 py qy hpy hqy z.im ⟨hi.2.2.1,hi.2.2.2⟩ ⟨hj.2.2.1,hj.2.2.2⟩
  rw [hxe,hye]

/-- The finite construction in `SourceProposer` satisfies `root_covered` under the displayed hypotheses. -/
private theorem root_covered (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy)
    (z : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0) :
    ∃ c∈retained ctx.factor (radius contexts bits gap) ix iy,
      ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ) := by
  have hz' : (ActualProjectionBinomialEval.inputPoly ctx.factor).eval z=0 := hz
  obtain ⟨px,hpx,hxp⟩ := containing_interval ix z.re (hx.2.2.2.2 z hz')
  obtain ⟨py,hpy,hyp⟩ := containing_interval iy z.im (hy.2.2.2.2 z hz')
  have hinside : Inside px py z := ⟨hxp.1,hxp.2,hyp.1,hyp.2⟩
  refine ⟨(midpoint px,midpoint py),List.mem_filter.mpr ⟨?_,?_⟩,?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨midpoint px,List.mem_map.mpr ⟨px,hpx,rfl⟩,?_⟩
    exact List.mem_map.mpr ⟨midpoint py,List.mem_map.mpr ⟨py,hpy,rfl⟩,rfl⟩
  · exact inside_rectangle_passes contexts bits gap hg ctx hctx hgood px py (hx.1 px hpx) (hy.1 py hpy) z hz hinside
  · have he := midpoint_error px.1 px.2 py.1 py.2 (midpointError contexts bits gap) z
      hxp.1.le hxp.2.le hyp.1.le hyp.2.le (hx.1 px hpx).2.2.2.2 (hy.1 py hpy).2.2.2.2
    rw [norm_sub_rev] at he
    have hle : (midpointError contexts bits gap : ℝ) ≤ (radius contexts bits gap : ℝ) := by
      exact_mod_cast cap_midpoint_le_radius contexts bits gap hg
    exact he.trans hle

end ActualProjectionCapRootMatching

namespace ActualProjectionCapExactCount
open Polynomial ActualProjectionCapRootMatching ActualProjectionIntervalIdentity
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionOriginalRetention
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualProjectionProducedArrays
open ActualProjectionEntryDegrees ActualProjectionCartesian ActualProjectionSourcePasses
open ActualProjectionAcceptedDisks ActualRootProjectionCap ActualSturmQueueCoverage
open ActualSturmComputedIsolation ActualSturmArrayTools ActualYunArrayStep ActualProjectionCapRound
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The same emitted instruction list satisfies `retained_length` with the displayed gate and query accounting. -/
private theorem retained_length (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy) :
    (retained ctx.factor (radius contexts bits gap) ix iy).length=
      (rootIntegerListPolynomial ctx.factor).natDegree := by
  classical
  let F := rootIntegerListPolynomial ctx.factor
  let kept := retained ctx.factor (radius contexts bits gap) ix iy
  let s := kept.toFinset
  let t := F.roots.toFinset
  have hF : F≠0 := by
    intro he
    have hd := hgood.1.2.1
    change 0<F.natDegree at hd
    rw [he,Polynomial.natDegree_zero] at hd
    omega
  have hsound : ∀ c∈s,∃ z∈t,‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ) := by
    intro c hc
    obtain ⟨z,⟨hz,hn⟩,_⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy c (List.mem_toFinset.mp hc)
    exact ⟨z,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hF).mpr hz),hn⟩
  let f : ∀ c∈s,ℂ := fun c hc => Classical.choose (hsound c hc)
  have hf : ∀ c hc,f c hc∈t ∧ ‖f c hc-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ) :=
    fun c hc => Classical.choose_spec (hsound c hc)
  have hcard : s.card=t.card := by
    apply Finset.card_bij f (fun c hc => (hf c hc).1)
    · intro c hc d hd he
      have hzc : F.eval (f c hc)=0 := (Polynomial.mem_roots hF).mp (Multiset.mem_toFinset.mp (hf c hc).1)
      have hzd : ‖f c hc-rootRationalCoordinate d‖ ≤ (radius contexts bits gap : ℝ) := by
        rw [he]; exact (hf d hd).2
      exact center_unique_for_root contexts bits gap hg ctx hctx hgood ix iy hx hy c d
        (List.mem_toFinset.mp hc) (List.mem_toFinset.mp hd) (f c hc) hzc (hf c hc).2 hzd
    · intro z hz
      have hze : F.eval z=0 := (Polynomial.mem_roots hF).mp (Multiset.mem_toFinset.mp hz)
      obtain ⟨c,hc,hnear⟩ := root_covered contexts bits gap hg ctx hctx hgood ix iy hx hy z hze
      have hcs : c∈s := List.mem_toFinset.mpr hc
      refine ⟨c,hcs,?_⟩
      obtain ⟨w,_,huniq⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy c hc
      have hfe : F.eval (f c hcs)=0 := (Polynomial.mem_roots hF).mp (Multiset.mem_toFinset.mp (hf c hcs).1)
      exact (huniq _ ⟨hfe,(hf c hcs).2⟩).trans (huniq z ⟨hze,hnear⟩).symm
  have hnd : kept.Nodup := retained_nodup ctx.factor _ ix iy hx.2.2.1 hy.2.2.1
    (fun p hp => (hx.1 p hp).1) (fun p hp => (hy.1 p hp).1)
  have hsep : F.Separable := hgood.1.1
  have ht : t.card=F.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
    exact (IsAlgClosed.splits F).natDegree_eq_card_roots.symm
  exact (List.toFinset_card_of_nodup hnd).symm.trans (hcard.trans ht)

/-- The same emitted instruction list satisfies `stored_factor_record_count` with the displayed gate and query accounting. -/
private theorem stored_factor_record_count (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) :
    ∃ fx fy ix iy,storedAxes ctx (cap contexts bits gap) fx fy=some (ix,iy) ∧
      RecordGood ctx (radius contexts bits gap) (factorRecord ctx (radius contexts bits gap) ix iy) ∧
      (factorRecord ctx (radius contexts bits gap) ix iy).disks.length=
        (rootIntegerListPolynomial ctx.factor).natDegree := by
  obtain ⟨fx,fy,ix,iy,hr,hx,hy⟩ := stored_axes_success ctx hgood (cap contexts bits gap)
  refine ⟨fx,fy,ix,iy,hr,factor_record_good ctx contexts bits gap ix iy ⟨?_,?_⟩,?_⟩
  · exact root_covered contexts bits gap hg ctx hctx hgood ix iy hx hy
  · intro c hc
    obtain ⟨z,hz,_⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy c hc
    exact ⟨z,hz⟩
  · change (List.map _ (retained ctx.factor (radius contexts bits gap) ix iy)).length=_
    rw [List.length_map]
    exact retained_length contexts bits gap hg ctx hctx hgood ix iy hx hy

end ActualProjectionCapExactCount

namespace ActualProjectionCapCountRound
open Polynomial ActualProjectionCapExactCount ActualProjectionCapRound
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionPreparedContexts
open ActualProjectionOriginalRetention ActualRootProjectionCap ActualYunPrimitiveContent
open ActualYunContentSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for Count Record Good in the source proposer model. -/
private def CountRecordGood (ctx : Context) (r : ℚ) (record : Record) : Prop :=
  RecordGood ctx r record ∧ record.disks.length=(rootIntegerListPolynomial ctx.factor).natDegree

/-- The same emitted instruction list satisfies `stored_count_round_success` with the displayed gate and query accounting. -/
private theorem stored_count_round_success (todo contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (hm : ∀ ctx∈todo,ctx∈contexts) (hgood : ∀ ctx∈todo,ContextGood ctx) :
    ∃ fuels records,fuels.length=todo.length ∧
      roundStored todo (cap contexts bits gap) (radius contexts bits gap) fuels=some records ∧
      List.Forall₂ (fun ctx record => CountRecordGood ctx (radius contexts bits gap) record) todo records := by
  induction todo with
  | nil => exact ⟨[],[],rfl,rfl,List.Forall₂.nil⟩
  | cons ctx tail ih =>
    obtain ⟨fx,fy,ix,iy,hr,hrecord,hcount⟩ := stored_factor_record_count contexts bits gap hg ctx
      (hm ctx (by simp)) (hgood ctx (by simp))
    obtain ⟨fuels,records,hlen,hrun,hrecords⟩ := ih
      (fun c hc => hm c (by simp only [List.mem_cons]; exact Or.inr hc))
      (fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc))
    refine ⟨(fx,fy)::fuels,factorRecord ctx (radius contexts bits gap) ix iy::records,?_,?_,?_⟩
    · simp only [List.length_cons,hlen]
    · simp only [roundStored,hr,Option.bind_some,hrun,Option.map_some]
    · exact List.Forall₂.cons ⟨hrecord,hcount⟩ hrecords

/-- The same emitted instruction list satisfies `count_records_sound` with the displayed gate and query accounting. -/
private theorem count_records_sound (todo : List Context) (records : List Record) (r : ℚ)
    (h : List.Forall₂ (fun ctx record => CountRecordGood ctx r record) todo records) :
    List.Forall₂ (fun ctx record => RecordGood ctx r record) todo records := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead _ ih => exact List.Forall₂.cons hhead.1 ih

/-- The same emitted instruction list satisfies `original_stored_cap_exact_counts` with the displayed gate and query accounting. -/
private theorem original_stored_cap_exact_counts (cs : List ℚ) (N : ℕ) (E : ℚ) (bits : ℕ) (gap : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (hg : 0<gap) :
    let H := sourceIntegerComplement cs N E
    ∃ fs c contexts fuels records,prepare H=some (c,contexts) ∧
      atCapStored H bits gap fuels=some (c,records) ∧ fuels.length=contexts.length ∧ c≠0 ∧
      integerPoly H=C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      List.Forall₂ (fun ctx record => CountRecordGood ctx (radius contexts bits gap) record) contexts records ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ record∈records,∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖ ≤ (d.2 : ℝ)) := by
  obtain ⟨fs,c,contexts,_,hprepare,hcn,hprod,hmap,hgood⟩ := original_prepare_success cs N E hparity hd
  obtain ⟨fuels,records,hlen,hrun,hrecords⟩ := stored_count_round_success contexts contexts bits gap hg
    (fun _ hc => hc) (fun ctx hc => (hgood ctx hc).1)
  refine ⟨fs,c,contexts,fuels,records,hprepare,?_,hlen,hcn,hprod,hmap,hrecords,?_⟩
  · simp only [atCapStored,hprepare,Option.bind_some,hrun,Option.map_some]
  · intro z hz
    obtain ⟨ctx,hctx,hzctx⟩ := original_root_context _ fs c contexts hcn hprod hmap z hz
    obtain ⟨record,hr,hrecord⟩ := record_for_context contexts records _ (count_records_sound _ _ _ hrecords) ctx hctx
    exact ⟨record,hr,hrecord.2.2.2 z hzctx⟩

end ActualProjectionCapCountRound

namespace ActualProjectionCapDiskSeparation
open Polynomial ActualProjectionCapRootMatching ActualProjectionCapCountRound
open ActualProjectionCapSeparationScale ActualProjectionRealSeparation
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionOriginalRetention
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualProjectionProducedArrays
open ActualProjectionEntryDegrees ActualProjectionCartesian ActualRootProjectionCap
open ActualSturmComputedIsolation ActualSturmArrayTools
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The finite construction in `SourceProposer` satisfies `roots_far` under the displayed hypotheses. -/
private theorem roots_far (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx)
    (z w : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0)
    (hw : (rootIntegerListPolynomial ctx.factor).eval w=0) (hne : z≠w) :
    4*(radius contexts bits gap : ℝ)<‖z-w‖ := by
  have hr : (0 : ℝ)<(radius contexts bits gap : ℝ) := by
    exact_mod_cast (cap_radius_budgets contexts bits gap hg).1
  by_cases hreal : z.re=w.re
  · have himag : z.im≠w.im := fun h => hne (Complex.ext hreal h)
    obtain ⟨hcan,hn,hd,hcoord⟩ := hgood.2.2.2
    have hs := lifted_real_separated ctx.yProjection hcan hn hd z.im w.im (hcoord z hz) (hcoord w hw) himag
    have hsmall := radius_projection_small contexts bits gap ctx hctx ctx.yProjection (Or.inr rfl)
    have hR : (radius contexts bits gap : ℝ) ≤ (1/(2 : ℝ)^separationExponent ctx.yProjection)/128 := by
      simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hsmall
    have habs : |z.im-w.im| ≤ ‖z-w‖ := by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z-w)
    linarith
  · obtain ⟨hcan,hn,hd,hcoord⟩ := hgood.2.2.1
    have hs := lifted_real_separated ctx.xProjection hcan hn hd z.re w.re (hcoord z hz) (hcoord w hw) hreal
    have hsmall := radius_projection_small contexts bits gap ctx hctx ctx.xProjection (Or.inl rfl)
    have hR : (radius contexts bits gap : ℝ) ≤ (1/(2 : ℝ)^separationExponent ctx.xProjection)/128 := by
      simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hsmall
    have habs : |z.re-w.re| ≤ ‖z-w‖ := by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z-w)
    linarith

/-- The finite construction in `SourceProposer` satisfies `retained_centers_far` under the displayed hypotheses. -/
private theorem retained_centers_far (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy)
    (c d : ℚ×ℚ) (hc : c∈retained ctx.factor (radius contexts bits gap) ix iy)
    (hd : d∈retained ctx.factor (radius contexts bits gap) ix iy) (hne : c≠d) :
    2*(radius contexts bits gap : ℝ)<‖rootRationalCoordinate c-rootRationalCoordinate d‖ := by
  obtain ⟨z,⟨hz,hzc⟩,_⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy c hc
  obtain ⟨w,⟨hw,hwd⟩,_⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy d hd
  have hzw : z≠w := by
    intro he
    subst w
    exact hne (center_unique_for_root contexts bits gap hg ctx hctx hgood ix iy hx hy c d hc hd z hz hzc hwd)
  have hfar := roots_far contexts bits gap hg ctx hctx hgood z w hz hw hzw
  have hbound : ‖z-w‖ ≤ (radius contexts bits gap : ℝ)+
      ‖rootRationalCoordinate c-rootRationalCoordinate d‖+(radius contexts bits gap : ℝ) := by
    calc
      _ = ‖(z-rootRationalCoordinate c)+(rootRationalCoordinate c-rootRationalCoordinate d)+
          (rootRationalCoordinate d-w)‖ := by congr 1; ring
      _ ≤ ‖z-rootRationalCoordinate c‖+‖rootRationalCoordinate c-rootRationalCoordinate d‖+
          ‖rootRationalCoordinate d-w‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by rw [norm_sub_rev (rootRationalCoordinate d) w]; gcongr
  linarith

/-- The finite construction in `SourceProposer` satisfies `retained_squared_guard` under the displayed hypotheses. -/
private theorem retained_squared_guard (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy)
    (c d : ℚ×ℚ) (hc : c∈retained ctx.factor (radius contexts bits gap) ix iy)
    (hd : d∈retained ctx.factor (radius contexts bits gap) ix iy) (hne : c≠d) :
    (radius contexts bits gap+radius contexts bits gap)^2<(c.1-d.1)^2+(c.2-d.2)^2 := by
  have hfar := retained_centers_far contexts bits gap hg ctx hctx hgood ix iy hx hy c d hc hd hne
  have hr : (0 : ℝ)<(radius contexts bits gap : ℝ) := by
    exact_mod_cast (cap_radius_budgets contexts bits gap hg).1
  have he : rootRationalCoordinate c-rootRationalCoordinate d=rootRationalCoordinate (c.1-d.1,c.2-d.2) := by
    apply Complex.ext <;> simp [rootRationalCoordinate]
  have hs := rootRationalCoordinate_sq_norm (c.1-d.1,c.2-d.2)
  rw [he] at hfar
  have hsq : ((radius contexts bits gap : ℝ)+(radius contexts bits gap : ℝ))^2<
      (((c.1-d.1)^2+(c.2-d.2)^2 : ℚ) : ℝ) := by
    nlinarith [norm_nonneg (rootRationalCoordinate (c.1-d.1,c.2-d.2))]
  exact_mod_cast hsq

end ActualProjectionCapDiskSeparation

namespace ActualProjectionCapDiskClassification
open Polynomial ActualProjectionCapRootMatching ActualProjectionCapCountRound
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionPreparedContexts
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualProjectionProducedArrays
open ActualProjectionEntryDegrees ActualProjectionCartesian ActualRootProjectionCap
open ActualSturmComputedIsolation ActualSturmArrayTools ActualYunContentSupply ActualYunPrimitiveContent
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `classify_of_radial_gap` under the displayed hypotheses. -/
private theorem classify_of_radial_gap (c : ℚ×ℚ) (r gap : ℚ) (hr : 0<r) (hgap : 2*r<gap)
    (z : ℂ) (hz : (gap : ℝ) ≤ |‖z‖-1|) (hd : ‖z-rootRationalCoordinate c‖ ≤ (r : ℝ)) :
    rootRationalDiskClassify c r≠none := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hgapR : 2*(r : ℝ)<(gap : ℝ) := by exact_mod_cast hgap
  have hc0 := norm_nonneg (rootRationalCoordinate c)
  have hs := rootRationalCoordinate_sq_norm c
  by_cases hzi : ‖z‖ ≤ 1
  · rw [abs_of_nonpos (sub_nonpos.mpr hzi)] at hz
    have htri : ‖rootRationalCoordinate c‖ ≤ ‖z‖+‖z-rootRationalCoordinate c‖ := by
      calc
        _ = ‖z-(z-rootRationalCoordinate c)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hc : ‖rootRationalCoordinate c‖ < 1-(r : ℝ) := by linarith
    have hr1 : r<1 := by exact_mod_cast (by linarith : (r : ℝ)<1)
    have hsq : ((c.1^2+c.2^2 : ℚ) : ℝ)<(1-(r : ℝ))^2 := by nlinarith
    have hsqQ : c.1^2+c.2^2<(1-r)^2 := by exact_mod_cast hsq
    have hi : r<1 ∧ c.1^2+c.2^2<(1-r)^2 := ⟨hr1,hsqQ⟩
    simp only [rootRationalDiskClassify,ite_eq_left hi,ne_eq,reduceCtorEq,not_false_eq_true]
  · have hzo : 1<‖z‖ := lt_of_not_ge hzi
    rw [abs_of_pos (sub_pos.mpr hzo)] at hz
    have htri : ‖z‖ ≤ ‖z-rootRationalCoordinate c‖+‖rootRationalCoordinate c‖ := by
      calc
        _ = ‖(z-rootRationalCoordinate c)+rootRationalCoordinate c‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hc : 1+(r : ℝ)<‖rootRationalCoordinate c‖ := by linarith
    have hsq : (1+(r : ℝ))^2<((c.1^2+c.2^2 : ℚ) : ℝ) := by nlinarith
    have hsqQ : (1+r)^2<c.1^2+c.2^2 := by exact_mod_cast hsq
    unfold rootRationalDiskClassify
    split_ifs <;> simp_all

/-- The finite construction in `SourceProposer` satisfies `raw_product_factor_root` under the displayed hypotheses. -/
private theorem raw_product_factor_root (fs : List (List ℤ×ℕ)) (f : List ℤ×ℕ) (hf : f∈fs) (he : 0<f.2)
    (z : ℂ) (hz : (rootIntegerListPolynomial f.1).eval z=0) :
    ((rawProduct fs).map (Int.castRingHom ℂ)).eval z=0 := by
  induction fs with
  | nil => cases hf
  | cons a fs ih =>
    rw [rawProduct,List.map_cons,List.prod_cons,Polynomial.map_mul,Polynomial.eval_mul]
    rcases List.mem_cons.mp hf with ha|hf
    · subst a
      rw [Polynomial.map_pow,Polynomial.eval_pow]
      change ((rootIntegerListPolynomial f.1).eval z)^f.2*_=0
      rw [hz,zero_pow (Nat.ne_of_gt he),zero_mul]
    · change ((integerPoly a.1^a.2).map (Int.castRingHom ℂ)).eval z*
        ((rawProduct fs).map (Int.castRingHom ℂ)).eval z=0
      rw [ih hf,mul_zero]

/-- The finite construction in `SourceProposer` satisfies `factor_root_original` under the displayed hypotheses. -/
private theorem factor_root_original (H : List ℤ) (fs : List (List ℤ×ℕ)) (c : ℤ) (contexts : List Context)
    (hprod : integerPoly H=C c*rawProduct fs)
    (hmap : contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs)
    (ctx : Context) (hctx : ctx∈contexts) (he : 0<ctx.exponent)
    (z : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0) :
    (rootIntegerListPolynomial H).eval z=0 := by
  have hf : (ctx.factor,ctx.exponent)∈fs := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨ctx,hctx,rfl⟩
  change ((integerPoly H).map (Int.castRingHom ℂ)).eval z=0
  rw [hprod,Polynomial.map_mul,Polynomial.eval_mul,raw_product_factor_root fs _ hf he z hz,mul_zero]

/-- The finite construction in `SourceProposer` satisfies `original_context_radial_gap` under the displayed hypotheses. -/
private theorem original_context_radial_gap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1)
    (c : ℤ) (contexts : List Context)
    (hprepare : prepare (sourceIntegerComplement cs N E)=some (c,contexts))
    (ctx : Context) (hctx : ctx∈contexts) (z : ℂ) (hz : (rootIntegerListPolynomial ctx.factor).eval z=0) :
    (sourceGamma0 cs N E : ℝ) ≤ |‖z‖-1| := by
  obtain ⟨fs,c',contexts',_,hp,_,hprod,hmap,hgood⟩ := original_prepare_success cs N E hparity hd
  have heq : (c',contexts')=(c,contexts) := Option.some.inj (hp.symm.trans hprepare)
  have hce : c'=c := congrArg Prod.fst heq
  have hcontextse : contexts'=contexts := congrArg Prod.snd heq
  subst c'
  subst contexts'
  have hexp : 0<ctx.exponent := (hgood ctx hctx).1.1.2.2.2.2
  exact sourceIntegerComplement_all_roots_gap cs N E hE htail hparity hd hnorm z
    (factor_root_original _ fs c contexts hprod hmap ctx hctx hexp z hz)

/-- The finite construction in `SourceProposer` satisfies `original_retained_classified` under the displayed hypotheses. -/
private theorem original_retained_classified (cs : List ℚ) (N : ℕ) (E : ℚ) (bits : ℕ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1)
    (content : ℤ) (contexts : List Context)
    (hprepare : prepare (sourceIntegerComplement cs N E)=some (content,contexts))
    (ctx : Context) (hctx : ctx∈contexts) (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits (sourceGamma0 cs N E)) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits (sourceGamma0 cs N E)) iy)
    (c : ℚ×ℚ) (hc : c∈retained ctx.factor (radius contexts bits (sourceGamma0 cs N E)) ix iy) :
    rootRationalDiskClassify c (radius contexts bits (sourceGamma0 cs N E))≠none := by
  have hg := sourceGamma0_pos cs N E hE hd
  have hgood := original_contexts_good cs N E hparity hd content contexts hprepare ctx hctx
  obtain ⟨z,⟨hz,hnear⟩,_⟩ := root_unique_for_center contexts bits _ hg ctx hctx hgood ix iy hx hy c hc
  have hbud := cap_radius_budgets contexts bits (sourceGamma0 cs N E) hg
  have hsmall : 2*radius contexts bits (sourceGamma0 cs N E)<sourceGamma0 cs N E := by linarith [hbud.2.2.2]
  exact classify_of_radial_gap c _ _ hbud.1 hsmall z
    (original_context_radial_gap cs N E hE htail hparity hd hnorm content contexts hprepare ctx hctx z hz) hnear

end ActualProjectionCapDiskClassification

namespace ActualProjectionCapGuardRound
open Polynomial ActualProjectionCapRootMatching ActualProjectionCapExactCount
open ActualProjectionCapCountRound ActualProjectionCapDiskSeparation ActualProjectionCapDiskClassification
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionPreparedContexts
open ActualProjectionCapRetention ActualProjectionSturmAxes ActualProjectionProducedArrays
open ActualProjectionEntryDegrees ActualProjectionCartesian ActualRootProjectionCap
open ActualSturmComputedIsolation ActualSturmArrayTools ActualProjectionCapRound
open ActualProjectionOriginalRetention ActualYunContentSupply ActualYunPrimitiveContent
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for Guard Record Good in the source proposer model. -/
private def GuardRecordGood (ctx : Context) (r eta : ℚ) (record : Record) : Prop :=
  CountRecordGood ctx r record ∧ record.disks.Nodup ∧
    (∀ d∈record.disks,∀ e∈record.disks,d≠e →
      (d.2+e.2)^2<(d.1.1-e.1.1)^2+(d.1.2-e.1.2)^2) ∧
    (∀ d∈record.disks,rootRationalDiskClassify d.1 d.2≠none) ∧
    (∀ d∈record.disks,d.2+|(rootGridPoint d.1 (eta/16)).1-d.1.1|+
      |(rootGridPoint d.1 (eta/16)).2-d.1.2|≤eta)

/-- The finite construction in `SourceProposer` satisfies `cap_grid_budget` under the displayed hypotheses. -/
private theorem cap_grid_budget (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap) (c : ℚ×ℚ) :
    radius contexts bits gap+|(rootGridPoint c (sourceWidth bits/16)).1-c.1|+
      |(rootGridPoint c (sourceWidth bits/16)).2-c.2|≤ sourceWidth bits := by
  have he := sourceWidth_positive bits
  have hx := (rootGridTruncate_spec c.1 (sourceWidth bits/16) (by positivity)).2
  have hy := (rootGridTruncate_spec c.2 (sourceWidth bits/16) (by positivity)).2
  have hr : radius contexts bits gap≤ sourceWidth bits/256 := (cap_radius_budgets contexts bits gap hg).2.2.1
  change radius contexts bits gap+|rootGridTruncate c.1 (sourceWidth bits/16)-c.1|+
    |rootGridTruncate c.2 (sourceWidth bits/16)-c.2|≤ sourceWidth bits
  linarith

/-- The finite construction in `SourceProposer` satisfies `factor_record_guards` under the displayed hypotheses. -/
private theorem factor_record_guards (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx)
    (hradial : ∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 → (gap : ℝ)≤|‖z‖-1|)
    (ix iy : List (ℚ×ℚ))
    (hx : IsolationProperties ctx.factor Axis.real ctx.xProjection (cap contexts bits gap) ix)
    (hy : IsolationProperties ctx.factor Axis.imag ctx.yProjection (cap contexts bits gap) iy) :
    GuardRecordGood ctx (radius contexts bits gap) (sourceWidth bits)
      (factorRecord ctx (radius contexts bits gap) ix iy) := by
  have hcoverage : DiskCoverage ctx contexts bits gap ix iy := by
    refine ⟨root_covered contexts bits gap hg ctx hctx hgood ix iy hx hy,?_⟩
    intro c hc
    obtain ⟨z,hz,_⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy c hc
    exact ⟨z,hz⟩
  refine ⟨⟨factor_record_good ctx contexts bits gap ix iy hcoverage,?_⟩,?_,?_,?_,?_⟩
  · change (List.map _ (retained ctx.factor (radius contexts bits gap) ix iy)).length=_
    rw [List.length_map]
    exact retained_length contexts bits gap hg ctx hctx hgood ix iy hx hy
  · exact List.Nodup.map (fun a b he => (Prod.mk.inj he).1)
      (ActualProjectionIntervalIdentity.retained_nodup ctx.factor _ ix iy hx.2.2.1 hy.2.2.1
        (fun p hp => (hx.1 p hp).1) (fun p hp => (hy.1 p hp).1))
  · intro d hd e he hne
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp he
    exact retained_squared_guard contexts bits gap hg ctx hctx hgood ix iy hx hy c c' hc hc'
      (fun h => hne (by rw [h]))
  · intro d hd
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    obtain ⟨z,⟨hz,hnear⟩,_⟩ := root_unique_for_center contexts bits gap hg ctx hctx hgood ix iy hx hy c hc
    have hb := cap_radius_budgets contexts bits gap hg
    exact classify_of_radial_gap c _ gap hb.1 (by linarith [hb.2.2.2]) z (hradial z hz) hnear
  · intro d hd
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hd
    exact cap_grid_budget contexts bits gap hg c

/-- The finite construction in `SourceProposer` satisfies `stored_guard_record_success` under the displayed hypotheses. -/
private theorem stored_guard_record_success (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (ctx : Context) (hctx : ctx∈contexts) (hgood : ContextGood ctx)
    (hradial : ∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 → (gap : ℝ)≤|‖z‖-1|) :
    ∃ fx fy ix iy,storedAxes ctx (cap contexts bits gap) fx fy=some (ix,iy) ∧
      GuardRecordGood ctx (radius contexts bits gap) (sourceWidth bits)
        (factorRecord ctx (radius contexts bits gap) ix iy) := by
  obtain ⟨fx,fy,ix,iy,hr,hx,hy⟩ := stored_axes_success ctx hgood (cap contexts bits gap)
  exact ⟨fx,fy,ix,iy,hr,factor_record_guards contexts bits gap hg ctx hctx hgood hradial ix iy hx hy⟩

/-- The finite construction in `SourceProposer` satisfies `stored_guard_round_success` under the displayed hypotheses. -/
private theorem stored_guard_round_success (todo contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0<gap)
    (hm : ∀ ctx∈todo,ctx∈contexts) (hgood : ∀ ctx∈todo,ContextGood ctx)
    (hradial : ∀ ctx∈todo,∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 → (gap : ℝ)≤|‖z‖-1|) :
    ∃ fuels records,fuels.length=todo.length ∧
      roundStored todo (cap contexts bits gap) (radius contexts bits gap) fuels=some records ∧
      List.Forall₂ (fun ctx record => GuardRecordGood ctx (radius contexts bits gap) (sourceWidth bits) record) todo records := by
  induction todo with
  | nil => exact ⟨[],[],rfl,rfl,List.Forall₂.nil⟩
  | cons ctx tail ih =>
    obtain ⟨fx,fy,ix,iy,hr,hrecord⟩ := stored_guard_record_success contexts bits gap hg ctx
      (hm ctx (by simp)) (hgood ctx (by simp)) (hradial ctx (by simp))
    obtain ⟨fuels,records,hlen,hrun,hrecords⟩ := ih
      (fun c hc => hm c (by simp only [List.mem_cons]; exact Or.inr hc))
      (fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc))
      (fun c hc => hradial c (by simp only [List.mem_cons]; exact Or.inr hc))
    refine ⟨(fx,fy)::fuels,factorRecord ctx (radius contexts bits gap) ix iy::records,?_,?_,?_⟩
    · simp only [List.length_cons,hlen]
    · simp only [roundStored,hr,Option.bind_some,hrun,Option.map_some]
    · exact List.Forall₂.cons hrecord hrecords

/-- The same emitted instruction list satisfies `guard_records_count_sound` with the displayed gate and query accounting. -/
private theorem guard_records_count_sound (todo : List Context) (records : List Record) (r eta : ℚ)
    (h : List.Forall₂ (fun ctx record => GuardRecordGood ctx r eta record) todo records) :
    List.Forall₂ (fun ctx record => CountRecordGood ctx r record) todo records := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead _ ih => exact List.Forall₂.cons hhead.1 ih

/-- The finite construction in `SourceProposer` satisfies `original_stored_cap_guards` under the displayed hypotheses. -/
private theorem original_stored_cap_guards (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1) :
    let H := sourceIntegerComplement cs N E
    ∃ fs c contexts fuels records,prepare H=some (c,contexts) ∧
      atCapStored H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,records) ∧
      fuels.length=contexts.length ∧ c≠0 ∧ integerPoly H=C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      List.Forall₂ (fun ctx record => GuardRecordGood ctx
        (radius contexts (sourceInputR cs N E) (sourceGamma0 cs N E)) (sourceInputEta cs N E) record) contexts records ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ record∈records,∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖≤(d.2 : ℝ)) := by
  obtain ⟨fs,c,contexts,_,hprepare,hcn,hprod,hmap,hgood⟩ := original_prepare_success cs N E hparity hd
  have hg := sourceGamma0_pos cs N E hE hd
  obtain ⟨fuels,records,hlen,hrun,hrecords⟩ := stored_guard_round_success contexts contexts (sourceInputR cs N E)
    (sourceGamma0 cs N E) hg (fun _ hc => hc) (fun ctx hc => (hgood ctx hc).1)
    (fun ctx hc z hz => original_context_radial_gap cs N E hE htail hparity hd hnorm c contexts hprepare ctx hc z hz)
  have he : sourceWidth (sourceInputR cs N E)=sourceInputEta cs N E := rfl
  rw [he] at hrecords
  refine ⟨fs,c,contexts,fuels,records,hprepare,?_,hlen,hcn,hprod,hmap,hrecords,?_⟩
  · simp only [atCapStored,hprepare,Option.bind_some,hrun,Option.map_some]
  · intro z hz
    obtain ⟨ctx,hctx,hzctx⟩ := original_root_context _ fs c contexts hcn hprod hmap z hz
    have hplain := count_records_sound _ _ _ (guard_records_count_sound _ _ _ _ hrecords)
    obtain ⟨record,hr,hrecord⟩ := record_for_context contexts records _ hplain ctx hctx
    exact ⟨record,hr,hrecord.2.2.2 z hzctx⟩

end ActualProjectionCapGuardRound


namespace ActualProjectionTypedRecord
open Polynomial ActualProjectionCapGuardRound ActualProjectionCapCountRound
open ActualProjectionCapRound ActualProjectionContexts ActualProjectionOriginalRetention
open ActualProjectionSourcePasses ActualProjectionSourceDerivative ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The finite construction in `SourceProposer` satisfies `pack_guards` under the displayed hypotheses. -/
private theorem pack_guards (ctx : Context) (record : Record) (r eta : ℚ) (hr : 0<r) (heta : 0<eta)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0)
    (hfactor : ctx.factor=List.ofFn a) (hexp : 0<ctx.exponent)
    (hlen : record.disks.length=n+1) (h : GuardRecordGood ctx r eta record) :
    RootIntegerFactorGuards (pack n a record) eta := by
  let d : Fin (n+1) → Disk := fun i => record.disks.getD i.val ((0,0),0)
  have hmem : ∀ i,d i∈record.disks := by
    intro i
    dsimp only [d]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hrad : ∀ i,(d i).2=r := fun i => (h.1.1.2.2.1 (d i) (hmem i)).1
  have hinj : Function.Injective d := by
    intro i j he
    have hei : record.disks[i.val]=record.disks[j.val] := by
      simpa only [d,List.getD_eq_getElem _ _ (show i.val<record.disks.length by omega),
        List.getD_eq_getElem _ _ (show j.val<record.disks.length by omega)] using he
    exact Fin.ext (h.2.1.getElem_inj_iff.mp hei)
  refine ⟨ha,?_,?_,?_,?_,?_,?_,?_⟩
  · change 0<record.exponent
    rw [h.1.1.2.1]
    exact hexp
  · intro i
    change 0<(d i).2
    rw [hrad i]
    exact hr
  · intro i
    have hp : sourcePasses (List.ofFn a) (d i).1 r=true := by
      rw [← hfactor]
      exact (h.1.1.2.2.1 (d i) (hmem i)).2.1
    have he := (passes_exact (List.ofFn a) (d i).1 r).mp hp
    simp only [horner,derivative_ofFn n a ha,List.length_ofFn,show n+2-1=n+1 by omega] at he
    change _ ∨ rootIntegerCoordinateBound (n+1) _ _ (d i).2
    rw [hrad i]
    rcases he with hz|hb
    · exact Or.inl hz
    · exact Or.inr hb.2
  · intro i j hij
    change ((d i).2+(d j).2)^2<((d i).1.1-(d j).1.1)^2+((d i).1.2-(d j).1.2)^2
    exact h.2.2.1 (d i) (hmem i) (d j) (hmem j) (fun he => hij (hinj he))
  · intro i
    exact h.2.2.2.1 (d i) (hmem i)
  · intro _ _
    exact heta
  · intro i _
    exact h.2.2.2.2 (d i) (hmem i)

/-- The finite construction in `SourceProposer` satisfies `context_record_typed` under the displayed hypotheses. -/
private theorem context_record_typed (ctx : Context) (hctx : ContextGood ctx)
    (record : Record) (r eta : ℚ) (hr : 0<r) (heta : 0<eta)
    (h : GuardRecordGood ctx r eta record) :
    ∃ (n : ℕ) (a : Fin (n+2) → ℤ),ctx.factor=List.ofFn a ∧
      (pack n a record).exponent=ctx.exponent ∧
      List.ofFn (fun i => ((pack n a record).centers i,(pack n a record).radii i))=record.disks ∧
      RootIntegerFactorGuards (pack n a record) eta := by
  obtain ⟨n,a,hfactor,ha,_⟩ := factor_as_ofFn (ctx.factor,ctx.exponent) hctx.1
  change ctx.factor=List.ofFn a at hfactor
  have hlength := congrArg List.length hfactor
  rw [List.length_ofFn] at hlength
  have hlen : record.disks.length=n+1 := by
    have hf := hctx.1.2.2.1
    have hc := h.1.2
    change record.disks.length=(rootIntegerListPolynomial ctx.factor).natDegree at hc
    change ctx.factor.length=(rootIntegerListPolynomial ctx.factor).natDegree+1 at hf
    omega
  refine ⟨n,a,hfactor,h.1.1.2.1,pack_disks n a record hlen,?_⟩
  exact pack_guards ctx record r eta hr heta n a ha hfactor hctx.1.2.2.2.2 hlen h

/-- The finite construction in `SourceProposer` satisfies `actual_record_typed` under the displayed hypotheses. -/
private theorem actual_record_typed (ctx : Context) (hctx : ContextGood ctx)
    (record : Record) (r eta : ℚ) (hr : 0<r) (heta : 0<eta)
    (h : GuardRecordGood ctx r eta record) :
    List.ofFn (packRecord record).coefficients=record.factor ∧
      (packRecord record).exponent=record.exponent ∧
      List.ofFn (fun i => ((packRecord record).centers i,(packRecord record).radii i))=record.disks ∧
      RootIntegerFactorGuards (packRecord record) eta := by
  let n := record.factor.length-2
  let a : Fin (n+2) → ℤ := fun i => record.factor.getD i.val 0
  have hfe : record.factor=ctx.factor := h.1.1.1
  have hdegree := hctx.1.2.1
  change 0<(rootIntegerListPolynomial ctx.factor).natDegree at hdegree
  have hlength := hctx.1.2.2.1
  change ctx.factor.length=(rootIntegerListPolynomial ctx.factor).natDegree+1 at hlength
  have hlenf : record.factor.length=n+2 := by
    have hl : 2≤record.factor.length := by rw [hfe]; omega
    dsimp only [n]
    omega
  have hclen : ctx.factor.length=n+2 := by rw [← hfe]; exact hlenf
  have hlist : List.ofFn a=record.factor := by
    apply List.ext_getElem (by rw [List.length_ofFn]; exact hlenf.symm)
    intro i _ hi
    simp only [List.getElem_ofFn]
    change record.factor.getD i 0=record.factor[i]
    exact List.getD_eq_getElem _ _ hi
  have hfactor : ctx.factor=List.ofFn a := hfe.symm.trans hlist.symm
  have ha : a (Fin.last (n+1))≠0 := by
    change record.factor.getD (n+1) 0≠0
    have ht := hctx.1.2.2.2.1
    change ctx.factor.getD (ctx.factor.length-1) 0≠0 at ht
    rw [← hfe,hlenf] at ht
    simpa only [show n+2-1=n+1 by omega] using ht
  have hlen : record.disks.length=n+1 := by
    have hc := h.1.2
    change record.disks.length=(rootIntegerListPolynomial ctx.factor).natDegree at hc
    omega
  refine ⟨hlist,rfl,pack_disks n a record hlen,?_⟩
  exact pack_guards ctx record r eta hr heta n a ha hfactor hctx.1.2.2.2.2 hlen h

end ActualProjectionTypedRecord

namespace ActualProjectionTypedRound
open Polynomial ActualProjectionTypedRecord ActualProjectionCapGuardRound
open ActualProjectionCapRound ActualProjectionContexts ActualProjectionStoredRound
open ActualProjectionPreparedContexts ActualRootProjectionCap
open ActualYunPrimitiveContent ActualYunContentSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for Packed Good in the source proposer model. -/
private def PackedGood (record : Record) (eta : ℚ) : Prop :=
  List.ofFn (packRecord record).coefficients=record.factor ∧
    (packRecord record).exponent=record.exponent ∧
    List.ofFn (fun i => ((packRecord record).centers i,(packRecord record).radii i))=record.disks ∧
    RootIntegerFactorGuards (packRecord record) eta

/-- The finite construction in `SourceProposer` satisfies `records_typed` under the displayed hypotheses. -/
private theorem records_typed (contexts : List Context) (records : List Record) (r eta : ℚ)
    (hr : 0<r) (heta : 0<eta) (hctx : ∀ ctx∈contexts,ContextGood ctx)
    (hrecords : List.Forall₂ (fun ctx record => GuardRecordGood ctx r eta record) contexts records) :
    (∀ record∈records,PackedGood record eta) ∧
      List.Forall₂ (fun ctx f => List.ofFn f.coefficients=ctx.factor ∧ f.exponent=ctx.exponent)
        contexts (records.map packRecord) := by
  induction hrecords with
  | nil =>
    refine ⟨?_,List.Forall₂.nil⟩
    intro record hm
    cases hm
  | @cons ctx record contexts records hhead _ ih =>
    have hp := actual_record_typed ctx (hctx ctx (by simp)) record r eta hr heta hhead
    obtain ⟨htail,hrel⟩ := ih (fun c hc => hctx c (by simp only [List.mem_cons]; exact Or.inr hc))
    constructor
    · intro d hd
      rcases List.mem_cons.mp hd with he|he
      · subst d
        exact hp
      · exact htail d he
    · exact List.Forall₂.cons ⟨hp.1.trans hhead.1.1.1,hp.2.1.trans hhead.1.1.2.1⟩ hrel

/-- Construction for at Cap Typed in the source proposer model. -/
private def atCapTyped (target : List ℤ) (bits : ℕ) (gap : ℚ) (fuels : List (ℕ×ℕ)) :
    Option (ℤ×List RootIntegerFactorData) :=
  (atCapStored target bits gap fuels).map (fun p => (p.1,p.2.map packRecord))

/-- The finite construction in `SourceProposer` satisfies `original_stored_cap_typed` under the displayed hypotheses. -/
private theorem original_stored_cap_typed (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1) :
    let H := sourceIntegerComplement cs N E
    ∃ fs c contexts fuels records,prepare H=some (c,contexts) ∧
      atCapStored H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,records) ∧
      atCapTyped H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,records.map packRecord) ∧
      c≠0 ∧ integerPoly H=C c*rawProduct fs ∧
      contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      (∀ record∈records,PackedGood record (sourceInputEta cs N E)) ∧
      List.Forall₂ (fun ctx f => List.ofFn f.coefficients=ctx.factor ∧ f.exponent=ctx.exponent)
        contexts (records.map packRecord) ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ f∈records.map packRecord,∃ i,‖z-rootRationalCoordinate (f.centers i)‖≤(f.radii i : ℝ)) := by
  obtain ⟨fs,c,contexts,fuels,records,hprepare,hrun,_,hcn,hprod,hmap,hrecords,hcover⟩ :=
    original_stored_cap_guards cs N E hE htail hparity hd hnorm
  have hr := (cap_radius_budgets contexts (sourceInputR cs N E) (sourceGamma0 cs N E)
    (sourceGamma0_pos cs N E hE hd)).1
  have heta : 0<sourceInputEta cs N E := by unfold sourceInputEta; positivity
  obtain ⟨hall,hrelation⟩ := records_typed contexts records _ _ hr heta
    (original_contexts_good cs N E hparity hd c contexts hprepare) hrecords
  refine ⟨fs,c,contexts,fuels,records,hprepare,hrun,?_,hcn,hprod,hmap,hall,hrelation,?_⟩
  · simp only [atCapTyped,hrun,Option.map_some]
  · intro z hz
    obtain ⟨record,hm,d,hdisk,hnear⟩ := hcover z hz
    have hpack := hall record hm
    rw [← hpack.2.2.1] at hdisk
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hdisk
    refine ⟨packRecord record,List.mem_map.mpr ⟨record,hm,rfl⟩,i,?_⟩
    rw [← hi] at hnear
    exact hnear

end ActualProjectionTypedRound

namespace ActualProjectionIntegerProductGuard
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- Construction for Normalized in the source proposer model. -/
private def Normalized (a : List ℤ) : Prop := a=[] ∨ ∃ b x,a=b++[x] ∧ x≠0

/-- The same emitted instruction list satisfies `normalized_length_le` with the displayed gate and query accounting. -/
private theorem normalized_length_le (a b : List ℤ) (hb : Normalized b)
    (hc : ∀ k,a.getD k 0=b.getD k 0) : b.length≤a.length := by
  rcases hb with rfl|⟨pre,x,rfl,hx⟩
  · exact Nat.zero_le _
  · by_contra hle
    have hi : a.length≤pre.length := by
      simp only [List.length_append,List.length_singleton] at hle
      omega
    have ha : a.getD pre.length 0=0 := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi,Option.getD_none]
    have hb : (pre++[x]).getD pre.length 0=x := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
    have he := hc pre.length
    rw [ha,hb] at he
    exact hx he.symm

/-- The finite construction in `SourceProposer` satisfies `normalized_ext` under the displayed hypotheses. -/
private theorem normalized_ext (a b : List ℤ) (ha : Normalized a) (hb : Normalized b)
    (hp : rootIntegerListPolynomial a=rootIntegerListPolynomial b) : a=b := by
  have hc : ∀ k,a.getD k 0=b.getD k 0 := by
    intro k
    have he := congrArg (fun p : ℂ[X] => p.coeff k) hp
    change (rootIntegerListPolynomial a).coeff k=(rootIntegerListPolynomial b).coeff k at he
    rw [rootIntegerListPolynomial_coeff,rootIntegerListPolynomial_coeff] at he
    exact_mod_cast he
  have hlen : a.length=b.length := Nat.le_antisymm
    (normalized_length_le b a ha (fun k => (hc k).symm)) (normalized_length_le a b hb hc)
  apply List.ext_getElem hlen
  intro i hi hj
  rw [← List.getD_eq_getElem a 0 hi,← List.getD_eq_getElem b 0 hj]
  exact hc i

/-- The finite construction in `SourceProposer` satisfies `canonical_normalized` under the displayed hypotheses. -/
private theorem canonical_normalized (a : List ℤ) : Normalized (rootCanonicalCoefficients a) :=
  rootCanonicalCoefficients_shape a

/-- The finite construction in `SourceProposer` satisfies `multiply_normalized` under the displayed hypotheses. -/
private theorem multiply_normalized (a b : List ℤ) : Normalized (rootIntegerListMultiply a b) := by
  cases a with
  | nil => exact Or.inl rfl
  | cons x xs =>
    cases b with
    | nil => exact Or.inl rfl
    | cons y ys => exact canonical_normalized _

/-- The finite construction in `SourceProposer` satisfies `repeat_normalized` under the displayed hypotheses. -/
private theorem repeat_normalized (factor : List ℤ) (n : ℕ) (acc : List ℤ) (ha : Normalized acc) :
    Normalized (rootIntegerListRepeatMultiply factor n acc) := by
  induction n generalizing acc with
  | zero => exact ha
  | succ n ih => exact ih _ (multiply_normalized acc factor)

/-- The finite construction in `SourceProposer` satisfies `fold_normalized` under the displayed hypotheses. -/
private theorem fold_normalized (factors : List (List ℤ×ℕ)) (acc : List ℤ) (ha : Normalized acc) :
    Normalized (factors.foldl (fun acc f => rootIntegerListRepeatMultiply f.1 f.2 acc) acc) := by
  induction factors generalizing acc with
  | nil => exact ha
  | cons f fs ih => exact ih _ (repeat_normalized f.1 f.2 acc ha)

/-- The finite construction in `SourceProposer` satisfies `product_normalized` under the displayed hypotheses. -/
private theorem product_normalized (c : ℤ) (hc : c≠0) (factors : List (List ℤ×ℕ)) :
    Normalized (rootIntegerFactorProduct c factors) := by
  apply fold_normalized factors [c]
  exact Or.inr ⟨[],c,rfl,hc⟩

/-- The finite construction in `SourceProposer` satisfies `coefficient_list_guard` under the displayed hypotheses. -/
private theorem coefficient_list_guard (H : List ℤ) (c : ℤ) (hc : c≠0) (factors : List (List ℤ×ℕ))
    (hp : rootIntegerListPolynomial H=C (c : ℂ)*
      (factors.map (fun f => (rootIntegerListPolynomial f.1)^f.2)).prod) :
    rootIntegerFactorProduct c factors=rootCanonicalCoefficients H := by
  apply normalized_ext _ _ (product_normalized c hc factors) (canonical_normalized H)
  rw [rootIntegerFactorProduct_polynomial,rootCanonicalCoefficients_polynomial]
  exact hp.symm

end ActualProjectionIntegerProductGuard

namespace ActualProjectionTypedCertificate
open Polynomial ActualProjectionIntegerProductGuard ActualProjectionTypedRecord ActualProjectionTypedRound
open ActualProjectionContexts ActualProjectionStoredRound ActualProjectionPreparedContexts ActualProjectionCapRound
open ActualYunPrimitiveContent ActualYunContentSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for factor List in the source proposer model. -/
private def factorList (fs : List RootIntegerFactorData) : List (List ℤ×ℕ) :=
  fs.map (fun f => (List.ofFn f.coefficients,f.exponent))

/-- Construction for family in the source proposer model. -/
private def family (fs : List RootIntegerFactorData) : Fin fs.length → RootIntegerFactorData := fs.get

/-- The finite construction in `SourceProposer` satisfies `raw_product_map` under the displayed hypotheses. -/
private theorem raw_product_map (fs : List (List ℤ×ℕ)) :
    (rawProduct fs).map (Int.castRingHom ℂ)=
      (fs.map (fun f => (rootIntegerListPolynomial f.1)^f.2)).prod := by
  induction fs with
  | nil => simp [rawProduct]
  | cons f fs ih =>
    change ((integerPoly f.1)^f.2*rawProduct fs).map (Int.castRingHom ℂ)=_
    rw [Polynomial.map_mul,Polynomial.map_pow,ih,List.map_cons,List.prod_cons]
    rfl

/-- The finite construction in `SourceProposer` satisfies `integer_product_guard` under the displayed hypotheses. -/
private theorem integer_product_guard (H : List ℤ) (c : ℤ) (fs : List (List ℤ×ℕ))
    (hc : c≠0) (hp : integerPoly H=C c*rawProduct fs) :
    rootIntegerFactorProduct c fs=rootCanonicalCoefficients H := by
  apply coefficient_list_guard H c hc fs
  have he := congrArg (fun p : ℤ[X] => p.map (Int.castRingHom ℂ)) hp
  change (integerPoly H).map (Int.castRingHom ℂ)=(C c*rawProduct fs).map (Int.castRingHom ℂ) at he
  rw [Polynomial.map_mul,Polynomial.map_C,raw_product_map] at he
  exact he

/-- The finite construction in `SourceProposer` satisfies `typed_factor_list` under the displayed hypotheses. -/
private theorem typed_factor_list (contexts : List ActualRootProjectionCap.Context) (fs : List RootIntegerFactorData)
    (h : List.Forall₂ (fun ctx f => List.ofFn f.coefficients=ctx.factor ∧ f.exponent=ctx.exponent) contexts fs) :
    factorList fs=contexts.map (fun ctx => (ctx.factor,ctx.exponent)) := by
  induction h with
  | nil => rfl
  | cons hhead _ ih =>
    change (List.ofFn _,_)::factorList _=(_,_)::List.map _ _
    rw [hhead.1,hhead.2,ih]

/-- The finite construction in `SourceProposer` satisfies `family_factor_list` under the displayed hypotheses. -/
private theorem family_factor_list (fs : List RootIntegerFactorData) :
    List.ofFn (fun j => (List.ofFn (family fs j).coefficients,(family fs j).exponent))=factorList fs := by
  have he := congrArg (List.map (fun f : RootIntegerFactorData => (List.ofFn f.coefficients,f.exponent))) (List.ofFn_get fs)
  simpa only [List.map_ofFn,Function.comp_def,factorList,family] using he

/-- The finite construction in `SourceProposer` satisfies `original_typed_certificate` under the displayed hypotheses. -/
private theorem original_typed_certificate (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1) :
    let H := sourceIntegerComplement cs N E
    ∃ c contexts fuels fs,prepare H=some (c,contexts) ∧
      atCapTyped H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,fs) ∧ c≠0 ∧
      rootIntegerFactorProduct c (List.ofFn (fun j =>
        (List.ofFn (family fs j).coefficients,(family fs j).exponent)))=rootCanonicalCoefficients H ∧
      (∀ j,RootIntegerFactorGuards (family fs j) (sourceInputEta cs N E)) := by
  obtain ⟨factors,c,contexts,fuels,records,hprepare,_,hrun,hcn,hprod,hmap,hall,hrelation,_⟩ :=
    original_stored_cap_typed cs N E hE htail hparity hd hnorm
  have hfs : factorList (records.map packRecord)=factors :=
    (typed_factor_list contexts _ hrelation).trans hmap
  refine ⟨c,contexts,fuels,records.map packRecord,hprepare,hrun,hcn,?_,?_⟩
  · rw [family_factor_list,hfs]
    exact integer_product_guard _ c factors hcn hprod
  · intro j
    obtain ⟨record,hm,he⟩ := List.mem_map.mp (List.get_mem (records.map packRecord) j)
    change RootIntegerFactorGuards ((records.map packRecord).get j) (sourceInputEta cs N E)
    rw [← he]
    exact (hall record hm).2.2.2

end ActualProjectionTypedCertificate

namespace ActualProjectionInsideAllocation
open Polynomial ActualProjectionTypedCertificate ActualProjectionTypedRound
open ActualProjectionPreparedContexts ActualYunOriginalTarget ActualYunPrimitiveContent
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `complete_weighted_degree` under the displayed hypotheses. -/
private theorem complete_weighted_degree (m : ℕ) (H : List ℤ) (f : Fin m → RootIntegerFactorData)
    (w : (j : Fin m) → Fin ((f j).n+1) → ℂ) (hinj : ∀ j,Function.Injective (w j))
    (hroots : (rootIntegerListPolynomial H).roots=(Finset.univ : Finset (Fin m)).val.bind
      (fun j => (f j).exponent • (Finset.univ.image (w j)).val)) :
    rootDecodedWeightedDegree f=(rootIntegerListPolynomial H).roots.card := by
  classical
  have hcardn (n : ℕ) (s : Multiset ℂ) : (n • s).card=n*s.card := by
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul,Multiset.card_add,ih]; ring
  have hcard (j : Fin m) : ((f j).exponent • (Finset.univ.image (w j)).val).card=((f j).n+1)*(f j).exponent := by
    rw [hcardn]
    change (f j).exponent*(Finset.univ.image (w j)).card=_
    rw [Finset.card_image_of_injective _ (hinj j),Finset.card_univ,Fintype.card_fin]
    exact Nat.mul_comm _ _
  rw [hroots,Multiset.card_bind,Finset.val_univ_fin]
  change ((List.finRange m).map (fun j => ((f j).n+1)*(f j).exponent)).sum=
    ((List.finRange m).map (fun j => ((f j).exponent • (Finset.univ.image (w j)).val).card)).sum
  simp only [hcard]

/-- The finite construction in `SourceProposer` satisfies `original_computed_allocation` under the displayed hypotheses. -/
private theorem original_computed_allocation (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1) :
    let H := sourceIntegerComplement cs N E
    ∃ c contexts fuels fs,prepare H=some (c,contexts) ∧
      atCapTyped H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,fs) ∧ c≠0 ∧
      rootIntegerFactorProduct c (List.ofFn (fun j =>
        (List.ofFn (family fs j).coefficients,(family fs j).exponent)))=rootCanonicalCoefficients H ∧
      (∀ j,RootIntegerFactorGuards (family fs j) (sourceInputEta cs N E)) ∧
      rootDecodedWeightedDegree (family fs)=2*sourceDegree cs N E ∧
      rootDecodedInsideCount (family fs)=sourceDegree cs N E ∧
      rootDecodedOutsideCount (family fs)=sourceDegree cs N E ∧
      (rootDecodedReturnList (family fs) (sourceInputEta cs N E)).length=sourceDegree cs N E ∧
      ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖<1) ∧
        List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
          ‖rootRationalCoordinate q-z‖≤(sourceInputEta cs N E : ℝ))
          (rootDecodedReturnList (family fs) (sourceInputEta cs N E)) zs := by
  obtain ⟨c,contexts,fuels,fs,hprepare,hrun,hcn,hguard,haccepted⟩ :=
    original_typed_certificate cs N E hE htail hparity hd hnorm
  let H := sourceIntegerComplement cs N E
  let eta := sourceInputEta cs N E
  obtain ⟨zs,hm,hpair⟩ := rootDecodedCertificate_returned fs.length H c (family fs) eta hcn hguard haccepted
  have hcard := congrArg Multiset.card hm
  change zs.length=((rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖<1)).card at hcard
  have hlen : (rootDecodedReturnList (family fs) eta).length=sourceDegree cs N E :=
    hpair.length_eq.trans (hcard.trans (sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm))
  have hin : rootDecodedInsideCount (family fs)=sourceDegree cs N E :=
    (rootDecodedReturnList_length (family fs) eta).symm.trans hlen
  obtain ⟨w,_,hinj,hroots,_,_⟩ := rootDecodedCertificate_sound fs.length H c (family fs) eta hcn hguard haccepted
  have hweighted := complete_weighted_degree fs.length H (family fs) w hinj hroots
  have hZdeg := (original_target_preconditions cs N E hparity hd).2.1
  have hCdeg : (rootIntegerListPolynomial H).natDegree=2*sourceDegree cs N E :=
    (Polynomial.natDegree_map_eq_of_injective Int.cast_injective (integerPoly H)).trans hZdeg
  have hW : rootDecodedWeightedDegree (family fs)=2*sourceDegree cs N E := by
    rw [hweighted,IsAlgClosed.card_roots_eq_natDegree,hCdeg]
  have hout : rootDecodedOutsideCount (family fs)=sourceDegree cs N E := by
    have hadd := rootDecodedCounts_add (family fs)
    omega
  exact ⟨c,contexts,fuels,fs,hprepare,hrun,hcn,hguard,haccepted,hW,hin,hout,hlen,zs,hm,hpair⟩

end ActualProjectionInsideAllocation

namespace ActualProjectionVerifierBounds
open Polynomial ActualProjectionIntegerProductGuard ActualYunOriginalTarget ActualYunPrimitiveContent
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `normalized_of_last` under the displayed hypotheses. -/
private theorem normalized_of_last (a : List ℤ) (ha : a.getD (a.length-1) 0≠0) : Normalized a := by
  induction a using List.reverseRecOn with
  | nil => simp at ha
  | append_singleton a x _ =>
    refine Or.inr ⟨a,x,rfl,?_⟩
    simpa only [List.length_append,List.length_singleton,Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] using ha

/-- The same emitted instruction list satisfies `original_canonical_length` with the displayed gate and query accounting. -/
private theorem original_canonical_length (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    let H := sourceIntegerComplement cs N E
    rootCanonicalCoefficients H=H ∧ H.length=2*sourceDegree cs N E+1 := by
  let H := sourceIntegerComplement cs N E
  obtain ⟨hZn,hZdeg,_⟩ := original_target_preconditions cs N E hparity hd
  have hCdeg : (rootIntegerListPolynomial H).natDegree=2*sourceDegree cs N E :=
    (Polynomial.natDegree_map_eq_of_injective Int.cast_injective (integerPoly H)).trans hZdeg
  have hlen : H.length=2*sourceDegree cs N E+1 := by
    dsimp only [H,sourceIntegerComplement,sourceIntegerTarget,sourceRawIntegers,sourceRationalComplement]
    simp only [List.length_map,List.length_ofFn]
    omega
  have hCn : rootIntegerListPolynomial H≠0 := by
    intro hz
    rw [hz,Polynomial.natDegree_zero] at hCdeg
    omega
  have hlast : H.getD (H.length-1) 0≠0 := by
    intro hz
    apply Polynomial.leadingCoeff_ne_zero.mpr hCn
    change (rootIntegerListPolynomial H).coeff (rootIntegerListPolynomial H).natDegree=0
    rw [rootIntegerListPolynomial_coeff,hCdeg]
    have hi : H.length-1=2*sourceDegree cs N E := by omega
    rw [hi] at hz
    rw [hz,Int.cast_zero]
  exact ⟨normalized_ext _ H (canonical_normalized H) (normalized_of_last H hlast)
    (rootCanonicalCoefficients_polynomial H),hlen⟩

/-- The estimate `source_precision_positive` retains the actual parameter, input-error and normalization budgets. -/
private theorem source_precision_positive (cs : List ℚ) (N : ℕ) (E : ℚ) : 0<sourceInputR cs N E := by
  let h := sourceGrid N (sourceInputU cs N E)
  have hh : 0<h := sourceGrid_pos _ _
  have hh1 : h≤1 := by
    dsimp only [h,sourceGrid]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hc : 0<sourceCeilLog2 (128/h) := by
    by_contra he
    have hz := Nat.eq_zero_of_not_pos he
    have he := sourceCeilLog2_envelope (128/h) (by positivity)
    rw [hz,pow_zero] at he
    have hlarge : (1 : ℚ)<128/h := (lt_div_iff₀ hh).mpr (by linarith)
    linarith
  have hmid : 0<(N+1)*sourceCeilLog2 (128/h) := Nat.mul_pos (Nat.succ_pos _) hc
  change 0<sourceRootPrecision N (sourceInputU cs N E)
  unfold sourceRootPrecision
  change 0<sourceCeilLog2 (sourceK N (sourceInputU cs N E))+
    (N+1)*sourceCeilLog2 (128/h)+_
  omega

/-- The actual finite word or frame satisfies `radius_encoding_precision` with all displayed legality, input and workspace hypotheses. -/
private theorem radius_encoding_precision (bits : ℕ) (r : ℚ) (hr : 0<r) (hb : r≤1/(2 : ℚ)^bits) :
    bits<r.den.size := by
  have hn : (1 : ℚ)≤(r.num : ℚ) := by exact_mod_cast (show (1 : ℤ)≤r.num from Rat.num_pos.mpr hr)
  have hden : (0 : ℚ)<r.den := by exact_mod_cast r.den_pos
  have hsmall : 1/(r.den : ℚ)≤r := by
    calc
      _ ≤ (r.num : ℚ)/r.den := div_le_div_of_nonneg_right hn hden.le
      _ = r := Rat.num_div_den r
  have hp := (div_le_div_iff₀ hden (by positivity : (0 : ℚ)<2^bits)).mp (hsmall.trans hb)
  have hpN : 2^bits≤r.den := by exact_mod_cast (by simpa only [one_mul] using hp : (2 : ℚ)^bits≤r.den)
  exact Nat.lt_size.mpr hpN

end ActualProjectionVerifierBounds



namespace ActualProjectionRawRecordDecode
open ActualProjectionTypedRecord ActualProjectionTypedRound ActualProjectionCapGuardRound
open ActualProjectionCapRound ActualProjectionContexts ActualProjectionIntegerProductGuard
open ActualProjectionVerifierBounds
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The finite construction in `SourceProposer` satisfies `generated_record_checks` under the displayed hypotheses. -/
private theorem generated_record_checks (ctx : ActualRootProjectionCap.Context) (hctx : ContextGood ctx)
    (record : Record) (r eta : ℚ) (h : GuardRecordGood ctx r eta record) :
    normalizeRecord record=record ∧ countCheck record=true := by
  have hfactor := h.1.1.1
  have hdeg := hctx.1.2.1
  change 0 < (rootIntegerListPolynomial ctx.factor).natDegree at hdeg
  have hlen := hctx.1.2.2.1
  change ctx.factor.length=(rootIntegerListPolynomial ctx.factor).natDegree+1 at hlen
  have hcount := h.1.2
  change record.disks.length=(rootIntegerListPolynomial ctx.factor).natDegree at hcount
  have hfactorlen : record.factor.length=ctx.factor.length := congrArg List.length hfactor
  constructor
  · have hlast : record.factor.getD (record.factor.length-1) 0≠0 := by
      rw [hfactor]
      exact hctx.1.2.2.2.1
    have hc : rootCanonicalCoefficients record.factor=record.factor :=
      normalized_ext _ _ (canonical_normalized _) (normalized_of_last _ hlast)
        (rootCanonicalCoefficients_polynomial _)
    unfold normalizeRecord
    rw [hc]
  · apply decide_eq_true
    constructor <;> omega

/-- The finite construction in `SourceProposer` satisfies `generated_list_checks` under the displayed hypotheses. -/
private theorem generated_list_checks (contexts : List ActualRootProjectionCap.Context) (records : List Record) (r eta : ℚ)
    (hctx : ∀ ctx∈contexts,ContextGood ctx)
    (h : List.Forall₂ (fun ctx record => GuardRecordGood ctx r eta record) contexts records) :
    ∀ record∈records,normalizeRecord record=record ∧ countCheck record=true := by
  induction h with
  | nil => intro record hm; cases hm
  | @cons ctx record contexts records hhead _ ih =>
    intro d hd
    rcases List.mem_cons.mp hd with he|he
    · subst d
      exact generated_record_checks ctx (hctx ctx (by simp)) record r eta hhead
    · exact ih (fun c hc => hctx c (by simp only [List.mem_cons]; exact Or.inr hc)) d he

/-- The finite construction in `SourceProposer` satisfies `decode_generated` under the displayed hypotheses. -/
private theorem decode_generated (contexts : List ActualRootProjectionCap.Context) (records : List Record) (r eta : ℚ)
    (hctx : ∀ ctx∈contexts,ContextGood ctx)
    (h : List.Forall₂ (fun ctx record => GuardRecordGood ctx r eta record) contexts records) :
    decode records=some (records.map packRecord) := by
  have hall := generated_list_checks contexts records r eta hctx h
  have hmap : records.map normalizeRecord=records := by
    calc
      _ = records.map id := by
        apply List.map_congr_left
        intro record hm
        exact (hall record hm).1
      _ = _ := List.map_id records
  have hcheck : records.all countCheck=true := List.all_eq_true.mpr (fun record hm => (hall record hm).2)
  simp only [decode,hmap,hcheck,ite_true]

end ActualProjectionRawRecordDecode

namespace ActualProjectionDecodedVerifierOriginalCap
open ActualProjectionDecodedVerifier ActualProjectionInsideAllocation ActualProjectionTypedRound
open ActualProjectionVerifierPrimitives ActualProjectionVerifierBounds ActualProjectionPreparedContexts
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `original_verified_cap` under the displayed hypotheses. -/
private theorem original_verified_cap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let H := sourceIntegerComplement cs N E
    ∃ c contexts fuels fs,prepare H=some (c,contexts) ∧
      atCapTyped H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,fs) ∧
      verify H (sourceInputR cs N E) (sourceDegree cs N E) c fs=
        some (rootDecodedReturnList (family fs) (sourceInputEta cs N E)) ∧
      ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
        List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
          ‖rootRationalCoordinate q-z‖ ≤ (sourceInputEta cs N E : ℝ))
          (rootDecodedReturnList (family fs) (sourceInputEta cs N E)) zs := by
  obtain ⟨c,contexts,fuels,fs,hprepare,hrun,hcn,hguard,haccepted,hweighted,_,houtside,hcount,zs,hm,hpair⟩ :=
    original_computed_allocation cs N E hE htail hparity hd hnorm
  change rootDecodedWeightedDegree (family fs)=2*sourceDegree cs N E at hweighted
  change rootDecodedOutsideCount (family fs)=sourceDegree cs N E at houtside
  obtain ⟨hcan,hlen⟩ := original_canonical_length cs N E hparity hd
  have hclen : (rootCanonicalCoefficients (sourceIntegerComplement cs N E)).length=2*sourceDegree cs N E+1 := by
    rw [hcan,hlen]
  have hweight : rootDecodedWeightedDegree (family fs)=
      (rootCanonicalCoefficients (sourceIntegerComplement cs N E)).length-1 := by rw [hclen,hweighted]; omega
  have hout : rootDecodedOutsideCount (family fs)=
      (rootCanonicalCoefficients (sourceIntegerComplement cs N E)).length-1-sourceDegree cs N E := by
    rw [hclen,houtside]
    omega
  refine ⟨c,contexts,fuels,fs,hprepare,hrun,?_,zs,hm,hpair⟩
  exact verify_of_generated_checks _ _ _ c fs (sourceInputEta cs N E) rfl
    (source_precision_positive cs N E) hd (by omega) (by omega) hcn hguard haccepted hweight hcount hout

end ActualProjectionDecodedVerifierOriginalCap


namespace ActualProjectionRawVerifier
open Polynomial ActualProjectionRawRecordDecode ActualProjectionDecodedVerifier
open ActualProjectionDecodedVerifierSound ActualProjectionVerifierPrimitives
open ActualProjectionVerifierBounds ActualProjectionTypedRecord ActualProjectionTypedRound
open ActualProjectionCapGuardRound ActualProjectionPreparedContexts ActualProjectionStoredRound
open ActualProjectionCapRound ActualProjectionInsideAllocation ActualYunOriginalTarget
open ActualYunPrimitiveContent ActualYunContentSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `SourceProposer` satisfies `original_raw_verified_cap` under the displayed hypotheses. -/
private theorem original_raw_verified_cap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let H := sourceIntegerComplement cs N E
    ∃ c contexts fuels records points,prepare H=some (c,contexts) ∧
      atCapStored H (sourceInputR cs N E) (sourceGamma0 cs N E) fuels=some (c,records) ∧
      verifyRecords H (sourceInputR cs N E) (sourceDegree cs N E) c records=some points ∧
      points.length=sourceDegree cs N E ∧
      ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
        List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
          ‖rootRationalCoordinate q-z‖ ≤ (sourceInputEta cs N E : ℝ)) points zs := by
  obtain ⟨factors,c,contexts,fuels,records,hprepare,hrun,_,hcn,hprod,hmap,hrecords,_⟩ :=
    original_stored_cap_guards cs N E hE htail hparity hd hnorm
  let H := sourceIntegerComplement cs N E
  let eta := sourceInputEta cs N E
  let fs := records.map packRecord
  have hr := (ActualRootProjectionCap.cap_radius_budgets contexts (sourceInputR cs N E) (sourceGamma0 cs N E)
    (sourceGamma0_pos cs N E hE hd)).1
  have heta : 0 < eta := by dsimp only [eta,sourceInputEta]; positivity
  have hctx := original_contexts_good cs N E hparity hd c contexts hprepare
  obtain ⟨hall,hrelation⟩ := records_typed contexts records _ eta hr heta hctx hrecords
  have hfs : factorList fs=factors := by
    change ActualProjectionTypedCertificate.factorList fs=factors
    exact (ActualProjectionTypedCertificate.typed_factor_list contexts fs hrelation).trans hmap
  have hguard : rootIntegerFactorProduct c (List.ofFn (fun j =>
      (List.ofFn (family fs j).coefficients,(family fs j).exponent)))=rootCanonicalCoefficients H := by
    rw [family_factor_list,hfs]
    exact ActualProjectionTypedCertificate.integer_product_guard H c factors hcn hprod
  have haccepted : ∀ j,RootIntegerFactorGuards (family fs j) eta := by
    intro j
    obtain ⟨record,hm,he⟩ := List.mem_map.mp (List.get_mem fs j)
    change RootIntegerFactorGuards (fs.get j) eta
    rw [← he]
    exact (hall record hm).2.2.2
  obtain ⟨zs,hm,hpair⟩ := rootDecodedCertificate_returned fs.length H c (family fs) eta hcn hguard haccepted
  have hcard := congrArg Multiset.card hm
  change zs.length=((rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1)).card at hcard
  have hcount : (rootDecodedReturnList (family fs) eta).length=sourceDegree cs N E :=
    hpair.length_eq.trans (hcard.trans (sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm))
  have hin : rootDecodedInsideCount (family fs)=sourceDegree cs N E :=
    (rootDecodedReturnList_length (family fs) eta).symm.trans hcount
  obtain ⟨w,_,hinj,hroots,_,_⟩ := rootDecodedCertificate_sound fs.length H c (family fs) eta hcn hguard haccepted
  have hweighted := complete_weighted_degree fs.length H (family fs) w hinj hroots
  have hZdeg := (original_target_preconditions cs N E hparity hd).2.1
  have hCdeg : (rootIntegerListPolynomial H).natDegree=2*sourceDegree cs N E :=
    (Polynomial.natDegree_map_eq_of_injective Int.cast_injective (integerPoly H)).trans hZdeg
  have hW : rootDecodedWeightedDegree (family fs)=2*sourceDegree cs N E := by
    rw [hweighted,IsAlgClosed.card_roots_eq_natDegree,hCdeg]
  have hout : rootDecodedOutsideCount (family fs)=sourceDegree cs N E := by
    have hadd := rootDecodedCounts_add (family fs)
    omega
  obtain ⟨hcanonical,hlen⟩ := original_canonical_length cs N E hparity hd
  have hclen : (rootCanonicalCoefficients H).length=2*sourceDegree cs N E+1 := by rw [hcanonical,hlen]
  have hwcheck : rootDecodedWeightedDegree (family fs)=(rootCanonicalCoefficients H).length-1 := by rw [hW,hclen]; omega
  have hocheck : rootDecodedOutsideCount (family fs)=(rootCanonicalCoefficients H).length-1-sourceDegree cs N E := by
    rw [hout,hclen]
    omega
  have htyped : verify H (sourceInputR cs N E) (sourceDegree cs N E) c fs=
      some (rootDecodedReturnList (family fs) eta) :=
    verify_of_generated_checks H _ _ c fs eta rfl (source_precision_positive cs N E) hd
      (by omega) (by omega) hcn hguard haccepted hwcheck hcount hocheck
  have hdecode : decode records=some fs := decode_generated contexts records _ eta hctx hrecords
  refine ⟨c,contexts,fuels,records,rootDecodedReturnList (family fs) eta,hprepare,hrun,?_,hcount,zs,hm,hpair⟩
  simp only [verifyRecords,hdecode,Option.bind_some]
  exact htyped

end ActualProjectionRawVerifier

namespace ActualProjectionPrecisionLoop
/-- Abbreviation for Points in the source proposer model. -/
private abbrev Points := List (ℚ×ℚ)
/-- Abbreviation for Result in the source proposer model. -/
private abbrev Result := Points×List ℕ

/-- Construction for next in the source proposer model. -/
private def next (cap P : ℕ) : ℕ := min (2*P) cap

/-- Construction for run in the source proposer model. -/
private def run (round : ℕ → Option Points) (cap : ℕ) : ℕ → ℕ → Option Result
  | 0,_ => none
  | fuel+1,P =>
    match round P with
    | some points => some (points,[P])
    | none => if cap ≤ P then none else
        (run round cap fuel (next cap P)).map (fun result => (result.1,P::result.2))

/-- The estimate `next_bounds` retains the actual parameter, input-error and normalization budgets. -/
private theorem next_bounds (cap P : ℕ) (hP : 0 < P) (hcap : P < cap) :
    P < next cap P ∧ next cap P ≤ cap := by
  unfold next
  omega

/-- The finite construction in `SourceProposer` satisfies `run_success` under the displayed hypotheses. -/
private theorem run_success (round : ℕ → Option Points) (cap fuel P : ℕ) (hP : 0 < P) (hcap : P ≤ cap)
    (points : Points) (trace : List ℕ) (h : run round cap fuel P=some (points,trace)) :
    ∃ Q,round Q=some points ∧ P ≤ Q ∧ Q ≤ cap ∧ trace≠[] ∧
      trace.head?=some P ∧ trace.getLast?=some Q ∧ trace.Pairwise (· < ·) := by
  induction fuel generalizing P trace with
  | zero => cases h
  | succ fuel ih =>
    cases he : round P with
    | some qs =>
      simp only [run,he] at h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨P,he,le_rfl,hcap,by simp,by simp,by simp,by simp⟩
    | none =>
      have hlt : P < cap := by
        by_contra hn
        have hn' : cap ≤ P := by omega
        simp only [run,he,ite_eq_left hn',reduceCtorEq] at h
      have hb := next_bounds cap P hP hlt
      simp only [run,he,ite_eq_right (by omega : ¬cap ≤ P)] at h
      cases hr : run round cap fuel (next cap P) with
      | none => simp only [hr,Option.map_none,reduceCtorEq] at h
      | some result =>
        have heq : (result.1,P::result.2)=(points,trace) := by
          simpa only [hr,Option.map_some,Option.some.injEq] using h
        obtain ⟨hq,ht⟩ := Prod.mk.inj heq
        rcases result with ⟨qs,ts⟩
        dsimp only at hq ht
        subst qs
        subst trace
        obtain ⟨Q,hQ,hPQ,hQc,hnil,hhead,hlast,hpair⟩ := ih (next cap P) (by omega) hb.2 _ hr
        refine ⟨Q,hQ,by omega,hQc,by simp,by simp,?_,?_⟩
        · simpa only [List.getLast?_cons_of_ne_nil hnil] using hlast
        · apply List.pairwise_cons.mpr
          refine ⟨?_,hpair⟩
          intro x hx
          have hmin : next cap P ≤ x := by
            obtain ⟨a,as,ha⟩ := List.exists_cons_of_ne_nil hnil
            subst ts
            have ha' : a=next cap P := Option.some.inj hhead
            subst a
            rcases List.mem_cons.mp hx with hxe|hxe
            · omega
            · exact (List.pairwise_cons.mp hpair).1 x hxe |>.le
          omega

/-- The finite construction in `SourceProposer` satisfies `run_reaches_cap` under the displayed hypotheses. -/
private theorem run_reaches_cap (round : ℕ → Option Points) (cap fuel P : ℕ)
    (hP : 0 < P) (hcap : P ≤ cap) (hbudget : cap-P < fuel)
    (capPoints : Points) (hterminal : round cap=some capPoints) :
    ∃ points trace,run round cap fuel P=some (points,trace) := by
  induction fuel generalizing P with
  | zero => omega
  | succ fuel ih =>
    cases he : round P with
    | some points => exact ⟨points,[P],by simp only [run,he]⟩
    | none =>
      have hlt : P < cap := by
        by_contra hn
        have heq : P=cap := by omega
        subst P
        rw [hterminal] at he
        cases he
      have hb := next_bounds cap P hP hlt
      obtain ⟨points,trace,hr⟩ := ih (next cap P) (by omega) hb.2 (by omega)
      exact ⟨points,P::trace,by simp only [run,he,ite_eq_right (by omega : ¬cap ≤ P),hr,Option.map_some]⟩

end ActualProjectionPrecisionLoop

namespace ActualProjectionPreparedLoop
open ActualProjectionRawVerifier ActualProjectionRawRecordDecode ActualProjectionPrecisionLoop
open ActualProjectionStoredRound ActualProjectionCapRound ActualProjectionContexts
open ActualProjectionCapRootMatching ActualProjectionPreparedContexts ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Abbreviation for Fuel Plan in the source proposer model. -/
private abbrev FuelPlan := List (List (ℕ×ℕ))

/-- Construction for round Value in the source proposer model. -/
private def roundValue (H : List ℤ) (bits inside : ℕ) (c : ℤ) (contexts : List Context)
    (plan : FuelPlan) (P : ℕ) : Option Points :=
  (roundStored contexts P (1/(2 : ℚ)^(P/2)) (plan.getD P [])).bind
    (verifyRecords H bits inside c)

/-- Construction for propose in the source proposer model. -/
private def propose (H : List ℤ) (bits inside : ℕ) (gap : ℚ) (plan : FuelPlan) : Option Result :=
  (prepare H).bind (fun pair =>
    let limit := cap pair.2 bits gap
    run (roundValue H bits inside pair.1 pair.2 plan) limit (limit+1) (2*bits+16))

/-- The finite construction in `SourceProposer` satisfies `stored_round_finite` under the displayed hypotheses. -/
private theorem stored_round_finite (contexts : List Context) (P : ℕ) (r : ℚ)
    (hctx : ∀ ctx∈contexts,ContextGood ctx) :
    ∃ fuels records,roundStored contexts P r fuels=some records := by
  induction contexts with
  | nil => exact ⟨[],[],rfl⟩
  | cons ctx tail ih =>
    obtain ⟨fx,fy,ix,iy,hr,_,_⟩ := stored_axes_success ctx (hctx ctx (by simp)) P
    obtain ⟨fuels,records,hs⟩ := ih (fun c hc => hctx c (by simp only [List.mem_cons]; exact Or.inr hc))
    exact ⟨(fx,fy)::fuels,factorRecord ctx r ix iy::records,by
      simp only [roundStored,hr,Option.bind_some,hs,Option.map_some]⟩

/-- The finite construction in `SourceProposer` satisfies `finite_plan` under the displayed hypotheses. -/
private theorem finite_plan (contexts : List Context) (limit : ℕ)
    (hctx : ∀ ctx∈contexts,ContextGood ctx) (capFuels : List (ℕ×ℕ)) (capRecords : List Record)
    (hr : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) capFuels=some capRecords) :
    ∃ plan : FuelPlan,plan.length=limit+1 ∧ plan.getD limit []=capFuels ∧
      ∀ P,P ≤ limit → ∃ records,
        roundStored contexts P (1/(2 : ℚ)^(P/2)) (plan.getD P [])=some records := by
  classical
  have ha : ∀ P,∃ fuels records,
      roundStored contexts P (1/(2 : ℚ)^(P/2)) fuels=some records ∧ (P=limit → fuels=capFuels) := by
    intro P
    by_cases he : P=limit
    · subst P
      exact ⟨capFuels,capRecords,hr,fun _ => rfl⟩
    · obtain ⟨fuels,records,hs⟩ := stored_round_finite contexts P _ hctx
      exact ⟨fuels,records,hs,fun h => (he h).elim⟩
  choose fuels records hs using ha
  let plan : FuelPlan := List.ofFn (fun i : Fin (limit+1) => fuels i.val)
  have hget : ∀ P,P ≤ limit → plan.getD P []=fuels P := by
    intro P hP
    have hlen : P < plan.length := by simp only [plan,List.length_ofFn]; omega
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_ofFn hlen
  refine ⟨plan,List.length_ofFn,?_,?_⟩
  · exact (hget limit le_rfl).trans ((hs limit).2 rfl)
  · intro P hP
    exact ⟨records P,by rw [hget P hP]; exact (hs P).1⟩

/-- The finite construction in `SourceProposer` satisfies `round_value_sound` under the displayed hypotheses. -/
private theorem round_value_sound (H : List ℤ) (bits inside : ℕ) (c : ℤ) (contexts : List Context)
    (plan : FuelPlan) (P : ℕ) (points : Points) (h : roundValue H bits inside c contexts plan P=some points) :
    ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ ((if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits) : ℝ)) points zs := by
  cases hr : roundStored contexts P (1/(2 : ℚ)^(P/2)) (plan.getD P []) with
  | none => simp only [roundValue,hr,Option.bind_none,reduceCtorEq] at h
  | some records =>
    have hv : verifyRecords H bits inside c records=some points := by
      simpa only [roundValue,hr,Option.bind_some] using h
    exact raw_returned_of_verify H bits inside c records points hv

/-- The finite construction in `SourceProposer` satisfies `original_prepared_loop` under the displayed hypotheses. -/
private theorem original_prepared_loop (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let H := sourceIntegerComplement cs N E
    let bits := sourceInputR cs N E
    let inside := sourceDegree cs N E
    let gap := sourceGamma0 cs N E
    ∃ c contexts plan points trace,prepare H=some (c,contexts) ∧
      plan.length=cap contexts bits gap+1 ∧
      (∀ P,P ≤ cap contexts bits gap → ∃ records,
        roundStored contexts P (1/(2 : ℚ)^(P/2)) (plan.getD P [])=some records) ∧
      propose H bits inside gap plan=some (points,trace) ∧
      trace.head?=some (2*bits+16) ∧ trace.Pairwise (· < ·) ∧
      (∃ Q,trace.getLast?=some Q ∧ Q ≤ cap contexts bits gap ∧
        roundValue H bits inside c contexts plan Q=some points) ∧
      ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
        points.length=inside ∧ List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
          ‖rootRationalCoordinate q-z‖ ≤ (sourceInputEta cs N E : ℝ)) points zs := by
  classical
  obtain ⟨c,contexts,fuels,records,capPoints,hprepare,hatcap,hverified,hcount,_,_,_⟩ :=
    original_raw_verified_cap cs N E hE htail hparity hd hnorm
  let H := sourceIntegerComplement cs N E
  let bits := sourceInputR cs N E
  let inside := sourceDegree cs N E
  let gap := sourceGamma0 cs N E
  let limit := cap contexts bits gap
  have hr : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels=some records := by
    simp only [atCapStored,hprepare,Option.bind_some] at hatcap
    change (roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels).map (fun rs => (c,rs))=some (c,records) at hatcap
    cases he : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels with
    | none => simp only [he,Option.map_none,reduceCtorEq] at hatcap
    | some rs =>
      have heq : rs=records := congrArg Prod.snd (Option.some.inj (by simpa only [he,Option.map_some] using hatcap))
      exact congrArg some heq
  obtain ⟨plan,hlen,hget,hfinite⟩ := finite_plan contexts limit
    (original_contexts_good cs N E hparity hd c contexts hprepare) fuels records hr
  have hterminal : roundValue H bits inside c contexts plan limit=some capPoints := by
    simp only [roundValue,hget,hr,Option.bind_some]
    exact hverified
  have hP : 0 < 2*bits+16 := by omega
  have hcap : 2*bits+16 ≤ limit := le_max_left _ _
  obtain ⟨points,trace,hrun⟩ := run_reaches_cap (roundValue H bits inside c contexts plan) limit (limit+1)
    (2*bits+16) hP hcap (by omega) capPoints hterminal
  obtain ⟨Q,hQ,_,hQc,_,hhead,hlast,hpair⟩ := run_success _ limit (limit+1) _ hP hcap points trace hrun
  obtain ⟨zs,hm,herror⟩ := round_value_sound H bits inside c contexts plan Q points hQ
  have hc : points.length=inside := herror.length_eq.trans ((congrArg Multiset.card hm).trans
    (sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm))
  refine ⟨c,contexts,plan,points,trace,hprepare,hlen,hfinite,?_,hhead,hpair,⟨Q,hlast,hQc,hQ⟩,zs,hm,hc,?_⟩
  · simp only [propose,hprepare,Option.bind_some]
    exact hrun
  · have hi : inside≠0 := Nat.ne_of_gt hd
    simpa only [hi,ite_false,sourceInputEta,Rat.cast_div,Rat.cast_one,Rat.cast_pow] using herror

end ActualProjectionPreparedLoop




namespace ActualProjectionSearchedRound
open ActualSturmFuelSearch ActualSturmComputedIsolation ActualSturmArrayTools
open ActualProjectionContexts ActualProjectionSturmAxes ActualProjectionStoredRound
open ActualProjectionCapRound ActualRootProjectionCap

/-- Construction for axes in the source proposer model. -/
private def axes (ctx : Context) (hg : ContextGood ctx) (P : ℕ) : List (ℚ×ℚ)×List (ℚ×ℚ) :=
  (searched (lift ctx.xProjection) hg.2.2.1.1 hg.2.2.1.2.1 hg.2.2.1.2.2.1 P,
   searched (lift ctx.yProjection) hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 P)

/-- The finite construction in `SourceProposer` satisfies `searched_of_run` under the displayed hypotheses. -/
private theorem searched_of_run (a : List ℚ) (hcan : ActualYunRationalCanonical.Canonical a)
    (ha : ActualYunRationalArray.poly a≠0) (hd : 0 < (ActualYunRationalArray.poly a).natDegree)
    (P fuel : ℕ) (ps : List (ℚ×ℚ)) (hr : intervals a P fuel=some ps) :
    searched a hcan ha hd P=ps :=
  intervals_unique a P _ fuel _ ps (ActualFiniteFuelSearch.trial_value _ _) hr

/-- The finite construction in `SourceProposer` satisfies `axes_of_run` under the displayed hypotheses. -/
private theorem axes_of_run (ctx : Context) (hg : ContextGood ctx) (P fx fy : ℕ)
    (ix iy : List (ℚ×ℚ)) (hr : storedAxes ctx P fx fy=some (ix,iy)) : axes ctx hg P=(ix,iy) := by
  cases hx : intervals (lift ctx.xProjection) P fx with
  | none => simp only [storedAxes,hx,Option.bind_none,reduceCtorEq] at hr
  | some xs =>
    cases hy : intervals (lift ctx.yProjection) P fy with
    | none => simp only [storedAxes,hx,hy,Option.bind_some,Option.map_none,reduceCtorEq] at hr
    | some ys =>
      have he : (xs,ys)=(ix,iy) := by
        simpa only [storedAxes,hx,hy,Option.bind_some,Option.map_some,Option.some.injEq] using hr
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      unfold axes
      rw [searched_of_run _ _ _ _ P fx xs hx,searched_of_run _ _ _ _ P fy ys hy]

/-- Construction for records in the source proposer model. -/
private def records : (contexts : List Context) → (∀ ctx∈contexts,ContextGood ctx) → ℕ → ℚ → List Record
  | [],_,_,_ => []
  | ctx::tail,hg,P,r =>
    let pair := axes ctx (hg ctx (by simp)) P
    factorRecord ctx r pair.1 pair.2::records tail
      (fun c hc => hg c (by simp only [List.mem_cons]; exact Or.inr hc)) P r

/-- The finite construction in `SourceProposer` satisfies `records_of_run` under the displayed hypotheses. -/
private theorem records_of_run (contexts : List Context) (hg : ∀ ctx∈contexts,ContextGood ctx)
    (P : ℕ) (r : ℚ) (fuels : List (ℕ×ℕ)) (rs : List Record)
    (hr : roundStored contexts P r fuels=some rs) : records contexts hg P r=rs := by
  induction contexts generalizing fuels rs with
  | nil =>
    have he : ([] : List Record)=rs := Option.some.inj hr
    exact he
  | cons ctx tail ih =>
    cases fuels with
    | nil => cases hr
    | cons pair fuels =>
      rcases pair with ⟨fx,fy⟩
      cases ha : storedAxes ctx P fx fy with
      | none => simp only [roundStored,ha,Option.bind_none,reduceCtorEq] at hr
      | some pair =>
        rcases pair with ⟨ix,iy⟩
        cases ht : roundStored tail P r fuels with
        | none => simp only [roundStored,ha,ht,Option.bind_some,Option.map_none,reduceCtorEq] at hr
        | some tailRecords =>
          have he : factorRecord ctx r ix iy::tailRecords=rs := by
            simpa only [roundStored,ha,ht,Option.bind_some,Option.map_some,Option.some.injEq] using hr
          rw [← he]
          have hax := axes_of_run ctx (hg ctx (by simp)) P fx fy ix iy ha
          simp only [records,hax]
          congr 1
          exact ih (fun c hc => hg c (by simp only [List.mem_cons]; exact Or.inr hc)) fuels tailRecords ht

end ActualProjectionSearchedRound

namespace ActualProjectionSearchedLoop
open ActualProjectionSearchedRound ActualProjectionPrecisionLoop
open ActualProjectionRawVerifier ActualProjectionContexts ActualProjectionPreparedContexts
open ActualProjectionStoredRound ActualProjectionCapRound ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for Preparation Good in the source proposer model. -/
private def PreparationGood (H : List ℤ) : Prop :=
  ∀ c contexts,prepare H=some (c,contexts) → ∀ ctx∈contexts,ContextGood ctx

/-- Construction for round Value in the source proposer model. -/
private def roundValue (H : List ℤ) (bits inside : ℕ) (c : ℤ) (contexts : List Context)
    (hg : ∀ ctx∈contexts,ContextGood ctx) (P : ℕ) : Option Points :=
  verifyRecords H bits inside c (records contexts hg P (1/(2 : ℚ)^(P/2)))

/-- Construction for propose in the source proposer model. -/
private def propose (H : List ℤ) (bits inside : ℕ) (gap : ℚ) (good : PreparationGood H) : Option Result :=
  match hp : prepare H with
  | none => none
  | some pair =>
    let limit := cap pair.2 bits gap
    run (roundValue H bits inside pair.1 pair.2 (good pair.1 pair.2 hp)) limit (limit+1) (2*bits+16)

/-- The finite construction in `SourceProposer` satisfies `propose_of_prepare` under the displayed hypotheses. -/
private theorem propose_of_prepare (H : List ℤ) (bits inside : ℕ) (gap : ℚ) (good : PreparationGood H)
    (c : ℤ) (contexts : List Context) (hp : prepare H=some (c,contexts)) :
    propose H bits inside gap good=
      run (roundValue H bits inside c contexts (good c contexts hp))
        (cap contexts bits gap) (cap contexts bits gap+1) (2*bits+16) := by
  unfold propose
  split
  next hn => rw [hn] at hp; cases hp
  next pair hs =>
    have he : pair=(c,contexts) := Option.some.inj (hs.symm.trans hp)
    subst pair
    rfl

/-- The finite construction in `SourceProposer` satisfies `original_preparation_good` under the displayed hypotheses. -/
private theorem original_preparation_good (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) : PreparationGood (sourceIntegerComplement cs N E) :=
  fun c contexts hp => original_contexts_good cs N E hparity hd c contexts hp

/-- Construction for original Propose in the source proposer model. -/
private def originalPropose (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) : Option Result :=
  propose (sourceIntegerComplement cs N E) (sourceInputR cs N E) (sourceDegree cs N E)
    (sourceGamma0 cs N E) (original_preparation_good cs N E hparity hd)

/-- The finite construction in `SourceProposer` satisfies `round_value_sound` under the displayed hypotheses. -/
private theorem round_value_sound (H : List ℤ) (bits inside : ℕ) (c : ℤ) (contexts : List Context)
    (hg : ∀ ctx∈contexts,ContextGood ctx) (P : ℕ) (points : Points)
    (h : roundValue H bits inside c contexts hg P=some points) :
    ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ ((if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits) : ℝ)) points zs :=
  raw_returned_of_verify H bits inside c _ points h

/-- The finite construction in `SourceProposer` satisfies `original_searched_loop` under the displayed hypotheses. -/
private theorem original_searched_loop (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let H := sourceIntegerComplement cs N E
    let bits := sourceInputR cs N E
    let inside := sourceDegree cs N E
    let gap := sourceGamma0 cs N E
    ∃ (c : ℤ) (contexts : List Context) (hg : ∀ ctx∈contexts,ContextGood ctx) (points : Points) (trace : List ℕ),
      prepare H=some (c,contexts) ∧ originalPropose cs N E hparity hd=some (points,trace) ∧
      trace.head?=some (2*bits+16) ∧ trace.Pairwise (· < ·) ∧
      (∃ Q,trace.getLast?=some Q ∧ Q ≤ cap contexts bits gap ∧
        roundValue H bits inside c contexts hg Q=some points) ∧
      ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
        points.length=inside ∧ List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
          ‖rootRationalCoordinate q-z‖ ≤ (sourceInputEta cs N E : ℝ)) points zs := by
  obtain ⟨c,contexts,fuels,raw,capPoints,hprepare,hatcap,hverified,_,_,_,_⟩ :=
    original_raw_verified_cap cs N E hE htail hparity hd hnorm
  let H := sourceIntegerComplement cs N E
  let bits := sourceInputR cs N E
  let inside := sourceDegree cs N E
  let gap := sourceGamma0 cs N E
  let limit := cap contexts bits gap
  have hg : ∀ ctx∈contexts,ContextGood ctx := original_contexts_good cs N E hparity hd c contexts hprepare
  have hr : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels=some raw := by
    simp only [atCapStored,hprepare,Option.bind_some] at hatcap
    change (roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels).map (fun rs => (c,rs))=some (c,raw) at hatcap
    cases he : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels with
    | none => simp only [he,Option.map_none,reduceCtorEq] at hatcap
    | some rs =>
      have heq : rs=raw := congrArg Prod.snd (Option.some.inj (by simpa only [he,Option.map_some] using hatcap))
      exact congrArg some heq
  have hterminal : roundValue H bits inside c contexts hg limit=some capPoints := by
    unfold roundValue
    rw [records_of_run contexts hg limit _ fuels raw hr]
    exact hverified
  have hP : 0 < 2*bits+16 := by omega
  have hcap : 2*bits+16 ≤ limit := le_max_left _ _
  obtain ⟨points,trace,hrun⟩ := run_reaches_cap (roundValue H bits inside c contexts hg) limit (limit+1)
    (2*bits+16) hP hcap (by omega) capPoints hterminal
  obtain ⟨Q,hQ,_,hQc,_,hhead,hlast,hpair⟩ := run_success _ limit (limit+1) _ hP hcap points trace hrun
  obtain ⟨zs,hm,herror⟩ := round_value_sound H bits inside c contexts hg Q points hQ
  have hc : points.length=inside := herror.length_eq.trans ((congrArg Multiset.card hm).trans
    (sourceIntegerComplement_inside_count cs N E hE htail hparity hd hnorm))
  refine ⟨c,contexts,hg,points,trace,hprepare,?_,hhead,hpair,⟨Q,hlast,hQc,hQ⟩,zs,hm,hc,?_⟩
  · change propose H bits inside gap (original_preparation_good cs N E hparity hd)=some (points,trace)
    rw [propose_of_prepare _ _ _ _ _ c contexts hprepare]
    exact hrun
  · have hi : inside≠0 := Nat.ne_of_gt hd
    simpa only [hi,ite_false,sourceInputEta,Rat.cast_div,Rat.cast_one,Rat.cast_pow] using herror

end ActualProjectionSearchedLoop

namespace ActualProjectionPayloadLoop
universe u
variable {α : Type u}
/-- Abbreviation for Result in the source proposer model. -/
private abbrev Result (α : Type u) := α×List ℕ

/-- Construction for next in the source proposer model. -/
private def next (cap P : ℕ) : ℕ := min (2*P) cap

/-- Construction for run in the source proposer model. -/
private def run (round : ℕ → Option α) (cap : ℕ) : ℕ → ℕ → Option (Result α)
  | 0,_ => none
  | fuel+1,P =>
    match round P with
    | some points => some (points,[P])
    | none => if cap ≤ P then none else
        (run round cap fuel (next cap P)).map (fun result => (result.1,P::result.2))

/-- The estimate `next_bounds` retains the actual parameter, input-error and normalization budgets. -/
private theorem next_bounds (cap P : ℕ) (hP : 0 < P) (hcap : P < cap) :
    P < next cap P ∧ next cap P ≤ cap := by
  unfold next
  omega

/-- The finite construction in `SourceProposer` satisfies `run_success` under the displayed hypotheses. -/
private theorem run_success (round : ℕ → Option α) (cap fuel P : ℕ) (hP : 0 < P) (hcap : P ≤ cap)
    (points : α) (trace : List ℕ) (h : run round cap fuel P=some (points,trace)) :
    ∃ Q,round Q=some points ∧ P ≤ Q ∧ Q ≤ cap ∧ trace≠[] ∧
      trace.head?=some P ∧ trace.getLast?=some Q ∧ trace.Pairwise (· < ·) := by
  induction fuel generalizing P trace with
  | zero => cases h
  | succ fuel ih =>
    cases he : round P with
    | some qs =>
      simp only [run,he] at h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨P,he,by omega,hcap,by simp,by simp,by simp,by simp⟩
    | none =>
      have hlt : P < cap := by
        by_contra hn
        have hn' : cap ≤ P := by omega
        simp only [run,he,ite_eq_left hn',reduceCtorEq] at h
      have hb := next_bounds cap P hP hlt
      simp only [run,he,ite_eq_right (by omega : ¬cap ≤ P)] at h
      cases hr : run round cap fuel (next cap P) with
      | none => simp only [hr,Option.map_none,reduceCtorEq] at h
      | some result =>
        have heq : (result.1,P::result.2)=(points,trace) := by
          simpa only [hr,Option.map_some,Option.some.injEq] using h
        obtain ⟨hq,ht⟩ := Prod.mk.inj heq
        rcases result with ⟨qs,ts⟩
        dsimp only at hq ht
        subst qs
        subst trace
        obtain ⟨Q,hQ,hPQ,hQc,hnil,hhead,hlast,hpair⟩ := ih (next cap P) (by omega) hb.2 _ hr
        refine ⟨Q,hQ,by omega,hQc,by simp,by simp,?_,?_⟩
        · simpa only [List.getLast?_cons_of_ne_nil hnil] using hlast
        · apply List.pairwise_cons.mpr
          refine ⟨?_,hpair⟩
          intro x hx
          have hmin : next cap P ≤ x := by
            obtain ⟨a,as,ha⟩ := List.exists_cons_of_ne_nil hnil
            subst ts
            have ha' : a=next cap P := Option.some.inj hhead
            subst a
            rcases List.mem_cons.mp hx with hxe|hxe
            · omega
            · have hh := (List.pairwise_cons.mp hpair).1 x hxe
              omega
          omega

/-- The finite construction in `SourceProposer` satisfies `run_reaches_cap` under the displayed hypotheses. -/
private theorem run_reaches_cap (round : ℕ → Option α) (cap fuel P : ℕ)
    (hP : 0 < P) (hcap : P ≤ cap) (hbudget : cap-P < fuel)
    (capValue : α) (hterminal : round cap=some capValue) :
    ∃ points trace,run round cap fuel P=some (points,trace) := by
  induction fuel generalizing P with
  | zero => omega
  | succ fuel ih =>
    cases he : round P with
    | some points => exact ⟨points,[P],by simp only [run,he]⟩
    | none =>
      have hlt : P < cap := by
        by_contra hn
        have heq : P=cap := by omega
        subst P
        rw [hterminal] at he
        cases he
      have hb := next_bounds cap P hP hlt
      obtain ⟨points,trace,hr⟩ := ih (next cap P) (by omega) hb.2 (by omega)
      exact ⟨points,P::trace,by simp only [run,he,ite_eq_right (by omega : ¬cap ≤ P),hr,Option.map_some]⟩

end ActualProjectionPayloadLoop

namespace ActualProjectionCertificateLoop
open ActualProjectionSearchedRound ActualProjectionSearchedLoop ActualProjectionRawVerifier
open ActualProjectionRawRecordDecode ActualProjectionDecodedVerifier ActualProjectionDecodedVerifierSound
open ActualProjectionVerifierPrimitives ActualProjectionPayloadLoop
open ActualProjectionContexts ActualProjectionPreparedContexts ActualProjectionStoredRound
open ActualProjectionCapRound ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Data and invariants for Certificate in the source proposer model. -/
private structure Certificate where
  content : ℤ
  factors : List RootIntegerFactorData
  points : List (ℚ×ℚ)

/-- Construction for checked Records in the source proposer model. -/
private def checkedRecords (H : List ℤ) (bits inside : ℕ) (c : ℤ) (raw : List Record) : Option Certificate :=
  (decode raw).bind (fun fs => (verify H bits inside c fs).map (fun points => ⟨c,fs,points⟩))

/-- Construction for round Value in the source proposer model. -/
private def roundValue (H : List ℤ) (bits inside : ℕ) (c : ℤ) (contexts : List Context)
    (hg : ∀ ctx∈contexts,ContextGood ctx) (P : ℕ) : Option Certificate :=
  checkedRecords H bits inside c (records contexts hg P (1/(2 : ℚ)^(P/2)))

/-- Construction for propose in the source proposer model. -/
private def propose (H : List ℤ) (bits inside : ℕ) (gap : ℚ) (good : PreparationGood H) : Option (Certificate×List ℕ) :=
  match hp : prepare H with
  | none => none
  | some pair =>
    let limit := cap pair.2 bits gap
    ActualProjectionPayloadLoop.run (roundValue H bits inside pair.1 pair.2 (good pair.1 pair.2 hp))
      limit (limit+1) (2*bits+16)

/-- Construction for original Propose in the source proposer model. -/
private def originalPropose (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) : Option (Certificate×List ℕ) :=
  propose (sourceIntegerComplement cs N E) (sourceInputR cs N E) (sourceDegree cs N E)
    (sourceGamma0 cs N E) (original_preparation_good cs N E hparity hd)

/-- The finite construction in `SourceProposer` satisfies `propose_of_prepare` under the displayed hypotheses. -/
private theorem propose_of_prepare (H : List ℤ) (bits inside : ℕ) (gap : ℚ) (good : PreparationGood H)
    (c : ℤ) (contexts : List Context) (hp : prepare H=some (c,contexts)) :
    propose H bits inside gap good=
      ActualProjectionPayloadLoop.run (roundValue H bits inside c contexts (good c contexts hp))
        (cap contexts bits gap) (cap contexts bits gap+1) (2*bits+16) := by
  unfold propose
  split
  next hn => rw [hn] at hp; cases hp
  next pair hs =>
    have he : pair=(c,contexts) := Option.some.inj (hs.symm.trans hp)
    subst pair
    rfl

/-- The finite construction in `SourceProposer` satisfies `checked_of_verified` under the displayed hypotheses. -/
private theorem checked_of_verified (H : List ℤ) (bits inside : ℕ) (c : ℤ) (raw : List Record)
    (points : List (ℚ×ℚ)) (h : verifyRecords H bits inside c raw=some points) :
    ∃ fs,checkedRecords H bits inside c raw=some ⟨c,fs,points⟩ := by
  cases hd : decode raw with
  | none => simp only [verifyRecords,hd,Option.bind_none,reduceCtorEq] at h
  | some fs =>
    have hv : verify H bits inside c fs=some points := by simpa only [verifyRecords,hd,Option.bind_some] using h
    exact ⟨fs,by simp only [checkedRecords,hd,Option.bind_some,hv,Option.map_some]⟩

/-- The finite construction in `SourceProposer` satisfies `checked_spec` under the displayed hypotheses. -/
private theorem checked_spec (H : List ℤ) (bits inside : ℕ) (c : ℤ) (raw : List Record)
    (result : Certificate) (h : checkedRecords H bits inside c raw=some result) :
    result.content=c ∧ verify H bits inside result.content result.factors=some result.points := by
  cases hd : decode raw with
  | none => simp only [checkedRecords,hd,Option.bind_none,reduceCtorEq] at h
  | some fs =>
    cases hv : verify H bits inside c fs with
    | none => simp only [checkedRecords,hd,Option.bind_some,hv,Option.map_none,reduceCtorEq] at h
    | some points =>
      have he : (⟨c,fs,points⟩ : Certificate)=result := by
        simpa only [checkedRecords,hd,Option.bind_some,hv,Option.map_some,Option.some.injEq] using h
      subst result
      exact ⟨rfl,hv⟩

/-- The finite construction in `SourceProposer` satisfies `original_certificate_loop` under the displayed hypotheses. -/
private theorem original_certificate_loop (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let H := sourceIntegerComplement cs N E
    ∃ (c : ℤ) (contexts : List Context) (hg : ∀ ctx∈contexts,ContextGood ctx)
        (result : Certificate) (trace : List ℕ),
      prepare H=some (c,contexts) ∧ originalPropose cs N E hparity hd=some (result,trace) ∧
      trace.head?=some (2*sourceInputR cs N E+16) ∧ trace.Pairwise (· < ·) ∧
      (∃ Q,trace.getLast?=some Q ∧ Q ≤ cap contexts (sourceInputR cs N E) (sourceGamma0 cs N E) ∧
        roundValue H (sourceInputR cs N E) (sourceDegree cs N E) c contexts hg Q=some result) ∧
      result.content=c ∧ result.content≠0 ∧
      rootIntegerFactorProduct result.content (List.ofFn (fun j =>
        (List.ofFn (family result.factors j).coefficients,(family result.factors j).exponent)))=rootCanonicalCoefficients H ∧
      (∀ j,RootIntegerFactorGuards (family result.factors j) (sourceInputEta cs N E)) ∧
      result.points=rootDecodedReturnList (family result.factors) (sourceInputEta cs N E) ∧
      result.points.length=sourceDegree cs N E := by
  obtain ⟨c,contexts,fuels,raw,capPoints,hprepare,hatcap,hverified,_,_,_,_⟩ :=
    original_raw_verified_cap cs N E hE htail hparity hd hnorm
  let H := sourceIntegerComplement cs N E
  let bits := sourceInputR cs N E
  let inside := sourceDegree cs N E
  let gap := sourceGamma0 cs N E
  let limit := cap contexts bits gap
  have hg : ∀ ctx∈contexts,ContextGood ctx := original_contexts_good cs N E hparity hd c contexts hprepare
  have hr : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels=some raw := by
    simp only [atCapStored,hprepare,Option.bind_some] at hatcap
    change (roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels).map (fun rs => (c,rs))=some (c,raw) at hatcap
    cases he : roundStored contexts limit (1/(2 : ℚ)^(limit/2)) fuels with
    | none => simp only [he,Option.map_none,reduceCtorEq] at hatcap
    | some rs =>
      have heq : rs=raw := congrArg Prod.snd (Option.some.inj (by simpa only [he,Option.map_some] using hatcap))
      exact congrArg some heq
  obtain ⟨fs,hchecked⟩ := checked_of_verified H bits inside c raw capPoints hverified
  have hterminal : roundValue H bits inside c contexts hg limit=some ⟨c,fs,capPoints⟩ := by
    unfold roundValue
    rw [records_of_run contexts hg limit _ fuels raw hr]
    exact hchecked
  have hP : 0 < 2*bits+16 := by omega
  have hcap : 2*bits+16 ≤ limit := le_max_left _ _
  obtain ⟨result,trace,hrun⟩ := ActualProjectionPayloadLoop.run_reaches_cap
    (roundValue H bits inside c contexts hg) limit (limit+1) (2*bits+16) hP hcap (by omega) _ hterminal
  obtain ⟨Q,hQ,_,hQc,_,hhead,hlast,hpair⟩ := ActualProjectionPayloadLoop.run_success
    _ limit (limit+1) _ hP hcap result trace hrun
  obtain ⟨hcontent,hv⟩ := checked_spec H bits inside c _ result hQ
  obtain ⟨hcn,hproduct,hguards,hpoints,hcount,_⟩ :=
    accepted_guards H bits inside result.content result.factors result.points hv
  have he : (if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits)=sourceInputEta cs N E := by
    rw [ite_eq_right (Nat.ne_of_gt hd)]
    rfl
  rw [he] at hguards hpoints
  refine ⟨c,contexts,hg,result,trace,hprepare,?_,hhead,hpair,⟨Q,hlast,hQc,hQ⟩,hcontent,hcn,hproduct,hguards,hpoints,hcount⟩
  change propose H bits inside gap (original_preparation_good cs N E hparity hd)=some (result,trace)
  rw [propose_of_prepare _ _ _ _ _ c contexts hprepare]
  exact hrun

end ActualProjectionCertificateLoop

namespace ActualProjectionGeneratedPacket
open ActualProjectionCertificateLoop ActualProjectionVerifierPrimitives
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Data and invariants for Packet Return in the source proposer model. -/
private structure PacketReturn where
  certificate : Certificate
  standard : PhaseData
  native : PhaseData
  trace : List ℕ

/-- Construction for finish in the source proposer model. -/
private def finish (cs : List ℚ) (N : ℕ) (E : ℚ) (certificate : Certificate) (trace : List ℕ) : PacketReturn :=
  let standard := sourceBoundaryPacket cs N E (family certificate.factors)
  ⟨certificate,standard,nativePacketFromStandard standard,trace⟩

/-- Construction for produce in the source proposer model. -/
private def produce (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E) : Option PacketReturn :=
  (originalPropose cs N E hparity hd).map (fun result => finish cs N E result.1 result.2)

/-- Construction for Certificate Valid in the source proposer model. -/
private def CertificateValid (cs : List ℚ) (N : ℕ) (E : ℚ) (c : Certificate) : Prop :=
  c.content≠0 ∧ rootIntegerFactorProduct c.content (List.ofFn (fun j =>
    (List.ofFn (family c.factors j).coefficients,(family c.factors j).exponent)))=
      rootCanonicalCoefficients (sourceIntegerComplement cs N E) ∧
    ∀ j,RootIntegerFactorGuards (family c.factors j) (sourceInputEta cs N E)

/-- Construction for Packet Good in the source proposer model. -/
private def PacketGood (cs : List ℚ) (N : ℕ) (E : ℚ) (result : PacketReturn) : Prop :=
  result.native=nativePacketFromStandard result.standard ∧
    result.standard.phases.length=N ∧ ‖gaussianRatComplex result.standard.base‖=1 ∧
    (∀ z∈result.standard.phases,‖gaussianRatComplex z‖=1) ∧
    result.native.phases.length=N ∧ ‖gaussianRatComplex result.native.base‖=1 ∧
    (∀ z∈result.native.phases,‖gaussianRatComplex z‖=1) ∧
    (∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex result.native.base) (result.native.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 13*(sourceInputU cs N E : ℝ)/32) ∧
    (nativeChebyshevMass (sourceResidual cs result.standard) : ℝ) ≤ 13*(E : ℝ)/32 ∧
    nativeChebyshevPacketCheck cs (sourceResidual cs result.standard) result.standard E=true

/-- The finite construction in `SourceProposer` satisfies `original_generated_packet` under the displayed hypotheses. -/
private theorem original_generated_packet (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ∃ certificate trace,originalPropose cs N E hparity hd=some (certificate,trace) ∧
      produce cs N E hparity hd=some (finish cs N E certificate trace) ∧
      CertificateValid cs N E certificate ∧ PacketGood cs N E (finish cs N E certificate trace) := by
  obtain ⟨_,_,_,certificate,trace,_,hrun,_,_,_,_,hcn,hproduct,hguards,_,_⟩ :=
    original_certificate_loop cs N E hE htail hparity hd hnorm
  refine ⟨certificate,trace,hrun,?_,⟨hcn,hproduct,hguards⟩,?_⟩
  · simp only [produce,hrun,Option.map_some]
  · obtain ⟨hslen,hsbase,hsunit⟩ := source_boundary_packet_spec cs N E hparity hd (family certificate.factors)
    obtain ⟨hnlen,hnbase,hnunit⟩ := source_native_packet_spec cs N E hparity hd (family certificate.factors)
    refine ⟨rfl,hslen,hsbase,hsunit,hnlen,hnbase,hnunit,?_,?_,?_⟩
    · exact source_native_uniform cs N E hE htail hparity hd hnorm certificate.factors.length certificate.content
        (family certificate.factors) hcn hproduct hguards
    · exact source_residual_mass_bound cs N E hE htail hparity hd hnorm certificate.factors.length certificate.content
        (family certificate.factors) hcn hproduct hguards
    · exact source_posterior_accepts cs N E hE htail hparity hd hnorm certificate.factors.length certificate.content
        (family certificate.factors) hcn hproduct hguards

end ActualProjectionGeneratedPacket

namespace ActualProjectionGeneratedCheckedWord
open ActualProjectionGeneratedPacket ActualProjectionCertificateLoop ActualProjectionVerifierPrimitives
open Qatlib
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `SourceProposer` satisfies `original_generated_checked_word` under the displayed hypotheses. -/
private theorem original_generated_checked_word
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
 (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (henc : ProjectedUnitaryEncoding A U L R) :
    ∃ certificate trace,
      originalPropose cs N E hparity hd=some (certificate,trace) ∧
      produce cs N E hparity hd=some (finish cs N E certificate trace) ∧
    let data := (finish cs N E certificate trace).standard
    let word := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
      WellFormedAdjointCircuit word ∧
      adjointQueryCount word=N ∧ adjointGateCount word=N+1 ∧
      (N%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) word) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (N%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) := by
  obtain ⟨certificate,trace,hrun,hproduce,hvalid,_⟩ := original_generated_packet cs N E hE htail hparity hd hnorm
  refine ⟨certificate,trace,hrun,hproduce,?_⟩
  exact source_checked_word_transform A U L R cs N E hE htail hparity hd hnorm
    certificate.factors.length certificate.content (family certificate.factors)
    hvalid.1 hvalid.2.1 hvalid.2.2 henc

end ActualProjectionGeneratedCheckedWord




end RootYunInternal
open Polynomial
open RootYunInternal.ActualYunRationalArray RootYunInternal.ActualYunPrimitive
open RootYunInternal.ActualYunPrimitiveContent RootYunInternal.ActualYunContentSupply
open RootYunInternal.ActualYunArrayLoop RootYunInternal.ActualYunContentGuard
open RootYunInternal.ActualYunOriginalTarget
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Same original cs/N/E supplies nonzero/degree/canonical target facts.
This is the actual last-entry rational ratio and exact coefficient-array
comparison before source projections; it is not whole proposer success. -/
theorem source_original_yun_guard (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    let H := sourceIntegerComplement cs N E
    ∃ (out : List (List ℤ×ℕ)) (c : ℤ),
      rootYunSquarefreeFactors (H.map (fun z : ℤ => (z : ℚ)))=some out ∧ c≠0 ∧
      let product := rootYunFactorProduct out
      let content := (H.getD (H.length-1) 0 : ℚ)/product.getD (product.length-1) 0
      content=(c : ℚ) ∧ content.den=1 ∧
      product.map (fun v => content*v)=H.map (fun z : ℤ => (z : ℚ)) :=
  original_generated_guard cs N E hparity hd

/-- Every factor of the same original-target run has actual complex
separability and source array shape; its exponent is at most the original
complement degree 2*d. This does not require disks or root certificates. -/
theorem source_original_yun_factor_properties (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (out : List (List ℤ×ℕ))
    (hout : rootYunSquarefreeFactors
      ((sourceIntegerComplement cs N E).map (fun z : ℤ => (z : ℚ)))=some out) :
    ∀ f∈out,RootYunFactorGood f ∧ f.2≤2*sourceDegree cs N E := by
  obtain ⟨hnz,hdegree,hcanonical⟩ := original_target_preconditions cs N E hparity hd
  let A := (sourceIntegerComplement cs N E).map (fun z : ℤ => (z : ℚ))
  have hAnz : poly A≠0 := by
    dsimp only [A]
    rw [castArray_poly]
    intro hz
    apply hnz
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [Polynomial.map_zero] using hz
  have hAdeg : (poly A).natDegree=2*sourceDegree cs N E := by
    dsimp only [A]
    rw [castArray_poly,Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective,hdegree]
  obtain ⟨ys,hys,hprod,hgood⟩ := rootYun_generated_factors A hAnz (by change 0<(poly A).natDegree; rw [hAdeg]; omega)
  have he : ys=out := Option.some.inj (hys.symm.trans hout)
  subst ys
  intro f hf
  have hg := hgood f hf
  exact ⟨hg.1,by have hb := hg.2; change f.2≤(poly A).natDegree at hb; rw [hAdeg] at hb; exact hb⟩


/-- Direct same-original cs/N/E consumer for real roots of H itself. It does not
claim the Cartesian projection candidates or a complex certificate. -/
theorem source_original_sturm_intervals (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (bits : ℕ) :
    let A := (sourceIntegerComplement cs N E).map (fun z : ℤ => (z : ℚ))
    ∃ fuel result,rootSturmIntervals A bits fuel=some result ∧
      (∀ p∈result,RootSturmGoodInterval A bits p) ∧
      (∀ x∈rootSturmRealRoots A,rootSturmHits result x=1) ∧
      result.Pairwise RootSturmApart ∧ result.Pairwise RootSturmLexLE := by
  obtain ⟨hnz,hdegree,hcanonical⟩ := original_target_preconditions cs N E hparity hd
  let A := (sourceIntegerComplement cs N E).map (fun z : ℤ => (z : ℚ))
  have hAnz : poly A≠0 := by
    dsimp only [A]
    rw [castArray_poly]
    intro hz
    apply hnz
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [Polynomial.map_zero] using hz
  have hAdeg : (poly A).natDegree=2*sourceDegree cs N E := by
    dsimp only [A]
    rw [castArray_poly,Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective,hdegree]
  exact RootYunInternal.ActualSturmComputedIsolation.computed_isolation A hcanonical hAnz
    (by rw [hAdeg]; omega) bits


/-- The finite construction in `SourceProposer` satisfies `projection_output_public` under the displayed hypotheses. -/
private theorem projection_output_public (cs out : List ℤ)
    (axis : RootYunInternal.ActualProjectionEntryDegrees.Axis)
    (h : RootYunInternal.ActualProjectionProducedArrays.OutputProperties cs axis out) :
    RootProjectionArrayGood cs out (RootYunInternal.ActualProjectionProducedArrays.coordinate axis) := by
  obtain ⟨hcan,hn,hd,hcoord⟩ := h
  have hlen := RootYunInternal.ActualYunRationalCanonical.canonical_length _ hcan
    ((RootYunInternal.ActualYunRationalCanonical.canonical_nonzero _ hcan).mpr hn)
  exact ⟨by simpa only [RootYunInternal.ActualSturmArrayTools.lift, RootYunInternal.ActualYunRationalArray.poly, List.length_map] using hlen,hn,hd,hcoord⟩

/-- Construction for root Projection Publish Record in the source proposer model. -/
private def rootProjectionPublishRecord (r : RootYunInternal.ActualProjectionCapRound.Record) :
    RootProjectionFactorRecord := ⟨r.factor,r.exponent,r.disks⟩

/-- Actual Yun content/full-array guard and generated stored projection contexts. -/
def rootProjectionPrepare (target : List ℤ) : Option (ℤ×List RootProjectionContext) :=
  RootYunInternal.ActualProjectionPreparedContexts.prepare target

/-- Literal zero-residual shortcut and derivative integer cross-product test. -/
def rootProjectionLiteralPasses (factor : List ℤ) (center : ℚ×ℚ) (r : ℚ) : Bool :=
  RootYunInternal.ActualProjectionSourcePasses.sourcePasses factor center r

/-- One round at the literal cap consumes the already stored Rx/Ry arrays.
Fuel is only an evaluation witness for the terminating real-isolation loops. -/
def rootProjectionStoredCapRound (target : List ℤ) (bits : ℕ) (gap : ℚ) (fuels : List (ℕ×ℕ)) :
    Option (ℤ×List RootProjectionFactorRecord) :=
  (RootYunInternal.ActualProjectionStoredRound.atCapStored target bits gap fuels).map
    (fun p => (p.1,p.2.map rootProjectionPublishRecord))

/-- Representation and separability supplied by the actual Yun output. -/
def RootProjectionFactorContextGood (ctx : RootProjectionContext) : Prop :=
  (rootIntegerListPolynomial ctx.factor).Separable ∧
    0<(rootIntegerListPolynomial ctx.factor).natDegree ∧
    ctx.factor.length=(rootIntegerListPolynomial ctx.factor).natDegree+1 ∧
    ctx.factor.getD (ctx.factor.length-1) 0≠0 ∧ 0<ctx.exponent

/-- Per-record source arithmetic, exact list count and disk geometry.
The complete typed verifier and its inside-count/precision loop are separate. -/
def RootProjectionFactorRecordGood (ctx : RootProjectionContext) (r eta : ℚ)
    (record : RootProjectionFactorRecord) : Prop :=
  record.factor=ctx.factor ∧ record.exponent=ctx.exponent ∧
    record.disks.length=(rootIntegerListPolynomial ctx.factor).natDegree ∧ record.disks.Nodup ∧
    (∀ d∈record.disks,d.2=r ∧ 0<d.2 ∧ rootProjectionLiteralPasses ctx.factor d.1 r=true ∧
      ∃ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 ∧ ‖z-rootRationalCoordinate d.1‖≤(d.2 : ℝ)) ∧
    (∀ z : ℂ,(rootIntegerListPolynomial ctx.factor).eval z=0 →
      ∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖≤(d.2 : ℝ)) ∧
    (∀ d∈record.disks,∀ e∈record.disks,d≠e →
      (d.2+e.2)^2<(d.1.1-e.1.1)^2+(d.1.2-e.1.2)^2) ∧
    (∀ d∈record.disks,rootRationalDiskClassify d.1 d.2≠none) ∧
    (∀ d∈record.disks,d.2+|(rootGridPoint d.1 (eta/16)).1-d.1.1|+
      |(rootGridPoint d.1 (eta/16)).2-d.1.2|≤eta)

/-- The finite construction in `SourceProposer` satisfies `rootProjectionPublishGood` under the displayed hypotheses. -/
private theorem rootProjectionPublishGood (ctx : RootProjectionContext) (r eta : ℚ) (hr : 0<r)
    (record : RootYunInternal.ActualProjectionCapRound.Record)
    (h : RootYunInternal.ActualProjectionCapGuardRound.GuardRecordGood ctx r eta record) :
    RootProjectionFactorRecordGood ctx r eta (rootProjectionPublishRecord record) := by
  refine ⟨h.1.1.1,h.1.1.2.1,h.1.2,h.2.1,?_,h.1.1.2.2.2,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  intro d hd
  obtain ⟨hrr,hpass,hz⟩ := h.1.1.2.2.1 d hd
  refine ⟨hrr,by rw [hrr]; exact hr,hpass,?_⟩
  rw [hrr]
  exact hz

/-- The finite construction in `SourceProposer` satisfies `rootProjectionPublishRecordsGood` under the displayed hypotheses. -/
private theorem rootProjectionPublishRecordsGood (contexts : List RootProjectionContext)
    (records : List RootYunInternal.ActualProjectionCapRound.Record) (r eta : ℚ) (hr : 0<r)
    (h : List.Forall₂ (fun ctx record => RootYunInternal.ActualProjectionCapGuardRound.GuardRecordGood ctx r eta record) contexts records) :
    List.Forall₂ (fun ctx record => RootProjectionFactorRecordGood ctx r eta record) contexts
      (records.map rootProjectionPublishRecord) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead _ ih => exact List.Forall₂.cons (rootProjectionPublishGood _ _ _ hr _ hhead) ih

/-- Same original cs/N/E computes H, Yun/context data and one literal cap
round. All per-record count, inclusion, separation, classification and grid
properties are derived; no factor/root/interval/gap answer is an input. -/
theorem source_original_projection_cap_records (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1) :
    let H := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceIntegerComplement cs N E
    ∃ c contexts fuels records,rootProjectionPrepare H=some (c,contexts) ∧
      rootProjectionStoredCapRound H (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputR cs N E) (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceGamma0 cs N E) fuels=some (c,records) ∧
      fuels.length=contexts.length ∧ c≠0 ∧
      (⟨⟨H.toFinsupp⟩⟩ : ℤ[X])=Polynomial.C c*(contexts.map
        (fun ctx => (⟨⟨ctx.factor.toFinsupp⟩⟩ : ℤ[X])^ctx.exponent)).prod ∧
      (∀ ctx∈contexts,RootProjectionFactorContextGood ctx) ∧
      List.Forall₂ (fun ctx record => RootProjectionFactorRecordGood ctx
        (rootProjectionRadius contexts (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputR cs N E) (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceGamma0 cs N E))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputEta cs N E) record) contexts records ∧
      (∀ z : ℂ,(rootIntegerListPolynomial H).eval z=0 →
        ∃ record∈records,∃ d∈record.disks,‖z-rootRationalCoordinate d.1‖≤(d.2 : ℝ)) := by
  obtain ⟨fs,c,contexts,fuels,records,hprepare,hrun,hlen,hcn,hprod,hmap,hrecords,hcover⟩ :=
    RootYunInternal.ActualProjectionCapGuardRound.original_stored_cap_guards cs N E hE htail hparity hd hnorm
  have hg := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceGamma0_pos cs N E hE hd
  have hr := (rootProjectionCap_radius_budgets contexts (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputR cs N E)
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceGamma0 cs N E) hg).1
  refine ⟨c,contexts,fuels,records.map rootProjectionPublishRecord,hprepare,?_,hlen,hcn,?_,?_,?_,?_⟩
  · simp only [rootProjectionStoredCapRound,hrun,Option.map_some]
  · simpa only [RootYunInternal.ActualYunContentSupply.rawProduct,← hmap,List.map_map, Function.comp_def, RootYunInternal.ActualYunPrimitiveContent.integerPoly] using hprod
  · intro ctx hc
    exact (RootYunInternal.ActualProjectionStoredRound.original_contexts_good cs N E hparity hd c contexts hprepare ctx hc).1
  · exact rootProjectionPublishRecordsGood contexts records _ _ hr hrecords
  · intro z hz
    obtain ⟨record,hm,d,hdisk,hnear⟩ := hcover z hz
    exact ⟨rootProjectionPublishRecord record,List.mem_map.mpr ⟨record,hm,rfl⟩,d,hdisk,hnear⟩

/-- Finite evaluation witnesses for the stored real-isolation loops.
Existence is internal to the theorem; no numerical fuel generator is claimed. -/
abbrev RootProjectionFuelPlan := List (List (ℕ×ℕ))

/-- One arbitrary precision round consumes the stored Rx/Ry in each context. -/
def rootProjectionStoredRound (contexts : List RootProjectionContext) (precision : ℕ) (r : ℚ)
    (fuels : List (ℕ×ℕ)) : Option (List RootProjectionFactorRecord) :=
  (RootYunInternal.ActualProjectionStoredRound.roundStored contexts precision r fuels).map
    (List.map rootProjectionPublishRecord)

/-- Same stored round and decoded checker at this precision. -/
def rootProjectionPrecisionAttempt (target : List ℤ) (bits inside : ℕ) (content : ℤ)
    (contexts : List RootProjectionContext) (plan : RootProjectionFuelPlan) (precision : ℕ) :
    Option (List (ℚ×ℚ)) :=
  RootYunInternal.ActualProjectionPreparedLoop.roundValue target bits inside content contexts plan precision

/-- Prepare Yun/projections once, start at 2*bits+16, and double with the
computed cap until the first accepted decoded output. The second component
is the ordered list of attempted precisions, not a cost ledger. -/
def rootProjectionPrecisionPropose (target : List ℤ) (bits inside : ℕ) (gap : ℚ)
    (plan : RootProjectionFuelPlan) : Option (List (ℚ×ℚ)×List ℕ) :=
  RootYunInternal.ActualProjectionPreparedLoop.propose target bits inside gap plan

/-- Original cs/N/E internally supplies finite isolation witnesses and an
accepted decoded precision-loop output, with every inside root and its
multiplicity. This models the positive radial-gap, unrestricted-attempt
branch at the value level; it does not supply a numerical fuel-generation
implementation, JSON/CPython refinement or explicit bit/physical fees. -/
theorem source_original_projection_verified_loop (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let H := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceIntegerComplement cs N E
    let bits := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputR cs N E
    let inside := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E
    let gap := Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceGamma0 cs N E
    ∃ c contexts plan points trace,rootProjectionPrepare H=some (c,contexts) ∧
      plan.length=rootProjectionCap contexts bits gap+1 ∧
      (∀ P,P ≤ rootProjectionCap contexts bits gap → ∃ records,
        rootProjectionStoredRound contexts P (1/(2 : ℚ)^(P/2)) (plan.getD P [])=some records) ∧
      rootProjectionPrecisionPropose H bits inside gap plan=some (points,trace) ∧
      trace.head?=some (2*bits+16) ∧ trace.Pairwise (· < ·) ∧
      (∃ Q,trace.getLast?=some Q ∧ Q ≤ rootProjectionCap contexts bits gap ∧
        rootProjectionPrecisionAttempt H bits inside c contexts plan Q=some points) ∧
      ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
        points.length=inside ∧ List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
          ‖rootRationalCoordinate q-z‖ ≤ (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputEta cs N E : ℝ)) points zs := by
  obtain ⟨c,contexts,plan,points,trace,hprepare,hlen,hfinite,hrun,hhead,hpair,hreturn,hpoints⟩ :=
    RootYunInternal.ActualProjectionPreparedLoop.original_prepared_loop cs N E hE htail hparity hd hnorm
  refine ⟨c,contexts,plan,points,trace,hprepare,hlen,?_,hrun,hhead,hpair,hreturn,hpoints⟩
  intro P hP
  obtain ⟨records,hr⟩ := hfinite P hP
  exact ⟨records.map rootProjectionPublishRecord,by simp only [rootProjectionStoredRound,hr,Option.map_some]⟩

section GeneratedNonconstantPacket
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Actual stored projection searches, raw count-safe checking and cached
accepted factors feed completion/deflation and both phase packets. This
entry computes the positive-degree test; zero-degree branches return none.
No numerical fuel plan or raw factor certificate is supplied by the caller.
Repeated bounded searches are not a CPython trace or a total fee theorem. -/
def rootProjectionGeneratedNonconstantPacket (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) :
    Option (PhaseData×PhaseData×List ℕ) :=
  if hd : 0 < Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E then
    (RootYunInternal.ActualProjectionGeneratedPacket.produce cs N E hparity hd).map
      (fun result => (result.standard,result.native,result.trace))
  else none

/-- The same original nonconstant input produces its own accepted root
payload and phase packet. Accuracy is for the complete original cs, with
actual convert-first residual/check. Host refinement and total fees remain
separate; no factor/root/count/fuel/certificate answer is a hypothesis. -/
theorem source_original_generated_nonconstant_packet (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0 < Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ∃ (standard native : PhaseData) (trace : List ℕ),
      rootProjectionGeneratedNonconstantPacket cs N E hparity=some (standard,native,trace) ∧
      native=nativePacketFromStandard standard ∧
      standard.phases.length=N ∧ ‖gaussianRatComplex standard.base‖=1 ∧
      (∀ z∈standard.phases,‖gaussianRatComplex z‖=1) ∧
      native.phases.length=N ∧ ‖gaussianRatComplex native.base‖=1 ∧
      (∀ z∈native.phases,‖gaussianRatComplex z‖=1) ∧
      (∀ x∈Set.Icc (-1 : ℝ) 1,
        |((responseP (gaussianRatComplex native.base) (native.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
          (nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 13*(Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputU cs N E : ℝ)/32) ∧
      (nativeChebyshevMass (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceResidual cs standard) : ℝ) ≤ 13*(E : ℝ)/32 ∧
      nativeChebyshevPacketCheck cs (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceResidual cs standard) standard E=true := by
  obtain ⟨certificate,trace,_,hp,_,hg⟩ :=
    RootYunInternal.ActualProjectionGeneratedPacket.original_generated_packet cs N E hE htail hparity hd hnorm
  refine ⟨(RootYunInternal.ActualProjectionGeneratedPacket.finish cs N E certificate trace).standard,
    (RootYunInternal.ActualProjectionGeneratedPacket.finish cs N E certificate trace).native,trace,?_,hg⟩
  simp only [rootProjectionGeneratedNonconstantPacket,dite_eq_left hd,hp,Option.map_some]
  rfl

end GeneratedNonconstantPacket

section GeneratedNonconstantWord
open Qatlib
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `SourceProposer` satisfies `source_original_generated_nonconstant_word` under the displayed hypotheses. -/
theorem source_original_generated_nonconstant_word
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
 (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (henc : ProjectedUnitaryEncoding A U L R) :
    ∃ (standard native : Qatlib.Concepts.NativeNumerics.PhaseSynthesis.PhaseData) (trace : List ℕ),
      rootProjectionGeneratedNonconstantPacket cs N E hparity=some (standard,native,trace) ∧
    let data := standard
    let word := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
      WellFormedAdjointCircuit word ∧
      adjointQueryCount word=N ∧ adjointGateCount word=N+1 ∧
      (N%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) word) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (N%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) := by
  obtain ⟨certificate,trace,_,hp,hw⟩ :=
    RootYunInternal.ActualProjectionGeneratedCheckedWord.original_generated_checked_word
      A U L R cs N E hE htail hparity hd hnorm henc
  refine ⟨(RootYunInternal.ActualProjectionGeneratedPacket.finish cs N E certificate trace).standard,
    (RootYunInternal.ActualProjectionGeneratedPacket.finish cs N E certificate trace).native,trace,?_,hw⟩
  simp only [rootProjectionGeneratedNonconstantPacket,dite_eq_left hd,hp,Option.map_some]
  rfl

end GeneratedNonconstantWord

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

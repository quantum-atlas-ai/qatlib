/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeSourceIntegerization
import Mathlib.Data.Nat.Find
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.Nodup
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.List.Sort
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Data.List.Induction
import Mathlib.Data.List.ToFinsupp
import Mathlib.RingTheory.Polynomial.GaussLemma
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCanonicalMultiply
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootClassifiedCatalogue
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCommonDenominator
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootConvolutionLoop
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCoordinateTruncation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDecodedCertificate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskCertificate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskClassification
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskCompleteness
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskInclusion
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootFactorProduct
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerCatalogue
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerConvolution
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerCoordinate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerHorner
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerList
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootProjectionBudget
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootReturnedCompleteness
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootReturnedList
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootSharedHorner
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeSourceBitPrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

/-! Exact polynomial-array algorithms: Yun.
These algorithms retain program bodies, guards, hypotheses and finite-fuel semantics. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
namespace RootYunInternal

namespace ActualYunInitial
open Polynomial

/-- The finite construction in `Yun` satisfies `initial_quotient_separable` under the displayed hypotheses. -/
theorem initial_quotient_separable (f : ℂ[X]) (hf : f ≠ 0) :
    (f / gcd f f.derivative).Separable := by
  classical
  let c := gcd f f.derivative
  let w := f/c
  have hc : c ≠ 0 := gcd_ne_zero_of_left hf
  have hw : w ≠ 0 := left_div_gcd_ne_zero hf
  have hprod : c*w=f := EuclideanDomain.mul_div_cancel' hc (gcd_dvd_left _ _)
  apply (Polynomial.nodup_roots_iff_of_splits hw (IsAlgClosed.splits w)).mp
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  rw [Polynomial.count_roots]
  by_cases hz : w.eval z=0
  · have hfz : f.IsRoot z := by rw [← hprod]; simp only [IsRoot.def,eval_mul,hz,mul_zero]
    have hd := Polynomial.derivative_rootMultiplicity_of_root hfz
    have hpowf : (X-C z)^(f.rootMultiplicity z-1) ∣ f :=
      (pow_dvd_pow (X-C z) (Nat.sub_le _ _)).trans (f.pow_rootMultiplicity_dvd z)
    have hpowd : (X-C z)^(f.rootMultiplicity z-1) ∣ f.derivative := by
      rw [← hd]
      exact f.derivative.pow_rootMultiplicity_dvd z
    have hpowc : (X-C z)^(f.rootMultiplicity z-1) ∣ c := dvd_gcd hpowf hpowd
    have hle := (Polynomial.le_rootMultiplicity_iff hc).mpr hpowc
    have hmult : f.rootMultiplicity z=c.rootMultiplicity z+w.rootMultiplicity z := by
      rw [← hprod,Polynomial.rootMultiplicity_mul (by simpa only [hprod] using hf)]
    omega
  · rw [Polynomial.rootMultiplicity_eq_zero hz]
    omega


/-- The finite construction in `Yun` satisfies `normalized_euclidean_eq_gcd` under the displayed hypotheses. -/
theorem normalized_euclidean_eq_gcd {K : Type} [Field K] [DecidableEq K] (f g : K[X]) :
    normalize (EuclideanDomain.gcd f g) = gcd f g := by
  symm
  apply gcd_eq_normalize
  · exact EuclideanDomain.dvd_gcd (gcd_dvd_left f g) (gcd_dvd_right f g)
  · exact dvd_gcd (EuclideanDomain.gcd_dvd_left f g) (EuclideanDomain.gcd_dvd_right f g)

/-- Matches mathematical Euclidean division followed by source monic.
The actual rational-list Euclidean loop still needs refinement. -/
def gcdQ (f g : ℚ[X]) : ℚ[X] := normalize (EuclideanDomain.gcd f g)

/-- The finite construction in `Yun` satisfies `gcdQ_map` under the displayed hypotheses. -/
theorem gcdQ_map (f g : ℚ[X]) :
    (gcdQ f g).map (Rat.castHom ℂ) = gcd (f.map (Rat.castHom ℂ)) (g.map (Rat.castHom ℂ)) := by
  classical
  unfold gcdQ
  rw [Polynomial.map_normalize,← Polynomial.gcd_map]
  exact normalized_euclidean_eq_gcd _ _

/-- The finite construction in `Yun` satisfies `initial_rational_quotient_separable` under the displayed hypotheses. -/
theorem initial_rational_quotient_separable (f : ℚ[X]) (hf : f ≠ 0) :
    ((f/gcdQ f f.derivative).map (Rat.castHom ℂ)).Separable := by
  classical
  have hmap : f.map (Rat.castHom ℂ) ≠ 0 := by
    exact Polynomial.map_ne_zero hf
  rw [Polynomial.map_div,gcdQ_map,← Polynomial.derivative_map]
  exact initial_quotient_separable _ hmap

end ActualYunInitial


namespace ActualYunStep
open Polynomial ActualYunInitial
open scoped BigOperators

/-- Data and invariants for State in the yun model. -/
structure State where
  w : ℚ[X]
  c : ℚ[X]
  exponent : ℕ
  factors : List (ℚ[X]×ℕ)

/-- Construction for factor Product in the yun model. -/
def factorProduct (s : State) : ℚ[X] := (s.factors.map (fun f => f.1^f.2)).prod
/-- Construction for measure in the yun model. -/
def measure (s : State) : ℕ := s.w.natDegree+s.c.natDegree
/-- Construction for step in the yun model. -/
def step (s : State) : State :=
  let y := gcdQ s.w s.c
  let z := s.w/y
  ⟨y,s.c/y,s.exponent+1,
    if 0<z.natDegree then s.factors++[(z,s.exponent)] else s.factors⟩

/-- Construction for Root Support in the yun model. -/
def RootSupport (c w : ℚ[X]) : Prop := ∀ z : ℂ,
  (c.map (Rat.castHom ℂ)).eval z=0 → (w.map (Rat.castHom ℂ)).eval z=0

/-- Data and invariants for Invariant in the yun model. -/
structure Invariant (F : ℚ[X]) (s : State) : Prop where
  w_monic : s.w.Monic
  c_monic : s.c.Monic
  exponent_pos : 0<s.exponent
  w_separable : (s.w.map (Rat.castHom ℂ)).Separable
  support : RootSupport s.c s.w
  product : F=factorProduct s*s.w^s.exponent*s.c
  factors : ∀ f ∈ s.factors,f.1.Monic ∧ (f.1.map (Rat.castHom ℂ)).Separable ∧ 0<f.2

/-- The finite construction in `Yun` satisfies `gcdQ_eq_gcd` under the displayed hypotheses. -/
theorem gcdQ_eq_gcd (f g : ℚ[X]) : gcdQ f g=gcd f g := normalized_euclidean_eq_gcd f g

/-- The finite construction in `Yun` satisfies `gcdQ_monic` under the displayed hypotheses. -/
theorem gcdQ_monic (f g : ℚ[X]) (hf : f≠0) : (gcdQ f g).Monic := by
  have hg : EuclideanDomain.gcd f g≠0 := by
    intro hz
    have hdiv := EuclideanDomain.gcd_dvd_left f g
    rw [hz,zero_dvd_iff] at hdiv
    exact hf hdiv
  exact Polynomial.monic_normalize hg

/-- The finite construction in `Yun` satisfies `step_invariant` under the displayed hypotheses. -/
theorem step_invariant (F : ℚ[X]) (s : State) (h : Invariant F s) : Invariant F (step s) := by
  classical
  let y := gcdQ s.w s.c
  let z := s.w/y
  let c' := s.c/y
  have hy : y.Monic := gcdQ_monic s.w s.c h.w_monic.ne_zero
  have hydw : y∣s.w := by rw [show y=gcd s.w s.c from gcdQ_eq_gcd _ _]; exact gcd_dvd_left _ _
  have hydc : y∣s.c := by rw [show y=gcd s.w s.c from gcdQ_eq_gcd _ _]; exact gcd_dvd_right _ _
  have hyz : y*z=s.w := EuclideanDomain.mul_div_cancel' hy.ne_zero hydw
  have hyc : y*c'=s.c := EuclideanDomain.mul_div_cancel' hy.ne_zero hydc
  have hz : z.Monic := hy.of_mul_monic_left (hyz.symm ▸ h.w_monic)
  have hc : c'.Monic := hy.of_mul_monic_left (hyc.symm ▸ h.c_monic)
  have hys : (y.map (Rat.castHom ℂ)).Separable := h.w_separable.of_dvd (Polynomial.map_dvd _ hydw)
  have hzs : (z.map (Rat.castHom ℂ)).Separable := h.w_separable.of_dvd
    (Polynomial.map_dvd _ ⟨y,by rw [mul_comm,hyz]⟩)
  have hsupport : RootSupport c' y := by
    intro a ha
    have hcroot : (s.c.map (Rat.castHom ℂ)).eval a=0 := by
      rw [← hyc,Polynomial.map_mul,Polynomial.eval_mul,ha,mul_zero]
    have hwroot := h.support a hcroot
    rw [show y=gcdQ s.w s.c from rfl,gcdQ_map]
    exact Polynomial.dvd_iff_isRoot.mp (dvd_gcd
      (Polynomial.dvd_iff_isRoot.mpr hwroot) (Polynomial.dvd_iff_isRoot.mpr hcroot))
  refine ⟨hy,hc,by dsimp [step]; omega,hys,hsupport,?_,?_⟩
  · change F=factorProduct (step s)*y^(s.exponent+1)*c'
    have hfactor : factorProduct (step s)=factorProduct s*z^s.exponent := by
      dsimp only [factorProduct,step]
      split_ifs with hdeg
      · simp only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,
          List.prod_nil,mul_one]
        rfl
      · change ¬0<z.natDegree at hdeg
        have hz1 : z=1 := hz.natDegree_eq_zero.mp (by omega)
        change factorProduct s=factorProduct s*z^s.exponent
        rw [hz1,one_pow,mul_one]
    rw [hfactor,h.product,← hyz,← hyc,mul_pow,pow_succ]
    ring
  · intro f hf
    change f∈(if 0<z.natDegree then s.factors++[(z,s.exponent)] else s.factors) at hf
    split_ifs at hf
    · rcases List.mem_append.mp hf with hold | hnew
      · exact h.factors f hold
      · have heq : f=(z,s.exponent) := List.mem_singleton.mp hnew
        subst f
        exact ⟨hz,hzs,h.exponent_pos⟩
    · exact h.factors f hf

/-- The finite construction in `Yun` satisfies `step_measure` under the displayed hypotheses. -/
theorem step_measure (s : State) (hw : s.w≠0) (hc : s.c≠0) :
    measure (step s)=s.c.natDegree := by
  let y := gcdQ s.w s.c
  have hy : y≠0 := (gcdQ_monic s.w s.c hw).ne_zero
  have hyd : y∣s.c := by rw [show y=gcd s.w s.c from gcdQ_eq_gcd _ _]; exact gcd_dvd_right _ _
  have hprod : y*(s.c/y)=s.c := EuclideanDomain.mul_div_cancel' hy hyd
  have hquot : s.c/y≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact hc hprod.symm
  have hn := Polynomial.natDegree_mul hy hquot
  rw [hprod] at hn
  exact hn.symm

/-- The finite construction in `Yun` satisfies `step_measure_strict` under the displayed hypotheses. -/
theorem step_measure_strict (F : ℚ[X]) (s : State) (h : Invariant F s)
    (hw : 0<s.w.natDegree) : measure (step s) < measure s := by
  rw [step_measure s h.w_monic.ne_zero h.c_monic.ne_zero]
  dsimp only [measure]
  omega

end ActualYunStep


namespace ActualYunLoop
open Polynomial ActualYunInitial ActualYunStep

/-- The finite construction in `Yun` satisfies `initial_complex_support` under the displayed hypotheses. -/
theorem initial_complex_support (f : ℂ[X]) (hf : f≠0) (hd : 0<f.natDegree) :
    ∀ z : ℂ,(gcd f f.derivative).eval z=0 → (f/gcd f f.derivative).eval z=0 := by
  classical
  let c := gcd f f.derivative
  let w := f/c
  have hc : c≠0 := gcd_ne_zero_of_left hf
  have hprod : c*w=f := EuclideanDomain.mul_div_cancel' hc (gcd_dvd_left _ _)
  have hdnz : f.derivative≠0 := by
    intro hz
    have h := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hz
    omega
  intro z hcz
  change c.eval z=0 at hcz
  have hfz : f.IsRoot z := by rw [← hprod]; simp only [IsRoot.def,eval_mul,hcz,zero_mul]
  have hder := Polynomial.derivative_rootMultiplicity_of_root hfz
  have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hdnz
    (gcd_dvd_right f f.derivative) z
  change c.rootMultiplicity z≤f.derivative.rootMultiplicity z at hle
  have hmult : f.rootMultiplicity z=c.rootMultiplicity z+w.rootMultiplicity z := by
    rw [← hprod,Polynomial.rootMultiplicity_mul (by simpa only [hprod] using hf)]
  have hpos : 0<c.rootMultiplicity z := (Polynomial.rootMultiplicity_pos hc).mpr hcz
  by_contra hwz
  have hw0 := Polynomial.rootMultiplicity_eq_zero hwz
  change w.rootMultiplicity z=0 at hw0
  rw [hder] at hle
  omega

/-- Construction for initial in the yun model. -/
def initial (F : ℚ[X]) : State := ⟨F/gcdQ F F.derivative,gcdQ F F.derivative,1,[]⟩

/-- The finite construction in `Yun` satisfies `initial_invariant` under the displayed hypotheses. -/
theorem initial_invariant (F : ℚ[X]) (hF : F.Monic) (hd : 0<F.natDegree) :
    Invariant F (initial F) := by
  classical
  let c := gcdQ F F.derivative
  let w := F/c
  have hc : c.Monic := gcdQ_monic F F.derivative hF.ne_zero
  have hdiv : c∣F := by rw [show c=gcd F F.derivative from gcdQ_eq_gcd _ _]; exact gcd_dvd_left _ _
  have hp : c*w=F := EuclideanDomain.mul_div_cancel' hc.ne_zero hdiv
  have hw : w.Monic := hc.of_mul_monic_left (hp.symm ▸ hF)
  refine ⟨hw,hc,Nat.zero_lt_one,initial_rational_quotient_separable F hF.ne_zero,?_,?_,?_⟩
  · intro z hcz
    have hm : (gcdQ F F.derivative).map (Rat.castHom ℂ) =
        gcd (F.map (Rat.castHom ℂ)) (F.map (Rat.castHom ℂ)).derivative := by
      rw [gcdQ_map,Polynomial.derivative_map]
    have hwmap : (F/gcdQ F F.derivative).map (Rat.castHom ℂ) =
        F.map (Rat.castHom ℂ)/gcd (F.map (Rat.castHom ℂ)) (F.map (Rat.castHom ℂ)).derivative := by
      rw [Polynomial.map_div,hm]
    have hdC : 0<(F.map (Rat.castHom ℂ)).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℂ).injective F]
      exact hd
    change ((F/gcdQ F F.derivative).map (Rat.castHom ℂ)).eval z=0
    rw [hwmap]
    apply initial_complex_support _ (Polynomial.map_ne_zero hF.ne_zero) hdC z
    simpa only [initial,hm] using hcz
  · change F=1*w^1*c
    simpa only [one_mul,pow_one,mul_comm] using hp.symm
  · intro f hf
    cases hf

/-- The finite construction in `Yun` satisfies `initial_measure` under the displayed hypotheses. -/
theorem initial_measure (F : ℚ[X]) (hF : F.Monic) : measure (initial F)=F.natDegree := by
  let c := gcdQ F F.derivative
  have hc : c.Monic := gcdQ_monic F F.derivative hF.ne_zero
  have hdiv : c∣F := by rw [show c=gcd F F.derivative from gcdQ_eq_gcd _ _]; exact gcd_dvd_left _ _
  have hp : c*(F/c)=F := EuclideanDomain.mul_div_cancel' hc.ne_zero hdiv
  have hw : F/c≠0 := by intro hz; rw [hz,mul_zero] at hp; exact hF.ne_zero hp.symm
  have hn := Polynomial.natDegree_mul hc.ne_zero hw
  rw [hp] at hn
  change (F/c).natDegree+c.natDegree=F.natDegree
  omega

/-- Construction for run in the yun model. -/
def run : ℕ → State → State
  | 0,s => s
  | fuel+1,s => if 0<s.w.natDegree then run fuel (step s) else s

/-- The finite construction in `Yun` satisfies `run_invariant_terminal` under the displayed hypotheses. -/
theorem run_invariant_terminal (F : ℚ[X]) (fuel : ℕ) (s : State) (h : Invariant F s)
    (hm : measure s≤fuel) : Invariant F (run fuel s) ∧ (run fuel s).w=1 := by
  induction fuel generalizing s with
  | zero =>
    have hw : s.w.natDegree=0 := by dsimp only [ActualYunStep.measure] at hm; omega
    exact ⟨h,h.w_monic.natDegree_eq_zero.mp hw⟩
  | succ fuel ih =>
    unfold run
    split_ifs with hw
    · have hmstep : measure (step s)≤fuel := by
        have hlt := step_measure_strict F s h hw
        omega
      exact ih (step s) (step_invariant F s h) hmstep
    · exact ⟨h,h.w_monic.natDegree_eq_zero.mp (by omega)⟩

/-- The same emitted instruction list satisfies `run_counter_bound` with the displayed gate and query accounting. -/
theorem run_counter_bound (F : ℚ[X]) (fuel : ℕ) (s : State) (h : Invariant F s) :
    measure (run fuel s)+(run fuel s).exponent ≤ measure s+s.exponent := by
  induction fuel generalizing s with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold run
    split_ifs with hw
    · have hi := ih (step s) (step_invariant F s h)
      have hms := step_measure s h.w_monic.ne_zero h.c_monic.ne_zero
      have hexp : (step s).exponent=s.exponent+1 := rfl
      dsimp only [ActualYunStep.measure] at *
      omega
    · exact Nat.le_refl _

/-- The finite construction in `Yun` satisfies `terminal_product` under the displayed hypotheses. -/
theorem terminal_product (F : ℚ[X]) (s : State) (h : Invariant F s) (hw : s.w=1) :
    s.c=1 ∧ F=factorProduct s := by
  have hcdeg : (s.c.map (Rat.castHom ℂ)).natDegree=0 := by
    by_contra hz
    obtain ⟨z,hzroot⟩ := (IsAlgClosed.splits (s.c.map (Rat.castHom ℂ))).exists_eval_eq_zero
      (Polynomial.degree_ne_of_natDegree_ne hz)
    have hbad := h.support z hzroot
    rw [hw,Polynomial.map_one,Polynomial.eval_one] at hbad
    exact one_ne_zero hbad
  have hc : s.c=1 := h.c_monic.natDegree_eq_zero.mp (by
    rwa [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℂ).injective s.c] at hcdeg)
  refine ⟨hc,?_⟩
  simpa only [hw,hc,one_pow,mul_one] using h.product

/-- The finite construction in `Yun` satisfies `generated_polynomial_factors` under the displayed hypotheses. -/
theorem generated_polynomial_factors (F : ℚ[X]) (hF : F.Monic) (hd : 0<F.natDegree) :
    let out := run F.natDegree (initial F)
    F=factorProduct out ∧ out.w=1 ∧ out.c=1 ∧ out.exponent≤F.natDegree+1 ∧
      ∀ f∈out.factors,f.1.Monic ∧ (f.1.map (Rat.castHom ℂ)).Separable ∧ 0<f.2 := by
  let out := run F.natDegree (initial F)
  have hi := initial_invariant F hF hd
  have ht := run_invariant_terminal F F.natDegree (initial F) hi (initial_measure F hF).le
  have hp := terminal_product F out ht.1 ht.2
  have hb := run_counter_bound F F.natDegree (initial F) hi
  rw [initial_measure F hF] at hb
  have he : out.exponent≤F.natDegree+1 := by
    change measure out+out.exponent≤F.natDegree+1 at hb
    omega
  exact ⟨hp.2,ht.2,hp.1,he,ht.1.factors⟩

end ActualYunLoop


namespace ActualYunOutputBounds
open Polynomial ActualYunInitial ActualYunStep ActualYunLoop

/-- Construction for Output Bound in the yun model. -/
def OutputBound (s : State) : Prop := ∀ f∈s.factors,
  0<f.1.natDegree ∧ f.2<s.exponent

/-- The estimate `step_output_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem step_output_bound (s : State) (h : OutputBound s) : OutputBound (step s) := by
  intro f hf
  change f∈(if 0<(s.w/gcdQ s.w s.c).natDegree then
    s.factors++[(s.w/gcdQ s.w s.c,s.exponent)] else s.factors) at hf
  change 0<f.1.natDegree ∧ f.2<s.exponent+1
  split_ifs at hf with hd
  · rcases List.mem_append.mp hf with hold | hnew
    · have hb := h f hold
      exact ⟨hb.1,by omega⟩
    · have heq := List.mem_singleton.mp hnew
      subst f
      exact ⟨hd,Nat.lt_succ_self _⟩
  · have hb := h f hf
    exact ⟨hb.1,by omega⟩

/-- The estimate `run_output_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem run_output_bound (fuel : ℕ) (s : State) (h : OutputBound s) :
    OutputBound (run fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    unfold run
    split_ifs
    · exact ih (step s) (step_output_bound s h)
    · exact h

/-- The same emitted instruction list satisfies `every_prefix_counter` with the displayed gate and query accounting. -/
theorem every_prefix_counter (F : ℚ[X]) (hF : F.Monic) (hd : 0<F.natDegree) (fuel : ℕ) :
    (run fuel (initial F)).exponent≤F.natDegree+1 := by
  have h := run_counter_bound F fuel (initial F) (initial_invariant F hF hd)
  rw [initial_measure F hF] at h
  change ActualYunStep.measure (run fuel (initial F))+(run fuel (initial F)).exponent≤F.natDegree+1 at h
  omega

/-- The finite construction in `Yun` satisfies `run_invariant` under the displayed hypotheses. -/
theorem run_invariant (F : ℚ[X]) (fuel : ℕ) (s : State) (h : Invariant F s) :
    Invariant F (run fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    unfold run
    split_ifs
    · exact ih (step s) (step_invariant F s h)
    · exact h

/-- The finite construction in `Yun` satisfies `every_stored_factor` under the displayed hypotheses. -/
theorem every_stored_factor (F : ℚ[X]) (hF : F.Monic) (hd : 0<F.natDegree) (fuel : ℕ) :
    ∀ f∈(run fuel (initial F)).factors,0<f.1.natDegree ∧ 0<f.2 ∧ f.2≤F.natDegree := by
  have hi := initial_invariant F hF hd
  have hrun := run_invariant F fuel (initial F) hi
  have houtput := run_output_bound fuel (initial F) (by intro f hf; cases hf)
  have hcounter := every_prefix_counter F hF hd fuel
  intro f hf
  have hb := houtput f hf
  exact ⟨hb.1,(hrun.factors f hf).2.2,by omega⟩

end ActualYunOutputBounds


namespace ActualYunRationalArray
open Polynomial

/-- Construction for poly in the yun model. -/
def poly (a : List ℚ) : ℚ[X] := ⟨⟨a.toFinsupp⟩⟩
/-- Construction for trim in the yun model. -/
def trim (a : List ℚ) : List ℚ := (a.reverse.dropWhile (fun x => x==0)).reverse

/-- The finite construction in `Yun` satisfies `coeff` under the displayed hypotheses. -/
theorem coeff (a : List ℚ) (k : ℕ) : (poly a).coeff k=a.getD k 0 := by
  change a.toFinsupp k=a.getD k 0
  exact List.toFinsupp_apply _ _

/-- The finite construction in `Yun` satisfies `poly_nil` under the displayed hypotheses. -/
theorem poly_nil : poly []=0 := by ext k; simp [coeff]

/-- The finite construction in `Yun` satisfies `poly_append_zero` under the displayed hypotheses. -/
theorem poly_append_zero (a : List ℚ) : poly (a++[0])=poly a := by
  apply Polynomial.ext
  intro k
  change (a++[0]).toFinsupp k=a.toFinsupp k
  rw [List.toFinsupp_concat_eq_toFinsupp_add_single]
  simp

/-- Constructors for Zero Tail Trace in the yun model. -/
inductive ZeroTailTrace : List ℚ → List ℚ → Prop where
  | refl (a : List ℚ) : ZeroTailTrace a a
  | pop (a b : List ℚ) : ZeroTailTrace a b → ZeroTailTrace (a++[0]) b

/-- The finite construction in `Yun` satisfies `trim_trace` under the displayed hypotheses. -/
theorem trim_trace (a : List ℚ) : ZeroTailTrace a (trim a) := by
  induction a using List.reverseRecOn with
  | nil => simpa [trim] using ZeroTailTrace.refl ([] : List ℚ)
  | append_singleton a x ih =>
    by_cases hx : x=0
    · subst x
      simpa [trim] using ZeroTailTrace.pop a (trim a) ih
    · have ht : trim (a++[x])=a++[x] := by simp [trim,hx]
      rw [ht]
      exact ZeroTailTrace.refl _

/-- The finite construction in `Yun` satisfies `trace_poly` under the displayed hypotheses. -/
theorem trace_poly {a b : List ℚ} (h : ZeroTailTrace a b) : poly a=poly b := by
  induction h with
  | refl => rfl
  | pop a _ _ ih => exact (poly_append_zero a).trans ih

/-- The finite construction in `Yun` satisfies `trim_poly` under the displayed hypotheses. -/
theorem trim_poly (a : List ℚ) : poly (trim a)=poly a := (trace_poly (trim_trace a)).symm

/-- The finite construction in `Yun` satisfies `trim_shape` under the displayed hypotheses. -/
theorem trim_shape (a : List ℚ) : trim a=[] ∨ ∃ b x,trim a=b++[x] ∧ x≠0 := by
  induction a using List.reverseRecOn with
  | nil => left; simp [trim]
  | append_singleton a x ih =>
    by_cases hx : x=0
    · subst x
      simpa only [show trim (a++[0])=trim a by simp [trim]] using ih
    · exact Or.inr ⟨a,x,by simp [trim,hx],hx⟩

/-- The finite construction in `Yun` satisfies `poly_set` under the displayed hypotheses. -/
theorem poly_set (a : List ℚ) (i : ℕ) (v : ℚ) (hi : i<a.length) :
    poly (a.set i v)=poly a+monomial i (v-a.getD i 0) := by
  ext k
  rw [Polynomial.coeff_add,Polynomial.coeff_monomial,coeff,coeff]
  by_cases hk : i=k
  · subst k
    rw [ite_eq_left rfl]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_set_self hi,Option.getD_some]
    ring
  · rw [ite_eq_right hk]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_set_ne hk,add_zero]

/-- The finite construction in `Yun` satisfies `poly_cons` under the displayed hypotheses. -/
theorem poly_cons (c : ℚ) (cs : List ℚ) : poly (c::cs)=C c+X*poly cs := by
  ext k
  cases k with
  | zero => simp [coeff]
  | succ k => simp [coeff,Polynomial.coeff_X_mul]

/-- Source enumerate(b) in ascending order; every update reads the current
array and replaces the same k+j cell. Length remains the initial allocation. -/
def subtractShift (a : List ℚ) : List ℚ → ℕ → ℚ → List ℚ
  | [],_,_ => a
  | c::cs,j,v => subtractShift (a.set j (a.getD j 0-v*c)) cs (j+1) v

/-- The same emitted instruction list satisfies `subtractShift_length` with the displayed gate and query accounting. -/
theorem subtractShift_length (a b : List ℚ) (j : ℕ) (v : ℚ) :
    (subtractShift a b j v).length=a.length := by
  induction b generalizing a j with
  | nil => rfl
  | cons c cs ih =>
    simpa only [subtractShift,List.length_set] using ih (a.set j (a.getD j 0-v*c)) (j+1)

/-- The finite construction in `Yun` satisfies `subtractShift_poly` under the displayed hypotheses. -/
theorem subtractShift_poly (a b : List ℚ) (j : ℕ) (v : ℚ)
    (hbound : j+b.length≤a.length) :
    poly (subtractShift a b j v)=poly a-C v*X^j*poly b := by
  induction b generalizing a j with
  | nil => simp [subtractShift,poly_nil]
  | cons c cs ih =>
    have hj : j<a.length := by simp only [List.length_cons] at hbound; omega
    have hnext : j+1+cs.length≤(a.set j (a.getD j 0-v*c)).length := by
      simp only [List.length_set]
      simp only [List.length_cons] at hbound
      omega
    rw [subtractShift,ih _ _ hnext,poly_set _ _ _ hj,poly_cons]
    have hmono : monomial j (a.getD j 0-v*c-a.getD j 0)= -(C v*X^j*C c) := by
      rw [show a.getD j 0-v*c-a.getD j 0= -(v*c) by ring,
        ← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.C_neg,Polynomial.C_mul]
      ring
    rw [hmono,pow_succ]
    ring

end ActualYunRationalArray


namespace ActualYunRationalCanonical
open Polynomial ActualYunRationalArray

/-- Construction for Canonical in the yun model. -/
def Canonical (a : List ℚ) : Prop := trim a=a

/-- The same emitted instruction list satisfies `poly_degree_lt_length` with the displayed gate and query accounting. -/
theorem poly_degree_lt_length (a : List ℚ) : (poly a).degree<a.length := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  rw [coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none hk,Option.getD_none]

/-- The finite construction in `Yun` satisfies `append_last_coeff` under the displayed hypotheses. -/
theorem append_last_coeff (a : List ℚ) (x : ℚ) : (poly (a++[x])).coeff a.length=x := by
  rw [coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

/-- The finite construction in `Yun` satisfies `append_last_nonzero` under the displayed hypotheses. -/
theorem append_last_nonzero (a : List ℚ) (x : ℚ) (hx : x≠0) : poly (a++[x])≠0 := by
  intro hp
  have hc := append_last_coeff a x
  rw [hp,Polynomial.coeff_zero] at hc
  exact hx hc.symm

/-- The finite construction in `Yun` satisfies `append_last_degree` under the displayed hypotheses. -/
theorem append_last_degree (a : List ℚ) (x : ℚ) (hx : x≠0) :
    (poly (a++[x])).natDegree=a.length := by
  have hnz := append_last_nonzero a x hx
  have hd := (Polynomial.natDegree_lt_iff_degree_lt hnz).mpr (poly_degree_lt_length (a++[x]))
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (by simp only [List.length_append,List.length_singleton] at hd; omega)
  rw [append_last_coeff]
  exact hx

/-- The finite construction in `Yun` satisfies `trim_canonical` under the displayed hypotheses. -/
theorem trim_canonical (a : List ℚ) : Canonical (trim a) := by
  rcases trim_shape a with he | ⟨b,x,he,hx⟩
  · change trim (trim a)=trim a
    rw [he]
    rfl
  · change trim (trim a)=trim a
    rw [he]
    simp [trim,hx]

/-- The finite construction in `Yun` satisfies `canonical_nonzero` under the displayed hypotheses. -/
theorem canonical_nonzero (a : List ℚ) (ha : Canonical a) : a≠[] ↔ poly a≠0 := by
  rcases trim_shape a with he | ⟨b,x,he,hx⟩
  · rw [ha] at he
    simp [he,poly_nil]
  · rw [ha] at he
    rw [he]
    exact ⟨fun _ => append_last_nonzero b x hx,fun _ => by simp⟩

/-- The same emitted instruction list satisfies `canonical_length` with the displayed gate and query accounting. -/
theorem canonical_length (a : List ℚ) (ha : Canonical a) (hn : a≠[]) :
    a.length=(poly a).natDegree+1 := by
  rcases trim_shape a with he | ⟨b,x,he,hx⟩
  · rw [ha] at he
    exact (hn he).elim
  · rw [ha] at he
    rw [he,append_last_degree b x hx]
    simp

/-- The finite construction in `Yun` satisfies `canonical_leading` under the displayed hypotheses. -/
theorem canonical_leading (a : List ℚ) (ha : Canonical a) (hn : a≠[]) :
    (poly a).leadingCoeff=a.getD (a.length-1) 0 := by
  have hd : (poly a).natDegree=a.length-1 := by have h := canonical_length a ha hn; omega
  rw [Polynomial.leadingCoeff,hd,coeff]

end ActualYunRationalCanonical


namespace ActualYunDivisionStep
open Polynomial ActualYunRationalArray ActualYunRationalCanonical

/-- Construction for offset in the yun model. -/
def offset (a b : List ℚ) : ℕ := a.length-b.length
/-- Construction for scale in the yun model. -/
def scale (a b : List ℚ) : ℚ := a.getD (a.length-1) 0 / b.getD (b.length-1) 0
/-- Construction for remainder Step in the yun model. -/
def remainderStep (a b : List ℚ) : List ℚ := trim (subtractShift a b (offset a b) (scale a b))

/-- The finite construction in `Yun` satisfies `remainderStep_poly` under the displayed hypotheses. -/
theorem remainderStep_poly (a b : List ℚ) (hlen : b.length≤a.length) :
    poly (remainderStep a b)=poly a-C (scale a b)*X^(offset a b)*poly b := by
  rw [remainderStep,trim_poly,subtractShift_poly]
  dsimp only [offset]
  omega

/-- The finite construction in `Yun` satisfies `scale_leading` under the displayed hypotheses. -/
theorem scale_leading (a b : List ℚ) (ha : Canonical a) (hb : Canonical b)
    (hna : a≠[]) (hnb : b≠[]) : scale a b=(poly a).leadingCoeff/(poly b).leadingCoeff := by
  rw [scale,canonical_leading a ha hna,canonical_leading b hb hnb]

/-- The finite construction in `Yun` satisfies `remainderStep_degree` under the displayed hypotheses. -/
theorem remainderStep_degree (a b : List ℚ) (ha : Canonical a) (hb : Canonical b)
    (hna : a≠[]) (hnb : b≠[]) (hlen : b.length≤a.length) :
    (poly (remainderStep a b)).degree < (poly a).degree := by
  have hnza := (canonical_nonzero a ha).mp hna
  have hnzb := (canonical_nonzero b hb).mp hnb
  have hla := canonical_length a ha hna
  have hlb := canonical_length b hb hnb
  have hoff : offset a b=(poly a).natDegree-(poly b).natDegree := by dsimp only [offset]; omega
  have hdegree : (poly b).natDegree≤(poly a).natDegree := by omega
  let v := (poly a).leadingCoeff/(poly b).leadingCoeff
  have hv : v≠0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnza)
    (Polynomial.leadingCoeff_ne_zero.mpr hnzb)
  have hterm : poly b*(C v*X^(offset a b))≠0 := mul_ne_zero hnzb
    (mul_ne_zero (Polynomial.C_ne_zero.mpr hv) (pow_ne_zero _ Polynomial.X_ne_zero))
  have htermdeg : (poly b*(C v*X^(offset a b))).natDegree=(poly a).natDegree := by
    rw [Polynomial.natDegree_mul hnzb (mul_ne_zero (Polynomial.C_ne_zero.mpr hv)
      (pow_ne_zero _ Polynomial.X_ne_zero)),Polynomial.natDegree_mul_X_pow (offset a b) (Polynomial.C_ne_zero.mpr hv),
      Polynomial.natDegree_C,zero_add,hoff]
    omega
  have hdeg : (poly a).degree=(poly b*(C v*X^(offset a b))).degree := by
    rw [Polynomial.degree_eq_natDegree hnza,Polynomial.degree_eq_natDegree hterm,htermdeg]
  have hlead : (poly b*(C v*X^(offset a b))).leadingCoeff=(poly a).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_mul_X_pow,Polynomial.leadingCoeff_C]
    dsimp only [v]
    field_simp [Polynomial.leadingCoeff_ne_zero.mpr hnzb]
  have hdrop := Polynomial.degree_sub_lt hdeg hnza hlead.symm
  have hp : poly (remainderStep a b)=poly a-poly b*(C v*X^(offset a b)) := by
    rw [remainderStep_poly a b hlen,scale_leading a b ha hb hna hnb]
    ring
  rw [hp]
  exact hdrop

/-- The same emitted instruction list satisfies `remainderStep_length` with the displayed gate and query accounting. -/
theorem remainderStep_length (a b : List ℚ) (ha : Canonical a) (hb : Canonical b)
    (hna : a≠[]) (hnb : b≠[]) (hlen : b.length≤a.length) :
    (remainderStep a b).length < a.length := by
  have hd := remainderStep_degree a b ha hb hna hnb hlen
  have hca : Canonical (remainderStep a b) := trim_canonical _
  by_cases hz : remainderStep a b=[]
  · rw [hz,List.length_nil]
    exact List.length_pos_iff.mpr hna
  · have hnza := (canonical_nonzero a ha).mp hna
    have hnzr := (canonical_nonzero _ hca).mp hz
    rw [Polynomial.degree_eq_natDegree hnzr,Polynomial.degree_eq_natDegree hnza] at hd
    have hdn : (poly (remainderStep a b)).natDegree < (poly a).natDegree := by exact_mod_cast hd
    have hla := canonical_length a ha hna
    have hlr := canonical_length _ hca hz
    omega

end ActualYunDivisionStep


namespace ActualYunDivremCore
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunDivisionStep

/-- Construction for Low Zeros in the yun model. -/
def LowZeros (q a b : List ℚ) : Prop := ∀ k,k+b.length≤a.length → q.getD k 0=0
/-- Construction for Capacity in the yun model. -/
def Capacity (q a b : List ℚ) : Prop := a.length+1≤q.length+b.length

/-- Construction for core in the yun model. -/
def core : ℕ → List ℚ → List ℚ → List ℚ → List ℚ×List ℚ
  | 0,a,_,q => (trim q,a)
  | fuel+1,a,b,q =>
    if a≠[] ∧ b.length≤a.length then
      core fuel (remainderStep a b) b (q.set (offset a b) (scale a b))
    else (trim q,a)

/-- The finite construction in `Yun` satisfies `core_correct` under the displayed hypotheses. -/
theorem core_correct (fuel : ℕ) (a b q : List ℚ)
    (ha : Canonical a) (hb : Canonical b) (hnb : b≠[])
    (hz : LowZeros q a b) (hc : Capacity q a b) (hf : a.length≤fuel) :
    let out := core fuel a b q
    Canonical out.1 ∧ Canonical out.2 ∧
    poly out.1*poly b+poly out.2=poly q*poly b+poly a ∧
      (poly out.2).degree < (poly b).degree := by
  have hnzb : poly b≠0 := (canonical_nonzero b hb).mp hnb
  induction fuel generalizing a q with
  | zero =>
    have he : a=[] := List.length_eq_zero_iff.mp (by omega)
    subst a
    refine ⟨trim_canonical q,ha,?_,?_⟩
    · simp only [core,trim_poly]
    · simp only [core,poly_nil,Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => hnzb (Polynomial.degree_eq_bot.mp h))
  | succ fuel ih =>
    unfold core
    split_ifs with hloop
    · have hna := hloop.1
      have hlen := hloop.2
      let j := offset a b
      let v := scale a b
      let a' := remainderStep a b
      let q' := q.set j v
      have hshort : a'.length < a.length := remainderStep_length a b ha hb hna hnb hlen
      have hjb : j+b.length=a.length := by dsimp only [j,offset]; omega
      have hjq : j<q.length := by dsimp only [Capacity] at hc; omega
      have hqzero : q.getD j 0=0 := hz j (by omega)
      have hlength : q'.length=q.length := List.length_set
      have hz' : LowZeros q' a' b := by
        intro k hk
        have hkj : j≠k := by omega
        dsimp only [q']
        rw [List.getD_eq_getElem?_getD,List.getElem?_set_ne hkj]
        exact hz k (by omega)
      have hc' : Capacity q' a' b := by
        dsimp only [Capacity] at hc ⊢
        rw [hlength]
        omega
      have hf' : a'.length≤fuel := by omega
      have hca : Canonical a' := trim_canonical _
      have hout := ih a' q' hca hz' hc' hf'
      refine ⟨hout.1,hout.2.1,?_,hout.2.2.2⟩
      have hqpoly : poly q'=poly q+C v*X^j := by
        rw [show q'=q.set j v from rfl,poly_set q j v hjq,hqzero,sub_zero,
          ← Polynomial.C_mul_X_pow_eq_monomial]
      have hapoly : poly a'=poly a-C v*X^j*poly b := remainderStep_poly a b hlen
      rw [hout.2.2.1,hqpoly,hapoly]
      ring
    · refine ⟨trim_canonical q,ha,?_,?_⟩
      · rw [trim_poly]
      · by_cases he : a=[]
        · rw [he,poly_nil,Polynomial.degree_zero]
          exact bot_lt_iff_ne_bot.mpr (fun h => hnzb (Polynomial.degree_eq_bot.mp h))
        · have hnza := (canonical_nonzero a ha).mp he
          have hla := canonical_length a ha he
          have hlb := canonical_length b hb hnb
          have hltlen : a.length<b.length := lt_of_not_ge (fun hge => hloop ⟨he,hge⟩)
          have hlt : (poly a).natDegree < (poly b).natDegree := by omega
          rw [Polynomial.degree_eq_natDegree hnza,Polynomial.degree_eq_natDegree hnzb]
          exact_mod_cast hlt

end ActualYunDivremCore


namespace ActualYunDivrem
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunDivremCore

/-- Construction for divrem in the yun model. -/
def divrem (a b : List ℚ) : Option (List ℚ×List ℚ) :=
  let a := trim a
  let b := trim b
  if b=[] then none else some (core a.length a b (List.replicate (a.length+1-b.length) 0))

/-- The finite construction in `Yun` satisfies `zero_array` under the displayed hypotheses. -/
theorem zero_array (n : ℕ) (k : ℕ) : (List.replicate n (0 : ℚ)).getD k 0=0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate]
  split_ifs <;> rfl

/-- The finite construction in `Yun` satisfies `zero_poly` under the displayed hypotheses. -/
theorem zero_poly (n : ℕ) : poly (List.replicate n (0 : ℚ))=0 := by
  ext k
  rw [coeff,zero_array,Polynomial.coeff_zero]

/-- The finite construction in `Yun` satisfies `divrem_success` under the displayed hypotheses. -/
theorem divrem_success (a b : List ℚ) (hb : poly b≠0) :
    ∃ q r,divrem a b=some (q,r) ∧ Canonical q ∧ Canonical r ∧
      poly q=poly a/poly b ∧ poly r=poly a%poly b ∧ r.length < (trim b).length := by
  let A := trim a
  let B := trim b
  let Q0 : List ℚ := List.replicate (A.length+1-B.length) 0
  have hA : Canonical A := trim_canonical a
  have hB : Canonical B := trim_canonical b
  have hBnz : B≠[] := (canonical_nonzero B hB).mpr (by simpa only [B,trim_poly] using hb)
  have hz : LowZeros Q0 A B := by intro k _; exact zero_array _ k
  have hc : Capacity Q0 A B := by dsimp only [Capacity,Q0]; rw [List.length_replicate]; omega
  have hout := core_correct A.length A B Q0 hA hB hBnz hz hc (Nat.le_refl _)
  let out := core A.length A B Q0
  have hpoly : poly out.1*poly b+poly out.2=poly a := by
    simpa only [A,B,Q0,zero_poly,trim_poly,zero_mul,zero_add] using hout.2.2.1
  have hdegree : (poly out.2).degree < (poly b).degree := by
    simpa only [B,trim_poly] using hout.2.2.2
  have hmod : poly a%poly b=poly out.2 := by
    have hdiv : poly b ∣ poly a-poly out.2 := ⟨poly out.1,by rw [← hpoly]; ring⟩
    have h := Polynomial.mod_eq_of_dvd_sub hdiv
    rw [(Polynomial.mod_eq_self_iff hb).mpr hdegree] at h
    exact h
  have hquot : poly out.1=poly a/poly b := by
    have hstd : (poly a/poly b)*poly b+(poly a%poly b)=poly a := by
      simpa only [mul_comm] using EuclideanDomain.div_add_mod (poly a) (poly b)
    rw [hmod] at hstd
    apply mul_right_cancel₀ hb
    exact add_right_cancel (hpoly.trans hstd.symm)
  have hlength : out.2.length<B.length := by
    by_cases he : out.2=[]
    · rw [he,List.length_nil]
      exact List.length_pos_iff.mpr hBnz
    · have hrnz := (canonical_nonzero out.2 hout.2.1).mp he
      have hBpoly : poly B≠0 := by simpa only [B,trim_poly] using hb
      have hd : (poly out.2).degree < (poly B).degree := by simpa only [B,trim_poly] using hdegree
      rw [Polynomial.degree_eq_natDegree hrnz,Polynomial.degree_eq_natDegree hBpoly] at hd
      have hdn : (poly out.2).natDegree < (poly B).natDegree := by exact_mod_cast hd
      have hlr := canonical_length out.2 hout.2.1 he
      have hlb := canonical_length B hB hBnz
      omega
  refine ⟨out.1,out.2,?_,hout.1,hout.2.1,hquot,hmod.symm,hlength⟩
  dsimp only [divrem]
  rw [ite_eq_right hBnz]



end ActualYunDivrem


namespace ActualYunMonic
open Polynomial ActualYunRationalArray ActualYunRationalCanonical

/-- Construction for monic in the yun model. -/
def monic (a : List ℚ) : List ℚ :=
  let a := trim a
  if a=[] then [] else a.map (fun c => c/a.getD (a.length-1) 0)

/-- The finite construction in `Yun` satisfies `map_div_poly` under the displayed hypotheses. -/
theorem map_div_poly (a : List ℚ) (d : ℚ) :
    poly (a.map (fun c => c/d))=poly a*C d⁻¹ := by
  ext k
  rw [coeff,Polynomial.coeff_mul_C,coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : a[k]? <;> simp [div_eq_mul_inv]

/-- The finite construction in `Yun` satisfies `map_div_canonical` under the displayed hypotheses. -/
theorem map_div_canonical (a : List ℚ) (ha : Canonical a) (d : ℚ) (hd : d≠0) :
    Canonical (a.map (fun c => c/d)) := by
  rcases trim_shape a with he | ⟨b,x,he,hx⟩
  · rw [ha] at he
    rw [he]
    rfl
  · rw [ha] at he
    rw [he]
    have hdiv : x/d≠0 := div_ne_zero hx hd
    simp [Canonical,trim,List.map_append,hdiv]

/-- The finite construction in `Yun` satisfies `monic_poly` under the displayed hypotheses. -/
theorem monic_poly (a : List ℚ) : poly (monic a)=normalize (poly a) := by
  let t := trim a
  have ht : Canonical t := trim_canonical a
  unfold monic
  dsimp only
  split_ifs with he
  · rw [poly_nil]
    have hp : poly a=0 := by rw [← trim_poly a,he,poly_nil]
    rw [hp,normalize_zero]
  · have hnz : poly t≠0 := (canonical_nonzero t ht).mp he
    have hl := canonical_leading t ht he
    rw [map_div_poly,← hl]
    change poly t*C (poly t).leadingCoeff⁻¹=normalize (poly a)
    rw [← trim_poly a]
    rw [normalize_apply,Polynomial.coe_normUnit,
      CommGroupWithZero.coe_normUnit ℚ (Polynomial.leadingCoeff_ne_zero.mpr hnz)]

/-- The finite construction in `Yun` satisfies `monic_canonical` under the displayed hypotheses. -/
theorem monic_canonical (a : List ℚ) : Canonical (monic a) := by
  unfold monic
  dsimp only
  split_ifs with he
  · rfl
  · have ht := trim_canonical a
    have hp := (canonical_nonzero (trim a) ht).mp he
    have hd : (trim a).getD ((trim a).length-1) 0≠0 := by
      rw [← canonical_leading _ ht he]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    exact map_div_canonical _ ht _ hd



end ActualYunMonic


namespace ActualYunGcd
open Polynomial ActualYunInitial ActualYunStep
open ActualYunRationalArray ActualYunRationalCanonical ActualYunMonic

/-- The finite construction in `Yun` satisfies `gcdQ_remainder` under the displayed hypotheses. -/
theorem gcdQ_remainder (A B : ℚ[X]) : gcdQ A B=gcdQ B (A%B) := by
  rw [gcdQ_eq_gcd,gcdQ_eq_gcd]
  apply dvd_antisymm_of_normalize_eq (normalize_gcd A B) (normalize_gcd B (A%B))
  · have hA := gcd_dvd_left A B
    have hB := gcd_dvd_right A B
    exact dvd_gcd hB ((EuclideanDomain.dvd_mod_iff hB).mpr hA)
  · have hB := gcd_dvd_left B (A%B)
    have hR := gcd_dvd_right B (A%B)
    exact dvd_gcd ((EuclideanDomain.dvd_mod_iff hB).mp hR) hB

/-- Construction for gcd Core in the yun model. -/
def gcdCore : ℕ → List ℚ → List ℚ → Option (List ℚ)
  | 0,_,_ => none
  | fuel+1,a,b =>
    if b=[] then some (monic a)
    else match ActualYunDivrem.divrem a b with
      | none => none
      | some (_,r) => gcdCore fuel b r

/-- The finite construction in `Yun` satisfies `gcdCore_success` under the displayed hypotheses. -/
theorem gcdCore_success (fuel : ℕ) (a b : List ℚ) (ha : Canonical a) (hb : Canonical b)
    (hf : b.length<fuel) : ∃ c,gcdCore fuel a b=some c ∧ Canonical c ∧
      poly c=gcdQ (poly a) (poly b) := by
  induction fuel generalizing a b with
  | zero => omega
  | succ fuel ih =>
    by_cases he : b=[]
    · refine ⟨monic a,?_,monic_canonical a,?_⟩
      · simp only [gcdCore,he,ite_true]
      · rw [monic_poly,he,poly_nil,gcdQ_eq_gcd,gcd_zero_right]
    · have hpolyB : poly b≠0 := (canonical_nonzero b hb).mp he
      obtain ⟨q,r,hqr,hq,hr,hqpoly,hrpoly,hlen⟩ := ActualYunDivrem.divrem_success a b hpolyB
      rw [hb] at hlen
      have hfr : r.length<fuel := by omega
      obtain ⟨c,hc,hcanon,hvalue⟩ := ih b r hb hr hfr
      refine ⟨c,?_,hcanon,?_⟩
      · simp only [gcdCore,ite_eq_right he,hqr]
        exact hc
      · rw [hvalue,hrpoly,← gcdQ_remainder]

/-- Construction for poly Gcd in the yun model. -/
def polyGcd (a b : List ℚ) : Option (List ℚ) := gcdCore (b.length+1) a b

/-- The finite construction in `Yun` satisfies `polyGcd_success` under the displayed hypotheses. -/
theorem polyGcd_success (a b : List ℚ) (ha : Canonical a) (hb : Canonical b) :
    ∃ c,polyGcd a b=some c ∧ Canonical c ∧ poly c=gcdQ (poly a) (poly b) :=
  gcdCore_success (b.length+1) a b ha hb (Nat.lt_succ_self _)



end ActualYunGcd


namespace ActualYunArrayInitialization
open Polynomial ActualYunInitial ActualYunStep
open ActualYunRationalArray ActualYunRationalCanonical ActualYunMonic ActualYunGcd

/-- Construction for derivative in the yun model. -/
def derivative (a : List ℚ) : List ℚ := trim (List.ofFn
  (fun i : Fin (a.length-1) => ((i.val+1 : ℕ) : ℚ)*a.getD (i.val+1) 0))

/-- The finite construction in `Yun` satisfies `derivative_poly` under the displayed hypotheses. -/
theorem derivative_poly (a : List ℚ) : poly (derivative a)=(poly a).derivative := by
  rw [derivative,trim_poly]
  ext k
  rw [coeff,Polynomial.coeff_derivative,coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  by_cases hk : k<a.length-1
  · rw [dite_eq_left hk,Option.getD_some]
    push_cast
    ring
  · rw [dite_eq_right hk,Option.getD_none]
    have ha : a.length≤k+1 := by omega
    rw [List.getElem?_eq_none ha,Option.getD_none,zero_mul]

/-- Construction for exact Div in the yun model. -/
def exactDiv (a b : List ℚ) : Option (List ℚ) :=
  match ActualYunDivrem.divrem a b with
  | none => none
  | some (q,r) => if r=[] then some q else none

/-- The finite construction in `Yun` satisfies `exactDiv_success` under the displayed hypotheses. -/
theorem exactDiv_success (a b : List ℚ) (hb : poly b≠0) (hd : poly b∣poly a) :
    ∃ q,exactDiv a b=some q ∧ Canonical q ∧ poly q=poly a/poly b := by
  obtain ⟨q,r,hqr,hq,hr,hquot,hrem,_⟩ := ActualYunDivrem.divrem_success a b hb
  have hr0 : r=[] := by
    by_contra hn
    have hpoly := (canonical_nonzero r hr).mp hn
    rw [hrem,EuclideanDomain.mod_eq_zero.mpr hd] at hpoly
    exact hpoly rfl
  refine ⟨q,?_,hq,hquot⟩
  simp only [exactDiv,hqr,hr0,ite_true]

/-- Construction for source Initialize in the yun model. -/
def sourceInitialize (a : List ℚ) : Option (List ℚ×List ℚ×List ℚ) :=
  let A := monic a
  match polyGcd A (derivative A) with
  | none => none
  | some c => match exactDiv A c with
    | none => none
    | some w => some (A,c,w)

/-- The finite construction in `Yun` satisfies `initialize_success` under the displayed hypotheses. -/
theorem initialize_success (a : List ℚ) (ha : poly a≠0) :
    ∃ A c w,sourceInitialize a=some (A,c,w) ∧ Canonical A ∧ Canonical c ∧ Canonical w ∧
      poly A=normalize (poly a) ∧ poly c=gcdQ (poly A) (poly A).derivative ∧
      poly w=poly A/gcdQ (poly A) (poly A).derivative ∧
      ((poly w).map (Rat.castHom ℂ)).Separable := by
  let A := monic a
  have hA : Canonical A := monic_canonical a
  have hApoly : poly A=normalize (poly a) := monic_poly a
  have hAnz : poly A≠0 := by
    rw [hApoly]
    intro hz
    exact ha (_root_.normalize_eq_zero.mp hz)
  have hD : Canonical (derivative A) := trim_canonical _
  obtain ⟨c,hc,hC,hCpoly⟩ := polyGcd_success A (derivative A) hA hD
  rw [derivative_poly] at hCpoly
  have hCnz : poly c≠0 := by
    rw [hCpoly,gcdQ_eq_gcd]
    exact gcd_ne_zero_of_left hAnz
  have hdiv : poly c∣poly A := by rw [hCpoly,gcdQ_eq_gcd]; exact gcd_dvd_left _ _
  obtain ⟨w,hw,hW,hWpoly⟩ := exactDiv_success A c hCnz hdiv
  have hWpoly' : poly w=poly A/gcdQ (poly A) (poly A).derivative := by rw [hWpoly,hCpoly]
  have hsep : ((poly w).map (Rat.castHom ℂ)).Separable := by
    rw [hWpoly']
    exact initial_rational_quotient_separable (poly A) hAnz
  refine ⟨A,c,w,?_,hA,hC,hW,hApoly,hCpoly,hWpoly',hsep⟩
  dsimp only [A] at hc hw ⊢
  simp only [sourceInitialize,hc,hw]



end ActualYunArrayInitialization


namespace ActualYunPrimitive
open Polynomial ActualYunRationalArray ActualYunRationalCanonical
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

/-- Construction for primitive in the yun model. -/
def primitive (a : List ℚ) : List ℤ := sourceIntegerTarget (trim a)
/-- Construction for primitive Scale in the yun model. -/
def primitiveScale (a : List ℚ) : ℚ :=
  (sourceDenominator (trim a) : ℚ)/(sourceContent (trim a) : ℚ)

/-- The finite construction in `Yun` satisfies `nonzero_member` under the displayed hypotheses. -/
theorem nonzero_member (a : List ℚ) (ha : poly a≠0) : ∃ q∈trim a,q≠0 := by
  rcases trim_shape a with he | ⟨b,x,he,hx⟩
  · have hz : poly a=0 := by rw [← trim_poly a,he,poly_nil]
    exact (ha hz).elim
  · exact ⟨x,by rw [he]; simp,hx⟩

/-- The finite construction in `Yun` satisfies `primitiveScale_pos` under the displayed hypotheses. -/
theorem primitiveScale_pos (a : List ℚ) (ha : poly a≠0) : 0<primitiveScale a := by
  have hD : (0 : ℚ)<sourceDenominator (trim a) := by exact_mod_cast sourceDenominator_pos (trim a)
  have hG : (0 : ℚ)<sourceContent (trim a) := by
    exact_mod_cast sourceContent_pos (trim a) (nonzero_member a ha)
  exact div_pos hD hG

/-- The finite construction in `Yun` satisfies `primitive_polynomial` under the displayed hypotheses. -/
theorem primitive_polynomial (a : List ℚ) (ha : poly a≠0) :
    rootIntegerListPolynomial (primitive a)=
      C (primitiveScale a : ℂ)*(poly a).map (Rat.castHom ℂ) := by
  have h := sourceIntegerTarget_polynomial (trim a) (nonzero_member a ha)
  change rootIntegerListPolynomial (primitive a)=
    C ((sourceDenominator (trim a) : ℂ)/(sourceContent (trim a) : ℂ))*
      (poly (trim a)).map (Rat.castHom ℂ) at h
  rw [trim_poly] at h
  simpa only [primitiveScale,Rat.cast_div,Rat.cast_natCast] using h

/-- The finite construction in `Yun` satisfies `primitive_separable` under the displayed hypotheses. -/
theorem primitive_separable (a : List ℚ) (ha : poly a≠0)
    (hsep : ((poly a).map (Rat.castHom ℂ)).Separable) :
    (rootIntegerListPolynomial (primitive a)).Separable := by
  have hs : (primitiveScale a : ℂ)≠0 := by
    exact_mod_cast (primitiveScale_pos a ha).ne'
  rw [primitive_polynomial a ha]
  exact Polynomial.Separable.unit_mul (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hs)) hsep

/-- The finite construction in `Yun` satisfies `primitive_degree` under the displayed hypotheses. -/
theorem primitive_degree (a : List ℚ) (ha : poly a≠0) :
    (rootIntegerListPolynomial (primitive a)).natDegree=(poly a).natDegree := by
  have hs : (primitiveScale a : ℂ)≠0 := by exact_mod_cast (primitiveScale_pos a ha).ne'
  rw [primitive_polynomial a ha,Polynomial.natDegree_C_mul hs,
    Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℂ).injective]

/-- The same emitted instruction list satisfies `primitive_length` with the displayed gate and query accounting. -/
theorem primitive_length (a : List ℚ) : (primitive a).length=(trim a).length := by
  simp only [primitive,sourceIntegerTarget,sourceRawIntegers,List.length_map]

/-- Construction for integer Poly Q in the yun model. -/
def integerPolyQ (a : List ℤ) : ℚ[X] := (⟨⟨a.toFinsupp⟩⟩ : ℤ[X]).map (Int.castRingHom ℚ)

/-- The finite construction in `Yun` satisfies `integerPolyQ_map` under the displayed hypotheses. -/
theorem integerPolyQ_map (a : List ℤ) :
    (integerPolyQ a).map (Rat.castHom ℂ)=rootIntegerListPolynomial a := by
  unfold integerPolyQ rootIntegerListPolynomial
  rw [Polynomial.map_map]
  congr 1

/-- The finite construction in `Yun` satisfies `primitive_polynomialQ` under the displayed hypotheses. -/
theorem primitive_polynomialQ (a : List ℚ) (ha : poly a≠0) :
    integerPolyQ (primitive a)=C (primitiveScale a)*poly a := by
  apply Polynomial.map_injective (Rat.castHom ℂ) (Rat.castHom ℂ).injective
  rw [integerPolyQ_map,Polynomial.map_mul,Polynomial.map_C]
  exact primitive_polynomial a ha

/-- Decoding a stored primitive integer factor back to its monic rational
polynomial recovers the source monic factor exactly, not its raw array. -/
theorem primitive_normalize (a : List ℚ) (ha : poly a≠0) :
    normalize (integerPolyQ (primitive a))=normalize (poly a) := by
  have hu : IsUnit (C (primitiveScale a) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (primitiveScale_pos a ha).ne')
  rw [primitive_polynomialQ a ha,normalize_mul,normalize_eq_one.mpr hu,one_mul]



end ActualYunPrimitive


namespace ActualYunArrayStep
open Polynomial ActualYunInitial ActualYunStep
open ActualYunRationalArray ActualYunRationalCanonical ActualYunMonic ActualYunGcd
open ActualYunArrayInitialization ActualYunPrimitive
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Data and invariants for Array State in the yun model. -/
structure ArrayState where
  w : List ℚ
  c : List ℚ
  exponent : ℕ
  factors : List (List ℤ×ℕ)

/-- Construction for decode in the yun model. -/
def decode (s : ArrayState) : State :=
  ⟨poly s.w,poly s.c,s.exponent,
    s.factors.map (fun f => (normalize (integerPolyQ f.1),f.2))⟩

/-- Construction for Factor Good in the yun model. -/
def FactorGood (f : List ℤ×ℕ) : Prop :=
  (rootIntegerListPolynomial f.1).Separable ∧
    0<(rootIntegerListPolynomial f.1).natDegree ∧
    f.1.length=(rootIntegerListPolynomial f.1).natDegree+1 ∧
    f.1.getD (f.1.length-1) 0≠0 ∧ 0<f.2

/-- Data and invariants for Array Invariant in the yun model. -/
structure ArrayInvariant (F : ℚ[X]) (s : ArrayState) : Prop where
  canonical_w : Canonical s.w
  canonical_c : Canonical s.c
  model : Invariant F (decode s)
  output_order : ActualYunOutputBounds.OutputBound (decode s)
  outputs : ∀ f∈s.factors,FactorGood f

/-- The finite construction in `Yun` satisfies `primitive_good` under the displayed hypotheses. -/
theorem primitive_good (a : List ℚ) (ha : Canonical a) (hm : (poly a).Monic)
    (hs : ((poly a).map (Rat.castHom ℂ)).Separable) (hd : 0<(poly a).natDegree)
    (e : ℕ) (he : 0<e) : FactorGood (primitive a,e) := by
  have hna : a≠[] := (canonical_nonzero a ha).mpr hm.ne_zero
  have hdegree := primitive_degree a hm.ne_zero
  have hlen : (primitive a).length=(rootIntegerListPolynomial (primitive a)).natDegree+1 := by
    rw [primitive_length a,ha,hdegree]
    exact canonical_length a ha hna
  have hp : rootIntegerListPolynomial (primitive a)≠0 := by
    intro hz
    rw [hz,Polynomial.natDegree_zero] at hdegree
    omega
  have hidx : (rootIntegerListPolynomial (primitive a)).natDegree=(primitive a).length-1 := by omega
  have htop : (primitive a).getD ((primitive a).length-1) 0≠0 := by
    have hc : (((primitive a).getD ((primitive a).length-1) 0 : ℤ) : ℂ)≠0 := by
      rw [← rootIntegerListPolynomial_coeff,← hidx]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    exact_mod_cast hc
  have hpos : 0<(rootIntegerListPolynomial (primitive a)).natDegree := by
    rw [primitive_degree a hm.ne_zero]
    exact hd
  exact ⟨primitive_separable a hm.ne_zero hs,hpos,hlen,htop,he⟩

/-- Construction for advance in the yun model. -/
def advance (s : ArrayState) : Option ArrayState :=
  match polyGcd s.w s.c with
  | none => none
  | some y => match exactDiv s.w y with
    | none => none
    | some z =>
      let factors := if 1<z.length then s.factors++[(primitive z,s.exponent)] else s.factors
      match exactDiv s.c y with
      | none => none
      | some c => some ⟨y,c,s.exponent+1,factors⟩

/-- The finite construction in `Yun` satisfies `advance_success` under the displayed hypotheses. -/
theorem advance_success (F : ℚ[X]) (s : ArrayState) (h : ArrayInvariant F s) :
    ∃ t,advance s=some t ∧ ArrayInvariant F t ∧ decode t=ActualYunStep.step (decode s) := by
  have hwm : (poly s.w).Monic := h.model.w_monic
  have hcm : (poly s.c).Monic := h.model.c_monic
  obtain ⟨y,hy,hY,hYpoly⟩ := polyGcd_success s.w s.c h.canonical_w h.canonical_c
  have hym : (poly y).Monic := by rw [hYpoly]; exact gcdQ_monic _ _ hwm.ne_zero
  have hydw : poly y∣poly s.w := by rw [hYpoly,gcdQ_eq_gcd]; exact gcd_dvd_left _ _
  have hydc : poly y∣poly s.c := by rw [hYpoly,gcdQ_eq_gcd]; exact gcd_dvd_right _ _
  obtain ⟨z,hz,hZ,hZpoly⟩ := exactDiv_success s.w y hym.ne_zero hydw
  obtain ⟨c,hc,hC,hCpoly⟩ := exactDiv_success s.c y hym.ne_zero hydc
  have hyz : poly y*poly z=poly s.w := by
    rw [hZpoly]
    exact EuclideanDomain.mul_div_cancel' hym.ne_zero hydw
  have hzm : (poly z).Monic := hym.of_mul_monic_left (hyz.symm ▸ hwm)
  have hwsep : ((poly s.w).map (Rat.castHom ℂ)).Separable := h.model.w_separable
  have hzs : ((poly z).map (Rat.castHom ℂ)).Separable := hwsep.of_dvd
    (Polynomial.map_dvd _ ⟨poly y,by rw [mul_comm,hyz]⟩)
  have hzn : z≠[] := (canonical_nonzero z hZ).mpr hzm.ne_zero
  have hzlen := canonical_length z hZ hzn
  have htest : (1<z.length) ↔ 0<(poly s.w/gcdQ (poly s.w) (poly s.c)).natDegree := by
    rw [← hYpoly,← hZpoly]
    omega
  let t : ArrayState := ⟨y,c,s.exponent+1,
    if 1<z.length then s.factors++[(primitive z,s.exponent)] else s.factors⟩
  have hdecode : decode t=ActualYunStep.step (decode s) := by
    dsimp only [decode,t,ActualYunStep.step]
    congr 1
    · simpa only [hYpoly] using hCpoly
    · by_cases ht : 1<z.length
      · rw [ite_eq_left ht,ite_eq_left (htest.mp ht),List.map_append,List.map_cons,List.map_nil,
          primitive_normalize z hzm.ne_zero,hzm.normalize_eq_self]
        congr 2
        rw [hZpoly,hYpoly]
      · rw [ite_eq_right ht,ite_eq_right (fun hp => ht (htest.mpr hp))]
  have hinv : ArrayInvariant F t := by
    refine ⟨hY,hC,?_,?_,?_⟩
    · rw [hdecode]
      exact step_invariant F (decode s) h.model
    · rw [hdecode]
      exact ActualYunOutputBounds.step_output_bound (decode s) h.output_order
    · intro f hf
      change f∈(if 1<z.length then s.factors++[(primitive z,s.exponent)] else s.factors) at hf
      split_ifs at hf with ht
      · rcases List.mem_append.mp hf with hold | hnew
        · exact h.outputs f hold
        · have heq := List.mem_singleton.mp hnew
          subst f
          exact primitive_good z hZ hzm hzs (by omega) s.exponent h.model.exponent_pos
      · exact h.outputs f hf
  refine ⟨t,?_,hinv,hdecode⟩
  dsimp only [t]
  simp only [advance,hy,hz,hc]

end ActualYunArrayStep


namespace ActualYunArrayLoop
open Polynomial ActualYunInitial ActualYunStep ActualYunLoop ActualYunOutputBounds
open ActualYunRationalArray ActualYunRationalCanonical ActualYunMonic ActualYunGcd
open ActualYunArrayInitialization ActualYunPrimitive ActualYunArrayStep

/-- The finite construction in `Yun` satisfies `while_iff` under the displayed hypotheses. -/
theorem while_iff (F : ℚ[X]) (s : ArrayState) (h : ArrayInvariant F s) :
    1<s.w.length ↔ 0<(decode s).w.natDegree := by
  have hn : s.w≠[] := (canonical_nonzero s.w h.canonical_w).mpr h.model.w_monic.ne_zero
  have hl := canonical_length s.w h.canonical_w hn
  change 1<s.w.length ↔ 0<(poly s.w).natDegree
  omega

/-- Construction for guarded Advance in the yun model. -/
def guardedAdvance (limit : ℕ) (s : ArrayState) : Option ArrayState :=
  match advance s with
  | none => none
  | some t => if limit<t.exponent then none else some t

/-- Construction for array Run in the yun model. -/
def arrayRun : ℕ → ℕ → ArrayState → Option ArrayState
  | 0,_,s => if 1<s.w.length then none else some s
  | fuel+1,limit,s =>
    if 1<s.w.length then match guardedAdvance limit s with
      | none => none
      | some t => arrayRun fuel limit t
    else some s

/-- The finite construction in `Yun` satisfies `arrayRun_success` under the displayed hypotheses. -/
theorem arrayRun_success (F : ℚ[X]) (fuel limit : ℕ) (s : ArrayState) (h : ArrayInvariant F s)
    (hbudget : ActualYunStep.measure (decode s)+s.exponent≤limit)
    (hfuel : ActualYunStep.measure (decode s)≤fuel) :
    ∃ t,arrayRun fuel limit s=some t ∧ ArrayInvariant F t ∧
      decode t=ActualYunLoop.run fuel (decode s) ∧ t.w.length≤1 ∧ t.exponent≤limit := by
  induction fuel generalizing s with
  | zero =>
    have hw : ¬1<s.w.length := by
      intro hw
      have hp := (while_iff F s h).mp hw
      dsimp only [ActualYunStep.measure] at hfuel
      omega
    refine ⟨s,?_,h,rfl,by omega,by omega⟩
    simp only [arrayRun,ite_eq_right hw]
  | succ fuel ih =>
    by_cases hw : 1<s.w.length
    · have hpos := (while_iff F s h).mp hw
      obtain ⟨t,ht,hinv,hdecode⟩ := advance_success F s h
      have hmeasure : ActualYunStep.measure (decode t) < ActualYunStep.measure (decode s) := by
        rw [hdecode]
        exact step_measure_strict F (decode s) h.model hpos
      have he : t.exponent=s.exponent+1 := by
        have hp := congrArg State.exponent hdecode
        exact hp
      have hbudget' : ActualYunStep.measure (decode t)+t.exponent≤limit := by omega
      have hfuel' : ActualYunStep.measure (decode t)≤fuel := by omega
      have hguard : ¬limit<t.exponent := by omega
      have hstep : guardedAdvance limit s=some t := by simp only [guardedAdvance,ht,ite_eq_right hguard]
      obtain ⟨u,hu,huinv,hudecode,hwlen,hucounter⟩ := ih t hinv hbudget' hfuel'
      refine ⟨u,?_,huinv,?_,hwlen,hucounter⟩
      · simp only [arrayRun,ite_eq_left hw,hstep]
        exact hu
      · rw [hudecode,ActualYunLoop.run,ite_eq_left hpos,← hdecode]
    · refine ⟨s,?_,h,?_,by omega,by omega⟩
      · simp only [arrayRun,ite_eq_right hw]
      · have hnot : ¬0<(decode s).w.natDegree := fun hp => hw ((while_iff F s h).mpr hp)
        simp only [ActualYunLoop.run,ite_eq_right hnot]

/-- The finite construction in `Yun` satisfies `initialize_array_invariant` under the displayed hypotheses. -/
theorem initialize_array_invariant (a : List ℚ) (ha : poly a≠0) (hd : 0<(poly a).natDegree) :
    ∃ A s,sourceInitialize a=some (A,s.c,s.w) ∧
      ArrayInvariant (normalize (poly a)) s ∧
      decode s=ActualYunLoop.initial (normalize (poly a)) ∧
      s.exponent=1 ∧ A.length=(normalize (poly a)).natDegree+1 := by
  obtain ⟨A,c,w,hinit,hA,hC,hW,hApoly,hCpoly,hWpoly,hsep⟩ := initialize_success a ha
  let s : ArrayState := ⟨w,c,1,[]⟩
  let F := normalize (poly a)
  have hnz : F≠0 := by intro hz; exact ha (_root_.normalize_eq_zero.mp hz)
  have hF : F.Monic := Polynomial.monic_normalize ha
  have hdegree : F.natDegree=(poly a).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_normalize (p := poly a))
  have hFpos : 0<F.natDegree := by omega
  have hdec : decode s=ActualYunLoop.initial F := by
    change State.mk (poly w) (poly c) 1 [] =
      State.mk (F/gcdQ F F.derivative) (gcdQ F F.derivative) 1 []
    rw [hCpoly,hWpoly,hApoly]
  have hmodel : Invariant F (decode s) := by
    rw [hdec]
    exact initial_invariant F hF hFpos
  have horder : OutputBound (decode s) := by
    intro f hf
    cases hf
  have hgood : ArrayInvariant F s := ⟨hW,hC,hmodel,horder,by intro f hf; cases hf⟩
  have hAnz : A≠[] := (canonical_nonzero A hA).mpr (by rw [hApoly]; exact hnz)
  have hlen : A.length=F.natDegree+1 := by rw [canonical_length A hA hAnz,hApoly]
  exact ⟨A,s,hinit,hgood,hdec,rfl,hlen⟩

/-- Construction for squarefree Arrays in the yun model. -/
def squarefreeArrays (a : List ℚ) : Option (List (List ℤ×ℕ)) :=
  match sourceInitialize a with
  | none => none
  | some (A,c,w) =>
    (arrayRun (A.length-1) A.length ⟨w,c,1,[]⟩).map (fun s => s.factors)

/-- The finite construction in `Yun` satisfies `generated_integer_factors` under the displayed hypotheses. -/
theorem generated_integer_factors (a : List ℚ) (ha : poly a≠0) (hd : 0<(poly a).natDegree) :
    ∃ out,squarefreeArrays a=some out ∧
      normalize (poly a)=(out.map (fun f => normalize (integerPolyQ f.1)^f.2)).prod ∧
      ∀ f∈out,FactorGood f ∧ f.2≤(poly a).natDegree := by
  let F := normalize (poly a)
  obtain ⟨A,s,hinit,hinv,hdecode,he,hlen⟩ := initialize_array_invariant a ha hd
  change A.length=F.natDegree+1 at hlen
  have hnz : F≠0 := by intro hz; exact ha (_root_.normalize_eq_zero.mp hz)
  have hF : F.Monic := Polynomial.monic_normalize ha
  have hm : ActualYunStep.measure (decode s)=F.natDegree := by
    rw [hdecode]
    exact initial_measure F hF
  have hb : ActualYunStep.measure (decode s)+s.exponent≤A.length := by omega
  have hfl : ActualYunStep.measure (decode s)≤A.length-1 := by omega
  obtain ⟨t,ht,htinv,htdecode,hwlen,hebound⟩ := arrayRun_success F (A.length-1) A.length s hinv hb hfl
  have hwnz : t.w≠[] := (canonical_nonzero t.w htinv.canonical_w).mpr htinv.model.w_monic.ne_zero
  have hwdegree : (decode t).w.natDegree=0 := by
    have hh := canonical_length t.w htinv.canonical_w hwnz
    change (poly t.w).natDegree=0
    omega
  have hw1 : (decode t).w=1 := htinv.model.w_monic.natDegree_eq_zero.mp hwdegree
  have hprod := (terminal_product F (decode t) htinv.model hw1).2
  have hdegree : F.natDegree=(poly a).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_normalize (p := poly a))
  refine ⟨t.factors,?_,?_,?_⟩
  · dsimp only [squarefreeArrays]
    rw [hinit]
    dsimp only
    have hs : s=ArrayState.mk s.w s.c 1 [] := by
      have hfields := hdecode
      have heq : s.factors=[] := by
        have hp := congrArg State.factors hfields
        change List.map (fun f => (normalize (integerPolyQ f.1),f.2)) s.factors=[] at hp
        exact List.map_eq_nil_iff.mp hp
      cases s with
      | mk w c e fs =>
        change e=1 at he
        change fs=[] at heq
        change ArrayState.mk w c e fs=ArrayState.mk w c 1 []
        rw [he,heq]
    rw [← hs,ht]
    rfl
  · change F=(t.factors.map (fun f => normalize (integerPolyQ f.1)^f.2)).prod
    simpa only [factorProduct,decode,List.map_map,Function.comp_def] using hprod
  · intro f hf
    have hmem : (normalize (integerPolyQ f.1),f.2)∈(decode t).factors := List.mem_map.mpr ⟨f,hf,rfl⟩
    have ho := htinv.output_order _ hmem
    change 0<(normalize (integerPolyQ f.1)).natDegree ∧ f.2<t.exponent at ho
    exact ⟨htinv.outputs f hf,by omega⟩



end ActualYunArrayLoop


namespace ActualYunPrimitiveContent
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

/-- Construction for integer Poly in the yun model. -/
def integerPoly (a : List ℤ) : ℤ[X] := ⟨⟨a.toFinsupp⟩⟩

/-- The finite construction in `Yun` satisfies `integerCoeff` under the displayed hypotheses. -/
theorem integerCoeff (a : List ℤ) (i : ℕ) :
    (integerPoly a).coeff i=a.getD i 0 := List.toFinsupp_apply _ _

/-- The finite construction in `Yun` satisfies `dvd_gcdFold` under the displayed hypotheses. -/
theorem dvd_gcdFold (xs : List ℤ) (d s : ℕ) (hs : d∣s)
    (hx : ∀ x∈xs,d∣x.natAbs) : d∣xs.foldl (fun g x => Nat.gcd g x.natAbs) s := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih _ (Nat.dvd_gcd hs (hx x (by simp))) (fun y hy => hx y (by simp [hy]))

/-- The finite construction in `Yun` satisfies `primitive_isPrimitive` under the displayed hypotheses. -/
theorem primitive_isPrimitive (a : List ℚ) (ha : poly a≠0) :
    (integerPoly (primitive a)).IsPrimitive := by
  have hmember : ∃ q∈trim a,q≠0 := by
    rcases trim_shape a with hz | ⟨b,x,he,hx⟩
    · have hzero : poly a=0 := by rw [← trim_poly a,hz,poly_nil]
      exact (ha hzero).elim
    · exact ⟨x,by rw [he]; simp,hx⟩
  let g := sourceContent (trim a)
  have hg : g≠0 := (sourceContent_pos (trim a) hmember).ne'
  intro r hr
  have hcoeff : ∀ i,r∣(primitive a).getD i 0 := by
    intro i
    rw [← integerCoeff]
    exact (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr i
  have hall : ∀ x∈sourceRawIntegers (trim a),r.natAbs*g∣x.natAbs := by
    intro x hx
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem hx
    have hlen : (primitive a).length=(sourceRawIntegers (trim a)).length := by
      simp only [primitive,sourceIntegerTarget,List.length_map]
    have hrd : r∣x/(g : ℤ) := by
      have he : (primitive a).getD i 0=x/(g : ℤ) := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp only [primitive,sourceIntegerTarget,List.getElem_map,hix]
        rfl
      rw [← he]
      exact hcoeff i
    have hcancel : x/(g : ℤ)*(g : ℤ)=x :=
      Int.ediv_mul_cancel (sourceContent_dvd (trim a) x hx)
    have hmul : r*(g : ℤ)∣x := by
      obtain ⟨k,hk⟩ := hrd
      refine ⟨k,?_⟩
      rw [← hcancel,hk]
      ring
    have hn := Int.natAbs_dvd_natAbs.mpr hmul
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hn
  have hdiv : r.natAbs*g∣g := dvd_gcdFold _ _ 0 (dvd_zero _) hall
  have hone : r.natAbs∣1 := (mul_dvd_mul_iff_right hg).mp (by simpa only [one_mul] using hdiv)
  exact Int.isUnit_iff_natAbs_eq.mpr (Nat.dvd_one.mp hone)

end ActualYunPrimitiveContent


namespace ActualYunIntegerProduct
open Polynomial ActualYunInitial ActualYunStep ActualYunLoop ActualYunOutputBounds
open ActualYunRationalArray ActualYunRationalCanonical ActualYunMonic ActualYunGcd
open ActualYunArrayInitialization ActualYunPrimitive ActualYunArrayStep ActualYunArrayLoop
open ActualYunPrimitiveContent

/-- Construction for Primitive Outputs in the yun model. -/
def PrimitiveOutputs (s : ArrayState) : Prop :=
  ∀ f∈s.factors,(integerPoly f.1).IsPrimitive

/-- The finite construction in `Yun` satisfies `advance_primitive` under the displayed hypotheses. -/
theorem advance_primitive (F : ℚ[X]) (s t : ArrayState)
    (h : ArrayInvariant F s) (hp : PrimitiveOutputs s) (ht : advance s=some t) :
    PrimitiveOutputs t := by
  obtain ⟨y,hy,hY,hYpoly⟩ := polyGcd_success s.w s.c h.canonical_w h.canonical_c
  have hym : (poly y).Monic := by rw [hYpoly]; exact gcdQ_monic _ _ h.model.w_monic.ne_zero
  have hydw : poly y∣poly s.w := by rw [hYpoly,gcdQ_eq_gcd]; exact gcd_dvd_left _ _
  have hydc : poly y∣poly s.c := by rw [hYpoly,gcdQ_eq_gcd]; exact gcd_dvd_right _ _
  obtain ⟨z,hz,hZ,hZpoly⟩ := exactDiv_success s.w y hym.ne_zero hydw
  obtain ⟨c,hc,hC,hCpoly⟩ := exactDiv_success s.c y hym.ne_zero hydc
  have hyz : poly y*poly z=poly s.w := by
    rw [hZpoly]
    exact EuclideanDomain.mul_div_cancel' hym.ne_zero hydw
  have hzm : (poly z).Monic := hym.of_mul_monic_left (hyz.symm ▸ h.model.w_monic)
  simp only [advance,hy,hz,hc,Option.some.injEq] at ht
  rw [← ht]
  intro f hf
  change f∈(if 1<z.length then s.factors++[(primitive z,s.exponent)] else s.factors) at hf
  split_ifs at hf
  · rcases List.mem_append.mp hf with hold | hnew
    · exact hp f hold
    · have heq := List.mem_singleton.mp hnew
      subst f
      exact primitive_isPrimitive z hzm.ne_zero
  · exact hp f hf

/-- The finite construction in `Yun` satisfies `run_primitive` under the displayed hypotheses. -/
theorem run_primitive (F : ℚ[X]) (fuel limit : ℕ) (s t : ArrayState)
    (h : ArrayInvariant F s) (hp : PrimitiveOutputs s) (ht : arrayRun fuel limit s=some t) :
    PrimitiveOutputs t := by
  induction fuel generalizing s with
  | zero =>
    dsimp only [arrayRun] at ht
    split_ifs at ht
    cases ht
    exact hp
  | succ fuel ih =>
    by_cases hw : 1<s.w.length
    · obtain ⟨u,hu,hinv,hdec⟩ := advance_success F s h
      have hpu : PrimitiveOutputs u := advance_primitive F s u h hp hu
      simp only [arrayRun,ite_eq_left hw,guardedAdvance,hu] at ht
      split_ifs at ht
      exact ih u hinv hpu ht
    · simp only [arrayRun,ite_eq_right hw,Option.some.injEq] at ht
      subst t
      exact hp

/-- The finite construction in `Yun` satisfies `generated_primitive` under the displayed hypotheses. -/
theorem generated_primitive (a : List ℚ) (ha : poly a≠0) (hd : 0<(poly a).natDegree)
    (out : List (List ℤ×ℕ)) (hout : squarefreeArrays a=some out) :
    ∀ f∈out,(integerPoly f.1).IsPrimitive := by
  obtain ⟨A,s,hinit,hinv,hdecode,he,hlen⟩ := initialize_array_invariant a ha hd
  have hnil : s.factors=[] := by
    have hp := congrArg State.factors hdecode
    change List.map (fun f => (normalize (integerPolyQ f.1),f.2)) s.factors=[] at hp
    exact List.map_eq_nil_iff.mp hp
  have hs : s=ArrayState.mk s.w s.c 1 [] := by
    cases s with
    | mk w c e fs =>
      change e=1 at he
      change fs=[] at hnil
      change ArrayState.mk w c e fs=ArrayState.mk w c 1 []
      rw [he,hnil]
  have hp : PrimitiveOutputs s := by intro f hf; rw [hnil] at hf; cases hf
  dsimp only [squarefreeArrays] at hout
  rw [hinit] at hout
  dsimp only at hout
  rw [← hs] at hout
  rcases Option.map_eq_some_iff.mp hout with ⟨t,ht,hf⟩
  rw [← hf]
  exact run_primitive _ _ _ s t hinv hp ht

end ActualYunIntegerProduct


namespace ActualYunContentSupply
open Polynomial ActualYunRationalArray ActualYunPrimitive ActualYunPrimitiveContent
open ActualYunIntegerProduct ActualYunArrayStep ActualYunArrayLoop

/-- Construction for raw Product in the yun model. -/
def rawProduct (out : List (List ℤ×ℕ)) : ℤ[X] :=
  (out.map (fun f => (integerPoly f.1)^f.2)).prod

/-- The finite construction in `Yun` satisfies `primitive_pow` under the displayed hypotheses. -/
theorem primitive_pow (p : ℤ[X]) (hp : p.IsPrimitive) (e : ℕ) :
    (p^e).IsPrimitive := by
  induction e with
  | zero => simpa only [pow_zero] using (Polynomial.isPrimitive_one (R := ℤ))
  | succ e ih => rw [pow_succ]; exact ih.mul hp

/-- The finite construction in `Yun` satisfies `rawProduct_primitive` under the displayed hypotheses. -/
theorem rawProduct_primitive (out : List (List ℤ×ℕ))
    (h : ∀ f∈out,(integerPoly f.1).IsPrimitive) : (rawProduct out).IsPrimitive := by
  induction out with
  | nil => simpa only [rawProduct,List.map_nil,List.prod_nil] using (Polynomial.isPrimitive_one (R := ℤ))
  | cons f fs ih =>
    change ((integerPoly f.1)^f.2*rawProduct fs).IsPrimitive
    exact (primitive_pow _ (h f (by simp)) _).mul (ih (fun g hg => h g (by simp [hg])))

/-- The finite construction in `Yun` satisfies `normalized_rawProduct` under the displayed hypotheses. -/
theorem normalized_rawProduct (out : List (List ℤ×ℕ)) :
    normalize ((rawProduct out).map (Int.castRingHom ℚ))=
      (out.map (fun f => normalize (integerPolyQ f.1)^f.2)).prod := by
  induction out with
  | nil => simp [rawProduct]
  | cons f fs ih =>
    change normalize (((integerPoly f.1)^f.2*rawProduct fs).map (Int.castRingHom ℚ))=
      normalize (integerPolyQ f.1)^f.2*(fs.map (fun f => normalize (integerPolyQ f.1)^f.2)).prod
    rw [Polynomial.map_mul,Polynomial.map_pow,normalize_mul,ih]
    exact congrArg (fun q => q*(fs.map (fun f => normalize (integerPolyQ f.1)^f.2)).prod)
      (map_pow normalizeHom (integerPolyQ f.1) f.2)

/-- The finite construction in `Yun` satisfies `normalize_field` under the displayed hypotheses. -/
theorem normalize_field (p : ℚ[X]) (hp : p≠0) :
    normalize p=p*C p.leadingCoeff⁻¹ := by
  rw [normalize_apply,Polynomial.coe_normUnit,
    CommGroupWithZero.coe_normUnit ℚ (Polynomial.leadingCoeff_ne_zero.mpr hp)]

/-- The finite construction in `Yun` satisfies `integral_content` under the displayed hypotheses. -/
theorem integral_content (H P : ℤ[X]) (hH : H≠0) (hP : P.IsPrimitive)
    (hnorm : normalize (H.map (Int.castRingHom ℚ))=normalize (P.map (Int.castRingHom ℚ))) :
    ∃ c : ℤ,(c : ℚ)=(H.map (Int.castRingHom ℚ)).leadingCoeff/
      (P.map (Int.castRingHom ℚ)).leadingCoeff ∧ c≠0 ∧ H=C c*P := by
  let h := H.map (Int.castRingHom ℚ)
  let p := P.map (Int.castRingHom ℚ)
  have hmap : Function.Injective (Polynomial.map (Int.castRingHom ℚ)) :=
    Polynomial.map_injective _ Rat.intCast_injective
  have hhn : h≠0 := by intro hz; apply hH; apply hmap; simpa only [Polynomial.map_zero] using hz
  have hpn : p≠0 := by intro hz; apply hP.ne_zero; apply hmap; simpa only [Polynomial.map_zero] using hz
  have hhl : h.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hhn
  have hpl : p.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hpn
  let q := h.leadingCoeff/p.leadingCoeff
  have hidentity : h=C q*p := by
    change normalize h=normalize p at hnorm
    rw [normalize_field h hhn,normalize_field p hpn] at hnorm
    have he := congrArg (fun v : ℚ[X] => v*C h.leadingCoeff) hnorm
    simp only [mul_assoc,← Polynomial.C_mul,inv_mul_cancel₀ hhl,Polynomial.C_1,mul_one] at he
    calc
      h=p*C (p.leadingCoeff⁻¹*h.leadingCoeff) := he
      _=C q*p := by dsimp only [q]; rw [div_eq_mul_inv]; ring
  have hlift : C q∈Polynomial.lifts (algebraMap ℤ ℚ) := by
    apply hP.mul_map_mem_lifts_iff.mp
    change C q*p∈Polynomial.lifts (algebraMap ℤ ℚ)
    rw [← hidentity]
    exact ⟨H,rfl⟩
  obtain ⟨c,hc⟩ := (Polynomial.lifts_iff_coeff_lifts (C q)).mp hlift 0
  have hcq : (c : ℚ)=q := by simpa only [Polynomial.coeff_C_zero,algebraMap_int_eq,Int.coe_castRingHom] using hc
  have hcz : c≠0 := by
    intro hz
    have hqz : q=0 := by rw [← hcq,hz]; rfl
    exact (div_ne_zero hhl hpl) hqz
  refine ⟨c,hcq,hcz,?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
  rw [Polynomial.map_mul,Polynomial.map_C]
  change h=C (c : ℚ)*p
  rw [hcq]
  exact hidentity


/-- The finite construction in `Yun` satisfies `castArray_poly` under the displayed hypotheses. -/
theorem castArray_poly (a : List ℤ) :
    poly (a.map (fun z : ℤ => (z : ℚ)))=(integerPoly a).map (Int.castRingHom ℚ) := by
  ext i
  rw [ActualYunRationalArray.coeff,Polynomial.coeff_map]
  change (a.map (fun z : ℤ => (z : ℚ))).getD i 0=(a.getD i 0 : ℚ)
  simpa only [Int.cast_zero] using (List.getD_map a 0 (n := i) (fun z : ℤ => (z : ℚ)))

/-- The finite construction in `Yun` satisfies `generated_content` under the displayed hypotheses. -/
theorem generated_content (a : List ℤ) (ha : integerPoly a≠0)
    (hd : 0<(integerPoly a).natDegree) :
    ∃ (out : List (List ℤ×ℕ)) (c : ℤ),squarefreeArrays (a.map (fun z : ℤ => (z : ℚ)))=some out ∧
      (c : ℚ)=((integerPoly a).map (Int.castRingHom ℚ)).leadingCoeff/
        ((rawProduct out).map (Int.castRingHom ℚ)).leadingCoeff ∧
      c≠0 ∧ integerPoly a=C c*rawProduct out ∧
      ∀ f∈out,FactorGood f ∧ f.2≤(integerPoly a).natDegree ∧ (integerPoly f.1).IsPrimitive := by
  have hmap := Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
  have haq : poly (a.map (fun z : ℤ => (z : ℚ)))≠0 := by
    rw [castArray_poly]
    intro hz
    apply ha
    apply hmap
    simpa only [Polynomial.map_zero] using hz
  have hdegree : (poly (a.map (fun z : ℤ => (z : ℚ)))).natDegree=(integerPoly a).natDegree := by
    rw [castArray_poly]
    exact Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective _
  have hdq : 0<(poly (a.map (fun z : ℤ => (z : ℚ)))).natDegree := by rw [hdegree]; exact hd
  obtain ⟨out,hout,hnorm,hgood⟩ := generated_integer_factors _ haq hdq
  have hprimitive := generated_primitive _ haq hdq out hout
  have hp := rawProduct_primitive out hprimitive
  have hn : normalize ((integerPoly a).map (Int.castRingHom ℚ))=
      normalize ((rawProduct out).map (Int.castRingHom ℚ)) := by
    rw [normalized_rawProduct]
    rw [castArray_poly] at hnorm
    exact hnorm
  obtain ⟨c,hc,hcn,hidentity⟩ := integral_content _ _ ha hp hn
  refine ⟨out,c,hout,hc,hcn,hidentity,?_⟩
  intro f hf
  have hg := hgood f hf
  exact ⟨hg.1,by rw [hdegree] at hg; exact hg.2,hprimitive f hf⟩


end ActualYunContentSupply


namespace ActualYunProductArrays
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualYunPrimitiveContent ActualYunContentSupply

/-- Construction for rows in the yun model. -/
def rows (c : List ℚ) : List ℚ → List ℚ → ℕ → List ℚ
  | [],_,_ => c
  | x::xs,b,j => rows (subtractShift c b j (-x)) xs b (j+1)

/-- The finite construction in `Yun` satisfies `rows_poly` under the displayed hypotheses. -/
theorem rows_poly (c a b : List ℚ) (j : ℕ)
    (hbound : j+a.length+b.length≤c.length+1) :
    poly (rows c a b j)=poly c+X^j*poly a*poly b := by
  induction a generalizing c j with
  | nil => simp only [rows,poly_nil,mul_zero,zero_mul,add_zero]
  | cons x xs ih =>
    have hj : j+b.length≤c.length := by simp only [List.length_cons] at hbound; omega
    have hnext : j+1+xs.length+b.length≤(subtractShift c b j (-x)).length+1 := by
      rw [subtractShift_length]
      simp only [List.length_cons] at hbound
      omega
    rw [rows,ih _ _ hnext,subtractShift_poly _ _ _ _ hj,poly_cons,pow_succ,Polynomial.C_neg]
    ring

/-- Construction for q Mul in the yun model. -/
def qMul (a b : List ℚ) : List ℚ :=
  if a=[] ∨ b=[] then [] else
    trim (rows (List.replicate (a.length+b.length-1) 0) a b 0)

/-- The finite construction in `Yun` satisfies `zeros_poly` under the displayed hypotheses. -/
theorem zeros_poly (n : ℕ) : poly (List.replicate n (0 : ℚ))=0 := by
  ext k
  rw [coeff]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate,Polynomial.coeff_zero]
  split_ifs <;> rfl

/-- The finite construction in `Yun` satisfies `qMul_poly` under the displayed hypotheses. -/
theorem qMul_poly (a b : List ℚ) : poly (qMul a b)=poly a*poly b := by
  by_cases h : a=[] ∨ b=[]
  · rw [qMul,ite_eq_left h,poly_nil]
    rcases h with ha | hb
    · rw [ha,poly_nil,zero_mul]
    · rw [hb,poly_nil,mul_zero]
  · have ha : 0<a.length := List.length_pos_iff.mpr (fun he => h (Or.inl he))
    have hb : 0<b.length := List.length_pos_iff.mpr (fun he => h (Or.inr he))
    rw [qMul,ite_eq_right h,trim_poly,rows_poly]
    · rw [zeros_poly,pow_zero,one_mul,zero_add]
    · rw [List.length_replicate]
      omega

/-- Construction for repeat Mul in the yun model. -/
def repeatMul : ℕ → List ℚ → List ℚ → List ℚ
  | 0,product,_ => product
  | e+1,product,f => repeatMul e (qMul product f) f

/-- The finite construction in `Yun` satisfies `repeatMul_poly` under the displayed hypotheses. -/
theorem repeatMul_poly (e : ℕ) (a f : List ℚ) :
    poly (repeatMul e a f)=poly a*poly f^e := by
  induction e generalizing a with
  | zero => simp only [repeatMul,pow_zero,mul_one]
  | succ e ih =>
    rw [repeatMul,ih,qMul_poly,pow_succ]
    ring

/-- Construction for factors Product in the yun model. -/
def factorsProduct : List (List ℤ×ℕ) → List ℚ → List ℚ
  | [],product => product
  | f::fs,product => factorsProduct fs
      (repeatMul f.2 product (f.1.map (fun z : ℤ => (z : ℚ))))

/-- The finite construction in `Yun` satisfies `factorsProduct_poly` under the displayed hypotheses. -/
theorem factorsProduct_poly (out : List (List ℤ×ℕ)) (product : List ℚ) :
    poly (factorsProduct out product)=poly product*(rawProduct out).map (Int.castRingHom ℚ) := by
  induction out generalizing product with
  | nil => simp only [factorsProduct,rawProduct,List.map_nil,List.prod_nil,Polynomial.map_one,mul_one]
  | cons f fs ih =>
    rw [factorsProduct,ih,repeatMul_poly,castArray_poly]
    change poly product*((integerPoly f.1).map (Int.castRingHom ℚ))^f.2*
      (rawProduct fs).map (Int.castRingHom ℚ)=
      poly product*(((integerPoly f.1)^f.2*rawProduct fs).map (Int.castRingHom ℚ))
    rw [Polynomial.map_mul,Polynomial.map_pow,mul_assoc]

end ActualYunProductArrays


namespace ActualYunContentGuard
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualYunPrimitiveContent ActualYunContentSupply ActualYunProductArrays ActualYunArrayLoop

/-- The finite construction in `Yun` satisfies `qMul_canonical` under the displayed hypotheses. -/
theorem qMul_canonical (a b : List ℚ) : Canonical (qMul a b) := by
  unfold qMul
  split_ifs
  · rfl
  · exact trim_canonical _

/-- The finite construction in `Yun` satisfies `repeatMul_canonical` under the displayed hypotheses. -/
theorem repeatMul_canonical (e : ℕ) (a f : List ℚ) (h : Canonical a) :
    Canonical (repeatMul e a f) := by
  induction e generalizing a with
  | zero => exact h
  | succ e ih => exact ih _ (qMul_canonical _ _)

/-- The finite construction in `Yun` satisfies `factorsProduct_canonical` under the displayed hypotheses. -/
theorem factorsProduct_canonical (out : List (List ℤ×ℕ)) (a : List ℚ)
    (h : Canonical a) : Canonical (factorsProduct out a) := by
  induction out generalizing a with
  | nil => exact h
  | cons f fs ih => exact ih _ (repeatMul_canonical _ _ _ h)

/-- The finite construction in `Yun` satisfies `poly_one` under the displayed hypotheses. -/
theorem poly_one : poly [1]=1 := by
  rw [poly_cons,poly_nil,mul_zero,add_zero,Polynomial.C_1]

/-- The finite construction in `Yun` satisfies `generated_source_content_guard` under the displayed hypotheses. -/
theorem generated_source_content_guard (a : List ℤ) (ha : integerPoly a≠0)
    (hd : 0<(integerPoly a).natDegree)
    (hcanonical : Canonical (a.map (fun z : ℤ => (z : ℚ)))) :
    ∃ (out : List (List ℤ×ℕ)) (c : ℤ),
      squarefreeArrays (a.map (fun z : ℤ => (z : ℚ)))=some out ∧ c≠0 ∧
      let product := factorsProduct out [1]
      let content := (a.getD (a.length-1) 0 : ℚ)/product.getD (product.length-1) 0
      content=(c : ℚ) ∧ content.den=1 ∧
      product.map (fun v => content*v)=a.map (fun z : ℤ => (z : ℚ)) := by
  obtain ⟨out,c,hout,hc,hcn,hidentity,hgood⟩ := generated_content a ha hd
  let product := factorsProduct out [1]
  let target := a.map (fun z : ℤ => (z : ℚ))
  have hp : poly product=(rawProduct out).map (Int.castRingHom ℚ) := by
    dsimp only [product]
    rw [factorsProduct_poly,poly_one,one_mul]
  have hcp : Canonical product := factorsProduct_canonical out [1] (by rfl)
  have hmap := Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
  have htarget : poly target≠0 := by
    dsimp only [target]
    rw [castArray_poly]
    intro hz
    apply ha
    apply hmap
    simpa only [Polynomial.map_zero] using hz
  have hcq : (c : ℚ)≠0 := by exact_mod_cast hcn
  have hpoly : poly target=C (c : ℚ)*poly product := by
    dsimp only [target]
    rw [castArray_poly,hidentity,Polynomial.map_mul,Polynomial.map_C,← hp]
    rfl
  have hpn : poly product≠0 := by
    intro hz
    rw [hz,mul_zero] at hpoly
    exact htarget hpoly
  have htn : target≠[] := (canonical_nonzero target hcanonical).mpr htarget
  have hprn : product≠[] := (canonical_nonzero product hcp).mpr hpn
  have hcontent : (a.getD (a.length-1) 0 : ℚ)/product.getD (product.length-1) 0=(c : ℚ) := by
    rw [← canonical_leading product hcp hprn,hp,hc]
    congr 1
    have htlead := canonical_leading target hcanonical htn
    dsimp only [target] at htlead
    rw [castArray_poly] at htlead
    rw [htlead]
    simp only [List.length_map]
    simpa only [Int.cast_zero] using
      (List.getD_map a 0 (n := a.length-1) (fun z : ℤ => (z : ℚ))).symm
  have hdegree : (poly target).natDegree=(poly product).natDegree := by
    rw [hpoly,Polynomial.natDegree_C_mul hcq]
  have hlen : product.length=target.length := by
    have hlp := canonical_length product hcp hprn
    have hlt := canonical_length target hcanonical htn
    omega
  have harray : product.map (fun v => (c : ℚ)*v)=target := by
    apply List.ext_getElem
    · rw [List.length_map,hlen]
    · intro i hi hj
      have hi' : i<product.length := by simpa only [List.length_map] using hi
      have he := congrArg (fun p : ℚ[X] => p.coeff i) hpoly
      rw [Polynomial.coeff_C_mul,ActualYunRationalArray.coeff,ActualYunRationalArray.coeff] at he
      rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hi'] at he
      simpa only [List.getElem_map] using he.symm
  refine ⟨out,c,hout,hcn,?_⟩
  change (a.getD (a.length-1) 0 : ℚ)/product.getD (product.length-1) 0=(c : ℚ) ∧ _
  refine ⟨hcontent,?_,?_⟩
  · rw [hcontent]
    simp
  · rw [hcontent]
    exact harray



end ActualYunContentGuard


end RootYunInternal
end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

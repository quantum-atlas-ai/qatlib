/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.List.Nodup
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Yun

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

/-! Exact polynomial-array algorithms: Sturm.
These algorithms retain program bodies, guards, hypotheses and finite-fuel semantics. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
namespace RootYunInternal

namespace ActualSturmCutSearch
open Polynomial ActualYunPrimitive
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- Construction for candidate in the sturm model. -/
def candidate (D : ℕ) (a b : ℚ) (j : Fin (D+1)) : ℚ :=
  a+(b-a)*(1/4+((j.val+1 : ℕ) : ℚ)/(2*((D : ℚ)+2)))

/-- The estimate `candidate_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem candidate_bounds (D : ℕ) (a b : ℚ) (hab : a<b) (j : Fin (D+1)) :
    a+(b-a)/4<candidate D a b j ∧ candidate D a b j<a+3*(b-a)/4 := by
  have hden : (0 : ℚ)<2*((D : ℚ)+2) := by positivity
  have hj : (0 : ℚ)<(j.val+1 : ℕ) := by exact_mod_cast Nat.succ_pos j.val
  have hjD : ((j.val+1 : ℕ) : ℚ)<(D : ℚ)+2 := by exact_mod_cast (show j.val+1<D+2 by omega)
  have hlo := div_pos hj hden
  have hhi : ((j.val+1 : ℕ) : ℚ)/(2*((D : ℚ)+2))<1/2 :=
    (div_lt_iff₀ hden).mpr (by nlinarith)
  dsimp only [candidate]
  constructor <;> nlinarith

/-- For rational endpoints `a < b`, distinct indices among the `D + 1` cut candidates give distinct rational points. -/
theorem candidate_injective (D : ℕ) (a b : ℚ) (hab : a<b) :
    Function.Injective (candidate D a b) := by
  intro i j hij
  have hw : b-a≠0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hd : (2*((D : ℚ)+2))≠0 := by positivity
  dsimp only [candidate] at hij
  have hfrac := add_left_cancel (mul_left_cancel₀ hw (add_left_cancel hij))
  have hc : ((i.val+1 : ℕ) : ℚ)=((j.val+1 : ℕ) : ℚ) := by
    exact (div_left_inj' hd).mp hfrac
  apply Fin.ext
  have hn : i.val+1=j.val+1 := by exact_mod_cast hc
  omega

/-- A nonzero rational polynomial of degree at most `D` is nonzero at some cut candidate between ordered endpoints `a` and `b`. -/
theorem nonroot_candidate (p : ℚ[X]) (hp : p≠0) (D : ℕ) (hD : p.natDegree≤D)
    (a b : ℚ) (hab : a<b) : ∃ j : Fin (D+1),p.eval (candidate D a b j)≠0 := by
  by_contra hn
  push Not at hn
  apply hp
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (candidate_injective D a b hab) hn (by simp only [Fintype.card_fin]; omega)

/-- Construction for qpoly in the sturm model. -/
def qpoly {D : ℕ} (a : Fin (D+1) → ℤ) : ℚ[X] := integerPolyQ (List.ofFn a)

/-- Casting the rational polynomial of the integer coefficient vector `a` to complex coefficients gives `rootIntegerPolynomial a`. -/
theorem qpoly_map {D : ℕ} (a : Fin (D+1) → ℤ) :
    (qpoly a).map (Rat.castHom ℂ)=rootIntegerPolynomial a := by
  rw [qpoly,integerPolyQ_map,rootIntegerListPolynomial_ofFn]

/-- Construction for numerator in the sturm model. -/
def numerator {D : ℕ} (a : Fin (D+1) → ℤ) (v : ℚ) : ℤ :=
  (rootCompactHorner (rootSharedNumerator (v,0)) (rootSharedDenominator (v,0)) (List.ofFn a)).numerator.1

/-- The integer numerator computed at `v` is nonzero exactly when the rational polynomial evaluates to a nonzero value at `v`. -/
theorem numerator_nonzero_iff {D : ℕ} (a : Fin (D+1) → ℤ) (v : ℚ) :
    numerator a v≠0 ↔ (qpoly a).eval v≠0 := by
  let s := rootCompactHorner (rootSharedNumerator (v,0)) (rootSharedDenominator (v,0)) (List.ofFn a)
  have hden : (s.denominator : ℝ)≠0 := by
    exact_mod_cast (rootCompactHorner_denominator_pos _ _ _ (rootSharedDenominator_pos (v,0))).ne'
  have hv : rootRationalCoordinate (v,0)=(Rat.castHom ℂ) v := by
    apply Complex.ext <;> simp [rootRationalCoordinate]
  have he := rootIntegerPolynomial_horner a (v,0)
  rw [← qpoly_map a,hv,Polynomial.eval_map_apply] at he
  have hr : (s.numerator.1 : ℝ)/(s.denominator : ℝ)=(((qpoly a).eval v : ℚ) : ℝ) := by
    have h := congrArg Complex.re he
    simpa [gaussianPointValue,s] using h
  change s.numerator.1≠0 ↔ _
  constructor
  · intro hn hz
    rw [hz,Rat.cast_zero,div_eq_zero_iff] at hr
    exact hn (by exact_mod_cast (hr.resolve_right hden))
  · intro hn hz
    apply hn
    have hvz : (((qpoly a).eval v : ℚ) : ℝ)=0 := by rw [hz,Int.cast_zero,zero_div] at hr; exact hr.symm
    exact_mod_cast hvz


/-- Construction for scan in the sturm model. -/
def scan {D : ℕ} (a : Fin (D+1) → ℤ) : List ℚ → Option ℚ
  | [] => none
  | v::vs => if numerator a v=0 then scan a vs else some v

/-- If a candidate in `vs` has a nonzero numerator, the scan returns a member of `vs` whose numerator is nonzero. -/
theorem scan_success {D : ℕ} (a : Fin (D+1) → ℤ) (vs : List ℚ)
    (h : ∃ v∈vs,numerator a v≠0) :
    ∃ v,scan a vs=some v ∧ v∈vs ∧ numerator a v≠0 := by
  induction vs with
  | nil => simp only [List.not_mem_nil,false_and,exists_false] at h
  | cons v vs ih =>
    by_cases hv : numerator a v=0
    · have hh : ∃ w∈vs,numerator a w≠0 := by
        obtain ⟨w,hw,hwn⟩ := h
        rcases List.mem_cons.mp hw with he | he
        · subst w; exact (hwn hv).elim
        · exact ⟨w,he,hwn⟩
      obtain ⟨w,hw,hm,hn⟩ := ih hh
      exact ⟨w,by simp only [scan,ite_eq_left hv]; exact hw,by simp [hm],hn⟩
    · exact ⟨v,by simp only [scan,ite_eq_right hv],by simp,hv⟩

/-- Construction for choose in the sturm model. -/
def choose {D : ℕ} (a : Fin (D+1) → ℤ) (left right : ℚ) : Option ℚ :=
  scan a (List.ofFn (candidate D left right))

/-- For a nonzero input polynomial and ordered endpoints, `choose` returns a nonroot strictly inside the middle half. Each resulting interval has length at most three quarters of the original length. -/
theorem choose_success {D : ℕ} (a : Fin (D+1) → ℤ) (ha : qpoly a≠0)
    (left right : ℚ) (hab : left<right) :
    ∃ v,choose a left right=some v ∧ numerator a v≠0 ∧
      (qpoly a).eval v≠0 ∧ left+(right-left)/4<v ∧ v<left+3*(right-left)/4 ∧
      v-left≤3*(right-left)/4 ∧ right-v≤3*(right-left)/4 := by
  have hdegree : (qpoly a).natDegree≤D := by
    rw [← Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℂ).injective (qpoly a),qpoly_map]
    exact rootIntegerPolynomial_degree a
  obtain ⟨j,hj⟩ := nonroot_candidate (qpoly a) ha D hdegree left right hab
  have hex : ∃ v∈List.ofFn (candidate D left right),numerator a v≠0 :=
    ⟨candidate D left right j,List.mem_ofFn.mpr ⟨j,rfl⟩,(numerator_nonzero_iff a _).mpr hj⟩
  obtain ⟨v,hv,hm,hn⟩ := scan_success a _ hex
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  have hb := candidate_bounds D left right hab i
  rw [hi] at hb
  exact ⟨v,hv,hn,(numerator_nonzero_iff a _).mp hn,hb.1,hb.2,by linarith,by linarith⟩

-- First source candidate -1/6 is an exact root, so search must continue.



end ActualSturmCutSearch


namespace ActualSturmArrayTools
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualYunContentSupply

/-- Construction for lift in the sturm model. -/
def lift (a : List ℤ) : List ℚ := a.map (fun z : ℤ => (z : ℚ))

/-- The polynomial of the rational lift of an integer list equals its integer-coefficient polynomial interpreted over the rationals. -/
theorem lift_poly (a : List ℤ) : poly (lift a)=integerPolyQ a := castArray_poly a

/-- The same emitted instruction list satisfies `canonical_of_degree_length` with the displayed gate and query accounting. -/
theorem canonical_of_degree_length (a : List ℚ) (ha : poly a≠0)
    (hlen : a.length=(poly a).natDegree+1) : Canonical a := by
  have hidx : a.length-1=(poly a).natDegree := by omega
  have hlast : a.getD (a.length-1) 0≠0 := by
    rw [← ActualYunRationalArray.coeff,hidx]
    exact Polynomial.leadingCoeff_ne_zero.mpr ha
  induction a using List.reverseRecOn with
  | nil => exact (ha poly_nil).elim
  | append_singleton a x ih =>
    have hx : x≠0 := by
      have he : (a++[x]).getD ((a++[x]).length-1) 0=x := by
        simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel,
          List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      rw [he] at hlast
      exact hlast
    change trim (a++[x])=a++[x]
    simp [trim,hx]

/-- Taking the primitive integer list and lifting it back to rationals preserves polynomial nonzeroness. -/
theorem primitive_lift_nonzero (a : List ℚ) (ha : poly a≠0) :
    poly (lift (primitive a))≠0 := by
  rw [lift_poly,primitive_polynomialQ a ha]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (primitiveScale_pos a ha).ne') ha

/-- For a nonzero rational polynomial, its lifted primitive coefficient list represents a polynomial of the same natural degree. -/
theorem primitive_lift_degree (a : List ℚ) (ha : poly a≠0) :
    (poly (lift (primitive a))).natDegree=(poly a).natDegree := by
  rw [lift_poly,primitive_polynomialQ a ha,Polynomial.natDegree_C_mul (primitiveScale_pos a ha).ne']

/-- If `a` represents a nonzero polynomial, the rational lift of its primitive integer coefficients is fixed by `trim`. -/
theorem primitive_lift_canonical (a : List ℚ) (ha : poly a≠0) :
    Canonical (lift (primitive a)) := by
  have ht : trim a≠[] := (canonical_nonzero _ (trim_canonical a)).mpr (by rw [trim_poly]; exact ha)
  apply canonical_of_degree_length _ (primitive_lift_nonzero a ha)
  rw [show (lift (primitive a)).length=(primitive a).length by simp only [lift,List.length_map],
    primitive_length,canonical_length _ (trim_canonical a) ht,trim_poly,
    primitive_lift_degree a ha]

/-- Negating every rational coefficient negates the represented polynomial. -/
theorem poly_neg (a : List ℚ) : poly (a.map (fun x : ℚ => -x))= -poly a := by
  ext i
  rw [ActualYunRationalArray.coeff,Polynomial.coeff_neg,ActualYunRationalArray.coeff]
  simpa only [neg_zero] using (List.getD_map a 0 (n := i) (fun x : ℚ => -x))

end ActualSturmArrayTools


namespace ActualSturmInitialization
open Polynomial ActualYunInitial ActualYunStep ActualYunRationalArray ActualYunRationalCanonical
open ActualYunGcd ActualYunArrayInitialization ActualYunPrimitive ActualSturmArrayTools

/-- Multiplying the right member of a coprime polynomial pair by a nonzero rational constant preserves coprimality. -/
theorem coprime_scale_right (F G : ℚ[X]) (s : ℚ) (hs : s≠0)
    (h : IsCoprime F G) : IsCoprime F (C s*G) := by
  obtain ⟨u,v,h⟩ := h
  refine ⟨u,C s⁻¹*v,?_⟩
  calc
    u*F+(C s⁻¹*v)*(C s*G)=u*F+(C s⁻¹*C s)*(v*G) := by ring
    _=1 := by rw [← Polynomial.C_mul,inv_mul_cancel₀ hs,Polynomial.C_1,one_mul,h]

/-- Construction for initial Chain in the sturm model. -/
def initialChain (a : List ℚ) : Option (List (List ℤ)) :=
  match polyGcd a (derivative a) with
  | none => none
  | some c => match exactDiv a c with
    | none => none
    | some q =>
      let f := primitive q
      if f.length<2 then some [] else
        some [f,primitive (derivative (lift f))]

/-- For a canonical nonzero input of positive degree, initialization returns two canonical lifts. The first represents a separable polynomial of positive degree at most the input degree, and the second is a nonzero positive rational multiple of its derivative and coprime to it. -/
theorem initialization_success (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) :
    ∃ f g,initialChain a=some [f,g] ∧ Canonical (lift f) ∧ Canonical (lift g) ∧
      (integerPolyQ f).Separable ∧ 0<(integerPolyQ f).natDegree ∧
      (integerPolyQ f).natDegree≤(poly a).natDegree ∧ integerPolyQ g≠0 ∧
      IsCoprime (integerPolyQ f) (integerPolyQ g) ∧
      ∃ s : ℚ,0<s ∧ integerPolyQ g=C s*(integerPolyQ f).derivative := by
  have hdc : Canonical (derivative a) := trim_canonical _
  obtain ⟨c,hc,hC,hCpoly⟩ := polyGcd_success a (derivative a) hcan hdc
  rw [derivative_poly] at hCpoly
  have hcn : poly c≠0 := by rw [hCpoly,gcdQ_eq_gcd]; exact gcd_ne_zero_of_left ha
  have hcd : poly c∣poly a := by rw [hCpoly,gcdQ_eq_gcd]; exact gcd_dvd_left _ _
  obtain ⟨q,hq,hQ,hQpoly⟩ := exactDiv_success a c hcn hcd
  have hprod : poly c*poly q=poly a := by rw [hQpoly]; exact EuclideanDomain.mul_div_cancel' hcn hcd
  have hqn : poly q≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact ha hprod.symm
  have hdn : (poly a).derivative≠0 := by
    intro hz
    have hh := Polynomial.derivative_eq_zero.mp hz
    omega
  have hcder : poly c∣(poly a).derivative := by rw [hCpoly,gcdQ_eq_gcd]; exact gcd_dvd_right _ _
  have hcle := Polynomial.natDegree_le_of_dvd hcder hdn
  have hdlt := Polynomial.natDegree_derivative_lt (ne_of_gt hd)
  have hdegrees : (poly c).natDegree+(poly q).natDegree=(poly a).natDegree := by
    rw [← Polynomial.natDegree_mul hcn hqn,hprod]
  have hqpos : 0<(poly q).natDegree := by omega
  have hqbound : (poly q).natDegree≤(poly a).natDegree := by omega
  have hqsep : (poly q).Separable := by
    apply (Polynomial.separable_map (Rat.castHom ℂ)).mp
    rw [hQpoly,hCpoly]
    exact initial_rational_quotient_separable (poly a) ha
  let f := primitive q
  have hfpoly : integerPolyQ f=C (primitiveScale q)*poly q := primitive_polynomialQ q hqn
  have hfm : (integerPolyQ f).Separable := by
    rw [hfpoly]
    exact Polynomial.Separable.unit_mul
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (primitiveScale_pos q hqn).ne')) hqsep
  have hfdeg : (integerPolyQ f).natDegree=(poly q).natDegree := by
    rw [hfpoly,Polynomial.natDegree_C_mul (primitiveScale_pos q hqn).ne']
  have hfc : Canonical (lift f) := primitive_lift_canonical q hqn
  have hfdn : (integerPolyQ f).derivative≠0 := by
    intro hz
    have hh := Polynomial.derivative_eq_zero.mp hz
    omega
  let df := derivative (lift f)
  have hdf : poly df=(integerPolyQ f).derivative := by dsimp only [df]; rw [derivative_poly,lift_poly]
  have hdfn : poly df≠0 := by rw [hdf]; exact hfdn
  let g := primitive df
  have hgc : Canonical (lift g) := primitive_lift_canonical df hdfn
  have hgpoly : integerPolyQ g=C (primitiveScale df)*(integerPolyQ f).derivative := by
    rw [show integerPolyQ g=C (primitiveScale df)*poly df from primitive_polynomialQ df hdfn,hdf]
  have hgn : integerPolyQ g≠0 := by
    rw [hgpoly]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (primitiveScale_pos df hdfn).ne') hfdn
  have hcop : IsCoprime (integerPolyQ f) (integerPolyQ g) := by
    rw [hgpoly]
    exact coprime_scale_right _ _ _ (primitiveScale_pos df hdfn).ne' hfm
  have hfnil : lift f≠[] := (canonical_nonzero _ hfc).mpr (by rw [lift_poly]; exact hfm.ne_zero)
  have hfl := canonical_length (lift f) hfc hfnil
  rw [lift_poly] at hfl
  have hguard : ¬f.length<2 := by
    simp only [lift,List.length_map] at hfl
    omega
  refine ⟨f,g,?_,hfc,hgc,hfm,by omega,by omega,hgn,hcop,
    primitiveScale df,primitiveScale_pos df hdfn,hgpoly⟩
  simp only [initialChain,hc,hq]
  rw [ite_eq_right hguard]



end ActualSturmInitialization


namespace ActualSturmStep
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualYunDivrem ActualSturmArrayTools

/-- Constructors for Next in the sturm model. -/
inductive Next where
  | done
  | more (a : List ℤ)
  deriving DecidableEq

/-- Construction for step in the sturm model. -/
def step (a b : List ℤ) : Option Next :=
  match divrem (lift a) (lift b) with
  | none => none
  | some (_,r) => if r=[] then some Next.done else
      some (Next.more (primitive (r.map (fun x : ℚ => -x))))

/-- If `F` and `G` are coprime and `s` is nonzero, `F` is coprime to the polynomial `C s * G`. -/
theorem coprime_scale_right (F G : ℚ[X]) (s : ℚ) (hs : s≠0)
    (h : IsCoprime F G) : IsCoprime F (C s*G) := by
  obtain ⟨u,v,h⟩ := h
  refine ⟨u,C s⁻¹*v,?_⟩
  calc
    u*F+(C s⁻¹*v)*(C s*G)=u*F+(C s⁻¹*C s)*(v*G) := by ring
    _=1 := by rw [← Polynomial.C_mul,inv_mul_cancel₀ hs,Polynomial.C_1,one_mul,h]

/-- Construction for Good in the sturm model. -/
def Good (a b : List ℤ) : Next → Prop
  | Next.done => (integerPolyQ b).natDegree=0
  | Next.more c => Canonical (lift c) ∧ integerPolyQ c≠0 ∧ c.length<b.length ∧
      IsCoprime (integerPolyQ b) (integerPolyQ c) ∧
      (∃ s : ℚ,0<s ∧ integerPolyQ c=C s*(-(integerPolyQ a%integerPolyQ b))) ∧
      ∀ x : ℝ,(integerPolyQ b).eval₂ (Rat.castHom ℝ) x=0 →
        (integerPolyQ a).eval₂ (Rat.castHom ℝ) x*
          (integerPolyQ c).eval₂ (Rat.castHom ℝ) x<0

/-- If `b` has a canonical lift and represents a nonzero polynomial coprime to that of `a`,
the step returns a `Good a b` outcome. It either stops with `b` of degree zero or returns a
shorter canonical array for a nonzero positive multiple of the negative remainder, coprime
to `b` and opposite in sign to `a` at every real zero of `b`. -/
theorem step_success (a b : List ℤ) (hbcan : Canonical (lift b)) (hbn : integerPolyQ b≠0)
    (hcop : IsCoprime (integerPolyQ a) (integerPolyQ b)) :
    ∃ result,step a b=some result ∧ Good a b result := by
  have hbn' : poly (lift b)≠0 := by rw [lift_poly]; exact hbn
  obtain ⟨q,r,hqr,hq,hr,hquot,hrem,hlen⟩ := divrem_success (lift a) (lift b) hbn'
  rw [lift_poly,lift_poly] at hquot hrem
  have hidentity : integerPolyQ a=poly q*integerPolyQ b+poly r := by
    rw [hquot,hrem]
    simpa only [mul_comm] using (EuclideanDomain.div_add_mod (integerPolyQ a) (integerPolyQ b)).symm
  by_cases hz : r=[]
  · have hmod : integerPolyQ a%integerPolyQ b=0 := by rw [← hrem,hz,poly_nil]
    have hdiv : integerPolyQ b∣integerPolyQ a := EuclideanDomain.mod_eq_zero.mp hmod
    refine ⟨Next.done,?_,Polynomial.natDegree_eq_zero_of_isUnit (hcop.symm.isUnit_of_dvd hdiv)⟩
    simp only [step,hqr,ite_eq_left hz]
  · have hrn : poly r≠0 := (canonical_nonzero r hr).mp hz
    let negR := r.map (fun x : ℚ => -x)
    have hneg : poly negR= -poly r := poly_neg r
    have hnegn : poly negR≠0 := by rw [hneg]; exact neg_ne_zero.mpr hrn
    let c := primitive negR
    have hcc : Canonical (lift c) := primitive_lift_canonical negR hnegn
    have hcn : integerPolyQ c≠0 := by
      have hh := primitive_lift_nonzero negR hnegn
      rw [lift_poly] at hh
      exact hh
    have hcvalue : integerPolyQ c=C (primitiveScale negR)*(-poly r) := by
      rw [show integerPolyQ c=C (primitiveScale negR)*poly negR from primitive_polynomialQ negR hnegn,hneg]
    have hcdegree : (integerPolyQ c).natDegree=(poly r).natDegree := by
      rw [hcvalue,Polynomial.natDegree_C_mul (primitiveScale_pos negR hnegn).ne',Polynomial.natDegree_neg]
    have hclen : c.length=r.length := by
      have hclift : lift c≠[] := (canonical_nonzero _ hcc).mpr (by rw [lift_poly]; exact hcn)
      have hh := canonical_length (lift c) hcc hclift
      rw [lift_poly,hcdegree] at hh
      simp only [lift,List.length_map] at hh
      rw [hh,canonical_length r hr hz]
    rw [hbcan] at hlen
    have hlen' : c.length<b.length := by
      rw [hclen]
      simpa only [lift,List.length_map] using hlen
    have hcr : IsCoprime (integerPolyQ b) (poly r) := by
      have hh := hcop
      rw [hidentity] at hh
      exact hh.of_mul_add_right_left.symm
    have hcopnext : IsCoprime (integerPolyQ b) (integerPolyQ c) := by
      rw [hcvalue]
      exact coprime_scale_right _ _ _ (primitiveScale_pos negR hnegn).ne'
        ((IsCoprime.neg_right_iff _ _).mpr hcr)
    have hsign : ∀ x : ℝ,(integerPolyQ b).eval₂ (Rat.castHom ℝ) x=0 →
        (integerPolyQ a).eval₂ (Rat.castHom ℝ) x*
          (integerPolyQ c).eval₂ (Rat.castHom ℝ) x<0 := by
      intro x hx
      have hvals := hcop.map (Polynomial.eval₂RingHom (Rat.castHom ℝ) x)
      change IsCoprime ((integerPolyQ a).eval₂ (Rat.castHom ℝ) x)
        ((integerPolyQ b).eval₂ (Rat.castHom ℝ) x) at hvals
      rw [hx,isCoprime_zero_right] at hvals
      have hpn := hvals.ne_zero
      have he := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) x) hidentity
      simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,hx,mul_zero,zero_add] at he
      have hnext := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) x) hcvalue
      simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_neg] at hnext
      have hs : (0 : ℝ)<(primitiveScale negR : ℚ) := by exact_mod_cast primitiveScale_pos negR hnegn
      have hsq := sq_pos_of_ne_zero hpn
      rw [hnext,← he]
      change _*( (primitiveScale negR : ℝ)*(-_))<0
      nlinarith [mul_pos hs hsq]
    refine ⟨Next.more c,?_,hcc,hcn,hlen',hcopnext,?_,hsign⟩
    · simp only [step,hqr,ite_eq_right hz]
      rfl
    · refine ⟨primitiveScale negR,primitiveScale_pos negR hnegn,?_⟩
      rw [← hrem]
      exact hcvalue



end ActualSturmStep


namespace ActualSturmChain
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualSturmArrayTools ActualSturmInitialization ActualSturmStep

/-- Construction for value in the sturm model. -/
def value (a : List ℤ) (x : ℝ) : ℝ := (integerPolyQ a).eval₂ (Rat.castHom ℝ) x

/-- Construction for Triple Good in the sturm model. -/
def TripleGood (a b : List ℤ) : List (List ℤ) → Prop
  | [] => True
  | c::_ => ∀ x : ℝ,value b x=0 → value a x*value c x<0

/-- Construction for Chain Good in the sturm model. -/
def ChainGood : List (List ℤ) → Prop
  | [] => False
  | [a] => Canonical (lift a) ∧ integerPolyQ a≠0 ∧ (integerPolyQ a).natDegree=0
  | a::b::xs => Canonical (lift a) ∧ integerPolyQ a≠0 ∧ b.length<a.length ∧
      IsCoprime (integerPolyQ a) (integerPolyQ b) ∧ TripleGood a b xs ∧ ChainGood (b::xs)

/-- Construction for run in the sturm model. -/
def run : ℕ → List ℤ → List ℤ → Option (List (List ℤ))
  | 0,_,_ => none
  | fuel+1,a,b => match step a b with
    | none => none
    | some Next.done => some [a,b]
    | some (Next.more c) => (run fuel b c).map (fun rest => a::rest)

/-- For canonical nonzero coprime inputs with `b.length < a.length`, fuel at least `b.length` returns a chain starting with `a`, `b` and satisfying `ChainGood`. -/
theorem run_success (fuel : ℕ) (a b : List ℤ) (hac : Canonical (lift a))
    (hbc : Canonical (lift b)) (han : integerPolyQ a≠0) (hbn : integerPolyQ b≠0)
    (hcop : IsCoprime (integerPolyQ a) (integerPolyQ b)) (hlen : b.length<a.length)
    (hfuel : b.length≤fuel) :
    ∃ xs,run fuel a b=some (a::b::xs) ∧ ChainGood (a::b::xs) := by
  induction fuel generalizing a b with
  | zero =>
    have hb0 : b=[] := List.length_eq_zero_iff.mp (by omega)
    have hh : integerPolyQ b=0 := by rw [← lift_poly,hb0]; exact poly_nil
    exact (hbn hh).elim
  | succ fuel ih =>
    obtain ⟨result,hstep,hgood⟩ := step_success a b hbc hbn hcop
    cases result with
    | done =>
      change (integerPolyQ b).natDegree=0 at hgood
      refine ⟨[],?_,?_⟩
      · simp only [run,hstep]
      · exact ⟨hac,han,hlen,hcop,True.intro,hbc,hbn,hgood⟩
    | more c =>
      change Canonical (lift c) ∧ integerPolyQ c≠0 ∧ c.length<b.length ∧
        IsCoprime (integerPolyQ b) (integerPolyQ c) ∧ _ at hgood
      obtain ⟨hcc,hcn,hclen,hcopnext,hscale,hsign⟩ := hgood
      obtain ⟨xs,hrun,hchain⟩ := ih b c hbc hcc hbn hcn hcopnext hclen (by omega)
      refine ⟨c::xs,?_,?_⟩
      · simp only [run,hstep,hrun,Option.map_some]
      · exact ⟨hac,han,hlen,hcop,hsign,hchain⟩

/-- Construction for source Chain in the sturm model. -/
def sourceChain (a : List ℚ) : Option (List (List ℤ)) :=
  match initialChain a with
  | none => none
  | some [] => some []
  | some [f,g] => run g.length f g
  | some _ => none

/-- A canonical nonzero input of positive degree yields a good chain whose first polynomial is separable of positive degree and whose second is a positive rational multiple of its derivative. -/
theorem source_chain_success (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) :
    ∃ f g xs,sourceChain a=some (f::g::xs) ∧ ChainGood (f::g::xs) ∧
      (integerPolyQ f).Separable ∧ 0<(integerPolyQ f).natDegree ∧
      ∃ s : ℚ,0<s ∧ integerPolyQ g=C s*(integerPolyQ f).derivative := by
  obtain ⟨f,g,hinit,hfc,hgc,hsep,hfd,hfdle,hgn,hcop,s,hs,hg⟩ := initialization_success a hcan ha hd
  have hgnil : lift g≠[] := (canonical_nonzero _ hgc).mpr (by rw [lift_poly]; exact hgn)
  have hfnil : lift f≠[] := (canonical_nonzero _ hfc).mpr (by rw [lift_poly]; exact hsep.ne_zero)
  have hfl := canonical_length (lift f) hfc hfnil
  have hgl := canonical_length (lift g) hgc hgnil
  rw [lift_poly] at hfl hgl
  simp only [lift,List.length_map] at hfl hgl
  have hgdegree : (integerPolyQ g).natDegree=(integerPolyQ f).derivative.natDegree := by
    rw [hg,Polynomial.natDegree_C_mul hs.ne']
  have hlen : g.length<f.length := by
    have hh := Polynomial.natDegree_derivative_lt (ne_of_gt hfd)
    omega
  obtain ⟨xs,hrun,hchain⟩ := run_success g.length f g hfc hgc hsep.ne_zero hgn hcop hlen (le_refl _)
  exact ⟨f,g,xs,by simp only [sourceChain,hinit]; exact hrun,hchain,hsep,hfd,s,hs,hg⟩



end ActualSturmChain


namespace ActualSturmRootset
open Polynomial ActualYunInitial ActualYunStep ActualYunRationalArray ActualYunRationalCanonical
open ActualYunGcd ActualYunArrayInitialization ActualYunPrimitive ActualSturmArrayTools
open ActualSturmInitialization ActualSturmChain

/-- For a nonzero real polynomial of positive degree, the quotient by its gcd with its derivative has exactly the same real zeros. -/
theorem radical_real_roots (F : ℝ[X]) (hF : F≠0) (hd : 0<F.natDegree) (x : ℝ) :
    (F/gcd F F.derivative).eval x=0 ↔ F.eval x=0 := by
  classical
  let c := gcd F F.derivative
  let w := F/c
  have hc : c≠0 := gcd_ne_zero_of_left hF
  have hw : w≠0 := left_div_gcd_ne_zero hF
  have hprod : c*w=F := EuclideanDomain.mul_div_cancel' hc (gcd_dvd_left _ _)
  have hdn : F.derivative≠0 := by
    intro hz
    have hh := Polynomial.derivative_eq_zero.mp hz
    omega
  constructor
  · intro hx
    rw [← hprod,Polynomial.eval_mul]
    change _*w.eval x=0
    rw [hx,mul_zero]
  · intro hx
    have hroot : F.IsRoot x := hx
    have hdroot := Polynomial.derivative_rootMultiplicity_of_root hroot
    have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hdn
      (gcd_dvd_right F F.derivative) x
    change c.rootMultiplicity x≤F.derivative.rootMultiplicity x at hle
    have hmult : F.rootMultiplicity x=c.rootMultiplicity x+w.rootMultiplicity x := by
      rw [← hprod,Polynomial.rootMultiplicity_mul (by simpa only [hprod] using hF)]
    have hpos : 0<F.rootMultiplicity x := (Polynomial.rootMultiplicity_pos hF).mpr hx
    by_contra hnot
    have hzero := Polynomial.rootMultiplicity_eq_zero hnot
    change w.rootMultiplicity x=0 at hzero
    rw [hdroot] at hle
    omega

/-- Mapping the rational gcd to real coefficients gives the gcd of the two coefficientwise casts. -/
theorem gcdQ_map_real (P Q : ℚ[X]) :
    (gcdQ P Q).map (Rat.castHom ℝ)=gcd (P.map (Rat.castHom ℝ)) (Q.map (Rat.castHom ℝ)) := by
  classical
  unfold gcdQ
  rw [Polynomial.map_normalize,← Polynomial.gcd_map]
  exact normalized_euclidean_eq_gcd _ _

/-- For a nonzero rational polynomial of positive degree, division by its normalized gcd with its derivative preserves vanishing at every real argument. -/
theorem quotient_real_roots (P : ℚ[X]) (hP : P≠0) (hd : 0<P.natDegree) (x : ℝ) :
    (P/gcdQ P P.derivative).eval₂ (Rat.castHom ℝ) x=0 ↔ P.eval₂ (Rat.castHom ℝ) x=0 := by
  have hm : (P.map (Rat.castHom ℝ))≠0 := Polynomial.map_ne_zero hP
  have hdeg : 0<(P.map (Rat.castHom ℝ)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact hd
  rw [← Polynomial.eval_map,Polynomial.map_div,gcdQ_map_real,← Polynomial.derivative_map,
    ← Polynomial.eval_map]
  exact radical_real_roots _ hm hdeg x

/-- For canonical nonzero input of positive degree, the first polynomial of any returned initial pair vanishes at precisely the real zeros of the input. -/
theorem initialized_real_roots (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (f g : List ℤ) (hinit : initialChain a=some [f,g]) :
    ∀ x : ℝ,(integerPolyQ f).eval₂ (Rat.castHom ℝ) x=0 ↔ (poly a).eval₂ (Rat.castHom ℝ) x=0 := by
  have hdc : Canonical (derivative a) := trim_canonical _
  obtain ⟨c,hc,hC,hCpoly⟩ := polyGcd_success a (derivative a) hcan hdc
  rw [derivative_poly] at hCpoly
  have hcn : poly c≠0 := by rw [hCpoly,gcdQ_eq_gcd]; exact gcd_ne_zero_of_left ha
  have hcd : poly c∣poly a := by rw [hCpoly,gcdQ_eq_gcd]; exact gcd_dvd_left _ _
  obtain ⟨q,hq,hQ,hQpoly⟩ := exactDiv_success a c hcn hcd
  have hprod : poly c*poly q=poly a := by rw [hQpoly]; exact EuclideanDomain.mul_div_cancel' hcn hcd
  have hqn : poly q≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact ha hprod.symm
  simp only [initialChain,hc,hq] at hinit
  split_ifs at hinit
  · have hh := Option.some.inj hinit
    cases hh
  · have hhead := congrArg (fun l : List (List ℤ) => l.head?) (Option.some.inj hinit)
    simp only [List.head?_cons,Option.some.injEq] at hhead
    intro x
    rw [← hhead,primitive_polynomialQ q hqn,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    have hs : (Rat.castHom ℝ) (primitiveScale q)≠0 := by
      change (primitiveScale q : ℝ)≠0
      exact_mod_cast (primitiveScale_pos q hqn).ne'
    simp only [mul_eq_zero,hs,false_or]
    rw [hQpoly,hCpoly]
    exact quotient_real_roots (poly a) ha hd x

end ActualSturmRootset


namespace ActualSturmVariations

/-- Construction for flips in the sturm model. -/
def flips : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a::b::xs => (if a=b then 0 else 1)+flips (b::xs)

/-- Construction for signs in the sturm model. -/
def signs : List ℝ → List Bool
  | [] => []
  | x::xs => if x=0 then signs xs else decide (0<x)::signs xs

/-- Construction for variation in the sturm model. -/
def variation (xs : List ℝ) : ℕ := flips (signs xs)

/-- An initial zero does not contribute to the sign-variation count. -/
theorem variation_zero (xs : List ℝ) : variation (0::xs)=variation xs := by
  simp [variation,signs]

/-- A list consisting of a single real number has no sign changes. -/
theorem variation_singleton (x : ℝ) : variation [x]=0 := by
  by_cases hx : x=0 <;> simp [variation,signs,hx,flips]

/-- With nonzero first two values, the variation count is that of the tail beginning at `b`, plus one precisely when `a` and `b` have opposite signs. -/
theorem variation_pair (a b : ℝ) (xs : List ℝ) (ha : a≠0) (hb : b≠0) :
    variation (a::b::xs)=(if decide (0<a)=decide (0<b) then 0 else 1)+variation (b::xs) := by
  simp only [variation,signs,ite_eq_right ha,ite_eq_right hb,flips]

/-- If `a` and `c` have opposite signs, the three values `a`, `b`, `c` contribute one sign change regardless of `b`, in addition to the count for `c :: xs`. -/
theorem variation_opposite (a b c : ℝ) (xs : List ℝ) (hac : a*c<0) :
    variation (a::b::c::xs)=1+variation (c::xs) := by
  rcases mul_neg_iff.mp hac with ⟨ha,hc⟩ | ⟨ha,hc⟩
  · have han : a≠0 := ne_of_gt ha
    have hcn : c≠0 := ne_of_lt hc
    have hcp : ¬0<c := not_lt.mpr hc.le
    by_cases hb : b=0
    · subst b
      simp [variation,signs,flips,han,hcn,ha,hcp]
    · by_cases hbp : 0<b <;> simp [variation,signs,flips,han,hb,hcn,ha,hcp,hbp]
  · have han : a≠0 := ne_of_lt ha
    have hcn : c≠0 := ne_of_gt hc
    have hap : ¬0<a := not_lt.mpr ha.le
    by_cases hb : b=0
    · subst b
      simp [variation,signs,flips,han,hcn,hap,hc]
    · by_cases hbp : 0<b <;> simp [variation,signs,flips,han,hb,hcn,hap,hc,hbp]

/-- Construction for integer Signs in the sturm model. -/
def integerSigns : List ℤ → List Bool
  | [] => []
  | x::xs => if x=0 then integerSigns xs else decide (0<x)::integerSigns xs

/-- Construction for integer Variation in the sturm model. -/
def integerVariation (xs : List ℤ) : ℕ := flips (integerSigns xs)

/-- Casting the integer list to reals preserves its sign-variation count. -/
theorem integer_cast_variation (xs : List ℤ) :
    variation (xs.map (fun z : ℤ => (z : ℝ)))=integerVariation xs := by
  have hsigns : signs (xs.map (fun z : ℤ => (z : ℝ)))=integerSigns xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x=0
      · subst x
        simpa only [List.map_cons,Int.cast_zero,signs,integerSigns,ite_eq_left rfl,ite_true] using ih
      · have hxr : (x : ℝ)≠0 := by exact_mod_cast hx
        simp only [List.map_cons,signs,integerSigns,ite_eq_right hx,ite_eq_right hxr,ih]
        congr 1
        simp only [Int.cast_pos]
  exact congrArg flips hsigns

end ActualSturmVariations


namespace ActualSturmLocalVariation
open Polynomial Filter ActualYunPrimitive ActualSturmChain ActualSturmVariations
open scoped Topology

/-- Construction for V in the sturm model. -/
def V (chain : List (List ℤ)) (x : ℝ) : ℕ := variation (chain.map (fun a => value a x))

/-- Evaluating the rational polynomial represented by an integer coefficient list is continuous as a function of the real argument. -/
theorem continuous_value (a : List ℤ) : Continuous (value a) :=
  (integerPolyQ a).continuous_eval₂ (Rat.castHom ℝ)

/-- Near a point where `value a` is nonzero, its evaluation stays nonzero and its positivity test stays constant. -/
theorem sign_eventually (a : List ℤ) (x : ℝ) (hx : value a x≠0) :
    ∀ᶠ y in 𝓝 x,(decide (0<value a y)=decide (0<value a x)) ∧ value a y≠0 := by
  by_cases hp : 0<value a x
  · have ho : IsOpen {y : ℝ | 0<value a y} := isOpen_lt continuous_const (continuous_value a)
    have hh : ∀ᶠ y in 𝓝 x,0<value a y := ho.mem_nhds hp
    filter_upwards [hh] with y hy
    exact ⟨by simp [hp,hy],ne_of_gt hy⟩
  · have hn : value a x<0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    have ho : IsOpen {y : ℝ | value a y<0} := isOpen_lt (continuous_value a) continuous_const
    have hh : ∀ᶠ y in 𝓝 x,value a y<0 := ho.mem_nhds hn
    filter_upwards [hh] with y hy
    exact ⟨by simp [hp,not_lt.mpr hy.le],ne_of_lt hy⟩

/-- A nonzero polynomial of natural degree zero evaluates to a nonzero value at every real argument. -/
theorem constant_value_nonzero (a : List ℤ) (ha : integerPolyQ a≠0)
    (hd : (integerPolyQ a).natDegree=0) (x : ℝ) : value a x≠0 := by
  have hc : (integerPolyQ a).coeff 0≠0 := by
    have hh := Polynomial.leadingCoeff_ne_zero.mpr ha
    simpa only [Polynomial.leadingCoeff,hd] using hh
  have he : integerPolyQ a=C ((integerPolyQ a).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [value,he,Polynomial.eval₂_C]
  change (((integerPolyQ a).coeff 0 : ℚ) : ℝ)≠0
  exact_mod_cast hc

/-- For a good chain, the sign-variation count is locally constant at any point where its first polynomial does not vanish. -/
theorem variation_eventually_eq (a : List ℤ) (tail : List (List ℤ))
    (hg : ChainGood (a::tail)) (x : ℝ) (hx : value a x≠0) :
    ∀ᶠ y in 𝓝 x,V (a::tail) y=V (a::tail) x := by
  induction tail using List.twoStepInduction generalizing a x with
  | nil =>
    exact Filter.Eventually.of_forall (fun y => by
      simp only [V,List.map_cons,List.map_nil,variation_singleton])
  | singleton b =>
    have hb : value b x≠0 := constant_value_nonzero b hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2 x
    filter_upwards [sign_eventually a x hx,sign_eventually b x hb] with y hay hby
    change variation [value a y,value b y]=variation [value a x,value b x]
    rw [variation_pair _ _ [] hay.2 hby.2,variation_pair _ _ [] hx hb,
      variation_singleton,variation_singleton,hay.1,hby.1]
  | cons_cons b c ys ihYs ihTail =>
    have hbt : ChainGood (b::c::ys) := hg.2.2.2.2.2
    by_cases hb : value b x=0
    · have hp : value a x*value c x<0 := hg.2.2.2.2.1 x hb
      have hc : value c x≠0 := (mul_ne_zero_iff.mp (ne_of_lt hp)).2
      have hct : ChainGood (c::ys) := hbt.2.2.2.2.2
      have hv := ihYs c hct x hc
      have ho : IsOpen {y : ℝ | value a y*value c y<0} :=
        isOpen_lt ((continuous_value a).mul (continuous_value c)) continuous_const
      have hn : ∀ᶠ y in 𝓝 x,value a y*value c y<0 := ho.mem_nhds hp
      filter_upwards [hn,hv] with y hny hvy
      change variation (value a y::value b y::value c y::ys.map (fun d => value d y))=
        variation (value a x::value b x::value c x::ys.map (fun d => value d x))
      rw [variation_opposite _ _ _ _ hny,variation_opposite _ _ _ _ hp]
      exact congrArg (fun n : ℕ => 1+n) hvy
    · have hv := ihTail c b hbt x hb
      filter_upwards [hv,sign_eventually a x hx,sign_eventually b x hb] with y hvy hay hby
      change variation (value a y::value b y::(c::ys).map (fun d => value d y))=
        variation (value a x::value b x::(c::ys).map (fun d => value d x))
      rw [variation_pair _ _ _ hay.2 hby.2,variation_pair _ _ _ hx hb,hay.1,hby.1]
      exact congrArg (fun n : ℕ => (if decide (0<value a x)=decide (0<value b x) then 0 else 1)+n) hvy

end ActualSturmLocalVariation


namespace ActualSturmHornerSign
open Polynomial ActualYunPrimitive ActualSturmChain ActualSturmVariations
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- Construction for state in the sturm model. -/
def state (a : List ℤ) (v : ℚ) : GaussianIntegerFraction :=
  rootCompactHorner (rootSharedNumerator (v,0)) (rootSharedDenominator (v,0)) a

/-- Construction for numerator in the sturm model. -/
def numerator (a : List ℤ) (v : ℚ) : ℤ := (state a v).numerator.1

/-- The denominator in the integer Horner state is positive at every rational argument. -/
theorem denominator_pos (a : List ℤ) (v : ℚ) : 0<(state a v).denominator :=
  rootCompactHorner_denominator_pos _ _ _ (rootSharedDenominator_pos (v,0))

/-- Dividing the Horner numerator by its state denominator over the reals gives the polynomial evaluation at the rational input. -/
theorem numerator_value (a : List ℤ) (v : ℚ) :
    (numerator a v : ℝ)/((state a v).denominator : ℝ)=value a (v : ℝ) := by
  have heval : gaussianPointValue (state a v)=((integerPolyQ a).eval v : ℚ) := by
    cases a with
    | nil =>
      have hp : integerPolyQ ([] : List ℤ)=0 := by
        rw [← ActualSturmArrayTools.lift_poly]
        exact ActualYunRationalArray.poly_nil
      simp only [state,rootCompactHorner,gaussianPointValue,Int.cast_zero,Nat.cast_one,zero_div,zero_mul,add_zero,hp,Polynomial.eval_zero,Rat.cast_zero]
    | cons c cs =>
      let coeff : Fin (cs.length+1) → ℤ := fun i => (c::cs).get i
      have hlist : List.ofFn coeff=c::cs := by simpa only [coeff] using (List.ofFn_get (c::cs))
      have hh := rootIntegerPolynomial_horner coeff (v,0)
      rw [← rootIntegerListPolynomial_ofFn,hlist,← integerPolyQ_map] at hh
      have hv : rootRationalCoordinate (v,0)=(Rat.castHom ℂ) v := by
        apply Complex.ext <;> simp [rootRationalCoordinate]
      rw [hv,Polynomial.eval_map_apply] at hh
      exact hh
  have hr := congrArg Complex.re heval
  have hval : value a (v : ℝ)=(((integerPolyQ a).eval v : ℚ) : ℝ) := by
    exact Polynomial.eval₂_at_apply (Rat.castHom ℝ) v
  rw [hval]
  simpa [gaussianPointValue,numerator] using hr

/-- The integer Horner numerator vanishes exactly when the polynomial vanishes at the rational argument viewed as a real number. -/
theorem numerator_zero_iff (a : List ℤ) (v : ℚ) : numerator a v=0 ↔ value a (v : ℝ)=0 := by
  have hd : ((state a v).denominator : ℝ)≠0 := by exact_mod_cast (denominator_pos a v).ne'
  rw [← numerator_value a v,div_eq_zero_iff]
  constructor
  · intro h; left; exact_mod_cast h
  · intro h; exact_mod_cast (h.resolve_right hd)

/-- The integer Horner numerator is positive exactly when the real polynomial evaluation at the rational input is positive. -/
theorem numerator_positive_iff (a : List ℤ) (v : ℚ) : 0<numerator a v ↔ 0<value a (v : ℝ) := by
  have hd : (0 : ℝ)<(state a v).denominator := by exact_mod_cast denominator_pos a v
  rw [← numerator_value a v]
  constructor
  · intro h
    exact div_pos (by exact_mod_cast h) hd
  · intro h
    have hh := (div_pos_iff_of_pos_right hd).mp h
    exact_mod_cast hh

/-- Construction for source Variation in the sturm model. -/
def sourceVariation (chain : List (List ℤ)) (v : ℚ) : ℕ :=
  integerVariation (chain.map (fun a => numerator a v))

/-- Counting sign variations from the integer numerators gives the same count as evaluating every chain polynomial over the reals and counting its sign variations. -/
theorem source_variation_value (chain : List (List ℤ)) (v : ℚ) :
    sourceVariation chain v=variation (chain.map (fun a => value a (v : ℝ))) := by
  have hsigns : integerSigns (chain.map (fun a => numerator a v))=
      signs (chain.map (fun a => value a (v : ℝ))) := by
    induction chain with
    | nil => rfl
    | cons a tail ih =>
      by_cases hn : numerator a v=0
      · have hv := (numerator_zero_iff a v).mp hn
        simp only [List.map_cons,integerSigns,signs,ite_eq_left hn,ite_eq_left hv,ih]
      · have hv : value a (v : ℝ)≠0 := by
          intro hz
          exact hn ((numerator_zero_iff a v).mpr hz)
        simp only [List.map_cons,integerSigns,signs,ite_eq_right hn,ite_eq_right hv,ih]
        congr 1
        simp only [numerator_positive_iff]
  exact congrArg flips hsigns

end ActualSturmHornerSign


namespace ActualSturmRootCrossing
open Polynomial Filter ActualYunPrimitive ActualSturmChain ActualSturmVariations ActualSturmLocalVariation
open scoped Topology

/-- If the first two real values have negative product, they contribute one sign change in addition to the count for the tail beginning at `b`. -/
theorem pair_negative (a b : ℝ) (xs : List ℝ) (hab : a*b<0) :
    variation (a::b::xs)=1+variation (b::xs) := by
  have han : a≠0 := (mul_ne_zero_iff.mp (ne_of_lt hab)).1
  have hbn : b≠0 := (mul_ne_zero_iff.mp (ne_of_lt hab)).2
  rw [variation_pair a b xs han hbn]
  rcases mul_neg_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp [ha,not_lt.mpr hb.le]
  · simp [not_lt.mpr ha.le,hb]

/-- A positive product of the first two real values leaves the sign-variation count equal to that of the tail beginning at `b`. -/
theorem pair_positive (a b : ℝ) (xs : List ℝ) (hab : 0<a*b) :
    variation (a::b::xs)=variation (b::xs) := by
  have han : a≠0 := (mul_ne_zero_iff.mp (ne_of_gt hab)).1
  have hbn : b≠0 := (mul_ne_zero_iff.mp (ne_of_gt hab)).2
  rw [variation_pair a b xs han hbn]
  rcases mul_pos_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp [ha,hb]
  · simp [not_lt.mpr ha.le,not_lt.mpr hb.le]

/-- Near a zero `x` of the head of a good chain, when the second polynomial is a positive multiple of its derivative, the variation equals the tail count at `x` plus one exactly to the left of `x`. -/
theorem root_crossing (a b : List ℤ) (tail : List (List ℤ))
    (hg : ChainGood (a::b::tail)) (s : ℚ) (hs : 0<s)
    (hderiv : integerPolyQ b=C s*(integerPolyQ a).derivative)
    (x : ℝ) (hx : value a x=0) :
    ∀ᶠ y in 𝓝 x,V (a::b::tail) y=V (b::tail) x+(if y<x then 1 else 0) := by
  have hcop := hg.2.2.2.1
  have hcopv := hcop.map (Polynomial.eval₂RingHom (Rat.castHom ℝ) x)
  change IsCoprime (value a x) (value b x) at hcopv
  rw [hx,isCoprime_zero_left] at hcopv
  have hb : value b x≠0 := hcopv.ne_zero
  let P := (integerPolyQ a).map (Rat.castHom ℝ)
  have hPx : P.eval x=0 := by simpa only [P,Polynomial.eval_map,value] using hx
  have hdiv : (X-C x : ℝ[X])∣P := Polynomial.dvd_iff_isRoot.mpr hPx
  obtain ⟨Q,hPQ⟩ := hdiv
  have hder : P.derivative.eval x=Q.eval x := by
    rw [hPQ,Polynomial.derivative_mul]
    simp
  have hG : value b x=(s : ℝ)*P.derivative.eval x := by
    dsimp only [value,P]
    rw [hderiv,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.derivative_map,Polynomial.eval_map]
    rfl
  have hQn : Q.eval x≠0 := by
    intro hz
    rw [hder,hz,mul_zero] at hG
    exact hb hG
  have hsr : (0 : ℝ)<s := by exact_mod_cast hs
  have hpos : 0<Q.eval x*value b x := by
    rw [hG,hder]
    nlinarith [mul_pos hsr (sq_pos_of_ne_zero hQn)]
  have heval : ∀ y : ℝ,value a y=(y-x)*Q.eval y := by
    intro y
    dsimp only [value]
    rw [← Polynomial.eval_map]
    change P.eval y=(y-x)*Q.eval y
    rw [hPQ,Polynomial.eval_mul]
    simp
  have ho : IsOpen {y : ℝ | 0<Q.eval y*value b y} :=
    isOpen_lt continuous_const (Q.continuous.mul (continuous_value b))
  have hp : ∀ᶠ y in 𝓝 x,0<Q.eval y*value b y := ho.mem_nhds hpos
  have hv := variation_eventually_eq b tail hg.2.2.2.2.2 x hb
  filter_upwards [hp,hv] with y hpy hvy
  by_cases hy : y<x
  · have hnegative : value a y*value b y<0 := by
      rw [heval]
      have hh := mul_neg_of_neg_of_pos (sub_neg.mpr hy) hpy
      nlinarith
    change variation (value a y::value b y::tail.map (fun c => value c y))=V (b::tail) x+_
    rw [pair_negative _ _ _ hnegative,ite_eq_left hy]
    change 1+V (b::tail) y=V (b::tail) x+1
    rw [hvy,Nat.add_comm]
  · have hright : x≤y := le_of_not_gt hy
    rw [ite_eq_right hy]
    by_cases he : y=x
    · subst y
      change variation (value a x::(b::tail).map (fun c => value c x))=V (b::tail) x+0
      rw [hx,variation_zero,Nat.add_zero]
      rfl
    · have hlt : x<y := lt_of_le_of_ne hright (Ne.symm he)
      have hpositive : 0<value a y*value b y := by
        rw [heval]
        have hh := mul_pos (sub_pos.mpr hlt) hpy
        nlinarith
      change variation (value a y::value b y::tail.map (fun c => value c y))=V (b::tail) x+0
      rw [pair_positive _ _ _ hpositive,Nat.add_zero]
      exact hvy

end ActualSturmRootCrossing


namespace ActualSturmFiniteCounts
open Filter
open scoped Topology

/-- Construction for left Count in the sturm model. -/
def leftCount (s : Finset ℝ) (x : ℝ) : ℕ := (s.filter (fun r => r≤x)).card

/-- If `x` lies outside a finite set of real numbers, then for all `y` sufficiently near `x`, every member of the set is at most `y` exactly when it is at most `x`. -/
theorem finite_order_stable (s : Finset ℝ) (x : ℝ) (hne : ∀ r∈s,r≠x) :
    ∀ᶠ y in 𝓝 x,∀ r∈s,(r≤y ↔ r≤x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (fun y r hr => by simp at hr)
  | @insert r s hrs ih =>
    have hrne : r≠x := hne r (by simp)
    have hsne : ∀ z∈s,z≠x := by intro z hz; exact hne z (by simp [hz])
    have hse := ih hsne
    have hre : ∀ᶠ y in 𝓝 x,(r≤y ↔ r≤x) := by
      by_cases hrx : r<x
      · have hh : ∀ᶠ y in 𝓝 x,r<y := isOpen_Ioi.mem_nhds hrx
        filter_upwards [hh] with y hy
        exact iff_of_true hy.le hrx.le
      · have hxr : x<r := lt_of_le_of_ne (le_of_not_gt hrx) (Ne.symm hrne)
        have hh : ∀ᶠ y in 𝓝 x,y<r := isOpen_Iio.mem_nhds hxr
        filter_upwards [hh] with y hy
        exact iff_of_false (not_le_of_gt hy) (not_le_of_gt hxr)
    filter_upwards [hre,hse] with y hry hsy
    intro z hz
    rcases Finset.mem_insert.mp hz with he | he
    · subst z; exact hry
    · exact hsy z he

/-- The same emitted instruction list satisfies `left_count_stable` with the displayed gate and query accounting. -/
theorem left_count_stable (s : Finset ℝ) (x : ℝ) (hx : x∉s) :
    ∀ᶠ y in 𝓝 x,leftCount s y=leftCount s x := by
  classical
  have hn : ∀ r∈s,r≠x := by intro r hr he; subst r; exact hx hr
  filter_upwards [finite_order_stable s x hn] with y hy
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter]
  by_cases hr : r∈s
  · simp only [hr,true_and]
    exact hy r hr
  · simp only [hr,false_and]

/-- The same emitted instruction list satisfies `left_count_insert` with the displayed gate and query accounting. -/
theorem left_count_insert (s : Finset ℝ) (x : ℝ) (hx : x∉s) (y : ℝ) :
    leftCount (insert x s) y=leftCount s y+(if x≤y then 1 else 0) := by
  classical
  have hn : x∉s.filter (fun r => r≤y) := fun hm => hx (Finset.mem_filter.mp hm).1
  unfold leftCount
  rw [Finset.filter_insert]
  by_cases hxy : x≤y
  · rw [ite_eq_left hxy,ite_eq_left hxy,Finset.card_insert_of_notMem hn]
  · rw [ite_eq_right hxy,ite_eq_right hxy,Nat.add_zero]

/-- The same emitted instruction list satisfies `left_count_crossing` with the displayed gate and query accounting. -/
theorem left_count_crossing (s : Finset ℝ) (x : ℝ) (hx : x∈s) :
    ∀ᶠ y in 𝓝 x,leftCount s y+(if y<x then 1 else 0)=leftCount s x := by
  classical
  let e := s.erase x
  have hstab : ∀ᶠ y in 𝓝 x,leftCount e y=leftCount e x := by
    apply left_count_stable e x
    simp [e]
  have hins : insert x e=s := Finset.insert_erase hx
  have hcx : leftCount s x=leftCount e x+1 := by
    have hh := left_count_insert e x (by simp [e]) x
    rw [hins,ite_eq_left (le_refl x)] at hh
    exact hh
  filter_upwards [hstab] with y hy
  have hcy := left_count_insert e x (by simp [e]) y
  rw [hins,hy] at hcy
  by_cases hyx : y<x
  · rw [ite_eq_left hyx,hcy,ite_eq_right (not_le_of_gt hyx),hcx]
  · rw [ite_eq_right hyx,hcy,ite_eq_left (le_of_not_gt hyx),hcx]

/-- The same emitted instruction list satisfies `left_count_interval` with the displayed gate and query accounting. -/
theorem left_count_interval (s : Finset ℝ) (a b : ℝ) (hab : a≤b) (hb : b∉s) :
    leftCount s b=leftCount s a+(s.filter (fun r => a<r ∧ r<b)).card := by
  classical
  let A := s.filter (fun r => r≤a)
  let I := s.filter (fun r => a<r ∧ r<b)
  let B := s.filter (fun r => r≤b)
  have hu : A∪I=B := by
    ext r
    simp only [A,I,B,Finset.mem_union,Finset.mem_filter]
    constructor
    · rintro (⟨hr,hra⟩ | ⟨hr,har,hrb⟩)
      · exact ⟨hr,hra.trans hab⟩
      · exact ⟨hr,hrb.le⟩
    · rintro ⟨hr,hrb⟩
      by_cases hra : r≤a
      · exact Or.inl ⟨hr,hra⟩
      · refine Or.inr ⟨hr,lt_of_not_ge hra,?_⟩
        have hrne : r≠b := by intro he; subst r; exact hb hr
        exact lt_of_le_of_ne hrb hrne
  have hd : Disjoint A I := by
    apply Finset.disjoint_left.mpr
    intro r hrA hrI
    have hle := (Finset.mem_filter.mp hrA).2
    have hlt := (Finset.mem_filter.mp hrI).2.1
    exact not_lt_of_ge hle hlt
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  exact hc

end ActualSturmFiniteCounts


namespace ActualSturmCount
open Polynomial Filter ActualYunPrimitive ActualSturmChain ActualSturmVariations
open ActualSturmLocalVariation ActualSturmRootCrossing ActualSturmFiniteCounts ActualSturmHornerSign
open scoped Topology

/-- Construction for real Roots in the sturm model. -/
def realRoots (a : List ℤ) : Finset ℝ :=
  ((integerPolyQ a).map (Rat.castHom ℝ)).roots.toFinset

/-- For a nonzero polynomial, membership in its real root finset is equivalent to vanishing at the given real argument. -/
theorem realRoots_mem (a : List ℤ) (ha : integerPolyQ a≠0) (x : ℝ) :
    x∈realRoots a ↔ value a x=0 := by
  unfold realRoots
  rw [Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero ha)]
  change ((integerPolyQ a).map (Rat.castHom ℝ)).eval x=0 ↔ _
  rw [Polynomial.eval_map]
  rfl

/-- The same emitted instruction list satisfies `variation_interval_count` with the displayed gate and query accounting. -/
theorem variation_interval_count (a b : List ℤ) (tail : List (List ℤ))
    (hg : ChainGood (a::b::tail)) (s : ℚ) (hs : 0<s)
    (hderiv : integerPolyQ b=C s*(integerPolyQ a).derivative)
    (left right : ℝ) (hab : left≤right) (hr : value a right≠0) :
    V (a::b::tail) left=V (a::b::tail) right+
      ((realRoots a).filter (fun r => left<r ∧ r<right)).card := by
  classical
  let S := realRoots a
  let J := fun x : ℝ => V (a::b::tail) x+leftCount S x
  have han : integerPolyQ a≠0 := hg.2.1
  have hJ : IsLocallyConstant J := by
    apply (IsLocallyConstant.iff_eventually_eq J).mpr
    intro x
    by_cases hx : value a x=0
    · have hm : x∈S := (realRoots_mem a han x).mpr hx
      have hv := root_crossing a b tail hg s hs hderiv x hx
      have hc := left_count_crossing S x hm
      have hVx : V (a::b::tail) x=V (b::tail) x := by
        change variation (value a x::(b::tail).map (fun c => value c x))=V (b::tail) x
        rw [hx,variation_zero]
        rfl
      filter_upwards [hv,hc] with y hvy hcy
      change V (a::b::tail) y+leftCount S y=V (a::b::tail) x+leftCount S x
      rw [hvy,hVx]
      omega
    · have hm : x∉S := fun hh => hx ((realRoots_mem a han x).mp hh)
      have hv := variation_eventually_eq a (b::tail) hg x hx
      have hc := left_count_stable S x hm
      filter_upwards [hv,hc] with y hvy hcy
      change V (a::b::tail) y+leftCount S y=V (a::b::tail) x+leftCount S x
      rw [hvy,hcy]
  have he := hJ.apply_eq_of_preconnectedSpace left right
  have hrS : right∉S := fun hh => hr ((realRoots_mem a han right).mp hh)
  have hc := left_count_interval S left right hab hrS
  dsimp only [J] at he
  rw [hc] at he
  change V (a::b::tail) left=V (a::b::tail) right+(S.filter (fun r => left<r ∧ r<right)).card
  omega

/-- The same emitted instruction list satisfies `source_variation_interval_count` with the displayed gate and query accounting. -/
theorem source_variation_interval_count (a b : List ℤ) (tail : List (List ℤ))
    (hg : ChainGood (a::b::tail)) (s : ℚ) (hs : 0<s)
    (hderiv : integerPolyQ b=C s*(integerPolyQ a).derivative)
    (left right : ℚ) (hab : left≤right) (hr : value a (right : ℝ)≠0) :
    sourceVariation (a::b::tail) left=sourceVariation (a::b::tail) right+
      ((realRoots a).filter (fun r => (left : ℝ)<r ∧ r<(right : ℝ))).card := by
  rw [source_variation_value,source_variation_value]
  exact variation_interval_count a b tail hg s hs hderiv left right (by exact_mod_cast hab) hr

end ActualSturmCount


namespace ActualSturmSourceCount
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualSturmArrayTools ActualSturmInitialization ActualSturmChain ActualSturmRootset
open ActualSturmCount ActualSturmHornerSign

/-- Construction for input Roots in the sturm model. -/
def inputRoots (a : List ℚ) : Finset ℝ := ((poly a).map (Rat.castHom ℝ)).roots.toFinset

/-- The same emitted instruction list satisfies `computed_chain_counts` with the displayed gate and query accounting. -/
theorem computed_chain_counts (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) :
    ∃ f g xs,sourceChain a=some (f::g::xs) ∧ ChainGood (f::g::xs) ∧
      (integerPolyQ f).Separable ∧
      ∀ left right : ℚ,left≤right → (poly a).eval right≠0 →
        sourceVariation (f::g::xs) left=sourceVariation (f::g::xs) right+
          ((inputRoots a).filter (fun r => (left : ℝ)<r ∧ r<(right : ℝ))).card := by
  classical
  obtain ⟨f,g,hinit,hfc,hgc,hsep,hfd,hfdle,hgn,hcop,s,hs,hg⟩ := initialization_success a hcan ha hd
  have hgnil : lift g≠[] := (canonical_nonzero _ hgc).mpr (by rw [lift_poly]; exact hgn)
  have hfnil : lift f≠[] := (canonical_nonzero _ hfc).mpr (by rw [lift_poly]; exact hsep.ne_zero)
  have hfl := canonical_length (lift f) hfc hfnil
  have hgl := canonical_length (lift g) hgc hgnil
  rw [lift_poly] at hfl hgl
  simp only [lift,List.length_map] at hfl hgl
  have hgdegree : (integerPolyQ g).natDegree=(integerPolyQ f).derivative.natDegree := by
    rw [hg,Polynomial.natDegree_C_mul hs.ne']
  have hlen : g.length<f.length := by
    have hh := Polynomial.natDegree_derivative_lt (ne_of_gt hfd)
    omega
  obtain ⟨xs,hrun,hchain⟩ := run_success g.length f g hfc hgc hsep.ne_zero hgn hcop hlen (le_refl _)
  have hroots := initialized_real_roots a hcan ha hd f g hinit
  have hsets : realRoots f=inputRoots a := by
    ext x
    rw [realRoots_mem f hsep.ne_zero]
    unfold inputRoots
    rw [Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero ha)]
    change value f x=0 ↔ ((poly a).map (Rat.castHom ℝ)).eval x=0
    rw [Polynomial.eval_map]
    exact hroots x
  refine ⟨f,g,xs,?_,hchain,hsep,?_⟩
  · simp only [sourceChain,hinit]
    exact hrun
  · intro left right hab hr
    have hfr : value f (right : ℝ)≠0 := by
      intro hz
      have hh := (hroots (right : ℝ)).mp hz
      have hval : (poly a).eval₂ (Rat.castHom ℝ) (right : ℝ)=
          (((poly a).eval right : ℚ) : ℝ) := Polynomial.eval₂_at_apply (Rat.castHom ℝ) right
      rw [hval] at hh
      exact hr (by exact_mod_cast hh)
    have hh := source_variation_interval_count f g xs hchain s hs hg left right hab hfr
    rw [hsets] at hh
    exact hh



end ActualSturmSourceCount


namespace ActualSturmVariationLoop
open ActualSturmVariations ActualSturmHornerSign ActualSturmSourceCount ActualSturmChain
open ActualYunRationalArray ActualYunRationalCanonical

/-- Construction for signed in the sturm model. -/
def signed : List ℤ → List ℤ
  | [] => []
  | x::xs => if x=0 then signed xs else (if 0<x then 1 else -1)::signed xs

/-- Construction for zip Loop in the sturm model. -/
def zipLoop (xs : List ℤ) : ℕ :=
  ((xs.zip xs.tail).map (fun p => if p.1=p.2 then 0 else 1)).sum

/-- Construction for tag in the sturm model. -/
def tag (b : Bool) : ℤ := if b then 1 else -1
/-- The integer signs `1` and `-1` distinguish the two Boolean values under `tag`. -/
theorem tag_injective : Function.Injective tag := by decide +kernel

/-- Removing zeros and encoding each integer sign as `1` or `-1` gives the list of tags of `integerSigns xs`. -/
theorem signed_tags (xs : List ℤ) : signed xs=(integerSigns xs).map tag := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hz : x=0
    · subst x
      simp [signed,integerSigns,ih]
    · by_cases hp : 0<x <;> simp [signed,integerSigns,hz,hp,ih,tag]

/-- The adjacent-pair loop on integer tags counts exactly the Boolean flips of the original list. -/
theorem zipLoop_tags (xs : List Bool) : zipLoop (xs.map tag)=flips xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih ih1 =>
    change (if tag a=tag b then 0 else 1)+zipLoop ((b::xs).map tag)=
      (if a=b then 0 else 1)+flips (b::xs)
    simp only [tag_injective.eq_iff,ih1 b]

/-- Construction for literal Source Variation in the sturm model. -/
def literalSourceVariation (chain : List (List ℤ)) (v : ℚ) : ℕ :=
  zipLoop (signed (chain.map (fun a => numerator a v)))

/-- The literal adjacent-pair loop computes the same sign-variation count as `sourceVariation` for every chain and rational input. -/
theorem literal_variation_eq (chain : List (List ℤ)) (v : ℚ) :
    literalSourceVariation chain v=sourceVariation chain v := by
  rw [literalSourceVariation,signed_tags,zipLoop_tags]
  rfl

/-- The same emitted instruction list satisfies `computed_literal_counts` with the displayed gate and query accounting. -/
theorem computed_literal_counts (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) :
    ∃ chain,sourceChain a=some chain ∧
      ∀ left right : ℚ,left≤right → (poly a).eval right≠0 →
        literalSourceVariation chain left=literalSourceVariation chain right+
          ((inputRoots a).filter (fun r => (left : ℝ)<r ∧ r<(right : ℝ))).card := by
  obtain ⟨f,g,xs,hchain,hgood,hsep,hcount⟩ := computed_chain_counts a hcan ha hd
  refine ⟨f::g::xs,hchain,?_⟩
  intro left right hab hr
  rw [literal_variation_eq,literal_variation_eq]
  exact hcount left right hab hr



end ActualSturmVariationLoop


namespace ActualSturmCauchyBound
open Polynomial
open scoped NNReal
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Folding maximum over a rational list produces a value at least as large as the starting value. -/
theorem max_seed (xs : List ℚ) (s : ℚ) : s≤xs.foldl max s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact (le_max_left s x).trans (ih (max s x))

/-- Every member of the rational list is bounded above by the maximum folded from `s`. -/
theorem max_member (xs : List ℚ) (s x : ℚ) (hx : x∈xs) : x≤xs.foldl max s := by
  induction xs generalizing s with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with he | he
    · subst y; exact (le_max_right s x).trans (max_seed ys (max s x))
    · exact ih (max s y) he

/-- Construction for ratio in the sturm model. -/
def ratio {d : ℕ} (a : Fin (d+1) → ℤ) : ℚ :=
  (List.ofFn (fun i : Fin d => ((a i.castSucc).natAbs : ℚ)/((a (Fin.last d)).natAbs : ℚ))).foldl max 0

/-- Construction for source Ceil in the sturm model. -/
def sourceCeil (q : ℚ) : ℤ := (q.num+(q.den : ℤ)-1)/(q.den : ℤ)
/-- Construction for bound in the sturm model. -/
def bound {d : ℕ} (a : Fin (d+1) → ℤ) : ℤ := 2+sourceCeil (ratio a)

/-- Every rational `q` is bounded above by the rational cast of the integer returned by `sourceCeil q`. -/
theorem sourceCeil_upper (q : ℚ) : q≤(sourceCeil q : ℚ) := by
  have hdZ : (0 : ℤ)<q.den := by exact_mod_cast q.den_pos
  have hm := Int.emod_lt_of_pos (q.num+(q.den : ℤ)-1) hdZ
  have he := Int.mul_ediv_add_emod (q.num+(q.den : ℤ)-1) (q.den : ℤ)
  rw [mul_comm (q.den : ℤ)] at he
  have hn : q.num≤ sourceCeil q*(q.den : ℤ) := by dsimp only [sourceCeil]; omega
  have hdQ : (0 : ℚ)<q.den := by exact_mod_cast q.den_pos
  conv_lhs => rw [← q.num_div_den]
  apply (div_le_iff₀ hdQ).mpr
  exact_mod_cast hn

/-- The coefficient-ratio maximum `ratio a` is nonnegative because its initial value is zero. -/
theorem ratio_nonnegative {d : ℕ} (a : Fin (d+1) → ℤ) : 0≤ratio a := max_seed _ _

/-- Each absolute lower coefficient divided by the absolute final coefficient is at most `ratio a`. -/
theorem ratio_member {d : ℕ} (a : Fin (d+1) → ℤ) (i : Fin d) :
    ((a i.castSucc).natAbs : ℚ)/((a (Fin.last d)).natAbs : ℚ)≤ratio a :=
  max_member _ 0 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

/-- The complex norm of a cast integer equals its natural absolute value viewed as a real number. -/
theorem int_norm (z : ℤ) : ‖(z : ℂ)‖=(z.natAbs : ℝ) := by
  simp only [Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]

/-- The estimate `source_bound_positive` retains the actual parameter, input-error and normalization budgets. -/
theorem source_bound_positive {d : ℕ} (a : Fin (d+1) → ℤ) : 0<bound a := by
  have hq := ratio_nonnegative a
  have hc := sourceCeil_upper (ratio a)
  have hh : (0 : ℚ)≤ sourceCeil (ratio a) := hq.trans hc
  have hZ : (0 : ℤ)≤ sourceCeil (ratio a) := by exact_mod_cast hh
  dsimp only [bound]
  omega

/-- The estimate `source_bound_roots` retains the actual parameter, input-error and normalization budgets. -/
theorem source_bound_roots {d : ℕ} (a : Fin (d+1) → ℤ) (ha : a (Fin.last d)≠0)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z=0) : ‖z‖<(bound a : ℝ) := by
  classical
  let p := rootIntegerPolynomial a
  have hpdeg : p.natDegree=d := rootIntegerPolynomial_natDegree a ha
  have hlead : p.leadingCoeff=(a (Fin.last d) : ℂ) := by
    rw [Polynomial.leadingCoeff,hpdeg]
    change (rootIntegerPolynomial a).coeff d=(a (Fin.last d) : ℂ)
    rw [rootIntegerPolynomial_coeff,dite_eq_left (Nat.lt_succ_self _)]
    rfl
  have hlne : p.leadingCoeff≠0 := by rw [hlead]; exact_mod_cast ha
  have hpn : p≠0 := Polynomial.leadingCoeff_ne_zero.mp hlne
  let T : ℝ≥0 := ⟨(ratio a : ℝ),by exact_mod_cast ratio_nonnegative a⟩
  have hden : (0 : ℝ)<((a (Fin.last d)).natAbs : ℝ) := by
    exact_mod_cast (Int.natAbs_pos.mpr ha)
  have hs : (Finset.range p.natDegree).sup (fun k => ‖p.coeff k‖₊)≤T*‖p.leadingCoeff‖₊ := by
    apply Finset.sup_le
    intro k hk
    have hkd : k<d := by simpa only [hpdeg,Finset.mem_range] using hk
    let i : Fin d := ⟨k,hkd⟩
    have hc : p.coeff k=(a i.castSucc : ℂ) := by
      change (rootIntegerPolynomial a).coeff k=(a i.castSucc : ℂ)
      rw [rootIntegerPolynomial_coeff,dite_eq_left (by omega : k<d+1)]
      rfl
    have hq := ratio_member a i
    have hqr : ((a i.castSucc).natAbs : ℝ)/((a (Fin.last d)).natAbs : ℝ)≤(ratio a : ℝ) := by
      have hh : ((((a i.castSucc).natAbs : ℚ)/((a (Fin.last d)).natAbs : ℚ) : ℚ) : ℝ)≤(ratio a : ℝ) :=
        (Rat.cast_le (K := ℝ)).mpr hq
      simpa only [Rat.cast_div,Rat.cast_natCast] using hh
    have hr : ‖p.coeff k‖≤(ratio a : ℝ)*‖p.leadingCoeff‖ := by
      rw [hc,hlead,int_norm,int_norm]
      exact (div_le_iff₀ hden).mp hqr
    exact_mod_cast hr
  have hln : (0 : ℝ≥0)<‖p.leadingCoeff‖₊ := by
    exact_mod_cast (norm_pos_iff.mpr hlne)
  have hcauchy : p.cauchyBound≤T+1 := by
    unfold Polynomial.cauchyBound
    exact add_le_add ((div_le_iff₀ hln).mpr hs) (le_refl 1)
  have hroot : ‖z‖<(T+1 : ℝ≥0) := by
    exact_mod_cast (Polynomial.IsRoot.norm_lt_cauchyBound hpn hz).trans_le hcauchy
  have hceil : (ratio a : ℝ)≤(sourceCeil (ratio a) : ℝ) := by
    exact_mod_cast sourceCeil_upper (ratio a)
  have hb : ((T+1 : ℝ≥0) : ℝ)<(bound a : ℝ) := by
    change (ratio a : ℝ)+1<(bound a : ℝ)
    dsimp only [bound]
    push_cast
    linarith
  exact hroot.trans hb

/-- If the final coefficient is nonzero, neither `bound a` nor its negative is a complex zero of the integer input polynomial. -/
theorem source_endpoints_nonzero {d : ℕ} (a : Fin (d+1) → ℤ) (ha : a (Fin.last d)≠0) :
    (rootIntegerPolynomial a).eval (bound a : ℂ)≠0 ∧
      (rootIntegerPolynomial a).eval (-(bound a : ℂ))≠0 := by
  have hb : (0 : ℝ)<bound a := by exact_mod_cast source_bound_positive a
  constructor
  · intro hz
    have hh := source_bound_roots a ha (bound a) hz
    rw [Complex.norm_intCast,abs_of_pos hb] at hh
    exact lt_irrefl _ hh
  · intro hz
    have hh := source_bound_roots a ha (-(bound a : ℂ)) hz
    rw [norm_neg,Complex.norm_intCast,abs_of_pos hb] at hh
    exact lt_irrefl _ hh



end ActualSturmCauchyBound


namespace ActualSturmCauchyInput
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualSturmArrayTools ActualSturmChain ActualSturmCauchyBound
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for list Ratio in the sturm model. -/
def listRatio (f : List ℤ) : ℚ :=
  (f.dropLast.map (fun c => (c.natAbs : ℚ)/((f.getD (f.length-1) 0).natAbs : ℚ))).foldl max 0

/-- Construction for list Bound in the sturm model. -/
def listBound (f : List ℤ) : ℤ := 2+sourceCeil (listRatio f)

/-- Looking up the last position of `List.ofFn a` gives the coefficient at `Fin.last d`. -/
theorem ofFn_last {d : ℕ} (a : Fin (d+1) → ℤ) :
    (List.ofFn a).getD ((List.ofFn a).length-1) 0=a (Fin.last d) := by
  simp only [List.length_ofFn,Nat.add_sub_cancel,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,dite_eq_left (Nat.lt_succ_self d),Option.getD_some]
  rfl

/-- The list-based coefficient-ratio calculation agrees with the vector-based calculation on `List.ofFn a`. -/
theorem listRatio_ofFn {d : ℕ} (a : Fin (d+1) → ℤ) : listRatio (List.ofFn a)=ratio a := by
  have hd : (List.ofFn a).dropLast=List.ofFn (fun i : Fin d => a i.castSucc) := by
    rw [List.ofFn_succ']
    simp
  rw [listRatio,hd,ofFn_last,List.map_ofFn]
  rfl

/-- The estimate `listBound_ofFn` retains the actual parameter, input-error and normalization budgets. -/
theorem listBound_ofFn {d : ℕ} (a : Fin (d+1) → ℤ) : listBound (List.ofFn a)=bound a := by
  rw [listBound,listRatio_ofFn]
  rfl

/-- An integer list with nonzero zero-default lookup at its last index can be written as `List.ofFn` of a coefficient vector with nonzero final entry. -/
theorem coefficient_input (f : List ℤ) (htop : f.getD (f.length-1) 0≠0) :
    ∃ (d : ℕ) (a : Fin (d+1) → ℤ),List.ofFn a=f ∧ a (Fin.last d)≠0 := by
  cases f with
  | nil => simp at htop
  | cons c cs =>
    let a : Fin (cs.length+1) → ℤ := fun i => (c::cs).get i
    have hlist : List.ofFn a=c::cs := by simpa only [a] using (List.ofFn_get (c::cs))
    refine ⟨cs.length,a,hlist,?_⟩
    have hh := ofFn_last a
    rw [hlist] at hh
    rw [← hh]
    exact htop

/-- If the lift of `f` is canonical and its polynomial is nonzero, the last coefficient of `f` is nonzero. -/
theorem canonical_top (f : List ℤ) (hcan : Canonical (lift f)) (hn : integerPolyQ f≠0) :
    f.getD (f.length-1) 0≠0 := by
  have hne : lift f≠[] := (canonical_nonzero _ hcan).mpr (by rw [lift_poly]; exact hn)
  have hlc := Polynomial.leadingCoeff_ne_zero.mpr hn
  rw [← lift_poly,canonical_leading (lift f) hcan hne] at hlc
  have he : (lift f).getD ((lift f).length-1) 0=(f.getD (f.length-1) 0 : ℚ) := by
    dsimp only [lift]
    simp only [List.length_map]
    simpa only [Int.cast_zero] using
      (List.getD_map f 0 (n := f.length-1) (fun z : ℤ => (z : ℚ)))
  rw [he] at hlc
  exact_mod_cast hlc

/-- The estimate `list_bound_roots` retains the actual parameter, input-error and normalization budgets. -/
theorem list_bound_roots (f : List ℤ) (htop : f.getD (f.length-1) 0≠0)
    (z : ℂ) (hz : (rootIntegerListPolynomial f).eval z=0) : ‖z‖<(listBound f : ℝ) := by
  obtain ⟨d,a,hlist,ha⟩ := coefficient_input f htop
  have hh := source_bound_roots a ha z
  rw [← rootIntegerListPolynomial_ofFn,hlist] at hh
  have hb : bound a=listBound f := by rw [← listBound_ofFn,hlist]
  rw [hb] at hh
  exact hh hz

/-- A list with nonzero last coefficient has positive `listBound`, and neither that bound nor its negative is a complex zero of the represented polynomial. -/
theorem list_endpoints (f : List ℤ) (htop : f.getD (f.length-1) 0≠0) :
    0<listBound f ∧ (rootIntegerListPolynomial f).eval (listBound f : ℂ)≠0 ∧
      (rootIntegerListPolynomial f).eval (-(listBound f : ℂ))≠0 := by
  obtain ⟨d,a,hlist,ha⟩ := coefficient_input f htop
  have he := source_endpoints_nonzero a ha
  have hb : bound a=listBound f := by rw [← listBound_ofFn,hlist]
  rw [← rootIntegerListPolynomial_ofFn,hlist,hb] at he
  exact ⟨by rw [← hb]; exact source_bound_positive a,he⟩



end ActualSturmCauchyInput


namespace ActualSturmIntervalStart
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualSturmArrayTools ActualSturmInitialization ActualSturmChain ActualSturmRootset
open ActualSturmCount ActualSturmSourceCount ActualSturmHornerSign ActualSturmVariationLoop
open ActualSturmCauchyBound ActualSturmCauchyInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for evaluate in the sturm model. -/
def evaluate (f : List ℤ) (x : ℚ) : ℚ :=
  (lift f).reverse.foldl (fun acc c => acc*x+c) 0

/-- Horner evaluation of the reversed coefficient list from `seed` equals the polynomial evaluation plus `seed * x^a.length`. -/
theorem evaluate_from (a : List ℚ) (x seed : ℚ) :
    a.reverse.foldl (fun acc c => acc*x+c) seed=(poly a).eval x+seed*x^a.length := by
  induction a generalizing seed with
  | nil => simp [poly_nil]
  | cons c cs ih =>
    rw [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,
      poly_cons,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
      List.length_cons,pow_succ]
    ring

/-- The rational Horner evaluator on an integer list returns the value of its rational polynomial. -/
theorem evaluate_value (f : List ℤ) (x : ℚ) : evaluate f x=(integerPolyQ f).eval x := by
  rw [evaluate,evaluate_from,zero_mul,add_zero,lift_poly]

/-- At a rational argument the complex polynomial's evaluation equals the cast of the rational Horner value. -/
theorem rational_value_complex (f : List ℤ) (x : ℚ) :
    (rootIntegerListPolynomial f).eval (x : ℂ)=(evaluate f x : ℂ) := by
  rw [evaluate_value]
  have hh := Polynomial.eval_map_apply (f := Rat.castHom ℂ) (p := integerPolyQ f) x
  rw [integerPolyQ_map] at hh
  exact hh

/-- At a real argument the complex polynomial's evaluation equals the cast of the real evaluation `value f x`. -/
theorem real_value_complex (f : List ℤ) (x : ℝ) :
    (rootIntegerListPolynomial f).eval (x : ℂ)=(value f x : ℂ) := by
  let P := (integerPolyQ f).map (Rat.castHom ℝ)
  have hhom : Complex.ofRealHom.comp (Rat.castHom ℝ)=Rat.castHom ℂ := Subsingleton.elim _ _
  have hm : P.map Complex.ofRealHom=rootIntegerListPolynomial f := by
    dsimp only [P]
    rw [Polynomial.map_map,hhom,integerPolyQ_map]
  have hh := Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := P) x
  rw [hm] at hh
  simpa [P,Polynomial.eval_map,value] using hh

/-- For a canonical nonzero input of positive degree, the returned good chain has exactly the input's real roots in its head. The positive bound from that head encloses all those roots strictly, both endpoints are nonroots, and the endpoint variation difference equals the number of distinct roots. -/
theorem computed_initial_queue (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) :
    ∃ f g xs,sourceChain a=some (f::g::xs) ∧ ChainGood (f::g::xs) ∧
      (∀ x : ℝ,x∈inputRoots a ↔ value f x=0) ∧
      let B := listBound f
      0<B ∧ evaluate f (B : ℚ)≠0 ∧ evaluate f (-(B : ℚ))≠0 ∧
      (∀ x∈inputRoots a,-(B : ℝ)<x ∧ x<(B : ℝ)) ∧
      literalSourceVariation (f::g::xs) (-(B : ℚ))=
        literalSourceVariation (f::g::xs) (B : ℚ)+(inputRoots a).card := by
  classical
  obtain ⟨f,g,hinit,hfc,hgc,hsep,hfd,hfdle,hgn,hcop,s,hs,hg⟩ := initialization_success a hcan ha hd
  have hgnil : lift g≠[] := (canonical_nonzero _ hgc).mpr (by rw [lift_poly]; exact hgn)
  have hfnil : lift f≠[] := (canonical_nonzero _ hfc).mpr (by rw [lift_poly]; exact hsep.ne_zero)
  have hfl := canonical_length (lift f) hfc hfnil
  have hgl := canonical_length (lift g) hgc hgnil
  rw [lift_poly] at hfl hgl
  simp only [lift,List.length_map] at hfl hgl
  have hgdegree : (integerPolyQ g).natDegree=(integerPolyQ f).derivative.natDegree := by
    rw [hg,Polynomial.natDegree_C_mul hs.ne']
  have hlen : g.length<f.length := by
    have hh := Polynomial.natDegree_derivative_lt (ne_of_gt hfd)
    omega
  obtain ⟨xs,hrun,hchain⟩ := run_success g.length f g hfc hgc hsep.ne_zero hgn hcop hlen (le_refl _)
  have hroots := initialized_real_roots a hcan ha hd f g hinit
  have hsets : realRoots f=inputRoots a := by
    ext x
    rw [realRoots_mem f hsep.ne_zero]
    unfold inputRoots
    rw [Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero ha)]
    change value f x=0 ↔ ((poly a).map (Rat.castHom ℝ)).eval x=0
    rw [Polynomial.eval_map]
    exact hroots x
  have hroot : ∀ x : ℝ,x∈inputRoots a ↔ value f x=0 := by
    intro x
    rw [← hsets]
    exact realRoots_mem f hsep.ne_zero x
  have htop := canonical_top f hfc hsep.ne_zero
  let B := listBound f
  obtain ⟨hBp,hEp,hEn⟩ := list_endpoints f htop
  have hEvalp : evaluate f (B : ℚ)≠0 := by
    intro hz
    have hh := rational_value_complex f (B : ℚ)
    rw [hz,Rat.cast_zero] at hh
    exact hEp (by simpa using hh)
  have hEvaln : evaluate f (-(B : ℚ))≠0 := by
    intro hz
    have hh := rational_value_complex f (-(B : ℚ))
    rw [hz,Rat.cast_zero] at hh
    exact hEn (by simpa using hh)
  have hfp : value f (B : ℝ)≠0 := by
    intro hz
    have hh := real_value_complex f (B : ℝ)
    rw [hz,Complex.ofReal_zero] at hh
    exact hEp (by simpa using hh)
  have hcapture : ∀ x∈inputRoots a,-(B : ℝ)<x ∧ x<(B : ℝ) := by
    intro x hx
    have hfx := (hroot x).mp hx
    have hh := real_value_complex f x
    rw [hfx,Complex.ofReal_zero] at hh
    have hn := list_bound_roots f htop (x : ℂ) hh
    rw [Complex.norm_real] at hn
    exact abs_lt.mp hn
  have hfilter : (realRoots f).filter (fun r => ((-(B : ℚ) : ℚ) : ℝ)<r ∧ r<((B : ℚ) : ℝ))=realRoots f := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    rw [hsets] at hx
    simpa only [Rat.cast_neg,Rat.cast_intCast] using hcapture x hx
  have horder : -(B : ℚ)≤(B : ℚ) := by
    have hp : (0 : ℚ)<B := by exact_mod_cast hBp
    linarith
  have hcount := source_variation_interval_count f g xs hchain s hs hg (-(B : ℚ)) (B : ℚ) horder hfp
  rw [← literal_variation_eq,← literal_variation_eq,hfilter,hsets] at hcount
  refine ⟨f,g,xs,?_,hchain,hroot,hBp,hEvalp,hEvaln,hcapture,hcount⟩
  simp only [sourceChain,hinit]
  exact hrun

end ActualSturmIntervalStart


namespace ActualSturmQueueSplit
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualSturmSourceCount
open ActualSturmVariationLoop ActualSturmChain

/-- Construction for roots In in the sturm model. -/
def rootsIn (S : Finset ℝ) (a b : ℚ) : Finset ℝ :=
  S.filter (fun r => (a : ℝ)<r ∧ r<(b : ℝ))

/-- Splitting at a strict interior point `c` outside `S` partitions the members of `S` in `(a, b)` into two disjoint sets in `(a, c)` and `(c, b)`. -/
theorem root_partition (S : Finset ℝ) (a c b : ℚ) (hac : a<c) (hcb : c<b) (hc : (c : ℝ)∉S) :
    rootsIn S a b=rootsIn S a c∪rootsIn S c b ∧ Disjoint (rootsIn S a c) (rootsIn S c b) := by
  classical
  have hacR : (a : ℝ)<c := by exact_mod_cast hac
  have hcbR : (c : ℝ)<b := by exact_mod_cast hcb
  constructor
  · ext x
    simp only [rootsIn,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hx,hax,hxb⟩
      by_cases hxc : x<(c : ℝ)
      · exact Or.inl ⟨hx,hax,hxc⟩
      · have hne : (c : ℝ)≠x := by intro he; subst x; exact hc hx
        exact Or.inr ⟨hx,lt_of_le_of_ne (le_of_not_gt hxc) hne,hxb⟩
    · rintro (⟨hx,hax,hxc⟩ | ⟨hx,hcx,hxb⟩)
      · exact ⟨hx,hax,hxc.trans hcbR⟩
      · exact ⟨hx,hacR.trans hcx,hxb⟩
  · apply Finset.disjoint_left.mpr
    intro x hleft hright
    have hl := (Finset.mem_filter.mp hleft).2.2
    have hr := (Finset.mem_filter.mp hright).2.1
    exact lt_asymm hl hr

/-- Data and invariants for Box in the sturm model. -/
structure Box where
  left : ℚ
  right : ℚ
  count : ℤ

/-- Construction for Good Box in the sturm model. -/
def GoodBox (S : Finset ℝ) (b : Box) : Prop :=
  b.left<b.right ∧ (b.left : ℝ)∉S ∧ (b.right : ℝ)∉S ∧
    b.count=((rootsIn S b.left b.right).card : ℤ)

/-- Construction for delta in the sturm model. -/
def delta (chain : List (List ℤ)) (a b : ℚ) : ℤ :=
  (literalSourceVariation chain a : ℤ)-(literalSourceVariation chain b : ℤ)

/-- Construction for split in the sturm model. -/
def split (chain : List (List ℤ)) (b : Box) (c : ℚ) : Box×Box :=
  (⟨b.left,c,delta chain b.left c⟩,⟨c,b.right,b.count-delta chain b.left c⟩)

/-- Given a good box, an interior nonroot cut, and a correct variation count for its left piece, both split boxes are good with nonnegative counts whose sum is the original count. -/
theorem split_good (S : Finset ℝ) (chain : List (List ℤ)) (b : Box) (c : ℚ)
    (hb : GoodBox S b) (hac : b.left<c) (hcb : c<b.right) (hc : (c : ℝ)∉S)
    (hleft : delta chain b.left c=((rootsIn S b.left c).card : ℤ)) :
    GoodBox S (split chain b c).1 ∧ GoodBox S (split chain b c).2 ∧
      0≤(split chain b c).1.count ∧ 0≤(split chain b c).2.count ∧
      b.count=(split chain b c).1.count+(split chain b c).2.count := by
  obtain ⟨hp,hd⟩ := root_partition S b.left c b.right hac hcb hc
  have hcard := Finset.card_union_of_disjoint hd
  rw [← hp] at hcard
  have hcZ : ((rootsIn S b.left b.right).card : ℤ)=
      ((rootsIn S b.left c).card : ℤ)+((rootsIn S c b.right).card : ℤ) := by exact_mod_cast hcard
  have hright : b.count-delta chain b.left c=((rootsIn S c b.right).card : ℤ) := by
    rw [hb.2.2.2,hleft]
    omega
  refine ⟨⟨hac,hb.2.1,hc,hleft⟩,⟨hcb,hc,hb.2.2.1,hright⟩,?_,?_,?_⟩
  · change 0≤delta chain b.left c
    rw [hleft]
    exact Int.natCast_nonneg _
  · change 0≤b.count-delta chain b.left c
    rw [hright]
    exact Int.natCast_nonneg _
  · change b.count=delta chain b.left c+(b.count-delta chain b.left c)
    omega

/-- For a nonzero input polynomial, a rational `c` lies in the real root finset exactly when the rational evaluation at `c` is zero. -/
theorem input_mem_rational (a : List ℚ) (ha : poly a≠0) (c : ℚ) :
    (c : ℝ)∈inputRoots a ↔ (poly a).eval c=0 := by
  unfold inputRoots
  rw [Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero ha)]
  change ((poly a).map (Rat.castHom ℝ)).eval (c : ℝ)=0 ↔ _
  rw [Polynomial.eval_map]
  have hv : (poly a).eval₂ (Rat.castHom ℝ) (c : ℝ)=(((poly a).eval c : ℚ) : ℝ) :=
    Polynomial.eval₂_at_apply (Rat.castHom ℝ) c
  rw [hv]
  constructor <;> intro h <;> exact_mod_cast h

/-- For canonical nonzero input of positive degree, a good box split at an interior nonroot using the returned source chain yields two good boxes with nonnegative counts adding to the original count. -/
theorem computed_split (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (b : Box) (hb : GoodBox (inputRoots a) b)
    (c : ℚ) (hac : b.left<c) (hcb : c<b.right) (hc : (c : ℝ)∉inputRoots a) :
    ∃ chain,sourceChain a=some chain ∧
      GoodBox (inputRoots a) (split chain b c).1 ∧ GoodBox (inputRoots a) (split chain b c).2 ∧
      0≤(split chain b c).1.count ∧ 0≤(split chain b c).2.count ∧
      b.count=(split chain b c).1.count+(split chain b c).2.count := by
  obtain ⟨chain,hchain,hcount⟩ := computed_literal_counts a hcan ha hd
  have hcn : (poly a).eval c≠0 := fun hz => hc ((input_mem_rational a ha c).mpr hz)
  have hh := hcount b.left c hac.le hcn
  have hleft : delta chain b.left c=((rootsIn (inputRoots a) b.left c).card : ℤ) := by
    have hZ : (literalSourceVariation chain b.left : ℤ)=
        (literalSourceVariation chain c : ℤ)+((rootsIn (inputRoots a) b.left c).card : ℤ) := by exact_mod_cast hh
    dsimp only [delta]
    omega
  exact ⟨chain,hchain,split_good _ chain b c hb hac hcb hc hleft⟩

end ActualSturmQueueSplit


namespace ActualSturmCutInput
open Polynomial ActualYunPrimitive ActualSturmArrayTools ActualSturmHornerSign

/-- Construction for cuts in the sturm model. -/
def cuts (f : List ℤ) (left right : ℚ) : List ℚ :=
  List.ofFn (fun i : Fin f.length => left+(right-left)*
    (1/4+((i.val+1 : ℕ) : ℚ)/(2*((f.length+1 : ℕ) : ℚ))))

/-- Construction for pick in the sturm model. -/
def pick (f : List ℤ) : List ℚ → Option ℚ
  | [] => none
  | v::vs => if numerator f v=0 then pick f vs else some v

/-- Construction for choose in the sturm model. -/
def choose (f : List ℤ) (left right : ℚ) : Option ℚ := pick f (cuts f left right)

/-- On a list made from a `Fin (d + 1)` coefficient vector, `cuts` enumerates the same candidates as the vector-based search. -/
theorem cuts_ofFn {d : ℕ} (a : Fin (d+1) → ℤ) (left right : ℚ) :
    cuts (List.ofFn a) left right=List.ofFn (ActualSturmCutSearch.candidate d left right) := by
  simp only [cuts,List.length_ofFn,Nat.cast_add,Nat.cast_one]
  have hh : ((d : ℚ)+1)+1=(d : ℚ)+2 := by ring
  rw [hh]
  apply congrArg (fun f : Fin (d+1) → ℚ => List.ofFn f)
  funext i
  simp only [ActualSturmCutSearch.candidate,Nat.cast_add,Nat.cast_one,Fin.val_cast]

/-- With coefficients supplied as `List.ofFn a`, the list-based picker agrees with scanning the same candidates using `a`. -/
theorem pick_ofFn {d : ℕ} (a : Fin (d+1) → ℤ) (vs : List ℚ) :
    pick (List.ofFn a) vs=ActualSturmCutSearch.scan a vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (if numerator (List.ofFn a) v=0 then pick (List.ofFn a) vs else some v)=
      (if ActualSturmCutSearch.numerator a v=0 then ActualSturmCutSearch.scan a vs else some v)
    have hn : numerator (List.ofFn a) v=ActualSturmCutSearch.numerator a v := rfl
    rw [hn,ih]

/-- Choosing a cut with the list `List.ofFn a` agrees with the vector-based cut search on `a`. -/
theorem choose_ofFn {d : ℕ} (a : Fin (d+1) → ℤ) (left right : ℚ) :
    choose (List.ofFn a) left right=ActualSturmCutSearch.choose a left right := by
  rw [choose,cuts_ofFn,pick_ofFn]
  rfl

/-- With a nonzero integer polynomial and ordered endpoints, the chooser returns a point strictly inside the middle half with nonzero numerator and evaluation. Both pieces have length at most three quarters of the original. -/
theorem choose_success (f : List ℤ) (hn : integerPolyQ f≠0) (left right : ℚ) (hab : left<right) :
    ∃ v,choose f left right=some v ∧ numerator f v≠0 ∧ (integerPolyQ f).eval v≠0 ∧
      left+(right-left)/4<v ∧ v<left+3*(right-left)/4 ∧
      v-left≤3*(right-left)/4 ∧ right-v≤3*(right-left)/4 := by
  cases f with
  | nil =>
    have hz : integerPolyQ ([] : List ℤ)=0 := by rw [← lift_poly]; exact ActualYunRationalArray.poly_nil
    exact (hn hz).elim
  | cons c cs =>
    let a : Fin (cs.length+1) → ℤ := fun i => (c::cs).get i
    have hlist : List.ofFn a=c::cs := by simpa only [a] using (List.ofFn_get (c::cs))
    have ha : ActualSturmCutSearch.qpoly a≠0 := by rw [ActualSturmCutSearch.qpoly,hlist]; exact hn
    obtain ⟨v,hv,hnum,heval,hlo,hhi,hwl,hwr⟩ := ActualSturmCutSearch.choose_success a ha left right hab
    have hchoose : choose (c::cs) left right=some v := by rw [← hlist,choose_ofFn]; exact hv
    have hnum' : numerator (c::cs) v≠0 := by
      have he : numerator (c::cs) v=ActualSturmCutSearch.numerator a v := by rw [← hlist]; rfl
      rw [he]
      exact hnum
    have heval' : (integerPolyQ (c::cs)).eval v≠0 := by
      simpa only [ActualSturmCutSearch.qpoly,hlist] using heval
    exact ⟨v,hchoose,hnum',heval',hlo,hhi,hwl,hwr⟩



end ActualSturmCutInput


namespace ActualSturmQueueReady
open Polynomial ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualSturmChain ActualSturmSourceCount ActualSturmHornerSign ActualSturmVariationLoop
open ActualSturmCauchyInput ActualSturmIntervalStart ActualSturmQueueSplit

/-- Construction for initial Box in the sturm model. -/
def initialBox (chain : List (List ℤ)) (f : List ℤ) : Box :=
  let B := listBound f
  ⟨-(B : ℚ),(B : ℚ),delta chain (-(B : ℚ)) (B : ℚ)⟩

/-- Construction for prepare in the sturm model. -/
def prepare (a : List ℚ) : Option (List (List ℤ)×Box) :=
  match sourceChain a with
  | some (f::tail) =>
    let B := listBound f
    if evaluate f (B : ℚ)=0 ∨ evaluate f (-(B : ℚ))=0 then none else
      some (f::tail,initialBox (f::tail) f)
  | _ => none

/-- For canonical nonzero input of positive degree, preparation returns a good source chain and good initial box. The zeros of the chain head are precisely the input's real roots. -/
theorem prepare_success (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) :
    ∃ f g xs,sourceChain a=some (f::g::xs) ∧
      prepare a=some (f::g::xs,initialBox (f::g::xs) f) ∧
      ChainGood (f::g::xs) ∧ GoodBox (inputRoots a) (initialBox (f::g::xs) f) ∧
      (∀ x : ℝ,x∈inputRoots a ↔ value f x=0) := by
  classical
  obtain ⟨f,g,xs,hsource,hgood,hroots,hBp,hEp,hEn,hcapture,hcount⟩ := computed_initial_queue a hcan ha hd
  let B := listBound f
  have hguard : ¬(evaluate f (B : ℚ)=0 ∨ evaluate f (-(B : ℚ))=0) := not_or_intro hEp hEn
  have hprepare : prepare a=some (f::g::xs,initialBox (f::g::xs) f) := by
    simp only [prepare,hsource]
    rw [ite_eq_right hguard]
  have hpos : (0 : ℚ)<B := by exact_mod_cast hBp
  have hleft : ((-(B : ℚ) : ℚ) : ℝ)∉inputRoots a := by
    intro hm
    have hh := (hcapture _ hm).1
    exact lt_irrefl (-(B : ℝ)) (by simpa only [Rat.cast_neg,Rat.cast_intCast] using hh)
  have hright : ((B : ℚ) : ℝ)∉inputRoots a := by
    intro hm
    have hh := (hcapture _ hm).2
    exact lt_irrefl (B : ℝ) (by simpa only [Rat.cast_intCast] using hh)
  have hfilt : rootsIn (inputRoots a) (-(B : ℚ)) (B : ℚ)=inputRoots a := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    simpa only [Rat.cast_neg,Rat.cast_intCast] using hcapture x hx
  have hdelta : delta (f::g::xs) (-(B : ℚ)) (B : ℚ)=((inputRoots a).card : ℤ) := by
    have hh : (literalSourceVariation (f::g::xs) (-(B : ℚ)) : ℤ)=
      (literalSourceVariation (f::g::xs) (B : ℚ) : ℤ)+((inputRoots a).card : ℤ) := by exact_mod_cast hcount
    dsimp only [delta]
    omega
  have hb : GoodBox (inputRoots a) (initialBox (f::g::xs) f) := by
    refine ⟨by change -(B : ℚ)<(B : ℚ); linarith,hleft,hright,?_⟩
    change delta (f::g::xs) (-(B : ℚ)) (B : ℚ)=
      ((rootsIn (inputRoots a) (-(B : ℚ)) (B : ℚ)).card : ℤ)
    rw [hdelta,hfilt]
  exact ⟨f,g,xs,hsource,hprepare,hgood,hb,hroots⟩

/-- Construction for advance in the sturm model. -/
def advance (chain : List (List ℤ)) (f : List ℤ) (b : Box) : Option (Box×Box) :=
  (ActualSturmCutInput.choose f b.left b.right).map (fun c => split chain b c)

/-- For canonical nonzero positive-degree input and a returned source chain whose nonzero head has the input's real zeros, advancing a good box chooses a cut and returns two good boxes. Their nonnegative counts sum to the original, and each width is at most three quarters of the original width. -/
theorem advance_success (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (f : List ℤ) (tail : List (List ℤ))
    (hsource : sourceChain a=some (f::tail)) (hfn : integerPolyQ f≠0)
    (hroots : ∀ x : ℝ,x∈inputRoots a ↔ value f x=0)
    (b : Box) (hb : GoodBox (inputRoots a) b) :
    ∃ c,ActualSturmCutInput.choose f b.left b.right=some c ∧
      advance (f::tail) f b=some (split (f::tail) b c) ∧
      GoodBox (inputRoots a) (split (f::tail) b c).1 ∧
      GoodBox (inputRoots a) (split (f::tail) b c).2 ∧
      0≤(split (f::tail) b c).1.count ∧ 0≤(split (f::tail) b c).2.count ∧
      b.count=(split (f::tail) b c).1.count+(split (f::tail) b c).2.count ∧
      (split (f::tail) b c).1.right-(split (f::tail) b c).1.left≤3*(b.right-b.left)/4 ∧
      (split (f::tail) b c).2.right-(split (f::tail) b c).2.left≤3*(b.right-b.left)/4 := by
  obtain ⟨c,hc,hnum,heval,hlo,hhi,hwl,hwr⟩ := ActualSturmCutInput.choose_success f hfn b.left b.right hb.1
  have hcl : b.left<c := by linarith [hb.1]
  have hcr : c<b.right := by linarith [hb.1]
  have hcS : (c : ℝ)∉inputRoots a := by
    intro hm
    have hzero := (hroots (c : ℝ)).mp hm
    exact hnum ((numerator_zero_iff f c).mpr hzero)
  obtain ⟨chain,hchain,hgl,hgr,hnl,hnr,hcons⟩ := computed_split a hcan ha hd b hb c hcl hcr hcS
  have he : chain=f::tail := Option.some.inj (hchain.symm.trans hsource)
  subst chain
  refine ⟨c,hc,?_,hgl,hgr,hnl,hnr,hcons,hwl,hwr⟩
  simp only [advance,hc,Option.map_some]

end ActualSturmQueueReady


namespace ActualSturmQueueRank
open ActualSturmQueueSplit

/-- Construction for distances in the sturm model. -/
def distances (S : Finset ℝ) : Finset ℝ :=
  ((S.product S).filter (fun p => p.1≠p.2)).image (fun p => |p.1-p.2|)

/-- The absolute distance between distinct members of `S` belongs to its finset of pairwise distances. -/
theorem distance_member (S : Finset ℝ) (x y : ℝ) (hx : x∈S) (hy : y∈S) (hne : x≠y) :
    |x-y|∈distances S := by
  classical
  exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hne⟩,rfl⟩

/-- Every finite real set admits a positive lower bound on the absolute distance between any two distinct members. -/
theorem exists_gap (S : Finset ℝ) :
    ∃ gap : ℝ,0<gap ∧ ∀ x∈S,∀ y∈S,x≠y → gap≤|x-y| := by
  classical
  by_cases hd : (distances S).Nonempty
  · refine ⟨(distances S).min' hd,?_,?_⟩
    · have hm := Finset.min'_mem (distances S) hd
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
      have hne := (Finset.mem_filter.mp hp).2
      have hh : 0 < |p.1-p.2| := abs_pos.mpr (sub_ne_zero.mpr hne)
      exact he ▸ hh
    · intro x hx y hy hne
      exact Finset.min'_le _ _ (distance_member S x y hx hy hne)
  · refine ⟨1,by norm_num,?_⟩
    intro x hx y hy hne
    exact (hd ⟨|x-y|,distance_member S x y hx hy hne⟩).elim

/-- The same emitted instruction list satisfies `small_box_count` with the displayed gate and query accounting. -/
theorem small_box_count (S : Finset ℝ) (gap : ℝ)
    (hsep : ∀ x∈S,∀ y∈S,x≠y → gap≤|x-y|) (a b : ℚ)
    (hw : ((b-a : ℚ) : ℝ)≤gap/2) : (rootsIn S a b).card≤1 := by
  classical
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1<(rootsIn S a b).card by omega)
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have hdist := hsep x hx'.1 y hy'.1 hxy
  have hdiff : |x-y|<(b : ℝ)-(a : ℝ) := abs_lt.mpr ⟨by linarith [hx'.2.1,hx'.2.2,hy'.2.1,hy'.2.2],
    by linarith [hx'.2.1,hx'.2.2,hy'.2.1,hy'.2.2]⟩
  push_cast at hw
  linarith

/-- A positive starting width `w` falls at or below any positive threshold `t` after some finite number of contractions by three quarters. -/
theorem exists_small (t w : ℝ) (ht : 0<t) (hw : 0<w) :
    ∃ n : ℕ,w*(3/4 : ℝ)^n≤t := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (div_pos ht hw) (by norm_num : (3/4 : ℝ)<1)
  refine ⟨n,?_⟩
  have hh := (lt_div_iff₀ hw).mp hn
  nlinarith

/-- Construction for rank in the sturm model. -/
noncomputable def rank (t : ℝ) (ht : 0<t) (w : ℝ) : ℕ :=
  if hw : 0<w then Nat.find (exists_small t w ht hw) else 0

/-- Contracting a positive width `w` by three quarters for `rank t ht w` steps gives a width at most `t`. -/
theorem rank_spec (t : ℝ) (ht : 0<t) (w : ℝ) (hw : 0<w) :
    w*(3/4 : ℝ)^(rank t ht w)≤t := by
  rw [rank,dite_eq_left hw]
  exact Nat.find_spec (exists_small t w ht hw)

/-- If `n` contractions by three quarters are enough to reach `t` from positive `w`, the rank for that threshold is at most `n`. -/
theorem rank_le (t : ℝ) (ht : 0<t) (w : ℝ) (hw : 0<w) (n : ℕ)
    (hn : w*(3/4 : ℝ)^n≤t) : rank t ht w≤n := by
  rw [rank,dite_eq_left hw]
  exact Nat.find_min' (exists_small t w ht hw) hn

/-- A positive width of rank zero is already at or below the threshold `t`. -/
theorem rank_zero_small (t : ℝ) (ht : 0<t) (w : ℝ) (hw : 0<w) (hz : rank t ht w=0) : w≤t := by
  have hh := rank_spec t ht w hw
  rw [hz,pow_zero,mul_one] at hh
  exact hh

/-- If positive `w` has positive rank and positive `u` is at most three quarters of `w`, the rank of `u` is strictly smaller. -/
theorem rank_contract (t : ℝ) (ht : 0<t) (w u : ℝ) (hw : 0<w) (hu : 0<u)
    (hc : u≤(3/4 : ℝ)*w) (hn : 0<rank t ht w) : rank t ht u<rank t ht w := by
  let n := rank t ht w
  have hpos : 0<n := hn
  have hp : w*(3/4 : ℝ)^n≤t := rank_spec t ht w hw
  have he : (3/4 : ℝ)^n=(3/4 : ℝ)^(n-1)*(3/4 : ℝ) := by
    conv_lhs => rw [show n=(n-1)+1 by omega]
    rw [pow_succ]
  have hs : u*(3/4 : ℝ)^(n-1)≤t := by
    calc
      _ ≤ ((3/4 : ℝ)*w)*(3/4 : ℝ)^(n-1) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = w*(3/4 : ℝ)^n := by rw [he]; ring
      _ ≤ t := hp
  have hh := rank_le t ht u hu (n-1) hs
  change rank t ht u<n
  omega

/-- Construction for weight in the sturm model. -/
def weight (n : ℕ) : ℕ := 2^(n+1)-1

/-- The weight `2^(n + 1) - 1` is positive for every natural rank `n`. -/
theorem weight_positive (n : ℕ) : 0<weight n := by
  have hh : 0<2^n := Nat.pow_pos (by decide)
  dsimp only [weight]
  rw [pow_succ]
  omega

/-- The sum of the weights of any two ranks strictly below `n` is less than the weight of `n`. -/
theorem weight_children (n a b : ℕ) (ha : a<n) (hb : b<n) : weight a+weight b<weight n := by
  have hpa : 2^(a+1)≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
  have hpb : 2^(b+1)≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
  have hapos : 0<2^(a+1) := Nat.pow_pos (by decide)
  have hbpos : 0<2^(b+1) := Nat.pow_pos (by decide)
  have hnpos : 0<2^n := Nat.pow_pos (by decide)
  dsimp only [weight]
  rw [pow_succ 2 n]
  omega

end ActualSturmQueueRank


namespace ActualSturmQueuePotential
open ActualSturmQueueSplit ActualSturmQueueRank

/-- Construction for width in the sturm model. -/
def width (b : Box) : ℝ := ((b.right-b.left : ℚ) : ℝ)
/-- Construction for box Weight in the sturm model. -/
def boxWeight (t : ℝ) (ht : 0<t) (b : Box) : ℕ := weight (rank t ht (width b))
/-- Construction for potential in the sturm model. -/
def potential (t : ℝ) (ht : 0<t) (bs : List Box) : ℕ :=
  (bs.map (boxWeight t ht)).sum

/-- A good box has positive width because its right endpoint exceeds its left endpoint. -/
theorem width_positive (S : Finset ℝ) (b : Box) (hb : GoodBox S b) : 0<width b := by
  dsimp only [width]
  exact_mod_cast sub_pos.mpr hb.1

/-- If `t` is positive, at most half a lower bound on root spacing, and at most the target width, a good box that must split has positive rank. Its count is nonzero and it fails the one-root stopping test. -/
theorem rank_positive_of_branch (S : Finset ℝ) (gap target t : ℝ)
    (ht : 0<t) (htg : t≤gap/2) (htt : t≤target)
    (hsep : ∀ x∈S,∀ y∈S,x≠y → gap≤|x-y|)
    (b : Box) (hb : GoodBox S b) (hz : b.count≠0)
    (hbranch : ¬(b.count=1 ∧ width b≤target)) : 0<rank t ht (width b) := by
  by_contra hn
  have hr : rank t ht (width b)=0 := by omega
  have hw := rank_zero_small t ht (width b) (width_positive S b hb) hr
  have hc := small_box_count S gap hsep b.left b.right (hw.trans htg)
  have hcount : b.count=1 := by rw [hb.2.2.2] at hz ⊢; omega
  exact hbranch ⟨hcount,hw.trans htt⟩

/-- For good boxes, replacing a positive-rank parent by two children each at most three quarters as wide strictly decreases the queue potential. -/
theorem split_potential (S : Finset ℝ) (t : ℝ) (ht : 0<t) (b l r : Box)
    (hb : GoodBox S b) (hl : GoodBox S l) (hr : GoodBox S r)
    (hbl : width l≤(3/4 : ℝ)*width b) (hbr : width r≤(3/4 : ℝ)*width b)
    (hn : 0<rank t ht (width b)) (bs : List Box) :
    potential t ht (r::l::bs)<potential t ht (b::bs) := by
  have hlr := rank_contract t ht (width b) (width l) (width_positive S b hb)
    (width_positive S l hl) hbl hn
  have hrr := rank_contract t ht (width b) (width r) (width_positive S b hb)
    (width_positive S r hr) hbr hn
  have hh := weight_children _ _ _ hlr hrr
  simp only [potential,List.map_cons,List.sum_cons,boxWeight]
  omega

/-- Popping the first box strictly decreases the queue potential because that box has positive weight. -/
theorem pop_potential (t : ℝ) (ht : 0<t) (b : Box) (bs : List Box) :
    potential t ht bs<potential t ht (b::bs) := by
  have hh := weight_positive (rank t ht (width b))
  simp only [potential,List.map_cons,List.sum_cons,boxWeight]
  omega

end ActualSturmQueuePotential


namespace ActualSturmQueueRun
open ActualSturmQueueSplit ActualSturmQueueReady ActualSturmQueuePotential ActualSturmQueueRank
open ActualSturmChain ActualSturmSourceCount ActualYunRationalArray ActualYunRationalCanonical
open ActualYunPrimitive

/-- Construction for core in the sturm model. -/
def core (chain : List (List ℤ)) (f : List ℤ) (target : ℚ) :
    ℕ → List Box → List (ℚ×ℚ) → Option (List (ℚ×ℚ))
  | _,[],done => some done
  | 0,_::_,_ => none
  | fuel+1,b::bs,done =>
    if b.count=0 then core chain f target fuel bs done else
    if b.count=1 ∧ b.right-b.left≤target then
      core chain f target fuel bs (done++[(b.left,b.right)]) else
    match advance chain f b with
    | none => none
    | some (l,r) => core chain f target fuel (r::l::bs) done

/-- Construction for Step Good in the sturm model. -/
def StepGood (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ) : Prop :=
  ∀ b,GoodBox S b → ∃ l r,advance chain f b=some (l,r) ∧
    GoodBox S l ∧ GoodBox S r ∧
    width l≤(3/4 : ℝ)*width b ∧ width r≤(3/4 : ℝ)*width b

/-- With a correct contracting split for each good box and a positive threshold bounded by half the root gap and by the target width, fuel at least the potential of the good pending boxes suffices for `core` to return an interval list. -/
theorem core_terminates (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ)
    (target : ℚ) (gap t : ℝ) (ht : 0<t) (htg : t≤gap/2) (htt : t≤(target : ℝ))
    (hsep : ∀ x∈S,∀ y∈S,x≠y → gap≤|x-y|) (hstep : StepGood S chain f)
    (fuel : ℕ) (bs : List Box) (done : List (ℚ×ℚ))
    (hgood : ∀ b∈bs,GoodBox S b) (hfuel : potential t ht bs≤fuel) :
    ∃ result,core chain f target fuel bs done=some result := by
  induction fuel generalizing bs done with
  | zero =>
    cases bs with
    | nil => exact ⟨done,rfl⟩
    | cons b bs =>
      have hh := pop_potential t ht b bs
      omega
  | succ fuel ih =>
    cases bs with
    | nil => exact ⟨done,rfl⟩
    | cons b bs =>
      have hb := hgood b (by simp)
      have hbs : ∀ c∈bs,GoodBox S c := fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc)
      have hpop : potential t ht bs≤fuel := by have hh := pop_potential t ht b bs; omega
      by_cases hz : b.count=0
      · obtain ⟨result,hr⟩ := ih bs done hbs hpop
        exact ⟨result,by simp only [core,ite_eq_left hz]; exact hr⟩
      · by_cases hleaf : b.count=1 ∧ b.right-b.left≤target
        · obtain ⟨result,hr⟩ := ih bs (done++[(b.left,b.right)]) hbs hpop
          exact ⟨result,by simp only [core,ite_eq_right hz,ite_eq_left hleaf]; exact hr⟩
        · have hbranch : ¬(b.count=1 ∧ width b≤(target : ℝ)) := by
            rintro ⟨hc,hw⟩
            have hwQ : b.right-b.left≤target := by
              dsimp only [width] at hw
              exact_mod_cast hw
            exact hleaf ⟨hc,hwQ⟩
          have hrank := rank_positive_of_branch S gap (target : ℝ) t ht htg htt hsep b hb hz hbranch
          obtain ⟨l,r,had,hl,hr,hwl,hwr⟩ := hstep b hb
          have hnew : potential t ht (r::l::bs)≤fuel := by
            have hh := split_potential S t ht b l r hb hl hr hwl hwr hrank bs
            omega
          have hgnew : ∀ c∈r::l::bs,GoodBox S c := by
            intro c hc
            simp only [List.mem_cons] at hc
            rcases hc with rfl|rfl|hc
            · exact hr
            · exact hl
            · exact hbs c hc
          obtain ⟨result,hresult⟩ := ih (r::l::bs) done hgnew hnew
          exact ⟨result,by simp only [core,ite_eq_right hz,ite_eq_right hleaf,had]; exact hresult⟩

/-- For canonical nonzero input of positive degree, a returned source chain whose nonzero head has the input's real roots satisfies `StepGood`. Every good box can be advanced to good children with widths at most three quarters of the parent's width. -/
theorem original_step_good (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (f : List ℤ) (tail : List (List ℤ))
    (hsource : sourceChain a=some (f::tail)) (hfn : integerPolyQ f≠0)
    (hroots : ∀ x : ℝ,x∈inputRoots a ↔ value f x=0) : StepGood (inputRoots a) (f::tail) f := by
  intro b hb
  obtain ⟨c,hc,had,hl,hr,hnl,hnr,hcount,hwl,hwr⟩ :=
    advance_success a hcan ha hd f tail hsource hfn hroots b hb
  refine ⟨(split (f::tail) b c).1,(split (f::tail) b c).2,had,hl,hr,?_,?_⟩
  · dsimp only [width]
    have hh : (((split (f::tail) b c).1.right-(split (f::tail) b c).1.left : ℚ) : ℝ)≤3*((b.right-b.left : ℚ) : ℝ)/4 := by exact_mod_cast hwl
    linarith
  · dsimp only [width]
    have hh : (((split (f::tail) b c).2.right-(split (f::tail) b c).2.left : ℚ) : ℝ)≤3*((b.right-b.left : ℚ) : ℝ)/4 := by exact_mod_cast hwr
    linarith

/-- Construction for run in the sturm model. -/
def run (a : List ℚ) (target : ℚ) (fuel : ℕ) : Option (List (ℚ×ℚ)) :=
  match prepare a with
  | none => none
  | some ([],_) => none
  | some (f::tail,b) => core (f::tail) f target fuel [b] []

/-- On canonical nonzero input of positive degree, every positive target width admits fuel for which the isolation run returns a list. -/
theorem original_run_terminates (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (target : ℚ) (htarget : 0<target) :
    ∃ fuel result,run a target fuel=some result := by
  obtain ⟨f,g,xs,hsource,hprep,hchain,hbox,hroots⟩ := prepare_success a hcan ha hd
  have hfn : integerPolyQ f≠0 := hchain.2.1
  have hstep := original_step_good a hcan ha hd f (g::xs) hsource hfn hroots
  obtain ⟨gap,hgap,hsep⟩ := exists_gap (inputRoots a)
  let t : ℝ := min (target : ℝ) (gap/2)
  have htargetR : (0 : ℝ)<(target : ℝ) := by exact_mod_cast htarget
  have ht : 0<t := lt_min htargetR (by positivity)
  let bs := [initialBox (f::g::xs) f]
  let fuel := potential t ht bs
  obtain ⟨result,hrun⟩ := core_terminates (inputRoots a) (f::g::xs) f target gap t ht
    (min_le_right _ _) (min_le_left _ _) hsep hstep fuel bs []
    (by intro b hb; simp only [bs,List.mem_singleton] at hb; subst b; exact hbox) (le_refl _)
  refine ⟨fuel,result,?_⟩
  simp only [run,hprep]
  exact hrun

end ActualSturmQueueRun


namespace ActualSturmQueueCoverage
open ActualSturmQueueSplit ActualSturmQueueReady ActualSturmQueueRun
open ActualSturmChain ActualSturmSourceCount ActualYunRationalArray ActualYunRationalCanonical
open ActualYunPrimitive

/-- Construction for endpoints in the sturm model. -/
def endpoints (b : Box) : ℚ×ℚ := (b.left,b.right)
/-- Construction for hit in the sturm model. -/
noncomputable def hit (p : ℚ×ℚ) (x : ℝ) : ℕ := if (p.1 : ℝ)<x ∧ x<(p.2 : ℝ) then 1 else 0
/-- Construction for hits in the sturm model. -/
noncomputable def hits (ps : List (ℚ×ℚ)) (x : ℝ) : ℕ := (ps.map (fun p => hit p x)).sum

/-- Prepending an interval adds its hit at `x` to the hit count of the original list. -/
theorem hits_cons (p : ℚ×ℚ) (ps : List (ℚ×ℚ)) (x : ℝ) :
    hits (p::ps) x=hit p x+hits ps x := rfl

/-- The hit count of the concatenated interval lists is the sum of their hit counts at `x`. -/
theorem hits_append (ps qs : List (ℚ×ℚ)) (x : ℝ) :
    hits (ps++qs) x=hits ps x+hits qs x := by
  simp only [hits,List.map_append,List.sum_append]

/-- Construction for Good Interval in the sturm model. -/
def GoodInterval (S : Finset ℝ) (target : ℚ) (p : ℚ×ℚ) : Prop :=
  p.1<p.2 ∧ (p.1 : ℝ)∉S ∧ (p.2 : ℝ)∉S ∧
    (rootsIn S p.1 p.2).card=1 ∧ p.2-p.1≤target

/-- Construction for Covered in the sturm model. -/
def Covered (S : Finset ℝ) (bs : List Box) (done : List (ℚ×ℚ)) : Prop :=
  ∀ x∈S,hits (bs.map endpoints) x+hits done x=1

/-- Construction for Correct Step in the sturm model. -/
def CorrectStep (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ) : Prop :=
  ∀ b,GoodBox S b → ∀ l r,advance chain f b=some (l,r) →
    GoodBox S l ∧ GoodBox S r ∧
    ∀ x∈S,hit (endpoints b) x=hit (endpoints l) x+hit (endpoints r) x

/-- No member of `S` hits the open interval of a good box whose count is zero. -/
theorem zero_hit (S : Finset ℝ) (b : Box) (hb : GoodBox S b) (hz : b.count=0)
    (x : ℝ) (hx : x∈S) : hit (endpoints b) x=0 := by
  classical
  have hc : (rootsIn S b.left b.right).card=0 := by have hh := hb.2.2.2; omega
  have hn : ¬((b.left : ℝ)<x ∧ x<(b.right : ℝ)) := by
    intro hm
    have hmem : x∈rootsIn S b.left b.right := Finset.mem_filter.mpr ⟨hx,hm⟩
    rw [Finset.card_eq_zero.mp hc] at hmem
    simp at hmem
  exact ite_eq_right hn

/-- For an interior cut outside `S`, the hit of any `x` in `S` on the parent box equals the sum of its hits on the two split boxes. -/
theorem split_hit (S : Finset ℝ) (chain : List (List ℤ)) (b : Box) (c : ℚ)
    (hac : b.left<c) (hcb : c<b.right) (hc : (c : ℝ)∉S) (x : ℝ) (hx : x∈S) :
    hit (endpoints b) x=hit (endpoints (split chain b c).1) x+
      hit (endpoints (split chain b c).2) x := by
  classical
  obtain ⟨hp,hd⟩ := root_partition S b.left c b.right hac hcb hc
  have he : ((b.left : ℝ)<x ∧ x<(b.right : ℝ)) ↔
      (((b.left : ℝ)<x ∧ x<(c : ℝ)) ∨ ((c : ℝ)<x ∧ x<(b.right : ℝ))) := by
    have hh := Finset.ext_iff.mp hp x
    simpa only [rootsIn,Finset.mem_filter,Finset.mem_union,hx,true_and] using hh
  have hnot : ¬(((b.left : ℝ)<x ∧ x<(c : ℝ)) ∧ ((c : ℝ)<x ∧ x<(b.right : ℝ))) := by
    rintro ⟨hl,hr⟩
    exact lt_asymm hl.2 hr.1
  dsimp only [hit,endpoints,split]
  by_cases hl : (b.left : ℝ)<x ∧ x<(c : ℝ)
  · have hp := he.mpr (Or.inl hl)
    have hr : ¬((c : ℝ)<x ∧ x<(b.right : ℝ)) := fun hr => hnot ⟨hl,hr⟩
    simp only [ite_eq_left hp,ite_eq_left hl,ite_eq_right hr]
  · by_cases hr : (c : ℝ)<x ∧ x<(b.right : ℝ)
    · have hp := he.mpr (Or.inr hr)
      simp only [ite_eq_left hp,ite_eq_right hl,ite_eq_left hr]
    · have hp : ¬((b.left : ℝ)<x ∧ x<(b.right : ℝ)) := fun hp => (he.mp hp).elim hl hr
      simp only [ite_eq_right hp,ite_eq_right hl,ite_eq_right hr]

/-- For canonical nonzero input of positive degree and a returned source chain whose nonzero head has the input's real zeros, `CorrectStep` holds. Every successful advance of a good box returns good children and preserves the hit total of each input root. -/
theorem original_correct_step (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (f : List ℤ) (tail : List (List ℤ))
    (hsource : sourceChain a=some (f::tail)) (hfn : integerPolyQ f≠0)
    (hroots : ∀ x : ℝ,x∈inputRoots a ↔ value f x=0) : CorrectStep (inputRoots a) (f::tail) f := by
  intro b hb l r had
  obtain ⟨c,hc,had',hl,hr,hnl,hnr,hcount,hwl,hwr⟩ :=
    advance_success a hcan ha hd f tail hsource hfn hroots b hb
  have he : (l,r)=split (f::tail) b c := Option.some.inj (had.symm.trans had')
  cases he
  obtain ⟨c',hc',hnum,heval,hlo,hhi,hwL,hwR⟩ :=
    ActualSturmCutInput.choose_success f hfn b.left b.right hb.1
  have hec : c'=c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  have hcl : b.left<c := by linarith [hb.1]
  have hcr : c<b.right := by linarith [hb.1]
  have hcS : (c : ℝ)∉inputRoots a := by
    intro hm
    exact hnum ((ActualSturmHornerSign.numerator_zero_iff f c).mpr ((hroots _).mp hm))
  exact ⟨hl,hr,fun x hx => split_hit _ _ _ _ hcl hcr hcS x hx⟩

/-- With correct splits, good pending boxes, good finished intervals and one initial hit per root across both lists, a successful core run returns only good intervals and retains one hit per root. -/
theorem core_correct (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ) (target : ℚ)
    (hstep : CorrectStep S chain f) (fuel : ℕ) (bs : List Box) (done result : List (ℚ×ℚ))
    (hgood : ∀ b∈bs,GoodBox S b) (hdone : ∀ p∈done,GoodInterval S target p)
    (hcover : Covered S bs done) (hrun : core chain f target fuel bs done=some result) :
    (∀ p∈result,GoodInterval S target p) ∧ ∀ x∈S,hits result x=1 := by
  induction fuel generalizing bs done result with
  | zero =>
    cases bs with
    | nil =>
      have he : done=result := Option.some.inj hrun
      subst result
      exact ⟨hdone,by intro x hx; simpa only [Covered,List.map_nil,hits,List.sum_nil,zero_add] using hcover x hx⟩
    | cons b bs => simp only [core] at hrun; contradiction
  | succ fuel ih =>
    cases bs with
    | nil =>
      have he : done=result := Option.some.inj hrun
      subst result
      exact ⟨hdone,by intro x hx; simpa only [Covered,List.map_nil,hits,List.sum_nil,zero_add] using hcover x hx⟩
    | cons b bs =>
      have hb := hgood b (by simp)
      have hbs : ∀ c∈bs,GoodBox S c := fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc)
      by_cases hz : b.count=0
      · have hc : Covered S bs done := by
          intro x hx
          have hh := hcover x hx
          simp only [List.map_cons,hits_cons,zero_hit S b hb hz x hx,zero_add] at hh
          exact hh
        apply ih bs done result hbs hdone hc
        simpa only [core,ite_eq_left hz] using hrun
      · by_cases hleaf : b.count=1 ∧ b.right-b.left≤target
        · have hnew : GoodInterval S target (endpoints b) := by
            refine ⟨hb.1,hb.2.1,hb.2.2.1,?_,hleaf.2⟩
            have hh := hb.2.2.2
            rw [hleaf.1] at hh
            exact_mod_cast hh.symm
          have hdnew : ∀ p∈done++[endpoints b],GoodInterval S target p := by
            intro p hp
            rcases List.mem_append.mp hp with hp|hp
            · exact hdone p hp
            · simp only [List.mem_singleton] at hp; subst p; exact hnew
          have hc : Covered S bs (done++[endpoints b]) := by
            intro x hx
            have hh := hcover x hx
            simp only [List.map_cons,hits_cons] at hh
            rw [hits_append,hits_cons]
            change hits (bs.map endpoints) x+(hits done x+(hit (endpoints b) x+0))=1
            omega
          apply ih bs (done++[endpoints b]) result hbs hdnew hc
          simpa only [core,ite_eq_right hz,ite_eq_left hleaf,endpoints] using hrun
        · cases had : advance chain f b with
          | none => simp only [core,ite_eq_right hz,ite_eq_right hleaf,had] at hrun; contradiction
          | some lr =>
            obtain ⟨l,r⟩ := lr
            obtain ⟨hl,hr,hpartition⟩ := hstep b hb l r had
            have hgnew : ∀ c∈r::l::bs,GoodBox S c := by
              intro c hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl|rfl|hc
              · exact hr
              · exact hl
              · exact hbs c hc
            have hc : Covered S (r::l::bs) done := by
              intro x hx
              have hh := hcover x hx
              have hp := hpartition x hx
              simp only [List.map_cons,hits_cons] at hh ⊢
              omega
            apply ih (r::l::bs) done result hgnew hdone hc
            simpa only [core,ite_eq_right hz,ite_eq_right hleaf,had] using hrun

end ActualSturmQueueCoverage


namespace ActualSturmQueueGeometry
open ActualSturmQueueSplit ActualSturmQueueReady ActualSturmQueueRun ActualSturmQueueCoverage
open ActualSturmChain ActualYunPrimitive

/-- Construction for Apart in the sturm model. -/
def Apart (p q : ℚ×ℚ) : Prop := p.2≤q.1 ∨ q.2≤p.1
/-- Construction for Within in the sturm model. -/
def Within (p q : ℚ×ℚ) : Prop := q.1≤p.1 ∧ p.2≤q.2

/-- If two intervals are apart in one order, they are apart in the reverse order. -/
theorem apart_symm {p q : ℚ×ℚ} (h : Apart p q) : Apart q p := h.symm

/-- An interval `q` within `p` is apart from `z` whenever `p` is apart from `z`. -/
theorem apart_sub {p q z : ℚ×ℚ} (h : Apart p z) (hp : Within q p) : Apart q z := by
  rcases h with h|h
  · exact Or.inl (hp.2.trans h)
  · exact Or.inr (h.trans hp.1)

/-- Replacing `p` by two mutually apart intervals within it preserves pairwise apartness from each other and from the remaining intervals. -/
theorem separated_split (p l r : ℚ×ℚ) (ps : List (ℚ×ℚ))
    (h : (p::ps).Pairwise Apart) (hl : Within l p) (hr : Within r p) (hlr : Apart r l) :
    (r::l::ps).Pairwise Apart := by
  obtain ⟨hp,hps⟩ := List.pairwise_cons.mp h
  apply List.pairwise_cons.mpr
  constructor
  · intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact hlr
    · exact apart_sub (hp z hz) hr
  · exact List.pairwise_cons.mpr ⟨fun z hz => apart_sub (hp z hz) hl,hps⟩

/-- Moving the front pending interval to the end of the finished list preserves pairwise apartness of the combined list. -/
theorem separated_accept (p : ℚ×ℚ) (ps done : List (ℚ×ℚ))
    (h : (p::(ps++done)).Pairwise Apart) : (ps++(done++[p])).Pairwise Apart := by
  obtain ⟨hp,htail⟩ := List.pairwise_cons.mp h
  have hh : ((ps++done)++[p]).Pairwise Apart := by
    apply List.pairwise_append.mpr
    refine ⟨htail,by simp,?_⟩
    intro z hz y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact apart_symm (hp z hz)
  simpa only [List.append_assoc] using hh

/-- Construction for Shape Step in the sturm model. -/
def ShapeStep (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ) : Prop :=
  ∀ b,GoodBox S b → ∀ l r,advance chain f b=some (l,r) →
    Within (endpoints l) (endpoints b) ∧ Within (endpoints r) (endpoints b) ∧
    Apart (endpoints r) (endpoints l)

/-- If `f` represents a nonzero polynomial, every successful advance of a good box returns two boxes within the parent whose intervals are apart. -/
theorem actual_shape_step (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ)
    (hfn : integerPolyQ f≠0) : ShapeStep S chain f := by
  intro b hb l r had
  obtain ⟨c,hc,hnum,heval,hlo,hhi,hwl,hwr⟩ :=
    ActualSturmCutInput.choose_success f hfn b.left b.right hb.1
  have had' : advance chain f b=some (split chain b c) := by simp only [advance,hc,Option.map_some]
  have he : (l,r)=split chain b c := Option.some.inj (had.symm.trans had')
  cases he
  have hcl : b.left≤c := by linarith [hb.1]
  have hcr : c≤b.right := by linarith [hb.1]
  exact ⟨⟨le_refl _,hcr⟩,⟨hcl,le_refl _⟩,Or.inr (le_refl _)⟩

/-- With correct, geometrically valid splits and pairwise apart starting intervals from good pending boxes and the finished list, a successful core run returns pairwise apart intervals. -/
theorem core_separated (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ) (target : ℚ)
    (hstep : CorrectStep S chain f) (hshape : ShapeStep S chain f)
    (fuel : ℕ) (bs : List Box) (done result : List (ℚ×ℚ))
    (hgood : ∀ b∈bs,GoodBox S b) (hsep : (bs.map endpoints++done).Pairwise Apart)
    (hrun : core chain f target fuel bs done=some result) : result.Pairwise Apart := by
  induction fuel generalizing bs done result with
  | zero =>
    cases bs with
    | nil =>
      have he : done=result := Option.some.inj hrun
      subst result
      exact hsep
    | cons b bs => simp only [core] at hrun; contradiction
  | succ fuel ih =>
    cases bs with
    | nil =>
      have he : done=result := Option.some.inj hrun
      subst result
      exact hsep
    | cons b bs =>
      have hb := hgood b (by simp)
      have hbs : ∀ c∈bs,GoodBox S c := fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc)
      change (endpoints b::(bs.map endpoints++done)).Pairwise Apart at hsep
      by_cases hz : b.count=0
      · apply ih bs done result hbs (List.pairwise_cons.mp hsep).2
        simpa only [core,ite_eq_left hz] using hrun
      · by_cases hleaf : b.count=1 ∧ b.right-b.left≤target
        · apply ih bs (done++[endpoints b]) result hbs
            (separated_accept (endpoints b) (bs.map endpoints) done hsep)
          simpa only [core,ite_eq_right hz,ite_eq_left hleaf,endpoints] using hrun
        · cases had : advance chain f b with
          | none => simp only [core,ite_eq_right hz,ite_eq_right hleaf,had] at hrun; contradiction
          | some lr =>
            obtain ⟨l,r⟩ := lr
            obtain ⟨hl,hr,hpartition⟩ := hstep b hb l r had
            obtain ⟨hwithinl,hwithinr,hlr⟩ := hshape b hb l r had
            have hgnew : ∀ c∈r::l::bs,GoodBox S c := by
              intro c hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl|rfl|hc
              · exact hr
              · exact hl
              · exact hbs c hc
            have hsnew : ((r::l::bs).map endpoints++done).Pairwise Apart :=
              separated_split (endpoints b) (endpoints l) (endpoints r) (bs.map endpoints++done)
                hsep hwithinl hwithinr hlr
            apply ih (r::l::bs) done result hgnew hsnew
            simpa only [core,ite_eq_right hz,ite_eq_right hleaf,had] using hrun

end ActualSturmQueueGeometry


namespace ActualSturmIntervalSort
open ActualSturmQueueCoverage ActualSturmQueueGeometry

/-- Construction for Lex LE in the sturm model. -/
def LexLE (p q : ℚ×ℚ) : Prop := p.1<q.1 ∨ p.1=q.1 ∧ p.2≤q.2
/-- Exact rational decision procedure for the lexicographic endpoint order. -/
instance instDecidableLexLE (p q : ℚ×ℚ) : Decidable (LexLE p q) :=
  inferInstanceAs (Decidable (p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 ≤ q.2))
/-- Construction for lex Compare in the sturm model. -/
def lexCompare (p q : ℚ×ℚ) : Bool := decide (LexLE p q)
/-- Construction for sort in the sturm model. -/
def sort (ps : List (ℚ×ℚ)) : List (ℚ×ℚ) := ps.mergeSort lexCompare

/-- The lexicographic endpoint relation is transitive on rational endpoint pairs. -/
theorem lex_trans (p q r : ℚ×ℚ) (hp : LexLE p q) (hq : LexLE q r) : LexLE p r := by
  rcases hp with hp|⟨hp,hp'⟩ <;> rcases hq with hq|⟨hq,hq'⟩
  · exact Or.inl (hp.trans hq)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hp.trans hq,hp'.trans hq'⟩

/-- Any two rational endpoint pairs are comparable in the lexicographic endpoint order. -/
theorem lex_total (p q : ℚ×ℚ) : LexLE p q ∨ LexLE q p := by
  rcases lt_trichotomy p.1 q.1 with h|h|h
  · exact Or.inl (Or.inl h)
  · rcases le_total p.2 q.2 with hh|hh
    · exact Or.inl (Or.inr ⟨h,hh⟩)
    · exact Or.inr (Or.inr ⟨h.symm,hh⟩)
  · exact Or.inr (Or.inl h)

/-- Rational endpoint pairs that are lexicographically at most one another have equal endpoints. -/
theorem lex_antisymm (p q : ℚ×ℚ) (hp : LexLE p q) (hq : LexLE q p) : p=q := by
  rcases hp with hp|⟨hp,hp'⟩ <;> rcases hq with hq|⟨hq,hq'⟩
  · exact (lt_asymm hp hq).elim
  · exact (by linarith : False).elim
  · exact (by linarith : False).elim
  · exact Prod.ext hp (le_antisymm hp' hq')

/-- Sorting the interval list permutes its entries, preserving multiplicities. -/
theorem sort_perm (ps : List (ℚ×ℚ)) : (sort ps).Perm ps := List.mergeSort_perm _ _

/-- The sorted list is pairwise nondecreasing in the lexicographic order of its endpoint pairs. -/
theorem sort_ordered (ps : List (ℚ×ℚ)) : (sort ps).Pairwise LexLE := by
  classical
  have htrans : ∀ p q r,lexCompare p q → lexCompare q r → lexCompare p r := by
    intro p q r hp hq
    have hp' : LexLE p q := by
      apply of_decide_eq_true
      simpa [lexCompare] using hp
    have hq' : LexLE q r := by
      apply of_decide_eq_true
      simpa [lexCompare] using hq
    simpa [lexCompare] using decide_eq_true (lex_trans p q r hp' hq')
  have htotal : ∀ p q,lexCompare p q || lexCompare q p := by
    intro p q
    simpa [lexCompare, Bool.or_eq_true, decide_eq_true_eq] using lex_total p q
  have hh := List.pairwise_mergeSort htrans htotal ps
  simpa [sort,lexCompare,decide_eq_true_eq] using hh

/-- Every lexicographically ordered permutation of `ps` equals `sort ps`. -/
theorem canonical_sorted_value (ps qs : List (ℚ×ℚ)) (hp : qs.Perm ps) (hs : qs.Pairwise LexLE) :
    qs=sort ps :=
  List.Perm.eq_of_pairwise (fun p q _ _ => lex_antisymm p q) hs (sort_ordered ps)
    (hp.trans (sort_perm ps).symm)

/-- Sorting preserves goodness of every interval, one hit per root and pairwise apartness, and orders the result lexicographically. -/
theorem sort_preserves (S : Finset ℝ) (target : ℚ) (ps : List (ℚ×ℚ))
    (hgood : ∀ p∈ps,GoodInterval S target p) (hcover : ∀ x∈S,hits ps x=1)
    (hsep : ps.Pairwise Apart) :
    (∀ p∈sort ps,GoodInterval S target p) ∧
    (∀ x∈S,hits (sort ps) x=1) ∧ (sort ps).Pairwise Apart ∧ (sort ps).Pairwise LexLE := by
  have hp := sort_perm ps
  refine ⟨fun p hm => hgood p (hp.subset hm),?_,hsep.perm hp.symm (fun h => apart_symm h),sort_ordered ps⟩
  intro x hx
  have hh : hits (sort ps) x=hits ps x := (hp.map (fun p => hit p x)).sum_eq
  rw [hh]
  exact hcover x hx

end ActualSturmIntervalSort


namespace ActualSturmComputedIsolation
open ActualSturmQueueSplit ActualSturmQueueReady ActualSturmQueueRun ActualSturmQueueCoverage
open ActualSturmQueueGeometry ActualSturmIntervalSort ActualSturmIntervalStart ActualSturmCauchyInput
open ActualSturmChain ActualSturmSourceCount ActualYunRationalArray ActualYunRationalCanonical
open ActualYunPrimitive

/-- Construction for source Width in the sturm model. -/
def sourceWidth (bits : ℕ) : ℚ := 1/(2 : ℚ)^bits

/-- The target width `sourceWidth bits` is strictly positive at every natural precision `bits`. -/
theorem sourceWidth_positive (bits : ℕ) : 0<sourceWidth bits := by dsimp only [sourceWidth]; positivity

/-- Construction for intervals in the sturm model. -/
def intervals (a : List ℚ) (bits fuel : ℕ) : Option (List (ℚ×ℚ)) :=
  (run a (sourceWidth bits) fuel).map sort

/-- For canonical nonzero input of positive degree, each real input root has one hit in the initial box of the returned source chain with an empty finished list. -/
theorem initial_covered (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (f : List ℤ) (tail : List (List ℤ))
    (hsource : sourceChain a=some (f::tail)) :
    Covered (inputRoots a) [initialBox (f::tail) f] [] := by
  obtain ⟨f',g',xs',hs,hgood,hroots,hBp,hEp,hEn,hcapture,hcount⟩ := computed_initial_queue a hcan ha hd
  have he : f'::g'::xs'=f::tail := Option.some.inj (hs.symm.trans hsource)
  have hf : f'=f := (List.cons.inj he).1
  subst f'
  intro x hx
  have hh := hcapture x hx
  have hp : hit (endpoints (initialBox (f::tail) f)) x=1 := by
    apply ite_eq_left
    simpa only [endpoints,initialBox,Rat.cast_neg,Rat.cast_intCast] using hh
  change hit (endpoints (initialBox (f::tail) f)) x+0+0=1
  rw [hp]

/-- For canonical nonzero input of positive degree and any precision, some fuel returns lexicographically ordered, pairwise apart intervals. Each has width at most `sourceWidth bits` and exactly one real root with nonroot endpoints, and every real root is hit once. -/
theorem computed_isolation (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (bits : ℕ) :
    ∃ fuel result,intervals a bits fuel=some result ∧
      (∀ p∈result,GoodInterval (inputRoots a) (sourceWidth bits) p) ∧
      (∀ x∈inputRoots a,hits result x=1) ∧
      result.Pairwise Apart ∧ result.Pairwise LexLE := by
  obtain ⟨fuel,raw,hrun⟩ := original_run_terminates a hcan ha hd (sourceWidth bits) (sourceWidth_positive bits)
  obtain ⟨f,g,xs,hsource,hprep,hchain,hbox,hroots⟩ := prepare_success a hcan ha hd
  have hfn : integerPolyQ f≠0 := hchain.2.1
  have hstep := original_correct_step a hcan ha hd f (g::xs) hsource hfn hroots
  have hcore : core (f::g::xs) f (sourceWidth bits) fuel [initialBox (f::g::xs) f] []=some raw := by
    simpa only [ActualSturmQueueRun.run,hprep] using hrun
  have hgood : ∀ b∈[initialBox (f::g::xs) f],GoodBox (inputRoots a) b := by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hbox
  have hcover := initial_covered a hcan ha hd f (g::xs) hsource
  obtain ⟨hout,hcoverage⟩ := core_correct (inputRoots a) (f::g::xs) f (sourceWidth bits) hstep
    fuel [initialBox (f::g::xs) f] [] raw hgood (by simp) hcover hcore
  have hsep := core_separated (inputRoots a) (f::g::xs) f (sourceWidth bits) hstep
    (actual_shape_step _ _ _ hfn) fuel [initialBox (f::g::xs) f] [] raw hgood (by simp) hcore
  refine ⟨fuel,sort raw,?_,sort_preserves _ _ raw hout hcoverage hsep⟩
  simp only [intervals,hrun,Option.map_some]





end ActualSturmComputedIsolation



end RootYunInternal
end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

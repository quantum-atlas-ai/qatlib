/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

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
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Bounds

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

/-! Exact polynomial-array algorithms: Fuel.
These algorithms retain program bodies, guards, hypotheses and finite-fuel semantics. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
namespace RootYunInternal

namespace ActualFiniteFuelSearch
universe u
variable {α : Type u}

/-- Construction for fuel in the fuel model. -/
def fuel (trial : ℕ → Option α) (h : ∃ n,(trial n).isSome=true) : ℕ := Nat.find h

/-- Construction for value in the fuel model. -/
def value (trial : ℕ → Option α) (h : ∃ n,(trial n).isSome=true) : α :=
  (trial (fuel trial h)).get (Nat.find_spec h)

/-- The finite construction in `Fuel` satisfies `trial_value` under the displayed hypotheses. -/
theorem trial_value (trial : ℕ → Option α) (h : ∃ n,(trial n).isSome=true) :
    trial (fuel trial h)=some (value trial h) := by
  unfold value
  exact (Option.some_get _).symm

/-- The finite construction in `Fuel` satisfies `least_fuel` under the displayed hypotheses. -/
theorem least_fuel (trial : ℕ → Option α) (h : ∃ n,(trial n).isSome=true) (n : ℕ)
    (hn : n < fuel trial h) : trial n=none := by
  have hf := Nat.find_min h hn
  cases he : trial n with
  | none => rfl
  | some a => exact (hf (by simp only [he,Option.isSome_some])).elim

end ActualFiniteFuelSearch


namespace ActualSturmFuelSearch
open ActualSturmComputedIsolation ActualSturmQueueRun ActualSturmQueueSplit ActualSturmIntervalSort
open ActualSturmQueueCoverage ActualSturmQueueGeometry ActualSturmQueueReady ActualSturmSourceCount
open ActualYunRationalArray ActualYunRationalCanonical

/-- The finite construction in `Fuel` satisfies `core_add` under the displayed hypotheses. -/
theorem core_add (chain : List (List ℤ)) (f : List ℤ) (target : ℚ) (fuel extra : ℕ)
    (bs : List Box) (done result : List (ℚ×ℚ))
    (h : core chain f target fuel bs done=some result) :
    core chain f target (fuel+extra) bs done=some result := by
  induction fuel generalizing bs done with
  | zero =>
    cases bs with
    | nil =>
      simp only [core] at h ⊢
      exact h
    | cons b bs => cases h
  | succ fuel ih =>
    cases bs with
    | nil =>
      simp only [core] at h ⊢
      exact h
    | cons b bs =>
      simp only [core,Nat.succ_add] at h ⊢
      by_cases hz : b.count=0
      · simp only [ite_eq_left hz] at h ⊢
        exact ih bs done h
      · simp only [ite_eq_right hz] at h ⊢
        by_cases hf : b.count=1 ∧ b.right-b.left ≤ target
        · simp only [ite_eq_left hf] at h ⊢
          exact ih bs (done++[(b.left,b.right)]) h
        · simp only [ite_eq_right hf] at h ⊢
          cases ha : advance chain f b with
          | none => simp only [ha,reduceCtorEq] at h
          | some pair =>
            rcases pair with ⟨l,r⟩
            simp only [ha] at h ⊢
            exact ih (r::l::bs) done h

/-- The finite construction in `Fuel` satisfies `run_add` under the displayed hypotheses. -/
theorem run_add (a : List ℚ) (target : ℚ) (fuel extra : ℕ) (result : List (ℚ×ℚ))
    (h : run a target fuel=some result) : run a target (fuel+extra)=some result := by
  cases hp : ActualSturmQueueReady.prepare a with
  | none => simp only [run,hp,reduceCtorEq] at h
  | some pair =>
    rcases pair with ⟨chain,b⟩
    cases chain with
    | nil => simp only [run,hp,reduceCtorEq] at h
    | cons f tail =>
      simp only [run,hp] at h ⊢
      exact core_add (f::tail) f target fuel extra [b] [] result h

/-- The finite construction in `Fuel` satisfies `intervals_add` under the displayed hypotheses. -/
theorem intervals_add (a : List ℚ) (bits fuel extra : ℕ) (result : List (ℚ×ℚ))
    (h : intervals a bits fuel=some result) : intervals a bits (fuel+extra)=some result := by
  cases hr : run a (sourceWidth bits) fuel with
  | none => simp only [intervals,hr,Option.map_none,reduceCtorEq] at h
  | some raw =>
    have hs := run_add a (sourceWidth bits) fuel extra raw hr
    simpa only [intervals,hs,hr,Option.map_some] using h

/-- The finite construction in `Fuel` satisfies `intervals_unique` under the displayed hypotheses. -/
theorem intervals_unique (a : List ℚ) (bits first second : ℕ) (x y : List (ℚ×ℚ))
    (hx : intervals a bits first=some x) (hy : intervals a bits second=some y) : x=y := by
  have h1 := intervals_add a bits first second x hx
  have h2 := intervals_add a bits second first y hy
  rw [Nat.add_comm first second] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- The finite construction in `Fuel` satisfies `exists_success` under the displayed hypotheses. -/
theorem exists_success (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0 < (poly a).natDegree) (bits : ℕ) : ∃ fuel,(intervals a bits fuel).isSome=true := by
  obtain ⟨fuel,result,hr,_,_,_⟩ := computed_isolation a hcan ha hd bits
  exact ⟨fuel,by simp only [hr,Option.isSome_some]⟩

/-- Construction for searched in the fuel model. -/
def searched (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0 < (poly a).natDegree) (bits : ℕ) : List (ℚ×ℚ) :=
  ActualFiniteFuelSearch.value (intervals a bits) (exists_success a hcan ha hd bits)

/-- The finite construction in `Fuel` satisfies `searched_correct` under the displayed hypotheses. -/
theorem searched_correct (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0 < (poly a).natDegree) (bits : ℕ) :
    (∀ p∈searched a hcan ha hd bits,GoodInterval (inputRoots a) (sourceWidth bits) p) ∧
      (∀ x∈inputRoots a,hits (searched a hcan ha hd bits) x=1) ∧
      (searched a hcan ha hd bits).Pairwise Apart ∧ (searched a hcan ha hd bits).Pairwise LexLE := by
  obtain ⟨fuel,result,hr,hgood,hcover,hsep⟩ := computed_isolation a hcan ha hd bits
  have hs : intervals a bits
      (ActualFiniteFuelSearch.fuel (intervals a bits) (exists_success a hcan ha hd bits))=
      some (searched a hcan ha hd bits) := ActualFiniteFuelSearch.trial_value _ _
  have he := intervals_unique a bits fuel _ result (searched a hcan ha hd bits) hr hs
  rw [← he]
  exact ⟨hgood,hcover,hsep⟩

end ActualSturmFuelSearch


namespace ActualSturmMassPotential
open ActualSturmQueueRun ActualSturmQueueSplit ActualSturmQueueReady
open ActualSturmQueuePotential ActualSturmQueueRank
open ActualSturmChain ActualSturmSourceCount ActualYunRationalArray ActualYunRationalCanonical
open ActualYunPrimitive

/-- The finite construction in `Fuel` satisfies `mass_children` under the displayed hypotheses. -/
theorem mass_children (c a b R x y : ℕ) (hc : 0<c) (hs : c=a+b)
    (hx : x<R) (hy : y<R) :
    (2*a*x+1)+(2*b*y+1)<2*c*R+1 := by
  have ha := Nat.mul_le_mul_left (2*a) (show x+1≤R by omega)
  have hb := Nat.mul_le_mul_left (2*b) (show y+1≤R by omega)
  nlinarith

/-- Construction for mass Weight in the fuel model. -/
def massWeight (t : ℝ) (ht : 0<t) (b : Box) : ℕ :=
  2*b.count.toNat*rank t ht (width b)+1

/-- Construction for mass Potential in the fuel model. -/
def massPotential (t : ℝ) (ht : 0<t) (bs : List Box) : ℕ :=
  (bs.map (massWeight t ht)).sum

/-- The finite construction in `Fuel` satisfies `mass_pop` under the displayed hypotheses. -/
theorem mass_pop (t : ℝ) (ht : 0<t) (b : Box) (bs : List Box) :
    massPotential t ht bs < massPotential t ht (b::bs) := by
  simp only [massPotential,List.map_cons,List.sum_cons,massWeight]
  omega

/-- The finite construction in `Fuel` satisfies `mass_split` under the displayed hypotheses. -/
theorem mass_split (S : Finset ℝ) (t : ℝ) (ht : 0<t) (b l r : Box)
    (hb : GoodBox S b) (hl : GoodBox S l) (hr : GoodBox S r)
    (hbl : width l≤(3/4 : ℝ)*width b) (hbr : width r≤(3/4 : ℝ)*width b)
    (hn : 0<rank t ht (width b)) (hz : b.count≠0) (hcounts : b.count=l.count+r.count)
    (bs : List Box) :
    massPotential t ht (r::l::bs) < massPotential t ht (b::bs) := by
  have hlr := rank_contract t ht (width b) (width l) (width_positive S b hb)
    (width_positive S l hl) hbl hn
  have hrr := rank_contract t ht (width b) (width r) (width_positive S b hb)
    (width_positive S r hr) hbr hn
  have hln : 0≤l.count := by rw [hl.2.2.2]; exact Int.natCast_nonneg _
  have hrn : 0≤r.count := by rw [hr.2.2.2]; exact Int.natCast_nonneg _
  have hc : b.count.toNat=l.count.toNat+r.count.toNat := by omega
  have hp : 0<b.count.toNat := by omega
  have hh := mass_children b.count.toNat r.count.toNat l.count.toNat
    (rank t ht (width b)) (rank t ht (width r)) (rank t ht (width l))
    hp (by omega) hrr hlr
  simpa only [massPotential,List.map_cons,List.sum_cons,massWeight,Nat.add_assoc] using
    Nat.add_lt_add_right hh ((bs.map (massWeight t ht)).sum)

/-- Construction for Mass Step Good in the fuel model. -/
def MassStepGood (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ) : Prop :=
  ∀ b,GoodBox S b → ∃ l r,advance chain f b=some (l,r) ∧
    GoodBox S l ∧ GoodBox S r ∧
    width l≤(3/4 : ℝ)*width b ∧ width r≤(3/4 : ℝ)*width b ∧
    b.count=l.count+r.count

/-- The finite construction in `Fuel` satisfies `core_mass_terminates` under the displayed hypotheses. -/
theorem core_mass_terminates (S : Finset ℝ) (chain : List (List ℤ)) (f : List ℤ)
    (target : ℚ) (gap t : ℝ) (ht : 0<t) (htg : t≤gap/2) (htt : t≤(target : ℝ))
    (hsep : ∀ x∈S,∀ y∈S,x≠y → gap≤|x-y|) (hstep : MassStepGood S chain f)
    (fuel : ℕ) (bs : List Box) (done : List (ℚ×ℚ))
    (hgood : ∀ b∈bs,GoodBox S b) (hfuel : massPotential t ht bs≤fuel) :
    ∃ result,core chain f target fuel bs done=some result := by
  induction fuel generalizing bs done with
  | zero =>
    cases bs with
    | nil => exact ⟨done,rfl⟩
    | cons b bs =>
      have hh := mass_pop t ht b bs
      omega
  | succ fuel ih =>
    cases bs with
    | nil => exact ⟨done,rfl⟩
    | cons b bs =>
      have hb := hgood b (by simp)
      have hbs : ∀ c∈bs,GoodBox S c := fun c hc => hgood c (by simp only [List.mem_cons]; exact Or.inr hc)
      have hpop : massPotential t ht bs≤fuel := by have hh := mass_pop t ht b bs; omega
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
          obtain ⟨l,r,had,hl,hr,hwl,hwr,hcounts⟩ := hstep b hb
          have hnew : massPotential t ht (r::l::bs)≤fuel := by
            have hh := mass_split S t ht b l r hb hl hr hwl hwr hrank hz hcounts bs
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


/-- The finite construction in `Fuel` satisfies `original_mass_step` under the displayed hypotheses. -/
theorem original_mass_step (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (hd : 0<(poly a).natDegree) (f : List ℤ) (tail : List (List ℤ))
    (hsource : sourceChain a=some (f::tail)) (hfn : integerPolyQ f≠0)
    (hroots : ∀ x : ℝ,x∈inputRoots a ↔ value f x=0) : MassStepGood (inputRoots a) (f::tail) f := by
  intro b hb
  obtain ⟨c,hc,had,hl,hr,hnl,hnr,hcount,hwl,hwr⟩ :=
    advance_success a hcan ha hd f tail hsource hfn hroots b hb
  refine ⟨(split (f::tail) b c).1,(split (f::tail) b c).2,had,hl,hr,?_,?_,hcount⟩
  · dsimp only [width]
    have hh : (((split (f::tail) b c).1.right-(split (f::tail) b c).1.left : ℚ) : ℝ)≤3*((b.right-b.left : ℚ) : ℝ)/4 := by exact_mod_cast hwl
    linarith
  · dsimp only [width]
    have hh : (((split (f::tail) b c).2.right-(split (f::tail) b c).2.left : ℚ) : ℝ)≤3*((b.right-b.left : ℚ) : ℝ)/4 := by exact_mod_cast hwr
    linarith


end ActualSturmMassPotential


namespace ActualSturmNumericalRank
open Polynomial ActualSturmMassPotential ActualSturmQueuePotential ActualSturmQueueRank
open ActualSturmQueueSplit ActualSturmQueueReady ActualSturmCauchyBound ActualSturmCauchyInput
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive
open ActualProjectionSquarefreeHeight ActualProjectionSeparationBudget
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The finite construction in `Fuel` satisfies `rank_numeric` under the displayed hypotheses. -/
theorem rank_numeric (t w : ℝ) (ht : 0<t) (hw : 0<w) (B K : ℕ)
    (hwidth : w≤(2 : ℝ)^B) (htarget : 1/(2 : ℝ)^K≤t) :
    rank t ht w≤4*(B+K) := by
  have hfour : (3/4 : ℝ)^4≤1/2 := by norm_num
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(3/4)^4) hfour (B+K)
  rw [← pow_mul] at hp
  have hsmall : w*(3/4 : ℝ)^(4*(B+K))≤t := by
    calc
      _ ≤ (2 : ℝ)^B*(1/2 : ℝ)^(B+K) :=
        mul_le_mul hwidth hp (by positivity) (by positivity)
      _ = 1/(2 : ℝ)^K := by
        rw [one_div_pow,pow_add]
        field_simp
      _ ≤ t := htarget
  unfold rank
  rw [dite_eq_left hw]
  exact Nat.find_min' _ hsmall

/-- The finite construction in `Fuel` satisfies `max_upper` under the displayed hypotheses. -/
theorem max_upper (xs : List ℚ) (seed upper : ℚ)
    (hs : seed≤upper) (hx : ∀x∈xs,x≤upper) : xs.foldl max seed≤upper := by
  induction xs generalizing seed with
  | nil => exact hs
  | cons x xs ih =>
    exact ih (max seed x) (max_le hs (hx x (by simp))) (fun y hy => hx y (by simp only [List.mem_cons]; exact Or.inr hy))

/-- The finite construction in `Fuel` satisfies `sourceCeil_le_integer` under the displayed hypotheses. -/
theorem sourceCeil_le_integer (q : ℚ) (C : ℤ) (hq : q≤(C : ℚ)) : sourceCeil q≤C := by
  have hdQ : (0 : ℚ)<q.den := by exact_mod_cast q.den_pos
  have hdZ : (0 : ℤ)<q.den := by exact_mod_cast q.den_pos
  have hnumQ : (q.num : ℚ)≤(C : ℚ)*q.den := by
    apply (div_le_iff₀ hdQ).mp
    simpa only [Rat.num_div_den] using hq
  have hnum : q.num≤C*(q.den : ℤ) := by exact_mod_cast hnumQ
  unfold sourceCeil
  apply (Int.ediv_le_iff_le_mul hdZ).mpr
  omega

/-- The estimate `list_bound_upper` retains the actual parameter, input-error and normalization budgets. -/
theorem list_bound_upper (f : List ℤ) (H : ℕ)
    (htop : f.getD (f.length-1) 0≠0)
    (hcoeff : ∀k,‖(rootIntegerListPolynomial f).coeff k‖≤(2 : ℝ)^H) :
    (listBound f : ℝ)≤(2 : ℝ)^H+2 := by
  have hd : (1 : ℚ)≤((f.getD (f.length-1) 0).natAbs : ℚ) := by
    exact_mod_cast (Int.natAbs_pos.mpr htop)
  have hcoefQ : ∀k,((f.getD k 0).natAbs : ℚ)≤(2 : ℚ)^H := by
    intro k
    have hh := hcoeff k
    rw [rootIntegerListPolynomial_coeff,Complex.norm_intCast] at hh
    have hR : ((f.getD k 0).natAbs : ℝ)≤(2 : ℝ)^H := by
      simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using hh
    exact_mod_cast hR
  have hratio : listRatio f≤(2 : ℚ)^H := by
    apply max_upper _ _ _ (by positivity)
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    have hz' : z∈f := List.mem_of_mem_dropLast hz
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hz'
    have hzi : f.getD i 0=z := by simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he]
    have hzQ : (z.natAbs : ℚ)≤(2 : ℚ)^H := by rw [← hzi]; exact hcoefQ i
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
      (hzQ.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (show (0 : ℚ)≤2^H by positivity)))
  have hc := sourceCeil_le_integer (listRatio f) (2^H) (by exact_mod_cast hratio)
  have hZ : listBound f≤(2 : ℤ)^H+2 := by unfold listBound; omega
  exact_mod_cast hZ

end ActualSturmNumericalRank


namespace ActualSturmNumericalFuel
open Polynomial ActualSturmNumericalRank ActualSturmMassPotential
open ActualSturmQueueSplit ActualSturmQueueReady ActualSturmQueueRun ActualSturmQueuePotential
open ActualSturmQueueRank ActualSturmSourceCount ActualSturmChain ActualSturmInitialization
open ActualSturmArrayTools ActualSturmCauchyInput ActualSturmIntervalStart
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive ActualYunPrimitiveContent
open ActualProjectionRealSeparation ActualProjectionSquarefreeHeight ActualProjectionSeparationBudget
open ActualRootProjectionCap ActualSturmComputedIsolation ActualSturmFuelSearch
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for width Bits in the fuel model. -/
def widthBits (a : List ℤ) : ℕ := squarefreeHeight (degree a) (height a)+3
/-- Construction for depth Budget in the fuel model. -/
def depthBudget (a : List ℤ) (bits : ℕ) : ℕ :=
  4*(widthBits a+max bits (separationExponent a+1))
/-- Construction for fuel Budget in the fuel model. -/
def fuelBudget (a : List ℤ) (bits : ℕ) : ℕ := 2*degree a*depthBudget a bits+1

/-- The finite construction in `Fuel` satisfies `original_intervals_numerical` under the displayed hypotheses. -/
theorem original_intervals_numerical (a : List ℤ) (hcan : Canonical (lift a))
    (hn : poly (lift a)≠0) (hd : 0<(poly (lift a)).natDegree) (bits : ℕ) :
    ∃ result,intervals (lift a) bits (fuelBudget a bits)=some result := by
  have ha : integerPoly a≠0 := by
    intro hz
    apply hn
    rw [lift_poly]
    change (integerPoly a).map (Int.castRingHom ℚ)=0
    rw [hz,Polynomial.map_zero]
  have hqdeg : (poly (lift a)).natDegree=(integerPoly a).natDegree := by
    rw [lift_poly]
    exact Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective _
  obtain ⟨f,g,hinit,hfc,hgc,hsep,hfd,hfdle,hgn,hcop,s,hs,hg⟩ :=
    initialization_success (lift a) hcan hn hd
  have hfn := hsep.ne_zero
  have hfl := canonical_length (lift f) hfc ((canonical_nonzero _ hfc).mpr (by rw [lift_poly]; exact hfn))
  have hgl := canonical_length (lift g) hgc ((canonical_nonzero _ hgc).mpr (by rw [lift_poly]; exact hgn))
  rw [lift_poly] at hfl hgl
  simp only [lift,List.length_map] at hfl hgl
  have hgdegree : (integerPolyQ g).natDegree=(integerPolyQ f).derivative.natDegree := by
    rw [hg,Polynomial.natDegree_C_mul hs.ne']
  have hlen : g.length<f.length := by
    have hh := Polynomial.natDegree_derivative_lt (ne_of_gt hfd)
    omega
  obtain ⟨xs,hrun,hchain⟩ := ActualSturmChain.run_success g.length f g hfc hgc hfn hgn hcop hlen (le_refl _)
  have hsource : sourceChain (lift a)=some (f::g::xs) := by
    simpa only [sourceChain,hinit] using hrun
  obtain ⟨f',g',xs',hsource',hprepare,hchain',hbox,hroots⟩ := prepare_success (lift a) hcan hn hd
  have he : f'::g'::xs'=f::g::xs := Option.some.inj (hsource'.symm.trans hsource)
  simp only [List.cons.injEq] at he
  obtain ⟨hf,hgfirst,hxtail⟩ := he
  subst f'
  subst g'
  subst xs'
  obtain ⟨ff,gg,hinit',_,_,_,_,_,hcoeff,_⟩ :=
    initialized_bounds a hcan ha (by rw [← hqdeg]; exact hd)
  have heinit : [ff,gg]=[f,g] := Option.some.inj (hinit'.symm.trans hinit)
  simp only [List.cons.injEq] at heinit
  obtain ⟨hff,hgg,_⟩ := heinit
  subst ff
  subst gg
  have htop := canonical_top f hfc hfn
  let b := initialBox (f::g::xs) f
  let gap : ℝ := 1/(2 : ℝ)^separationExponent a
  let t : ℝ := min (sourceWidth bits : ℝ) (gap/2)
  have hgap : 0<gap := by dsimp only [gap]; positivity
  have htarg : (0 : ℝ)<(sourceWidth bits : ℝ) := by exact_mod_cast sourceWidth_positive bits
  have ht : 0<t := lt_min htarg (by positivity)
  have hseparated : ∀x∈inputRoots (lift a),∀y∈inputRoots (lift a),x≠y → gap≤|x-y| := by
    intro x hx y hy hxy
    exact lifted_real_separated a hcan hn hd x y
      ((member_zero_iff a hn x).mp hx) ((member_zero_iff a hn y).mp hy) hxy
  have hwidth : width b≤(2 : ℝ)^widthBits a := by
    have hb := list_bound_upper f (squarefreeHeight (degree a) (height a)) htop hcoeff
    have hp : (1 : ℝ)≤2^squarefreeHeight (degree a) (height a) := one_le_pow₀ (by norm_num)
    dsimp only [width,b,initialBox,widthBits]
    push_cast
    rw [pow_add]
    norm_num
    nlinarith
  let K := max bits (separationExponent a+1)
  have hKtarget : 1/(2 : ℝ)^K≤(sourceWidth bits : ℝ) := by
    have hp : (2 : ℝ)^bits≤2^K := pow_le_pow_right₀ (by norm_num) (Nat.le_max_left _ _)
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<2^bits) hp
    simpa only [sourceWidth,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hKgap : 1/(2 : ℝ)^K≤gap/2 := by
    have hp : (2 : ℝ)^(separationExponent a+1)≤2^K := pow_le_pow_right₀ (by norm_num) (Nat.le_max_right _ _)
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<2^(separationExponent a+1)) hp
    simpa only [gap,pow_succ,div_div] using hh
  have hrank : rank t ht (width b)≤depthBudget a bits :=
    rank_numeric t (width b) ht (width_positive _ b hbox) (widthBits a) K hwidth (le_min hKtarget hKgap)
  have hcard : (inputRoots (lift a)).card≤degree a := by
    have hc := (Multiset.toFinset_card_le (((poly (lift a)).map (Rat.castHom ℝ)).roots)).trans
      (Polynomial.card_roots_map_le_natDegree (poly (lift a)))
    have hl := canonical_length (lift a) hcan ((canonical_nonzero _ hcan).mpr hn)
    rw [hqdeg] at hl
    simp only [lift,List.length_map] at hl
    change (inputRoots (lift a)).card≤_ at hc
    rw [hqdeg] at hc
    dsimp only [ActualRootProjectionCap.degree]
    omega
  have hmass : b.count.toNat≤degree a := by
    have hh : (rootsIn (inputRoots (lift a)) b.left b.right).card≤(inputRoots (lift a)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [hbox.2.2.2]
    simpa only [Int.toNat_natCast] using hh.trans hcard
  have hfuel : massPotential t ht [b]≤fuelBudget a bits := by
    simp only [massPotential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,massWeight,fuelBudget]
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmass) hrank) 1
  have hstep := original_mass_step (lift a) hcan hn hd f (g::xs) hsource hfn hroots
  obtain ⟨result,hresult⟩ := core_mass_terminates (inputRoots (lift a)) (f::g::xs) f
    (sourceWidth bits) gap t ht (min_le_right _ _) (min_le_left _ _) hseparated hstep
    (fuelBudget a bits) [b] [] (by intro c hc; simp only [List.mem_singleton] at hc; subst c; exact hbox) hfuel
  have hrunResult : ActualSturmQueueRun.run (lift a) (sourceWidth bits) (fuelBudget a bits)=some result := by
    simpa only [ActualSturmQueueRun.run,hprepare] using hresult
  exact ⟨ActualSturmIntervalSort.sort result,by simp only [intervals,hrunResult,Option.map_some]⟩

/-- The finite construction in `Fuel` satisfies `original_search_numerical` under the displayed hypotheses. -/
theorem original_search_numerical (a : List ℤ) (hcan : Canonical (lift a))
    (hn : poly (lift a)≠0) (hd : 0<(poly (lift a)).natDegree) (bits : ℕ) :
    ActualFiniteFuelSearch.fuel (intervals (lift a) bits) (exists_success (lift a) hcan hn hd bits)
      ≤fuelBudget a bits ∧
    intervals (lift a) bits (fuelBudget a bits)=some (searched (lift a) hcan hn hd bits) := by
  obtain ⟨result,hr⟩ := original_intervals_numerical a hcan hn hd bits
  have hf := Nat.find_min' (exists_success (lift a) hcan hn hd bits)
    (show (intervals (lift a) bits (fuelBudget a bits)).isSome=true by simp only [hr,Option.isSome_some])
  have hs := ActualFiniteFuelSearch.trial_value (intervals (lift a) bits) (exists_success (lift a) hcan hn hd bits)
  have he := intervals_unique (lift a) bits (fuelBudget a bits) _ result
    (searched (lift a) hcan hn hd bits) hr hs
  exact ⟨hf,by simpa only [he] using hr⟩

/-- The finite construction in `Fuel` satisfies `fuelBudget_formula` under the displayed hypotheses. -/
theorem fuelBudget_formula (a : List ℤ) (bits : ℕ) :
    fuelBudget a bits=8*degree a*(squarefreeHeight (degree a) (height a)+3+
      max bits (separationExponent a+1))+1 := by
  unfold fuelBudget depthBudget widthBits
  ring

end ActualSturmNumericalFuel


end RootYunInternal
end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

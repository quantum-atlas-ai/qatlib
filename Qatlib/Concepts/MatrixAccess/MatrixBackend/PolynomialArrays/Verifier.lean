/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public

set_option backward.isDefEq.respectTransparency false

/-! Raw record count checks precede finite packing; accepted values retain the complete ordered root pairing.
The exact array checker is separate from original-input cap generation and from JSON parsing. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
namespace RootYunInternal
namespace ActualProjectionCapRound
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
/-- Abbreviation for Disk in the verifier model. -/
abbrev Disk := (ℚ×ℚ)×ℚ

/-- Data and invariants for Record in the verifier model. -/
structure Record where
  factor : List ℤ
  exponent : ℕ
  disks : List Disk

end ActualProjectionCapRound

namespace ActualProjectionTypedRecord
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open ActualProjectionCapRound
/-- Construction for pack in the verifier model. -/
def pack (n : ℕ) (a : Fin (n+2) → ℤ) (record : Record) : RootIntegerFactorData where
  n := n
  coefficients := a
  exponent := record.exponent
  centers := fun i => (record.disks.getD i.val ((0,0),0)).1
  radii := fun i => (record.disks.getD i.val ((0,0),0)).2

/-- The finite construction in `raw polynomial certificate checker` satisfies `pack_disks` under the displayed hypotheses. -/
theorem pack_disks (n : ℕ) (a : Fin (n+2) → ℤ) (record : Record) (hlen : record.disks.length=n+1) :
    List.ofFn (fun i => ((pack n a record).centers i,(pack n a record).radii i))=record.disks := by
  apply List.ext_getElem (by simp only [List.length_ofFn]; exact hlen.symm)
  intro i _ hi
  simp only [List.getElem_ofFn,pack,Prod.eta,List.getD_eq_getElem _ _ hi]

/-- Construction for pack Record in the verifier model. -/
def packRecord (record : Record) : RootIntegerFactorData :=
  pack (record.factor.length-2) (fun i => record.factor.getD i.val 0) record

end ActualProjectionTypedRecord

namespace ActualProjectionVerifierDiskChecks
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- Typeclass instance for coordinate Decidable in the verifier model. -/
private instance coordinateDecidable (n : ℕ) (v w : GaussianIntegerFraction) (r : ℚ) :
    Decidable (rootIntegerCoordinateBound n v w r) := by
  unfold rootIntegerCoordinateBound
  infer_instance

/-- Construction for disk Value in the verifier model. -/
def diskValue (f : RootIntegerFactorData) (i : Fin (f.n+1)) : GaussianIntegerFraction :=
  rootCompactHorner (rootSharedNumerator (f.centers i)) (rootSharedDenominator (f.centers i)) (List.ofFn f.coefficients)

/-- Construction for disk Prime in the verifier model. -/
def diskPrime (f : RootIntegerFactorData) (i : Fin (f.n+1)) : GaussianIntegerFraction :=
  rootCompactHorner (rootSharedNumerator (f.centers i)) (rootSharedDenominator (f.centers i))
    (List.ofFn (rootIntegerDerivative f.n f.coefficients))

/-- Construction for inclusion Check in the verifier model. -/
def inclusionCheck (f : RootIntegerFactorData) (i : Fin (f.n+1)) : Bool :=
  let v := diskValue f i
  if v.numerator=(0,0) then true else
  let w := diskPrime f i
  decide (v.denominator=w.denominator*rootSharedDenominator (f.centers i)) &&
    decide (0 < max |w.numerator.1| |w.numerator.2|) &&
    decide (rootIntegerCoordinateBound (f.n+1) v w (f.radii i))

/-- Construction for previous Check in the verifier model. -/
def previousCheck (f : RootIntegerFactorData) (i : Fin (f.n+1)) : Bool :=
  ((List.finRange (f.n+1)).take i.val).all (fun j =>
    decide ((f.radii i+f.radii j)^2 <
      ((f.centers i).1-(f.centers j).1)^2+((f.centers i).2-(f.centers j).2)^2))

/-- Construction for disk Check in the verifier model. -/
def diskCheck (f : RootIntegerFactorData) (eta : ℚ) (i : Fin (f.n+1)) : Bool :=
  previousCheck f i && inclusionCheck f i &&
    match rootRationalDiskClassify (f.centers i) (f.radii i) with
    | none => false
    | some false => true
    | some true => decide (0 < eta) && decide (f.radii i+
        |(rootGridPoint (f.centers i) (eta/16)).1-(f.centers i).1|+
        |(rootGridPoint (f.centers i) (eta/16)).2-(f.centers i).2| ≤ eta)

/-- Construction for header Check in the verifier model. -/
def headerCheck (f : RootIntegerFactorData) : Bool :=
  decide (f.coefficients (Fin.last (f.n+1)) ≠ 0 ∧ 0 < f.exponent)

/-- Construction for radius Check in the verifier model. -/
def radiusCheck (f : RootIntegerFactorData) : Bool :=
  (List.finRange (f.n+1)).all (fun i => decide (0 < f.radii i))

/-- Construction for group Check in the verifier model. -/
def groupCheck (f : RootIntegerFactorData) (eta : ℚ) : Bool :=
  (List.finRange (f.n+1)).all (diskCheck f eta)

/-- The finite construction in `raw polynomial certificate checker` satisfies `denominator_assert` under the displayed hypotheses. -/
theorem denominator_assert (f : RootIntegerFactorData) (i : Fin (f.n+1)) :
    (diskValue f i).denominator=(diskPrime f i).denominator*rootSharedDenominator (f.centers i) := by
  simp only [diskValue,diskPrime,rootCompactHorner_denominator,List.length_ofFn,
    show f.n+2-1=f.n+1 by omega,Nat.add_sub_cancel,pow_succ]

/-- The finite construction in `raw polynomial certificate checker` satisfies `inclusion_check_of_guards` under the displayed hypotheses. -/
theorem inclusion_check_of_guards (f : RootIntegerFactorData) (eta : ℚ)
    (h : RootIntegerFactorGuards f eta) (i : Fin (f.n+1)) : inclusionCheck f i=true := by
  let v := diskValue f i
  let w := diskPrime f i
  by_cases hz : v.numerator=(0,0)
  · change (if v.numerator=(0,0) then true else _)=true
    rw [ite_eq_left hz]
  · have hb : rootIntegerCoordinateBound (f.n+1) v w (f.radii i) := (h.inclusion i).resolve_left hz
    have hu : 0 < |v.numerator.1|+|v.numerator.2| := by
      have hx := abs_nonneg v.numerator.1
      have hy := abs_nonneg v.numerator.2
      by_contra he
      have hx0 : |v.numerator.1|=0 := by omega
      have hy0 : |v.numerator.2|=0 := by omega
      exact hz (Prod.ext (abs_eq_zero.mp hx0) (abs_eq_zero.mp hy0))
    have hw : (0 : ℤ) < w.denominator := by
      exact_mod_cast rootCompactHorner_denominator_pos (rootSharedNumerator (f.centers i))
        (rootSharedDenominator (f.centers i)) (List.ofFn (rootIntegerDerivative f.n f.coefficients))
        (rootSharedDenominator_pos (f.centers i))
    have hr : (0 : ℤ) < (f.radii i).den := by exact_mod_cast (f.radii i).den_pos
    have hn : (0 : ℤ) < (f.n+1 : ℕ) := by exact_mod_cast Nat.succ_pos f.n
    have hl : 0 < max |w.numerator.1| |w.numerator.2| := by
      have hn0 : 0 ≤ max |w.numerator.1| |w.numerator.2| :=
        (abs_nonneg w.numerator.1).trans (le_max_left _ _)
      by_contra he
      have hzero : max |w.numerator.1| |w.numerator.2|=0 := le_antisymm (le_of_not_gt he) hn0
      have hc := hb
      unfold rootIntegerCoordinateBound at hc
      simp only [hzero,mul_zero,zero_mul] at hc
      exact (not_le_of_gt (mul_pos (mul_pos (mul_pos hn hu) hw) hr)) hc
    change (if v.numerator=(0,0) then true else _)=true
    rw [ite_eq_right hz]
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨denominator_assert f i,hl⟩,hb⟩

/-- The finite construction in `raw polynomial certificate checker` satisfies `previous_check_of_guards` under the displayed hypotheses. -/
theorem previous_check_of_guards (f : RootIntegerFactorData) (eta : ℚ)
    (h : RootIntegerFactorGuards f eta) (i : Fin (f.n+1)) : previousCheck f i=true := by
  apply List.all_eq_true.mpr
  intro j hj
  obtain ⟨k,hk,he⟩ := List.getElem_of_mem hj
  have hki : k < i.val := by rw [List.length_take] at hk; omega
  have hjk : j.val=k := by
    have hh := congrArg Fin.val he
    simpa only [List.getElem_take,List.getElem_finRange, Fin.coe_cast] using hh.symm
  apply decide_eq_true
  exact h.separation i j (fun h => by have hv := congrArg Fin.val h; omega)

/-- The finite construction in `raw polynomial certificate checker` satisfies `disk_check_of_guards` under the displayed hypotheses. -/
theorem disk_check_of_guards (f : RootIntegerFactorData) (eta : ℚ)
    (h : RootIntegerFactorGuards f eta) (i : Fin (f.n+1)) : diskCheck f eta i=true := by
  unfold diskCheck
  rw [previous_check_of_guards f eta h i,inclusion_check_of_guards f eta h i]
  simp only [Bool.true_and]
  rw [rootRationalDiskClassify_computed_tag _ _ (h.classified i)]
  cases ht : rootRationalDiskComputedTag (f.centers i) (f.radii i) with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨h.eta_pos i ht,h.budget i ht⟩

/-- The finite construction in `raw polynomial certificate checker` satisfies `all_checks_of_guards` under the displayed hypotheses. -/
theorem all_checks_of_guards (f : RootIntegerFactorData) (eta : ℚ)
    (h : RootIntegerFactorGuards f eta) :
    headerCheck f=true ∧ radiusCheck f=true ∧ groupCheck f eta=true := by
  refine ⟨?_,?_,?_⟩
  · exact decide_eq_true ⟨h.leading,h.exponent_pos⟩
  · exact List.all_eq_true.mpr (fun i _ => decide_eq_true (h.radius_pos i))
  · exact List.all_eq_true.mpr (fun i _ => disk_check_of_guards f eta h i)


end ActualProjectionVerifierDiskChecks

namespace ActualProjectionVerifierPrimitives
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for factor List in the verifier model. -/
def factorList (fs : List RootIntegerFactorData) : List (List ℤ×ℕ) :=
  fs.map (fun f => (List.ofFn f.coefficients,f.exponent))

/-- Construction for family in the verifier model. -/
def family (fs : List RootIntegerFactorData) : Fin fs.length → RootIntegerFactorData := fs.get

/-- The finite construction in `raw polynomial certificate checker` satisfies `family_factor_list` under the displayed hypotheses. -/
theorem family_factor_list (fs : List RootIntegerFactorData) :
    List.ofFn (fun j => (List.ofFn (family fs j).coefficients,(family fs j).exponent))=factorList fs := by
  have he := congrArg (List.map (fun f : RootIntegerFactorData => (List.ofFn f.coefficients,f.exponent))) (List.ofFn_get fs)
  simpa only [List.map_ofFn,Function.comp_def,factorList,family] using he

/-- The actual finite word or frame satisfies `radius_encoding_precision` with all displayed legality, input and workspace hypotheses. -/
theorem radius_encoding_precision (bits : ℕ) (r : ℚ) (hr : 0 < r) (hb : r ≤ 1/(2 : ℚ)^bits) :
    bits < r.den.size := by
  have hn : (1 : ℚ) ≤ (r.num : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ r.num from Rat.num_pos.mpr hr)
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hsmall : 1/(r.den : ℚ) ≤ r := by
    calc
      _ ≤ (r.num : ℚ)/r.den := div_le_div_of_nonneg_right hn hden.le
      _ = r := Rat.num_div_den r
  have hp := (div_le_div_iff₀ hden (by positivity : (0 : ℚ) < 2^bits)).mp (hsmall.trans hb)
  have hpN : 2^bits ≤ r.den := by exact_mod_cast (by simpa only [one_mul] using hp : (2 : ℚ)^bits ≤ r.den)
  exact Nat.lt_size.mpr hpN


end ActualProjectionVerifierPrimitives

namespace ActualProjectionVerifierInputChecks
open ActualProjectionVerifierPrimitives ActualProjectionVerifierDiskChecks
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for radius Bit Values in the verifier model. -/
def radiusBitValues (fs : List RootIntegerFactorData) : List ℕ :=
  fs.flatMap (fun f => (List.finRange (f.n+1)).map (fun i => (f.radii i).den.size))

/-- Construction for maximum Radius Bits in the verifier model. -/
def maximumRadiusBits (fs : List RootIntegerFactorData) : ℕ := (radiusBitValues fs).foldl max 0

/-- The finite construction in `raw polynomial certificate checker` satisfies `fold_max_initial` under the displayed hypotheses. -/
theorem fold_max_initial (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

/-- The finite construction in `raw polynomial certificate checker` satisfies `fold_max_member` under the displayed hypotheses. -/
theorem fold_max_member (xs : List ℕ) (a k : ℕ) (hk : k∈xs) : k ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hk
  | cons x xs ih =>
    rcases List.mem_cons.mp hk with he|he
    · subst x
      exact (le_max_right a k).trans (fold_max_initial xs (max a k))
    · exact ih (max a x) he

/-- The finite construction in `raw polynomial certificate checker` satisfies `radius_bits_member` under the displayed hypotheses. -/
theorem radius_bits_member (fs : List RootIntegerFactorData) (f : RootIntegerFactorData)
    (hf : f∈fs) (i : Fin (f.n+1)) : (f.radii i).den.size ≤ maximumRadiusBits fs := by
  apply fold_max_member
  apply List.mem_flatMap.mpr
  exact ⟨f,hf,List.mem_map.mpr ⟨i,by simp,rfl⟩⟩

/-- The finite construction in `raw polynomial certificate checker` satisfies `guard_member` under the displayed hypotheses. -/
theorem guard_member (fs : List RootIntegerFactorData) (eta : ℚ)
    (h : ∀ j,RootIntegerFactorGuards (family fs j) eta) (f : RootIntegerFactorData) (hf : f∈fs) :
    RootIntegerFactorGuards f eta := by
  obtain ⟨j,he⟩ := List.mem_iff_get.mp hf
  have hj := h j
  change RootIntegerFactorGuards (fs.get j) eta at hj
  rw [he] at hj
  exact hj

/-- The finite construction in `raw polynomial certificate checker` satisfies `all_header_checks` under the displayed hypotheses. -/
theorem all_header_checks (fs : List RootIntegerFactorData) (eta : ℚ)
    (h : ∀ j,RootIntegerFactorGuards (family fs j) eta) :
    fs.all headerCheck=true ∧ fs.all radiusCheck=true ∧ fs.all (fun f => groupCheck f eta)=true := by
  refine ⟨List.all_eq_true.mpr ?_,List.all_eq_true.mpr ?_,List.all_eq_true.mpr ?_⟩
  · intro f hf
    exact (all_checks_of_guards f eta (guard_member fs eta h f hf)).1
  · intro f hf
    exact (all_checks_of_guards f eta (guard_member fs eta h f hf)).2.1
  · intro f hf
    exact (all_checks_of_guards f eta (guard_member fs eta h f hf)).2.2

/-- The finite construction in `raw polynomial certificate checker` satisfies `radius_precheck` under the displayed hypotheses. -/
theorem radius_precheck (fs : List RootIntegerFactorData) (bits : ℕ) (eta : ℚ)
    (heta : eta=1/(2 : ℚ)^bits) (h : ∀ j,RootIntegerFactorGuards (family fs j) eta)
    (hpos : 0 < (rootDecodedReturnList (family fs) eta).length) : bits < maximumRadiusBits fs := by
  cases he : rootDecodedReturnIndices (family fs) with
  | nil =>
    simp only [rootDecodedReturnList,he,List.map_nil,List.length_nil] at hpos
    omega
  | cons s ss =>
    have hs : s∈rootDecodedReturnIndices (family fs) := by rw [he]; exact List.mem_cons_self
    have ht := rootDecodedReturnIndices_inside (family fs) s hs
    have hb := (h s.1).budget s.2 ht
    have hr : (family fs s.1).radii s.2 ≤ eta := by
      have hx := abs_nonneg ((rootGridPoint ((family fs s.1).centers s.2) (eta/16)).1-
        ((family fs s.1).centers s.2).1)
      have hy := abs_nonneg ((rootGridPoint ((family fs s.1).centers s.2) (eta/16)).2-
        ((family fs s.1).centers s.2).2)
      linarith
    rw [heta] at hr
    exact (radius_encoding_precision bits _ ((h s.1).radius_pos s.2) hr).trans_le
      (radius_bits_member fs (family fs s.1) (List.get_mem fs s.1) s.2)


end ActualProjectionVerifierInputChecks

namespace ActualProjectionVerifierDiskSound
open ActualProjectionVerifierDiskChecks
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The finite construction in `raw polynomial certificate checker` satisfies `inclusion_of_check` under the displayed hypotheses. -/
theorem inclusion_of_check (f : RootIntegerFactorData) (i : Fin (f.n+1))
    (h : inclusionCheck f i=true) :
    (diskValue f i).numerator=(0,0) ∨
      rootIntegerCoordinateBound (f.n+1) (diskValue f i) (diskPrime f i) (f.radii i) := by
  by_cases hz : (diskValue f i).numerator=(0,0)
  · exact Or.inl hz
  · simp only [inclusionCheck,hz,ite_false,Bool.and_eq_true,decide_eq_true_eq] at h
    exact Or.inr h.2

/-- The finite construction in `raw polynomial certificate checker` satisfies `prior_member` under the displayed hypotheses. -/
theorem prior_member (n : ℕ) (i j : Fin n) (hji : j.val < i.val) :
    j∈(List.finRange n).take i.val := by
  apply List.mem_iff_getElem.mpr
  refine ⟨j.val,?_,?_⟩
  · rw [List.length_take,List.length_finRange]
    omega
  · apply Fin.ext
    simp only [List.getElem_take,List.getElem_finRange, Fin.coe_cast]

/-- The finite construction in `raw polynomial certificate checker` satisfies `separation_of_checks` under the displayed hypotheses. -/
theorem separation_of_checks (f : RootIntegerFactorData)
    (h : ∀ i,previousCheck f i=true) (i j : Fin (f.n+1)) (hne : i≠j) :
    (f.radii i+f.radii j)^2<
      ((f.centers i).1-(f.centers j).1)^2+((f.centers i).2-(f.centers j).2)^2 := by
  have hv : i.val≠j.val := fun he => hne (Fin.ext he)
  rcases lt_or_gt_of_ne hv with hij|hji
  · have hs := List.all_eq_true.mp (h j) i (prior_member _ j i hij)
    simp only [decide_eq_true_eq] at hs
    nlinarith
  · have hs := List.all_eq_true.mp (h i) j (prior_member _ i j hji)
    exact of_decide_eq_true hs

/-- The finite construction in `raw polynomial certificate checker` satisfies `side_of_check` under the displayed hypotheses. -/
theorem side_of_check (f : RootIntegerFactorData) (eta : ℚ) (i : Fin (f.n+1))
    (h : diskCheck f eta i=true) :
    rootRationalDiskClassify (f.centers i) (f.radii i)≠none ∧
      (rootRationalDiskComputedTag (f.centers i) (f.radii i)=true → 0 < eta) ∧
      (rootRationalDiskComputedTag (f.centers i) (f.radii i)=true → f.radii i+
        |(rootGridPoint (f.centers i) (eta/16)).1-(f.centers i).1|+
        |(rootGridPoint (f.centers i) (eta/16)).2-(f.centers i).2| ≤ eta) := by
  unfold diskCheck at h
  have hb := (Bool.and_eq_true_iff.mp h).2
  cases he : rootRationalDiskClassify (f.centers i) (f.radii i) with
  | none => rw [he] at hb; cases hb
  | some b =>
    cases b with
    | false =>
      have ht : rootRationalDiskComputedTag (f.centers i) (f.radii i)=false := by
        simp only [rootRationalDiskComputedTag,he,Option.getD_some]
      refine ⟨by simp,?_,?_⟩
      · intro hf
        rw [ht] at hf
        cases hf
      · intro hf
        rw [ht] at hf
        cases hf
    | true =>
      rw [he] at hb
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hb
      exact ⟨by simp,fun _ => hb.1,fun _ => hb.2⟩

/-- The finite construction in `raw polynomial certificate checker` satisfies `guards_of_all_checks` under the displayed hypotheses. -/
theorem guards_of_all_checks (f : RootIntegerFactorData) (eta : ℚ)
    (hh : headerCheck f=true) (hr : radiusCheck f=true) (hg : groupCheck f eta=true) :
    RootIntegerFactorGuards f eta := by
  have hhead : f.coefficients (Fin.last (f.n+1))≠0 ∧ 0 < f.exponent := of_decide_eq_true hh
  have hd : ∀ i,diskCheck f eta i=true := fun i => List.all_eq_true.mp hg i (by simp)
  have hp : ∀ i,previousCheck f i=true := by
    intro i
    have hc := hd i
    unfold diskCheck at hc
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  refine ⟨hhead.1,hhead.2,?_,?_,separation_of_checks f hp,?_,?_,?_⟩
  · intro i
    exact of_decide_eq_true (List.all_eq_true.mp hr i (by simp))
  · intro i
    exact inclusion_of_check f i (by
      have hc := hd i
      unfold diskCheck at hc
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2)
  · intro i
    exact (side_of_check f eta i (hd i)).1
  · intro i
    exact (side_of_check f eta i (hd i)).2.1
  · intro i
    exact (side_of_check f eta i (hd i)).2.2


end ActualProjectionVerifierDiskSound

namespace ActualProjectionDecodedVerifier
open ActualProjectionVerifierPrimitives ActualProjectionVerifierDiskChecks ActualProjectionVerifierInputChecks
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for verify in the verifier model. -/
def verify (target : List ℤ) (bits inside : ℕ) (content : ℤ) (fs : List RootIntegerFactorData) :
    Option (List (ℚ×ℚ)) :=
  let target := rootCanonicalCoefficients target
  let degree := target.length-1
  if target.length < 2 ∨ bits < 1 ∨ degree < inside then none else
  if content=0 ∨ fs.isEmpty=true then none else
  if fs.all headerCheck≠true then none else
  if rootDecodedWeightedDegree (family fs)≠degree then none else
  if fs.all radiusCheck≠true then none else
  if 0 < inside ∧ ¬bits < maximumRadiusBits fs then none else
  let eta : ℚ := if inside=0 then 0 else 1/(2 : ℚ)^bits
  if rootIntegerFactorProduct content (factorList fs)≠target then none else
  if fs.all (fun f => groupCheck f eta)≠true then none else
  let points := rootDecodedReturnList (family fs) eta
  if points.length≠inside ∨ rootDecodedOutsideCount (family fs)≠degree-inside then none else some points

/-- The finite construction in `raw polynomial certificate checker` satisfies `verify_of_generated_checks` under the displayed hypotheses. -/
theorem verify_of_generated_checks (H : List ℤ) (bits inside : ℕ) (c : ℤ) (fs : List RootIntegerFactorData)
    (eta : ℚ) (heta : eta=1/(2 : ℚ)^bits) (hbits : 0 < bits) (hinside : 0 < inside)
    (hdegree : 2 ≤ (rootCanonicalCoefficients H).length)
    (hvalid : inside ≤ (rootCanonicalCoefficients H).length-1) (hc : c≠0)
    (hproduct : rootIntegerFactorProduct c (List.ofFn (fun j =>
      (List.ofFn (family fs j).coefficients,(family fs j).exponent)))=rootCanonicalCoefficients H)
    (haccepted : ∀ j,RootIntegerFactorGuards (family fs j) eta)
    (hweighted : rootDecodedWeightedDegree (family fs)=(rootCanonicalCoefficients H).length-1)
    (hcount : (rootDecodedReturnList (family fs) eta).length=inside)
    (houtside : rootDecodedOutsideCount (family fs)=(rootCanonicalCoefficients H).length-1-inside) :
    verify H bits inside c fs=some (rootDecodedReturnList (family fs) eta) := by
  have hfs : fs≠[] := by
    intro he
    subst fs
    change 0=(rootCanonicalCoefficients H).length-1 at hweighted
    omega
  have hpre := radius_precheck fs bits eta heta haccepted (by rw [hcount]; exact hinside)
  obtain ⟨hheader,hradii,hgroups⟩ := all_header_checks fs eta haccepted
  have hprod : rootIntegerFactorProduct c (factorList fs)=rootCanonicalCoefficients H := by
    rw [← family_factor_list]
    exact hproduct
  have hinitial : ¬((rootCanonicalCoefficients H).length < 2 ∨ bits < 1 ∨
      (rootCanonicalCoefficients H).length-1 < inside) := by omega
  have hempty : fs.isEmpty=false := by
    cases fs with
    | nil => exact (hfs rfl).elim
    | cons f fs => rfl
  have hscalar : ¬(c=0 ∨ fs.isEmpty=true) := by
    rw [hempty]
    simpa only [Bool.false_eq_true,or_false] using hc
  have hencoding : ¬(0 < inside ∧ ¬bits < maximumRadiusBits fs) := by omega
  have he : (if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits)=eta := by
    rw [ite_eq_right (Nat.ne_of_gt hinside)]
    exact heta.symm
  unfold verify
  rw [ite_eq_right hinitial,ite_eq_right hscalar,hheader,ite_eq_right (not_not.mpr rfl),
    ite_eq_right (not_not.mpr hweighted),hradii,ite_eq_right (not_not.mpr rfl),ite_eq_right hencoding,he,
    ite_eq_right (not_not.mpr hprod),hgroups,ite_eq_right (not_not.mpr rfl)]
  rw [ite_eq_right (not_or_intro (not_not.mpr hcount) (not_not.mpr houtside))]


end ActualProjectionDecodedVerifier

namespace ActualProjectionRawRecordDecode
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open ActualProjectionCapRound ActualProjectionTypedRecord
/-- Construction for normalize Record in the verifier model. -/
def normalizeRecord (r : Record) : Record :=
  ⟨rootCanonicalCoefficients r.factor,r.exponent,r.disks⟩

/-- Construction for count Check in the verifier model. -/
def countCheck (r : Record) : Bool := decide (2 ≤ r.factor.length ∧ r.disks.length=r.factor.length-1)

/-- Construction for decode in the verifier model. -/
def decode (records : List Record) : Option (List RootIntegerFactorData) :=
  let records := records.map normalizeRecord
  if records.all countCheck then some (records.map packRecord) else none

/-- The same emitted instruction list satisfies `preserves_of_count` with the displayed gate and query accounting. -/
theorem preserves_of_count (record : Record) (h : countCheck record=true) :
    List.ofFn (packRecord record).coefficients=record.factor ∧
      (packRecord record).exponent=record.exponent ∧
      List.ofFn (fun i => ((packRecord record).centers i,(packRecord record).radii i))=record.disks := by
  have hc : 2 ≤ record.factor.length ∧ record.disks.length=record.factor.length-1 := of_decide_eq_true h
  let n := record.factor.length-2
  let a : Fin (n+2) → ℤ := fun i => record.factor.getD i.val 0
  have hf : record.factor.length=n+2 := by dsimp only [n]; omega
  have hd : record.disks.length=n+1 := by omega
  refine ⟨?_,rfl,pack_disks n a record hd⟩
  apply List.ext_getElem (by rw [List.length_ofFn]; exact hf.symm)
  intro i _ hi
  simp only [List.getElem_ofFn]
  change record.factor.getD i 0=record.factor[i]
  exact List.getD_eq_getElem _ _ hi

end ActualProjectionRawRecordDecode

namespace ActualProjectionDecodedVerifierSound
open ActualProjectionDecodedVerifier ActualProjectionVerifierPrimitives ActualProjectionVerifierDiskChecks
open ActualProjectionVerifierDiskSound
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The finite construction in `raw polynomial certificate checker` satisfies `accepted_guards` under the displayed hypotheses. -/
theorem accepted_guards (H : List ℤ) (bits inside : ℕ) (c : ℤ) (fs : List RootIntegerFactorData)
    (points : List (ℚ×ℚ)) (h : verify H bits inside c fs=some points) :
    let eta : ℚ := if inside=0 then 0 else 1/(2 : ℚ)^bits
    c≠0 ∧ rootIntegerFactorProduct c (List.ofFn (fun j =>
      (List.ofFn (family fs j).coefficients,(family fs j).exponent)))=rootCanonicalCoefficients H ∧
      (∀ j,RootIntegerFactorGuards (family fs j) eta) ∧
      points=rootDecodedReturnList (family fs) eta ∧ points.length=inside ∧
      rootDecodedOutsideCount (family fs)=(rootCanonicalCoefficients H).length-1-inside := by
  classical
  dsimp only [verify] at h
  dsimp only
  generalize heta : (if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits)=eta at h ⊢
  split_ifs at h with h0 h1 h2 h3 h4 h5 h6 h7 h8; try cases h
  have hc : c≠0 := fun he => h1 (Or.inl he)
  have hheader : fs.all headerCheck=true := not_not.mp h2
  have hradius : fs.all radiusCheck=true := not_not.mp h4
  have hgroup : fs.all (fun f => groupCheck f eta)=true := not_not.mp h7
  have hproduct : rootIntegerFactorProduct c (factorList fs)=rootCanonicalCoefficients H := not_not.mp h6
  have haccepted : ∀ j,RootIntegerFactorGuards (family fs j) eta := by
    intro j
    have hm : family fs j∈fs := List.get_mem fs j
    exact guards_of_all_checks _ eta
      (List.all_eq_true.mp hheader _ hm) (List.all_eq_true.mp hradius _ hm) (List.all_eq_true.mp hgroup _ hm)
  have hcounts := not_or.mp h8
  refine ⟨hc,?_,haccepted,rfl,not_not.mp hcounts.1,not_not.mp hcounts.2⟩
  · rw [family_factor_list]
    exact hproduct

/-- The finite construction in `raw polynomial certificate checker` satisfies `returned_of_verify` under the displayed hypotheses. -/
theorem returned_of_verify (H : List ℤ) (bits inside : ℕ) (c : ℤ) (fs : List RootIntegerFactorData)
    (points : List (ℚ×ℚ)) (h : verify H bits inside c fs=some points) :
    ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ ((if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits) : ℝ)) points zs := by
  obtain ⟨hc,hguard,haccepted,hpoints,_,_⟩ := accepted_guards H bits inside c fs points h
  obtain ⟨zs,hm,hpair⟩ := rootDecodedCertificate_returned fs.length H c (family fs)
    (if inside=0 then 0 else 1/(2 : ℚ)^bits) hc hguard haccepted
  refine ⟨zs,hm,?_⟩
  rw [hpoints]
  by_cases hz : inside=0
  · simpa only [hz,ite_true] using hpair
  · simpa only [hz,ite_false,Rat.cast_div,Rat.cast_one,Rat.cast_pow] using hpair


end ActualProjectionDecodedVerifierSound

namespace ActualProjectionRawVerifier
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open ActualProjectionCapRound ActualProjectionRawRecordDecode ActualProjectionDecodedVerifier ActualProjectionDecodedVerifierSound
/-- Construction for verify Records in the verifier model. -/
def verifyRecords (H : List ℤ) (bits inside : ℕ) (c : ℤ) (records : List Record) :
    Option (List (ℚ×ℚ)) := (decode records).bind (verify H bits inside c)

/-- The finite construction in `raw polynomial certificate checker` satisfies `raw_returned_of_verify` under the displayed hypotheses. -/
theorem raw_returned_of_verify (H : List ℤ) (bits inside : ℕ) (c : ℤ)
    (records : List Record) (points : List (ℚ×ℚ))
    (h : verifyRecords H bits inside c records=some points) :
    ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial H).roots.filter (fun z => ‖z‖ < 1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ ((if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits) : ℝ)) points zs := by
  cases he : decode records with
  | none => simp only [verifyRecords,he,Option.bind_none,reduceCtorEq] at h
  | some fs =>
    have hv : verify H bits inside c fs=some points := by simpa only [verifyRecords,he,Option.bind_some] using h
    exact returned_of_verify H bits inside c fs points hv

end ActualProjectionRawVerifier

end RootYunInternal

/-- Data and invariants for Root Projection Factor Record in the verifier model. -/
structure RootProjectionFactorRecord where
  factor : List ℤ
  exponent : ℕ
  disks : List ((ℚ×ℚ)×ℚ)

/-- Construction for root Projection Internal Record in the verifier model. -/
def rootProjectionInternalRecord (r : RootProjectionFactorRecord) :
    RootYunInternal.ActualProjectionCapRound.Record := ⟨r.factor,r.exponent,r.disks⟩

/-- Construction for root Projection Decoded Verify in the verifier model. -/
def rootProjectionDecodedVerify (target : List ℤ) (bits inside : ℕ) (content : ℤ)
    (records : List RootProjectionFactorRecord) : Option (List (ℚ×ℚ)) :=
  RootYunInternal.ActualProjectionRawVerifier.verifyRecords target bits inside content
    (records.map rootProjectionInternalRecord)

/-- The finite construction in `raw polynomial certificate checker` satisfies `rootProjectionDecodedVerify_returned` under the displayed hypotheses. -/
theorem rootProjectionDecodedVerify_returned (target : List ℤ) (bits inside : ℕ) (content : ℤ)
    (records : List RootProjectionFactorRecord) (points : List (ℚ×ℚ))
    (h : rootProjectionDecodedVerify target bits inside content records=some points) :
    ∃ zs : List ℂ,(zs : Multiset ℂ)=(rootIntegerListPolynomial target).roots.filter (fun z => ‖z‖ < 1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖ < 1 ∧
        ‖rootRationalCoordinate q-z‖ ≤ ((if inside=0 then (0 : ℚ) else 1/(2 : ℚ)^bits) : ℝ)) points zs :=
  RootYunInternal.ActualProjectionRawVerifier.raw_returned_of_verify target bits inside content
    (records.map rootProjectionInternalRecord) points h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Uniform Matched Sampling

Uniform Matched Sampling constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [DecidableEq S]

/-- Construction for set Average in the uniform matched sampling model. -/
def setAverage (R : Finset S) (f : S → ℝ) : ℝ := (∑ x ∈ R, f x)/(R.card : ℝ)

/-- Construction for without Replacement Expect in the uniform matched sampling model. -/
def withoutReplacementExpect : Finset S → ℕ → (List S → ℝ) → ℝ
  | _, 0, F => F []
  | R, n+1, F => (∑ x ∈ R, withoutReplacementExpect (R.erase x) n (fun xs => F (x::xs)))/(R.card : ℝ)

/-- Complete original `without_replacement_mono` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mono (R : Finset S) (n : ℕ) (F G : List S → ℝ)
    (h : ∀ xs, F xs ≤ G xs) :
    withoutReplacementExpect R n F ≤ withoutReplacementExpect R n G := by
  induction n generalizing R F G with
  | zero => exact h []
  | succ n ih =>
    rw [withoutReplacementExpect, withoutReplacementExpect]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro x hx
    exact ih (R.erase x) _ _ (fun xs => h (x::xs))

/-- Complete original `without_replacement_mul` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mul (R : Finset S) (n : ℕ) (F : List S → ℝ) (c : ℝ) :
    withoutReplacementExpect R n (fun xs => c*F xs)=c*withoutReplacementExpect R n F := by
  induction n generalizing R F with
  | zero => rfl
  | succ n ih =>
    simp only [withoutReplacementExpect]
    simp_rw [ih]
    rw [← Finset.mul_sum]
    ring

/-- Complete original `without_replacement_nonneg` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_nonneg (R : Finset S) (n : ℕ) (F : List S → ℝ)
    (h : ∀ xs, 0 ≤ F xs) : 0 ≤ withoutReplacementExpect R n F := by
  induction n generalizing R F with
  | zero => exact h []
  | succ n ih =>
    rw [withoutReplacementExpect]
    apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg fun x hx => ih (R.erase x) _ (fun xs => h (x::xs))

/-- Complete original `without_replacement_const` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_const (R : Finset S) (n : ℕ) (hn : n ≤ R.card) (c : ℝ) :
    withoutReplacementExpect R n (fun _ => c)=c := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have hc : (R.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : R.card ≠ 0)
    rw [withoutReplacementExpect]
    have hs : (∑ x ∈ R, withoutReplacementExpect (R.erase x) n (fun _ => c))=
        (R.card : ℝ)*c := by
      calc
        _ = ∑ _x ∈ R, c := by
          apply Finset.sum_congr rfl
          intro x hx
          exact ih (R.erase x) (by rw [Finset.card_erase_of_mem hx]; omega)
        _ = _ := by simp
    rw [hs]
    field_simp

/-- Construction for uniform Law in the uniform matched sampling model. -/
def uniformLaw (X : Type) [Fintype X] [Nonempty X] : FinDist X where
  prob _ := 1/(Fintype.card X : ℝ)
  nonneg _ := by positivity
  sum_one := by
    have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

omit [DecidableEq S] in
/-- Complete original `uniform_set_expect` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem uniform_set_expect (R : Finset S) (hR : R.Nonempty) (f : S → ℝ) :
    let : Nonempty R := ⟨⟨hR.choose,hR.choose_spec⟩⟩
    (uniformLaw R).expect (fun x => f x)=setAverage R f := by
  unfold FinDist.expect uniformLaw setAverage
  simp only [one_div_mul_eq_div, ← Finset.sum_div, Fintype.card_coe]
  congr 1
  exact Finset.sum_coe_sort R f

omit [DecidableEq S] in
/-- Complete original `set_average_mul` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem set_average_mul (R : Finset S) (c : ℝ) (f : S → ℝ) :
    setAverage R (fun x => c*f x)=c*setAverage R f := by
  unfold setAverage
  rw [← Finset.mul_sum]
  ring

/-- Complete original `set_average_erase` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem set_average_erase (R : Finset S) (f : S → ℝ) (x : S) (hx : x ∈ R) :
    setAverage (R.erase x) f=((∑ y ∈ R, f y)-f x)/((R.card-1 : ℕ) : ℝ) := by
  unfold setAverage
  rw [Finset.card_erase_of_mem hx, Finset.sum_erase_eq_sub hx]

omit [DecidableEq S] in
/-- Complete original `set_average_congr` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem set_average_congr (R : Finset S) (f g : S → ℝ) (h : ∀ x ∈ R, f x=g x) :
    setAverage R f=setAverage R g := by
  unfold setAverage
  congr 1
  exact Finset.sum_congr rfl h

omit [DecidableEq S] in
/-- Complete original `set_average_const` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem set_average_const (R : Finset S) (hR : R.Nonempty) (c : ℝ) :
    setAverage R (fun _ => c)=c := by
  have hc : (R.card : ℝ) ≠ 0 := by exact_mod_cast hR.card_pos.ne'
  simp only [setAverage, Finset.sum_const, nsmul_eq_mul]
  field_simp

omit [DecidableEq S] in
/-- Complete original `bounded_set_centered_mgf` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem bounded_set_centered_mgf (R : Finset S) (hR : R.Nonempty) (f : S → ℝ)
    (hf : ∀ x ∈ R, |f x| ≤ 1) (c t : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    setAverage R (fun x => Real.exp (t*c*(f x-setAverage R f))) ≤ Real.exp (t^2/2) := by
  classical
  let : Nonempty R := ⟨⟨hR.choose,hR.choose_spec⟩⟩
  let p := uniformLaw R
  have hm : p.expect (fun x : R => f x)=setAverage R f := uniform_set_expect R hR f
  have hcm : p.expect (fun x : R => c*f x)=c*setAverage R f := by
    rw [finite_expect_mul, hm]
  have hb (x : R) : c*f x ∈ Set.Icc (-c) c := by
    have hx := abs_le.mp (hf x x.property)
    constructor <;> nlinarith
  have ht := finite_hoeffding_centered_mgf R p (fun x => c*f x) (-c) c t (by linarith) hb
  rw [hcm] at ht
  have hfun : (fun x : R => Real.exp (t*(c*f x-c*setAverage R f)))=
      fun x : R => Real.exp (t*c*(f x-setAverage R f)) := by
    funext x
    congr 1
    ring
  rw [hfun] at ht
  have he := uniform_set_expect R hR (fun x => Real.exp (t*c*(f x-setAverage R f)))
  change p.expect (fun x : R => Real.exp (t*c*(f x-setAverage R f)))=_ at he
  rw [he] at ht
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have hc2 : c^2 ≤ 1 := by nlinarith
  have hprod := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hc2)
  nlinarith

/-- Complete original `sampling_increment_identity` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem sampling_increment_identity (R : Finset S) (n : ℕ) (f : S → ℝ)
    (x : S) (hx : x ∈ R) (hcard : 1 < R.card) :
    f x+(n : ℝ)*setAverage (R.erase x) f-((n+1 : ℕ) : ℝ)*setAverage R f=
      (((R.card : ℝ)-(n+1 : ℕ))/(R.card-1 : ℝ))*(f x-setAverage R f) := by
  rw [set_average_erase R f x hx]
  unfold setAverage
  rw [Nat.cast_sub (by omega : 1 ≤ R.card), Nat.cast_one]
  have hN : (R.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : R.card ≠ 0)
  have hd : (R.card : ℝ)-1 ≠ 0 := by
    have hNr : (1 : ℝ) < R.card := by exact_mod_cast hcard
    linarith
  push_cast
  field_simp
  ring

/-- Complete original `sampling_increment_mgf` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem sampling_increment_mgf (R : Finset S) (n : ℕ) (hn : n+1 ≤ R.card)
    (f : S → ℝ) (hf : ∀ x ∈ R, |f x| ≤ 1) (t : ℝ) :
    setAverage R (fun x => Real.exp (t*(f x+(n : ℝ)*setAverage (R.erase x) f-
      ((n+1 : ℕ) : ℝ)*setAverage R f))) ≤ Real.exp (t^2/2) := by
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hcard : R.card=1
  · have hn0 : n=0 := by omega
    subst n
    have hp (x : S) (hx : x ∈ R) : f x=setAverage R f := by
      obtain ⟨y,hy⟩ := Finset.card_eq_one.mp hcard
      rw [hy] at hx
      have he : x=y := Finset.mem_singleton.mp hx
      subst x
      simp [setAverage,hy]
    calc
      _ = setAverage R (fun _ => 1) := set_average_congr R _ _ (by
        intro x hx
        simp only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, zero_mul, add_zero, one_mul]
        rw [hp x hx, sub_self, mul_zero, Real.exp_zero])
      _ = 1 := set_average_const R hR 1
      _ ≤ Real.exp (t^2/2) := by nlinarith [Real.add_one_le_exp (t^2/2),sq_nonneg t]
  · have hcard' : 1 < R.card := by omega
    let c : ℝ := ((R.card : ℝ)-(n+1 : ℕ))/(R.card-1 : ℝ)
    have hd : (0 : ℝ) < (R.card : ℝ)-1 := by
      have hNr : (1 : ℝ) < R.card := by exact_mod_cast hcard'
      linarith
    have hnR : ((n+1 : ℕ) : ℝ) ≤ R.card := by exact_mod_cast hn
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hc1 : c ≤ 1 := by
      dsimp [c]
      apply (div_le_iff₀ hd).mpr
      have hn0 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n+1)
      linarith
    calc
      _ = setAverage R (fun x => Real.exp (t*c*(f x-setAverage R f))) :=
        set_average_congr R _ _ (by
          intro x hx
          rw [sampling_increment_identity R n f x hx hcard']
          dsimp [c]
          congr 1
          ring)
      _ ≤ _ := bounded_set_centered_mgf R hR f hf c t hc0 hc1

/-- Complete original `without_replacement_centered_mgf` guarantee for `UniformMatchedSampling`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_centered_mgf (R : Finset S) (n : ℕ) (hn : n ≤ R.card)
    (f : S → ℝ) (hf : ∀ x ∈ R, |f x| ≤ 1) (t : ℝ) :
    withoutReplacementExpect R n (fun xs => Real.exp
      (t*((xs.map f).sum-(n : ℝ)*setAverage R f))) ≤ Real.exp ((n : ℝ)*t^2/2) := by
  induction n generalizing R with
  | zero => simp [withoutReplacementExpect]
  | succ n ih =>
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    let D : S → ℝ := fun x => f x+(n : ℝ)*setAverage (R.erase x) f-
      ((n+1 : ℕ) : ℝ)*setAverage R f
    have hp (x : S) (hx : x ∈ R) :
        withoutReplacementExpect (R.erase x) n (fun xs => Real.exp
          (t*((((x::xs).map f).sum)-((n+1 : ℕ) : ℝ)*setAverage R f))) ≤
        Real.exp (t*D x)*Real.exp ((n : ℝ)*t^2/2) := by
      have hfun : (fun xs : List S => Real.exp
          (t*((((x::xs).map f).sum)-((n+1 : ℕ) : ℝ)*setAverage R f)))=
          fun xs => Real.exp (t*D x)*Real.exp
            (t*((xs.map f).sum-(n : ℝ)*setAverage (R.erase x) f)) := by
        funext xs
        rw [← Real.exp_add]
        simp only [List.map_cons, List.sum_cons]
        dsimp [D]
        congr 1
        ring
      rw [hfun, without_replacement_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact ih (R.erase x) (by rw [Finset.card_erase_of_mem hx]; omega)
        (fun y hy => hf y (Finset.mem_of_mem_erase hy))
    rw [withoutReplacementExpect]
    calc
      _ ≤ (∑ x ∈ R, Real.exp (t*D x)*Real.exp ((n : ℝ)*t^2/2))/(R.card : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum hp) (by positivity)
      _ = Real.exp ((n : ℝ)*t^2/2)*setAverage R (fun x => Real.exp (t*D x)) := by
        unfold setAverage
        rw [← Finset.sum_mul]
        ring
      _ ≤ Real.exp ((n : ℝ)*t^2/2)*Real.exp (t^2/2) :=
        mul_le_mul_of_nonneg_left (sampling_increment_mgf R n hn f hf t) (Real.exp_pos _).le
      _ = Real.exp (((n+1 : ℕ) : ℝ)*t^2/2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_mono
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_mul
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_nonneg
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_const
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_set_expect
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.set_average_erase
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.bounded_set_centered_mgf
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.sampling_increment_mgf
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_centered_mgf

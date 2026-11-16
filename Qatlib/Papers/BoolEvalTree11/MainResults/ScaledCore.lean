/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models
public import Mathlib.Tactic.FinCases

@[expose] public section


/-! # Actual one-bit span programs and their two witness costs

The legacy witness sets and infima are evaluated exactly. These calculations
supply a nonconstant, nonempty model for auditing the old tree interface.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.ScaledCore
open Models
open scoped BigOperators

/-- The nonconstant one-bit identity function. -/
def bit (x : Fin 1→Bool) : Bool := x 0

/-- A one-dimensional span program with one scalar column. -/
abbrev scaled (s : ℂ) : DirectSpanProgram 1 where
  C := 1
  hC := by norm_num
  v := fun _ _ => s
  flip := fun _ => false

/-- Every nonzero scalar column represents the actual identity function. -/
theorem represents (s : ℂ) (hs : s≠0) : (scaled s).Represents bit := by
  intro x
  cases hx : x 0
  · constructor
    · intro h; simp [bit,hx] at h
    · rintro ⟨a,hz,hr⟩
      have ha : a 0=0 := hz 0 (by simp [DirectSpanProgram.chi,hx])
      have hh := hr (scaled s).target
      simp only [Fin.sum_univ_one,ha,zero_mul,ite_true] at hh
      norm_num at hh
  · constructor
    · intro _
      refine ⟨fun _ => s⁻¹,?_,?_⟩
      · intro j hj
        fin_cases j
        simp [DirectSpanProgram.chi,hx] at hj
      · intro i
        have hi : i=(scaled s).target := Subsingleton.elim _ _
        simp only [Fin.sum_univ_one,inv_mul_cancel₀ hs,hi,ite_true]
    · intro _; exact hx

/-- The represented identity function has both possible outputs. -/
theorem nonconstant : ¬DirectSpanProgram.IsConstant bit := by
  rintro ⟨r,hr⟩
  have he : (false:Bool)=true := (hr (fun _ => false)).trans (hr (fun _ => true)).symm
  cases he

/-- Every true witness has the actual reciprocal scalar and its squared norm cost. -/
theorem trueValue (s : ℂ) (hs : s≠0) (x : Fin 1→Bool) (hx : x 0=true) :
    (scaled s).wsizeTrue x=‖s⁻¹‖^2 := by
  have hset : DirectSpanProgram.witnessCost (fun _ => (1:ℝ)) ''
      (scaled s).trueWitnessSet x={‖s⁻¹‖^2} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hmul : w 0*s=1 := by simpa only [Fin.sum_univ_one] using hw.1
      have hw0 : w 0=s⁻¹ := by
        apply mul_right_cancel₀ hs
        simpa only [inv_mul_cancel₀ hs] using hmul
      simp [DirectSpanProgram.witnessCost,hw0]
    · intro hz
      have hz0 : z=‖s⁻¹‖^2 := by simpa using hz
      subst z
      refine ⟨fun _ => s⁻¹,?_,?_⟩
      · refine ⟨?_,?_,?_⟩
        · simp only [Fin.sum_univ_one,inv_mul_cancel₀ hs]
        · intro i hi; exact False.elim (hi (Subsingleton.elim _ _))
        · intro j hj; fin_cases j; simp [DirectSpanProgram.chi,hx] at hj
      · simp [DirectSpanProgram.witnessCost]
  unfold DirectSpanProgram.wsizeTrue
  rw [hset,csInf_singleton]

/-- Every false witness at an unavailable input has the actual scalar norm cost. -/
theorem falseValue (s : ℂ) (x : Fin 1→Bool) (hx : x 0=false) :
    (scaled s).wsizeFalse x=‖s‖^2 := by
  have hset : DirectSpanProgram.witnessCost (fun _ => (1:ℝ)) ''
      (scaled s).falseWitnessSet x={‖s‖^2} := by
    ext z
    constructor
    · rintro ⟨w,⟨α,hα,hw,_hz⟩,rfl⟩
      have hα0 : α 0=1 := hα
      have hw0 := hw 0
      simp only [Fin.sum_univ_one,hα0,one_mul] at hw0
      simp [DirectSpanProgram.witnessCost,hw0]
    · intro hz
      have hz0 : z=‖s‖^2 := by simpa using hz
      subst z
      refine ⟨fun _ => s,?_,?_⟩
      · refine ⟨fun _ => 1,rfl,?_,?_⟩
        · intro j; simp only [Fin.sum_univ_one,one_mul]
        · intro j hj; fin_cases j; simp [DirectSpanProgram.chi,hx] at hj
      · simp [DirectSpanProgram.witnessCost]
  unfold DirectSpanProgram.wsizeFalse
  rw [hset,csInf_singleton]

/-- A half column has witness costs four and one quarter, on the actual two inputs. -/
theorem halfCosts (x : Fin 1→Bool) :
    (scaled (1/2)).witnessSize bit x=(if x 0 then (4:ℝ) else 1/4) := by
  cases hx : x 0
  · simp only [DirectSpanProgram.witnessSize,bit,hx,Bool.false_eq_true,ite_false]
    rw [falseValue (1/2) x hx]
    norm_num
  · simp only [DirectSpanProgram.witnessSize,bit,hx,ite_true]
    rw [trueValue (1/2) (by norm_num) x hx]
    norm_num

end Qatlib.Papers.BoolEvalTree11.MainResults.ScaledCore

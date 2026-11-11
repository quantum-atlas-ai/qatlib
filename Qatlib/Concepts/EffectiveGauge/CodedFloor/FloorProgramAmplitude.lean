/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Floor Program Amplitude

Coded Floor constructions for Effective Gauge.
Defines `floorProgramHaltsWithin`, `floorProgramAmplitudeApprox`, `floorProgramAmplitude`.
Proves `floorProgramHaltsWithin_zero`, `floorProgramHaltsWithin_mono`, `floorProgramAmplitude_spec`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor

/-- An actual bounded evaluator of finite partial-recursive program code.
The cutoff is the library's numeric evaluation bound, not a runtime clock. -/
def floorProgramHaltsWithin (c : Nat.Partrec.Code) (k : ℕ) : Bool :=
  (Nat.Partrec.Code.evaln k c 0).isSome

/-- Original `floorProgramHaltsWithin_zero` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramHaltsWithin_zero (c : Nat.Partrec.Code) : floorProgramHaltsWithin c 0=false := by
  simp [floorProgramHaltsWithin, Nat.Partrec.Code.evaln]

/-- Original `floorProgramHaltsWithin_mono` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramHaltsWithin_mono (c : Nat.Partrec.Code) (k l : ℕ) (hkl : k ≤ l)
    (hk : floorProgramHaltsWithin c k=true) : floorProgramHaltsWithin c l=true := by
  cases he : Nat.Partrec.Code.evaln k c 0 with
  | none => simp [floorProgramHaltsWithin,he] at hk
  | some v =>
    have hv : v∈Nat.Partrec.Code.evaln k c 0 := by simp [he]
    have hl := Nat.Partrec.Code.evaln_mono hkl hv
    cases he' : Nat.Partrec.Code.evaln l c 0 with
    | none => simp [he'] at hl
    | some w => simp [floorProgramHaltsWithin,he']

/-- This finite rational algorithm inspects only bounded program runs. -/
def floorProgramAmplitudeApprox (c : Nat.Partrec.Code) (b : ℕ) : ℚ :=
  if floorProgramHaltsWithin c b then
    1/(2 : ℚ)^(Nat.findGreatest (fun k => floorProgramHaltsWithin c k=false) b+1+4)
  else 0

/-- Definition of floor Program Amplitude in the Coded Floor construction. -/
noncomputable def floorProgramAmplitude (c : Nat.Partrec.Code) : ℚ := by
  classical
  exact if h : ∃ k, floorProgramHaltsWithin c k=true then 1/(2 : ℚ)^(Nat.find h+4) else 0

/-- Original `floorProgramAmplitude_spec` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramAmplitude_spec (c : Nat.Partrec.Code) :
    0 ≤ floorProgramAmplitude c ∧ floorProgramAmplitude c ≤ 1/16 ∧
      (0<floorProgramAmplitude c ↔ ∃ k, floorProgramHaltsWithin c k=true) := by
  classical
  by_cases h : ∃ k, floorProgramHaltsWithin c k=true
  · rw [floorProgramAmplitude,dif_pos h]
    have hp : (0 : ℚ)<2^(Nat.find h+4) := pow_pos (by norm_num) _
    have hb : (16 : ℚ) ≤ 2^(Nat.find h+4) := by
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega : 4 ≤ Nat.find h+4)
      norm_num at hpow
      exact hpow
    exact ⟨(one_div_pos.mpr hp).le,one_div_le_one_div_of_le (by norm_num) hb,
      iff_of_true (one_div_pos.mpr hp) h⟩
  · rw [floorProgramAmplitude,dif_neg h]
    simp [h]

/-- Original `floorProgramAmplitudeApprox_eq_of_seen` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramAmplitudeApprox_eq_of_seen (c : Nat.Partrec.Code) (b : ℕ)
    (hb : floorProgramHaltsWithin c b=true) : floorProgramAmplitudeApprox c b=floorProgramAmplitude c := by
  classical
  let h : ∃ k, floorProgramHaltsWithin c k=true := ⟨b,hb⟩
  let t := Nat.find h
  have ht : floorProgramHaltsWithin c t=true := Nat.find_spec h
  have htpos : 0<t := by
    by_contra hn
    have he : t=0 := by omega
    rw [he,floorProgramHaltsWithin_zero] at ht
    contradiction
  have htb : t ≤ b := Nat.find_min' h hb
  have hmax : Nat.findGreatest (fun k => floorProgramHaltsWithin c k=false) b=t-1 := by
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨by omega,?_,?_⟩
    · intro _
      cases he : floorProgramHaltsWithin c (t-1) with
      | false => rfl
      | true => exact (Nat.find_min h (by omega : t-1<t) he).elim
    · intro k hk _ hnone
      have hseen := floorProgramHaltsWithin_mono c t k (by omega) ht
      rw [hseen] at hnone
      contradiction
  rw [floorProgramAmplitudeApprox,if_pos hb,hmax]
  rw [floorProgramAmplitude,dif_pos h]
  congr 2
  omega

/-- Original `floorProgramAmplitudeApprox_error` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramAmplitudeApprox_error (c : Nat.Partrec.Code) (b : ℕ) :
    |floorProgramAmplitudeApprox c b-floorProgramAmplitude c| ≤ 1/(2 : ℚ)^b := by
  classical
  by_cases hb : floorProgramHaltsWithin c b=true
  · rw [floorProgramAmplitudeApprox_eq_of_seen c b hb,sub_self,abs_zero]
    positivity
  · rw [floorProgramAmplitudeApprox,if_neg hb,zero_sub,abs_neg,abs_of_nonneg (floorProgramAmplitude_spec c).1]
    by_cases h : ∃ k, floorProgramHaltsWithin c k=true
    · rw [floorProgramAmplitude,dif_pos h]
      have ht : floorProgramHaltsWithin c (Nat.find h)=true := Nat.find_spec h
      have hbt : b<Nat.find h := by
        by_contra hn
        exact hb (floorProgramHaltsWithin_mono c (Nat.find h) b (by omega) ht)
      apply one_div_le_one_div_of_le (pow_pos (by norm_num) b)
      exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
    · rw [floorProgramAmplitude,dif_neg h]
      positivity

/-- Original `floorProgramHaltsWithin_iff_dom` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramHaltsWithin_iff_dom (c : Nat.Partrec.Code) :
    (∃ k, floorProgramHaltsWithin c k=true) ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  constructor
  · rintro ⟨k,hk⟩
    cases he : Nat.Partrec.Code.evaln k c 0 with
    | none => simp [floorProgramHaltsWithin,he] at hk
    | some v =>
      apply Part.dom_iff_mem.mpr
      have hv : v ∈ Nat.Partrec.Code.evaln k c 0 := by simp [he]
      exact ⟨v,Nat.Partrec.Code.evaln_sound hv⟩
  · intro hc
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp hc
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨k,?_⟩
    cases he : Nat.Partrec.Code.evaln k c 0 with
    | none => simp [he] at hk
    | some w => simp [floorProgramHaltsWithin,he]

/-- Original `floorProgramAmplitude_pos_iff_dom` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramAmplitude_pos_iff_dom (c : Nat.Partrec.Code) :
    (0<floorProgramAmplitude c) ↔ (Nat.Partrec.Code.eval c 0).Dom :=
  (floorProgramAmplitude_spec c).2.2.trans (floorProgramHaltsWithin_iff_dom c)

/-- First-order dyadic payload: numerator and denominator, before rational reduction. -/
def floorProgramAmplitudePayload (c : Nat.Partrec.Code) (b : ℕ) : ℕ × ℕ :=
  if floorProgramHaltsWithin c b then
    (1,2^(Nat.findGreatest (fun k => floorProgramHaltsWithin c k=false) b+1+4))
  else (0,1)

/-- Original `floorProgramAmplitudePayload_value` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem floorProgramAmplitudePayload_value (c : Nat.Partrec.Code) (b : ℕ) :
    (floorProgramAmplitudePayload c b).1 / ((floorProgramAmplitudePayload c b).2 : ℚ) =
      floorProgramAmplitudeApprox c b := by
  unfold floorProgramAmplitudePayload floorProgramAmplitudeApprox
  split <;> simp

/-- Original `primrec_floorProgramHaltsWithin` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem primrec_floorProgramHaltsWithin :
    Primrec fun x : Nat.Partrec.Code × ℕ => floorProgramHaltsWithin x.1 x.2 := by
  exact Primrec.option_isSome.comp
    (Nat.Partrec.Code.primrec_evaln.comp ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)))

/-- Original `primrec_floorProgramAmplitudePayload` guarantee for the `FloorProgramAmplitude` construction; the complete source hypotheses are retained. -/
theorem primrec_floorProgramAmplitudePayload :
    Primrec fun x : Nat.Partrec.Code × ℕ => floorProgramAmplitudePayload x.1 x.2 := by
  have hg : Primrec fun x : Nat.Partrec.Code × ℕ =>
      Nat.findGreatest (fun k => floorProgramHaltsWithin x.1 k=false) x.2 := by
    apply Primrec.nat_findGreatest Primrec.snd
    exact Primrec.eq.comp
      (primrec_floorProgramHaltsWithin.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (Primrec.const false)
  have he := Primrec.nat_add.comp (Primrec.nat_add.comp hg (Primrec.const 1)) (Primrec.const 4)
  have hp : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  apply (Primrec.cond primrec_floorProgramHaltsWithin
    ((Primrec.const 1).pair (hp.comp (Primrec.const 2) he))
    (Primrec.const (0,1))).of_eq
  intro x
  cases hx : floorProgramHaltsWithin x.1 x.2 <;> simp [floorProgramAmplitudePayload,hx]

end Qatlib.Concepts.EffectiveGauge.CodedFloor

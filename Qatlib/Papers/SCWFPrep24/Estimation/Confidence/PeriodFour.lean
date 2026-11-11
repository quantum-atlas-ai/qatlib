/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPromise
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.FullLossNuisance
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Period Four

The original periodic coordinate modulo four, including every wrap edge.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PeriodFour
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The original periodic coordinate modulo four, including every wrap edge. -/
def residue4 (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j : Fin d) (x : Fin d → Fin N) : ZMod 4 :=
  ZMod.castHom h4 (ZMod 4) ((ZMod.finEquiv N) (x j))

/-- The literal original double shift changes the selected four-residue by exactly two. -/
theorem residue4_double_shift (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j k : Fin d)
    (x : Fin d → Fin N) :
    residue4 d N h4 j (periodicDoubleShift d N k x)=residue4 d N h4 j x+(if k=j then 2 else 0) := by
  unfold residue4
  rw [periodic_double_shift_coordinates,map_add]
  by_cases h : k=j
  · subst k
    simp only [ite_true,map_ofNat]
  · simp [h,Ne.symm h]

/-- The real period-four pattern keeps the low coordinate bit and flips its high residue bit. -/
def side4 (q : ZMod 4) : Bool := decide (q=2 ∨ q=3)

/-- The fixed four-color pattern flips under addition by two. -/
theorem side4_add_two (q : ZMod 4) : side4 (q+2)=!(side4 q) := by
  fin_cases q <;> decide

/-- The actual weak-spin sign of the real period-four witness. -/
def sign4 (q : ZMod 4) : ℝ := if side4 q then -1 else 1

/-- Every actual period-four sign is a unit real sign. -/
theorem sign4_unit (q : ZMod 4) : (sign4 q)^2=1 := by
  unfold sign4
  split_ifs <;> norm_num

/-- Adding two negates the actual real sign, including modular wrap. -/
theorem sign4_add_two (q : ZMod 4) : sign4 (q+2)=-sign4 q := by
  simp only [sign4,side4_add_two]
  cases side4 q <;> norm_num

/-- The actual periodic-grid sign field of the dense witness. -/
def field (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j : Fin d) (x : Fin d → Fin N) : ℝ :=
  sign4 (residue4 d N h4 j x)

/-- The original double shift flips exactly the selected direction of the dense witness. -/
theorem field_double_shift (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j k : Fin d)
    (x : Fin d → Fin N) :
    field d N h4 j (periodicDoubleShift d N k x)=if k=j then -field d N h4 j x else field d N h4 j x := by
  unfold field
  rw [residue4_double_shift]
  by_cases h : k=j
  · simp only [ite_eq_left h,sign4_add_two]
  · simp only [ite_eq_right h,add_zero]

/-- The real periodic witness has exactly zero global sign mean, derived from the actual permutation. -/
theorem field_sum_zero (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j : Fin d) :
    (∑ x : Fin d → Fin N,field d N h4 j x)=0 := by
  have h := Equiv.sum_comp (periodicDoubleShift d N j) (field d N h4 j)
  simp_rw [field_double_shift] at h
  simp only [ite_true] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- The dense witness's actual Bell probability is nonzero in exactly one original double-shift direction. -/
theorem field_bell (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j k : Fin d)
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (x : Fin d → Fin N) :
    bellProbability (weakSpin b (field d N h4 j x))
      (weakSpin b (field d N h4 j (periodicDoubleShift d N k x)))=
        if k=j then 2*b*(1-b) else 0 := by
  rw [weakSpin_bell_exact b _ _ hb0 hb1,field_double_shift]
  by_cases h : k=j
  · rw [ite_eq_left h,ite_eq_left h]
    have hu : (field d N h4 j x)^2=1 := sign4_unit _
    calc
      b*(1-b)*(-field d N h4 j x-field d N h4 j x)^2/2=
          2*b*(1-b)*(field d N h4 j x)^2 := by ring
      _ = _ := by simp only [hu,mul_one]
  · simp only [ite_eq_right h,sub_self,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_div]

/-- Every real weak-sign field has the original pointwise source-coordinate normalization. -/
theorem real_weak_coordinate_mass {S : Type*} (b : ℝ) (σ : S → ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (hσ : ∀ x,(σ x)^2=1) (x : S) :
    (real0 (fun x => weakSpin b (σ x)) x)^2+(imag0 (fun x => weakSpin b (σ x)) x)^2+
      (real1 (fun x => weakSpin b (σ x)) x)^2+(imag1 (fun x => weakSpin b (σ x)) x)^2=1 := by
  have h := weakSpin_normalized b (σ x) hb0 hb1 (hσ x)
  simp only [Normalized,Fintype.sum_bool,Complex.sq_norm] at h
  simpa only [real0,imag0,real1,imag1,Complex.normSq_apply,pow_two,add_assoc,add_comm,add_left_comm] using h

/-- The actual real witnesses have exactly zero original current before any measurement. -/
theorem real_weak_current {S : Type*} {d : ℕ} (b : ℝ) (σ : S → ℝ)
    (e : Fin d → Equiv.Perm S) (j : Fin d) (x : S) :
    spinorCurrentMean (real0 (fun x => weakSpin b (σ x))) (imag0 (fun x => weakSpin b (σ x)))
      (real1 (fun x => weakSpin b (σ x))) (imag1 (fun x => weakSpin b (σ x))) e j x=0 := by
  simp [spinorCurrentMean,spinorInnerIm,imag0,imag1,weakSpin]

/-- The actual original Bell mean of the dense witness is exact in every periodic direction. -/
theorem field_bell_mean (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j k : Fin d)
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) :
    bellMean (real0 (fun x => weakSpin b (field d N h4 j x)))
      (imag0 (fun x => weakSpin b (field d N h4 j x)))
      (real1 (fun x => weakSpin b (field d N h4 j x)))
      (imag1 (fun x => weakSpin b (field d N h4 j x))) (periodicDoubleShift d N k)=
        if k=j then 2*b*(1-b) else 0 := by
  unfold bellMean
  simp_rw [complexSpinor_parts,field_bell d N h4 j k b hb0 hb1]
  exact site_mean_const _

/-- Every actual real weak field has exactly its original Bell spin loss, since its original current is zero. -/
theorem real_weak_loss_bell {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (b : ℝ) (σ : S → ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hσ : ∀ x,(σ x)^2=1)
    (e : Fin d → Equiv.Perm S) (h lam : ℝ) (hh : h≠0) :
    spinorDiscreteLoss (real0 (fun x => weakSpin b (σ x))) (imag0 (fun x => weakSpin b (σ x)))
      (real1 (fun x => weakSpin b (σ x))) (imag1 (fun x => weakSpin b (σ x)))
      (fun _ _ => 0) e h 1 lam=
        (2*lam^2/h^2)*(∑ j : Fin d,bellMean
          (real0 (fun x => weakSpin b (σ x))) (imag0 (fun x => weakSpin b (σ x)))
          (real1 (fun x => weakSpin b (σ x))) (imag1 (fun x => weakSpin b (σ x))) ((e j).trans (e j))) := by
  have hn := real_weak_coordinate_mass b σ hb0 hb1 hσ
  have hG : 4*(lam^2/(2*h^2))=2*lam^2/h^2 := by field_simp; ring
  rw [spinor_discrete_loss_eq _ _ _ _ hn (fun _ _ => 0) e h 1 lam hh one_ne_zero]
  rw [implemented_loss_bell_form _ _ _ _ _ _ hn]
  simp only [real_weak_current,mul_zero,sub_zero,zero_pow (by decide : (2 : ℕ)≠0),
    site_mean_const,Finset.sum_const_zero,zero_add]
  rw [hG]

/-- The dense period-four witness has the exact full original loss, with no omitted velocity term. -/
theorem field_full_loss (d N : ℕ) [NeZero N] (h4 : 4 ∣ N) (j : Fin d)
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (h lam : ℝ) (hh : h≠0) :
    spinorDiscreteLoss (real0 (fun x => weakSpin b (field d N h4 j x)))
      (imag0 (fun x => weakSpin b (field d N h4 j x)))
      (real1 (fun x => weakSpin b (field d N h4 j x)))
      (imag1 (fun x => weakSpin b (field d N h4 j x)))
      (fun _ _ => 0) (periodicUnitShift d N) h 1 lam=(2*lam^2/h^2)*(2*b*(1-b)) := by
  rw [real_weak_loss_bell b (field d N h4 j) hb0 hb1 (fun _ => sign4_unit _) (periodicUnitShift d N) h lam hh]
  simp only [periodic_unit_shift_square,field_bell_mean d N h4 j _ b hb0 hb1,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The actual constant-sign weak field has zero Bell mean on every address map. -/
theorem constant_bell_mean {S : Type} [Fintype S] [Nonempty S] (τ : S → S)
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) :
    bellMean (real0 (fun _x : S => weakSpin b 1)) (imag0 (fun _x : S => weakSpin b 1))
      (real1 (fun _x : S => weakSpin b 1)) (imag1 (fun _x : S => weakSpin b 1)) τ=0 := by
  unfold bellMean
  simp_rw [complexSpinor_parts,weakSpin_bell_exact b 1 1 hb0 hb1]
  simp only [sub_self,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_div]
  exact site_mean_const _

/-- The actual constant-sign input has zero complete original loss. -/
theorem constant_full_loss {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (e : Fin d → Equiv.Perm S) (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (h lam : ℝ) (hh : h≠0) :
    spinorDiscreteLoss (real0 (fun _x : S => weakSpin b 1)) (imag0 (fun _x : S => weakSpin b 1))
      (real1 (fun _x : S => weakSpin b 1)) (imag1 (fun _x : S => weakSpin b 1))
      (fun _ _ => 0) e h 1 lam=0 := by
  rw [real_weak_loss_bell b (fun _x : S => 1) hb0 hb1 (by intro; norm_num) e h lam hh]
  simp only [constant_bell_mean _ b hb0 hb1,Finset.sum_const_zero,mul_zero]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PeriodFour

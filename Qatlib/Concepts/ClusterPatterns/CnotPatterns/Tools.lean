/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Wire
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical

def pin5 (a0 a1 a2 a3 a4 : Bool) : Reg 5 := fun t =>
  if (t : ℕ) = 0 then a0 else if (t : ℕ) = 1 then a1 else if (t : ℕ) = 2 then a2
  else if (t : ℕ) = 3 then a3 else a4

@[simp] theorem pin5_0 (a0 a1 a2 a3 a4 : Bool) : pin5 a0 a1 a2 a3 a4 0 = a0 := rfl

@[simp] theorem pin5_1 (a0 a1 a2 a3 a4 : Bool) : pin5 a0 a1 a2 a3 a4 1 = a1 := rfl

@[simp] theorem pin5_2 (a0 a1 a2 a3 a4 : Bool) : pin5 a0 a1 a2 a3 a4 2 = a2 := rfl

@[simp] theorem pin5_3 (a0 a1 a2 a3 a4 : Bool) : pin5 a0 a1 a2 a3 a4 3 = a3 := rfl

@[simp] theorem pin5_4 (a0 a1 a2 a3 a4 : Bool) : pin5 a0 a1 a2 a3 a4 4 = a4 := rfl

theorem reg5_eq_pin5 (x : Reg 5) : x = pin5 (x 0) (x 1) (x 2) (x 3) (x 4) := by
  funext t
  fin_cases t <;> rfl

def pin6 (a0 a1 a2 a3 a4 a5 : Bool) : Reg 6 := fun t =>
  if (t : ℕ) = 0 then a0 else if (t : ℕ) = 1 then a1 else if (t : ℕ) = 2 then a2
  else if (t : ℕ) = 3 then a3 else if (t : ℕ) = 4 then a4 else a5

@[simp] theorem pin6_0 (a0 a1 a2 a3 a4 a5 : Bool) : pin6 a0 a1 a2 a3 a4 a5 0 = a0 := rfl

@[simp] theorem pin6_1 (a0 a1 a2 a3 a4 a5 : Bool) : pin6 a0 a1 a2 a3 a4 a5 1 = a1 := rfl

@[simp] theorem pin6_2 (a0 a1 a2 a3 a4 a5 : Bool) : pin6 a0 a1 a2 a3 a4 a5 2 = a2 := rfl

@[simp] theorem pin6_3 (a0 a1 a2 a3 a4 a5 : Bool) : pin6 a0 a1 a2 a3 a4 a5 3 = a3 := rfl

@[simp] theorem pin6_4 (a0 a1 a2 a3 a4 a5 : Bool) : pin6 a0 a1 a2 a3 a4 a5 4 = a4 := rfl

@[simp] theorem pin6_5 (a0 a1 a2 a3 a4 a5 : Bool) : pin6 a0 a1 a2 a3 a4 a5 5 = a5 := rfl

theorem reg6_eq_pin6 (x : Reg 6) : x = pin6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  funext t
  fin_cases t <;> rfl

theorem sum_prod4_bool (g : Bool × Bool × Bool × Bool → ℂ) :
    ∑ p : Bool × Bool × Bool × Bool, g p = ∑ a, ∑ b, ∑ c, ∑ d, g (a, b, c, d) := by
  have h1 : (∑ p : Bool × Bool × Bool × Bool, g p)
      = ∑ a : Bool, ∑ q : Bool × (Bool × Bool), g (a, q) :=
    Fintype.sum_prod_type g
  have h2 : ∀ a : Bool, (∑ q : Bool × (Bool × Bool), g (a, q))
      = ∑ b : Bool, ∑ r : Bool × Bool, g (a, (b, r)) := fun a =>
    Fintype.sum_prod_type (fun q => g (a, q))
  have h3 : ∀ a b : Bool, (∑ r : Bool × Bool, g (a, (b, r)))
      = ∑ c : Bool, ∑ d : Bool, g (a, (b, (c, d))) := fun a b =>
    Fintype.sum_prod_type (fun r => g (a, (b, r)))
  rw [h1]
  simp only [h2]
  simp only [h3]

theorem sum_prod5_bool (g : Bool × Bool × Bool × Bool × Bool → ℂ) :
    ∑ p : Bool × Bool × Bool × Bool × Bool, g p =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, g (a, b, c, d, e) := by
  have h1 : (∑ p : Bool × Bool × Bool × Bool × Bool, g p)
      = ∑ a : Bool, ∑ q : Bool × (Bool × (Bool × Bool)), g (a, q) :=
    Fintype.sum_prod_type g
  have h2 : ∀ a : Bool, (∑ q : Bool × (Bool × (Bool × Bool)), g (a, q))
      = ∑ b : Bool, ∑ r : Bool × (Bool × Bool), g (a, (b, r)) := fun a =>
    Fintype.sum_prod_type (fun q => g (a, q))
  have h3 : ∀ a b : Bool, (∑ r : Bool × (Bool × Bool), g (a, (b, r)))
      = ∑ c : Bool, ∑ s : Bool × Bool, g (a, (b, (c, s))) := fun a b =>
    Fintype.sum_prod_type (fun r => g (a, (b, r)))
  have h4 : ∀ a b c : Bool, (∑ s : Bool × Bool, g (a, (b, (c, s))))
      = ∑ d : Bool, ∑ e : Bool, g (a, (b, (c, (d, e)))) := fun a b c =>
    Fintype.sum_prod_type (fun s => g (a, (b, (c, s))))
  rw [h1]
  simp only [h2]
  simp only [h3]
  simp only [h4]

theorem sum_reg5_pin_prod (f : Reg 5 → ℂ) :
    ∑ z : Reg 5, f z
      = ∑ p : Bool × Bool × Bool × Bool × Bool,
          f (pin5 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  refine Finset.sum_bij (fun z _ => (z 0, z 1, z 2, z 3, z 4)) ?_ ?_ ?_ ?_
  · intro z _; simp
  · intro z1 _ z2 _ heq
    have h0 : z1 0 = z2 0 := congrArg Prod.fst heq
    have h1 : z1 1 = z2 1 := congrArg (fun p : Bool × Bool × Bool × Bool × Bool => p.2.1) heq
    have h2 : z1 2 = z2 2 := congrArg (fun p : Bool × Bool × Bool × Bool × Bool => p.2.2.1) heq
    have h3 : z1 3 = z2 3 := congrArg (fun p : Bool × Bool × Bool × Bool × Bool => p.2.2.2.1) heq
    have h4 : z1 4 = z2 4 := congrArg (fun p : Bool × Bool × Bool × Bool × Bool => p.2.2.2.2) heq
    rw [reg5_eq_pin5 z1, reg5_eq_pin5 z2]
    simp [h0, h1, h2, h3, h4]
  · intro p _
    refine ⟨pin5 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, Finset.mem_univ _, ?_⟩
    obtain ⟨a, b, c, d, e⟩ := p
    rfl
  · intro z _
    conv_lhs => rw [reg5_eq_pin5 z]

theorem sum_reg5_pin (f : Reg 5 → ℂ) :
    ∑ z : Reg 5, f z =
      ∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, f (pin5 b0 b1 b2 b3 b4) := by
  rw [sum_reg5_pin_prod]
  exact sum_prod5_bool _

theorem sum_reg6_fixed (f : Reg 6 → ℂ) (a0 a5 : Bool)
    (hvan : ∀ c : Reg 6, (c 0 ≠ a0 ∨ c 5 ≠ a5) → f c = 0) :
    ∑ c : Reg 6, f c =
      ∑ b1, ∑ b2, ∑ b3, ∑ b4, f (pin6 a0 b1 b2 b3 b4 a5) := by
  have hfilter :
      ∑ c : Reg 6, f c
        = ∑ c ∈ (Finset.univ.filter fun c : Reg 6 => c 0 = a0 ∧ c 5 = a5), f c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : c 0 = a0 ∧ c 5 = a5
    · rw [if_pos h]
    · rw [if_neg h]
      have h' : c 0 ≠ a0 ∨ c 5 ≠ a5 := by
        by_contra hc
        push Not at hc
        exact h hc
      exact hvan c h'
  have hprod :
      ∑ c ∈ (Finset.univ.filter fun c : Reg 6 => c 0 = a0 ∧ c 5 = a5), f c
        = ∑ p : Bool × Bool × Bool × Bool,
            f (pin6 a0 p.1 p.2.1 p.2.2.1 p.2.2.2 a5) := by
    refine Finset.sum_bij (fun c _ => (c 1, c 2, c 3, c 4)) ?_ ?_ ?_ ?_
    · intro c hc; simp
    · intro c1 hc1 c2 hc2 heq
      have h1 : c1 0 = a0 ∧ c1 5 = a5 := by
        simpa using (Finset.mem_filter.mp hc1).2
      have h2 : c2 0 = a0 ∧ c2 5 = a5 := by
        simpa using (Finset.mem_filter.mp hc2).2
      have e1 : c1 1 = c2 1 := congrArg Prod.fst heq
      have e2 : c1 2 = c2 2 :=
        congrArg (fun p : Bool × Bool × Bool × Bool => p.2.1) heq
      have e3 : c1 3 = c2 3 :=
        congrArg (fun p : Bool × Bool × Bool × Bool => p.2.2.1) heq
      have e4 : c1 4 = c2 4 :=
        congrArg (fun p : Bool × Bool × Bool × Bool => p.2.2.2) heq
      conv_lhs => rw [reg6_eq_pin6 c1]
      conv_rhs => rw [reg6_eq_pin6 c2]
      simp [h1.1, h1.2, h2.1, h2.2, e1, e2, e3, e4]
    · intro p _
      refine ⟨pin6 a0 p.1 p.2.1 p.2.2.1 p.2.2.2 a5, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [pin6_0, pin6_5]
      · obtain ⟨b1, b2, b3, b4⟩ := p
        rfl
    · intro c hc
      have h1 : c 0 = a0 ∧ c 5 = a5 := by
        simpa using (Finset.mem_filter.mp hc).2
      conv_lhs => rw [reg6_eq_pin6 c]
      rw [h1.1, h1.2]
  rw [hfilter, hprod]
  exact sum_prod4_bool _

theorem sum_bool_eq {α : Type*} [AddCommMonoid α] (f : Bool → α) :
    ∑ b : Bool, f b = f true + f false :=
  Fintype.sum_bool f

theorem sum_ite_bool {α : Type*} [AddCommMonoid α] (b : Bool) (g : Bool → α) :
    ∑ a : Bool, (if a = b then g a else 0) = g b := by
  cases b <;> simp [sum_bool_eq]

theorem sv_eq_ofReal (α : ℝ) (o b : Bool) :
    mpSVector α o b
      = (((if b then (if o then -Real.exp α else Real.exp α) else 1) / Real.sqrt 2 : ℝ) : ℂ) := by
  have hexp : Complex.exp (Complex.ofReal α) = ((Real.exp α : ℝ) : ℂ) :=
    (Complex.ofReal_exp α).symm
  simp only [mpSVector, hexp]
  rcases b with rfl | rfl <;> rcases o with rfl | rfl <;>
    simp [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg]

theorem star_sv (α : ℝ) (o b : Bool) : star (mpSVector α o b) = mpSVector α o b := by
  rw [sv_eq_ofReal]
  exact Complex.conj_ofReal _
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a

def cnotAux_pin4 (a0 a1 a2 a3 : Bool) : Reg 4 := fun t =>
  if (t : ℕ) = 0 then a0 else if (t : ℕ) = 1 then a1 else if (t : ℕ) = 2 then a2 else a3

@[simp] theorem cnotAux_pin4_0 (a0 a1 a2 a3 : Bool) : cnotAux_pin4 a0 a1 a2 a3 0 = a0 := rfl

@[simp] theorem cnotAux_pin4_1 (a0 a1 a2 a3 : Bool) : cnotAux_pin4 a0 a1 a2 a3 1 = a1 := rfl

@[simp] theorem cnotAux_pin4_2 (a0 a1 a2 a3 : Bool) : cnotAux_pin4 a0 a1 a2 a3 2 = a2 := rfl

@[simp] theorem cnotAux_pin4_3 (a0 a1 a2 a3 : Bool) : cnotAux_pin4 a0 a1 a2 a3 3 = a3 := rfl

theorem cnotAux_reclause4_eq_pin4 (x : Reg 4) : x = cnotAux_pin4 (x 0) (x 1) (x 2) (x 3) := by
  funext t
  fin_cases t <;> rfl

theorem cnotAux_sum_reclause4_fix (f : Reg 4 → ℂ) (a0 a2 a3 : Bool)
    (hvan : ∀ c : Reg 4, (c 0 ≠ a0 ∨ c 2 ≠ a2 ∨ c 3 ≠ a3) → f c = 0) :
    ∑ c : Reg 4, f c = ∑ b1 : Bool, f (cnotAux_pin4 a0 b1 a2 a3) := by
  have hfilter :
      ∑ c : Reg 4, f c
        = ∑ c ∈ (Finset.univ.filter fun c : Reg 4 => c 0 = a0 ∧ c 2 = a2 ∧ c 3 = a3), f c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : c 0 = a0 ∧ c 2 = a2 ∧ c 3 = a3
    · rw [if_pos h]
    · rw [if_neg h]
      have h' : c 0 ≠ a0 ∨ c 2 ≠ a2 ∨ c 3 ≠ a3 := by
        by_contra hc
        push Not at hc
        exact h hc
      exact hvan c h'
  have hprod :
      ∑ c ∈ (Finset.univ.filter fun c : Reg 4 => c 0 = a0 ∧ c 2 = a2 ∧ c 3 = a3), f c
        = ∑ b1 : Bool, f (cnotAux_pin4 a0 b1 a2 a3) := by
    refine Finset.sum_bij (fun c _ => c 1) ?_ ?_ ?_ ?_
    · intro c _; simp
    · intro c1 hc1 c2 hc2 heq
      obtain ⟨h10, h12, h13⟩ : c1 0 = a0 ∧ c1 2 = a2 ∧ c1 3 = a3 := by
        simpa using (Finset.mem_filter.mp hc1).2
      obtain ⟨h20, h22, h23⟩ : c2 0 = a0 ∧ c2 2 = a2 ∧ c2 3 = a3 := by
        simpa using (Finset.mem_filter.mp hc2).2
      conv_lhs => rw [cnotAux_reclause4_eq_pin4 c1]
      conv_rhs => rw [cnotAux_reclause4_eq_pin4 c2]
      simp [h10, h12, h13, h20, h22, h23, heq]
    · intro b _
      refine ⟨cnotAux_pin4 a0 b a2 a3, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [cnotAux_pin4_0, cnotAux_pin4_2, cnotAux_pin4_3]
      · rfl
    · intro c hc
      obtain ⟨h10, h12, h13⟩ : c 0 = a0 ∧ c 2 = a2 ∧ c 3 = a3 := by
        simpa using (Finset.mem_filter.mp hc).2
      conv_lhs => rw [cnotAux_reclause4_eq_pin4 c, h10, h12, h13]
  rw [hfilter, hprod]

theorem cnotAux_star_bitPhase (b : Bool) :
    star (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b) = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b := by
  rcases Bool.eq_false_or_eq_true b with h | h <;> rw [h] <;>
    simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

theorem cnotAux_bitPhase_mul_star (b : Bool) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b * star (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b) = 1 := by
  rw [cnotAux_star_bitPhase, Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase_sq]

theorem cnotAux_bitPhase_and (a b : Bool) :
    (if a && b then (-1 : ℂ) else 1) = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (a && b) := by
  rcases Bool.eq_false_or_eq_true (a && b) with h | h <;> rw [h] <;>
    simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

theorem cnotAux_bitPhase_inj {a b : Bool}
    (h : Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase a = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h (by norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase])
  · exact absurd h (by norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase])
  · rfl

theorem cnotAux_one_add_bitPhase (e : Bool) :
    (1 : ℂ) + Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase e = if e then 0 else 2 := by
  rcases Bool.eq_false_or_eq_true e with h | h <;> rw [h] <;>
    simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase] <;> norm_num

theorem cnotAux_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Complex.ofReal_ofNat]

theorem cnotAux_sqrt8_eq : (Real.sqrt 8 : ℝ) = 2 * Real.sqrt 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
  have hs : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [show (2 * Real.sqrt 2) * (2 * Real.sqrt 2)
      = 2 * 2 * (Real.sqrt 2 * Real.sqrt 2) by ring, hs]
  norm_num

theorem cnotAux_inv_sqrt8 : ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ / 2 := by
  rw [cnotAux_sqrt8_eq, Complex.ofReal_mul, mul_inv, Complex.ofReal_ofNat]
  ring

theorem cnotAux_inv_sqrt2_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ :=
  Clause18Wire1a.hcinv

theorem cnotAux_inv_sqrt2_cube :
    (((Real.sqrt 2 : ℝ) : ℂ) ^ 3)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [pow_two, cnotAux_sqrt2_sq]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h2, mul_inv]
  ring

theorem cnotAux_inv_sqrt2_cube' :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by
  rw [inv_pow, cnotAux_inv_sqrt2_cube]

theorem cnotAux_smul_mul {l m n : ℕ} (a : ℂ) (A : Matrix (Fin l) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin n) ℂ) : (a • A) * B = a • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem cnotAux_smul_mul_smul {l m n : ℕ} (a b : ℂ) (A : Matrix (Fin l) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin n) ℂ) : (a • A) * (b • B) = (a * b) • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm,
    Finset.mul_sum]

theorem cnotAux_bv1 (y : Fin 2) : ((bitVecEquiv 1).symm y) 0 = decide (y = 1) := by
  fin_cases y <;> decide

theorem cnotAux_bitVec1 (y : Reg 1) : (bitVecEquiv 1) y = if y 0 then 1 else 0 := by
  cases h : y 0
  · have hy : y = fun _ => false := by
      funext t
      fin_cases t
      simp [h]
    subst hy
    decide
  · have hy : y = fun _ => true := by
      funext t
      fin_cases t
      simp [h]
    subst hy
    decide

theorem cnotAux_star_inv_sqrt2 : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [star_inv₀]
  exact congrArg (fun x : ℂ => x⁻¹) (Complex.conj_ofReal _)

theorem cnotAux_sv0 (o b : Bool) :
    mpSVector 0 o b
      = (if b then (if o then (-1 : ℂ) else 1) else 1) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [sv_zero]
  rcases b with rfl | rfl <;> rcases o with rfl | rfl <;>
    simp [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat,
      div_eq_mul_inv]

theorem cnotAux_star_sv0 (o b : Bool) :
    star (mpSVector 0 o b)
      = (if b then (if o then (-1 : ℂ) else 1) else 1) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [star_sv, cnotAux_sv0]

theorem cnotAux_bv2_bits (xp : Fin 4) :
    ((bitVecEquiv 2).symm xp) 0 = decide (2 ≤ (xp : ℕ))
      ∧ ((bitVecEquiv 2).symm xp) 1 = decide ((xp : ℕ) % 2 = 1) := by
  fin_cases xp <;> decide

@[simp] theorem cnotAux_bv2_00 : ((bitVecEquiv 2).symm 0) 0 = false := by decide

@[simp] theorem cnotAux_bv2_01 : ((bitVecEquiv 2).symm 0) 1 = false := by decide

@[simp] theorem cnotAux_bv2_10 : ((bitVecEquiv 2).symm 1) 0 = false := by decide

@[simp] theorem cnotAux_bv2_11 : ((bitVecEquiv 2).symm 1) 1 = true := by decide

@[simp] theorem cnotAux_bv2_20 : ((bitVecEquiv 2).symm 2) 0 = true := by decide

@[simp] theorem cnotAux_bv2_21 : ((bitVecEquiv 2).symm 2) 1 = false := by decide

@[simp] theorem cnotAux_bv2_30 : ((bitVecEquiv 2).symm 3) 0 = true := by decide

@[simp] theorem cnotAux_bv2_31 : ((bitVecEquiv 2).symm 3) 1 = true := by decide
end Qatlib.Concepts.ClusterPatterns.CnotPatterns

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
  set_option linter.unusedSimpArgs false in
set_option autoImplicit false
set_option maxHeartbeats 800000

private noncomputable def clause3Kappa (s : Bool × Bool) (v : Fin 2) : Operator 2 :=
  if v = 0 then (if s.1 then pauliX else 1) * (if s.2 then (1 : Operator 2) else pauliZ)
  else (if s.1 then pauliX else 1) * (if s.2 then pauliZ else (1 : Operator 2))

private theorem clause3Kappa_pauli (s : Bool × Bool) (v : Fin 2) : MbqcPauliWire (clause3Kappa s v) := by
  obtain ⟨s1, s2⟩ := s
  fin_cases v <;> cases s1 <;> cases s2 <;> simp [clause3Kappa, MbqcPauliWire]

private theorem sum_reg_erase_delta {n : ℕ} (x : Reg n) (v : Fin n) (F : Reg n → ℂ) :
    (∑ y : Reg n, (∏ i ∈ (Finset.univ : Finset (Fin n)).erase v,
        (if x i = y i then (1 : ℂ) else 0)) * F y)
      = F (Function.update x v false) + F (Function.update x v true) := by
  have hupd : Function.update x v false ≠ Function.update x v true := by
    intro h
    have h1 : Function.update x v false v = false := Function.update_self v false x
    rw [h] at h1
    have h2 : Function.update x v true v = true := Function.update_self v true x
    rw [h1] at h2
    exact Bool.false_ne_true h2
  have hprod : ∀ y : Reg n,
      (∏ i ∈ (Finset.univ : Finset (Fin n)).erase v, (if x i = y i then (1 : ℂ) else 0)) * F y
        = (if y = Function.update x v false then F (Function.update x v false) else 0)
          + (if y = Function.update x v true then F (Function.update x v true) else 0) := by
    intro y
    by_cases hc : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase v, x i = y i
    · have hy : y = Function.update x v (y v) := by
        funext i
        by_cases hi : i = v
        · subst hi
          simp
        · rw [Function.update_of_ne hi]
          exact (hc i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)).symm
      rcases hyv : y v with hyv | hyv
      · have hy' : y = Function.update x v false := by rw [hy, hyv]
        subst hy'
        have hprod' : (∏ i ∈ (Finset.univ : Finset (Fin n)).erase v,
            (if x i = Function.update x v false i then (1 : ℂ) else 0)) = 1 := by
          refine Finset.prod_eq_one fun i hi => ?_
          rw [if_pos (hc i hi)]
        rw [hprod', one_mul, if_pos rfl, if_neg hupd, add_zero]
      · have hy' : y = Function.update x v true := by rw [hy, hyv]
        subst hy'
        have hprod' : (∏ i ∈ (Finset.univ : Finset (Fin n)).erase v,
            (if x i = Function.update x v true i then (1 : ℂ) else 0)) = 1 := by
          refine Finset.prod_eq_one fun i hi => ?_
          rw [if_pos (hc i hi)]
        rw [hprod', one_mul, if_neg (Ne.symm hupd), if_pos rfl, zero_add]
    · have hex : ∃ i ∈ (Finset.univ : Finset (Fin n)).erase v, x i ≠ y i := by
        by_contra hc'
        apply hc
        intro i hi
        by_contra hne
        exact hc' ⟨i, hi, hne⟩
      obtain ⟨i, hi, hne⟩ := hex
      have hprod' : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase v,
          (if x k = y k then (1 : ℂ) else 0)) = 0 := by
        refine Finset.prod_eq_zero hi ?_
        rw [if_neg hne]
      rw [hprod', zero_mul]
      by_cases h0 : y = Function.update x v false
      · subst h0
        have hxi : x i = Function.update x v false i := by
          rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
        exact absurd hxi hne
      · rw [if_neg h0]
        by_cases h1 : y = Function.update x v true
        · subst h1
          have hxi : x i = Function.update x v true i := by
            rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
          exact absurd hxi hne
        · rw [if_neg h1, add_zero]
  calc ∑ y : Reg n, (∏ i ∈ (Finset.univ : Finset (Fin n)).erase v,
          (if x i = y i then (1 : ℂ) else 0)) * F y
      = ∑ y : Reg n, ((if y = Function.update x v false
            then F (Function.update x v false) else 0)
          + (if y = Function.update x v true
            then F (Function.update x v true) else 0)) :=
        Finset.sum_congr rfl fun y _ => hprod y
    _ = ∑ y : Reg n, (if y = Function.update x v false
            then F (Function.update x v false) else 0)
          + ∑ y : Reg n, (if y = Function.update x v true
            then F (Function.update x v true) else 0) :=
        Finset.sum_add_distrib
    _ = F (Function.update x v false) + F (Function.update x v true) := by
        rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp

private theorem hadamard_entry (a b : Bool) :
    Hadamard a b = (Real.sqrt 2 : ℂ)⁻¹ * (if a && b then -1 else 1) := rfl

private theorem wireH_mul_apply (v : Fin 4) (A : Matrix (Reg 4) (Fin 4) ℂ) (x : Reg 4) (j : Fin 4) :
    (rbWireH v * A) x j
      = (Real.sqrt 2 : ℂ)⁻¹ *
          ((if x v then -(1 : ℂ) else 1) * A (Function.update x v true) j
            + A (Function.update x v false) j) := by
  rw [Matrix.mul_apply, rbWireH, mbqcRegWireGate]
  simp only [Matrix.of_apply]
  have hrel : ∀ a b : Bool,
      relabelGate boolEquivFin2 Hadamard (boolEquivFin2 a) (boolEquivFin2 b) = Hadamard a b := by
    intro a b
    simp [relabelGate, boolEquivFin2]
  simp only [hrel, hadamard_entry]
  rw [show (∑ y : Reg 4,
        ((Real.sqrt 2 : ℂ)⁻¹ * (if x v && y v then -1 else 1))
          * (∏ i ∈ (Finset.univ : Finset (Fin 4)).erase v,
            (if x i = y i then (1 : ℂ) else 0)) * A y j)
      = ∑ y : Reg 4, (∏ i ∈ (Finset.univ : Finset (Fin 4)).erase v,
          (if x i = y i then (1 : ℂ) else 0))
          * (((Real.sqrt 2 : ℂ)⁻¹ * (if x v && y v then -1 else 1)) * A y j) from
        Finset.sum_congr rfl fun y _ => by ring]
  rw [sum_reg_erase_delta]
  simp only [Function.update_self]
  rcases hx : x v <;> simp_all <;> ring

private theorem proj_mul_apply (v : Fin 4) (b : Bool) (A : Matrix (Reg 4) (Fin 4) ℂ)
    (x : Reg 4) (j : Fin 4) :
    (rbProjGate v b * A) x j = (if x v = b then (1 : ℂ) else 0) * A x j := by
  rw [Matrix.mul_apply, rbProjGate, mbqcRegWireGate]
  simp only [Matrix.of_apply]
  have hrel : ∀ p q : Bool,
      relabelGate boolEquivFin2 (Projector ({b} : Finset Bool))
        (boolEquivFin2 p) (boolEquivFin2 q)
        = (if p = q ∧ p = b then (1 : ℂ) else 0) := by
    intro p q
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Projector,
      Matrix.diagonal_apply, boolEquivFin2]
    cases p <;> cases q <;> simp
  simp only [hrel]
  rw [show (∑ y : Reg 4, (if x v = y v ∧ x v = b then (1 : ℂ) else 0)
          * (∏ i ∈ (Finset.univ : Finset (Fin 4)).erase v,
            (if x i = y i then (1 : ℂ) else 0)) * A y j)
      = ∑ y : Reg 4, (∏ i ∈ (Finset.univ : Finset (Fin 4)).erase v,
          (if x i = y i then (1 : ℂ) else 0))
          * (((if x v = y v ∧ x v = b then (1 : ℂ) else 0)) * A y j) from
        Finset.sum_congr rfl fun y _ => by ring]
  rw [sum_reg_erase_delta]
  simp only [Function.update_self]
  have hxx : A x j = A (Function.update x v (x v)) j := by rw [Function.update_eq_self]
  rw [hxx]
  rcases hx : x v <;> rcases hb : b <;> simp_all

private theorem frame_entry (x : Reg 4) (j : Fin 4) :
    rbCnotFrame x j =
      (if x 0 = (bitVecEquiv 2).symm j 0 then (1 : ℂ) else 0) *
        (if x 1 = (bitVecEquiv 2).symm j 1 then (1 : ℂ) else 0) * (2 : ℂ)⁻¹ := by
  rw [rbCnotFrame]
  simp only [Matrix.of_apply]
  rw [Fin.prod_univ_four]
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← pow_two, sqrt2_sq]
  simp
  rw [h2]

private theorem pulse_entry (x y : Reg 4) :
    rbCnotPulse x y =
      if x = y then
        bitPhase (x 2) * bitPhase (x 0 && x 2) * bitPhase (x 1 && x 3) * bitPhase (x 2 && x 3)
      else 0 := by
  have h0 : incomingOdd rbCnotEdges 0 = false := by decide +kernel
  have h1 : incomingOdd rbCnotEdges 1 = false := by decide +kernel
  have h2 : incomingOdd rbCnotEdges 2 = true := by decide +kernel
  have h3 : incomingOdd rbCnotEdges 3 = false := by decide +kernel
  rw [rbCnotPulse, sourcePulse_eq_frame_cz, frameMatrix, czMatrix]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    rw [Finset.sum_eq_single x]
    · rw [Fin.prod_univ_four, h0, h1, h2, h3]
      simp [bitPhase, rbCnotEdges]
    · intro w _ hw
      simp [hw]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · rw [Finset.sum_eq_zero (fun w _ => by
      by_cases hxw : x = w
      · have hwy : w ≠ y := fun h => hxy (hxw.trans h)
        rw [if_pos hxw, if_neg hwy, mul_zero]
      · rw [if_neg hxw, zero_mul])]
    rw [if_neg hxy]

private theorem outframe_entry (z : Bool × Bool) (j' : Fin 4) (x : Reg 4) :
    rbCnotOutFrame z j' x =
      (if x 0 = z.1 then (1 : ℂ) else 0) * (if x 1 = z.2 then (1 : ℂ) else 0) *
        (if x 2 = (bitVecEquiv 2).symm j' 0 then (1 : ℂ) else 0) *
        (if x 3 = (bitVecEquiv 2).symm j' 1 then (1 : ℂ) else 0) := by
  rw [rbCnotOutFrame]
  simp only [Matrix.of_apply]
  ring

private theorem outframe_sum (z : Bool × Bool) (j' : Fin 4)
    (B : Matrix (Reg 4) (Fin 4) ℂ) (j : Fin 4) :
    (rbCnotOutFrame z * B) j' j
      = B ![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] j := by
  rw [Matrix.mul_apply]
  simp only [outframe_entry]
  rw [Finset.sum_eq_single ![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1]]
  · have h0 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 0
        = z.1 := rfl
    have h1 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 1
        = z.2 := rfl
    have h2 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 2
        = (bitVecEquiv 2).symm j' 0 := rfl
    have h3 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 3
        = (bitVecEquiv 2).symm j' 1 := rfl
    rw [h0, h1, h2, h3]
    simp
  · intro y _ hy
    by_cases hy0 : y 0 = z.1
    · by_cases hy1 : y 1 = z.2
      · by_cases hy2 : y 2 = (bitVecEquiv 2).symm j' 0
        · by_cases hy3 : y 3 = (bitVecEquiv 2).symm j' 1
          · exact absurd (funext fun k => by
              fin_cases k <;> simp [hy0, hy1, hy2, hy3]) hy
          · rw [if_neg hy3]
            ring
        · rw [if_neg hy2]
          ring
      · rw [if_neg hy1]
        ring
    · rw [if_neg hy0]
      ring
  · intro h
    exact absurd (Finset.mem_univ _) h

private noncomputable def cnotA0 : Matrix (Reg 4) (Fin 4) ℂ := rbCnotFrame

private noncomputable def cnotA1 : Matrix (Reg 4) (Fin 4) ℂ := rbWireH 0 * cnotA0

private noncomputable def cnotA2 : Matrix (Reg 4) (Fin 4) ℂ := rbCnotPulse * cnotA1

private noncomputable def cnotA3 : Matrix (Reg 4) (Fin 4) ℂ := rbWireH 1 * cnotA2

private noncomputable def cnotA4 : Matrix (Reg 4) (Fin 4) ℂ := rbWireH 0 * cnotA3

private noncomputable def cnotA5 (s : Bool × Bool) : Matrix (Reg 4) (Fin 4) ℂ :=
  rbProjGate 1 s.2 * cnotA4

private noncomputable def cnotA6 (s : Bool × Bool) : Matrix (Reg 4) (Fin 4) ℂ :=
  rbProjGate 0 s.1 * cnotA5 s

private noncomputable def cnotA7 (s : Bool × Bool) : Matrix (Reg 4) (Fin 4) ℂ :=
  rbWireH 3 * cnotA6 s

private theorem wireGate_mul_same (v : Fin 4) (U V : Operator 2) :
    mbqcRegWireGate v U * mbqcRegWireGate v V = mbqcRegWireGate v (U * V) := by
  rw [mbqcRegWireGate_eq, mbqcRegWireGate_eq, pauliProductDensity_mul]
  have h : (fun i : Fin 4 => (if i = v then U else 1) * (if i = v then V else 1))
      = (fun i : Fin 4 => if i = v then U * V else 1) := by
    funext i
    by_cases hi : i = v
    · subst hi
      simp
    · simp [hi]
  rw [h, mbqcRegWireGate_eq]

private theorem wireGate_one (v : Fin 4) :
    mbqcRegWireGate v (1 : Operator 2) = 1 := by
  rw [mbqcRegWireGate_eq]
  have h : (fun i : Fin 4 => if i = v then (1 : Operator 2) else 1)
      = (fun _ : Fin 4 => (1 : Operator 2)) := by
    funext i
    by_cases hi : i = v <;> simp [hi]
  rw [h, pauliProductDensity_one]

private theorem wireH1_sq : rbWireH 1 * rbWireH 1 = (1 : Matrix (Reg 4) (Reg 4) ℂ) := by
  rw [rbWireH, wireGate_mul_same, ← teleportRelabelGate_mul, hadamard_mul_self,
    teleportRelabelGate_one, wireGate_one]

private theorem drop_wireH1 (B : Matrix (Reg 4) (Fin 4) ℂ) :
    rbWireH 1 * (rbWireH 1 * B) = B := by
  rw [← Matrix.mul_assoc, wireH1_sq]
  exact Matrix.one_mul B

private theorem rbCnotKraus_split (s z : Bool × Bool) :
    rbCnotKraus s z = rbCnotOutFrame z * cnotA7 s := by
  rw [rbCnotKraus, cnotA7, cnotA6, cnotA5, cnotA4, cnotA3, cnotA2, cnotA1, cnotA0]
  simp only [Matrix.mul_assoc]
  rw [drop_wireH1]

private theorem s1_entry (x : Reg 4) (j : Fin 4) :
    cnotA1 x j = (Real.sqrt 2 : ℂ)⁻¹ *
      bitPhase (x 0 && (bitVecEquiv 2).symm j 0) *
        (if x 1 = (bitVecEquiv 2).symm j 1 then (1 : ℂ) else 0) * (2 : ℂ)⁻¹ := by
  rw [cnotA1, wireH_mul_apply, cnotA0]
  simp only [frame_entry]
  rcases hd0 : (bitVecEquiv 2).symm j 0
    <;> simp_all [bitPhase]

private theorem s2_entry (x : Reg 4) (j : Fin 4) :
    cnotA2 x j = bitPhase (x 2) * bitPhase (x 0 && x 2) * bitPhase (x 1 && x 3) *
      bitPhase (x 2 && x 3) *
        (Real.sqrt 2 : ℂ)⁻¹ * bitPhase (x 0 && (bitVecEquiv 2).symm j 0) *
          (if x 1 = (bitVecEquiv 2).symm j 1 then (1 : ℂ) else 0) * (2 : ℂ)⁻¹ := by
  rw [cnotA2, Matrix.mul_apply]
  simp only [pulse_entry]
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl, s1_entry]
    ring
  · intro y _ hy
    rw [if_neg (Ne.symm hy), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

private theorem s3_entry (x : Reg 4) (j : Fin 4) :
    cnotA3 x j = (Real.sqrt 2 : ℂ)⁻¹ * bitPhase (x 1 && (bitVecEquiv 2).symm j 1) *
      bitPhase (x 2) * bitPhase (x 0 && x 2) *
        bitPhase ((bitVecEquiv 2).symm j 1 && x 3) * bitPhase (x 2 && x 3) *
          (Real.sqrt 2 : ℂ)⁻¹ * bitPhase (x 0 && (bitVecEquiv 2).symm j 0) * (2 : ℂ)⁻¹ := by
  rw [cnotA3, wireH_mul_apply]
  simp only [s2_entry]
  have hu0 : ∀ b : Bool, Function.update x 1 b 0 = x 0 :=
    fun b => Function.update_of_ne (show (0 : Fin 4) ≠ 1 from by decide) b x
  have hu2 : ∀ b : Bool, Function.update x 1 b 2 = x 2 :=
    fun b => Function.update_of_ne (show (2 : Fin 4) ≠ 1 from by decide) b x
  have hu3 : ∀ b : Bool, Function.update x 1 b 3 = x 3 :=
    fun b => Function.update_of_ne (show (3 : Fin 4) ≠ 1 from by decide) b x
  simp only [hu0, hu2, hu3, Function.update_self]
  rcases hd0 : (bitVecEquiv 2).symm j 0 <;> rcases hd1 : (bitVecEquiv 2).symm j 1
    <;> rcases hx0 : x 0 <;> rcases hx1 : x 1 <;> rcases hx2 : x 2 <;> rcases hx3 : x 3
    <;> simp_all [bitPhase] <;> ring

private theorem s4_entry (x : Reg 4) (j : Fin 4) :
    cnotA4 x j = ((Real.sqrt 2 : ℂ)⁻¹) ^ 3 *
      (2 : ℂ)⁻¹ * bitPhase (x 1 && (bitVecEquiv 2).symm j 1) * bitPhase (x 2) *
        bitPhase ((bitVecEquiv 2).symm j 1 && x 3) * bitPhase (x 2 && x 3) *
          (1 + bitPhase (x 0) * bitPhase ((bitVecEquiv 2).symm j 0) * bitPhase (x 2)) := by
  rw [cnotA4, wireH_mul_apply]
  simp only [s3_entry]
  have hu1 : ∀ b : Bool, Function.update x 0 b 1 = x 1 :=
    fun b => Function.update_of_ne (show (1 : Fin 4) ≠ 0 from by decide) b x
  have hu2 : ∀ b : Bool, Function.update x 0 b 2 = x 2 :=
    fun b => Function.update_of_ne (show (2 : Fin 4) ≠ 0 from by decide) b x
  have hu3 : ∀ b : Bool, Function.update x 0 b 3 = x 3 :=
    fun b => Function.update_of_ne (show (3 : Fin 4) ≠ 0 from by decide) b x
  simp only [hu1, hu2, hu3, Function.update_self]
  rcases hd0 : (bitVecEquiv 2).symm j 0 <;> rcases hd1 : (bitVecEquiv 2).symm j 1
    <;> rcases hx0 : x 0 <;> rcases hx1 : x 1 <;> rcases hx2 : x 2 <;> rcases hx3 : x 3
    <;> simp_all [bitPhase] <;> ring

private theorem s5_entry (s : Bool × Bool) (x : Reg 4) (j : Fin 4) :
    cnotA5 s x j = (if x 1 = s.2 then (1 : ℂ) else 0) * cnotA4 x j := by
  rw [cnotA5, proj_mul_apply]

private theorem s6_entry (s : Bool × Bool) (x : Reg 4) (j : Fin 4) :
    cnotA6 s x j = (if x 0 = s.1 then (1 : ℂ) else 0) * (if x 1 = s.2 then (1 : ℂ) else 0) *
      cnotA4 x j := by
  rw [cnotA6, proj_mul_apply, s5_entry]
  ring

private theorem sqrt2_norm : ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 * (2 : ℂ)⁻¹ = ((2 : ℂ)⁻¹) ^ 3 := by
  have h : ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = ((2 : ℂ)⁻¹) ^ 2 := by
    calc ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = (((Real.sqrt 2 : ℂ)⁻¹) ^ 2) ^ 2 := by ring
      _ = (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) ^ 2 := by rw [inv_pow]
      _ = ((2 : ℂ)⁻¹) ^ 2 := by rw [sqrt2_sq]
  rw [h]
  norm_num

private theorem s7_entry (s : Bool × Bool) (x : Reg 4) (j : Fin 4) :
    cnotA7 s x j = (if x 0 = s.1 then (1 : ℂ) else 0) * (if x 1 = s.2 then (1 : ℂ) else 0) *
      ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 * (2 : ℂ)⁻¹ * bitPhase (x 1 && (bitVecEquiv 2).symm j 1) *
        bitPhase (x 2) *
          (1 + bitPhase (x 0) * bitPhase ((bitVecEquiv 2).symm j 0) * bitPhase (x 2)) *
            (1 + bitPhase (x 3) * bitPhase ((bitVecEquiv 2).symm j 1) * bitPhase (x 2)) := by
  rw [cnotA7, wireH_mul_apply]
  simp only [s6_entry, s4_entry]
  have hu0 : ∀ b : Bool, Function.update x 3 b 0 = x 0 :=
    fun b => Function.update_of_ne (show (0 : Fin 4) ≠ 3 from by decide) b x
  have hu1 : ∀ b : Bool, Function.update x 3 b 1 = x 1 :=
    fun b => Function.update_of_ne (show (1 : Fin 4) ≠ 3 from by decide) b x
  have hu2 : ∀ b : Bool, Function.update x 3 b 2 = x 2 :=
    fun b => Function.update_of_ne (show (2 : Fin 4) ≠ 3 from by decide) b x
  simp only [hu0, hu1, hu2, Function.update_self]
  rcases hd0 : (bitVecEquiv 2).symm j 0 <;> rcases hd1 : (bitVecEquiv 2).symm j 1
    <;> rcases hx0 : x 0 <;> rcases hx1 : x 1 <;> rcases hx2 : x 2 <;> rcases hx3 : x 3
    <;> rcases hs0 : s.1 <;> rcases hs1 : s.2 <;> simp_all [bitPhase] <;> ring

private theorem sqrt2_pow4 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = ((2 : ℂ)⁻¹) ^ 2 := by
  calc ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = (((Real.sqrt 2 : ℂ)⁻¹) ^ 2) ^ 2 := by ring
    _ = (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) ^ 2 := by rw [inv_pow]
    _ = ((2 : ℂ)⁻¹) ^ 2 := by rw [sqrt2_sq]

private theorem pauliX_entry (i j : Fin 2) :
    pauliX i j = if i = j then (0 : ℂ) else 1 := by
  fin_cases i <;> fin_cases j <;> simp [pauliX]

private theorem pauliZ_entry (i j : Fin 2) :
    pauliZ i j = if i = j then (if i = 0 then (1 : ℂ) else -1) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

private theorem bv2_symm_bit0 (k : Fin 4) :
    (bitVecEquiv 2).symm k 0 = (teleportOutcomeEquiv.symm k).1 := by
  fin_cases k <;> decide +kernel

private theorem bv2_symm_bit1 (k : Fin 4) :
    (bitVecEquiv 2).symm k 1 = (teleportOutcomeEquiv.symm k).2 := by
  fin_cases k <;> decide +kernel

private theorem bv2_cnotFlip0 (j : Fin 4) :
    (bitVecEquiv 2).symm (teleportOutcomeEquiv (cnotFlip (teleportOutcomeEquiv.symm j))) 0
      = (bitVecEquiv 2).symm j 0 := by
  fin_cases j <;> decide +kernel

private theorem bv2_cnotFlip1 (j : Fin 4) :
    (bitVecEquiv 2).symm (teleportOutcomeEquiv (cnotFlip (teleportOutcomeEquiv.symm j))) 1
      = ((bitVecEquiv 2).symm j 1 ^^ (bitVecEquiv 2).symm j 0) := by
  fin_cases j <;> decide +kernel

private theorem rbCnotOp_apply (k j : Fin 4) :
    rbCnotOp k j
      = if k = teleportOutcomeEquiv (cnotFlip (teleportOutcomeEquiv.symm j)) then (1 : ℂ) else 0 := by
  simp only [rbCnotOp, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, CNOT, permMatrix,
    Matrix.of_apply]
  have h : (teleportOutcomeEquiv.symm k = cnotFlip (teleportOutcomeEquiv.symm j))
      ↔ (k = teleportOutcomeEquiv (cnotFlip (teleportOutcomeEquiv.symm j))) :=
    Equiv.symm_apply_eq teleportOutcomeEquiv
  simp only [h]

private theorem target_entry (s : Bool × Bool) (j' j : Fin 4) :
    (relabelGate (bitVecEquiv 2) (pauliProductDensity (clause3Kappa s)) * rbCnotOp) j' j
      = clause3Kappa s 0 (boolEquivFin2 ((bitVecEquiv 2).symm j' 0))
          (boolEquivFin2 ((bitVecEquiv 2).symm j 0)) *
        clause3Kappa s 1 (boolEquivFin2 ((bitVecEquiv 2).symm j' 1))
          (boolEquivFin2 ((bitVecEquiv 2).symm j 1 ^^ (bitVecEquiv 2).symm j 0)) := by
  rw [Matrix.mul_apply]
  have hsingle : (∑ k : Fin 4,
      relabelGate (bitVecEquiv 2) (pauliProductDensity (clause3Kappa s)) j' k * rbCnotOp k j)
      = relabelGate (bitVecEquiv 2) (pauliProductDensity (clause3Kappa s)) j'
          (teleportOutcomeEquiv (cnotFlip (teleportOutcomeEquiv.symm j))) := by
    rw [Finset.sum_eq_single (teleportOutcomeEquiv (cnotFlip (teleportOutcomeEquiv.symm j)))]
    · rw [rbCnotOp_apply, if_pos rfl, mul_one]
    · intro k _ hk
      rw [rbCnotOp_apply, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine hsingle.trans ?_
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, pauliProductDensity,
    Matrix.of_apply]
  rw [Fin.prod_univ_two]
  rw [bv2_cnotFlip0, bv2_cnotFlip1]

private theorem rbCnotKraus_entry (s z : Bool × Bool) (j' j : Fin 4) :
    rbCnotKraus s z j' j
      = (if z = s then (if s.1 then -(2 : ℂ)⁻¹ else (2 : ℂ)⁻¹) else 0) *
          (clause3Kappa s 0 (boolEquivFin2 ((bitVecEquiv 2).symm j' 0))
              (boolEquivFin2 ((bitVecEquiv 2).symm j 0)) *
            clause3Kappa s 1 (boolEquivFin2 ((bitVecEquiv 2).symm j' 1))
              (boolEquivFin2 ((bitVecEquiv 2).symm j 1 ^^ (bitVecEquiv 2).symm j 0))) := by
  rw [rbCnotKraus_split, outframe_sum]
  have e0 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 0
      = z.1 := rfl
  have e1 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 1
      = z.2 := rfl
  have e2 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 2
      = (bitVecEquiv 2).symm j' 0 := rfl
  have e3 : (![z.1, z.2, (bitVecEquiv 2).symm j' 0, (bitVecEquiv 2).symm j' 1] : Reg 4) 3
      = (bitVecEquiv 2).symm j' 1 := rfl
  simp only [s7_entry, e0, e1, e2, e3]
  rw [sqrt2_pow4]
  rcases hz1 : z.1 <;> rcases hz2 : z.2 <;> rcases hs1 : s.1 <;> rcases hs2 : s.2
    <;> rcases hd0 : (bitVecEquiv 2).symm j 0 <;> rcases hd1 : (bitVecEquiv 2).symm j 1
    <;> rcases hc0 : (bitVecEquiv 2).symm j' 0 <;> rcases hc1 : (bitVecEquiv 2).symm j' 1
    <;> simp_all [bitPhase, clause3Kappa, pauliX_entry, pauliZ_entry, boolEquivFin2,
      Matrix.mul_apply, Matrix.one_apply, Prod.ext_iff]
    <;> norm_num

private theorem rbCnotKraus_smul (s z : Bool × Bool) :
    rbCnotKraus s z
      = (if z = s then (if s.1 then -(2 : ℂ)⁻¹ else (2 : ℂ)⁻¹) else 0) •
          (relabelGate (bitVecEquiv 2) (pauliProductDensity (clause3Kappa s)) * rbCnotOp) := by
  ext j' j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [rbCnotKraus_entry, target_entry]

private theorem conjBranch_smul {D : ℕ} (c : ℂ) (M ρ : Operator D) :
    conjBranch (c • M) ρ = (c * star c) • (M * ρ * M.conjTranspose) := by
  simp only [conjBranch_apply, Matrix.conjTranspose_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]

private theorem inv2_star : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [Complex.star_def, Complex.conj_inv, Complex.conj_ofNat]

private theorem cnotScalar_norm (s : Bool × Bool) :
    ((if s.1 then -(2 : ℂ)⁻¹ else (2 : ℂ)⁻¹)
        * star (if s.1 then -(2 : ℂ)⁻¹ else (2 : ℂ)⁻¹))
      = ((2 : ℂ)⁻¹) ^ 2 := by
  by_cases hs : s.1 = true
  · rw [if_pos hs, star_neg, inv2_star]
    ring
  · rw [if_neg hs, inv2_star]
    ring

theorem clause3_clause2 :
    ∃ κ : (Bool × Bool) → Fin 2 → Operator 2,
      (∀ s : Bool × Bool, ∀ v : Fin 2, MbqcPauliWire (κ s v)) ∧
      ∀ (ρ : Operator 4) (s : Bool × Bool),
        rbCnotBranch s ρ
          = ((2 : ℂ)⁻¹) ^ 2 •
              ((relabelGate (bitVecEquiv 2) (pauliProductDensity (κ s)) * rbCnotOp) * ρ
                * (relabelGate (bitVecEquiv 2) (pauliProductDensity (κ s)) * rbCnotOp).conjTranspose) := by
  refine ⟨clause3Kappa, clause3Kappa_pauli, ?_⟩
  intro ρ s
  rw [rbCnotBranch, rbCnotBranchMap, LinearMap.sum_apply]
  rw [Finset.sum_eq_single s]
  · rw [rbCnotKraus_smul, if_pos rfl, conjBranch_smul, cnotScalar_norm]
  · intro z _ hz
    rw [rbCnotKraus_smul, if_neg hz, zero_smul]
    simp
  · intro h
    exact absurd (Finset.mem_univ s) h
end Qatlib.Concepts.MbqcFlow.FlowDecision

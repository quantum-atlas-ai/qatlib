/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators ComplexConjugate

def algorithm1Step2 (p : ℕ) [Fact p.Prime] [NeZero p] (s : ZMod p) : ZMod p → ℂ :=
  modularFourier p (legendreSetupState p s)

def algorithm1Step3 (p : ℕ) [Fact p.Prime] [NeZero p] (s : ZMod p) : ZMod p → ℂ :=
  fun y => ((quadCharZMod p y : ℤ) : ℂ) * algorithm1Step2 p s y

def algorithm1FinalState (p : ℕ) [Fact p.Prime] [NeZero p] (s : ZMod p) : ZMod p → ℂ :=
  modularFourierInv p (algorithm1Step3 p s)

theorem theorem1_queries : algorithm1Queries = 2 := rfl

theorem theorem1_polynomialTime : PolynomiallyBounded (fun n => n ^ 3) :=
  ⟨1, 3, fun n => by rw [one_mul]; exact Nat.pow_le_pow_left (Nat.le_succ n) 3⟩

theorem legendre_amplitude (p : ℕ) [Fact p.Prime] [NeZero p] (hp : p ≠ 2) (s y : ZMod p) :
    ∑ x : ZMod p, ((quadCharZMod p (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y)
      = legendreGaussSum p * ZMod.stdAddChar (-(s * y)) * ((quadCharZMod p y : ℤ) : ℂ) := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  have hshift :
      (∑ x : ZMod p, ((quadCharZMod p (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y))
      = ZMod.stdAddChar (-(s * y)) *
          ∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (fun u : ZMod p => u + s) (Equiv.addRight s).bijective
      (fun x => ((quadCharZMod p (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y))
      (fun u => ZMod.stdAddChar (-(s * y)) *
        (((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y))) ?_
    intro u
    change ((quadCharZMod p (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)
        = ZMod.stdAddChar (-(s * y)) *
            (((quadCharZMod p (u + s) : ℤ) : ℂ) * ZMod.stdAddChar ((u + s) * y))
    rw [show (u + s) * y = u * y + s * y by ring, AddChar.map_add_eq_mul]
    have hneg : ZMod.stdAddChar (-(s * y)) * ZMod.stdAddChar (s * y) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc
      ((quadCharZMod p (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)
          = (((quadCharZMod p (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)) * 1 := by ring
      _ = (((quadCharZMod p (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)) *
            (ZMod.stdAddChar (-(s * y)) * ZMod.stdAddChar (s * y)) := by rw [hneg]
      _ = ZMod.stdAddChar (-(s * y)) *
            (((quadCharZMod p (u + s) : ℤ) : ℂ) *
              (ZMod.stdAddChar (u * y) * ZMod.stdAddChar (s * y))) := by ring
  by_cases hy : y = 0
  · subst hy
    have hS0 : (∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * 0)) = 0 := by
      have hcast : (∑ u : ZMod p, quadraticChar (ZMod p) u) = 0 :=
        quadraticChar_sum_zero hchar
      rw [show (∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * 0))
            = ∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) from by
        apply Finset.sum_congr rfl
        intro u _
        rw [mul_zero, AddChar.map_zero_eq_one, mul_one]]
      rw [← Int.cast_sum]
      simp only [quadCharZMod]
      exact_mod_cast hcast
    rw [hshift, hS0, mul_zero]
    simp [quadCharZMod]
  · have hy0 : y ≠ 0 := hy
    have hchi_ne : quadraticChar (ZMod p) y ≠ 0 := by
      intro h
      exact hy0 (quadraticChar_eq_zero_iff.mp h)
    have hinv : quadraticChar (ZMod p) y⁻¹ = quadraticChar (ZMod p) y := by
      have h1 : quadraticChar (ZMod p) y⁻¹ * quadraticChar (ZMod p) y = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hy0, map_one]
      have h2 : quadraticChar (ZMod p) y * quadraticChar (ZMod p) y = 1 := by
        have h := quadraticChar_sq_one hy0
        simpa [pow_two] using h
      exact mul_right_cancel₀ hchi_ne (h1.trans h2.symm)
    have hS : (∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y))
        = ((quadCharZMod p y : ℤ) : ℂ) * legendreGaussSum p := by
      have hreindex :
          (∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y))
          = ∑ v : ZMod p,
              ((quadCharZMod p (y⁻¹ * v) : ℤ) : ℂ) * ZMod.stdAddChar v := by
        refine Fintype.sum_bijective (fun u : ZMod p => u * y)
          (Equiv.mulRight₀ y hy0).bijective
          (fun u => ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y))
          (fun v => ((quadCharZMod p (y⁻¹ * v) : ℤ) : ℂ) * ZMod.stdAddChar v) ?_
        intro u
        show ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y)
            = ((quadCharZMod p (y⁻¹ * (u * y)) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)
        rw [show y⁻¹ * (u * y) = u by field_simp]
      calc
        (∑ u : ZMod p, ((quadCharZMod p u : ℤ) : ℂ) * ZMod.stdAddChar (u * y))
            = ∑ v : ZMod p,
                ((quadCharZMod p (y⁻¹ * v) : ℤ) : ℂ) * ZMod.stdAddChar v := hreindex
        _ = ∑ v : ZMod p,
                (((quadCharZMod p y⁻¹ : ℤ) : ℂ) * ((quadCharZMod p v : ℤ) : ℂ)) *
                  ZMod.stdAddChar v := by
              apply Finset.sum_congr rfl
              intro v _
              rw [show quadCharZMod p (y⁻¹ * v)
                    = quadraticChar (ZMod p) (y⁻¹ * v) from rfl, map_mul]
              simp only [quadCharZMod]
              push_cast
              ring
        _ = ((quadCharZMod p y⁻¹ : ℤ) : ℂ) *
              ∑ v : ZMod p, ((quadCharZMod p v : ℤ) : ℂ) * ZMod.stdAddChar v := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v _
              ring
        _ = ((quadCharZMod p y : ℤ) : ℂ) *
              ∑ v : ZMod p, ((quadCharZMod p v : ℤ) : ℂ) * ZMod.stdAddChar v := by
              rw [show quadCharZMod p y⁻¹ = quadraticChar (ZMod p) y⁻¹ from rfl,
                show quadCharZMod p y = quadraticChar (ZMod p) y from rfl, hinv]
        _ = ((quadCharZMod p y : ℤ) : ℂ) * legendreGaussSum p := rfl
    rw [hshift, hS]
    ring

theorem norm_legendreGaussSum (p : ℕ) [Fact p.Prime] [NeZero p] (hp : p ≠ 2) :
    ‖legendreGaussSum p‖ ^ 2 = (p : ℝ) := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  let χ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hinj : Function.Injective (Int.castRingHom ℂ) := by
    simpa using (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℂ))
  have hχne : χ ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hinj]
    exact quadraticChar_ne_one hchar
  have hcard : gaussSum χ (ZMod.stdAddChar) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ = (p : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card (χ := χ) hχne
      (ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) (ZMod.isPrimitive_stdAddChar p)
    simpa [ZMod.card] using h
  have hG : gaussSum χ (ZMod.stdAddChar) = legendreGaussSum p := by
    unfold gaussSum legendreGaussSum
    apply Finset.sum_congr rfl
    intro a _
    simp [χ, quadCharZMod]
  have hmul : legendreGaussSum p * star (legendreGaussSum p) = (p : ℂ) := by
    rw [show star (legendreGaussSum p) = gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ from by
      rw [← hG]; exact star_gaussSum_eq χ (ZMod.stdAddChar)]
    rw [← hG]
    exact hcard
  have hstarconj : star (legendreGaussSum p) = conj (legendreGaussSum p) := by
    rw [Complex.star_def]
  rw [hstarconj] at hmul
  rw [Complex.mul_conj] at hmul
  have h3 : Complex.normSq (legendreGaussSum p) = (p : ℝ) := by
    have hre := congrArg Complex.re hmul
    simpa using hre
  rw [Complex.normSq_eq_norm_sq] at h3
  exact h3

theorem theorem1_successProbability (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp : p ≠ 2) (s : ZMod p) :
    ‖algorithm1FinalState p s (-s)‖ ^ 2 = ((p : ℝ) - 1) / (p : ℝ) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hspos : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1pos : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hsp : (Real.sqrt (p:ℝ))^2 = (p:ℝ) := Real.sq_sqrt hspos.le
  have hsq : (Real.sqrt ((p:ℝ)-1))^2 = ((p:ℝ)-1) := Real.sq_sqrt hp1pos.le
  have hspnz : ((Real.sqrt (p:ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hspos).ne'
  have hpm1nz : ((Real.sqrt ((p:ℝ)-1) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hp1pos).ne'

  have hstep2 : ∀ y : ZMod p, algorithm1Step2 p s y
      = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
          (legendreGaussSum p * ZMod.stdAddChar (-(s * y)) *
            ((quadCharZMod p y : ℤ) : ℂ)) := by
    intro y
    unfold algorithm1Step2 modularFourier legendreSetupState
    rw [show (∑ x : ZMod p,
          ((quadCharZMod p (x + s) : ℤ) : ℂ) * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
            ZMod.stdAddChar (x * y))
        = ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
            ∑ x : ZMod p,
              ((quadCharZMod p (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring]
    rw [legendre_amplitude p hp s y]
    ring

  have hstep3 : ∀ y : ZMod p, algorithm1Step3 p s y
      = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
          legendreGaussSum p *
            (ZMod.stdAddChar (-(s * y)) * (((quadCharZMod p y : ℤ) : ℂ))^2) := by
    intro y
    unfold algorithm1Step3
    rw [hstep2 y]
    ring

  have hsum_sq :
      (∑ y : ZMod p, (((quadCharZMod p y : ℤ) : ℂ))^2) = (p:ℂ) - 1 := by
    have hf0 : (((quadCharZMod p (0 : ZMod p) : ℤ) : ℂ))^2 = 0 := by
      simp [quadCharZMod]
    have hfne : ∀ y : ZMod p, y ≠ 0 →
        (((quadCharZMod p y : ℤ) : ℂ))^2 = 1 := by
      intro y hy
      have h : quadraticChar (ZMod p) y ^ 2 = 1 := quadraticChar_sq_one hy
      have hcast : ((quadraticChar (ZMod p) y : ℤ) : ℂ)^2 = 1 := by
        rw [← Int.cast_pow, h]
        norm_num
      simpa [quadCharZMod] using hcast
    rw [← Finset.sum_erase Finset.univ (f := fun y : ZMod p => (((quadCharZMod p y : ℤ) : ℂ))^2) (a := (0 : ZMod p)) hf0]
    rw [Finset.sum_congr rfl (fun y hy => hfne y (Finset.ne_of_mem_erase hy))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    simp [ZMod.card, Nat.cast_sub (by omega : 1 ≤ p)]

  have hfinal : algorithm1FinalState p s (-s)
      = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt (p:ℝ) : ℂ))⁻¹ *
          ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ * legendreGaussSum p * ((p:ℂ) - 1) := by
    unfold algorithm1FinalState modularFourierInv
    simp only [hstep3]
    have hterm : ∀ x : ZMod p,
        ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
          legendreGaussSum p *
            (ZMod.stdAddChar (-(s * x)) * (((quadCharZMod p x : ℤ) : ℂ))^2) *
        ZMod.stdAddChar (-(x * -s))
        = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
          legendreGaussSum p * (((quadCharZMod p x : ℤ) : ℂ))^2 := by
      intro x
      rw [show -(x * -s) = s * x by ring]
      have hpos : ZMod.stdAddChar (-(s * x)) * ZMod.stdAddChar (s * x) = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      calc
        ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
          legendreGaussSum p *
            (ZMod.stdAddChar (-(s * x)) * (((quadCharZMod p x : ℤ) : ℂ))^2) *
        ZMod.stdAddChar (s * x)
          = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
              legendreGaussSum p * (((quadCharZMod p x : ℤ) : ℂ))^2 *
                (ZMod.stdAddChar (-(s * x)) * ZMod.stdAddChar (s * x)) := by ring
        _ = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
              legendreGaussSum p * (((quadCharZMod p x : ℤ) : ℂ))^2 := by
            rw [hpos]; ring
    have hsum1 : (∑ x : ZMod p,
        ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
          legendreGaussSum p *
            (ZMod.stdAddChar (-(s * x)) * (((quadCharZMod p x : ℤ) : ℂ))^2) *
        ZMod.stdAddChar (-(x * -s)))
        = ∑ x : ZMod p, ((Real.sqrt (p:ℝ) : ℂ))⁻¹ *
            ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ * legendreGaussSum p *
              (((quadCharZMod p x : ℤ) : ℂ))^2 :=
      Finset.sum_congr rfl (fun x _ => hterm x)
    have hfac : (∑ x : ZMod p, ((Real.sqrt (p:ℝ) : ℂ))⁻¹ *
            ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ * legendreGaussSum p *
              (((quadCharZMod p x : ℤ) : ℂ))^2)
        = ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt ((p:ℝ)-1) : ℂ))⁻¹ *
            legendreGaussSum p * (∑ x : ZMod p, (((quadCharZMod p x : ℤ) : ℂ))^2) := by
      rw [Finset.mul_sum]
    rw [hsum1]
    rw [hfac]
    rw [hsum_sq]
    ac_rfl

  have hfinal2 : algorithm1FinalState p s (-s)
      = legendreGaussSum p * (Real.sqrt ((p:ℝ)-1) : ℂ) / (p:ℂ) := by
    rw [hfinal]
    have hspc : ((Real.sqrt (p:ℝ) : ℂ))^2 = (p:ℂ) := by
      rw [← Complex.ofReal_pow, hsp, Complex.ofReal_natCast]
    have hsqc : ((Real.sqrt ((p:ℝ)-1) : ℂ))^2 = ((p:ℂ)-1) := by
      rw [← Complex.ofReal_pow, hsq]
      norm_num
    have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hAA : ((Real.sqrt (p:ℝ) : ℂ))⁻¹ * ((Real.sqrt (p:ℝ) : ℂ))⁻¹ = ((p:ℂ))⁻¹ := by
      rw [← hspc, pow_two, mul_inv]
    rw [hAA]
    field_simp
    rw [hsqc]
    ring
  rw [hfinal2, norm_div, norm_mul]
  have hsqrtnorm : ‖(Real.sqrt ((p:ℝ)-1) : ℂ)‖ = Real.sqrt ((p:ℝ)-1) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (Real.sqrt_pos.mpr hp1pos)
  have hpnorm : ‖(p:ℂ)‖ = (p:ℝ) := by
    rw [Complex.norm_natCast]
  rw [hsqrtnorm, hpnorm]
  have hnormG := norm_legendreGaussSum p hp
  rw [div_pow, mul_pow, hnormG, hsq]
  have hpne : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

theorem theorem1_shiftedLegendre_solved (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp : p ≠ 2) :
    algorithm1Queries = 2 ∧
      PolynomiallyBounded (fun n => n ^ 3) ∧
      ∀ s : ZMod p, ‖algorithm1FinalState p s (-s)‖ ^ 2 = ((p : ℝ) - 1) / (p : ℝ) :=
  ⟨theorem1_queries, theorem1_polynomialTime,
    fun s => theorem1_successProbability p hp s⟩

theorem theorem1_failureProbability (p : ℕ) [Fact p.Prime] [NeZero p] (_hp : p ≠ 2) :
    1 - ((p : ℝ) - 1) / (p : ℝ) = 1 / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp
  ring

end Qatlib.Papers.QuadChar00.MainResults

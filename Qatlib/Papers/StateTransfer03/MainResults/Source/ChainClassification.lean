/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Defs
import Mathlib.NumberTheory.Niven
set_option warningAsError false

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

theorem cos_sum_range (N : ℕ) (hN : 0 < N) :
    (∑ i ∈ Finset.range N, Real.cos (2 * Real.pi * ((i : ℝ) + 1) / ((N : ℝ) + 1))) = -1 := by
  set a : ℝ := 2 * Real.pi / ((N : ℝ) + 1) with ha
  set g : ℕ → ℝ := fun i => Real.sin (((i : ℝ) + 1 / 2) * a) with hg
  have ha2 : a / 2 = Real.pi / ((N : ℝ) + 1) := by rw [ha]; field_simp
  have hsin : 0 < Real.sin (a / 2) := by
    rw [ha2]
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    refine div_lt_self Real.pi_pos ?_
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hterm : ∀ i : ℕ, 2 * Real.sin (a / 2) * Real.cos (((i : ℝ) + 1) * a) = g (i + 1) - g i := by
    intro i
    simp only [g]
    have h1 : ((↑(i + 1) + 1 / 2 : ℝ) * a) = ((i : ℝ) + 1) * a + a / 2 := by
      push_cast
      ring
    have h2 : ((↑i + 1 / 2 : ℝ) * a) = ((i : ℝ) + 1) * a - a / 2 := by
      ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  have hgN : g N = -Real.sin (Real.pi / ((N : ℝ) + 1)) := by
    simp only [g]
    have hv : (((N : ℝ)) + 1 / 2) * a = 2 * Real.pi - Real.pi / ((N : ℝ) + 1) := by
      rw [ha]
      field_simp
      ring
    rw [hv, Real.sin_two_pi_sub]
  have hg0 : g 0 = Real.sin (Real.pi / ((N : ℝ) + 1)) := by
    simp only [g]
    norm_num
    rw [show (1 / 2 : ℝ) * a = a / 2 by ring, ha2]
  have hmain : (∑ i ∈ Finset.range N,
        2 * Real.sin (a / 2) * Real.cos (((i : ℝ) + 1) * a)) = g N - g 0 := by
    rw [show (∑ i ∈ Finset.range N, 2 * Real.sin (a / 2) * Real.cos (((i : ℝ) + 1) * a))
        = ∑ i ∈ Finset.range N, (g (i + 1) - g i) from
      Finset.sum_congr rfl (fun i _ => hterm i)]
    exact Finset.sum_range_sub g N
  calc (∑ i ∈ Finset.range N, Real.cos (2 * Real.pi * ((i : ℝ) + 1) / ((N : ℝ) + 1)))
      = ∑ i ∈ Finset.range N, Real.cos (((i : ℝ) + 1) * a) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        congr 1
        rw [ha]
        field_simp
    _ = (1 / (2 * Real.sin (a / 2))) *
          ∑ i ∈ Finset.range N, (2 * Real.sin (a / 2) * Real.cos (((i : ℝ) + 1) * a)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        field_simp
    _ = (1 / (2 * Real.sin (a / 2))) * (g N - g 0) := by rw [hmain]
    _ = -1 := by
        rw [hgN, hg0, ha2]
        have hpos : 0 < Real.sin (Real.pi / ((N : ℝ) + 1)) := by
          refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
          refine div_lt_self Real.pi_pos ?_
          have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        field_simp
        ring

theorem sin_sq_sum_range (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin N, (Real.sin (((i.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1))) ^ 2)
      = ((N : ℝ) + 1) / 2 := by
  have hsin2 : ∀ x : ℝ, Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
    intro x
    have h1 := Real.sin_sq_add_cos_sq x
    have h2 := Real.cos_two_mul x
    linarith
  have hcos' : (∑ i ∈ Finset.range N,
      Real.cos (2 * ((i : ℝ) + 1) * (Real.pi / ((N : ℝ) + 1)))) = -1 := by
    rw [← cos_sum_range N hN]
    refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    ring
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (Real.sin (((i : ℝ) + 1) * Real.pi / ((N : ℝ) + 1))) ^ 2)]
  simp only [hsin2]
  have hsplit : (∑ i ∈ Finset.range N,
        (1 - Real.cos (2 * (((i : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)))) / 2)
      = ((N : ℝ) - (∑ i ∈ Finset.range N,
          Real.cos (2 * (((i : ℝ) + 1) * Real.pi / ((N : ℝ) + 1))))) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsplit]
  have hcos'' : (∑ i ∈ Finset.range N,
      Real.cos (2 * (((i : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)))) = -1 := by
    rw [← hcos']
    refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    ring
  rw [hcos'']
  ring

theorem pathWeight_abs (N : ℕ) (hN : 0 < N) (k : Fin N) :
    |pathWeight N k| =
      (2 / ((N : ℝ) + 1)) *
        (Real.sin (((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1))) ^ 2 := by
  set n : ℕ := k.val + 1 with hn
  have hncast : ((k.val : ℝ) + 1) = (n : ℝ) := by
    rw [hn]; push_cast; ring
  set θ : ℝ := (n : ℝ) * Real.pi / ((N : ℝ) + 1) with hθ
  have hθ0 : 0 < θ := by
    rw [hθ]
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.succ_pos k.val
    positivity
  have hθπ : θ < Real.pi := by
    rw [hθ]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hnN : (n : ℝ) ≤ (N : ℝ) := by
      have : n ≤ N := by omega
      exact_mod_cast this
    nlinarith [Real.pi_pos]
  have hsinθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le
  have harg1 : ((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1) = θ := by
    rw [hθ, hncast]
  have harg2 : ((k.val : ℝ) + 1) * (N : ℝ) * Real.pi / ((N : ℝ) + 1) =
      (n : ℝ) * Real.pi - θ := by
    rw [hθ, hncast]
    field_simp
    ring
  have hsinψ : Real.sin (((k.val : ℝ) + 1) * (N : ℝ) * Real.pi / ((N : ℝ) + 1)) =
      -((-1) ^ n * Real.sin θ) := by
    rw [harg2, Real.sin_nat_mul_pi_sub]
  unfold pathWeight
  rw [harg1, hsinψ]
  have hfac : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hfac, abs_of_nonneg hsinθ]
  have h2 : |(-((-1 : ℝ) ^ n * Real.sin θ))| = Real.sin θ := by
    rw [abs_neg, abs_mul]
    rw [show |(-1 : ℝ) ^ n| = 1 by rw [abs_pow]; norm_num, one_mul,
      abs_of_nonneg hsinθ]
  rw [h2]
  ring

theorem pathWeight_ne_zero (N : ℕ) (hN : 0 < N) (k : Fin N) :
    pathWeight N k ≠ 0 := by
  intro hp
  have habs := pathWeight_abs N hN k
  rw [hp, abs_zero] at habs
  have hfac : (2 / ((N : ℝ) + 1)) ≠ 0 := by positivity
  have hs2 : (Real.sin (((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1))) ^ 2 = 0 := by
    rcases mul_eq_zero.mp habs.symm with h | h
    · exact absurd h hfac
    · exact h
  have hs : Real.sin (((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 0 :=
    sq_eq_zero_iff.mp hs2
  have hpos : 0 < Real.sin (((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · have : (0 : ℝ) < ((k.val : ℝ) + 1) := by positivity
      positivity
    · have hnN : ((k.val : ℝ) + 1) ≤ (N : ℝ) := by
        have : k.val + 1 ≤ N := by omega
        exact_mod_cast this
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith [Real.pi_pos]
  linarith

theorem pathWeight_norm_sum (N : ℕ) (hN : 0 < N) :
    (∑ k : Fin N, ‖(pathWeight N k : ℂ)‖) = 1 := by
  have hterm : ∀ k : Fin N, ‖(pathWeight N k : ℂ)‖ = |pathWeight N k| := by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hterm, pathWeight_abs N hN]
  rw [← Finset.mul_sum]
  rw [sin_sq_sum_range N hN]
  field_simp

theorem sameRay_sum_of_norm_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, w i ≠ 0)
    (h : ‖∑ i ∈ s, w i‖ = ∑ i ∈ s, ‖w i‖) :
    ∀ i ∈ s, SameRay ℝ (w i) (∑ j ∈ s, w j) := by
  induction s using Finset.induction with
  | empty => intro i hi; simp at hi
  | insert b s hb ih =>
      have h' : ‖w b + ∑ x ∈ s, w x‖ = ‖w b‖ + ∑ x ∈ s, ‖w x‖ := by
        simpa only [Finset.sum_insert hb] using h
      have hsplit : ‖w b + ∑ x ∈ s, w x‖ = ‖w b‖ + ‖∑ x ∈ s, w x‖ := by
        have h1 : (‖w b + ∑ x ∈ s, w x‖ : ℝ) ≤ ‖w b‖ + ‖∑ x ∈ s, w x‖ := norm_add_le _ _
        have h2 : ‖∑ x ∈ s, w x‖ ≤ ∑ x ∈ s, ‖w x‖ := norm_sum_le _ _
        linarith
      have hbT : ‖∑ x ∈ s, w x‖ = ∑ x ∈ s, ‖w x‖ := by
        have h1 : (‖w b + ∑ x ∈ s, w x‖ : ℝ) ≤ ‖w b‖ + ‖∑ x ∈ s, w x‖ := norm_add_le _ _
        have h2 : ‖∑ x ∈ s, w x‖ ≤ ∑ x ∈ s, ‖w x‖ := norm_sum_le _ _
        linarith
      have hwa : SameRay ℝ (w b) (∑ x ∈ s, w x) := by
        rcases Complex.norm_add_eq_iff.mp hsplit with h0 | h0 | h0
        · exact absurd h0 (hw b (Finset.mem_insert_self b s))
        · rw [h0]; exact SameRay.zero_right _
        · exact Complex.sameRay_of_arg_eq h0
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with hia | hi
      · rw [hia]
        rw [Finset.sum_insert hb]
        exact SameRay.add_right SameRay.rfl hwa
      · have hbne : (∑ x ∈ s, w x) ≠ 0 := by
          intro h0
          have hnorm : ‖∑ x ∈ s, w x‖ = 0 := by rw [h0]; simp
          have hsum0 : ∑ x ∈ s, ‖w x‖ = 0 := by rw [← hbT]; exact hnorm
          have hzi : ‖w i‖ = 0 := (Finset.sum_eq_zero_iff_of_nonneg
            (fun x _ => norm_nonneg _)).mp hsum0 i hi
          exact hw i (Finset.mem_insert_of_mem hi) (norm_eq_zero.mp hzi)
        have hwi : SameRay ℝ (w i) (∑ x ∈ s, w x) :=
          ih (fun x hx => hw x (Finset.mem_insert_of_mem hx)) hbT i hi
        have hbi : SameRay ℝ (w i) (w b) :=
          SameRay.trans hwi (SameRay.symm hwa) (fun h0 => absurd h0 hbne)
        rw [Finset.sum_insert hb]
        exact SameRay.add_right hbi hwi

theorem sameRay_pairwise {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, w i ≠ 0)
    (h : ‖∑ i ∈ s, w i‖ = ∑ i ∈ s, ‖w i‖)
    (hT : (∑ i ∈ s, w i) ≠ 0) :
    ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (w i) (w j) := by
  intro i hi j hj
  exact SameRay.trans (sameRay_sum_of_norm_eq s w hw h i hi)
    (SameRay.symm (sameRay_sum_of_norm_eq s w hw h j hj)) (fun h0 => absurd h0 hT)

theorem expI_real (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [mul_comm Complex.I (x : ℂ)]
  simpa [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.exp_mul_I (x : ℂ)

theorem phase_ne_zero' (E t : ℝ) : phase E t ≠ 0 := by
  unfold phase
  exact Complex.exp_ne_zero _

theorem phase_mul_exp (E F t : ℝ) :
    phase E t * Complex.exp (Complex.I * ((t : ℂ) * (F : ℂ))) =
      Complex.exp (Complex.I * (((F - E) * t : ℝ) : ℂ)) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem im_real_mul_expI (a x : ℝ) :
    (↑a * Complex.exp (Complex.I * (x : ℂ)) : ℂ).im = a * Real.sin x := by
  rw [expI_real]
  simp [Complex.mul_im, Complex.mul_re, Complex.sin_ofReal_re, Complex.cos_ofReal_re]

theorem sin_zero_of_sameRay {u v E F t : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : SameRay ℝ ((u : ℂ) * phase E t) ((v : ℂ) * phase F t)) :
    Real.sin ((F - E) * t) = 0 := by
  have hx : ((u : ℂ) * phase E t) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hu) (phase_ne_zero' E t)
  have hy : ((v : ℂ) * phase F t) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hv) (phase_ne_zero' F t)
  have harg : ((u : ℂ) * phase E t).arg = ((v : ℂ) * phase F t).arg := by
    rcases (Complex.sameRay_iff.mp h) with h0 | h0 | h0
    · exact absurd h0 hx
    · exact absurd h0 hy
    · exact h0
  have hratio : (↑‖(v : ℂ) * phase F t‖ / ↑‖(u : ℂ) * phase E t‖ : ℂ) *
      ((u : ℂ) * phase E t) = (v : ℂ) * phase F t :=
    (Complex.arg_eq_arg_iff hx hy).mp harg
  set Z : ℂ := Complex.exp (Complex.I * ((t : ℂ) * (F : ℂ))) with hZ
  have hFZ : phase F t * Z = 1 := by
    have h1 := phase_mul_exp F F t
    have h0 : ((F - F) * t : ℝ) = 0 := by ring
    rw [h0] at h1
    simpa [Z] using h1
  have hEZ := phase_mul_exp E F t
  have hkey : (↑(‖(v : ℂ) * phase F t‖ / ‖(u : ℂ) * phase E t‖ * u) : ℂ) *
      Complex.exp (Complex.I * (((F - E) * t : ℝ) : ℂ)) = (↑v : ℂ) := by
    have hre : (↑‖(v : ℂ) * phase F t‖ / ↑‖(u : ℂ) * phase E t‖ : ℂ) *
        ((u : ℂ) * (phase E t * Z)) = (v : ℂ) * (phase F t * Z) := by
      calc (↑‖(v : ℂ) * phase F t‖ / ↑‖(u : ℂ) * phase E t‖ : ℂ) *
            ((u : ℂ) * (phase E t * Z))
          = ((↑‖(v : ℂ) * phase F t‖ / ↑‖(u : ℂ) * phase E t‖ : ℂ) *
              ((u : ℂ) * phase E t)) * Z := by ring
        _ = ((v : ℂ) * phase F t) * Z := by rw [hratio]
        _ = (v : ℂ) * (phase F t * Z) := by ring
    rw [hFZ, hEZ, mul_one] at hre
    calc (↑(‖(v : ℂ) * phase F t‖ / ‖(u : ℂ) * phase E t‖ * u) : ℂ) *
          Complex.exp (Complex.I * (((F - E) * t : ℝ) : ℂ))
        = ((↑‖(v : ℂ) * phase F t‖ / ↑‖(u : ℂ) * phase E t‖ : ℂ) * ↑u) *
            Complex.exp (Complex.I * (((F - E) * t : ℝ) : ℂ)) := by
          rw [Complex.ofReal_mul, Complex.ofReal_div]
      _ = (↑‖(v : ℂ) * phase F t‖ / ↑‖(u : ℂ) * phase E t‖ : ℂ) *
            (↑u * Complex.exp (Complex.I * (((F - E) * t : ℝ) : ℂ))) := by ring
      _ = (↑v : ℂ) := hre
  have him := congrArg Complex.im hkey
  rw [im_real_mul_expI] at him
  simp only [Complex.ofReal_im] at him
  have hcoef : ‖(v : ℂ) * phase F t‖ / ‖(u : ℂ) * phase E t‖ * u ≠ 0 := by
    have hn1 : ‖(u : ℂ) * phase E t‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hn2 : ‖(v : ℂ) * phase F t‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have hdiv : ‖(v : ℂ) * phase F t‖ / ‖(u : ℂ) * phase E t‖ ≠ 0 := div_ne_zero hn2 hn1
    exact mul_ne_zero hdiv hu
  rcases mul_eq_zero.mp him with h1 | h1
  · exact absurd h1 hcoef
  · exact h1

theorem phase_norm (E t : ℝ) : ‖phase E t‖ = 1 := by
  unfold phase
  have h : -(Complex.I * (t : ℂ) * (E : ℂ)) = ((-(t * E) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem pathEigenvalue_rec0 (N : ℕ) (hN : 4 ≤ N) :
    pathEigenvalue N ⟨2, by omega⟩ + pathEigenvalue N ⟨0, by omega⟩ =
      (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) * pathEigenvalue N ⟨1, by omega⟩ := by
  set a : ℝ := Real.pi / ((N : ℝ) + 1) with ha
  unfold pathEigenvalue
  push_cast
  rw [show (((2 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 3 * a by rw [ha]; ring,
    show (((0 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = a by rw [ha]; ring,
    show (((1 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 2 * a by rw [ha]; ring]
  have hc : Real.cos (3 * a) + Real.cos a = 2 * Real.cos (2 * a) * Real.cos a := by
    have h := Real.cos_add_cos (3 * a) a
    rw [show (3 * a + a) / 2 = 2 * a by ring,
      show (3 * a - a) / 2 = a by ring] at h
    exact h
  linear_combination 2 * hc

theorem pathEigenvalue_rec1 (N : ℕ) (hN : 4 ≤ N) :
    pathEigenvalue N ⟨3, by omega⟩ + pathEigenvalue N ⟨1, by omega⟩ =
      (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) * pathEigenvalue N ⟨2, by omega⟩ := by
  set a : ℝ := Real.pi / ((N : ℝ) + 1) with ha
  unfold pathEigenvalue
  push_cast
  rw [show (((3 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 4 * a by rw [ha]; ring,
    show (((1 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 2 * a by rw [ha]; ring,
    show (((2 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 3 * a by rw [ha]; ring]
  have hc : Real.cos (4 * a) + Real.cos (2 * a) = 2 * Real.cos (3 * a) * Real.cos a := by
    have h := Real.cos_add_cos (4 * a) (2 * a)
    rw [show (4 * a + 2 * a) / 2 = 3 * a by ring,
      show (4 * a - 2 * a) / 2 = a by ring] at h
    exact h
  linear_combination 2 * hc

theorem pathEigenvalue_two_lt_one (N : ℕ) (hN : 4 ≤ N) :
    pathEigenvalue N ⟨2, by omega⟩ < pathEigenvalue N ⟨1, by omega⟩ := by
  set a : ℝ := Real.pi / ((N : ℝ) + 1) with ha
  have ha0 : 0 < a := by
    rw [ha]; positivity
  have haπ : 3 * a ≤ Real.pi := by
    rw [ha]
    rw [show 3 * (Real.pi / ((N : ℝ) + 1)) = 3 * Real.pi / ((N : ℝ) + 1) by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have h5 : (3 : ℝ) ≤ (N : ℝ) := by
      have : (3 : ℕ) ≤ N := by omega
      exact_mod_cast this
    nlinarith [Real.pi_pos]
  unfold pathEigenvalue
  push_cast
  rw [show (((2 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 3 * a by rw [ha]; ring,
    show (((1 : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) = 2 * a by rw [ha]; ring]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 2 * a) (y := 3 * a)
    (by positivity) (by linarith) (by linarith)
  linarith

theorem chain_no_perfect_transfer_four (N : ℕ) (hN : 4 ≤ N) :
    ¬ SpectralPerfectTransfer (pathEigenvalue N) (fun k => (pathWeight N k : ℂ)) := by
  rintro ⟨t, ht, hF⟩
  have hN0 : 0 < N := by omega
  set w : Fin N → ℂ := fun k => (pathWeight N k : ℂ) * phase (pathEigenvalue N k) t with hw
  have hsum_eq : (∑ k : Fin N, w k) =
      spectralAmplitude (pathEigenvalue N) (fun k => (pathWeight N k : ℂ)) t := by
    simp only [hw, spectralAmplitude]
  have hFw : ‖∑ k : Fin N, w k‖ = 1 := by rw [hsum_eq]; exact hF
  have hwne : ∀ k : Fin N, w k ≠ 0 := by
    intro k
    rw [hw]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (pathWeight_ne_zero N hN0 k))
      (phase_ne_zero' _ _)
  have hnorm : ∀ k : Fin N, ‖w k‖ = |pathWeight N k| := by
    intro k
    rw [hw]
    simp only [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnorm_sum : (∑ k : Fin N, ‖w k‖) = 1 := by
    have h' : (∑ k : Fin N, ‖(pathWeight N k : ℂ)‖) = 1 := pathWeight_norm_sum N hN0
    simpa only [hnorm, Complex.norm_real, Real.norm_eq_abs] using h'
  have hEq : ‖∑ k ∈ Finset.univ, w k‖ = ∑ k ∈ Finset.univ, ‖w k‖ := by
    have h : ‖∑ k : Fin N, w k‖ = ∑ k : Fin N, ‖w k‖ := by rw [hFw, hnorm_sum]
    simpa using h
  have hT : (∑ k ∈ Finset.univ, w k) ≠ 0 := by
    have hpos : ‖∑ k ∈ Finset.univ, w k‖ ≠ 0 := by rw [hEq, hnorm_sum]; norm_num
    intro h0
    exact hpos (by rw [h0]; simp)
  have halign := sameRay_pairwise Finset.univ w (fun k _ => hwne k) hEq hT
  have hS01 : SameRay ℝ (w ⟨0, by omega⟩) (w ⟨1, by omega⟩) :=
    halign ⟨0, by omega⟩ (Finset.mem_univ _) ⟨1, by omega⟩ (Finset.mem_univ _)
  have hS12 : SameRay ℝ (w ⟨1, by omega⟩) (w ⟨2, by omega⟩) :=
    halign ⟨1, by omega⟩ (Finset.mem_univ _) ⟨2, by omega⟩ (Finset.mem_univ _)
  have hS23 : SameRay ℝ (w ⟨2, by omega⟩) (w ⟨3, by omega⟩) :=
    halign ⟨2, by omega⟩ (Finset.mem_univ _) ⟨3, by omega⟩ (Finset.mem_univ _)
  have hs0 : Real.sin ((pathEigenvalue N ⟨1, by omega⟩ - pathEigenvalue N ⟨0, by omega⟩) * t) = 0 := by
    refine sin_zero_of_sameRay (pathWeight_ne_zero N hN0 ⟨0, by omega⟩)
      (pathWeight_ne_zero N hN0 ⟨1, by omega⟩) ?_
    simpa [hw] using hS01
  have hs1 : Real.sin ((pathEigenvalue N ⟨2, by omega⟩ - pathEigenvalue N ⟨1, by omega⟩) * t) = 0 := by
    refine sin_zero_of_sameRay (pathWeight_ne_zero N hN0 ⟨1, by omega⟩)
      (pathWeight_ne_zero N hN0 ⟨2, by omega⟩) ?_
    simpa [hw] using hS12
  have hs2 : Real.sin ((pathEigenvalue N ⟨3, by omega⟩ - pathEigenvalue N ⟨2, by omega⟩) * t) = 0 := by
    refine sin_zero_of_sameRay (pathWeight_ne_zero N hN0 ⟨2, by omega⟩)
      (pathWeight_ne_zero N hN0 ⟨3, by omega⟩) ?_
    simpa [hw] using hS23
  rcases Real.sin_eq_zero_iff.mp hs0 with ⟨m0, hm0⟩
  rcases Real.sin_eq_zero_iff.mp hs1 with ⟨m1, hm1⟩
  rcases Real.sin_eq_zero_iff.mp hs2 with ⟨m2, hm2⟩
  have hrec0 := pathEigenvalue_rec0 N hN
  have hrec1 := pathEigenvalue_rec1 N hN
  have hkey : (pathEigenvalue N ⟨3, by omega⟩ - pathEigenvalue N ⟨2, by omega⟩) +
      (pathEigenvalue N ⟨1, by omega⟩ - pathEigenvalue N ⟨0, by omega⟩) =
      (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) *
        (pathEigenvalue N ⟨2, by omega⟩ - pathEigenvalue N ⟨1, by omega⟩) := by
    linear_combination hrec1 - hrec0
  have hd1 : pathEigenvalue N ⟨2, by omega⟩ < pathEigenvalue N ⟨1, by omega⟩ :=
    pathEigenvalue_two_lt_one N hN
  have hd1ne : (pathEigenvalue N ⟨2, by omega⟩ - pathEigenvalue N ⟨1, by omega⟩) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt hd1)
  have hm1ne : m1 ≠ 0 := by
    intro h
    have hzero : (pathEigenvalue N ⟨2, by omega⟩ - pathEigenvalue N ⟨1, by omega⟩) * t = 0 := by
      rw [← hm1, h]
      simp
    exact (mul_ne_zero hd1ne (ne_of_gt ht)) hzero
  have hdt : ((pathEigenvalue N ⟨3, by omega⟩ - pathEigenvalue N ⟨2, by omega⟩) +
      (pathEigenvalue N ⟨1, by omega⟩ - pathEigenvalue N ⟨0, by omega⟩)) * t =
      (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) *
        ((pathEigenvalue N ⟨2, by omega⟩ - pathEigenvalue N ⟨1, by omega⟩) * t) := by
    rw [hkey]
    ring
  have h1 : ((m2 + m0 : ℤ) : ℝ) * Real.pi =
      (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) * ((m1 : ℝ) * Real.pi) := by
    calc ((m2 + m0 : ℤ) : ℝ) * Real.pi
        = (m2 : ℝ) * Real.pi + (m0 : ℝ) * Real.pi := by push_cast; ring
      _ = (pathEigenvalue N ⟨3, by omega⟩ - pathEigenvalue N ⟨2, by omega⟩) * t +
            (pathEigenvalue N ⟨1, by omega⟩ - pathEigenvalue N ⟨0, by omega⟩) * t := by
          rw [hm2, hm0]
      _ = ((pathEigenvalue N ⟨3, by omega⟩ - pathEigenvalue N ⟨2, by omega⟩) +
            (pathEigenvalue N ⟨1, by omega⟩ - pathEigenvalue N ⟨0, by omega⟩)) * t := by ring
      _ = (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) *
            ((pathEigenvalue N ⟨2, by omega⟩ - pathEigenvalue N ⟨1, by omega⟩) * t) := hdt
      _ = (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) * ((m1 : ℝ) * Real.pi) := by rw [hm1]
  have h2 : ((m2 + m0 : ℤ) : ℝ) =
      (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) * (m1 : ℝ) := by
    have h3 : ((m2 + m0 : ℤ) : ℝ) * Real.pi =
        ((2 * Real.cos (Real.pi / ((N : ℝ) + 1))) * (m1 : ℝ)) * Real.pi := by
      rw [h1]; ring
    exact mul_right_cancel₀ Real.pi_ne_zero h3
  have hrat_eq : (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) =
      ((m2 + m0 : ℤ) : ℝ) / (m1 : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hm1ne)]
    exact h2.symm
  have hq : (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) =
      (((((m2 + m0 : ℤ) : ℚ) / (m1 : ℚ)) : ℚ) : ℝ) := by
    rw [hrat_eq]
    push_cast
    ring
  have hint : IsIntegral ℤ (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) := by
    have h := Real.isIntegral_two_mul_cos_rat_mul_pi ((1 : ℚ) / ((N : ℚ) + 1))
    convert h using 2
    push_cast
    ring_nf
  have hex : ∃ k : ℤ, (k : ℝ) = (2 * Real.cos (Real.pi / ((N : ℝ) + 1))) :=
    (IsIntegral.exists_int_iff_exists_rat hint).mp ⟨_, hq.symm⟩
  rcases hex with ⟨k, hk⟩
  have hk := hk.symm
  have h3N : (3 : ℝ) < (N : ℝ) + 1 := by
    have h : (3 : ℕ) < N + 1 := by omega
    exact_mod_cast h
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ha0 : 0 < Real.pi / ((N : ℝ) + 1) := by positivity
  have haπ3 : Real.pi / ((N : ℝ) + 1) < Real.pi / 3 :=
    (div_lt_div_iff_of_pos_left Real.pi_pos hN1 (by norm_num : (0 : ℝ) < 3)).mpr h3N
  have haπ : Real.pi / ((N : ℝ) + 1) ≤ Real.pi := by
    have : Real.pi / ((N : ℝ) + 1) < Real.pi := by
      rw [div_lt_iff₀ hN1]
      nlinarith [Real.pi_pos]
    linarith
  have hlow : (1 : ℝ) < 2 * Real.cos (Real.pi / ((N : ℝ) + 1)) := by
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / ((N : ℝ) + 1))
      (y := Real.pi / 3) ha0.le (by linarith [Real.pi_pos]) haπ3
    have hc3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [hc3] at hc
    linarith
  have hhigh : 2 * Real.cos (Real.pi / ((N : ℝ) + 1)) < 2 := by
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0)
      (y := Real.pi / ((N : ℝ) + 1)) (le_refl 0) haπ ha0
    have hc0 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    rw [hc0] at hc
    linarith
  have hk1 : (1 : ℤ) < k := by
    have h : (1 : ℝ) < (k : ℝ) := by rw [← hk]; exact hlow
    exact_mod_cast h
  have hk2 : k < 2 := by
    have h : (k : ℝ) < (2 : ℝ) := by rw [← hk]; exact hhigh
    exact_mod_cast h
  omega

end

end Qatlib.Papers.StateTransfer03.MainResults.Source

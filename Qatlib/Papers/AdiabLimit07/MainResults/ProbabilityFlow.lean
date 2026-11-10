/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Calculus
import Qatlib.Papers.AdiabLimit07.MainResults.CharacterBounds
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n : ℕ}

theorem walshChar_im (z x y : Reg n) : (walshChar z x y).im = 0 := by
  unfold walshChar
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Complex.mul_im, ih, mul_zero, zero_add]
    split_ifs <;> simp

theorem im_mul_of_im_zero {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) :
    (a * b).im = 0 := by
  rw [Complex.mul_im, ha, hb]; ring

theorem im_sum_zero {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i, (f i).im = 0) :
    (∑ i ∈ s, f i).im = 0 := by
  change Complex.imAddGroupHom (∑ i ∈ s, f i) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i _ => h i)

theorem re_mul_neg_I_im (w z : ℂ) : (w * (-Complex.I * z)).re = (w * z).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im]
  ring

theorem walshChar_factor (x y a : Reg n) :
    walshChar a x y
      = ∏ i, ((if x i && a i then (-1:ℂ) else 1) *
                (if y i && a i then (-1:ℂ) else 1)) := by
  unfold walshChar
  apply Finset.prod_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> cases ha : a i <;> simp_all

theorem sqrt2_inv_mul : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = ((2:ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem coeff_sqrt (n : ℕ) :
    (((Real.sqrt 2 : ℂ)⁻¹) ^ n) * (((Real.sqrt 2 : ℂ)⁻¹) ^ n) = (((2:ℕ)^n : ℂ))⁻¹ := by
  rw [← mul_pow, sqrt2_inv_mul, inv_pow]
  push_cast
  rfl

theorem hadamardN_entry_mul (x y a : Reg n) :
    HadamardN n x a * (starRingEnd ℂ) (HadamardN n y a)
      = (((2:ℕ)^n : ℂ))⁻¹ * walshChar a x y := by
  rw [hadamardN_conj, hadamardN_apply, hadamardN_apply]
  have hP : (∏ i, (if x i && a i then (-1:ℂ) else 1)) *
      (∏ i, (if y i && a i then (-1:ℂ) else 1)) = walshChar a x y := by
    rw [← Finset.prod_mul_distrib, ← walshChar_factor]
  rw [← hP, ← coeff_sqrt]
  ring

theorem sum_qBlock_walsh {q : ℕ} (qIdx : Reg n → Fin (q + 1)) (x y : Reg n) :
    (∑ k : Fin (q + 1), ∑ z ∈ qBlock qIdx k, walshChar z x y)
      = (((2:ℕ)^n : ℂ)) * (if x = y then 1 else 0) := by
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Reg n))) (t := (Finset.univ : Finset (Fin (q + 1))))
    (g := qIdx) (fun i _ => Finset.mem_univ _) (fun z => walshChar z x y)
  simp only [qBlock]
  rw [hfib, walshChar_sum]
  split_ifs <;> simp

theorem entry_as_fiber {q : ℕ} (F : Fin (q + 1) → ℝ) (qIdx : Reg n → Fin (q + 1)) (x y : Reg n) :
    (∑ a : Reg n, (F (qIdx a) : ℂ) * walshChar a x y)
      = ∑ k : Fin (q + 1), (F k : ℂ) * ∑ z ∈ qBlock qIdx k, walshChar z x y := by
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Reg n))) (t := (Finset.univ : Finset (Fin (q + 1))))
    (g := qIdx) (fun i _ => Finset.mem_univ _) (fun a => (F (qIdx a) : ℂ) * walshChar a x y)
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hk : qIdx a = k := (Finset.mem_filter.mp ha).2
  simp [hk]

theorem hadamardHamiltonian_entry {q : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) (K : Fin (q + 1)) (x y : Reg n) :
    hadamardHamiltonian F qIdx x y
      = (F K : ℂ) * (if x = y then 1 else 0)
        - (((2 : ℕ) ^ n : ℂ))⁻¹ * ∑ k : Fin (q + 1),
            ((F K - F k : ℝ) : ℂ) * ∑ z ∈ qBlock qIdx k, walshChar z x y := by
  set Nc : ℂ := (((2:ℕ)^n : ℂ)) with hNc
  set S : Fin (q+1) → ℂ := fun k => ∑ z ∈ qBlock qIdx k, walshChar z x y with hS
  set T : ℂ := ∑ k : Fin (q+1), (F k : ℂ) * S k with hT
  have hL : hadamardHamiltonian F qIdx x y = Nc⁻¹ * T := by
    have hexp : hadamardHamiltonian F qIdx x y
        = ∑ a : Reg n, (F (qIdx a) : ℂ) *
            (HadamardN n x a * (starRingEnd ℂ) (HadamardN n y a)) := by
      unfold hadamardHamiltonian
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [Matrix.diagonal]; ring
      · intro b _ hb; simp [Matrix.diagonal, hb]
      · intro h; simp at h
    rw [hexp]
    simp only [hadamardN_entry_mul]
    have hfac : (∑ a : Reg n, (F (qIdx a) : ℂ) * ((((2:ℕ)^n : ℂ))⁻¹ * walshChar a x y))
        = Nc⁻¹ * ∑ a : Reg n, (F (qIdx a) : ℂ) * walshChar a x y := by
      rw [hNc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hfac, entry_as_fiber, ← hT]
  have hSsum : (∑ k : Fin (q+1), S k) = Nc * (if x = y then 1 else 0) := by
    rw [hS, hNc]; exact sum_qBlock_walsh qIdx x y
  have hR : (F K : ℂ) * (if x = y then 1 else 0)
      - Nc⁻¹ * ∑ k : Fin (q+1), ((F K - F k : ℝ) : ℂ) * S k = Nc⁻¹ * T := by
    have hsplit : (∑ k : Fin (q+1), ((F K - F k : ℝ) : ℂ) * S k)
        = (F K : ℂ) * (∑ k : Fin (q+1), S k) - T := by
      rw [hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [hsplit, hSsum]
    have hNcinv : Nc⁻¹ * Nc = 1 := inv_mul_cancel₀ (by rw [hNc]; norm_num)
    have hmid : Nc⁻¹ * ((F K : ℂ) * (Nc * (if x = y then 1 else 0)))
        = (F K : ℂ) * (if x = y then 1 else 0) := by
      calc Nc⁻¹ * ((F K : ℂ) * (Nc * (if x = y then 1 else 0)))
          = (F K : ℂ) * (if x = y then 1 else 0) * (Nc⁻¹ * Nc) := by ring
        _ = (F K : ℂ) * (if x = y then 1 else 0) := by rw [hNcinv, mul_one]
    rw [mul_sub, hmid]
    ring
  rw [hL, hR]

theorem im_sub_of_im_zero {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) : (a - b).im = 0 := by
  simp [Complex.sub_im, ha, hb]

theorem im_inv_two_pow (n : ℕ) : (((((2:ℕ)^n : ℂ)))⁻¹).im = 0 := by
  rw [Complex.inv_im]
  have hz : ((((2:ℕ)^n : ℂ))).im = 0 := by
    have h : ((((2:ℕ)^n : ℂ))) = ((((2:ℕ)^n : ℝ)) : ℂ) := by push_cast; norm_num
    rw [h]; exact Complex.ofReal_im _
  rw [hz]; simp

theorem hadamardHamiltonian_im {q : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) (x y : Reg n) :
    (hadamardHamiltonian F qIdx x y).im = 0 := by
  rw [hadamardHamiltonian_entry F qIdx 0 x y]
  apply im_sub_of_im_zero
  · exact im_mul_of_im_zero (by simp) (by split_ifs <;> simp)
  · apply im_mul_of_im_zero
    · exact im_inv_two_pow n
    · apply im_sum_zero
      intro k
      exact im_mul_of_im_zero (by simp)
        (im_sum_zero _ _ (fun z => walshChar_im z x y))

theorem computationalHamiltonian_im {p : ℕ} (E : Fin (p + 1) → ℝ)
    (pIdx : Reg n → Fin (p + 1)) (x y : Reg n) :
    (computationalHamiltonian E pIdx x y).im = 0 := by
  unfold computationalHamiltonian
  rw [Matrix.diagonal_apply]
  split_ifs <;> simp

theorem genHamiltonian_im (s : ℝ) {H0 H1 : Matrix (Reg n) (Reg n) ℂ}
    (h0 : ∀ x y, (H0 x y).im = 0) (h1 : ∀ x y, (H1 x y).im = 0) (x y : Reg n) :
    (genHamiltonian s H0 H1 x y).im = 0 := by
  unfold genHamiltonian
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Complex.add_im,
    Complex.smul_im, Complex.smul_im, h0 x y, h1 x y, smul_zero, smul_zero, add_zero]

theorem hasDerivAt_bornProb {H : ℝ → Matrix (Reg n) (Reg n) ℂ}
    {ψ : ℝ → QState (Reg n)} {T : ℝ}
    (hSchrod : SchrodingerIVP H ψ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : Reg n) :
    HasDerivAt (fun u => BornProb (ψ u) x)
      (2 * (starRingEnd ℂ (ψ t x) * (-(Complex.I) * (H t).mulVec (ψ t) x)).re) t := by
  have h := (hSchrod t ht x).norm_sq
  have hinner : inner ℝ (ψ t x) (( -(Complex.I)) * (H t).mulVec (ψ t) x)
      = (starRingEnd ℂ (ψ t x) * (-(Complex.I) * (H t).mulVec (ψ t) x)).re := by
    rw [Complex.inner]
    congr 1
    ring
  rw [hinner] at h
  exact h

theorem hasDerivAt_solutionProb {p : ℕ} {H : ℝ → Matrix (Reg n) (Reg n) ℂ}
    (pIdx : Reg n → Fin (p + 1)) {ψ : ℝ → QState (Reg n)} {T : ℝ}
    (hSchrod : SchrodingerIVP H ψ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivAt (fun u => solutionProb pIdx (ψ u))
      (∑ x ∈ solutionSet pIdx,
        2 * (starRingEnd ℂ (ψ t x) * (-(Complex.I) * (H t).mulVec (ψ t) x)).re) t := by
  have h := HasDerivAt.sum (u := solutionSet pIdx)
    (A := fun x u => BornProb (ψ u) x)
    (A' := fun x => 2 * (starRingEnd ℂ (ψ t x) * (-(Complex.I) * (H t).mulVec (ψ t) x)).re)
    (x := t) (fun x _ => hasDerivAt_bornProb hSchrod ht x)
  have hfun : (∑ x ∈ solutionSet pIdx, (fun u => BornProb (ψ u) x))
      = (fun u => solutionProb pIdx (ψ u)) := by
    funext u
    simp [solutionProb]
  rw [hfun] at h
  exact h

theorem im_mulVec_real (H : Matrix (Reg n) (Reg n) ℂ) (γ : QState (Reg n)) (a : ℂ)
    (x : Reg n) (hH : ∀ y, (H x y).im = 0) :
    (starRingEnd ℂ a * (H.mulVec γ) x).im
      = ∑ y, (H x y).re * (starRingEnd ℂ a * γ y).im := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  change Complex.imAddGroupHom (∑ i, starRingEnd ℂ a * (H x i * γ i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y _
  change (starRingEnd ℂ a * (H x y * γ y)).im
      = (H x y).re * (starRingEnd ℂ a * γ y).im
  have hreorder : starRingEnd ℂ a * (H x y * γ y)
      = (starRingEnd ℂ a * γ y) * H x y := by ring
  rw [hreorder, Complex.mul_im, hH y, mul_zero, zero_add, mul_comm]

theorem abs_im_conj_comm (a b : ℂ) :
    |(starRingEnd ℂ a * b).im| = |(a * starRingEnd ℂ b).im| := by
  have h : starRingEnd ℂ a * b = starRingEnd ℂ (a * starRingEnd ℂ b) := by
    rw [map_mul]
    simp
  rw [h, Complex.conj_im, abs_neg]

theorem im_sum_abs_le_sqrt {γ : Reg n → ℂ} (hγ : Normalized γ) (w : Reg n) :
    (∑ y : Reg n, |(starRingEnd ℂ (γ w) * γ y).im|)
      ≤ Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
  calc
    (∑ y : Reg n, |(starRingEnd ℂ (γ w) * γ y).im|)
        = ∑ y : Reg n, |(γ w * starRingEnd ℂ (γ y)).im| := by
          apply Finset.sum_congr rfl
          intro y _
          rw [abs_im_conj_comm]
    _ ≤ Real.sqrt (((2 : ℕ) ^ n : ℝ)) := im_inner_sum_le_sqrt hγ w

theorem genHamiltonian_offdiag_bound {q p : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) (E : Fin (p + 1) → ℝ) (pIdx : Reg n → Fin (p + 1))
    (K : Fin (q + 1))
    (hmono : ∀ a b : Fin (q + 1), a ≤ b → F a ≤ F b)
    (hF0 : 0 ≤ F 0) (maxF : ℝ) (hmax : ∀ k, F k ≤ maxF)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {x y : Reg n} (hxy : x ≠ y) :
    ‖genHamiltonian s (hadamardHamiltonian F qIdx) (computationalHamiltonian E pIdx) x y‖
      ≤ maxF * eigenspaceComplementDim qIdx K / ((2 : ℕ) ^ n : ℝ) := by
  set Nc : ℂ := (((2 : ℕ) ^ n : ℂ)) with hNc
  set N : ℝ := (((2 : ℕ) ^ n : ℝ)) with hNN
  have hH1 : computationalHamiltonian E pIdx x y = 0 := by
    unfold computationalHamiltonian
    rw [Matrix.diagonal_apply, if_neg hxy]
  have hH0eq : hadamardHamiltonian F qIdx x y
      = -(Nc⁻¹) * (∑ k : Fin (q + 1),
          ((F K - F k : ℝ) : ℂ) * ∑ z ∈ qBlock qIdx k, walshChar z x y) := by
    rw [hadamardHamiltonian_entry F qIdx K x y, if_neg hxy]
    ring
  have hNcnorm : ‖Nc⁻¹‖ = N⁻¹ := by
    have hcast : Nc = ((N : ℝ) : ℂ) := by rw [hNc, hNN]; push_cast; norm_num
    rw [hcast, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hH0norm : ‖hadamardHamiltonian F qIdx x y‖
      ≤ maxF * eigenspaceComplementDim qIdx K / N := by
    rw [hH0eq, norm_mul, norm_neg, hNcnorm]
    have hS := coupling_bound F qIdx K hmono hF0 maxF hmax x y
    calc
      N⁻¹ * ‖∑ k : Fin (q + 1),
          ((F K - F k : ℝ) : ℂ) * (∑ z ∈ qBlock qIdx k, walshChar z x y)‖
          ≤ N⁻¹ * (maxF * (((2 : ℕ) ^ n : ℝ) - ((qBlock qIdx K).card : ℝ))) :=
            mul_le_mul_of_nonneg_left hS (by positivity)
      _ = maxF * eigenspaceComplementDim qIdx K / N := by
            unfold eigenspaceComplementDim
            rw [hNN]
            ring
  unfold genHamiltonian
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, hH1, smul_zero, add_zero]
  rw [norm_smul]
  have h1s : ‖(1 - s : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    ‖(1 - s : ℝ)‖ * ‖hadamardHamiltonian F qIdx x y‖
        ≤ 1 * ‖hadamardHamiltonian F qIdx x y‖ :=
          mul_le_mul_of_nonneg_right h1s (norm_nonneg _)
    _ = ‖hadamardHamiltonian F qIdx x y‖ := one_mul _
    _ ≤ maxF * eigenspaceComplementDim qIdx K / N := hH0norm
    _ = maxF * eigenspaceComplementDim qIdx K / ((2 : ℕ) ^ n : ℝ) := by rw [hNN]

theorem probability_flow_bound {q p : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) (E : Fin (p + 1) → ℝ) (pIdx : Reg n → Fin (p + 1))
    (K : Fin (q + 1))
    (hmono : ∀ a b : Fin (q + 1), a ≤ b → F a ≤ F b)
    (hF0 : 0 ≤ F 0) (maxF : ℝ) (hmax : ∀ k, F k ≤ maxF)
    (s : ℝ → ℝ) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (ψ : ℝ → QState (Reg n)) (T : ℝ)
    (hSchrod : SchrodingerIVP
      (fun t => genHamiltonian (s t) (hadamardHamiltonian F qIdx)
        (computationalHamiltonian E pIdx)) ψ T)
    (hψnorm : ∀ t ∈ Set.Icc 0 T, Normalized (ψ t)) :
    ∀ t ∈ Set.Icc 0 T,
      |deriv (fun u => solutionProb pIdx (ψ u)) t|
        ≤ 2 * ((solutionSet pIdx).card : ℝ) * maxF * eigenspaceComplementDim qIdx K
            / Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
  intro t ht
  set N : ℝ := (((2 : ℕ) ^ n : ℝ)) with hNN
  have hNpos : (0 : ℝ) < N := by rw [hNN]; positivity
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsq : Real.sqrt N * Real.sqrt N = N := by
    rw [← pow_two]; exact Real.sq_sqrt (le_of_lt hNpos)
  set compDim : ℝ := eigenspaceComplementDim qIdx K with hcompDim
  set B : ℝ := maxF * compDim / Real.sqrt N with hB
  have hmax0 : 0 ≤ maxF := le_trans hF0 (hmax 0)
  rw [(hasDerivAt_solutionProb pIdx hSchrod ht).deriv]
  set M : Matrix (Reg n) (Reg n) ℂ :=
    genHamiltonian (s t) (hadamardHamiltonian F qIdx) (computationalHamiltonian E pIdx) with hM
  simp only [re_mul_neg_I_im]
  rw [← Finset.mul_sum, abs_mul]
  rw [show |(2 : ℝ)| = 2 by norm_num]
  have hMreal : ∀ x y, (M x y).im = 0 := by
    intro x y
    rw [hM]
    exact genHamiltonian_im (s t) (fun a b => hadamardHamiltonian_im F qIdx a b)
      (fun a b => computationalHamiltonian_im E pIdx a b) x y
  have hdiag : ∀ x : Reg n, (starRingEnd ℂ (ψ t x) * ψ t x).im = 0 := by
    intro x
    rw [show starRingEnd ℂ (ψ t x) * ψ t x = ((Complex.normSq (ψ t x) : ℝ) : ℂ) from by
      rw [Complex.normSq_eq_conj_mul_self]]
    exact Complex.ofReal_im _
  have hfbound : ∀ x ∈ solutionSet pIdx,
      |(starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im| ≤ B := by
    intro x _
    rw [im_mulVec_real M (ψ t) (ψ t x) x (hMreal x)]
    have hdiagx : (starRingEnd ℂ (ψ t x) * ψ t x).im = 0 := hdiag x
    calc
      |∑ y : Reg n, (M x y).re * (starRingEnd ℂ (ψ t x) * ψ t y).im|
          ≤ ∑ y : Reg n, |(M x y).re| * |(starRingEnd ℂ (ψ t x) * ψ t y).im| := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            apply Finset.sum_le_sum
            intro y _
            rw [abs_mul]
      _ ≤ ∑ y : Reg n, (maxF * compDim / N) * |(starRingEnd ℂ (ψ t x) * ψ t y).im| := by
            apply Finset.sum_le_sum
            intro y _
            by_cases hyx : y = x
            · subst hyx
              rw [hdiagx]
              simp
            · have hle := genHamiltonian_offdiag_bound F qIdx E pIdx K hmono hF0 maxF hmax
                (s t) (hs0 t) (hs1 t) (x := x) (y := y) (Ne.symm hyx)
              have hle' : ‖M x y‖ ≤ maxF * compDim / N := by
                rw [hM, hcompDim, hNN]
                exact hle
              exact mul_le_mul_of_nonneg_right
                ((Complex.abs_re_le_norm (M x y)).trans hle') (abs_nonneg _)
      _ = (maxF * compDim / N) * ∑ y : Reg n, |(starRingEnd ℂ (ψ t x) * ψ t y).im| := by
            rw [Finset.mul_sum]
      _ ≤ (maxF * compDim / N) * Real.sqrt N := by
            apply mul_le_mul_of_nonneg_left (im_sum_abs_le_sqrt (hψnorm t ht) x)
            have hcardle : ((qBlock qIdx K).card : ℝ) ≤ ((2 : ℕ) ^ n : ℝ) := by
              have h := Finset.card_le_univ (qBlock qIdx K)
              rw [card_reg] at h
              exact_mod_cast h
            have hcd : 0 ≤ compDim := by
              rw [hcompDim]
              unfold eigenspaceComplementDim
              exact sub_nonneg.mpr hcardle
            exact div_nonneg (mul_nonneg hmax0 hcd) (le_of_lt hNpos)
      _ = maxF * compDim / Real.sqrt N := by
            have hsqrt_inv : Real.sqrt N / N = 1 / Real.sqrt N := by
              rw [div_eq_div_iff (ne_of_gt hNpos) (ne_of_gt hsN)]
              simpa using hsq
            calc
              (maxF * compDim / N) * Real.sqrt N
                  = maxF * compDim * (Real.sqrt N / N) := by ring
              _ = maxF * compDim * (1 / Real.sqrt N) := by rw [hsqrt_inv]
              _ = maxF * compDim / Real.sqrt N := by ring
      _ = B := by rw [hB]
  have hsumle : |∑ x ∈ solutionSet pIdx,
        (starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im|
      ≤ ∑ x ∈ solutionSet pIdx,
        |(starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsumB : (∑ x ∈ solutionSet pIdx,
        |(starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im|)
      ≤ ∑ x ∈ solutionSet pIdx, B := Finset.sum_le_sum hfbound
  have hcardB : (∑ x ∈ solutionSet pIdx, B) = ((solutionSet pIdx).card : ℝ) * B := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hfinal : |∑ x ∈ solutionSet pIdx,
        (starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im|
      ≤ ((solutionSet pIdx).card : ℝ) * B := by
    calc
      |∑ x ∈ solutionSet pIdx, (starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im|
          ≤ ∑ x ∈ solutionSet pIdx,
              |(starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im| := hsumle
      _ ≤ ∑ x ∈ solutionSet pIdx, B := hsumB
      _ = ((solutionSet pIdx).card : ℝ) * B := hcardB
  calc
    2 * |∑ x ∈ solutionSet pIdx,
          (starRingEnd ℂ (ψ t x) * (M.mulVec (ψ t) x)).im|
        ≤ 2 * (((solutionSet pIdx).card : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hfinal (by norm_num)
    _ = 2 * ((solutionSet pIdx).card : ℝ) * maxF * eigenspaceComplementDim qIdx K
          / Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
          rw [hB, hcompDim, hNN]
          ring

end Qatlib.Papers.AdiabLimit07.MainResults

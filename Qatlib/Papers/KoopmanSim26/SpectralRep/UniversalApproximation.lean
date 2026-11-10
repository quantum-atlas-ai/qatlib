/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.DiagonalizedLCHS
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KoopmanSim26.SpectralRep

abbrev Cube (n : ℕ) := Fin n → Bool

def hammingWeight {n : ℕ} (s : Cube n) : ℕ := (Finset.univ.filter (fun k => s k = true)).card

noncomputable def walsh {n : ℕ} (s x : Cube n) : ℝ :=
  ∏ k : Fin n, if s k = true then (if x k = true then (-1 : ℝ) else 1) else 1

noncomputable def cubeAvg {n : ℕ} (f : Cube n → ℝ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x

noncomputable def walshCoeff {n : ℕ} (f : Cube n → ℝ) (s : Cube n) : ℝ :=
  cubeAvg (fun x => f x * walsh s x)

noncomputable def walshPhase {n : ℕ} (c : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ s, c s * walsh s x

def cubeXor {n : ℕ} (s t : Cube n) : Cube n := fun k => decide (s k ≠ t k)

noncomputable def diagonalUnitary {n : ℕ} (f : Cube n → ℝ) : Matrix (Cube n) (Cube n) ℂ :=
  Matrix.diagonal (fun x => Complex.exp (Complex.I * (f x : ℂ)))

noncomputable def frobNormSq {n : ℕ} (A : Matrix (Cube n) (Cube n) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

noncomputable def normalizedFrobError {n : ℕ} (f g : Cube n → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * frobNormSq (diagonalUnitary f - diagonalUnitary g)

noncomputable def betaStar {n : ℕ} (α : Cube n → ℝ) : Cube n → ℝ :=
  fun s => if hammingWeight s ≤ 1 then α s else 0

lemma card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

lemma abs_walsh {n : ℕ} (s x : Cube n) : |walsh s x| = 1 := by
  simp only [walsh, Finset.abs_prod]
  refine Finset.prod_eq_one (fun k _ => ?_)
  cases h : s k
  · simp
  · cases x k <;> simp

lemma sum_walsh {n : ℕ} (u : Cube n) :
    ∑ x : Cube n, walsh u x = ∏ k : Fin n, (if u k = true then (0 : ℝ) else 2) := by
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => Bool)
      (fun _ : Fin n => (Finset.univ : Finset Bool))
      (fun (k : Fin n) (b : Bool) => if u k = true then (if b = true then (-1 : ℝ) else 1) else 1)
  rw [Fintype.piFinset_univ] at h
  simp only [walsh]
  rw [← h]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Fintype.sum_bool]
  cases u k <;> norm_num

lemma cubeAvg_walsh {n : ℕ} (u : Cube n) :
    cubeAvg (walsh u) = if u = (fun _ => false) then 1 else 0 := by
  simp only [cubeAvg, sum_walsh]
  by_cases hu : u = (fun _ => false)
  · rw [if_pos hu]
    subst hu
    simp only [Bool.false_eq_true, if_false, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0))
  · rw [if_neg hu]
    have hex : ∃ k, u k = true := by
      by_contra hcon
      push Not at hcon
      exact hu (funext fun k => by
        cases h : u k
        · rfl
        · exact absurd h (hcon k))
    obtain ⟨k, hk⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])]
    simp

lemma walsh_mul_walsh {n : ℕ} (s t x : Cube n) :
    walsh s x * walsh t x = walsh (cubeXor s t) x := by
  simp only [walsh]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  cases hs : s k <;> cases ht : t k <;> cases hx : x k <;> simp [cubeXor, hs, ht]

lemma cubeXor_eq_zero_iff {n : ℕ} (s t : Cube n) :
    cubeXor s t = (fun _ => false) ↔ s = t := by
  constructor
  · intro hcc
    funext k
    have hk : cubeXor s t k = false := by rw [hcc]
    simpa [cubeXor] using! hk
  · intro hst
    funext k
    simp [cubeXor, hst]

lemma cubeAvg_walsh_mul_walsh {n : ℕ} (s t : Cube n) :
    cubeAvg (fun x => walsh s x * walsh t x) = if s = t then 1 else 0 := by
  have hfun : (fun x => walsh s x * walsh t x) = walsh (cubeXor s t) := by
    funext x; exact walsh_mul_walsh s t x
  rw [hfun, cubeAvg_walsh]
  by_cases h : s = t
  · rw [if_pos ((cubeXor_eq_zero_iff s t).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((cubeXor_eq_zero_iff s t).mp hc)), if_neg h]

lemma cubeAvg_add {n : ℕ} (f g : Cube n → ℝ) :
    cubeAvg (fun x => f x + g x) = cubeAvg f + cubeAvg g := by
  simp only [cubeAvg, Finset.sum_add_distrib, mul_add]

lemma cubeAvg_const_mul {n : ℕ} (a : ℝ) (f : Cube n → ℝ) :
    cubeAvg (fun x => a * f x) = a * cubeAvg f := by
  simp only [cubeAvg]
  rw [← Finset.mul_sum]
  ring

lemma cubeAvg_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Cube n → ℝ) :
    cubeAvg (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, cubeAvg (g i) := by
  simp only [cubeAvg, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma cubeAvg_mono {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) :
    cubeAvg f ≤ cubeAvg g := by
  rw [cubeAvg, cubeAvg]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x))
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n))

lemma cubeAvg_const {n : ℕ} (a : ℝ) : cubeAvg (fun _ : Cube n => a) = a := by
  rw [cubeAvg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Cube n) : ℝ) = (2 : ℝ) ^ n := by
    rw [card_cube]; push_cast; ring
  rw [hc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0)), one_mul]

lemma cubeAvg_walshPhase_sq {n : ℕ} (c : Cube n → ℝ) :
    cubeAvg (fun x => (walshPhase c x) ^ 2) = ∑ s, c s ^ 2 := by
  have hexp : (fun x => (walshPhase c x) ^ 2)
      = fun x => ∑ s, ∑ t, (c s * c t) * (walsh s x * walsh t x) := by
    funext x
    rw [walshPhase, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
    ring
  calc cubeAvg (fun x => (walshPhase c x) ^ 2)
      = ∑ s, ∑ t, cubeAvg (fun x => (c s * c t) * (walsh s x * walsh t x)) := by
          rw [hexp, cubeAvg_finset_sum]
          simp_rw [cubeAvg_finset_sum]
    _ = ∑ s, ∑ t, (c s * c t) * cubeAvg (fun x => walsh s x * walsh t x) := by
          simp_rw [cubeAvg_const_mul]
    _ = ∑ s, ∑ t, (c s * c t) * (if s = t then 1 else 0) := by
          simp_rw [cubeAvg_walsh_mul_walsh]
    _ = ∑ s, c s ^ 2 := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.sum_eq_single s]
          · rw [if_pos rfl]; ring
          · intro t _ hts
            rw [if_neg (Ne.symm hts)]; ring
          · intro hs; exact absurd (Finset.mem_univ s) hs

lemma abs_walshPhase_le {n : ℕ} (c : Cube n → ℝ) (x : Cube n) :
    |walshPhase c x| ≤ ∑ s, |c s| := by
  rw [walshPhase]
  calc |∑ s, c s * walsh s x| ≤ ∑ s, |c s * walsh s x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, |c s| := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [abs_mul, abs_walsh, mul_one]

lemma cubeAvg_pow_four_le {n : ℕ} (c : Cube n → ℝ) :
    cubeAvg (fun x => (walshPhase c x) ^ 4) ≤ (∑ s, |c s|) ^ 4 := by
  have hpt : ∀ x, (walshPhase c x) ^ 4 ≤ (∑ s, |c s|) ^ 4 := by
    intro x
    have h1 : |walshPhase c x| ≤ ∑ s, |c s| := abs_walshPhase_le c x
    have h2 : 0 ≤ ∑ s, |c s| := Finset.sum_nonneg (fun s _ => abs_nonneg (c s))
    have h3 : (walshPhase c x) ^ 4 = |walshPhase c x| ^ 4 := by
      have hsq : |walshPhase c x| ^ 2 = (walshPhase c x) ^ 2 := sq_abs _
      calc (walshPhase c x) ^ 4 = ((walshPhase c x) ^ 2) ^ 2 := by ring
        _ = (|walshPhase c x| ^ 2) ^ 2 := by rw [hsq]
        _ = |walshPhase c x| ^ 4 := by ring
    rw [h3]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 4
  calc cubeAvg (fun x => (walshPhase c x) ^ 4)
      ≤ cubeAvg (fun _ => (∑ s, |c s|) ^ 4) := cubeAvg_mono hpt
    _ = (∑ s, |c s|) ^ 4 := cubeAvg_const _

lemma four_sin_sq_half (θ : ℝ) : 4 * Real.sin (θ/2) ^ 2 = 2 - 2 * Real.cos θ := by
  have h := Real.sin_sq_eq_half_sub (x := θ/2)
  rw [show 2 * (θ/2) = θ by ring] at h
  nlinarith

lemma cos_le_taylor4 (θ : ℝ) : Real.cos θ ≤ 1 - θ^2/2 + θ^4/24 := by
  have hd3 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y - Real.sin y) (1 - Real.cos x) x := by
    intro x; simpa using! (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  have hd2 : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -1 + y^2/2 + Real.cos y) (x - Real.sin x) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => -1 + y^2/2 + Real.cos y)
        (0 + (2 * x^(2-1))/2 + (-Real.sin x)) x := by
      exact ((hasDerivAt_const (x:=x) (-1)).add ((hasDerivAt_pow 2 x).div_const 2)).add
        (Real.hasDerivAt_cos x)
    convert! h using 1
    ring
  have hd1 : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -y + y^3/6 + Real.sin y) (-1 + x^2/2 + Real.cos x) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => -y + y^3/6 + Real.sin y)
        (-1 + (3 * x^(3-1))/6 + Real.cos x) x := by
      exact ((hasDerivAt_id x).neg.add ((hasDerivAt_pow 3 x).div_const 6)).add
        (Real.hasDerivAt_sin x)
    convert! h using 1
    ring
  have hdF : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => 1 - y^2/2 + y^4/24 - Real.cos y)
        (-x + x^3/6 + Real.sin x) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => 1 - y^2/2 + y^4/24 - Real.cos y)
        (0 - (2 * x^(2-1))/2 + (4 * x^(4-1))/24 - (-Real.sin x)) x := by
      exact (((hasDerivAt_const (x:=x) (1:ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub (Real.hasDerivAt_cos x)
    convert! h using 1
    ring
  have hm3 : MonotoneOn (fun y : ℝ => y - Real.sin y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
    intro x hx
    rw [(hd3 x).deriv]
    linarith [Real.cos_le_one x]
  have h3 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - Real.sin x := by
    intro x hx
    have := hm3 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
    simpa using! this
  have hm2 : MonotoneOn (fun y : ℝ => -1 + y^2/2 + Real.cos y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
    intro x hx
    rw [(hd2 x).deriv]
    exact h3 x (le_of_lt (by simpa using! hx))
  have h2 : ∀ x : ℝ, 0 ≤ x → 0 ≤ -1 + x^2/2 + Real.cos x := by
    intro x hx
    have := hm2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
    simpa using! this
  have hm1 : MonotoneOn (fun y : ℝ => -y + y^3/6 + Real.sin y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
    intro x hx
    rw [(hd1 x).deriv]
    exact h2 x (le_of_lt (by simpa using! hx))
  have h1 : ∀ x : ℝ, 0 ≤ x → 0 ≤ -x + x^3/6 + Real.sin x := by
    intro x hx
    have := hm1 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
    simpa using! this
  have hmF : MonotoneOn (fun y : ℝ => 1 - y^2/2 + y^4/24 - Real.cos y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
    intro x hx
    rw [(hdF x).deriv]
    exact h1 x (le_of_lt (by simpa using! hx))
  rcases le_or_gt 0 θ with hx | hx
  · have := hmF (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
    simpa using! this
  · have h := hmF (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (neg_pos.mpr hx).le) (neg_pos.mpr hx).le
    have he : (fun y : ℝ => 1 - y^2/2 + y^4/24 - Real.cos y) (-θ)
        = 1 - θ^2/2 + θ^4/24 - Real.cos θ := by
      simp only [Real.cos_neg]; ring
    rw [he] at h
    simpa using! h

lemma cos_fourth_lower (θ : ℝ) : θ^2 - θ^4/12 ≤ 2 - 2 * Real.cos θ := by
  have h := cos_le_taylor4 θ
  nlinarith

lemma cos_fourth_upper (θ : ℝ) : 2 - 2 * Real.cos θ ≤ θ^2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := θ)
  nlinarith

lemma sin_sq_sandwich (θ : ℝ) :
    θ^2 - θ^4/12 ≤ 4 * Real.sin (θ/2) ^ 2 ∧ 4 * Real.sin (θ/2) ^ 2 ≤ θ^2 := by
  rw [four_sin_sq_half]
  exact ⟨cos_fourth_lower θ, cos_fourth_upper θ⟩

lemma frobNormSq_diagonal {n : ℕ} (d : Cube n → ℂ) :
    frobNormSq (Matrix.diagonal d) = ∑ x, ‖d x‖ ^ 2 := by
  simp only [frobNormSq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne d (Ne.symm hj)]
    simp
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma normSq_exp_sub (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a:ℂ)) - Complex.exp (Complex.I * (b:ℂ))‖ ^ 2
      = 4 * Real.sin ((a - b) / 2) ^ 2 := by
  have hre : ∀ r : ℝ, (Complex.exp (Complex.I * (r:ℂ))).re = Real.cos r := by
    intro r; rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have him : ∀ r : ℝ, (Complex.exp (Complex.I * (r:ℂ))).im = Real.sin r := by
    intro r; rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    hre a, hre b, him a, him b]
  have hs : Real.sin ((a - b) / 2) ^ 2 = 1 / 2 - Real.cos (a - b) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    rw [show 2 * ((a - b) / 2) = a - b by ring]
  rw [hs, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

lemma normalizedFrobError_eq {n : ℕ} (f g : Cube n → ℝ) :
    normalizedFrobError f g
      = cubeAvg (fun x => 4 * Real.sin ((f x - g x) / 2) ^ 2) := by
  simp only [normalizedFrobError, cubeAvg]
  have hdiag : frobNormSq (diagonalUnitary f - diagonalUnitary g)
      = ∑ x, ‖Complex.exp (Complex.I * (f x : ℂ)) - Complex.exp (Complex.I * (g x : ℂ))‖ ^ 2 := by
    rw [show diagonalUnitary f - diagonalUnitary g
          = Matrix.diagonal (fun x =>
              Complex.exp (Complex.I * (f x : ℂ)) - Complex.exp (Complex.I * (g x : ℂ))) by
        rw [diagonalUnitary, diagonalUnitary, Matrix.diagonal_sub]]
    rw [frobNormSq_diagonal]
  rw [hdiag]
  rw [show (∑ x, ‖Complex.exp (Complex.I * (f x : ℂ)) - Complex.exp (Complex.I * (g x : ℂ))‖ ^ 2)
        = ∑ x, 4 * Real.sin ((f x - g x) / 2) ^ 2 from
      Finset.sum_congr rfl (fun x _ => normSq_exp_sub (f x) (g x))]

lemma walshPhase_sub {n : ℕ} (α β : Cube n → ℝ) (x : Cube n) :
    walshPhase (fun s => α s - β s) x = walshPhase α x - walshPhase β x := by
  simp only [walshPhase, sub_mul, Finset.sum_sub_distrib]

theorem walsh_error_sandwich (n : ℕ) (c : Cube n → ℝ) :
    (∑ s, c s ^ 2) - (∑ s, |c s|) ^ 4 / 12
        ≤ cubeAvg (fun x => 4 * Real.sin (walshPhase c x / 2) ^ 2) ∧
    cubeAvg (fun x => 4 * Real.sin (walshPhase c x / 2) ^ 2) ≤ ∑ s, c s ^ 2 := by
  have hparse : cubeAvg (fun x => (walshPhase c x) ^ 2) = ∑ s, c s ^ 2 :=
    cubeAvg_walshPhase_sq c
  have hupper_pt : ∀ x, 4 * Real.sin (walshPhase c x / 2) ^ 2 ≤ (walshPhase c x) ^ 2 := by
    intro x
    rw [four_sin_sq_half]
    exact cos_fourth_upper _
  have hlower_pt : ∀ x, (walshPhase c x) ^ 2 - (walshPhase c x) ^ 4 / 12
      ≤ 4 * Real.sin (walshPhase c x / 2) ^ 2 := by
    intro x
    rw [four_sin_sq_half]
    exact cos_fourth_lower _
  refine ⟨?_, ?_⟩
  · have h1 : cubeAvg (fun x => (walshPhase c x) ^ 2 - (walshPhase c x) ^ 4 / 12)
        ≤ cubeAvg (fun x => 4 * Real.sin (walshPhase c x / 2) ^ 2) := cubeAvg_mono hlower_pt
    have h2 : cubeAvg (fun x => (walshPhase c x) ^ 2 - (walshPhase c x) ^ 4 / 12)
        = (∑ s, c s ^ 2) - cubeAvg (fun x => (walshPhase c x) ^ 4 / 12) := by
      rw [show (fun x => (walshPhase c x) ^ 2 - (walshPhase c x) ^ 4 / 12)
            = fun x => (walshPhase c x) ^ 2 + (-1) * ((walshPhase c x) ^ 4 / 12) from by
              funext x; ring]
      rw [cubeAvg_add, cubeAvg_const_mul, hparse]
      ring
    have h3 : cubeAvg (fun x => (walshPhase c x) ^ 4 / 12) ≤ (∑ s, |c s|) ^ 4 / 12 := by
      rw [show (fun x => (walshPhase c x) ^ 4 / 12)
            = fun x => (1/12) * (walshPhase c x) ^ 4 from by
              funext x; ring]
      rw [cubeAvg_const_mul]
      have h := mul_le_mul_of_nonneg_left (cubeAvg_pow_four_le c) (by norm_num : (0:ℝ) ≤ 1/12)
      calc (1/12) * cubeAvg (fun x => (walshPhase c x) ^ 4)
          ≤ (1/12) * (∑ s, |c s|) ^ 4 := h
        _ = (∑ s, |c s|) ^ 4 / 12 := by ring
    rw [h2] at h1
    linarith
  · have h := cubeAvg_mono hupper_pt
    rw [hparse] at h
    exact h

theorem universal_approximation_bound (n : ℕ) (α : Cube n → ℝ) :
    (∑ s, if 2 ≤ hammingWeight s then α s ^ 2 else 0)
        - (∑ s, if 2 ≤ hammingWeight s then |α s| else 0) ^ 4 / 12
      ≤ normalizedFrobError (walshPhase (betaStar α)) (walshPhase α) ∧
    normalizedFrobError (walshPhase (betaStar α)) (walshPhase α)
      ≤ ∑ s, if 2 ≤ hammingWeight s then α s ^ 2 else 0 := by
  have hc : ∀ s, α s - betaStar α s = if 2 ≤ hammingWeight s then α s else 0 := by
    intro s
    simp only [betaStar]
    by_cases h : hammingWeight s ≤ 1
    · rw [if_pos h, if_neg (by omega : ¬ 2 ≤ hammingWeight s)]; ring
    · rw [if_neg h, if_pos (by omega : 2 ≤ hammingWeight s)]; ring
  have hsq : (∑ s, (α s - betaStar α s) ^ 2)
      = ∑ s, if 2 ≤ hammingWeight s then α s ^ 2 else 0 := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hc s]
    by_cases h : 2 ≤ hammingWeight s <;> simp [h]
  have habs : (∑ s, |α s - betaStar α s|)
      = ∑ s, if 2 ≤ hammingWeight s then |α s| else 0 := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hc s]
    by_cases h : 2 ≤ hammingWeight s <;> simp [h]
  have hbridge : normalizedFrobError (walshPhase (betaStar α)) (walshPhase α)
      = cubeAvg (fun x => 4 * Real.sin (walshPhase (fun s => α s - betaStar α s) x / 2) ^ 2) := by
    rw [normalizedFrobError_eq]
    refine congrArg cubeAvg (funext fun x => ?_)
    have hs : walshPhase (betaStar α) x - walshPhase α x
        = - walshPhase (fun s => α s - betaStar α s) x := by
      rw [walshPhase_sub]; ring
    rw [hs, show (-(walshPhase (fun s => α s - betaStar α s) x)) / 2
          = -(walshPhase (fun s => α s - betaStar α s) x / 2) by ring, Real.sin_neg]
    ring
  rw [hbridge]
  have hsand := walsh_error_sandwich n (fun s => α s - betaStar α s)
  rw [hsq, habs] at hsand
  exact hsand

theorem arg_le_chord (z : ℂ) (hz : ‖z‖ = 1) : |z.arg| ≤ (Real.pi / 2) * ‖z-1‖ := by
  have hre : z.re = Real.cos z.arg := by
    have h := Complex.norm_mul_cos_arg z
    simpa only [hz, one_mul] using! h.symm
  have hcos := Real.cos_le_one_sub_mul_cos_sq (Complex.abs_arg_le_pi z)
  have hnorm : ‖z-1‖^2 = 2 - 2*z.re := by
    have hn : z.re^2+z.im^2=1 := by
      have h := Complex.sq_norm z
      rw [hz] at h
      simpa only [one_pow, Complex.normSq_apply, pow_two, one_mul] using! h.symm
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    nlinarith
  have hs : 4 * |z.arg|^2 ≤ Real.pi^2 * ‖z-1‖^2 := by
    rw [sq_abs, hnorm, hre]
    have hp := Real.pi_pos
    have h := (le_sub_iff_add_le.mp hcos)
    field_simp at h
    nlinarith
  have hp := Real.pi_pos
  have hN := norm_nonneg (z-1)
  apply (sq_le_sq₀ (abs_nonneg z.arg) (mul_nonneg (by positivity) hN)).mp
  nlinarith [hs]

theorem exp_arg_unit (z : ℂ) (hz : ‖z‖ = 1) :
    Complex.exp (Complex.I * (z.arg : ℂ)) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  simpa only [hz, Complex.ofReal_one, one_mul, mul_comm Complex.I] using! h

def lowPhase {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (x : Cube n) : ℝ :=
  φ + ∑ j, if x j then θ j else 0

def phaseValue (a : ℝ) : ℂ := Complex.exp (Complex.I * (a:ℂ))

theorem phaseValue_norm (a : ℝ) : ‖phaseValue a‖ = 1 := by
  simp [phaseValue, Complex.norm_exp_I_mul_ofReal]

theorem lowPhase_product {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (x : Cube n) :
    phaseValue (lowPhase φ θ x) = phaseValue φ * ∏ j, if x j then phaseValue (θ j) else 1 := by
  simp only [lowPhase, phaseValue, Complex.ofReal_add, Complex.ofReal_sum,
    mul_add, Finset.mul_sum, Complex.exp_add, Complex.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> simp

def zeroCube (n : ℕ) : Cube n := fun _ => false

def bitCube {n : ℕ} (j : Fin n) : Cube n := fun k => decide (k=j)

theorem lowPhase_zero {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) :
    lowPhase φ θ (zeroCube n) = φ := by simp [lowPhase, zeroCube]

theorem lowPhase_bit {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (j : Fin n) :
    lowPhase φ θ (bitCube j) = φ + θ j := by simp [lowPhase, bitCube]

theorem lowPhase_ratio {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (j : Fin n) :
    phaseValue (lowPhase φ θ (bitCube j)) / phaseValue (lowPhase φ θ (zeroCube n)) =
      phaseValue (θ j) := by
  rw [lowPhase_bit, lowPhase_zero]
  simp only [phaseValue, Complex.ofReal_add, mul_add, Complex.exp_add]
  apply mul_div_cancel_left₀
  exact Complex.exp_ne_zero _

theorem lowPhase_unwrap {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (x : Cube n) :
    phaseValue (lowPhase (Complex.arg (phaseValue φ))
      (fun j => Complex.arg (phaseValue (θ j))) x) = phaseValue (lowPhase φ θ x) := by
  rw [lowPhase_product, lowPhase_product]
  rw [show phaseValue (Complex.arg (phaseValue φ)) = phaseValue φ from
    exp_arg_unit _ (phaseValue_norm _)]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> simp only [Bool.false_eq_true, if_false, if_true]
  exact exp_arg_unit _ (phaseValue_norm _)

theorem normalizedFrobError_normsq {n : ℕ} (f g : Cube n → ℝ) :
    normalizedFrobError f g = cubeAvg (fun x => ‖phaseValue (f x)-phaseValue (g x)‖^2) := by
  unfold normalizedFrobError cubeAvg
  rw [show diagonalUnitary f-diagonalUnitary g =
    Matrix.diagonal (fun x => phaseValue (f x)-phaseValue (g x)) by
      simp only [diagonalUnitary,phaseValue,Matrix.diagonal_sub]]
  rw [frobNormSq_diagonal]

theorem phaseError_nonneg {n : ℕ} (f g : Cube n → ℝ) : 0 ≤ normalizedFrobError f g := by
  rw [normalizedFrobError_normsq, cubeAvg]
  positivity

theorem norm_phase_sub_one_le (a : ℝ) : ‖phaseValue a-1‖ ≤ |a| := by
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg a)).mp
  have he : ‖phaseValue a-1‖^2 = 4*Real.sin (a/2)^2 := by
    simpa only [phaseValue, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      sub_zero] using! normSq_exp_sub a 0
  rw [he, sq_abs]
  exact (sin_sq_sandwich a).2

theorem point_chord_le {n : ℕ} (f g : Cube n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : normalizedFrobError f g ≤ δ^2) (x : Cube n) :
    ‖phaseValue (f x)-phaseValue (g x)‖ ≤ Real.sqrt ((2:ℝ)^n)*δ := by
  have hD : 0 ≤ (2:ℝ)^n := by positivity
  have hsum : ‖phaseValue (f x)-phaseValue (g x)‖^2 ≤
      ∑ y : Cube n, ‖phaseValue (f y)-phaseValue (g y)‖^2 :=
    Finset.single_le_sum (fun y _ => sq_nonneg ‖phaseValue (f y)-phaseValue (g y)‖) (Finset.mem_univ x)
  have hEq : (∑ y : Cube n, ‖phaseValue (f y)-phaseValue (g y)‖^2) =
      (2:ℝ)^n * normalizedFrobError f g := by
    rw [normalizedFrobError_normsq,cubeAvg]
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2:ℝ)^n ≠ 0),one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hδ)).mp
  calc
    _ ≤ ∑ y : Cube n, ‖phaseValue (f y)-phaseValue (g y)‖^2 := hsum
    _ = (2:ℝ)^n * normalizedFrobError f g := hEq
    _ ≤ (2:ℝ)^n * δ^2 := mul_le_mul_of_nonneg_left he hD
    _ = (Real.sqrt ((2:ℝ)^n)*δ)^2 := by rw [mul_pow,Real.sq_sqrt hD]

theorem competitor_near_one {n : ℕ} (h g : Cube n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hh : ∀ x, |h x| ≤ δ) (he : normalizedFrobError g h ≤ δ^2) (x : Cube n) :
    ‖phaseValue (g x)-1‖ ≤ (Real.sqrt ((2:ℝ)^n)+1)*δ := by
  calc
    _ ≤ ‖phaseValue (g x)-phaseValue (h x)‖ + ‖phaseValue (h x)-1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt ((2:ℝ)^n)*δ + δ := add_le_add (point_chord_le g h δ hδ he x)
      ((norm_phase_sub_one_le (h x)).trans (hh x))
    _ = _ := by ring

theorem local_phase_chord {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (B : ℝ)
    (hb : ∀ x, ‖phaseValue (lowPhase φ θ x)-1‖ ≤ B) (j : Fin n) :
    ‖phaseValue (θ j)-1‖ ≤ 2*B := by
  have hprod : phaseValue (φ+θ j)-phaseValue φ = phaseValue φ * (phaseValue (θ j)-1) := by
    simp only [phaseValue, Complex.ofReal_add,mul_add,Complex.exp_add]
    ring
  have heq : ‖phaseValue (φ+θ j)-phaseValue φ‖ = ‖phaseValue (θ j)-1‖ := by
    rw [hprod,norm_mul,phaseValue_norm,one_mul]
  rw [← heq]
  calc
    _ ≤ ‖phaseValue (φ+θ j)-1‖ + ‖1-phaseValue φ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖phaseValue (lowPhase φ θ (bitCube j))-1‖ +
        ‖phaseValue (lowPhase φ θ (zeroCube n))-1‖ := by
      rw [lowPhase_bit,lowPhase_zero,norm_sub_rev 1]
    _ ≤ B+B := add_le_add (hb _) (hb _)
    _ = _ := by ring

theorem abs_lowPhase_le {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (x : Cube n) :
    |lowPhase φ θ x| ≤ |φ| + ∑ j, |θ j| := by
  unfold lowPhase
  apply (abs_add_le _ _).trans
  apply add_le_add_right
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  cases x j <;> simp

theorem unwrap_phase_bound {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (B : ℝ)
    (hb : ∀ x, ‖phaseValue (lowPhase φ θ x)-1‖ ≤ B) (x : Cube n) :
    |lowPhase (Complex.arg (phaseValue φ)) (fun j => Complex.arg (phaseValue (θ j))) x| ≤
      (Real.pi/2)*(1+2*n)*B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb (zeroCube n))
  have hφ : |Complex.arg (phaseValue φ)| ≤ (Real.pi/2)*B := by
    apply (arg_le_chord _ (phaseValue_norm φ)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [lowPhase_zero] using! hb (zeroCube n)
  have hθ (j : Fin n) : |Complex.arg (phaseValue (θ j))| ≤ Real.pi*B := by
    apply (arg_le_chord _ (phaseValue_norm (θ j))).trans
    have hp := mul_le_mul_of_nonneg_left (local_phase_chord φ θ B hb j)
      (by positivity : 0 ≤ Real.pi/2)
    nlinarith
  calc
    _ ≤ |Complex.arg (phaseValue φ)| + ∑ j, |Complex.arg (phaseValue (θ j))| := abs_lowPhase_le _ _ _
    _ ≤ (Real.pi/2)*B + ∑ j : Fin n, Real.pi*B := add_le_add hφ (Finset.sum_le_sum (fun j _ => hθ j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

lemma cubeAvg_sub {n : ℕ} (f g : Cube n → ℝ) :
    cubeAvg (fun x => f x-g x)=cubeAvg f-cubeAvg g := by
  simp only [cubeAvg,Finset.sum_sub_distrib,mul_sub]

lemma walsh_bit {n : ℕ} (j : Fin n) (x : Cube n) :
    walsh (bitCube j) x = if x j then -1 else 1 := by
  unfold walsh
  rw [Finset.prod_eq_single j]
  · simp [bitCube]
  · intro k _ hk
    simp [bitCube,hk]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem high_low_cross {n : ℕ} (h : Cube n → ℝ)
    (hzero : cubeAvg h=0) (hlocal : ∀ j, cubeAvg (fun x => h x*walsh (bitCube j) x)=0)
    (φ : ℝ) (θ : Fin n → ℝ) : cubeAvg (fun x => h x*lowPhase φ θ x)=0 := by
  have hfun : (fun x => h x*lowPhase φ θ x) =
      fun x => φ*h x + ∑ j, (θ j/2)*(h x-h x*walsh (bitCube j) x) := by
    funext x
    simp only [lowPhase,mul_add,Finset.mul_sum]
    rw [mul_comm (h x) φ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [walsh_bit]
    cases x j <;> simp
    all_goals ring
  rw [hfun,cubeAvg_add,cubeAvg_const_mul,cubeAvg_finset_sum,hzero,mul_zero,zero_add]
  simp_rw [cubeAvg_const_mul,cubeAvg_sub,hzero,hlocal]
  simp

theorem high_low_quadratic {n : ℕ} (h : Cube n → ℝ)
    (hzero : cubeAvg h=0) (hlocal : ∀ j, cubeAvg (fun x => h x*walsh (bitCube j) x)=0)
    (φ : ℝ) (θ : Fin n → ℝ) :
    cubeAvg (fun x => h x^2) ≤ cubeAvg (fun x => (lowPhase φ θ x-h x)^2) := by
  have heq : (fun x => (lowPhase φ θ x-h x)^2) =
      fun x => h x^2+(lowPhase φ θ x)^2-2*(h x*lowPhase φ θ x) := by funext x;ring
  rw [heq,cubeAvg_sub,cubeAvg_add,cubeAvg_const_mul,high_low_cross h hzero hlocal φ θ]
  have hn : 0 ≤ cubeAvg (fun x => (lowPhase φ θ x)^2) := by
    simpa only [cubeAvg_const] using!
      (cubeAvg_mono (f:=fun _ : Cube n => (0:ℝ)) (fun x => sq_nonneg (lowPhase φ θ x)))
  linarith

theorem local_error_lower {n : ℕ} (f g : Cube n → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hb : ∀ x, |f x-g x| ≤ M) :
    cubeAvg (fun x => (f x-g x)^2)-M^4/12 ≤ normalizedFrobError f g := by
  have hp (x : Cube n) : (f x-g x)^2-M^4/12 ≤ 4*Real.sin ((f x-g x)/2)^2 := by
    have h4 : (f x-g x)^4 ≤ M^4 := by
      have hh := pow_le_pow_left₀ (abs_nonneg (f x-g x)) (hb x) 4
      simpa only [(by decide : Even 4).pow_abs] using hh
    have ht := (sin_sq_sandwich (f x-g x)).1
    linarith
  have ha := cubeAvg_mono hp
  rw [cubeAvg_sub,cubeAvg_const,← normalizedFrobError_eq] at ha
  exact ha

theorem quadratic_le_bound {n : ℕ} (h : Cube n → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hh : ∀ x, |h x| ≤ δ) : cubeAvg (fun x => h x^2) ≤ δ^2 := by
  have hp (x : Cube n) : h x^2 ≤ δ^2 := by
    simpa only [sq_abs] using! (pow_le_pow_left₀ (abs_nonneg (h x)) (hh x) 2)
  simpa only [cubeAvg_const] using! cubeAvg_mono hp

def phaseConstant (n : ℕ) : ℝ := 1+(Real.pi/2)*(1+2*n)*(Real.sqrt ((2:ℝ)^n)+1)

theorem global_error_lower {n : ℕ} (h : Cube n → ℝ)
    (hzero : cubeAvg h=0) (hlocal : ∀ j, cubeAvg (fun x => h x*walsh (bitCube j) x)=0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hh : ∀ x, |h x| ≤ δ) (φ : ℝ) (θ : Fin n → ℝ) :
    cubeAvg (fun x => h x^2)-(phaseConstant n*δ)^4/12 ≤
      normalizedFrobError (lowPhase φ θ) h := by
  by_cases he : normalizedFrobError (lowPhase φ θ) h ≤ cubeAvg (fun x => h x^2)
  · have heδ := he.trans (quadratic_le_bound h δ hδ hh)
    let B := (Real.sqrt ((2:ℝ)^n)+1)*δ
    have hB : ∀ x, ‖phaseValue (lowPhase φ θ x)-1‖ ≤ B :=
      competitor_near_one h (lowPhase φ θ) δ hδ hh heδ
    let φ' := Complex.arg (phaseValue φ)
    let θ' := fun j => Complex.arg (phaseValue (θ j))
    have hphase (x : Cube n) : |lowPhase φ' θ' x-h x| ≤ phaseConstant n*δ := by
      have hl := unwrap_phase_bound φ θ B hB x
      have ha := abs_sub (lowPhase φ' θ' x) (h x)
      calc
        _ ≤ |lowPhase φ' θ' x|+|h x| := ha
        _ ≤ (Real.pi/2)*(1+2*n)*B+δ := add_le_add hl (hh x)
        _ = _ := by dsimp [B,phaseConstant];ring
    have hC : 0 ≤ phaseConstant n*δ := by unfold phaseConstant;positivity
    have hlo := local_error_lower (lowPhase φ' θ') h (phaseConstant n*δ) hC hphase
    have hquad := high_low_quadratic h hzero hlocal φ' θ'
    have heq : normalizedFrobError (lowPhase φ' θ') h = normalizedFrobError (lowPhase φ θ) h := by
      rw [normalizedFrobError_normsq,normalizedFrobError_normsq]
      apply congrArg cubeAvg
      funext x
      rw [show phaseValue (lowPhase φ' θ' x)=phaseValue (lowPhase φ θ x) from lowPhase_unwrap φ θ x]
    rw [heq] at hlo
    linarith
  · have h4 : 0 ≤ (phaseConstant n*δ)^4/12 := by positivity
    linarith

def bestProductError {n : ℕ} (h : Cube n → ℝ) : ℝ :=
  sInf (Set.range (fun p : ℝ × (Fin n → ℝ) => normalizedFrobError (lowPhase p.1 p.2) h))

theorem errorRange_bddBelow {n : ℕ} (h : Cube n → ℝ) :
    BddBelow (Set.range (fun p : ℝ × (Fin n → ℝ) => normalizedFrobError (lowPhase p.1 p.2) h)) := by
  refine ⟨0,?_⟩
  rintro y ⟨p,rfl⟩
  exact phaseError_nonneg _ _

theorem identity_error_upper {n : ℕ} (h : Cube n → ℝ) :
    normalizedFrobError (lowPhase 0 (fun _ => 0)) h ≤ cubeAvg (fun x => h x^2) := by
  rw [normalizedFrobError_eq]
  apply cubeAvg_mono
  intro x
  have hs := (sin_sq_sandwich (-h x)).2
  simpa only [lowPhase,ite_self,Finset.sum_const_zero,add_zero,zero_sub,neg_sq] using! hs

theorem global_infimum_sandwich {n : ℕ} (h : Cube n → ℝ)
    (hzero : cubeAvg h=0) (hlocal : ∀ j, cubeAvg (fun x => h x*walsh (bitCube j) x)=0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hh : ∀ x, |h x| ≤ δ) :
    cubeAvg (fun x => h x^2)-(phaseConstant n*δ)^4/12 ≤ bestProductError h ∧
      bestProductError h ≤ cubeAvg (fun x => h x^2) := by
  constructor
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨⟨φ,θ⟩,rfl⟩
    exact global_error_lower h hzero hlocal δ hδ hh φ θ
  · exact (csInf_le (errorRange_bddBelow h) (Set.mem_range_self (0,(fun _ => 0)))).trans
      (identity_error_upper h)

lemma hammingWeight_bit {n : ℕ} (j : Fin n) : hammingWeight (bitCube j)=1 := by
  unfold hammingWeight bitCube
  have he : (Finset.univ.filter (fun x : Fin n => decide (x=j)=true)) = {j} := by
    ext x
    simp
  rw [he]
  simp

lemma bitCube_injective {n : ℕ} : Function.Injective (bitCube (n:=n)) := by
  intro j k h
  have he := congrFun h j
  simpa [bitCube] using! he.symm

lemma zero_ne_bit {n : ℕ} (j : Fin n) : zeroCube n ≠ bitCube j := by
  intro h
  have he := congrFun h j
  simp [zeroCube,bitCube] at he

lemma low_label_classification {n : ℕ} (s : Cube n) :
    hammingWeight s ≤ 1 ↔ s=zeroCube n ∨ ∃ j, s=bitCube j := by
  constructor
  · intro hs
    by_cases hz : s=zeroCube n
    · exact Or.inl hz
    · right
      obtain ⟨j,hj⟩ : ∃ j, s j=true := by
        by_contra hnot
        push Not at hnot
        apply hz
        funext j
        cases he : s j
        · rfl
        · exact False.elim (hnot j he)
      refine ⟨j,?_⟩
      funext k
      by_cases hk : k=j
      · subst k; simp [bitCube,hj]
      · have hf : s k=false := by
          cases he : s k
          · rfl
          · have heq := Finset.card_le_one.mp hs k (by simp [he])
              j (by simp [hj])
            exact False.elim (hk heq)
        simp [bitCube,hk,hf]
  · rintro (rfl|⟨j,rfl⟩)
    · simp [hammingWeight,zeroCube]
    · rw [hammingWeight_bit]

lemma low_filter {n : ℕ} :
    Finset.univ.filter (fun s : Cube n => hammingWeight s ≤ 1) =
      insert (zeroCube n) (Finset.univ.image bitCube) := by
  ext s
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,low_label_classification,
    Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro (hz|⟨j,hj⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨j,hj.symm⟩
  · rintro (hz|⟨j,hj⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨j,hj.symm⟩

theorem betaStar_lowPhase {n : ℕ} (α : Cube n → ℝ) :
    walshPhase (betaStar α) = lowPhase (α (zeroCube n)+∑ j,α (bitCube j))
      (fun j => -2*α (bitCube j)) := by
  funext x
  unfold walshPhase betaStar
  simp only [ite_mul,zero_mul]
  rw [← Finset.sum_filter,low_filter,Finset.sum_insert]
  · rw [Finset.sum_image]
    · have hz : walsh (zeroCube n) x=1 := by simp [walsh,zeroCube]
      rw [hz,mul_one]
      unfold lowPhase
      rw [add_assoc,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [walsh_bit]
      cases x j <;> simp
      all_goals ring
    · exact fun _ _ _ _ hij => bitCube_injective hij
  · intro hz
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hz
    exact zero_ne_bit j he.symm

def highPart {n : ℕ} (α : Cube n → ℝ) : Cube n → ℝ :=
  fun s => if 2 ≤ hammingWeight s then α s else 0

theorem walshPhase_low_high {n : ℕ} (α : Cube n → ℝ) :
    walshPhase α = fun x => walshPhase (betaStar α) x+walshPhase (highPart α) x := by
  funext x
  unfold walshPhase
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  unfold betaStar highPart
  by_cases hs : hammingWeight s ≤ 1
  · rw [if_pos hs,if_neg (by omega : ¬ 2 ≤ hammingWeight s)]
    ring
  · rw [if_neg hs,if_pos (by omega : 2 ≤ hammingWeight s)]
    ring

theorem phase_cross_walsh {n : ℕ} (α : Cube n → ℝ) (s : Cube n) :
    cubeAvg (fun x => walshPhase α x*walsh s x)=α s := by
  have hf : (fun x => walshPhase α x*walsh s x)=
      fun x => ∑ t,α t*(walsh t x*walsh s x) := by
    funext x
    unfold walshPhase
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hf,cubeAvg_finset_sum]
  simp_rw [cubeAvg_const_mul,cubeAvg_walsh_mul_walsh]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [ht]
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

theorem highPart_orthogonal {n : ℕ} (α : Cube n → ℝ) :
    cubeAvg (walshPhase (highPart α))=0 ∧
      ∀ j,cubeAvg (fun x => walshPhase (highPart α) x*walsh (bitCube j) x)=0 := by
  constructor
  · have hz : walsh (zeroCube n)=(fun _ => (1:ℝ)) := by funext x;simp [walsh,zeroCube]
    have he := phase_cross_walsh (highPart α) (zeroCube n)
    have hez : highPart α (zeroCube n)=0 := by simp [highPart,hammingWeight,zeroCube]
    simpa only [hz,mul_one,hez] using! he
  · intro j
    rw [phase_cross_walsh]
    simp [highPart,hammingWeight_bit]

lemma lowPhase_sub {n : ℕ} (φ a : ℝ) (θ b : Fin n → ℝ) (x : Cube n) :
    lowPhase φ θ x-lowPhase a b x = lowPhase (φ-a) (fun j => θ j-b j) x := by
  have hs : (∑ j,if x j then θ j-b j else 0) =
      (∑ j,if x j then θ j else 0)-(∑ j,if x j then b j else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    cases x j <;> simp
  unfold lowPhase
  rw [hs]
  ring

theorem error_shift_low {n : ℕ} (h : Cube n → ℝ) (φ a : ℝ) (θ b : Fin n → ℝ) :
    normalizedFrobError (lowPhase φ θ) (fun x => lowPhase a b x+h x) =
      normalizedFrobError (lowPhase (φ-a) (fun j => θ j-b j)) h := by
  rw [normalizedFrobError_eq,normalizedFrobError_eq]
  apply congrArg cubeAvg
  funext x
  have he : lowPhase φ θ x-(lowPhase a b x+h x) =
      lowPhase (φ-a) (fun j => θ j-b j) x-h x := by rw [← lowPhase_sub];ring
  rw [he]

theorem shifted_infimum_sandwich {n : ℕ} (h : Cube n → ℝ)
    (hzero : cubeAvg h=0) (hlocal : ∀ j,cubeAvg (fun x => h x*walsh (bitCube j) x)=0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hh : ∀ x,|h x| ≤ δ) (a : ℝ) (b : Fin n → ℝ) :
    cubeAvg (fun x => h x^2)-(phaseConstant n*δ)^4/12 ≤
      bestProductError (fun x => lowPhase a b x+h x) ∧
    bestProductError (fun x => lowPhase a b x+h x) ≤ cubeAvg (fun x => h x^2) := by
  constructor
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨⟨φ,θ⟩,rfl⟩
    (try dsimp only)
    rw [error_shift_low]
    exact global_error_lower h hzero hlocal δ hδ hh _ _
  · have he := csInf_le (errorRange_bddBelow (fun x => lowPhase a b x+h x))
      (Set.mem_range_self (a,b))
    dsimp only at he
    rw [error_shift_low] at he
    simp only [sub_self] at he
    exact he.trans (identity_error_upper h)

theorem universal_global_infimum_bound {n : ℕ} (α : Cube n → ℝ) :
    (∑ s,(highPart α s)^2)-(phaseConstant n*(∑ s,|highPart α s|))^4/12 ≤
      bestProductError (walshPhase α) ∧
    bestProductError (walshPhase α) ≤ ∑ s,(highPart α s)^2 := by
  obtain ⟨hz,hl⟩ := highPart_orthogonal α
  have he := shifted_infimum_sandwich (walshPhase (highPart α)) hz hl
    (∑ s,|highPart α s|) (Finset.sum_nonneg (fun s _ => abs_nonneg _))
    (abs_walshPhase_le (highPart α))
    (α (zeroCube n)+∑ j,α (bitCube j)) (fun j => -2*α (bitCube j))
  rw [← betaStar_lowPhase α,← walshPhase_low_high α,cubeAvg_walshPhase_sq] at he
  exact he

theorem universal_global_infimum_abs {n : ℕ} (α : Cube n → ℝ) :
    |bestProductError (walshPhase α)-(∑ s,(highPart α s)^2)| ≤
      (phaseConstant n)^4/12*(∑ s,|highPart α s|)^4 := by
  obtain ⟨hl,hu⟩ := universal_global_infimum_bound α
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  nlinarith [hl]

theorem universal_global_infimum_max {n : ℕ} (α : Cube n → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hmax : ∀ s,|highPart α s| ≤ M) :
    |bestProductError (walshPhase α)-(∑ s,(highPart α s)^2)| ≤
      (phaseConstant n*(2:ℝ)^n)^4/12*M^4 := by
  have hz : 0 ≤ ∑ s,|highPart α s| := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hsum : (∑ s,|highPart α s|) ≤ (2:ℝ)^n*M := by
    have he := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hmax s)
    simpa only [Finset.sum_const,Finset.card_univ,card_cube,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using! he
  calc
    _ ≤ (phaseConstant n)^4/12*(∑ s,|highPart α s|)^4 := universal_global_infimum_abs α
    _ ≤ (phaseConstant n)^4/12*((2:ℝ)^n*M)^4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hsum 4) (by positivity)
    _ = _ := by ring

theorem product_error_continuous {n : ℕ} (h : Cube n → ℝ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => normalizedFrobError (lowPhase p.1 p.2) h) := by
  have hphase (x : Cube n) : Continuous (fun p : ℝ × (Fin n → ℝ) => lowPhase p.1 p.2 x) := by
    unfold lowPhase
    apply continuous_fst.add
    apply continuous_finsetSum
    intro j _
    cases x j
    · simp only [Bool.false_eq_true,if_false]
      fun_prop
    · simp only [if_true]
      fun_prop
  simp_rw [normalizedFrobError_normsq]
  unfold cubeAvg
  apply continuous_const.mul
  apply continuous_finsetSum
  intro x _
  have hx := hphase x
  unfold phaseValue
  fun_prop

theorem bestProductError_attained {n : ℕ} (h : Cube n → ℝ) :
    ∃ (φ : ℝ) (θ : Fin n → ℝ), normalizedFrobError (lowPhase φ θ) h=bestProductError h ∧
      ∀ (a : ℝ) (b : Fin n → ℝ),
        normalizedFrobError (lowPhase φ θ) h ≤ normalizedFrobError (lowPhase a b) h := by
  let K : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc (-Real.pi) Real.pi ×ˢ {θ | ∀ j,θ j ∈ Set.Icc (-Real.pi) Real.pi}
  have hK : IsCompact K :=
    isCompact_Icc.prod (isCompact_pi_infinite (fun _ : Fin n => isCompact_Icc))
  have hne : K.Nonempty := by
    refine ⟨(0,fun _ => 0),?_⟩
    constructor
    · constructor <;> linarith [Real.pi_pos]
    · intro j
      constructor <;> linarith [Real.pi_pos]
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne (product_error_continuous h).continuousOn
  have hglobal (a : ℝ) (b : Fin n → ℝ) :
      normalizedFrobError (lowPhase p.1 p.2) h ≤ normalizedFrobError (lowPhase a b) h := by
    let q : ℝ × (Fin n → ℝ) := (Complex.arg (phaseValue a),fun j => Complex.arg (phaseValue (b j)))
    have hq : q ∈ K := by
      exact ⟨abs_le.mp (Complex.abs_arg_le_pi _),fun j => abs_le.mp (Complex.abs_arg_le_pi _)⟩
    have heq : normalizedFrobError (lowPhase q.1 q.2) h = normalizedFrobError (lowPhase a b) h := by
      rw [normalizedFrobError_normsq,normalizedFrobError_normsq]
      apply congrArg cubeAvg
      funext x
      rw [show phaseValue (lowPhase q.1 q.2 x)=phaseValue (lowPhase a b x) from lowPhase_unwrap a b x]
    exact (hmin hq).trans_eq heq
  refine ⟨p.1,p.2,?_,hglobal⟩
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨⟨a,b⟩,rfl⟩
    exact hglobal a b
  · exact csInf_le (errorRange_bddBelow h) (Set.mem_range_self p)

theorem universal_global_minimum {n : ℕ} (α : Cube n → ℝ) :
    ∃ (φ : ℝ) (θ : Fin n → ℝ),
      (∀ (a : ℝ) (b : Fin n → ℝ), normalizedFrobError (lowPhase φ θ) (walshPhase α) ≤
        normalizedFrobError (lowPhase a b) (walshPhase α)) ∧
      |normalizedFrobError (lowPhase φ θ) (walshPhase α)-(∑ s,(highPart α s)^2)| ≤
        (phaseConstant n)^4/12*(∑ s,|highPart α s|)^4 := by
  obtain ⟨φ,θ,heq,hmin⟩ := bestProductError_attained (walshPhase α)
  refine ⟨φ,θ,hmin,?_⟩
  rw [heq]
  exact universal_global_infimum_abs α

def rzProductMatrix {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) : Matrix (Cube n) (Cube n) ℂ :=
  Matrix.diagonal (fun x => phaseValue φ *
    ∏ j,if x j then phaseValue (θ j/2) else phaseValue (-θ j/2))

theorem rzProductMatrix_eq {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) :
    rzProductMatrix φ θ = diagonalUnitary (lowPhase (φ-∑ j,θ j/2) θ) := by
  apply congrArg Matrix.diagonal
  funext x
  have hprod : (∏ j,if x j then phaseValue (θ j/2) else phaseValue (-θ j/2)) =
      phaseValue (∑ j,if x j then θ j/2 else -θ j/2) := by
    unfold phaseValue
    rw [Complex.ofReal_sum,Finset.mul_sum,Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    cases x j <;> simp
  rw [hprod]
  have hsum : φ+(∑ j,if x j then θ j/2 else -θ j/2) =
      lowPhase (φ-∑ j,θ j/2) θ x := by
    unfold lowPhase
    have hs : (∑ j,if x j then θ j/2 else -θ j/2) =
        -(∑ j,θ j/2)+(∑ j,if x j then θ j else 0) := by
      rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases x j <;> simp
      all_goals ring
    rw [hs]
    ring
  change phaseValue φ*phaseValue _ = phaseValue _
  rw [show phaseValue φ*phaseValue (∑ j,if x j then θ j/2 else -θ j/2) =
      phaseValue (φ+∑ j,if x j then θ j/2 else -θ j/2) by
        simp only [phaseValue,Complex.ofReal_add,mul_add,Complex.exp_add],hsum]

def rzProductError {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (f : Cube n → ℝ) : ℝ :=
  ((2:ℝ)^n)⁻¹*frobNormSq (rzProductMatrix φ θ-diagonalUnitary f)

theorem rzProductError_eq {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) (f : Cube n → ℝ) :
    rzProductError φ θ f=normalizedFrobError (lowPhase (φ-∑ j,θ j/2) θ) f := by
  rw [rzProductError,rzProductMatrix_eq]
  rfl

theorem universal_rz_minimum {n : ℕ} (α : Cube n → ℝ) :
    ∃ (φ : ℝ) (θ : Fin n → ℝ),
      rzProductError φ θ (walshPhase α)=bestProductError (walshPhase α) ∧
      (∀ (a : ℝ) (b : Fin n → ℝ),rzProductError φ θ (walshPhase α) ≤
        rzProductError a b (walshPhase α)) ∧
      |rzProductError φ θ (walshPhase α)-(∑ s,(highPart α s)^2)| ≤
        (phaseConstant n)^4/12*(∑ s,|highPart α s|)^4 := by
  obtain ⟨φ,θ,heq,hmin⟩ := bestProductError_attained (walshPhase α)
  refine ⟨φ+∑ j,θ j/2,θ,?_,?_,?_⟩
  · simpa only [rzProductError_eq,add_sub_cancel_right] using! heq
  · intro a b
    simpa only [rzProductError_eq,add_sub_cancel_right] using! hmin (a-∑ j,b j/2) b
  · rw [rzProductError_eq,add_sub_cancel_right,heq]
    exact universal_global_infimum_abs α

end Qatlib.Papers.KoopmanSim26.SpectralRep

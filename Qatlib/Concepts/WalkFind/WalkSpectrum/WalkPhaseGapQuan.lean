/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.WalkPhaseGapStat
import Qatlib.Concepts.WalkFind.UniqueCollision.WalkUnitaryQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.WalkStartFixedQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonSpectrumAux
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonPopulationAux

/-!
# Phase gaps for the Johnson walk

The module proves `WalkPhaseGap` by comparing Johnson-walk eigenvalues with ideal block phases
and controlling the start-vector weight. It also lifts eigenvectors of powers to eigenvectors of
the walk and bounds the amplified phases away from zero and π.

The size estimates and the three-dimensional determinant calculation support the phase analysis
and the large-overlap algorithm bound. See [Ambainis2007ElementDistinctness] for the
mathematical background.

## Main statements

* `walkPhaseGap`: eigenvalue distance bounds from 1 and −1.
* `jwWalk_powered_phase_gap`: a phase gap after the prescribed walk power.
* `jwAlgorithm_large_overlap`: an iteration and amplitude bound.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

/-- Under the half-step size bounds, the Johnson walk preserves the Hermitian squared norm. -/
theorem jwWalk_normSq (k N r : ℕ) (h1 : k ≤ N - r) (h2 : k ≤ r + 1)
    (v : Fin (2 * k + 1) → ℂ) :
    (star (jwWalk k N r *ᵥ v) ⬝ᵥ (jwWalk k N r *ᵥ v)) = star v ⬝ᵥ v := by
  have hu := (walkUnitary k N r h1 h2).2.2.1
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hu,
    Matrix.vecMul_one]

/-- For `0 ≤ ε ≤ 1`, the squared distances of the ideal block phase from 1 and −1 are `4 * ε`
and `4 * (1 - ε)`, respectively. -/
theorem jwIdealBlockPhase_chords (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Complex.normSq (jwIdealBlockPhase ε - 1) = 4*ε ∧
    Complex.normSq (jwIdealBlockPhase ε + 1) = 4*(1-ε) := by
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ ε-ε*ε)
  constructor <;> simp [jwIdealBlockPhase, Complex.normSq_apply]
  all_goals nlinarith

/-- The two-dimensional ideal block obtained by multiplying `jwD2 ε` by the diagonal signs 1 and
−1. -/
noncomputable def jwIdealBlock (ε : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of (jwD2 ε) * Matrix.diagonal (fun b => if b then -1 else 1)

/-- The vector with coordinates 1 and `-I` is an eigenvector of `jwIdealBlock ε` with eigenvalue
`jwIdealBlockPhase ε`. -/
theorem jwIdealBlock_eigen (ε : ℝ) :
    jwIdealBlock ε *ᵥ (fun b => if b then -Complex.I else 1) =
      jwIdealBlockPhase ε • (fun b => if b then -Complex.I else 1) := by
  funext b
  cases b <;> simp [jwIdealBlock, jwIdealBlockPhase, jwD2, Matrix.mulVec, dotProduct,
    Matrix.mul_diagonal, Matrix.of_apply]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/-- Under the half-step size bounds, any Johnson-walk eigenvalue with a nonzero eigenvector has
norm 1. -/
theorem jwWalk_eigenvalue_unit_norm (k N r : ℕ) (h1 : k ≤ N-r) (h2 : k ≤ r+1)
    (μ : ℂ) (v : Fin (2*k+1) → ℂ) (heigen : jwWalk k N r *ᵥ v = μ • v)
    (hv : v ≠ 0) : ‖μ‖ = 1 := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i,hi⟩ := hex
  have hp : 0 < ∑ j, ‖v j‖^2 :=
    lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi))
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i))
  have hdot : star v ⬝ᵥ v = ((∑ j, ‖v j‖^2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hn : star v ⬝ᵥ v ≠ 0 := by rw [hdot]; exact_mod_cast ne_of_gt hp
  have h := jwWalk_normSq k N r h1 h2 v
  rw [heigen, star_smul, smul_dotProduct, dotProduct_smul] at h
  have he : star μ * μ = 1 := by
    apply mul_right_cancel₀ hn
    simpa only [smul_eq_mul, mul_assoc, one_mul] using h
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at he
  have hs : ‖μ‖^2 = 1 := by exact_mod_cast he
  nlinarith [norm_nonneg μ]

/-- The stated population bound with `k ≥ 1` implies `k < N - r`. -/
theorem jwWalk_size_physical (k N r : ℕ) (hk : 1 ≤ k)
    (hsize : (8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) *
      (k + 1) * k : ℝ) ≤ N - r) : k < N - r := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR
  have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 4) := one_le_pow₀ (by norm_num)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hlow : 8 * (k : ℝ) ≤
      8 * Real.pi ^ 2 * (k : ℝ) ^ 3 * (r + 1) * (2 : ℝ) ^ (k + 4) * (k + 1) * k := by
    calc
      _ = 8 * 1 * 1 * 1 * 1 * 1 * (k : ℝ) := by ring
      _ ≤ _ := by gcongr
  have hreal : (k : ℝ) + r < N := by linarith
  have hnat : k + r < N := by exact_mod_cast hreal
  omega

/-- The stated population bound with `k ≥ 1` implies `2 * k * (r + 1) ≤ N`. -/
theorem jwWalk_size_population (k N r : ℕ) (hk : 1 ≤ k)
    (hsize : (8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) *
      (k + 1) * k : ℝ) ≤ N-r) : 2*k*(r+1) ≤ N := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hk2 : (1 : ℝ) ≤ (k : ℝ)^2 := one_le_pow₀ hkR
  have hk3 : (k : ℝ) ≤ (k : ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have htwo : (1 : ℝ) ≤ (2 : ℝ)^(k+4) := one_le_pow₀ (by norm_num)
  have hk1 : (1 : ℝ) ≤ (k : ℝ)+1 := by linarith
  have hlow : 2*(k : ℝ)*(r+1) ≤
      8*Real.pi^2*(k : ℝ)^3*(r+1)*(2 : ℝ)^(k+4)*(k+1)*k := by
    calc
      _ = 2*1*(k : ℝ)*(r+1)*1*1*1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have hreal : 2*(k : ℝ)*(r+1) ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) r]
  exact_mod_cast hreal

/-- The stated population bound implies the weaker estimate `512 * π² * k * (r + 1) ≤ N - r`
needed to control the amplified phase error. -/
theorem jwWalk_size_phase_error (k N r : ℕ) (hk : 1 ≤ k)
    (hsize : (8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) *
      (k + 1) * k : ℝ) ≤ N-r) : (512*Real.pi^2*k*(r+1) : ℝ) ≤ N-r := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ)^2 := one_le_pow₀ hkR
  have hk3 : (k : ℝ) ≤ (k : ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have htwo : (32 : ℝ) ≤ (2 : ℝ)^(k+4) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 5 ≤ k+4)
    norm_num at h
    exact h
  have hk1 : (2 : ℝ) ≤ (k : ℝ)+1 := by linarith
  calc
    _ = 8*Real.pi^2*(k : ℝ)*(r+1)*32*2*1 := by ring
    _ ≤ 8*Real.pi^2*(k : ℝ)^3*(r+1)*(2 : ℝ)^(k+4)*(k+1)*k := by gcongr
    _ ≤ _ := hsize

/-- Under the stated size assumptions, coordinate zero of `jwStart` is nonzero and carries at
least half its squared Euclidean norm. -/
theorem jwWalk_start_population (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hsize : (8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) *
      (k + 1) * k : ℝ) ≤ N-r) :
    jwL2Norm (jwStart k N r)^2 ≤ 2*Complex.normSq (jwStart k N r 0) ∧
      jwStart k N r 0 ≠ 0 := by
  have hkNr := jwWalk_size_physical k N r hk hsize
  have hrN : r < N := by omega
  have hkN : k ≤ N-r := by omega
  have hcount : 0 < jwCnt k N r 0 false := by
    simp only [jwCnt,Nat.choose_zero_right,Nat.sub_zero,Bool.false_eq_true,
      ↓reduceIte,one_mul]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (by omega)
  have hs0 : jwStart k N r 0 ≠ 0 := by
    have hp : (0 : ℝ) < jwCnt k N r 0 false := by exact_mod_cast hcount
    have hcoord : jwStart k N r 0 = (Real.sqrt (jwCnt k N r 0 false : ℝ) : ℂ) := by
      simp [jwStart,jwPsiCoord]
    rw [hcoord]
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hp)
  have hmass : jwL2Norm (jwStart k N r)^2 ≤ 2*Complex.normSq (jwStart k N r 0) := by
    have h := jwStart_zero_population_half k N r (by omega) hkr hkN (by omega)
      (jwWalk_size_population k N r hk hsize)
    rw [jwL2Norm_sq]
    simp only [Complex.normSq_eq_norm_sq,jwStart_normSq]
    have hzero : ‖jwStart k N r 0‖^2 = (jwCnt k N r 0 false : ℝ) := by
      simp [jwStart,jwPsiCoord,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hzero]
    exact h
  exact ⟨hmass,hs0⟩

/-- Establishes the eigenvalue gap bounds from 1 and −1 specified by `WalkPhaseGap`. -/
theorem walkPhaseGap : WalkPhaseGap := by
  intro k N r hk hkr hr hsize μ v heigen horth hv
  have hkNr := jwWalk_size_physical k N r hk hsize
  have hrN : r < N := by omega
  have hkN : k ≤ N-r := by omega
  obtain ⟨hmass,hs0⟩ := jwWalk_start_population k N r hk hkr hsize
  have horth' : star v ⬝ᵥ jwStart k N r = 0 := horth
  have hgap := jwWalk_eigenvalue_gap_one_of_start_weight k N r hrN hkN (by omega)
    μ v (jwStart k N r) heigen hv horth' hmass hs0
  have herr := jwSpectral_error_dominates_projected k N r hk hrN
  constructor
  · linarith
  · exact jwWalk_eigenvalue_gap_neg_one k N r hk hrN hkN hr μ v heigen hv

/-- Establishes `WalkPhaseGap`, the Johnson-walk eigenvalue distance bounds under the stated
size and start-orthogonality conditions. See [Ambainis2007ElementDistinctness]. -/
theorem walkPhaseGap_answer : WalkPhaseGap := walkPhaseGap

/-- Under the stated size conditions, a Johnson-walk eigenvalue with a nonzero eigenvector
orthogonal to `jwStart` lies within `2 * sqrt 2 * sqrt (k / (N - r))` of an ideal block
phase or its conjugate. -/
theorem jwWalk_eigenvalue_localization (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (_hr : 2*k ≤ r+1)
    (hsize : (8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) *
      (k + 1) * k : ℝ) ≤ N-r)
    (μ : ℂ) (v : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r *ᵥ v = μ • v)
    (horth : (∑ i, star (v i)*jwStart k N r i) = 0) (hv : v ≠ 0) :
    ∃ j : Fin k,
      ‖μ-jwIdealBlockPhase ((k-j.val : ℝ)/(r+1))‖ ≤
        2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)) ∨
      ‖μ-star (jwIdealBlockPhase ((k-j.val : ℝ)/(r+1)))‖ ≤
        2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)) := by
  have hkNr := jwWalk_size_physical k N r hk hsize
  have hrN : r < N := by omega
  obtain ⟨hmass,hs0⟩ := jwWalk_start_population k N r hk hkr hsize
  obtain ⟨j,hj⟩ := jwWalk_eigenvalue_localization_of_start_weight k N r hrN (by omega)
    (by omega) μ v (jwStart k N r) heigen hv horth hmass hs0
  have hD : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hrN
    linarith
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg k) (le_of_lt hD))
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : (2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)))^2 = 8*k/(N-r) := by
    rw [mul_pow,mul_pow,hs,hs2]
    ring
  have hd : 0 ≤ 2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)) := by positivity
  have hbound : ∀ z : ℂ, Complex.normSq (z-μ) ≤ 8*k/(N-r) →
      ‖μ-z‖ ≤ 2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)) := by
    intro z hz
    rw [Complex.normSq_eq_norm_sq,← hsq,norm_sub_rev] at hz
    exact (sq_le_sq₀ (norm_nonneg _) hd).mp hz
  refine ⟨j,?_⟩
  exact hj.imp (hbound _) (hbound _)

/-- Under the stated size conditions, an eigenvalue `ν` of a walk power on a nonzero
start-orthogonal vector equals `μ ^ t` for a walk eigenvalue `μ` with a nonzero
start-orthogonal eigenvector. -/
theorem jwWalk_powered_eigenvector_lift (k N r t : ℕ) (hk : 1 ≤ k)
    (hkr : k ≤ r) (_hr : 2 * k ≤ r + 1)
    (hsize : (8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) *
      (k + 1) * k : ℝ) ≤ N - r)
    (ν : ℂ) (v : Fin (2 * k + 1) → ℂ)
    (heigen : jwWalk k N r ^ t *ᵥ v = ν • v)
    (horth : (∑ i, star (v i) * jwStart k N r i) = 0) (hv : v ≠ 0) :
    ∃ (μ : ℂ) (w : Fin (2 * k + 1) → ℂ),
      jwWalk k N r *ᵥ w = μ • w ∧
      (∑ i, star (w i) * jwStart k N r i) = 0 ∧ w ≠ 0 ∧ μ ^ t = ν := by
  have hNr := jwWalk_size_physical k N r hk hsize
  exact jw_unitary_pow_eigenvector_lift (2 * k + 1) t (jwWalk k N r)
    (jwStart k N r) v ν ((walkUnitary k N r (by omega) (by omega)).2.2.1)
    (walkStartFixed k N r hk hkr hNr) heigen horth hv

/-- For `1 ≤ k ≤ r`, the arc parameter `jwEpsArc k r` is strictly positive and at most 1. -/
theorem jwEpsArc_bounds (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    0 < jwEpsArc k r ∧ jwEpsArc k r ≤ 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkrR : (k : ℝ) ≤ r+1 := by exact_mod_cast (by omega : k ≤ r+1)
  have hsk : 1 ≤ Real.sqrt (k : ℝ) := by
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg k)).mpr (by nlinarith)
  have hskp : 0 < Real.sqrt (k : ℝ) := by linarith
  have hsr : Real.sqrt (k : ℝ) ≤ Real.sqrt (r+1 : ℝ) := Real.sqrt_le_sqrt hkrR
  have hsrp : 0 < Real.sqrt (r+1 : ℝ) := hskp.trans_le hsr
  have hp : 0 < Real.pi := Real.pi_pos
  have hsmall : 1/(Real.pi*Real.sqrt (r+1 : ℝ)) ≤ 1/(Real.pi*Real.sqrt (k : ℝ)) :=
    one_div_le_one_div_of_le (mul_pos hp hskp) (by gcongr)
  have hc : 3 < (Real.pi-1)*Real.pi := by nlinarith [Real.pi_gt_three]
  have hlo : 1/(Real.pi*Real.sqrt (k : ℝ)) < (Real.pi-1)/(3*Real.sqrt (k : ℝ)) := by
    apply (div_lt_div_iff₀ (mul_pos hp hskp) (by positivity)).mpr
    have hm := mul_lt_mul_of_pos_right hc hskp
    nlinarith
  have hhi : (Real.pi-1)/(3*Real.sqrt (k : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_lt_four]
  have hnonneg : 0 ≤ 1/(Real.pi*Real.sqrt (r+1 : ℝ)) := by positivity
  unfold jwEpsArc
  constructor <;> linarith

/-- In the stated large-overlap regime, there is an iteration count bounded by `8 / (jwEpsArc *
jwAlpha)` with marked amplitude at least `jwEpsArc³ / 1000` and the specified query bound. -/
theorem jwAlgorithm_large_overlap (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hsize : (8*Real.pi^2*(k^3)*(r+1)*(2^(k+4))*(k+1)*k : ℝ) ≤ N-r)
    (I : Finset (Fin N)) (hI : I.card = k)
    (hlarge : jwEpsArc k r^2/200 ≤ jwAlpha k N r) :
    ∃ t1 : ℕ, (t1 : ℝ) ≤ 8/(jwEpsArc k r*jwAlpha k N r) ∧
      jwEpsArc k r^3/1000 ≤ ‖jwMarkedAmplitude k N r t1 (jwT2 k r) I‖ ∧
      ((r+2*t1*jwT2 k r : ℕ) : ℝ) ≤
        (r : ℝ)+16*(jwT2 k r : ℝ)/(jwEpsArc k r*jwAlpha k N r) := by
  have hkNr := jwWalk_size_physical k N r hk hsize
  obtain ⟨he,he1⟩ := jwEpsArc_bounds k r hk hkr
  obtain ⟨_,_,_,ha,_⟩ := alphaFromInput k N r hk hkr hkNr
  have hbig : jwEpsArc k r^3/1000 ≤ jwAlpha k N r := by
    have hmul := mul_nonneg (sq_nonneg (jwEpsArc k r)) (sub_nonneg.mpr he1)
    nlinarith [sq_nonneg (jwEpsArc k r)]
  refine ⟨0,?_,?_,?_⟩
  · simp only [Nat.cast_zero]
    positivity
  · rw [jwMarkedAmplitude_zero_eq_alpha k N r (jwT2 k r) hkr hkNr I hI,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
    exact hbig
  · simp only [mul_zero,zero_mul,add_zero]
    have hterm : 0 ≤ 16*(jwT2 k r : ℝ)/(jwEpsArc k r*jwAlpha k N r) := by positivity
    linarith

/-- For `e` and `f` in `[0, 1]`, factors the displayed three-dimensional block determinant into
`1 - μ` and `μ² - 2 * (1 - 2 * e - 2 * f + 2 * e * f) * μ + 1`. -/
theorem jwThreeBlock_det_factor (e f : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hf : 0 ≤ f) (hf1 : f ≤ 1) (μ : ℂ) :
    let a : ℂ := (1-2*e : ℝ)
    let b : ℂ := (2*Real.sqrt (e-e*e) : ℝ)
    let c : ℂ := (-1+2*f : ℝ)
    let d : ℂ := (2*Real.sqrt (f-f*f) : ℝ)
    Matrix.det (!![a,b,0; b*c,-a*c,d; b*d,-a*d,-c] - μ • (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      (1-μ)*(μ^2-2*(1-2*e-2*f+2*e*f : ℝ)*μ+1) := by
  have hsE : (Real.sqrt (e-e*e) : ℂ)^2 = (e-e*e : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by nlinarith : 0 ≤ e-e*e)
  have hsF : (Real.sqrt (f-f*f) : ℂ)^2 = (f-f*f : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by nlinarith : 0 ≤ f-f*f)
  push_cast at hsE hsF
  have hA : (1-2*(e:ℂ))^2 + 4*(Real.sqrt (e-e*e) : ℂ)^2 = 1 := by
    linear_combination 4*hsE
  have hB : (-1+2*(f:ℂ))^2 + 4*(Real.sqrt (f-f*f) : ℂ)^2 = 1 := by
    linear_combination 4*hsF
  (try dsimp only)
  simp only [Matrix.det_fin_three,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply]
  norm_num
  push_cast
  linear_combination (1+(-1+2*(f:ℂ))*μ)*hA +
    ((1-2*(e:ℂ))^2+4*(Real.sqrt (e-e*e) : ℂ)^2-(1-2*(e:ℂ))*μ)*hB

/-- For `1 ≤ r < N`, factors `det (jwWalk 1 N r - μ • 1)` into `1 - μ` and the stated quadratic
factor. -/
theorem jwWalk_one_det_factor (N r : ℕ) (hr : 1 ≤ r) (hrN : r < N) (μ : ℂ) :
    Matrix.det (jwWalk 1 N r - μ • (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      (1-μ)*(μ^2-2*(1-2/(N-r)-2/(r+1)+2/((N-r)*(r+1)) : ℝ)*μ+1) := by
  let e : ℝ := 1/(N-r)
  let f : ℝ := 1/(r+1)
  have he : 0 ≤ e := by
    dsimp [e]
    have h : (r : ℝ) < N := by exact_mod_cast hrN
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (le_of_lt h))
  have he1 : e ≤ 1 := by
    dsimp [e]
    have h : (r : ℝ)+1 ≤ N := by exact_mod_cast (by omega : r+1 ≤ N)
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < N-r)).mpr
    linarith
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hf1 : f ≤ 1 := by
    dsimp [f]; apply (div_le_iff₀ (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hm : jwWalk 1 N r =
      !![(1-2*e : ℂ),(2*Real.sqrt (e-e*e) : ℂ),0;
         (2*Real.sqrt (e-e*e) : ℂ)*(-1+2*f : ℝ),-(1-2*e : ℂ)*(-1+2*f : ℝ),(2*Real.sqrt (f-f*f) : ℝ);
         (2*Real.sqrt (e-e*e) : ℂ)*(2*Real.sqrt (f-f*f) : ℝ),
         -(1-2*e : ℂ)*(2*Real.sqrt (f-f*f) : ℝ),-(-1+2*f : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jwWalk,jwStep1,jwStep2,jwPsiCoord,jwPhiCoord,jwD2,
        Matrix.mul_apply,Fin.sum_univ_succ,e,f]
    all_goals ring
  have h := jwThreeBlock_det_factor e f he he1 hf hf1 μ
  push_cast at h hm
  rw [hm,h]
  dsimp [e,f]
  congr 2
  push_cast
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

/-- Under the stated size conditions, a start-orthogonal Johnson-walk eigenvalue raised to `jwT2
k r` has an angle in the prescribed closed arc that differs from π. -/
theorem jwWalk_eigenphase_amplified (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hr : 2*k ≤ r+1)
    (hsize : (8*Real.pi^2*(k^3)*(r+1)*(2^(k+4))*(k+1)*k : ℝ) ≤ N-r)
    (μ : ℂ) (v : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r *ᵥ v = μ • v)
    (horth : (∑ i, star (v i)*jwStart k N r i) = 0) (hv : v ≠ 0) :
    ∃ θ : ℝ, jwEpsArc k r ≤ θ ∧ θ ≤ 2*Real.pi-jwEpsArc k r ∧
      θ ≠ Real.pi ∧ μ^jwT2 k r = Complex.exp (Complex.I*θ) := by
  have hkNr := jwWalk_size_physical k N r hk hsize
  have hunit := jwWalk_eigenvalue_unit_norm k N r (by omega) (by omega) μ v heigen hv
  obtain ⟨j,hj⟩ := jwWalk_eigenvalue_localization k N r hk hkr hr hsize μ v heigen horth hv
  let e : ℝ := (k-j.val : ℝ)/(r+1)
  let q : ℝ := 2*Real.arcsin (Real.sqrt e)
  let K : ℝ := Real.sqrt (k : ℝ)
  let t : ℝ := jwT2 k r
  let δ : ℝ := 2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r))
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : 0 < K := Real.sqrt_pos.mpr (by linarith)
  have hK1 : 1 ≤ K := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg k)).mpr (by simpa)
  have hje : (j.val : ℝ)+1 ≤ k := by exact_mod_cast j.isLt
  have hrR : (2 : ℝ)*k ≤ r+1 := by exact_mod_cast hr
  have he : 0 ≤ e := div_nonneg (by linarith) (by positivity)
  have hehalf : e ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < r+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j.val]
  have hexp : jwIdealBlockPhase e = Complex.exp (Complex.I*q) := by
    have h := jw_diffusion_phase_exp e he (by linarith)
    simpa only [jwIdealBlockPhase,q,Complex.ofReal_sub,Complex.ofReal_mul,
      Complex.ofReal_one,Complex.ofReal_ofNat] using h
  have hconj : star (jwIdealBlockPhase e) = Complex.exp (Complex.I*(-q : ℝ)) := by
    rw [hexp,Complex.star_def,← Complex.exp_conj]
    congr 1
    simp
  have hphase : ∃ a : ℝ, |a| ≤ Real.pi/2*δ ∧
      (μ = Complex.exp (Complex.I*(q+a : ℝ)) ∨ μ = Complex.exp (Complex.I*(-q+a : ℝ))) := by
    rcases hj with hj | hj
    · rw [hexp] at hj
      obtain ⟨a,ha,hμ⟩ := jw_unit_circle_phase_transport μ hunit q
      refine ⟨a,?_,Or.inl hμ⟩
      exact ha.trans (mul_le_mul_of_nonneg_left hj (by positivity))
    · rw [hconj] at hj
      obtain ⟨a,ha,hμ⟩ := jw_unit_circle_phase_transport μ hunit (-q)
      refine ⟨a,?_,Or.inr hμ⟩
      exact ha.trans (mul_le_mul_of_nonneg_left hj (by positivity))
  obtain ⟨a,ha,hμ⟩ := hphase
  have htδ : t*δ ≤ 1/(6*Real.pi*K) :=
    jwT2_perturbation_bound k N r hk hr (jwWalk_size_phase_error k N r hk hsize)
  have hta : |t*a| ≤ 1/(12*K) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ t)]
    calc
      _ ≤ t*(Real.pi/2*δ) := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (Real.pi/2)*(t*δ) := by ring
      _ ≤ (Real.pi/2)*(1/(6*Real.pi*K)) := mul_le_mul_of_nonneg_left htδ (by positivity)
      _ = _ := by field_simp; ring
  have hblocks := jwIdealBlock_amplification_bounds k r hk hr j
  have hqlo : Real.pi/(3*K) ≤ t*q := hblocks.1
  have hqhi : t*q ≤ 3 := hblocks.2.1
  have heps : jwEpsArc k r ≤ (Real.pi-1)/(3*K) := by
    dsimp [jwEpsArc,K]
    exact sub_le_self _ (by positivity)
  have h12 : (1 : ℝ)/(12*K) ≤ 1/12 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hangle : ∀ b : ℝ, |b| ≤ 1/(12*K) →
      jwEpsArc k r ≤ t*q+b ∧ t*q+b < Real.pi := by
    intro b hb
    have hb' := abs_le.mp hb
    have hid : Real.pi/(3*K)-1/(12*K) = (Real.pi-1)/(3*K)+1/(4*K) := by
      field_simp
      ring
    constructor
    · have hpos : 0 ≤ 1/(4*K) := by positivity
      linarith
    · linarith [Real.pi_gt_d2]
  obtain ⟨_,heps1⟩ := jwEpsArc_bounds k r hk hkr
  rcases hμ with hμ | hμ
  · obtain ⟨hlo,hhi⟩ := hangle (t*a) hta
    refine ⟨t*q+t*a,hlo,?_,ne_of_lt hhi,?_⟩
    · linarith [Real.pi_gt_three]
    · rw [hμ,← Complex.exp_nat_mul]
      congr 1
      dsimp [t]
      push_cast
      ring
  · obtain ⟨hlo,hhi⟩ := hangle (-t*a) (by simpa [abs_mul] using hta)
    refine ⟨2*Real.pi-(t*q-t*a),?_,?_,?_,?_⟩
    · linarith [Real.pi_gt_three]
    · linarith
    · linarith
    · have hpow : μ^jwT2 k r = Complex.exp (Complex.I*(-(t*q-t*a) : ℝ)) := by
        rw [hμ,← Complex.exp_nat_mul]
        congr 1
        dsimp [t]
        push_cast
        ring
      rw [hpow]
      symm
      rw [show Complex.I*(2*Real.pi-(t*q-t*a) : ℝ) =
          (2*Real.pi : ℝ)*Complex.I+Complex.I*(-(t*q-t*a) : ℝ) by push_cast; ring,
        Complex.exp_add]
      simp [Complex.exp_two_pi_mul_I]

/-- Under the stated size conditions, an eigenvalue of the prescribed walk power with a nonzero
start-orthogonal eigenvector has a phase in the specified arc and different from π. -/
theorem jwWalk_powered_phase_gap (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hr : 2*k ≤ r+1)
    (hsize : (8*Real.pi^2*(k^3)*(r+1)*(2^(k+4))*(k+1)*k : ℝ) ≤ N-r)
    (ν : ℂ) (v : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r^jwT2 k r *ᵥ v = ν • v)
    (horth : (∑ i, star (v i)*jwStart k N r i) = 0) (hv : v ≠ 0) :
    ∃ θ : ℝ, jwEpsArc k r ≤ θ ∧ θ ≤ 2*Real.pi-jwEpsArc k r ∧
      θ ≠ Real.pi ∧ ν = Complex.exp (Complex.I*θ) := by
  obtain ⟨μ,w,hμ,horthw,hw,hpow⟩ := jwWalk_powered_eigenvector_lift k N r (jwT2 k r)
    hk hkr hr hsize ν v heigen horth hv
  obtain ⟨θ,hlo,hhi,hne,hphase⟩ :=
      jwWalk_eigenphase_amplified k N r hk hkr hr hsize μ w hμ horthw hw
  exact ⟨θ,hlo,hhi,hne,hpow ▸ hphase⟩

end Qatlib.Concepts.WalkFind.WalkSpectrum

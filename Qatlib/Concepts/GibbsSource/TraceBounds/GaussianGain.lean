/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSpectralTraceLeakage
public import Qatlib.Concepts.GibbsSource.SourceForms.PhysicalCoordinates
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section


/-! # Hermitian Gaussian contraction for arbitrary finite spectral flags

The two signs of every energy difference are paired before estimating the
Gaussian thermal multiplier. Orthogonal spectral blocks retain their full
multiplicities, including at collisions; no individual signed gain is assumed
to be at most one.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.TraceBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed thermal Gaussian gain on a scaled Bohr frequency. -/
def gaussianGain (s : ℝ) : ℝ := Real.exp (-s^2/8+s/4)


/-- Sum of the two squared thermal Gaussian amplitudes on an unordered
Hermitian spectral pair. -/
def pairedSquare (s : ℝ) : ℝ :=
  Real.exp (-s^2/4+s/2) + Real.exp (-s^2/4-s/2)

/-- Has Deriv At paired Square for the stated finite source data. -/
theorem hasDerivAt_pairedSquare (s : ℝ) :
    HasDerivAt pairedSquare
      ((1/2 : ℝ) * ((1-s) * Real.exp (-s^2/4+s/2) -
        (1+s) * Real.exp (-s^2/4-s/2))) s := by
  unfold pairedSquare
  convert (((((hasDerivAt_id s).pow 2).neg.div_const 4).add
    ((hasDerivAt_id s).div_const 2)).exp).add
      (((((hasDerivAt_id s).pow 2).neg.div_const 4).sub
        ((hasDerivAt_id s).div_const 2)).exp) using 1
  · funext u
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- Paired Square derivative nonpos for the stated finite source data. -/
theorem pairedSquare_derivative_nonpos {s : ℝ} (hs : 0 ≤ s) :
    (1/2 : ℝ) * ((1-s) * Real.exp (-s^2/4+s/2) -
      (1+s) * Real.exp (-s^2/4-s/2)) ≤ 0 := by
  have hone : 1-s ≤ Real.exp (-s) := by
    have h := Real.add_one_le_exp (-s)
    linarith
  have h := mul_le_mul_of_nonneg_right hone (Real.exp_pos (-s^2/4+s/2)).le
  have he : Real.exp (-s) * Real.exp (-s^2/4+s/2) =
      Real.exp (-s^2/4-s/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  nlinarith [Real.exp_pos (-s^2/4-s/2)]

/-- Paired Square antitone for the stated finite source data. -/
theorem pairedSquare_antitone : AntitoneOn pairedSquare (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
      (by unfold pairedSquare; fun_prop)
      (fun x _ => (hasDerivAt_pairedSquare x).hasDerivWithinAt)
  intro x hx
  apply pairedSquare_derivative_nonpos
  have hx' : 0 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  exact hx'.le

/-- Paired Square neg for the stated finite source data. -/
theorem pairedSquare_neg (s : ℝ) : pairedSquare (-s) = pairedSquare s := by
  unfold pairedSquare
  have h₁ : -(-s)^2/4+(-s)/2 = -s^2/4-s/2 := by ring
  have h₂ : -(-s)^2/4-(-s)/2 = -s^2/4+s/2 := by ring
  rw [h₁, h₂, add_comm]

/-- Paired Square le two for the stated finite source data. -/
theorem pairedSquare_le_two (s : ℝ) : pairedSquare s ≤ 2 := by
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : pairedSquare x ≤ 2 := by
    have h := pairedSquare_antitone (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
    norm_num [pairedSquare] at h
    exact h
  by_cases hs : 0 ≤ s
  · exact hnonneg s hs
  · rw [← pairedSquare_neg]
    exact hnonneg (-s) (by linarith)


/-- Pairing opposite signed frequencies bounds their squared gains by two. -/
theorem gaussianGain_pair_sq_le_two (s : ℝ) :
    gaussianGain s ^ 2 + gaussianGain (-s) ^ 2 ≤ 2 := by
  have h₁ : gaussianGain s ^ 2 = Real.exp (-s^2/4+s/2) := by
    unfold gaussianGain
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h₂ : gaussianGain (-s) ^ 2 = Real.exp (-s^2/4-s/2) := by
    unfold gaussianGain
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h₁, h₂]
  exact pairedSquare_le_two s

/-- A complete spectral block, without a choice of basis inside its range. -/
def spectralBlock (P : ι → Operator D) (A : Operator D) (i j : ι) : Operator D :=
  P i * A * P j

/-- A multiplier on all ordered spectral blocks. -/
def spectralMultiplier (P : ι → Operator D) (W : ι → ι → ℂ)
    (A : Operator D) : Operator D :=
  ∑ i, ∑ j, W i j • spectralBlock P A i j

omit [Fintype ι] in
/-- Distinct ordered blocks of Hermitian orthogonal flags are Hilbert--Schmidt orthogonal. -/
theorem hsInner_spectralBlock (P : ι → Operator D)
    (hP : ∀ i, (P i).IsHermitian)
    (hPP : ∀ i j, P i * P j = if i = j then P i else 0)
    (A B : Operator D) (i j k l : ι) :
    hsInner (spectralBlock P A i j) (spectralBlock P B k l) =
      if i = k ∧ j = l then
        hsInner (spectralBlock P A i j) (spectralBlock P B i j) else 0 := by
  by_cases hi : i = k
  · subst k
    by_cases hj : j = l
    · subst l
      simp
    · rw [ite_eq_right (by simp [hj])]
      unfold hsInner spectralBlock
      simp only [Matrix.conjTranspose_mul, (hP i).eq, (hP j).eq]
      have he : P j * (Aᴴ * P i) * (P i * B * P l) =
          P j * ((Aᴴ * P i) * (P i * B)) * P l := by noncomm_ring
      rw [he, Matrix.trace_mul_cycle]
      rw [hPP l j, ite_eq_right (Ne.symm hj), Matrix.zero_mul, Matrix.trace_zero]
  · rw [ite_eq_right (by simp [hi])]
    unfold hsInner spectralBlock
    simp only [Matrix.conjTranspose_mul, (hP i).eq, (hP j).eq]
    have he : P j * (Aᴴ * P i) * (P k * B * P l) =
        P j * Aᴴ * (P i * P k) * B * P l := by noncomm_ring
    rw [he, hPP i k, ite_eq_right hi]
    simp

/-- The exact squared Hilbert--Schmidt mass of an arbitrary spectral multiplier. -/
theorem hsSquare_spectralMultiplier (P : ι → Operator D)
    (hP : ∀ i, (P i).IsHermitian)
    (hPP : ∀ i j, P i * P j = if i = j then P i else 0)
    (W : ι → ι → ℂ) (A : Operator D) :
    (hsInner (spectralMultiplier P W A) (spectralMultiplier P W A)).re =
      ∑ i, ∑ j, Complex.normSq (W i j) *
        (hsInner (spectralBlock P A i j) (spectralBlock P A i j)).re := by
  simp only [spectralMultiplier, hsInner_sum_left, hsInner_sum_right,
    hsInner_smul_left, hsInner_smul_right, Finset.mul_sum]
  have he (k l i j : ι) :
      W k l * (star (W i j) * hsInner (spectralBlock P A i j) (spectralBlock P A k l)) =
      if i = k ∧ j = l then
        (Complex.normSq (W i j) : ℂ) * hsInner (spectralBlock P A i j) (spectralBlock P A i j)
      else 0 := by
    rw [hsInner_spectralBlock P hP hPP A A i j k l]
    by_cases h : i = k ∧ j = l
    · rcases h with ⟨rfl, rfl⟩
      simp [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm]
    · simp [h]
  simp_rw [he]
  simp [Complex.re_sum, ite_and]

/-- A complete flag decomposition preserves total squared mass. -/
theorem sum_spectralBlock_hsSquare (P : ι → Operator D)
    (hP : ∀ i, (P i).IsHermitian)
    (hPP : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (A : Operator D) :
    (∑ i, ∑ j, (hsInner (spectralBlock P A i j) (spectralBlock P A i j)).re) =
      (hsInner A A).re := by
  have he : spectralMultiplier P (fun _ _ => 1) A = A := by
    simp only [spectralMultiplier, one_smul, spectralBlock, ← Finset.mul_sum,
      ← Finset.sum_mul, hsum, Matrix.one_mul, Matrix.mul_one]
  have h := hsSquare_spectralMultiplier P hP hPP (fun _ _ => 1) A
  simpa only [he, Complex.normSq_one, one_mul] using h.symm

/-- A spectral multiplier with unit diagonal preserves the original source trace. -/
theorem trace_spectralMultiplier (P : ι → Operator D)
    (hPP : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (W : ι → ι → ℂ) (hW : ∀ i, W i i = 1)
    (A : Operator D) : Matrix.trace (spectralMultiplier P W A) = Matrix.trace A := by
  have hb (i j : ι) : Matrix.trace (spectralBlock P A i j) =
      if j = i then Matrix.trace (P i * A) else 0 := by
    unfold spectralBlock
    rw [Matrix.trace_mul_cycle, hPP j i]
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  simp only [spectralMultiplier, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, hb,
    mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hW, one_mul]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- Reversing a Hermitian source block preserves its squared mass. -/
theorem spectralBlock_hsSquare_swap (P : ι → Operator D)
    (hP : ∀ i, (P i).IsHermitian) (A : Operator D) (hA : A.IsHermitian)
    (i j : ι) :
    (hsInner (spectralBlock P A j i) (spectralBlock P A j i)).re =
      (hsInner (spectralBlock P A i j) (spectralBlock P A i j)).re := by
  have he : spectralBlock P A j i = (spectralBlock P A i j)ᴴ := by
    simp only [spectralBlock, Matrix.conjTranspose_mul, (hP i).eq, (hP j).eq,
      hA.eq, Matrix.mul_assoc]
  rw [he]
  unfold hsInner
  rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

/-- The full Gaussian multiplier contracts every Hermitian source in Hilbert--Schmidt norm. -/
theorem spectralMultiplier_gaussianGain_hsSquare_le (P : ι → Operator D)
    (hP : ∀ i, (P i).IsHermitian)
    (hPP : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (E : ι → ℝ) (β : ℝ)
    (A : Operator D) (hA : A.IsHermitian) :
    (hsInner (spectralMultiplier P (fun i j => (gaussianGain (β * (E i-E j)) : ℂ)) A)
      (spectralMultiplier P (fun i j => (gaussianGain (β * (E i-E j)) : ℂ)) A)).re ≤
      (hsInner A A).re := by
  let w := fun i j => (hsInner (spectralBlock P A i j) (spectralBlock P A i j)).re
  have hswap :
      (∑ i, ∑ j, gaussianGain (-(β * (E i-E j))) ^ 2 * w i j) =
        ∑ i, ∑ j, gaussianGain (β * (E i-E j)) ^ 2 * w i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show -(β * (E j-E i)) = β * (E i-E j) by ring]
    rw [show w j i = w i j from spectralBlock_hsSquare_swap P hP A hA i j]
  have hpair :
      (∑ i, ∑ j, (gaussianGain (β * (E i-E j)) ^ 2 +
        gaussianGain (-(β * (E i-E j))) ^ 2) * w i j) ≤
      ∑ i, ∑ j, 2 * w i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (gaussianGain_pair_sq_le_two _)
      (hsInner_self_nonneg _)
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hpair
  rw [hswap] at hpair
  rw [hsSquare_spectralMultiplier P hP hPP]
  simp only [Complex.normSq_ofReal, ← pow_two]
  have hmass := sum_spectralBlock_hsSquare P hP hPP hsum A
  change (∑ i, ∑ j, gaussianGain (β * (E i-E j)) ^ 2 * w i j) ≤ _
  change (∑ i, ∑ j, w i j) = _ at hmass
  linarith

end
end Qatlib.Concepts.GibbsSource.TraceBounds

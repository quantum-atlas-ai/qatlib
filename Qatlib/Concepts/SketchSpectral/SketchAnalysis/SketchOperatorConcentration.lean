/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Qatlib.Concepts.MatrixWeights.WeightsCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Operator concentration for sampled Gram matrices

This module proves an operator norm tail bound for importance-sampled Gram matrices under
domination of normalized row energies. The sampled Gram construction and its role in low-rank
arithmetic follow [ChiaEtAl2022]. `compactGramOperatorBadMass` records the probability of a
strict threshold exceedance.

The proof develops finite sign symmetrization, trace moment inequalities, covariance moment
bounds, and a truncated Markov estimate. Normalized rows connect those covariance estimates to
the original Gram sketch, including a separate zero-matrix case.

## Main statements

* `sketchSign_trace_moment`: an even trace moment bound for signed Hermitian sums.
* `sketch_covariance_truncated_moment`: a truncated covariance error moment bound.
* `compact_sketch_operator_tail_nontrivial`: a universal-constant Gram operator tail bound under
  an explicit sample budget.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The probability that the operator norm error of the sampled Gram matrix strictly exceeds
`η`. -/
def compactGramOperatorBadMass {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (r : ℕ)
    (A : Matrix K C ℂ) (η : ℝ) : ℝ :=
  p.probEvent (fun ω : Fin r → K => η < ‖sketchProduct p r A A ω - Aᴴ * A‖)

/-- The product sketch of two zero matrices is zero for every sample tuple. -/
theorem sketchProduct_zero {K C : Type} [Fintype K] (p : FinDist K) (r : ℕ) (ω : Fin r → K) :
    sketchProduct p r (0 : Matrix K C ℂ) (0 : Matrix K C ℂ) ω = 0 := by
  funext i j
  rw [sketchProduct_entry_average]
  simp [sketchSampleMatrix]

/-- Under positive energy domination, a row with zero sampling probability is identically zero. -/
theorem sketchRow_zero_of_prob_zero {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (p : FinDist K) (A : Matrix K C ℂ) (φ E : ℝ) (hφ : 0 < φ) (hE : 0 < E)
    (hdom : ∀ i, sketchRowSquared A i / (φ * E) ≤ p.prob i) (k : K) (hk : p.prob k = 0)
    (j : C) : A k j = 0 := by
  have hh := (div_le_iff₀ (mul_pos hφ hE)).mp (hdom k)
  rw [hk, zero_mul] at hh
  exact sketchRowSquared_eq_zero_entry A k (le_antisymm hh (sketchRowSquared_nonneg A k)) j

/-- Under the positive domination assumptions, the importance-weighted mean of each Gram entry
equals the corresponding entry of AᴴA. -/
theorem sketchGram_mean {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ E : ℝ) (hφ : 0 < φ) (hE : 0 < E)
    (hdom : ∀ i, sketchRowSquared A i / (φ * E) ≤ p.prob i) (i : C) (j : C) :
    ∑ k, (p.prob k : ℂ) * ((p.prob k : ℂ)⁻¹ * (star (A k i) * A k j)) = (Aᴴ * A) i j := by
  have hterm (k : K) :
      (p.prob k : ℂ) * ((p.prob k : ℂ)⁻¹ * (star (A k i) * A k j)) = star (A k i) * A k j := by
    by_cases hk : p.prob k = 0
    · have hA : A k i = 0 := sketchRow_zero_of_prob_zero p A φ E hφ hE hdom k hk i
      have hA2 : A k j = 0 := sketchRow_zero_of_prob_zero p A φ E hφ hE hdom k hk j
      simp [hk, hA, hA2]
    · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hk), one_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp [Matrix.mul_apply, Matrix.conjTranspose]

/-- The zero matrix has zero Gram operator bad mass at every nonnegative error threshold. See
[ChiaEtAl2022]. -/
theorem compactGramOperatorBadMass_zero : ∀ (K C : Type) [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (r : ℕ) (η : ℝ), 0 ≤ η →
    compactGramOperatorBadMass p r (0 : Matrix K C ℂ) η = 0 := by
  intro K C _ _ _ _ p r η hη
  unfold compactGramOperatorBadMass FinDist.probEvent
  have hzero : ∀ ω : Fin r → K,
      ¬(η < ‖sketchProduct p r (0 : Matrix K C ℂ) (0 : Matrix K C ℂ) ω
        - (0 : Matrix K C ℂ)ᴴ * (0 : Matrix K C ℂ)‖) := by
    intro ω hbad
    rw [sketchProduct_zero, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero, norm_zero] at hbad
    linarith
  refine Finset.sum_eq_zero fun ω hω => ?_
  rw [Finset.mem_filter] at hω
  rcases hω with ⟨_, hbad⟩
  exact absurd hbad (hzero ω)

/-- The row product mass of a matrix with itself is its total squared energy. -/
theorem sketchGram_row_product_mass {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) : sketchRowProductMass A A = sketchSquared A := by
  unfold sketchRowProductMass sketchSquared
  apply Finset.sum_congr rfl
  intro k _
  rw [← pow_two, Real.sq_sqrt (sketchRowSquared_nonneg A k)]

open scoped Matrix.Norms.Frobenius in

/-- The spectral Frobenius quantity equals the matrix Frobenius norm. -/
theorem sketchGram_spectralFrobenius_eq {C : Type} [Fintype C]
    (B : Matrix C C ℂ) : spectralFrobenius B = ‖B‖ := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [spectralFrobenius, Real.rpow_two, Complex.normSq_eq_norm_sq]

open scoped Matrix.Norms.Frobenius in

/-- Under row energy domination with φ ≥ 1 and positive total energy, each Gram sampling atom
has Frobenius norm at most φ times the total energy. -/
theorem sketchGram_frobenius_atom_bound {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ) (hφ : 1 ≤ φ)
    (hE : 0 < sketchSquared A)
    (hdom : ∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ p.prob k) (k : K) :
    ‖sketchSampleMatrix p A A k‖ ≤ φ*sketchSquared A := by
  have hW : 0 < sketchRowProductMass A A := by rwa [sketchGram_row_product_mass]
  have hd : ∀ j, Real.sqrt (sketchRowSquared A j)*Real.sqrt (sketchRowSquared A j)/
      (φ*sketchRowProductMass A A) ≤ p.prob j := by
    intro j
    rw [← pow_two, Real.sq_sqrt (sketchRowSquared_nonneg A j), sketchGram_row_product_mass]
    exact hdom j
  simpa only [sketchGram_row_product_mass] using!
    sketch_two_source_atom_bound p A A φ hφ hW hd k

/-- Under row energy domination with φ ≥ 1 and positive total energy, each Gram sampling atom
has operator norm at most φ times the total energy. -/
theorem sketchGram_operator_atom_bound {K C : Type} [Fintype K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ) (hφ : 1 ≤ φ)
    (hE : 0 < sketchSquared A)
    (hdom : ∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ p.prob k) (k : K) :
    ‖sketchSampleMatrix p A A k‖ ≤ φ*sketchSquared A := by
  apply (spectral_operator_norm_le_frobenius _).trans
  rw [sketchGram_spectralFrobenius_eq]
  exact sketchGram_frobenius_atom_bound p A φ hφ hE hdom k

/-- Every Gram sampling atom is positive semidefinite. -/
theorem sketchGram_atom_posSemidef {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (A : Matrix K C ℂ) (k : K) :
    (sketchSampleMatrix p A A k).PosSemidef := by
  let U : Matrix (Fin 1) C ℂ := fun _ j => A k j
  have he : sketchSampleMatrix p A A k = (p.prob k)⁻¹ • (Uᴴ*U) := by
    ext i j
    simp [sketchSampleMatrix, U, Matrix.mul_apply, Matrix.conjTranspose,
      Complex.real_smul, Complex.ofReal_inv]
  rw [he]
  exact (Matrix.posSemidef_conjTranspose_mul_self U).smul (inv_nonneg.mpr (p.nonneg k))

/-- Squaring a Gram sampling atom multiplies it by the row energy divided by its sampling
probability. -/
theorem sketchGram_atom_square {K C : Type} [Fintype K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (k : K) :
    (sketchSampleMatrix p A A k)^2 =
      (sketchRowSquared A k/p.prob k) • sketchSampleMatrix p A A k := by
  have hrow : (∑ l, star (A k l)*A k l) = (sketchRowSquared A k : ℂ) := by
    simp only [sketchRowSquared, Complex.ofReal_sum,
      Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ext i j
  rw [pow_two, Matrix.mul_apply]
  change (∑ l, ((p.prob k : ℂ)⁻¹*(star (A k i)*A k l))*
      ((p.prob k : ℂ)⁻¹*(star (A k l)*A k j))) =
    ((sketchRowSquared A k/p.prob k : ℝ) : ℂ)*
      ((p.prob k : ℂ)⁻¹*(star (A k i)*A k j))
  calc
    _ = ((p.prob k : ℂ)⁻¹)^2 * (star (A k i)*A k j) *
        (∑ l, star (A k l)*A k l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [hrow]; simp only [Complex.ofReal_div]; ring

/-- Under row energy domination and positive total energy, the mean Gram sampling atom is AᴴA. -/
theorem sketchGram_mean_matrix {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ)
    (hφ : 1 ≤ φ) (hE : 0 < sketchSquared A)
    (hdom : ∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ p.prob k) :
    (∑ k, p.prob k • sketchSampleMatrix p A A k) = Aᴴ*A := by
  ext i j
  simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, sketchSampleMatrix] using!
    sketchGram_mean p A φ (sketchSquared A) (by linarith) hE hdom i j

/-- Under row energy domination, the second moment of the Gram atom is bounded in positive
semidefinite order by φ times the total energy times AᴴA. -/
theorem sketchGram_second_moment_posSemidef {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ)
    (hφ : 1 ≤ φ) (hE : 0 < sketchSquared A)
    (hdom : ∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ p.prob k) :
    ((φ*sketchSquared A) • (Aᴴ*A) -
      ∑ k, p.prob k • ((sketchSampleMatrix p A A k)^2)).PosSemidef := by
  have hcoef (k : K) : 0 ≤ p.prob k*(φ*sketchSquared A-sketchRowSquared A k/p.prob k) := by
    by_cases hk : p.prob k=0
    · simp [hk]
    · have hp : 0 < p.prob k := lt_of_le_of_ne (p.nonneg k) (Ne.symm hk)
      have hden : 0 < φ*sketchSquared A := mul_pos (by linarith) hE
      have hrow := (div_le_iff₀ hden).mp (hdom k)
      apply mul_nonneg hp.le
      exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr (by nlinarith))
  have he : (φ*sketchSquared A) • (Aᴴ*A) -
      ∑ k, p.prob k • ((sketchSampleMatrix p A A k)^2) =
      ∑ k, (p.prob k*(φ*sketchSquared A-sketchRowSquared A k/p.prob k)) •
        sketchSampleMatrix p A A k := by
    rw [← sketchGram_mean_matrix p A φ hφ hE hdom, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [sketchGram_atom_square p A k, smul_smul, smul_smul, ← sub_smul]
    congr 1
    ring
  rw [he]
  exact Matrix.posSemidef_sum _ (fun k _ => (sketchGram_atom_posSemidef p A k).smul (hcoef k))

/-- The complex sign associated with a Boolean value. -/
def sketchSign (b : Bool) : ℂ := if b then 1 else -1

/-- The Boolean sign tuple obtained by flipping coordinate `i`. -/
def sketchSignFlip {r : ℕ} (i : Fin r) (s : Fin r → Bool) : Fin r → Bool :=
  Function.update s i (!s i)

/-- Flipping the same Boolean sign coordinate twice restores the original tuple. -/
theorem sketchSignFlip_involutive {r : ℕ} (i : Fin r) :
    Function.Involutive (sketchSignFlip i) := by
  intro s
  funext j
  by_cases h : j = i
  · subst j
    simp [sketchSignFlip]
  · simp [sketchSignFlip, h]

/-- Summing over all Boolean sign tuples is invariant under a fixed coordinate flip. -/
theorem sketchSignFlip_sum {r : ℕ} (i : Fin r) {M : Type*} [AddCommMonoid M]
    (f : (Fin r → Bool) → M) :
    (∑ s, f (sketchSignFlip i s)) = ∑ s, f s :=
  Equiv.sum_comp ((sketchSignFlip_involutive i).toPerm) f

/-- The matrix sum with coefficients given by the Boolean signs. -/
def sketchSignMatrix {C : Type*} {r : ℕ} (B : Fin r → Matrix C C ℂ)
    (s : Fin r → Bool) : Matrix C C ℂ := ∑ i, sketchSign (s i) • B i

/-- Flipping one sign subtracts twice its original signed matrix contribution from the signed
sum. -/
theorem sketchSignMatrix_flip {C : Type*} {r : ℕ}
    (B : Fin r → Matrix C C ℂ) (i : Fin r) (s : Fin r → Bool) :
    sketchSignMatrix B (sketchSignFlip i s) =
      sketchSignMatrix B s - (2 * sketchSign (s i)) • B i := by
  have hterm : (fun j => sketchSign (sketchSignFlip i s j) • B j) =
      Function.update (fun j => sketchSign (s j) • B j) i
        (-(sketchSign (s i) • B i)) := by
    funext j
    by_cases h : j = i
    · subst j
      cases hs : s i <;> simp [sketchSignFlip, sketchSign, hs]
    · simp [sketchSignFlip, h]
  unfold sketchSignMatrix
  rw [hterm, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => sketchSign (s j) • B j)
    (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← hsum, mul_smul]
  module

/-- Four times the total trace of the (n + 1)st powers of signed sums equals the summed trace
pairing of coordinate-flip differences with differences of nth powers. -/
theorem sketchSign_trace_flip_identity {C : Type*} [Fintype C] [DecidableEq C]
    {r : ℕ} (B : Fin r → Matrix C C ℂ) (n : ℕ) :
    (4 : ℂ) * (∑ s, Matrix.trace (sketchSignMatrix B s ^ (n + 1))) =
      ∑ i, ∑ s, Matrix.trace ((sketchSignMatrix B s -
        sketchSignMatrix B (sketchSignFlip i s)) *
        (sketchSignMatrix B s ^ n - sketchSignMatrix B (sketchSignFlip i s) ^ n)) := by
  let f := fun i s => Matrix.trace ((sketchSign (s i) • B i) * sketchSignMatrix B s ^ n)
  have hflip (i : Fin r) :
      (∑ s, Matrix.trace ((sketchSign (s i) • B i) *
        sketchSignMatrix B (sketchSignFlip i s) ^ n)) = -(∑ s, f i s) := by
    have he (s : Fin r → Bool) :
        Matrix.trace ((sketchSign (s i) • B i) * sketchSignMatrix B (sketchSignFlip i s) ^ n) =
          -(f i (sketchSignFlip i s)) := by
      dsimp [f]
      cases hs : s i <;>
        simp [sketchSignFlip, sketchSign, hs, neg_mul, Matrix.trace_neg]
    simp_rw [he]
    rw [Finset.sum_neg_distrib, sketchSignFlip_sum]
  have hi (i : Fin r) :
      (∑ s, Matrix.trace ((sketchSignMatrix B s -
        sketchSignMatrix B (sketchSignFlip i s)) *
        (sketchSignMatrix B s ^ n - sketchSignMatrix B (sketchSignFlip i s) ^ n))) =
          4 * ∑ s, f i s := by
    have hd (s : Fin r → Bool) :
        sketchSignMatrix B s - sketchSignMatrix B (sketchSignFlip i s) =
          (2 : ℂ) • (sketchSign (s i) • B i) := by
      rw [sketchSignMatrix_flip, sub_sub_cancel, mul_smul]
    simp_rw [hd, mul_sub, smul_mul_assoc (2 : ℂ), Matrix.trace_sub,
      Matrix.trace_smul (2 : ℂ), smul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hflip]
    dsimp [f]
    ring
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  dsimp [f]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul]
  change Matrix.trace (sketchSignMatrix B s ^ (n + 1)) =
    Matrix.trace (sketchSignMatrix B s * sketchSignMatrix B s ^ n)
  rw [pow_succ']

/-- The uniform sign average of the real trace of the squared signed sum equals the real trace
of the sum of the individual matrix squares. -/
theorem sketchSign_trace_second_moment {C : Type*} [Fintype C] [DecidableEq C]
    {r : ℕ} (B : Fin r → Matrix C C ℂ) :
    (2 : ℝ) ^ (-(r : ℤ)) *
      (∑ s, (Matrix.trace (sketchSignMatrix B s ^ 2)).re) =
        (Matrix.trace (∑ i, B i * B i)).re := by
  have ht (i : Fin r) (s : Fin r → Bool) :
      Matrix.trace ((sketchSignMatrix B s - sketchSignMatrix B (sketchSignFlip i s)) *
        (sketchSignMatrix B s - sketchSignMatrix B (sketchSignFlip i s))) =
          4 * Matrix.trace (B i * B i) := by
    rw [sketchSignMatrix_flip, sub_sub_cancel, smul_mul_assoc, mul_smul_comm,
      smul_smul, Matrix.trace_smul, smul_eq_mul]
    cases s i <;> norm_num [sketchSign]
  have hid := sketchSign_trace_flip_identity B 1
  simp only [pow_one] at hid
  simp_rw [ht] at hid
  have hc : Fintype.card (Fin r → Bool) = 2 ^ r := by simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc] at hid
  have hs : (∑ s, Matrix.trace (sketchSignMatrix B s ^ 2)) =
      ((2 : ℂ)^r) * Matrix.trace (∑ i, B i * B i) := by
    apply mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0)
    convert! hid using 1
    rw [Matrix.trace_sum]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hre := congrArg Complex.re hs
  simp only [Complex.re_sum, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  rw [hre, _root_.zpow_neg, zpow_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ)^r ≠ 0), one_mul]

open intervalIntegral in

/-- For even `n`, the scalar power difference pairing is bounded by (n + 1) / 2 times the
squared difference and the sum of nth powers. -/
theorem sketch_even_power_mean_value (n : ℕ) (hn : Even n) (a b : ℝ) :
    (a-b)*(a^(n+1)-b^(n+1)) ≤ ((n+1 : ℕ) : ℝ)/2*(a-b)^2*(a^n+b^n) := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    nlinarith
  by_cases heq : a = b
  · subst b; simp
  have hpos : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  have hc : ConvexOn ℝ Set.univ (fun x : ℝ => x^n) := by
    by_cases hz : n=0
    · subst n; simpa using! (convexOn_const (c := (1:ℝ)) convex_univ)
    · exact (hn.strictConvexOn_pow hz).convexOn
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc a b) :
      (b-a)*x^n ≤ (b-x)*a^n+(x-a)*b^n := by
    have hweights : (b-x)/(b-a)+(x-a)/(b-a)=1 := by field_simp; ring
    have hcombo : (b-x)/(b-a)*a+(x-a)/(b-a)*b=x := by field_simp; ring
    have h := hc.2 (Set.mem_univ a) (Set.mem_univ b)
      (div_nonneg (sub_nonneg.mpr hx.2) hpos.le)
      (div_nonneg (sub_nonneg.mpr hx.1) hpos.le) hweights
    simp only [smul_eq_mul, hcombo] at h
    have hh := mul_le_mul_of_nonneg_left h hpos.le
    field_simp at hh
    nlinarith
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    ((continuous_const.mul (continuous_pow n)).intervalIntegrable a b)
    ((((continuous_const.sub continuous_id).mul continuous_const).add
      ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable a b)
    hpoint
  have hia : (∫ x in a..b, (b-x)*a^n) = (b-a)^2/2*a^n := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun x : ℝ => x) (continuous_const.intervalIntegrable a b) (continuous_id.intervalIntegrable a b),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  have hib : (∫ x in a..b, (x-a)*b^n) = (b-a)^2/2*b^n := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a) (continuous_id.intervalIntegrable a b) (continuous_const.intervalIntegrable a b),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  change (∫ x in a..b, (b-a)*x^n) ≤ (∫ x in a..b, (b-x)*a^n+(x-a)*b^n) at hint
  rw [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_add (f := fun x : ℝ => (b-x)*a^n) (g := fun x : ℝ => (x-a)*b^n)
      (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable a b)
      (((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable a b), hia, hib] at hint
  have hnpos : (0 : ℝ) < (n : ℝ)+1 := by positivity
  rw [← mul_div_assoc] at hint
  have hm := (div_le_iff₀ hnpos).mp hint
  push_cast
  nlinarith

open Qatlib.Concepts.PhaseGeometry.Phase in
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing in

/-- The real trace of AᵖBᑫ is the sum of products of ordered eigenvalue powers weighted by
squared overlaps of the two eigenbases. -/
theorem sketch_hermitian_trace_pow_cross {C : Type} [Fintype C] [DecidableEq C]
    (A B : Matrix C C ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (p q : ℕ) :
    (Matrix.trace (A^p*B^q)).re =
      ∑ i, ∑ j, (orderedHermitianValues hA i)^p * (orderedHermitianValues hB j)^q *
        Complex.normSq (((basisColumns (orderedHermitianBasis hA))ᴴ *
          basisColumns (orderedHermitianBasis hB)) i j) := by
  let VA := basisColumns (orderedHermitianBasis hA)
  let VB := basisColumns (orderedHermitianBasis hB)
  have ha : A^p=VA*diagonal (fun i => ((orderedHermitianValues hA i ^ p : ℝ) : ℂ))*VAᴴ := by
    have h := aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hA) A
      (fun i => (orderedHermitianValues hA i : ℂ)) (orderedHermitianBasis_action hA)
      (Polynomial.X^p)
    simpa [Polynomial.aeval_X_pow, spectralDiagonal, VA] using! h
  have hb : B^q=VB*diagonal (fun i => ((orderedHermitianValues hB i ^ q : ℝ) : ℂ))*VBᴴ := by
    have h := aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hB) B
      (fun i => (orderedHermitianValues hB i : ℂ)) (orderedHermitianBasis_action hB)
      (Polynomial.X^q)
    simpa [Polynomial.aeval_X_pow, spectralDiagonal, VB] using! h
  have h := singular_cross_trace (Fintype.card C) VA VB VA VB
    (fun i => (orderedHermitianValues hA i)^p)
    (fun j => (orderedHermitianValues hB j)^q)
  rw [← ha, ← hb, (hA.pow p).eq] at h
  convert! h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [VA, VB, Complex.mul_re, Complex.normSq_apply]

open Qatlib.Concepts.PhaseGeometry.Phase in
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing in

/-- For even `m`, the Hermitian trace pairing of a matrix difference with the difference of (m +
1)st powers satisfies the stated mean-value inequality. -/
theorem sketch_hermitian_trace_mean_value {C : Type} [Fintype C] [DecidableEq C]
    (A B : Matrix C C ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (m : ℕ) (hm : Even m) :
    (Matrix.trace ((A-B)*(A^(m+1)-B^(m+1)))).re ≤
      ((m+1 : ℕ) : ℝ)/2*(Matrix.trace ((A-B)^2*(A^m+B^m))).re := by
  let T := fun p q => (Matrix.trace (A^p*B^q)).re
  have ha (j : ℕ) : (Matrix.trace ((A*A)*A^j)).re = T (j+2) 0 := by
    simp [T, pow_succ', mul_assoc]
  have hb (j : ℕ) : (Matrix.trace ((B*B)*B^j)).re = T 0 (j+2) := by
    simp [T, pow_succ', mul_assoc]
  have hab (j : ℕ) : (Matrix.trace ((A*B)*A^j)).re = T (j+1) 1 := by
    rw [Matrix.trace_mul_cycle, ← pow_succ]
    simp [T]
  have hba (j : ℕ) : (Matrix.trace ((B*A)*B^j)).re = T 1 (j+1) := by
    rw [Matrix.trace_mul_cycle, ← pow_succ, Matrix.trace_mul_comm]
    simp [T]
  have hl : (Matrix.trace ((A-B)*(A^(m+1)-B^(m+1)))).re =
      T (m+2) 0 + T 0 (m+2) - T 1 (m+1) - T (m+1) 1 := by
    simp only [sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re]
    have hc := Matrix.trace_mul_comm B (A^(m+1))
    rw [hc]
    simp [T, pow_succ']
    ring
  have he : (A-B)^2*(A^m+B^m) =
      (A*A)*A^m+(B*B)*B^m+B^2*A^m+A^2*B^m-
        (A*B)*A^m-(B*A)*A^m-(A*B)*B^m-(B*A)*B^m := by
    simp only [pow_two]
    noncomm_ring
  have hr : (Matrix.trace ((A-B)^2*(A^m+B^m))).re =
      T (m+2) 0+T 0 (m+2)+T m 2+T 2 m-2*T (m+1) 1-2*T 1 (m+1) := by
    rw [he]
    simp only [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
    rw [ha, hb, hab, hba, Matrix.trace_mul_comm (B^2) (A^m)]
    have hx : (Matrix.trace ((B*A)*A^m)).re = T (m+1) 1 := by
      rw [mul_assoc, ← pow_succ', Matrix.trace_mul_comm]
      simp [T]
    have hy : (Matrix.trace ((A*B)*B^m)).re = T 1 (m+1) := by
      rw [mul_assoc, ← pow_succ']
      simp [T]
    rw [hx,hy]
    dsimp [T]
    ring
  let W := fun i j => Complex.normSq (((basisColumns (orderedHermitianBasis hA))ᴴ *
    basisColumns (orderedHermitianBasis hB)) i j)
  let a := orderedHermitianValues hA
  let b := orderedHermitianValues hB
  have ht (p q : ℕ) : T p q=∑ i,∑ j,a i^p*b j^q*W i j :=
    sketch_hermitian_trace_pow_cross A B hA hB p q
  have hleft : (Matrix.trace ((A-B)*(A^(m+1)-B^(m+1)))).re =
      ∑ i,∑ j, W i j*((a i-b j)*(a i^(m+1)-b j^(m+1))) := by
    rw [hl]
    simp_rw [ht]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [pow_zero, pow_succ']
    ring
  have hright : (Matrix.trace ((A-B)^2*(A^m+B^m))).re =
      ∑ i,∑ j,W i j*((a i-b j)^2*(a i^m+b j^m)) := by
    rw [hr]
    simp_rw [ht]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [pow_zero, pow_succ']
    ring
  rw [hleft, hright, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ W i j * (((m+1 : ℕ) : ℝ)/2*(a i-b j)^2*(a i^m+b j^m)) :=
      mul_le_mul_of_nonneg_left (sketch_even_power_mean_value m hm (a i) (b j))
        (Complex.normSq_nonneg _)
    _ = _ := by ring

/-- For Hermitian summands and even `m`, the sign-summed trace moment of order m + 2 is bounded
by m + 1 times the trace pairing of the mth power with the sum of squares. -/
theorem sketchSign_trace_moment_recurrence {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (B : Fin r → Matrix C C ℂ) (hB : ∀ i, (B i).IsHermitian)
    (m : ℕ) (hm : Even m) :
    (∑ s, (Matrix.trace (sketchSignMatrix B s ^ (m+2))).re) ≤
      ((m+1 : ℕ) : ℝ) * (∑ s,
        (Matrix.trace (sketchSignMatrix B s ^ m * (∑ i, B i * B i))).re) := by
  have hh (s : Fin r → Bool) : (sketchSignMatrix B s).IsHermitian := by
    exact isSelfAdjoint_sum _
        (fun i _ => (hB i).smul (by cases s i <;> simp [sketchSign, IsSelfAdjoint]))
  have hd (i : Fin r) (s : Fin r → Bool) :
      (sketchSignMatrix B s-sketchSignMatrix B (sketchSignFlip i s))^2 =
        (4 : ℂ) • (B i * B i) := by
    rw [sketchSignMatrix_flip, sub_sub_cancel, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    cases s i <;> norm_num [sketchSign]
  let f := fun i s => (Matrix.trace ((B i*B i)*sketchSignMatrix B s ^ m)).re
  have hp (i : Fin r) (s : Fin r → Bool) :
      (Matrix.trace ((sketchSignMatrix B s-sketchSignMatrix B (sketchSignFlip i s))*
        (sketchSignMatrix B s^(m+1)-sketchSignMatrix B (sketchSignFlip i s)^(m+1)))).re ≤
          2*((m+1 : ℕ) : ℝ)*(f i s+f i (sketchSignFlip i s)) := by
    have h := sketch_hermitian_trace_mean_value _ _ (hh s) (hh (sketchSignFlip i s)) m hm
    rw [hd, smul_mul_assoc, Matrix.trace_smul, mul_add, Matrix.trace_add] at h
    dsimp [f]
    simp only [smul_eq_mul, Complex.mul_re, ← Complex.ofReal_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re] at h
    convert! h using 1
    ring
  have hi (i : Fin r) :
      (∑ s, (Matrix.trace ((sketchSignMatrix B s-sketchSignMatrix B (sketchSignFlip i s))*
        (sketchSignMatrix B s^(m+1)-sketchSignMatrix B (sketchSignFlip i s)^(m+1)))).re) ≤
          4*((m+1 : ℕ) : ℝ)*(∑ s,f i s) := by
    have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hp i s)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, sketchSignFlip_sum] at h
    convert! h using 1
    ring
  have hid := congrArg Complex.re (sketchSign_trace_flip_identity B (m+1))
  simp only [Complex.mul_re, ← Complex.ofReal_ofNat, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum] at hid
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [← hid, ← Finset.mul_sum, Finset.sum_comm] at h
  have hf (s : Fin r → Bool) : (∑ i,f i s)=
      (Matrix.trace (sketchSignMatrix B s^m*(∑ i,B i*B i))).re := by
    dsimp [f]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, Matrix.trace_mul_comm]
  simp_rw [hf] at h
  nlinarith

/-- For a positive semidefinite matrix and positive integer `q`, the qth power of its Schatten
q-norm is the real trace of its qth power. -/
theorem sketch_psd_schatten_moment {C : Type} [Fintype C] [DecidableEq C] (V : Matrix C C ℂ)
    (hV : V.PosSemidef) (q : ℕ) (hq : 0 < q) :
    schattenNorm V q ^ q = (Matrix.trace (V^q)).re := by
  let H : HermitianMat C ℂ := ⟨V,hV.isHermitian⟩
  have hp : 0 ≤ H := HermitianMat.zero_le_iff.mpr hV
  have h := trace_eq_schattenNorm_rpow H hp (q : ℝ) (by exact_mod_cast hq)
  rw [HermitianMat.rpow_eq_cfc] at h
  simp_rw [Real.rpow_natCast] at h
  rw [HermitianMat.cfc_pow, HermitianMat.trace_eq_re_trace, HermitianMat.mat_pow] at h
  simpa [H] using! h.symm

/-- For q ≥ 2, the real trace of S^(2q - 2)V is bounded by the corresponding Schatten 2q- and
q-norm product. -/
theorem sketch_trace_lower_moment_holder {C : Type} [Fintype C] [DecidableEq C] (S V : Matrix C C ℂ)
    (q : ℕ) (hq : 2 ≤ q) :
    (Matrix.trace (S^(2*q-2)*V)).re ≤
      schattenNorm S (2*q) ^ (2*q-2) * schattenNorm V q := by
  have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hn : 0 < 2*q-2 := by omega
  have hnR : 0 < ((2*q-2 : ℕ) : ℝ) := by exact_mod_cast hn
  have he : ((2*q-2 : ℕ) : ℝ)=2*(q:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hp : 0 < (2*(q:ℝ))/((2*q-2 : ℕ):ℝ) := div_pos (by positivity) hnR
  have hh : (1 : ℝ)=1/((2*(q:ℝ))/((2*q-2 : ℕ):ℝ))+1/(q:ℝ) := by
    rw [he]
    field_simp
    ring
  have hmul := schattenNorm_mul_le (S^(2*q-2)) V (by norm_num : (0:ℝ)<1)
    hp (by positivity : (0:ℝ)<q) (by simpa using! hh)
  have hpw := mmw_schatten_power_le S (2*q) (by positivity) (2*q-2) hn
  exact (Complex.re_le_norm _).trans ((mmw_trace_le_schatten_one _).trans
    (hmul.trans (mul_le_mul_of_nonneg_right hpw (schattenNorm_nonneg V q))))

/-- For nonnegative values under normalized nonnegative weights, a recurrence bounding the 2qth
moment by `K` times the (2q - 2)nd moment implies a bound by Kᑫ when q ≥ 2. -/
theorem sketch_finite_moment_self_bound {I : Type*} [Fintype I] (w x : I → ℝ) (q : ℕ)
    (hq : 2 ≤ q) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i,w i=1) (hx : ∀ i, 0 ≤ x i)
    (K : ℝ) (hK : 0 ≤ K)
    (hrec : (∑ i,w i*x i^(2*q)) ≤ K*(∑ i,w i*x i^(2*q-2))) :
    (∑ i,w i*x i^(2*q)) ≤ K^q := by
  have hqr : 2 ≤ (q:ℝ) := by exact_mod_cast hq
  have hqm : 0 < (q:ℝ)-1 := by linarith
  have hqpos : 0 < (q:ℝ) := by linarith
  let T := ∑ i,w i*x i^(2*q)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (pow_nonneg (hx i) _))
  have hmean := Real.arith_mean_le_rpow_mean Finset.univ w (fun i=>x i^(2*q-2))
    (fun i _=>hw i) hw1 (fun i _=>pow_nonneg (hx i) _)
    (p := (q:ℝ)/((q:ℝ)-1)) ((le_div_iff₀ hqm).mpr (by linarith))
  have hexp : ((2*q-2 : ℕ):ℝ)*((q:ℝ)/((q:ℝ)-1)) = (2*q : ℕ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
  have hpw (i : I) : (x i^(2*q-2))^((q:ℝ)/((q:ℝ)-1)) = x i^(2*q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i), hexp, Real.rpow_natCast]
  simp_rw [hpw] at hmean
  have he : 1/((q:ℝ)/((q:ℝ)-1)) = ((q:ℝ)-1)/(q:ℝ) := by field_simp
  rw [he] at hmean
  have hh : T ≤ K*T^(((q:ℝ)-1)/(q:ℝ)) :=
    hrec.trans (mul_le_mul_of_nonneg_left hmean hK)
  by_cases hzero : T=0
  · change T ≤ _
    rw [hzero]
    positivity
  have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  have hprod : T = T^(1/(q:ℝ))*T^(((q:ℝ)-1)/(q:ℝ)) := by
    rw [← Real.rpow_add hTp]
    have hs : (1:ℝ)/(q:ℝ)+((q:ℝ)-1)/(q:ℝ)=1 := by field_simp; ring
    rw [hs, Real.rpow_one]
  nth_rw 1 [hprod] at hh
  have hroot : T^(1/(q:ℝ)) ≤ K :=
    (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hTp _)).mp hh
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hT _) hroot hqpos.le
  rw [← Real.rpow_mul hT, one_div_mul_cancel (ne_of_gt hqpos), Real.rpow_one,
    Real.rpow_natCast] at hr
  exact hr

/-- For Hermitian summands and q ≥ 1, the averaged real trace moment of order 2q is at most (2q
- 1)ᑫ times the real trace of the qth power of the sum of squares. -/
theorem sketchSign_trace_moment {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (B : Fin r → Matrix C C ℂ) (q : ℕ) (hq : 1 ≤ q) (hB : ∀ i, (B i).IsHermitian) :
    (2 : ℝ)^(-(r:ℤ))*(∑ s,(Matrix.trace (sketchSignMatrix B s^(2*q))).re) ≤
      ((2*q-1 : ℕ):ℝ)^q*(Matrix.trace ((∑ i,B i*B i)^q)).re := by
  by_cases hq1 : q=1
  · subst q
    simpa using! (sketchSign_trace_second_moment B).le
  have hq2 : 2 ≤ q := by omega
  let V := ∑ i,B i*B i
  let w : ℝ := (2:ℝ)^(-(r:ℤ))
  let x := fun s => schattenNorm (sketchSignMatrix B s) (2*q)
  have hV : V.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    simpa [(hB i).eq] using! Matrix.posSemidef_conjTranspose_mul_self (B i)
  have hh (s : Fin r → Bool) : (sketchSignMatrix B s).IsHermitian :=
    isSelfAdjoint_sum _ (fun i _ => (hB i).smul (by cases s i <;> simp [sketchSign, IsSelfAdjoint]))
  have he (s : Fin r → Bool) : (Matrix.trace (sketchSignMatrix B s^(2*q))).re=x s^(2*q) := by
    have h := mmw_schatten_even_moment (sketchSignMatrix B s) q (by omega)
    rw [(hh s).eq, ← pow_two, ← pow_mul] at h
    simpa [x, Nat.mul_comm] using! h.symm
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : (∑ s : Fin r → Bool,w)=1 := by
    simp [w, _root_.zpow_neg, zpow_natCast, nsmul_eq_mul]
  have hx (s : Fin r → Bool) : 0 ≤ x s := schattenNorm_nonneg _ _
  have hc : 0 ≤ ((2*q-1 : ℕ):ℝ) := by positivity
  have hn : 0 ≤ schattenNorm V q := schattenNorm_nonneg _ _
  have hr := sketchSign_trace_moment_recurrence B hB (2*q-2)
    (by exact ⟨q-1, by omega⟩)
  have ha : 2*q-2+2=2*q := by omega
  have hb : 2*q-2+1=2*q-1 := by omega
  rw [ha,hb] at hr
  simp_rw [he] at hr
  have ht := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    sketch_trace_lower_moment_holder (sketchSignMatrix B s) V q hq2)
  have hrec : (∑ s,w*x s^(2*q)) ≤
      (((2*q-1 : ℕ):ℝ)*schattenNorm V q)*(∑ s,w*x s^(2*q-2)) := by
    have h := mul_le_mul_of_nonneg_left (hr.trans
      (mul_le_mul_of_nonneg_left ht hc)) hw
    dsimp [x,V] at h ⊢
    simp only [← Finset.mul_sum, ← Finset.sum_mul] at h ⊢
    convert! h using 1
    ring
  have h := sketch_finite_moment_self_bound (fun _ => w) x q hq2 (fun _=>hw) hw1 hx
    (((2*q-1 : ℕ):ℝ)*schattenNorm V q) (mul_nonneg hc hn) hrec
  rw [mul_pow, sketch_psd_schatten_moment V hV q (by omega)] at h
  simp only [← Finset.mul_sum] at h
  simpa only [he,w,V] using! h

/-- For a positive semidefinite matrix and positive `q`, the real trace of its qth power is at
most its rank times the qth power of its operator norm. -/
theorem sketch_psd_trace_power_rank_bound {C : Type} [Fintype C] [DecidableEq C] (V : Matrix C C ℂ)
    (hV : V.PosSemidef) (q : ℕ) (hq : 0 < q) :
    (Matrix.trace (V^q)).re ≤ (V.rank : ℝ)*‖V‖^q := by
  cases isEmpty_or_nonempty C with
  | inl he =>
    simp [Matrix.trace]
    positivity
  | inr hn =>
    let H : HermitianMat C ℂ := ⟨V,hV.isHermitian⟩
    let e := hV.isHermitian.eigenvalues
    have ht : (Matrix.trace (V^q)).re=∑ i,e i^q := by
      have h := H.trace_cfc_eq (fun x : ℝ => x^q)
      rw [HermitianMat.cfc_pow, HermitianMat.trace_eq_re_trace, HermitianMat.mat_pow] at h
      exact h
    have hb (i : C) : e i ≤ ‖V‖ := by
      have h := spectrum.norm_le_norm_of_mem (hV.isHermitian.eigenvalues_mem_spectrum_real i)
      simpa [e, Real.norm_eq_abs, abs_of_nonneg (hV.eigenvalues_nonneg i)] using! h
    let s : Finset C := Finset.univ.filter (fun i=>e i ≠ 0)
    have he : (∑ i,e i^q)=∑ i∈s,e i^q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hz : e i=0 := by simpa [s] using! hi
      simp [hz,ne_of_gt hq]
    have hc : s.card=V.rank := by
      rw [hV.isHermitian.rank_eq_card_non_zero_eigs]
      simp [s,e,Fintype.card_subtype]
    rw [ht,he]
    calc
      _ ≤ ∑ i∈s,‖V‖^q := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (hV.eigenvalues_nonneg i) (hb i) q)
      _ = _ := by simp [hc]

/-- A weighted sum of `r` outer products has rank at most `r`. -/
theorem sketch_weighted_outer_sum_rank {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (a : Fin r → ℂ) (u v : Fin r → C → ℂ) :
    (∑ i,a i • Matrix.vecMulVec (u i) (v i)).rank ≤ r := by
  let U : Matrix C (Fin r) ℂ := fun j i => a i*u i j
  let V : Matrix (Fin r) C ℂ := fun i j => v i j
  have he : (∑ i,a i • Matrix.vecMulVec (u i) (v i))=U*V := by
    ext j k
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
        Matrix.mul_apply,U,V,mul_assoc]
  rw [he]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using! Matrix.rank_le_card_width U)

/-- The square of a covariance outer product equals that outer product multiplied by the
vector's total squared magnitude. -/
theorem sketch_covariance_atom_square {C : Type} [Fintype C] [DecidableEq C] (u : C → ℂ) :
    (Matrix.vecMulVec u (star u))^2 =
      (∑ j,‖u j‖^2) • Matrix.vecMulVec u (star u) := by
  have hs : (∑ j, star (u j)*u j)=((∑ j,‖u j‖^2 : ℝ):ℂ) := by
    simp only [Complex.ofReal_sum, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
        Complex.star_def]
  ext i j
  rw [pow_two,Matrix.mul_apply]
  change (∑ k,(u i*star (u k))*(u k*star (u j)))=
    (((∑ k,‖u k‖^2 : ℝ):ℂ)*(u i*star (u j)))
  rw [← hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

open Qatlib.Concepts.PhaseGeometry.Phase in
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing in

/-- For a Hermitian matrix and positive `q`, the 2qth power of the operator norm is at most the
real trace of the 2qth matrix power. -/
theorem sketch_hermitian_operator_even_trace {C : Type} [Fintype C] [DecidableEq C] (S : Matrix C C ℂ)
    (hS : S.IsHermitian) (q : ℕ) (hq : 0 < q) :
    ‖S‖^(2*q) ≤ (Matrix.trace (S^(2*q))).re := by
  let a := orderedHermitianValues hS
  let T := ∑ i,a i^(2*q)
  have hn (i : Fin (Fintype.card C)) : 0 ≤ a i^(2*q) :=
    Even.pow_nonneg ⟨q,by omega⟩ _
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _=>hn i)
  have hp : (0 : ℝ)<(2*q : ℕ) := by positivity
  have hi (i : Fin (Fintype.card C)) : |a i|^(2*q) ≤ T := by
    rw [← abs_pow, abs_of_nonneg (hn i)]
    exact Finset.single_le_sum (fun j _=>hn j) (Finset.mem_univ i)
  have hroot (i : Fin (Fintype.card C)) : |a i| ≤ T^((2*q : ℕ):ℝ)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg _) hT hp).mpr
    simpa only [Real.rpow_natCast] using! hi i
  have hs : ‖S‖ ≤ T^((2*q : ℕ):ℝ)⁻¹ := by
    rw [orderedHermitian_diagonal hS]
    apply spectralDiagonal_norm_le _ _ (Real.rpow_nonneg hT _)
    intro i
    simpa [a, Complex.norm_real, Real.norm_eq_abs] using! hroot i
  have ht : (Matrix.trace (S^(2*q))).re=T := by
    have h := aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hS) S
      (fun i => (a i : ℂ)) (orderedHermitianBasis_action hS) (Polynomial.X^(2*q))
    have he : S^(2*q)=spectralDiagonal (orderedHermitianBasis hS)
      (fun i => ((a i^(2*q) : ℝ):ℂ)) := by simpa using! h
    rw [he,spectralDiagonal_trace]
    simp only [Complex.re_sum, Complex.ofReal_re]
    rfl
  rw [ht]
  have h := pow_le_pow_left₀ (norm_nonneg S) hs (2*q)
  have he : (T^((2*q : ℕ):ℝ)⁻¹)^(2*q)=T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT, inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  exact h.trans_eq he

open scoped MatrixOrder in

/-- For vectors of Euclidean norm at most `R`, the norm of the sum of squared covariance atoms
is at most R² times the norm of their sum. -/
theorem sketch_covariance_variance_norm {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ i, ‖toEuclidean_fromVec (y i)‖ ≤ R) :
    ‖∑ i,(Matrix.vecMulVec (y i) (star (y i)))^2‖ ≤
      R^2*‖∑ i,Matrix.vecMulVec (y i) (star (y i))‖ := by
  letI : CStarAlgebra (Matrix C C ℂ) := {}
  let B := fun i => Matrix.vecMulVec (y i) (star (y i))
  have hB (i : Fin r) : (B i).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have he (i : Fin r) : (B i)^2=‖toEuclidean_fromVec (y i)‖^2 • B i := by
    rw [norm_toEuclidean_fromVec_sq]
    exact sketch_covariance_atom_square _
  have ho : ((R^2) • (∑ i,B i)-(∑ i,(B i)^2)).PosSemidef := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    simp_rw [he, ← sub_smul]
    apply Matrix.posSemidef_sum
    intro i _
    apply (hB i).smul
    exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hR).mpr (hy i))
  have hv : (∑ i,(B i)^2).PosSemidef := Matrix.posSemidef_sum _ (fun i _ => (hB i).pow 2)
  have h :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg (A := Matrix C C ℂ) (a := ∑ i,(B i)^2)
      (b := R^2 • (∑ i,B i)) (Matrix.le_iff.mpr ho) hv.nonneg
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg R)] at h
  exact h

/-- The sum of the squares of `r` covariance atoms has rank at most `r`. -/
theorem sketch_covariance_variance_rank {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ) :
    (∑ i,(Matrix.vecMulVec (y i) (star (y i)))^2).rank ≤ r := by
  simp_rw [sketch_covariance_atom_square]
  simpa only [Complex.real_smul] using!
    sketch_weighted_outer_sum_rank (fun i => ((∑ j,‖y i j‖^2 : ℝ):ℂ)) y (fun i=>star (y i))

/-- For vectors of norm at most `R` and q ≥ 1, the averaged 2qth operator norm moment of the
signed covariance sum is bounded by r(2q - 1)ᑫ times the qth power of R² times the
covariance sum norm. -/
theorem sketch_covariance_rademacher_even_moment {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ i, ‖toEuclidean_fromVec (y i)‖ ≤ R) (q : ℕ) (hq : 1 ≤ q) :
    (2:ℝ)^(-(r:ℤ))*(∑ s,‖sketchSignMatrix (fun i=>Matrix.vecMulVec (y i) (star (y i))) s‖^(2*q)) ≤
      (r:ℝ)*((2*q-1 : ℕ):ℝ)^q*(R^2*‖∑ i,Matrix.vecMulVec (y i) (star (y i))‖)^q := by
  let B := fun i=>Matrix.vecMulVec (y i) (star (y i))
  let V := ∑ i,B i*B i
  have hB (i : Fin r) : (B i).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hh (s : Fin r → Bool) : (sketchSignMatrix B s).IsHermitian :=
    isSelfAdjoint_sum _ (fun i _ => (hB i).isHermitian.smul (by cases s i <;> simp [sketchSign, IsSelfAdjoint]))
  have hV : V.PosSemidef := Matrix.posSemidef_sum _ (fun i _=>by
    simpa only [pow_two] using! (hB i).pow 2)
  have ht := sketch_psd_trace_power_rank_bound V hV q (by omega)
  have hr : V.rank ≤ r := by simpa [V,pow_two] using! sketch_covariance_variance_rank y
  have hn : ‖V‖ ≤ R^2*‖∑ i,B i‖ := by
    simpa [V,pow_two] using! sketch_covariance_variance_norm y R hR hy
  have hb : (Matrix.trace (V^q)).re ≤ (r:ℝ)*(R^2*‖∑ i,B i‖)^q := ht.trans
    (mul_le_mul (by exact_mod_cast hr) (pow_le_pow_left₀ (norm_nonneg _) hn q)
      (pow_nonneg (norm_nonneg _) q) (by positivity))
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ)=>
    sketch_hermitian_operator_even_trace (sketchSignMatrix B s) (hh s) q (by omega))
  have hc : 0 ≤ ((2*q-1 : ℕ):ℝ)^q := by positivity
  have hw : 0 ≤ (2:ℝ)^(-(r:ℤ)) := by positivity
  have h := (mul_le_mul_of_nonneg_left hs hw).trans
    ((sketchSign_trace_moment B q hq (fun i=>(hB i).isHermitian)).trans
      (mul_le_mul_of_nonneg_left hb hc))
  dsimp [B,V] at h ⊢
  convert! h using 1
  ring

/-- For nonnegative values under probability weights, a bound on the nth moment by Yⁿ implies
the bound Yᵖ on every positive moment order p ≤ n. -/
theorem sketch_finite_lower_moment {I : Type*} [Fintype I] (w x : I → ℝ) (p n : ℕ)
    (hp : 1 ≤ p) (hpn : p ≤ n) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i,w i=1)
    (hx : ∀ i, 0 ≤ x i) (Y : ℝ) (hY : 0 ≤ Y)
    (hbound : (∑ i,w i*x i^n) ≤ Y^n) : (∑ i,w i*x i^p) ≤ Y^p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hn : (p:ℝ)≤n := by exact_mod_cast hpn
  have hm := Real.arith_mean_le_rpow_mean Finset.univ w (fun i=>x i^p)
    (fun i _=>hw i) hw1 (fun i _=>pow_nonneg (hx i) _)
    (p := (n:ℝ)/(p:ℝ)) ((le_div_iff₀ hpR).mpr (by simpa))
  have he (i : I) : (x i^p)^((n:ℝ)/(p:ℝ))=x i^n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i)]
    have hc : (p:ℝ)*((n:ℝ)/(p:ℝ))=n := by field_simp
    rw [hc,Real.rpow_natCast]
  simp_rw [he] at hm
  have h := hm.trans (Real.rpow_le_rpow
    (Finset.sum_nonneg (fun i _=>mul_nonneg (hw i) (pow_nonneg (hx i) _))) hbound (by positivity))
  have hy : (Y^n)^(1/((n:ℝ)/(p:ℝ)))=Y^p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY]
    have hc : (n:ℝ)*(1/((n:ℝ)/(p:ℝ)))=p := by field_simp
    rw [hc,Real.rpow_natCast]
  rw [hy] at h
  exact h

/-- For r ≥ 2 and p ≥ 1, there is a positive moment index `q` with p ≤ 2q and r(2q - 1)ᑫ ≤ (16(p
+ log r))ᑫ. -/
theorem sketch_rademacher_moment_choice (r p : ℕ) (hr : 2 ≤ r) (hp : 1 ≤ p) :
    ∃ q : ℕ, 1 ≤ q ∧ p ≤ 2*q ∧
      (r:ℝ)*((2*q-1 : ℕ):ℝ)^q ≤ (16*((p:ℝ)+Real.log (r:ℝ)))^q := by
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hrpos : (0:ℝ)<r := by linarith
  have hpR : (1:ℝ)≤p := by exact_mod_cast hp
  have hl : 0 ≤ Real.log (r:ℝ) := Real.log_nonneg (by linarith)
  let L := (p:ℝ)+Real.log (r:ℝ)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  let q : ℕ := ⌈L⌉₊
  have hq : 1 ≤ q := Nat.one_le_ceil_iff.mpr (by linarith)
  have hlow : L ≤ (q:ℝ) := Nat.le_ceil L
  have hhi : (q:ℝ)<L+1 := Nat.ceil_lt_add_one (by linarith)
  have hpn : p ≤ 2*q := by
    have h : (p:ℝ)≤2*(q:ℝ) := by dsimp [L] at hlow; nlinarith
    exact_mod_cast h
  have hrpow : (r:ℝ) ≤ (4:ℝ)^q := by
    have h := Real.exp_le_exp.mpr (show Real.log (r:ℝ)≤q by dsimp [L] at hlow; linarith)
    rw [Real.exp_log hrpos] at h
    have he : Real.exp (q:ℝ)=(Real.exp 1)^q := by rw [← Real.exp_nat_mul, mul_one]
    rw [he] at h
    exact h.trans (pow_le_pow_left₀ (Real.exp_nonneg 1) (by linarith [Real.exp_one_lt_three]) q)
  have hcoef : ((2*q-1 : ℕ):ℝ) ≤ 4*L := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    nlinarith
  refine ⟨q,hq,hpn,?_⟩
  have h := mul_le_mul hrpow (pow_le_pow_left₀ (by positivity) hcoef q)
    (by positivity : (0:ℝ)≤((2*q-1 : ℕ):ℝ)^q) (by positivity : (0:ℝ)≤4^q)
  calc
    _ ≤ (4:ℝ)^q*(4*L)^q := h
    _ = _ := by rw [← mul_pow]; congr 1; dsimp [L]; ring

/-- For r ≥ 2 and p ≥ 1, the averaged pth norm moment of a signed covariance sum is bounded by
the pth power of 4R sqrt(p + log r) times the square root of the covariance sum norm. -/
theorem sketch_covariance_rademacher_moment {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ i, ‖toEuclidean_fromVec (y i)‖ ≤ R) (p : ℕ) (hp : 1 ≤ p) (hr : 2 ≤ r) :
    (2:ℝ)^(-(r:ℤ))*(∑ s,‖sketchSignMatrix (fun i=>Matrix.vecMulVec (y i) (star (y i))) s‖^p) ≤
      (4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R*
        Real.sqrt ‖∑ i,Matrix.vecMulVec (y i) (star (y i))‖)^p := by
  obtain ⟨q,hq,hpq,hchoice⟩ := sketch_rademacher_moment_choice r p hr hp
  let B := fun i=>Matrix.vecMulVec (y i) (star (y i))
  let w : ℝ := (2:ℝ)^(-(r:ℤ))
  let L := (p:ℝ)+Real.log (r:ℝ)
  let Y := 4*Real.sqrt L*R*Real.sqrt ‖∑ i,B i‖
  let x := fun s=>‖sketchSignMatrix B s‖
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg (Nat.cast_nonneg p) (Real.log_nonneg (by exact_mod_cast (by omega : 1≤r)))
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hsq : Y^2=16*L*(R^2*‖∑ i,B i‖) := by
    dsimp [Y]
    simp only [mul_pow, Real.sq_sqrt hL, Real.sq_sqrt (norm_nonneg (∑ i,B i))]
    ring
  have he : Y^(2*q)=(16*L)^q*(R^2*‖∑ i,B i‖)^q := by
    rw [pow_mul,hsq,mul_pow]
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : (∑ s : Fin r → Bool,w)=1 := by
    simp [w,_root_.zpow_neg,zpow_natCast,nsmul_eq_mul]
  have hh := sketch_covariance_rademacher_even_moment y R hR hy q hq
  have hbound : (∑ s,w*x s^(2*q)) ≤ Y^(2*q) := by
    rw [he,← Finset.mul_sum]
    exact hh.trans (by
      calc
        (r:ℝ)*((2*q-1 : ℕ):ℝ)^q*(R^2*‖∑ i,B i‖)^q ≤
            (16*L)^q*(R^2*‖∑ i,B i‖)^q :=
          mul_le_mul_of_nonneg_right hchoice (by positivity))
  have h := sketch_finite_lower_moment (fun _=>w) x p (2*q) hp hpq (fun _=>hw) hw1
    (fun _=>norm_nonneg _) Y hY hbound
  rw [← Finset.mul_sum] at h
  exact h

/-- The norm power of a finite matrix expectation is at most the expectation of the
corresponding norm power. -/
theorem sketch_finite_matrix_jensen {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (F : K → Matrix C C ℂ) (p : ℕ) :
    ‖∑ k,law.prob k • F k‖^p ≤ law.expect (fun k=>‖F k‖^p) := by
  have hn : ‖∑ k,law.prob k • F k‖ ≤ ∑ k,law.prob k*‖F k‖ := by
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro k _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (law.nonneg k)]
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ law.prob (fun k=>‖F k‖)
    (fun k _=>law.nonneg k) law.sum_one (fun _ _=>norm_nonneg _) p
  exact (pow_le_pow_left₀ (norm_nonneg _) hn p).trans h

/-- Taking the expectation of `X - F` gives `X` minus the expectation of `F`. -/
theorem sketch_finite_matrix_center_mean {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (F : K → Matrix C C ℂ) (X : Matrix C C ℂ) :
    (∑ k,law.prob k • (X-F k)) = X-(∑ k,law.prob k • F k) := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, law.sum_one, one_smul]

/-- For a positive sample count, the expectation of the average of independent matrix samples
equals the single-sample mean. -/
theorem sketch_independent_matrix_mean {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (F : K → Matrix C C ℂ) (r : ℕ) (hr : 0 < r) :
    (∑ ω : Fin r → K,(independentSampleLaw (fun _ : Fin r=>law)).prob ω •
      ((r:ℝ)⁻¹ • (∑ i,F (ω i)))) = ∑ k,law.prob k • F k := by
  ext a b
  apply Complex.ext
  · simp only [Matrix.sum_apply,Matrix.smul_apply,Complex.smul_re,Complex.re_sum]
    convert! law.expect_avg (fun k=>(F k a b).re) hr using 1
    simp [FinDist.avg,independentSampleLaw,FinDist.probOf,
        div_eq_mul_inv,mul_assoc,mul_comm]
  · simp only [Matrix.sum_apply,Matrix.smul_apply,Complex.smul_im,Complex.im_sum]
    convert! law.expect_avg (fun k=>(F k a b).im) hr using 1
    simp [FinDist.avg,independentSampleLaw,FinDist.probOf,
        div_eq_mul_inv,mul_assoc,mul_comm]

/-- The pair of sample tuples obtained by exchanging their coordinates where the Boolean
selector is false. -/
def sketchGhostSwap {K : Type} {r : ℕ} (s : Fin r → Bool)
    (ω : (Fin r → K) × (Fin r → K)) : (Fin r → K) × (Fin r → K) :=
  (fun i=>if s i then ω.1 i else ω.2 i, fun i=>if s i then ω.2 i else ω.1 i)

/-- Applying the same coordinatewise exchange to a pair of sample tuples twice restores the
pair. -/
theorem sketchGhostSwap_involutive {K : Type} {r : ℕ} (s : Fin r → Bool) :
    Function.Involutive (sketchGhostSwap (K := K) s) := by
  intro ω
  apply Prod.ext <;> funext i <;> cases hs : s i <;> simp [sketchGhostSwap,hs]

/-- The coordinatewise exchange preserves the product probability of two independent sample
tuples. -/
theorem sketchGhostSwap_weight {K : Type} [Fintype K] [DecidableEq K] {r : ℕ}
    (law : FinDist K) (s : Fin r → Bool) (ω : (Fin r → K) × (Fin r → K)) :
    law.probOf (sketchGhostSwap s ω).1 * law.probOf (sketchGhostSwap s ω).2 =
      law.probOf ω.1*law.probOf ω.2 := by
  unfold FinDist.probOf
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hs : s i <;> simp [sketchGhostSwap,hs,mul_comm]

/-- The difference of matrix sums after the coordinatewise exchange is the signed sum of the
original coordinate differences. -/
theorem sketchGhostSwap_difference {K C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (F : K → Matrix C C ℂ) (s : Fin r → Bool) (ω : (Fin r → K) × (Fin r → K)) :
    (∑ i,F ((sketchGhostSwap s ω).1 i))-(∑ i,F ((sketchGhostSwap s ω).2 i)) =
      sketchSignMatrix (fun i=>F (ω.1 i)-F (ω.2 i)) s := by
  rw [← Finset.sum_sub_distrib]
  unfold sketchSignMatrix
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s i <;> simp [sketchGhostSwap,sketchSign,hs]

/-- The expectation of a function of two sample-sum differences is unchanged when the
differences are replaced by signed coordinate differences. -/
theorem sketchGhostSwap_sum {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    {r : ℕ} (law : FinDist K) (F : K → Matrix C C ℂ) (s : Fin r → Bool)
    (g : Matrix C C ℂ → ℝ) :
    (∑ ω : (Fin r → K) × (Fin r → K),law.probOf ω.1*law.probOf ω.2*
      g ((∑ i,F (ω.1 i))-(∑ i,F (ω.2 i)))) =
    (∑ ω : (Fin r → K) × (Fin r → K),law.probOf ω.1*law.probOf ω.2*
      g (sketchSignMatrix (fun i=>F (ω.1 i)-F (ω.2 i)) s)) := by
  have h := Equiv.sum_comp ((sketchGhostSwap_involutive (K := K) s).toPerm)
    (fun ω : (Fin r → K) × (Fin r → K)=>law.probOf ω.1*law.probOf ω.2*
      g ((∑ i,F (ω.1 i))-(∑ i,F (ω.2 i))))
  simp only [Function.Involutive.coe_toPerm,sketchGhostSwap_weight,sketchGhostSwap_difference] at h
  exact h.symm

/-- For a positive sample count, the centered sample-mean norm moment is at most the
corresponding moment of the difference from an independent sample mean. -/
theorem sketch_matrix_ghost_jensen {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (F : K → Matrix C C ℂ) (r p : ℕ) (hr : 0 < r) :
    (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
      ‖(r:ℝ)⁻¹ • (∑ i,F (ω i))-(∑ k,law.prob k • F k)‖^p) ≤
    (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
      (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ν=>
        ‖(r:ℝ)⁻¹ • (∑ i,F (ω i))-(r:ℝ)⁻¹ • (∑ i,F (ν i))‖^p)) := by
  let Q := independentSampleLaw (fun _ : Fin r=>law)
  have h (ω : Fin r → K) := sketch_finite_matrix_jensen Q
    (fun ν=>(r:ℝ)⁻¹ • (∑ i,F (ω i))-(r:ℝ)⁻¹ • (∑ i,F (ν i))) p
  have hm := sketch_independent_matrix_mean law F r hr
  have hj (ω : Fin r → K) :
      ‖(r:ℝ)⁻¹ • (∑ i,F (ω i))-(∑ k,law.prob k • F k)‖^p ≤
      Q.expect (fun ν=>‖(r:ℝ)⁻¹ • (∑ i,F (ω i))-(r:ℝ)⁻¹ • (∑ i,F (ν i))‖^p) := by
    have hh := h ω
    rw [sketch_finite_matrix_center_mean,hm] at hh
    exact hh
  exact Finset.sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hj ω) (Q.nonneg ω))

/-- The expected function of the difference of two independent matrix sample sums equals its
average over signed coordinate differences. -/
theorem sketch_matrix_ghost_sign_average {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (F : K → Matrix C C ℂ) (r : ℕ) (g : Matrix C C ℂ → ℝ) :
    (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
      (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ν=>
        g ((∑ i,F (ω i))-(∑ i,F (ν i))))) =
      (2:ℝ)^(-(r:ℤ))*(∑ s,
        (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
          (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ν=>
            g (sketchSignMatrix (fun i=>F (ω i)-F (ν i)) s)))) := by
  let Q := independentSampleLaw (fun _ : Fin r=>law)
  let D := Q.expect (fun ω=>Q.expect (fun ν=>g ((∑ i,F (ω i))-(∑ i,F (ν i)))))
  have he (s : Fin r → Bool) : D = Q.expect (fun ω=>Q.expect (fun ν=>
      g (sketchSignMatrix (fun i=>F (ω i)-F (ν i)) s))) := by
    have h := sketchGhostSwap_sum law F s g
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
    dsimp [D,Q,FinDist.expect,independentSampleLaw]
    simp only [FinDist.probOf,mul_assoc] at h
    simpa only [Finset.mul_sum,mul_assoc] using! h
  have hw : (2:ℝ)^(-(r:ℤ))*(∑ _ : Fin r → Bool,(1:ℝ))=1 := by
    simp [_root_.zpow_neg,zpow_natCast,nsmul_eq_mul]
  change D = _
  calc
    D = (2:ℝ)^(-(r:ℤ))*(∑ _ : Fin r → Bool,D) := by
      have hc : (∑ _ : Fin r → Bool,D)=(∑ _ : Fin r → Bool,(1:ℝ))*D := by
        rw [Finset.sum_mul]
        simp only [one_mul]
      rw [hc,← mul_assoc,hw,one_mul]
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl (fun s _=>he s)

/-- The pth power of the norm of X - Y is at most 2ᵖ times the sum of the pth norm powers of `X`
and `Y`. -/
theorem sketch_matrix_sub_power_bound {C : Type} [Fintype C] [DecidableEq C] (X Y : Matrix C C ℂ) (p : ℕ) :
    ‖X-Y‖^p ≤ (2:ℝ)^p*(‖X‖^p+‖Y‖^p) := by
  by_cases hxy : ‖X‖ ≤ ‖Y‖
  · have hn : ‖X-Y‖ ≤ 2*‖Y‖ := (norm_sub_le X Y).trans (by linarith)
    have h := pow_le_pow_left₀ (norm_nonneg _) hn p
    rw [mul_pow] at h
    exact h.trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg (norm_nonneg X) p)) (by positivity))
  · have hn : ‖X-Y‖ ≤ 2*‖X‖ := (norm_sub_le X Y).trans (by linarith)
    have h := pow_le_pow_left₀ (norm_nonneg _) hn p
    rw [mul_pow] at h
    exact h.trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (norm_nonneg Y) p)) (by positivity))

/-- The signed sum of matrix differences equals the difference of the signed sums. -/
theorem sketchSignMatrix_sub {C : Type} {r : ℕ} (B D : Fin r → Matrix C C ℂ) (s : Fin r → Bool) :
    sketchSignMatrix (fun i=>B i-D i) s=sketchSignMatrix B s-sketchSignMatrix D s := by
  simp only [sketchSignMatrix,smul_sub,Finset.sum_sub_distrib]

/-- Finite expectation distributes over a scalar multiple of the sum of two real-valued
functions. -/
theorem sketch_finite_expect_scale_add {K : Type} [Fintype K] [DecidableEq K] (law : FinDist K) (f g : K → ℝ) (c : ℝ) :
    law.expect (fun k=>c*(f k+g k))=c*(law.expect f+law.expect g) := by
  simp only [FinDist.expect,Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring

/-- For p ≥ 1, the norm moment of the difference of two independent sample means is bounded by
4ᵖ times the sign-averaged norm moment of one signed sample mean. -/
theorem sketch_matrix_ghost_rademacher_bound {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (F : K → Matrix C C ℂ) (r p : ℕ) (hp : 1 ≤ p) :
    (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
      (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ν=>
        ‖(r:ℝ)⁻¹ • ((∑ i,F (ω i))-(∑ i,F (ν i)))‖^p)) ≤
    (4:ℝ)^p*(2:ℝ)^(-(r:ℤ))*(∑ s,
      (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
        ‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p)) := by
  let Q := independentSampleLaw (fun _ : Fin r=>law)
  let h : (Fin r → Bool) → (Fin r → K) → ℝ :=
      fun s ω=>‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p
  have hc : (2:ℝ)^p*2 ≤ (4:ℝ)^p := by
    have hp2 : (2:ℝ)≤2^p := by
      simpa using! (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hp)
    calc
      _ ≤ (2:ℝ)^p*2^p := mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hb (s : Fin r → Bool) :
      Q.expect (fun ω=>Q.expect (fun ν=>‖(r:ℝ)⁻¹ •
        sketchSignMatrix (fun i=>F (ω i)-F (ν i)) s‖^p)) ≤
          (4:ℝ)^p*Q.expect (h s) := by
    have hn : 0 ≤ Q.expect (h s) := Finset.sum_nonneg (fun ω _=>
      mul_nonneg (Q.nonneg ω) (by dsimp [h]; positivity))
    have hpoint (ω ν : Fin r → K) : ‖(r:ℝ)⁻¹ •
        sketchSignMatrix (fun i=>F (ω i)-F (ν i)) s‖^p ≤
          (2:ℝ)^p*(h s ω+h s ν) := by
      rw [sketchSignMatrix_sub,smul_sub]
      exact sketch_matrix_sub_power_bound _ _ p
    have he (ω : Fin r → K) : Q.expect (fun ν=>(2:ℝ)^p*(h s ω+h s ν)) =
        (2:ℝ)^p*(h s ω+Q.expect (h s)) := by
      rw [sketch_finite_expect_scale_add,Q.expect_const]
    have he2 : Q.expect (fun ω=>(2:ℝ)^p*(h s ω+Q.expect (h s))) =
        (2:ℝ)^p*(Q.expect (h s)+Q.expect (h s)) := by
      rw [sketch_finite_expect_scale_add,Q.expect_const]
    have hh : Q.expect (fun ω=>Q.expect (fun ν=>‖(r:ℝ)⁻¹ •
        sketchSignMatrix (fun i=>F (ω i)-F (ν i)) s‖^p)) ≤
        Q.expect (fun ω=>Q.expect (fun ν=>(2:ℝ)^p*(h s ω+h s ν))) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (Q.nonneg ω)
      exact Finset.sum_le_sum (fun ν _=>mul_le_mul_of_nonneg_left (hpoint ω ν) (Q.nonneg ν))
    simp_rw [he] at hh
    rw [he2] at hh
    have hc' := mul_le_mul_of_nonneg_right hc hn
    exact hh.trans (by nlinarith)
  have hsign := sketch_matrix_ghost_sign_average law F r (fun Z=>‖(r:ℝ)⁻¹ • Z‖^p)
  rw [hsign]
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ)=>hb s))
      (by positivity : (0:ℝ)≤2^(-(r:ℤ)))
  rw [← Finset.mul_sum] at hs
  convert! hs using 1
  ring

/-- If nonnegative `M` satisfies M ≤ Aᵖ(sqrt M + 1), then any Z ≤ min(M, 1) is bounded by (2A)ᵖ
for p ≥ 1 and nonnegative `A`. -/
theorem sketch_truncated_moment_self_bound (M A Z : ℝ) (p : ℕ) (hp : 1 ≤ p) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hrec : M ≤ A^p*(Real.sqrt M+1)) (hZM : Z ≤ M) (hZ1 : Z ≤ 1) :
    Z ≤ (2*A)^p := by
  have hAp : 0 ≤ A^p := pow_nonneg hA p
  have hp2 : (2:ℝ)≤2^p := by
    simpa using! pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hp
  have hs := Real.sq_sqrt hM
  have hsn := Real.sqrt_nonneg M
  have hcoef : 2*A^p ≤ (2*A)^p := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hp2 hAp
  by_cases hle : M ≤ 1
  · have hs1 : Real.sqrt M ≤ 1 := by nlinarith
    exact hZM.trans ((hrec.trans (by nlinarith)).trans hcoef)
  · have hs1 : 1 ≤ Real.sqrt M := by nlinarith
    have hsp : 0 < Real.sqrt M := by linarith
    have hmul : Real.sqrt M*Real.sqrt M ≤ (2*A^p)*Real.sqrt M := by nlinarith
    have hbound : Real.sqrt M ≤ 2*A^p := (mul_le_mul_iff_left₀ hsp).mp hmul
    exact hZ1.trans (hs1.trans (hbound.trans hcoef))

/-- For a nonnegative finite random variable, the pth moment of its square root is at most the
square root of its pth moment. -/
theorem sketch_finite_root_moment {K : Type} [Fintype K] [DecidableEq K] (law : FinDist K)
    (e : K → ℝ) (he : ∀ k,0 ≤ e k) (p : ℕ) :
    law.expect (fun k=>(Real.sqrt (e k))^p) ≤ Real.sqrt (law.expect (fun k=>e k^p)) := by
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ law.prob
    (fun k=>(Real.sqrt (e k))^p) (fun k _=>law.nonneg k) law.sum_one
    (fun k _=>pow_nonneg (Real.sqrt_nonneg _) p) 2
  have hp (k : K) : ((Real.sqrt (e k))^p)^2=e k^p := by
    rw [← pow_mul, Nat.mul_comm p 2, pow_mul, Real.sq_sqrt (he k)]
  simp_rw [hp] at h
  have hn : 0 ≤ law.expect (fun k=>(Real.sqrt (e k))^p) :=
    Finset.sum_nonneg (fun k _=>mul_nonneg (law.nonneg k) (by positivity))
  have hM : 0 ≤ law.expect (fun k=>e k^p) :=
    Finset.sum_nonneg (fun k _=>mul_nonneg (law.nonneg k) (pow_nonneg (he k) p))
  change (law.expect (fun k=>(Real.sqrt (e k))^p))^2 ≤ law.expect (fun k=>e k^p) at h
  nlinarith [Real.sq_sqrt hM,Real.sqrt_nonneg (law.expect (fun k=>e k^p))]

/-- For nonnegative `e`, the pth power of sqrt(e + 1) is at most sqrt(2)ᵖ times the sum of
sqrt(e)ᵖ and one. -/
theorem sketch_root_add_one_power (e : ℝ) (he : 0 ≤ e) (p : ℕ) :
    (Real.sqrt (e+1))^p ≤ (Real.sqrt 2)^p*((Real.sqrt e)^p+1) := by
  have hs : (0:ℝ)≤Real.sqrt 2 := Real.sqrt_nonneg _
  have hp : (0:ℝ)≤(Real.sqrt 2)^p := pow_nonneg hs _
  by_cases hle : e ≤ 1
  · have h := pow_le_pow_left₀ (Real.sqrt_nonneg (e+1))
      (Real.sqrt_le_sqrt (by linarith : e+1≤2)) p
    exact h.trans (by nlinarith [pow_nonneg (Real.sqrt_nonneg e) p])
  · have hsq : Real.sqrt (e+1) ≤ Real.sqrt 2*Real.sqrt e := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hs (Real.sqrt_nonneg e))).mp
      rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt he,
        Real.sq_sqrt (by linarith : 0≤e+1)]
      linarith
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg (e+1)) hsq p
    rw [mul_pow] at h
    exact h.trans (by nlinarith)

/-- For r ≥ 2 and p ≥ 1, the pth norm moment of the signed covariance average is bounded by the
stated radius, logarithmic, and covariance norm factors. -/
theorem sketch_covariance_rademacher_average_moment {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ i,‖toEuclidean_fromVec (y i)‖ ≤ R) (p : ℕ) (hp : 1 ≤ p) (hr : 2 ≤ r) :
    (2:ℝ)^(-(r:ℤ))*(∑ s,‖(r:ℝ)⁻¹ • sketchSignMatrix
      (fun i=>Matrix.vecMulVec (y i) (star (y i))) s‖^p) ≤
    (4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ))^p*
      (Real.sqrt ‖∑ i,Matrix.vecMulVec (y i) (star (y i))‖)^p := by
  have hrR : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  have h := sketch_covariance_rademacher_moment y R hR hy p hp hr
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hrR)),mul_pow]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hrR.le) p)
  calc
    _ = (r:ℝ)⁻¹^p*((2:ℝ)^(-(r:ℤ))*(∑ s,‖sketchSignMatrix
        (fun i=>Matrix.vecMulVec (y i) (star (y i))) s‖^p)) := by ring
    _ ≤ (r:ℝ)⁻¹^p*(4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R*
        Real.sqrt ‖∑ i,Matrix.vecMulVec (y i) (star (y i))‖)^p := hh
    _ = _ := by rw [mul_pow,mul_pow,div_pow]; ring

/-- If the reference matrix has norm at most one and `r` is positive, the square-root norm power
of a matrix sum is bounded by the stated factor times one plus the square-root deviation
power of its average. -/
theorem sketch_matrix_sum_root_deviation {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (F : Fin r → Matrix C C ℂ) (M : Matrix C C ℂ) (hM : ‖M‖ ≤ 1)
    (hr : 0 < r) (p : ℕ) :
    (Real.sqrt ‖∑ i,F i‖)^p ≤
      (Real.sqrt (r:ℝ)*Real.sqrt 2)^p*
        ((Real.sqrt ‖(r:ℝ)⁻¹ • (∑ i,F i)-M‖)^p+1) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  let X := (r:ℝ)⁻¹ • (∑ i,F i)
  have hx : ‖X‖ ≤ ‖X-M‖+1 := (norm_le_norm_sub_add X M).trans (by linarith)
  have he : ‖∑ i,F i‖=(r:ℝ)*‖X‖ := by
    dsimp [X]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hrR.le),
      ← mul_assoc,mul_inv_cancel₀ (ne_of_gt hrR),one_mul]
  have hn := Real.sqrt_le_sqrt (show ‖∑ i,F i‖ ≤ (r:ℝ)*(‖X-M‖+1) by
    rw [he]; exact mul_le_mul_of_nonneg_left hx hrR.le)
  rw [Real.sqrt_mul hrR.le] at hn
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn p
  rw [mul_pow] at hp
  have h := mul_le_mul_of_nonneg_left (sketch_root_add_one_power ‖X-M‖ (norm_nonneg _) p)
    (pow_nonneg (Real.sqrt_nonneg (r:ℝ)) p)
  exact hp.trans (by simpa only [mul_pow,mul_assoc] using! h)

/-- Finite expectation commutes with multiplication by a real scalar. -/
theorem sketch_finite_expect_scale {K : Type} [Fintype K] [DecidableEq K] (law : FinDist K) (f : K → ℝ) (c : ℝ) :
    law.expect (fun k=>c*f k)=c*law.expect f := by
  simpa only [add_zero,law.expect_const] using! sketch_finite_expect_scale_add law f (fun _=>0) c

/-- A finite sum of expectations equals the expectation of the finite sum. -/
theorem sketch_finite_expect_sum {K I : Type} [Fintype K] [DecidableEq K] [Fintype I]
    (law : FinDist K) (f : I → K → ℝ) :
    (∑ i,law.expect (f i))=law.expect (fun k=>∑ i,f i k) := by
  simp only [FinDist.expect,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Pointwise comparison of real functions implies comparison of their finite expectations. -/
theorem sketch_finite_expect_mono {K : Type} [Fintype K] [DecidableEq K] (law : FinDist K) (f g : K → ℝ)
    (h : ∀ k,f k≤g k) : law.expect f ≤ law.expect g := by
  exact Finset.sum_le_sum (fun k _=>mul_le_mul_of_nonneg_left (h k) (law.nonneg k))

/-- For bounded vectors, r ≥ 2, p ≥ 1, and a covariance mean of norm at most one, the centered
covariance norm moment `M` satisfies the stated bound by a coefficient times sqrt M + 1. -/
theorem sketch_covariance_moment_self_bound {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (y : K → C → ℂ) (R : ℝ) (r p : ℕ)
    (hr : 2 ≤ r) (hp : 1 ≤ p) (hR : 0 ≤ R)
    (hy : ∀ k,‖toEuclidean_fromVec (y k)‖ ≤ R)
    (hmean : ‖∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k))‖ ≤ 1) :
    let Q := independentSampleLaw (fun _ : Fin r=>law)
    let e := fun ω : Fin r → K=>‖(r:ℝ)⁻¹ • (∑ i,Matrix.vecMulVec (y (ω i)) (star (y (ω i))))-
      (∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k)))‖
    let M := Q.expect (fun ω=>e ω^p)
    M ≤ (4*(4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ))*(Real.sqrt (r:ℝ)*Real.sqrt 2))^p*
      (Real.sqrt M+1) := by
  let Q := independentSampleLaw (fun _ : Fin r=>law)
  let F := fun k=>Matrix.vecMulVec (y k) (star (y k))
  let B := ∑ k,law.prob k • F k
  let e := fun ω : Fin r → K=>‖(r:ℝ)⁻¹ • (∑ i,F (ω i))-B‖
  let M := Q.expect (fun ω=>e ω^p)
  let w := (2:ℝ)^(-(r:ℤ))
  let c := 4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ)
  let d := Real.sqrt (r:ℝ)*Real.sqrt 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hj := sketch_matrix_ghost_jensen law F r p (by omega)
  have hg := sketch_matrix_ghost_rademacher_bound law F r p hp
  simp_rw [smul_sub] at hg
  have hfirst : M ≤ (4:ℝ)^p*w*(∑ s,Q.expect (fun ω=>
      ‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p)) := hj.trans hg
  have hswap : w*(∑ s,Q.expect (fun ω=>
      ‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p)) =
      Q.expect (fun ω=>w*(∑ s,‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p)) := by
    rw [sketch_finite_expect_sum,sketch_finite_expect_scale]
  have hsign (ω : Fin r → K) : w*(∑ s,‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p) ≤
      c^p*(Real.sqrt ‖∑ i,F (ω i)‖)^p :=
    sketch_covariance_rademacher_average_moment (fun i=>y (ω i)) R hR (fun i=>hy (ω i)) p hp hr
  have hdev (ω : Fin r → K) : (Real.sqrt ‖∑ i,F (ω i)‖)^p ≤
      d^p*((Real.sqrt (e ω))^p+1) :=
    sketch_matrix_sum_root_deviation (fun i=>F (ω i)) B hmean (by omega) p
  have hroot := sketch_finite_root_moment Q e (fun ω=>norm_nonneg _) p
  change M ≤ (4*c*d)^p*(Real.sqrt M+1)
  calc
    M ≤ (4:ℝ)^p*(w*(∑ s,Q.expect (fun ω=>
        ‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p))) := by simpa only [mul_assoc] using! hfirst
    _ = (4:ℝ)^p*Q.expect (fun ω=>w*(∑ s,‖(r:ℝ)⁻¹ • sketchSignMatrix (fun i=>F (ω i)) s‖^p)) := by rw [hswap]
    _ ≤ (4:ℝ)^p*Q.expect (fun ω=>c^p*(Real.sqrt ‖∑ i,F (ω i)‖)^p) :=
      mul_le_mul_of_nonneg_left (sketch_finite_expect_mono Q _ _ hsign) (by positivity)
    _ = (4:ℝ)^p*c^p*Q.expect (fun ω=>(Real.sqrt ‖∑ i,F (ω i)‖)^p) := by rw [sketch_finite_expect_scale,mul_assoc]
    _ ≤ (4:ℝ)^p*c^p*Q.expect (fun ω=>d^p*((Real.sqrt (e ω))^p+1)) :=
      mul_le_mul_of_nonneg_left (sketch_finite_expect_mono Q _ _ hdev) (by positivity)
    _ = (4:ℝ)^p*c^p*d^p*(Q.expect (fun ω=>(Real.sqrt (e ω))^p)+1) := by
      rw [sketch_finite_expect_scale_add,Q.expect_const]
      ring
    _ ≤ (4:ℝ)^p*c^p*d^p*(Real.sqrt M+1) :=
      mul_le_mul_of_nonneg_left (add_le_add hroot (le_refl 1)) (by positivity)
    _ = _ := by simp only [mul_pow,mul_assoc]

/-- For r ≥ 2, p ≥ 1, and nonnegative `R`, the covariance moment coefficient is at most 64R
sqrt(log r / r) sqrt p. -/
theorem sketch_covariance_coefficient (R : ℝ) (hR : 0 ≤ R) (r p : ℕ) (hr : 2 ≤ r) (hp : 1 ≤ p) :
    4*(4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ))*(Real.sqrt (r:ℝ)*Real.sqrt 2) ≤
      64*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ) := by
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hrp : (0:ℝ)<r := by linarith
  have hpR : (1:ℝ)≤p := by exact_mod_cast hp
  have hl : (1/2:ℝ)<Real.log (r:ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2) hrR
    linarith [Real.log_two_gt_d9]
  have hpl : (p:ℝ)+Real.log (r:ℝ) ≤ 3*(p:ℝ)*Real.log (r:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpR (by linarith : 0≤Real.log (r:ℝ))
    have h' := mul_le_mul_of_nonneg_left (le_of_lt hl) (by positivity : (0:ℝ)≤p)
    nlinarith
  have hL : 0≤(p:ℝ)+Real.log (r:ℝ) := by positivity
  have hlr : 0≤Real.log (r:ℝ)/(r:ℝ) := by positivity
  have hsq :
      (4*(4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ))*(Real.sqrt (r:ℝ)*Real.sqrt 2))^2 =
      512*R^2*((p:ℝ)+Real.log (r:ℝ))/(r:ℝ) := by
    rw [mul_pow,mul_pow,div_pow,mul_pow,mul_pow,Real.sq_sqrt hL,mul_pow,
      Real.sq_sqrt hrp.le,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    field_simp
    ring
  have ht : (64*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ))^2 =
      4096*R^2*Real.log (r:ℝ)/(r:ℝ)*(p:ℝ) := by
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hlr,Real.sq_sqrt (by positivity : (0:ℝ)≤p)]
    ring
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [hsq,ht]
  have hh := mul_le_mul_of_nonneg_left hpl (by positivity : 0≤512*R^2/(r:ℝ))
  have hn : 0≤R^2*Real.log (r:ℝ)/(r:ℝ)*(p:ℝ) := by positivity
  calc
    _ ≤ 1536*(R^2*Real.log (r:ℝ)/(r:ℝ)*(p:ℝ)) := by convert! hh using 1 <;> ring
    _ ≤ 4096*(R^2*Real.log (r:ℝ)/(r:ℝ)*(p:ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) hn
    _ = _ := by ring

/-- For bounded vectors with covariance mean norm at most one, r ≥ 2, and p ≥ 1, the moment of
the centered covariance error truncated at one is at most (128R sqrt(log r / r) sqrt p)ᵖ. -/
theorem sketch_covariance_truncated_moment {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (y : K → C → ℂ) (R : ℝ) (r p : ℕ)
    (hr : 2 ≤ r) (hp : 1 ≤ p) (hR : 0 ≤ R)
    (hy : ∀ k,‖toEuclidean_fromVec (y k)‖ ≤ R)
    (hmean : ‖∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k))‖ ≤ 1) :
    (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
      min ‖(r:ℝ)⁻¹ • (∑ i,Matrix.vecMulVec (y (ω i)) (star (y (ω i))))-
        (∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k)))‖ 1 ^p) ≤
      (128*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ))^p := by
  let Q := independentSampleLaw (fun _ : Fin r=>law)
  let e := fun ω : Fin r → K=>‖(r:ℝ)⁻¹ • (∑ i,Matrix.vecMulVec (y (ω i)) (star (y (ω i))))-
    (∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k)))‖
  let M := Q.expect (fun ω=>e ω^p)
  let Z := Q.expect (fun ω=>min (e ω) 1 ^p)
  let a := 4*(4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ))*(Real.sqrt (r:ℝ)*Real.sqrt 2)
  have hM : 0≤M := Finset.sum_nonneg (fun ω _=>mul_nonneg (Q.nonneg ω) (by dsimp [e]; positivity))
  have ha : 0≤a := by dsimp [a]; positivity
  have hm : Z≤M := sketch_finite_expect_mono Q _ _ (fun ω=>
    pow_le_pow_left₀ (le_min (norm_nonneg _) (by norm_num)) (min_le_left _ _) p)
  have h1 : Z≤1 := by
    have h := sketch_finite_expect_mono Q (fun ω=>min (e ω) 1 ^p) (fun _=>1^p) (fun ω=>
      pow_le_pow_left₀ (le_min (norm_nonneg _) (by norm_num)) (min_le_right _ _) p)
    simpa only [one_pow,Q.expect_const] using! h
  have hrec := sketch_covariance_moment_self_bound law y R r p hr hp hR hy hmean
  have h := sketch_truncated_moment_self_bound M a Z p hp hM ha hrec hm h1
  have hab := sketch_covariance_coefficient R hR r p hr hp
  change Z≤_
  calc
    Z≤(2*a)^p := h
    _≤(128*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ))^p := by
      apply pow_le_pow_left₀ (by positivity)
      calc
        2*a ≤ 2*(64*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ)) :=
          mul_le_mul_of_nonneg_left hab (by norm_num)
        _ = _ := by ring

/-- The conjugate of row `k` scaled by the reciprocal square root of its sampling probability
times `S`. -/
noncomputable def sketchNormalizedRow {K C : Type} [Fintype K] (p : FinDist K) (A : Matrix K C ℂ)
    (S : ℝ) (k : K) : C → ℂ := fun j=>(Real.sqrt (p.prob k*S))⁻¹ • star (A k j)

/-- For nonnegative `S`, the normalized row covariance atom is the Gram sampling atom scaled by
S⁻¹. -/
theorem sketchNormalizedRow_outer {K C : Type} [Fintype K] (p : FinDist K) (A : Matrix K C ℂ)
    (S : ℝ) (hS : 0≤S) (k : K) :
    Matrix.vecMulVec (sketchNormalizedRow p A S k) (star (sketchNormalizedRow p A S k)) =
      S⁻¹ • sketchSampleMatrix p A A k := by
  have hs : ((Real.sqrt (p.prob k*S))⁻¹)^2 = (p.prob k*S)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (mul_nonneg (p.nonneg k) hS)]
  have hsC := congrArg Complex.ofReal hs
  simp only [Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_mul] at hsC
  ext i j
  simp only [sketchNormalizedRow,Matrix.vecMulVec_apply,Pi.star_apply,
    Complex.real_smul,star_mul,Complex.star_def,map_inv₀,Complex.conj_ofReal,Complex.conj_conj,Complex.ofReal_inv,
    Matrix.smul_apply,sketchSampleMatrix]
  calc
    _ = ((Real.sqrt (p.prob k*S) : ℂ)⁻¹)^2*(star (A k i)*A k j) := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hsC,_root_.mul_inv_rev]; simp only [Complex.star_def]; ring

/-- For nonnegative `S`, the normalized row's squared Euclidean norm is its row energy divided
by its sampling probability times `S`. -/
theorem sketchNormalizedRow_norm_sq {K C : Type} [Fintype K] [Fintype C] (p : FinDist K)
    (A : Matrix K C ℂ) (S : ℝ) (hS : 0≤S) (k : K) :
    ‖toEuclidean_fromVec (sketchNormalizedRow p A S k)‖^2 = sketchRowSquared A k/(p.prob k*S) := by
  rw [norm_toEuclidean_fromVec_sq]
  simp only [sketchNormalizedRow,Complex.real_smul,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_pow]
  rw [← Finset.mul_sum,inv_pow,Real.sq_sqrt (mul_nonneg (p.nonneg k) hS)]
  simp only [sketchRowSquared,Complex.normSq_eq_norm_sq]
  ring
set_option warningAsError false
open scoped Matrix.Norms.Frobenius in

/-- A nonzero matrix has positive total squared energy. -/
theorem sketchSquared_pos_of_ne_zero {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) (hA : A≠0) :
    0<sketchSquared A := by
  rw [← sketch_frobenius_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hA)

/-- Under row energy domination and positive `S`, each normalized row has Euclidean norm at most
sqrt(φ times the total energy divided by S). -/
theorem sketchNormalizedRow_bound {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ S : ℝ) (hφ : 1≤φ) (hS : 0<S)
    (hE : 0<sketchSquared A) (hdom : ∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤p.prob k) (k : K) :
    ‖toEuclidean_fromVec (sketchNormalizedRow p A S k)‖ ≤ Real.sqrt (φ*sketchSquared A/S) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sketchNormalizedRow_norm_sq p A S hS.le,Real.sq_sqrt (by positivity : 0≤φ*sketchSquared A/S)]
  by_cases hk : p.prob k=0
  · simp only [hk,zero_mul,div_zero]
    positivity
  · have hp : 0<p.prob k := lt_of_le_of_ne (p.nonneg k) (Ne.symm hk)
    have hrow := (div_le_iff₀ (by positivity : 0<φ*sketchSquared A)).mp (hdom k)
    apply (div_le_iff₀ (mul_pos hp hS)).mpr
    have he : (φ*sketchSquared A/S)*(p.prob k*S)=p.prob k*(φ*sketchSquared A) := by field_simp
    rw [he]
    exact hrow

/-- The operator norm of AᴴA equals the square of the operator norm of `A`. -/
theorem sketchGram_norm {K C : Type} [Fintype K] [Fintype C] [DecidableEq C] (A : Matrix K C ℂ) :
    ‖Aᴴ*A‖=‖A‖^2 := by
  simpa only [pow_two] using! Matrix.l2_opNorm_conjTranspose_mul_self A

/-- Under row energy domination and nonnegative `S`, the mean normalized row covariance is S⁻¹
times AᴴA. -/
theorem sketchNormalizedRow_mean {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ S : ℝ) (hφ : 1≤φ) (hS : 0≤S)
    (hE : 0<sketchSquared A) (hdom : ∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤p.prob k) :
    (∑ k,p.prob k • Matrix.vecMulVec (sketchNormalizedRow p A S k) (star (sketchNormalizedRow p A S k))) =
      S⁻¹ • (Aᴴ*A) := by
  simp_rw [sketchNormalizedRow_outer p A S hS]
  rw [← sketchGram_mean_matrix p A φ hφ hE hdom,Finset.smul_sum]
  exact Finset.sum_congr rfl (fun k _=>smul_comm _ _ _)

/-- For positive `S` under row energy domination, the normalized covariance error equals the
Gram sketch operator error divided by `S`. -/
theorem sketchNormalizedRow_error {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ S : ℝ) (hφ : 1≤φ) (hS : 0<S)
    (hE : 0<sketchSquared A) (hdom : ∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤p.prob k)
    (r : ℕ) (ω : Fin r → K) :
    ‖(r:ℝ)⁻¹ • (∑ i,Matrix.vecMulVec (sketchNormalizedRow p A S (ω i)) (star (sketchNormalizedRow p A S (ω i))))-
      (∑ k,p.prob k • Matrix.vecMulVec (sketchNormalizedRow p A S k) (star (sketchNormalizedRow p A S k)))‖ =
      ‖sketchProduct p r A A ω-Aᴴ*A‖/S := by
  rw [sketchNormalizedRow_mean p A φ S hφ hS.le hE hdom]
  simp_rw [sketchNormalizedRow_outer p A S hS.le]
  rw [← Finset.smul_sum,smul_comm,← smul_sub]
  have hprod : (r:ℝ)⁻¹ • (∑ i,sketchSampleMatrix p A A (ω i))=sketchProduct p r A A ω := by
    rw [sketchProduct_matrix_average]
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,smul_eq_mul]
  rw [hprod,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hS.le)]
  ring

/-- For a nonzero matrix under row energy domination, normalization by the squared operator norm
makes the covariance mean have norm one. -/
theorem sketchNormalizedRow_mean_norm {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ) (hφ : 1≤φ) (hA : A≠0)
    (hdom : ∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤p.prob k) :
    ‖∑ k,p.prob k • Matrix.vecMulVec (sketchNormalizedRow p A (‖A‖^2) k)
      (star (sketchNormalizedRow p A (‖A‖^2) k))‖=1 := by
  have hS : 0<‖A‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hA)
  rw [sketchNormalizedRow_mean p A φ (‖A‖^2) hφ hS.le (sketchSquared_pos_of_ne_zero A hA) hdom,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hS.le),sketchGram_norm,
    inv_mul_cancel₀ (ne_of_gt hS)]

/-- For a nonnegative finite random variable and 0 ≤ t ≤ 1, tᵖ times the probability of
exceeding `t` is at most the pth moment of the variable truncated at one. -/
theorem sketch_finite_truncated_markov {X : Type} [Fintype X] [DecidableEq X] (law : FinDist X)
    (e : X → ℝ) (he : ∀ x,0≤e x) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (p : ℕ) :
    t^p*(∑ x ∈ Finset.univ.filter (fun x=>t<e x),law.prob x) ≤ law.expect (fun x=>min (e x) 1 ^p) := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x=>t<e x),law.prob x*min (e x) 1 ^p := by
      apply Finset.sum_le_sum
      intro x hx
      have hxt := (Finset.mem_filter.mp hx).2
      have hh := pow_le_pow_left₀ ht (le_min hxt.le ht1) p
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hh (law.nonneg x)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x _ _=>
      mul_nonneg (law.nonneg x) (pow_nonneg (le_min (he x) (by norm_num)) p))

/-- For 0 < δ < 1, there is a positive integer moment order p ≤ 2 log(4 / δ) with 2⁻ᵖ ≤ δ. -/
theorem sketch_tail_moment_choice (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ p : ℕ,1≤p ∧ (p:ℝ)≤2*Real.log (4/δ) ∧ (2:ℝ)^(-(p:ℤ))≤δ := by
  have hl2 : (1/2:ℝ)<Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2p : 0<Real.log 2 := by linarith
  have hld : Real.log δ<0 := Real.log_neg hδ hδ1
  let L := -Real.log δ/Real.log 2
  have hL : 0<L := div_pos (by linarith) hl2p
  let p : ℕ := ⌈L⌉₊
  have hp : 1≤p := Nat.one_le_ceil_iff.mpr hL
  have hlo : L≤(p:ℝ) := Nat.le_ceil L
  have hhi : (p:ℝ)<L+1 := Nat.ceil_lt_add_one hL.le
  have hlog4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hlogd : Real.log (4/δ)=2*Real.log 2-Real.log δ := by
    rw [Real.log_div (by norm_num) hδ.ne',hlog4]
  have hLhi : L≤2*(-Real.log δ) := by
    dsimp [L]
    apply (div_le_iff₀ hl2p).mpr
    nlinarith
  have hpm : (p:ℝ)≤2*Real.log (4/δ) := by rw [hlogd]; linarith
  have hplo : -Real.log δ≤(p:ℝ)*Real.log 2 := (div_le_iff₀ hl2p).mp hlo
  have hex := Real.exp_le_exp.mpr (show -(p:ℝ)*Real.log 2≤Real.log δ by linarith)
  rw [Real.exp_log hδ] at hex
  have he : Real.exp (-(p:ℝ)*Real.log 2)=(2:ℝ)^(-(p:ℤ)) := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2),
      _root_.zpow_neg,zpow_natCast]
  rw [he] at hex
  exact ⟨p,hp,hpm,hex⟩

/-- The stated sample budget and moment-order bound make the covariance moment scale at most η /
(2S) under the parameter assumptions. -/
theorem sketch_tail_budget (E S φ η δ : ℝ) (r p : ℕ) (hE : 0≤E) (hS : 0<S)
    (hφ : 1≤φ) (hη : 0≤η) (hr : 2≤r) (hδ : 0<δ) (hδ1 : δ<1)
    (hp : (p:ℝ)≤2*Real.log (4/δ))
    (hb : 131072*φ^2*E*S*Real.log (r:ℝ)*Real.log (4/δ)≤(r:ℝ)*η^2) :
    128*Real.sqrt (φ*E/S)*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ) ≤ η/(2*S) := by
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hrp : (0:ℝ)<r := by linarith
  have hlr : 0≤Real.log (r:ℝ) := Real.log_nonneg (by linarith)
  have hld : 0≤Real.log (4/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hφ2 : φ≤φ^2 := by nlinarith
  have hn : 65536*φ*E*S*Real.log (r:ℝ)*(p:ℝ)≤(r:ℝ)*η^2 := by
    calc
      _ ≤ 65536*φ*E*S*Real.log (r:ℝ)*(2*Real.log (4/δ)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 131072*φ*E*S*Real.log (r:ℝ)*Real.log (4/δ) := by ring
      _ ≤ 131072*φ^2*E*S*Real.log (r:ℝ)*Real.log (4/δ) := by
        have h :=
            mul_le_mul_of_nonneg_right hφ2
            (by positivity : 0≤131072*E*S*Real.log (r:ℝ)*Real.log (4/δ))
        convert! h using 1 <;> ring
      _ ≤ _ := hb
  have hs : (128*Real.sqrt (φ*E/S)*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ))^2 =
      16384*φ*E*Real.log (r:ℝ)*(p:ℝ)/(S*(r:ℝ)) := by
    simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤φ*E/S),
      Real.sq_sqrt (by positivity : 0≤Real.log (r:ℝ)/(r:ℝ)),Real.sq_sqrt (Nat.cast_nonneg p)]
    ring
  have ht : (η/(2*S))^2=η^2/(4*S^2) := by ring
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [hs,ht]
  apply (div_le_div_iff₀ (mul_pos hS hrp) (by positivity : 0<4*S^2)).mpr
  convert! mul_le_mul_of_nonneg_right hn hS.le using 1 <;> ring

/-- There is a universal positive constant such that the stated sample budget bounds the Gram
operator error probability by `δ`, for r ≥ 2 and a positive threshold no larger than the
squared operator norm. See [ChiaEtAl2022]. -/
theorem compact_sketch_operator_tail_nontrivial :
    ∃ c₀ : ℝ,0<c₀ ∧ ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
      (law : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (φ η δ : ℝ),
      2≤r → 1≤φ → 0<η → η≤‖A‖^2 → 0<δ → δ<1 →
      (∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤law.prob k) →
      c₀*φ^2*sketchSquared A*‖A‖^2*Real.log (r:ℝ)*Real.log (4/δ)≤(r:ℝ)*η^2 →
      compactGramOperatorBadMass law r A η≤δ := by
  refine ⟨131072,by norm_num,?_⟩
  intro K C _ _ _ _ law r A φ η δ hr hφ hη hηS hδ hδ1 hdom hb
  have hS : 0<‖A‖^2 := lt_of_lt_of_le hη hηS
  have hA : A≠0 := by intro hz; simp only [hz,norm_zero,zero_pow (by omega : 2≠0)] at hS; linarith
  have hE := sketchSquared_pos_of_ne_zero A hA
  obtain ⟨p,hp,hpbound,hptail⟩ := sketch_tail_moment_choice δ hδ hδ1
  let S := ‖A‖^2
  let R := Real.sqrt (φ*sketchSquared A/S)
  let y := sketchNormalizedRow law A S
  let Q := independentSampleLaw (fun _ : Fin r=>law)
  let e := fun ω : Fin r → K=>‖(r:ℝ)⁻¹ • (∑ i,Matrix.vecMulVec (y (ω i)) (star (y (ω i))))-
    (∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k)))‖
  let t := η/S
  have ht : 0<t := div_pos hη hS
  have ht1 : t≤1 := (div_le_one hS).mpr hηS
  have he (ω : Fin r → K) : e ω=‖sketchProduct law r A A ω-Aᴴ*A‖/S :=
    sketchNormalizedRow_error law A φ S hφ hS hE hdom r ω
  have hm := sketch_covariance_truncated_moment law y R r p hr hp (Real.sqrt_nonneg _)
    (sketchNormalizedRow_bound law A φ S hφ hS hE hdom)
    (le_of_eq (sketchNormalizedRow_mean_norm law A φ hφ hA hdom))
  have hbudget :=
      sketch_tail_budget (sketchSquared A) S φ η δ r p hE.le hS hφ hη.le hr hδ hδ1 hpbound hb
  have hprob : (∑ ω ∈ Finset.univ.filter (fun ω : Fin r → K=>t<e ω),Q.prob ω)=compactGramOperatorBadMass law r A η := by
    unfold compactGramOperatorBadMass FinDist.probEvent
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro ω _
      rw [he]
      exact div_lt_div_iff_of_pos_right hS
    · intro ω _
      rfl
  have hmark := sketch_finite_truncated_markov Q e (fun ω=>norm_nonneg _) t ht.le ht1 p
  rw [hprob] at hmark
  have hcoef : 128*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ) ≤ t/2 := by
    convert! hbudget using 1
    dsimp [R,t]
    ring
  have hpow := pow_le_pow_left₀ (by dsimp [R]; positivity :
      0≤128*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ)) hcoef p
  have hbad : t^p*compactGramOperatorBadMass law r A η≤(t/2)^p := hmark.trans (hm.trans hpow)
  have hpdiv : (t/2)^p=t^p*(2:ℝ)^(-(p:ℤ)) := by
    rw [div_pow,_root_.zpow_neg,zpow_natCast]
    ring
  rw [hpdiv] at hbad
  exact ((mul_le_mul_iff_right₀ (pow_pos ht p)).mp hbad).trans hptail

end Qatlib.Concepts.SketchSpectral.SketchAnalysis

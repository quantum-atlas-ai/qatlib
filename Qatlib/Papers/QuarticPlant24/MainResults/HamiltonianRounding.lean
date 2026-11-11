/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option backward.isDefEq.respectTransparency false

/-!
# QuarticPlant24, Lemma 58: rounding error of sparse Hamiltonian simulation

Source: Schmidhuber, O'Donnell, Kothari, Babbush, "Quartic quantum speedups for planted
inference", fixed arXiv:2406.19378v2 (Phys. Rev. X 15, 021077 (2025)),
Appendix E 1, Lemma 58 (lines 2147--2166 of the fixed v2 PDF text).

The paper proves that simulating `exp(-i H t)` from `b`-bit rounded entries costs an error
`‖exp(-iHt) - exp(-iH't)‖ ≤ s t 2^{-b}`, hence `ε` once `b = O(log(s t / ε))`, by the chain

1. `‖exp(iA) - exp(iB)‖ ≤ ‖A - B‖` for Hermitian `A`, `B` (folklore; proved here through the
   Duhamel integral with unitary endpoints, which is exactly the telescoping argument of the
   paper's proof),
2. `‖E‖ ≤ s ‖E‖max` for an `s`-sparse matrix `E` (the paper's row-sum estimate), and
3. `‖H - H'‖max ≤ 2^{-b}` for entrywise `b`-bit rounding.

Everything is stated for the ℓ² operator norm (`Matrix.Norms.L2Operator`), which is the norm
the paper uses throughout ("`‖M‖` denotes the operator norm or largest singular value").
The empty register is excluded from the unitary-norm step, where the matrix ring degenerates.
-/

set_option autoImplicit false
noncomputable section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QuarticPlant24.MainResults

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The Hamiltonian-simulation unitary `exp(-i t H)` of a complex matrix `H`. The paper writes
`exp(-iHt)`; no Hermiticity is needed for the definition. -/
def evolution (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  exp ((-t) • (Complex.I • H))

/-- The adjoint of `evolution H t` is `evolution H (-t)` for Hermitian `H`, because
`(-t • i H)ᴴ = t • i H` and `exp` commutes with the adjoint. -/
theorem conjTranspose_evolution {H : Matrix I I ℂ} (hH : H.IsHermitian) (t : ℝ) :
    (evolution H t)ᴴ = evolution H (-t) := by
  unfold evolution
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    hH.eq]
  congr 1
  simp [Complex.conj_I]

/-- For Hermitian `H` and real `t` the evolution matrix is unitary: the two factors are
commuting scalar multiples of `H`, and the exponents cancel. -/
theorem evolution_mem_unitary (H : Matrix I I ℂ) (hH : H.IsHermitian) (t : ℝ) :
    evolution H t ∈ unitary (Matrix I I ℂ) := by
  rw [Unitary.mem_iff]
  have hcomm : Commute ((-t) • (Complex.I • H)) (t • (Complex.I • H)) :=
    (Commute.refl (Complex.I • H)).smul_left (-t) |>.smul_right t
  have ht : (- -t : ℝ) = t := by ring
  constructor
  · rw [Matrix.star_eq_conjTranspose, conjTranspose_evolution hH t]
    unfold evolution
    rw [ht, ← Matrix.exp_add_of_commute _ _ hcomm.symm]
    have hzero : t • (Complex.I • H) + (-t) • (Complex.I • H) = 0 := by
      rw [← add_smul]
      simp
    rw [hzero, exp_zero]
  · rw [Matrix.star_eq_conjTranspose, conjTranspose_evolution hH t]
    unfold evolution
    rw [ht, ← Matrix.exp_add_of_commute _ _ hcomm]
    have hzero : (-t) • (Complex.I • H) + t • (Complex.I • H) = 0 := by
      rw [← add_smul]
      simp
    rw [hzero, exp_zero]

/-- A unitary matrix has unit ℓ² operator norm. -/
theorem norm_evolution_eq_one [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian) (t : ℝ) :
    ‖evolution H t‖ = 1 :=
  CStarRing.norm_of_mem_unitary (evolution_mem_unitary H hH t)

/-- **Duhamel identity for the evolution.** The two evolutions differ by the integral of
`evolution H s * (i H' - i H) * evolution H' (t - s)`; no commutation of `H` and `H'` is assumed. -/
theorem evolution_sub_eq_integral (H H' : Matrix I I ℂ) (t : ℝ) :
    evolution H t - evolution H' t =
      ∫ s in (0 : ℝ)..t, evolution H s * (Complex.I • H' - Complex.I • H) * evolution H' (t - s) := by
  have hdA (s : ℝ) : HasDerivAt (evolution H)
      (evolution H s * (-(Complex.I • H))) s := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • H) (-s)).scomp
      (x := s) (h := fun u : ℝ => -u) (hasDerivAt_neg' (x := s))
    simp only [Function.comp_def] at h
    show HasDerivAt (fun x : ℝ => exp ((-x) • (Complex.I • H)))
      (exp ((-s) • (Complex.I • H)) * (-(Complex.I • H))) s
    simpa [mul_neg] using h
  have hdB (s : ℝ) : HasDerivAt (fun u => evolution H' (t - u))
      (Complex.I • H' * evolution H' (t - s)) s := by
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Complex.I • H') (s - t)).scomp
      (x := s) (h := fun u : ℝ => u - t) ((hasDerivAt_id s).sub_const t)
    simpa [evolution, Function.comp_def, neg_sub] using h
  have hd (s : ℝ) : HasDerivAt
      (fun u => evolution H u * evolution H' (t - u))
      (evolution H s * (Complex.I • H' - Complex.I • H) * evolution H' (t - s)) s := by
    convert HasDerivAt.mul (hdA s) (hdB s) using 1
    noncomm_ring
  have hcA : Continuous (evolution H) :=
    continuous_iff_continuousAt.mpr fun s => (hdA s).continuousAt
  have hcB : Continuous (fun s => evolution H' (t - s)) :=
    continuous_iff_continuousAt.mpr fun s => (hdB s).continuousAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((hcA.mul continuous_const).mul hcB).intervalIntegrable 0 t)
  simpa [evolution, exp_zero] using hi.symm

/-- The operator-norm difference of the two evolutions: `‖exp(-iHt) - exp(-iH't)‖ ≤ |t| ‖H - H'‖`
for Hermitian `H`, `H'`. This is the paper's folklore estimate `‖exp(iA) - exp(iB)‖ ≤ ‖A - B‖`
applied to `A = -tH`, `B = -tH'`. -/
theorem norm_evolution_sub_le_of_nonneg [Nonempty I] {H H' : Matrix I I ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    ‖evolution H t - evolution H' t‖ ≤ ‖H - H'‖ * |t| := by
  have hsmul : Complex.I • H' - Complex.I • H = Complex.I • (H' - H) := by
    rw [smul_sub]
  rw [evolution_sub_eq_integral]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖H - H'‖) ?_).trans_eq ?_
  · intro s hs
    rw [Set.uIoc_of_le ht] at hs
    obtain ⟨hs0, hst⟩ := hs
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst
    calc ‖evolution H s * (Complex.I • H' - Complex.I • H) * evolution H' (t - s)‖
        = ‖(evolution H s * (Complex.I • H' - Complex.I • H)) * evolution H' (t - s)‖ := rfl
      _ ≤ ‖evolution H s * (Complex.I • H' - Complex.I • H)‖ *
            ‖evolution H' (t - s)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖evolution H s‖ * ‖Complex.I • H' - Complex.I • H‖) *
            ‖evolution H' (t - s)‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ = ‖H - H'‖ := by
          rw [norm_evolution_eq_one H hH s, norm_evolution_eq_one H' hH' (t - s),
            hsmul, norm_smul, Complex.norm_I, norm_sub_rev]
          simp
  · rw [sub_zero, abs_of_nonneg ht]

/-- `‖exp(-iHt) - exp(-iH't)‖ ≤ |t| ‖H - H'‖` for all real `t`, obtained from the
nonnegative case by taking adjoints. -/
theorem norm_evolution_sub_le [Nonempty I] {H H' : Matrix I I ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) (t : ℝ) :
    ‖evolution H t - evolution H' t‖ ≤ ‖H - H'‖ * |t| := by
  by_cases ht : 0 ≤ t
  · exact norm_evolution_sub_le_of_nonneg hH hH' ht
  · push Not at ht
    have hneg : 0 ≤ -t := by linarith
    have hbound := norm_evolution_sub_le_of_nonneg hH hH' (t := -t) hneg
    have hconj : evolution H t - evolution H' t =
        (evolution H (-t) - evolution H' (-t))ᴴ := by
      rw [Matrix.conjTranspose_sub]
      congr 1
      · rw [conjTranspose_evolution hH (-t)]
        simp
      · rw [conjTranspose_evolution hH' (-t)]
        simp
    rw [hconj, Matrix.l2_opNorm_conjTranspose]
    simpa [abs_neg] using hbound

/-- **Sparsity norm estimate.** A matrix with at most `s` nonzero entries in every row and in
every column, whose entries have norm at most `M`, has ℓ² operator norm at most `s * M`. This is
the paper's step `‖E‖ ≤ s ‖E‖max` in the proof of Lemma 58; it is derived here from the sparse
projected-unitary encoding of `s⁻¹ E` and the contractivity of the compressed encoding. -/
theorem opNorm_le_card_support_mul_maxEntry {A : Matrix I I ℂ} {s : ℕ} {M : ℝ}
    (hM : 0 < M) (hs : 0 < s)
    (hrow : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ s)
    (hcol : ∀ j, (Finset.univ.filter (fun i => A i j ≠ 0)).card ≤ s)
    (hentry : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ (s : ℝ) * M :=
  (Qatlib.Concepts.BlockEncoding.EncodingCore.sparse_overlap_derived_sparse_entry_norm_consumer
    I I A s M hM hs hrow hcol hentry).2

/-- The paper's bound `‖H‖ ≤ s ‖H‖max ≤ s` for an `s`-sparse Hamiltonian whose entries have
norm at most one; this is the estimate behind the simulation time `t = π/(2s)` used in the proof
of Theorem 63. -/
theorem norm_le_sparsity_of_entry_le_one {A : Matrix I I ℂ} {s : ℕ} (hs : 0 < s)
    (hrow : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ s)
    (hcol : ∀ j, (Finset.univ.filter (fun i => A i j ≠ 0)).card ≤ s)
    (hentry : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A‖ ≤ (s : ℝ) := by
  have h := opNorm_le_card_support_mul_maxEntry (A := A) (s := s) (M := 1)
    (by norm_num) hs hrow hcol hentry
  simpa using h

/-- **Lemma 58** (fixed arXiv:2406.19378v2, Appendix E 1). Let `H` and `H'` be Hermitian, let the
difference `H - H'` have at most `s` nonzero entries in every row and column (the paper's
`s`-sparsity of `H - H'`, which holds when `H'` is `H` with every nonzero entry rounded to `b`
binary digits), and let `‖H - H'‖max ≤ 2^{-b}`. Then simulating `H'` instead of `H` for time `t`
costs operator-norm error at most `s * t * 2^{-b}`.

Hermiticity of the rounded matrix `H'` is carried as an explicit hypothesis: rounding real and
imaginary parts to `b` binary digits commutes with conjugation, so it is automatic for the paper's
`H'`. The paper's normalisation `‖H‖max ≤ 1` is not needed for the error bound; it only fixes the
simulation time in Theorem 63 and is isolated in `norm_le_sparsity_of_entry_le_one`. -/
theorem lemma58_rounding_error [Nonempty I] {H H' : Matrix I I ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {s b : ℕ}
    (hs : 0 < s)
    (hrow : ∀ i, (Finset.univ.filter (fun j => (H - H') i j ≠ 0)).card ≤ s)
    (hcol : ∀ j, (Finset.univ.filter (fun i => (H - H') i j ≠ 0)).card ≤ s)
    (hround : ∀ i j, ‖(H - H') i j‖ ≤ (2 : ℝ) ^ (-(b : ℝ))) (t : ℝ) :
    ‖evolution H t - evolution H' t‖ ≤ (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) * |t| := by
  have hbpos : 0 < (2 : ℝ) ^ (-(b : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hnorm : ‖H - H'‖ ≤ (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) :=
    opNorm_le_card_support_mul_maxEntry hbpos hs hrow hcol hround
  calc ‖evolution H t - evolution H' t‖
      ≤ ‖H - H'‖ * |t| := norm_evolution_sub_le hH hH' t
    _ ≤ ((s : ℝ) * (2 : ℝ) ^ (-(b : ℝ))) * |t| := by
        exact mul_le_mul_of_nonneg_right hnorm (abs_nonneg t)

/-- The `ε` form of Lemma 58: `b` bits of precision suffice for target error `ε` as soon as
`s * |t| * 2^{-b} ≤ ε`; this is the paper's `b = O(log(s t / ε))` requirement. -/
theorem lemma58_error_le [Nonempty I] {H H' : Matrix I I ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {s b : ℕ} {ε : ℝ}
    (hs : 0 < s)
    (hrow : ∀ i, (Finset.univ.filter (fun j => (H - H') i j ≠ 0)).card ≤ s)
    (hcol : ∀ j, (Finset.univ.filter (fun i => (H - H') i j ≠ 0)).card ≤ s)
    (hround : ∀ i j, ‖(H - H') i j‖ ≤ (2 : ℝ) ^ (-(b : ℝ))) (t : ℝ)
    (hε : (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) * |t| ≤ ε) :
    ‖evolution H t - evolution H' t‖ ≤ ε :=
  (lemma58_rounding_error hH hH' hs hrow hcol hround t).trans hε

/-- A rounding precision always exists: for `1 ≤ s`, `t ≠ 0` and `ε > 0` there are `b` binary
digits with `s |t| 2^{-b} ≤ ε`. The bound only grows logarithmically in `s |t| / ε`, which is the
paper's `b = O(log(s t / ε))` bit requirement. -/
theorem exists_rounding_bits {s : ℕ} {t ε : ℝ} (hs : 0 < s) (ht : 0 < |t|) (hε : 0 < ε) :
    ∃ b : ℕ, (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) * |t| ≤ ε := by
  have hst : 0 < (s : ℝ) * |t| := mul_pos (by exact_mod_cast hs) ht
  have hX : 0 < (s : ℝ) * |t| / ε := div_pos hst hε
  have hb2 : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hpos : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        have : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          nlinarith
        simpa using this
  obtain ⟨b, hb⟩ := exists_nat_gt ((s : ℝ) * |t| / ε)
  refine ⟨b, ?_⟩
  have hpow : (2 : ℝ) ^ (-(b : ℝ)) = ((2 : ℝ) ^ (b : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
  have h2b : ((2 : ℝ) ^ (b : ℝ)) = (2 : ℝ) ^ b := Real.rpow_natCast 2 b
  have hinv : ((2 : ℝ) ^ (b : ℝ))⁻¹ ≤ ((s : ℝ) * |t| / ε)⁻¹ :=
    inv_anti₀ hX (by rw [h2b]; exact hb.le.trans (hb2 b))
  have hinv2 : ((s : ℝ) * |t| / ε)⁻¹ = ε / ((s : ℝ) * |t|) := by field_simp
  calc (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) * |t|
      = (s : ℝ) * |t| * ((2 : ℝ) ^ (b : ℝ))⁻¹ := by rw [hpow]; ring
    _ ≤ (s : ℝ) * |t| * (ε / ((s : ℝ) * |t|)) := by
        exact mul_le_mul_of_nonneg_left (hinv.trans_eq hinv2) hst.le
    _ = ε := by field_simp

end Qatlib.Papers.QuarticPlant24.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix

/-!
# A certified four-bit adversary witness

Verifies a rational matrix certificate for `fourBitGamma`, the adversary witness for
`ambainisSorted4`. Explicit factorizations of `1 - A.transpose * A` establish the required
filter norm bounds, while a constant row sum supplies a lower bound on the witness norm.

The resulting `ambainis_four_bit_printed_bound` formalizes the numerical lower bound associated
with the four-bit example in [HoyerLeeSpalek2007].

## Main statements

* `four_filter_certificate`: exact rational factorization of each filter residual.
* `fourBitGamma_filter_le`: every coordinate filter has operator norm at most one.
* `fourBitGamma_norm_lower`: witness norm at least `2513526 / 1000005`.
* `ambainis_four_bit_printed_bound`: negative-weight adversary value at least `2.5135`.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
/-- The rational four-bit witness matrix with entries retained only where the inputs differ at
coordinate `i`. -/
private def fourFilterQ (i : Fin 4) : Matrix FourBitWord FourBitWord ℚ := fun x y =>
  if x i = y i then 0 else fourBitQ x y
/-- The rational coefficient table used to assemble the matrices `fourL`. -/
private def fourLCoeff : ℕ → ℚ
  | 2 => (-249064929734976327 / 1109158497044169197)
  | 3 => (-249064929734976327 / 614572268504478062)
  | 4 => (-249064929734976327 / 712062774575208569)
  | 5 => (-90772494771 / 188452070015)
  | 6 => (-90772494771 / 376898652356)
  | 7 => (-90772494771 / 43729288571)
  | 8 => (-90772494771 / 87453089468)
  | 9 => (188446582341 / 188452070015)
  | 10 => (43723800897 / 43729288571)
  | 11 => (472105751928599853 / 712062774575208569)
  | 12 => (494586228539691135 / 614572268504478062)
  | 13 => (75010029459639225 / 1109158497044169197)
  | 14 => (97490506070730507 / 614572268504478062)
  | 1 => 1
  | _ => 0
/-- The lookup tag selecting a coefficient of the rational factor `fourL` from a coordinate and
two encoded inputs. -/
private def fourLTag (i x y : ℕ) : ℕ :=
  if x = y then 1 else match i, x, y with
  | 0, 1, 0 => 5
  | 0, 3, 0 => 5
  | 0, 3, 1 => 14
  | 0, 4, 2 => 5
  | 0, 5, 2 => 9
  | 0, 5, 4 => 3
  | 0, 6, 2 => 5
  | 0, 6, 4 => 14
  | 0, 6, 5 => 2
  | 0, 7, 0 => 9
  | 0, 7, 1 => 3
  | 0, 7, 3 => 4
  | 0, 10, 9 => 7
  | 0, 11, 9 => 10
  | 0, 11, 10 => 3
  | 0, 12, 8 => 5
  | 0, 13, 9 => 7
  | 0, 13, 10 => 12
  | 0, 13, 11 => 4
  | 0, 14, 8 => 5
  | 0, 14, 12 => 14
  | 0, 15, 8 => 9
  | 0, 15, 12 => 3
  | 0, 15, 14 => 4
  | 1, 1, 0 => 10
  | 1, 3, 0 => 7
  | 1, 3, 1 => 8
  | 1, 5, 4 => 10
  | 1, 6, 4 => 7
  | 1, 6, 5 => 8
  | 1, 8, 0 => 7
  | 1, 8, 1 => 8
  | 1, 8, 3 => 11
  | 1, 9, 2 => 9
  | 1, 10, 2 => 5
  | 1, 10, 9 => 6
  | 1, 11, 2 => 5
  | 1, 11, 9 => 6
  | 1, 11, 10 => 13
  | 1, 12, 7 => 9
  | 1, 13, 4 => 7
  | 1, 13, 5 => 8
  | 1, 13, 6 => 11
  | 1, 14, 7 => 5
  | 1, 14, 12 => 6
  | 1, 15, 7 => 5
  | 1, 15, 12 => 6
  | 1, 15, 14 => 13
  | 2, 1, 0 => 7
  | 2, 5, 4 => 5
  | 2, 6, 2 => 7
  | 2, 7, 3 => 5
  | 2, 8, 0 => 10
  | 2, 8, 1 => 3
  | 2, 9, 4 => 9
  | 2, 9, 5 => 3
  | 2, 10, 2 => 10
  | 2, 10, 6 => 3
  | 2, 11, 2 => 7
  | 2, 11, 6 => 12
  | 2, 11, 10 => 4
  | 2, 12, 0 => 7
  | 2, 12, 1 => 12
  | 2, 12, 8 => 4
  | 2, 13, 4 => 5
  | 2, 13, 5 => 14
  | 2, 13, 9 => 2
  | 2, 14, 3 => 9
  | 2, 14, 7 => 3
  | 2, 15, 3 => 5
  | 2, 15, 7 => 14
  | 2, 15, 14 => 2
  | 3, 3, 1 => 5
  | 3, 4, 2 => 7
  | 3, 6, 2 => 10
  | 3, 6, 4 => 3
  | 3, 7, 1 => 5
  | 3, 7, 3 => 14
  | 3, 8, 0 => 5
  | 3, 9, 5 => 5
  | 3, 10, 2 => 7
  | 3, 10, 4 => 12
  | 3, 10, 6 => 4
  | 3, 11, 5 => 9
  | 3, 11, 9 => 3
  | 3, 12, 0 => 5
  | 3, 12, 8 => 14
  | 3, 13, 5 => 5
  | 3, 13, 9 => 14
  | 3, 13, 11 => 2
  | 3, 14, 0 => 9
  | 3, 14, 8 => 3
  | 3, 14, 12 => 4
  | 3, 15, 1 => 9
  | 3, 15, 3 => 3
  | 3, 15, 7 => 4
  | _, _, _ => 0
/-- The rational matrix factor assembled from `fourLCoeff` and `fourLTag` for coordinate `i`. -/
private def fourL (i : Fin 4) : Matrix FourBitWord FourBitWord ℚ := fun x y =>
  fourLCoeff (fourLTag i.val (fourBitCode x) (fourBitCode y))
/-- The rational coefficient table used to assemble the diagonal weights `fourD`. -/
private def fourDCoeff : ℕ → ℚ
  | 0 => (1109158497044169197 / 94225605337986506577225)
  | 1 => (12996661669026520756780856 / 1109169588656868601118074229925)
  | 2 => (12996661669026520756780856 / 712069895220755890450070214225)
  | 3 => (2458289074017912248 / 188453954540411451750375)
  | 4 => (2458289074017912248 / 43729725864978942214275)
  | 5 => (3907568374404233108678506 / 307289207121263706746615975775)
  | 6 => (4136593870338119888 / 188453954540411451750375)
  | 7 => (6086700246108364153977778 / 307289207121263706746615975775)
  | 8 => (712062774575208569 / 21863491000270251809175)
  | 9 => (75380828006 / 200002000005)
  | 10 => (87458577142 / 1000010000025)
  | 11 => (959828090586434864 / 43729725864978942214275)
  | _ => 0
/-- The lookup tag selecting a diagonal weight from a coordinate and an encoded four-bit input. -/
private def fourDTag : ℕ → ℕ → ℕ
  | 0, 0 => 9
  | 0, 1 => 3
  | 0, 2 => 9
  | 0, 3 => 5
  | 0, 4 => 3
  | 0, 5 => 7
  | 0, 6 => 1
  | 0, 7 => 2
  | 0, 8 => 9
  | 0, 9 => 10
  | 0, 10 => 4
  | 0, 11 => 5
  | 0, 12 => 3
  | 0, 13 => 2
  | 0, 14 => 5
  | 0, 15 => 2
  | 1, 0 => 10
  | 1, 1 => 11
  | 1, 2 => 9
  | 1, 3 => 8
  | 1, 4 => 10
  | 1, 5 => 11
  | 1, 6 => 8
  | 1, 7 => 9
  | 1, 8 => 2
  | 1, 9 => 6
  | 1, 10 => 0
  | 1, 11 => 1
  | 1, 12 => 6
  | 1, 13 => 2
  | 1, 14 => 0
  | 1, 15 => 1
  | 2, 0 => 10
  | 2, 1 => 4
  | 2, 2 => 10
  | 2, 3 => 9
  | 2, 4 => 9
  | 2, 5 => 3
  | 2, 6 => 4
  | 2, 7 => 3
  | 2, 8 => 5
  | 2, 9 => 7
  | 2, 10 => 5
  | 2, 11 => 2
  | 2, 12 => 2
  | 2, 13 => 1
  | 2, 14 => 7
  | 2, 15 => 1
  | 3, 0 => 9
  | 3, 1 => 9
  | 3, 2 => 10
  | 3, 3 => 3
  | 3, 4 => 4
  | 3, 5 => 9
  | 3, 6 => 5
  | 3, 7 => 5
  | 3, 8 => 3
  | 3, 9 => 3
  | 3, 10 => 2
  | 3, 11 => 7
  | 3, 12 => 5
  | 3, 13 => 1
  | 3, 14 => 2
  | 3, 15 => 2
  | _, _ => 0
/-- The rational diagonal weight assigned to an input in the residual factorization for
coordinate `i`. -/
private def fourD (i : Fin 4) (x : FourBitWord) : ℚ :=
  fourDCoeff (fourDTag i.val (fourBitCode x))

/-- Every row of the integer four-bit witness has sum `2513526`. -/
private theorem four_integer_rows : ∀ x : FourBitWord, (∑ y : FourBitWord, fourBitInteger x y) = 2513526 := by
  decide +kernel

/-- The integer four-bit witness matrix is symmetric. -/
private theorem four_integer_symmetric : ∀ x y : FourBitWord, fourBitInteger x y = fourBitInteger y x := by
  decide +kernel

/-- The integer four-bit witness vanishes whenever `ambainisSorted4` has equal values on its two
inputs. -/
private theorem four_integer_support : ∀ x y : FourBitWord,
    ambainisSorted4 x = ambainisSorted4 y → fourBitInteger x y = 0 := by
  decide +kernel

/-- All diagonal weights in the four-bit residual certificates are nonnegative. -/
private theorem four_D_nonneg : ∀ i : Fin 4, ∀ x : FourBitWord, 0 ≤ fourD i x := by
  decide +kernel

/-- Each rational filter residual `1 - A.transpose * A` equals `fourL i * Matrix.diagonal (fourD
i) * (fourL i).transpose` entrywise. -/
private theorem four_filter_certificate : ∀ i : Fin 4, ∀ x y : FourBitWord,
    (1 - (fourFilterQ i).transpose * fourFilterQ i) x y =
      (fourL i * Matrix.diagonal (fourD i) * (fourL i).transpose) x y := by
  decide +kernel
noncomputable section

/-- A complex matrix has operator norm at most one if `1 - Aᴴ * A` is positive semidefinite. -/
theorem norm_le_one_of_residual_psd {H : Type} [Fintype H] [DecidableEq H] (A : Matrix H H ℂ)
    (h : (1 - Aᴴ * A).PosSemidef) : ‖A‖ ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := H) (𝕜 := ℂ) A‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  let w : QState H := WithLp.ofLp v
  have hp := h.re_dotProduct_nonneg w
  have hi : Qatlib.Foundations.PureStateMath.Inner w ((1 - Aᴴ * A) *ᵥ w) = Qatlib.Foundations.PureStateMath.Inner w w - Qatlib.Foundations.PureStateMath.Inner (A *ᵥ w) (A *ᵥ w) := by
    rw [lift_inner_rect, Matrix.mulVec_mulVec]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Qatlib.Foundations.PureStateMath.Inner,
        dotProduct_sub]
  change 0 ≤ (Qatlib.Foundations.PureStateMath.Inner w ((1 - Aᴴ * A) *ᵥ w)).re at hp
  rw [hi, Complex.sub_re, ← norm_toEuclidean_sq_eq_re_inner,
    ← norm_toEuclidean_sq_eq_re_inner] at hp
  change ‖toEuclidean_fromVec (A *ᵥ w)‖ ≤ 1 * ‖toEuclidean_fromVec w‖
  rw [one_mul]
  nlinarith [norm_nonneg (toEuclidean_fromVec (A *ᵥ w)), norm_nonneg (toEuclidean_fromVec w)]
end
noncomputable section

/-- The complex four-bit adversary witness `fourBitGamma` is Hermitian. -/
theorem fourBitGamma_hermitian : fourBitGamma.IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, fourBitGamma, fourBitQ]
  norm_cast
  rw [four_integer_symmetric]
end
noncomputable section

/-- The four-bit adversary witness vanishes on pairs having the same value of `ambainisSorted4`. -/
theorem fourBitGamma_support (x y : FourBitWord) (h : ambainisSorted4 x = ambainisSorted4 y) :
    fourBitGamma x y = 0 := by
  simp [fourBitGamma, fourBitQ, four_integer_support x y h]
end
noncomputable section

/-- Every coordinate filter of `fourBitGamma` has operator norm at most one. -/
theorem fourBitGamma_filter_le (i : Fin 4) :
    ‖genAdvFilter (fun w : FourBitWord => w) fourBitGamma i‖ ≤ 1 := by
  let f : ℚ →+* ℂ := Rat.castHom ℂ
  let L : Matrix FourBitWord FourBitWord ℂ := (fourL i).map f
  let D : FourBitWord → ℂ := fun x => (fourD i x : ℂ)
  have hd (x : FourBitWord) : 0 ≤ D x := by
    change 0 ≤ ((fourD i x : ℚ) : ℂ)
    have hr : 0 ≤ ((fourD i x : ℚ) : ℝ) := by exact_mod_cast four_D_nonneg i x
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa using! hr
    · simp
  have hP : (L * Matrix.diagonal D * Lᴴ).PosSemidef :=
    (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same L
  have hF : (fourFilterQ i).map f = genAdvFilter (fun w : FourBitWord => w) fourBitGamma i := by
    ext x y
    by_cases h : x i = y i <;> simp [genAdvFilter, fourFilterQ, fourBitGamma, h, f]
  have hT (Q : Matrix FourBitWord FourBitWord ℚ) : Q.transpose.map f = (Q.map f)ᴴ := by
    ext x y
    simp [f, Matrix.conjTranspose_apply]
  have hdiag : (Matrix.diagonal (fourD i)).map f = Matrix.diagonal D := by
    ext x y
    by_cases h : x = y <;> simp [h, D, f]
  have hc := congrArg (fun M : Matrix FourBitWord FourBitWord ℚ => M.map f)
    (Matrix.ext (four_filter_certificate i))
  have he : 1 - (genAdvFilter (fun w : FourBitWord => w) fourBitGamma i)ᴴ *
        genAdvFilter (fun w : FourBitWord => w) fourBitGamma i = L * Matrix.diagonal D * Lᴴ := by
    rw [Matrix.map_sub f (map_sub f), Matrix.map_one f (map_zero f) (map_one f)] at hc
    simpa only [Matrix.map_mul, hT, hF, hdiag] using! hc
  apply norm_le_one_of_residual_psd
  rw [he]
  exact hP
end
noncomputable section

/-- Every row of `fourBitGamma` sums to `2513526 / 1000005`. -/
theorem fourBitGamma_row_sum (x : FourBitWord) :
    (∑ y, fourBitGamma x y) = (2513526 / 1000005 : ℂ) := by
  have hr : (∑ y, fourBitQ x y) = (2513526 / 1000005 : ℚ) := by
    simp only [fourBitQ, ← Finset.sum_div, ← Int.cast_sum, four_integer_rows]
    norm_num
  change (∑ y, (fourBitQ x y : ℂ)) = _
  have hc := congrArg (fun z : ℚ => (z : ℂ)) hr
  push_cast at hc
  norm_num only at hc ⊢
  exact hc
end
noncomputable section

/-- The operator norm of `fourBitGamma` is at least `2513526 / 1000005`. -/
theorem fourBitGamma_norm_lower : (2513526 / 1000005 : ℝ) ≤ ‖fourBitGamma‖ := by
  let v : QState FourBitWord := fun _ => 1
  have hv : toEuclidean_fromVec v ≠ 0 := by
    intro h
    have hh :=
        congrArg (fun w : EuclideanSpace ℂ FourBitWord => WithLp.ofLp w (fun _ : Fin 4 => false)) h
    norm_num [v] at hh
  have he : fourBitGamma *ᵥ v = (2513526 / 1000005 : ℂ) • v := by
    ext x
    simpa only [Matrix.mulVec, dotProduct, v, mul_one, Pi.smul_apply, smul_eq_mul] using!
        fourBitGamma_row_sum x
  have hn := l2_norm_mulVec_fromVec_le fourBitGamma v
  rw [he] at hn
  change ‖(2513526 / 1000005 : ℂ) • toEuclidean_fromVec v‖ ≤ _ at hn
  rw [norm_smul] at hn
  have hc : ‖(2513526 / 1000005 : ℂ)‖ = (2513526 / 1000005 : ℝ) := by norm_num
  rw [hc] at hn
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp hn
end
noncomputable section

/-- The negative-weight adversary value of `ambainisSorted4` is at least `2.5135`, giving the
four-bit bound of [Hoyer, Lee, and Spalek, Theorem 20][HoyerLeeSpalek2007]. -/
theorem ambainis_four_bit_printed_bound :
    ENNReal.ofReal (25135 / 10000 : ℝ) ≤ advPmValue (fun w : FourBitWord => w) ambainisSorted4 := by
  have hG0 : fourBitGamma ≠ 0 := by
    intro hh
    have h := fourBitGamma_norm_lower
    rw [hh, norm_zero] at h
    norm_num at h
  have hnorm : ENNReal.ofReal (25135 / 10000 : ℝ) ≤ ENNReal.ofReal ‖fourBitGamma‖ :=
    ENNReal.ofReal_le_ofReal ((by norm_num : (25135 / 10000 : ℝ) ≤ 2513526 / 1000005).trans fourBitGamma_norm_lower)
  have hmax : maxFilterNorm (fun w : FourBitWord => w) fourBitGamma ≤ 1 := by
    unfold maxFilterNorm
    exact ciSup_le (fun i => fourBitGamma_filter_le i)
  have hwit : ENNReal.ofReal ‖fourBitGamma‖ ≤ advPmWitnessValue (fun w : FourBitWord => w) fourBitGamma := by
    unfold advPmWitnessValue
    apply (ENNReal.le_div_iff_mul_le (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hG0)))) (Or.inl ENNReal.ofReal_ne_top)).mpr
    exact (mul_le_mul_of_nonneg_left (by simpa using! ENNReal.ofReal_le_ofReal hmax) (by exact bot_le)).trans_eq (mul_one _)
  exact hnorm.trans (hwit.trans (le_iSup_of_le
    ⟨fourBitGamma, fourBitGamma_hermitian, fourBitGamma_support, hG0⟩ le_rfl))
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality

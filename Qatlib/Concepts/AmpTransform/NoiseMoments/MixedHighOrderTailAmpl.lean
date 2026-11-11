/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseMoments.MixedHighOrderTailStat
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments

/-!
# Fourth-moment and tail bounds for noisy intensity

`finite_centered_tail` derives a fourth-moment bound and a second-moment tail estimate for a
bounded finite family. `mixedHighOrderTail_answer` applies this estimate to the centered Fourier
noise intensity using a variance that includes order-two resonance, in the setting of
[Cornwell2014].

## Main statements

* `finite_centered_tail`: For a nonnegative weight a and |Xᵢ| ≤ B, a prescribed second moment v
  bounds the weighted fourth moment by B²v and the weighted tail above t > 0 by v/t².
* `mixedHighOrderTail_answer`: Proves fourth-moment and tail bounds for centered affine Fourier
  noise intensity using its resonance-corrected variance.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.QuditTeleport.TeleportCore
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

/-- For a nonnegative weight a and |Xᵢ| ≤ B, a prescribed second moment v bounds the weighted
fourth moment by B²v and the weighted tail above t > 0 by v/t². -/
theorem finite_centered_tail {I : Type*} [Fintype I] (X : I → ℝ) (a B v : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hx : ∀ i, |X i| ≤ B)
    (hv : a * ∑ i, (X i)^2 = v) :
    a * ∑ i, (X i)^4 ≤ B^2 * v ∧
    ∀ t : ℝ, 0 < t → a * ∑ i, (if t ≤ |X i| then (1 : ℝ) else 0) ≤ v / t^2 := by
  constructor
  · rw [← hv, mul_left_comm (B^2) a]
    apply mul_le_mul_of_nonneg_left _ ha
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    have hs : (X i)^2 ≤ B^2 := by nlinarith [sq_abs (X i), abs_nonneg (X i), hx i]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (X i))]
  · intro t ht
    rw [le_div_iff₀ (sq_pos_of_pos ht), ← hv]
    rw [mul_assoc, Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ ha
    apply Finset.sum_le_sum
    intro i _hi
    split_ifs with h
    · nlinarith [sq_abs (X i), abs_nonneg (X i)]
    · simpa using sq_nonneg (X i)

/-- Proves fourth-moment and tail bounds for centered affine Fourier noise intensity using its
resonance-corrected variance. -/
theorem mixedHighOrderTail_answer : MixedHighOrderTail := by
  intro N L _ y c b hy
  (try dsimp only)
  apply finite_centered_tail _ _ _ _ (by positivity) (by positivity) _
    (noise_sequence_variance_corrected N L y c b hy)
  intro ω
  have hs : ‖∑ i, ZMod.stdAddChar (ω i * y)‖ ≤ (L : ℝ) := by
    simpa only [norm_stdAddChar, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using
      norm_sum_le Finset.univ (fun i : Fin L => ZMod.stdAddChar (ω i * y))
  have hn : ‖c + (b : ℂ) * ∑ i, ZMod.stdAddChar (ω i * y)‖ ≤ ‖c‖ + |b| * L := by
    calc
      _ ≤ ‖c‖ + ‖(b : ℂ) * ∑ i, ZMod.stdAddChar (ω i * y)‖ := norm_add_le _ _
      _ = ‖c‖ + |b| * ‖∑ i, ZMod.stdAddChar (ω i * y)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hs (abs_nonneg b)) _
  calc
    _ ≤ |‖c + (b : ℂ) * ∑ i, ZMod.stdAddChar (ω i * y)‖^2| +
        |‖c‖^2 + b^2 * (L : ℝ)| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (c + (b : ℂ) * ∑ i, ZMod.stdAddChar (ω i * y)),
        norm_nonneg c, abs_nonneg b, Nat.cast_nonneg (α := ℝ) L]

end Qatlib.Concepts.AmpTransform.NoiseMoments

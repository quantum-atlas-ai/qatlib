/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseMoments.AllFrequencyMomentCorrectionStat
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments
set_option warningAsError false
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

theorem allFrequencyMomentCorrection_answer : AllFrequencyMomentCorrection := by
  intro N L _ c b y
  constructor
  · intro hy
    subst y
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hcard : (Fintype.card (Fin L → ZMod N) : ℝ) = (N : ℝ) ^ L := by
      rw [noise_tuple_card, Nat.cast_pow]
    simp only [mul_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Nat.cast_pow]
    simp only [Nat.cast_pow] at *
    rw [hcard]
    constructor
    · field_simp
      simp
    · field_simp
  · exact noise_sequence_second_moment N L y c b

end Qatlib.Concepts.AmpTransform.NoiseMoments

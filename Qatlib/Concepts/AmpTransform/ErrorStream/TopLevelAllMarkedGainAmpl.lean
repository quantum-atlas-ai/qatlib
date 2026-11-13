/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.TopLevelAllMarkedGainStat

/-!
# All-marked boundary of amplified Fourier sampling

`topLevelAllMarkedGain_answer` treats the boundary in which the progression and its complement
mark every label. The amplified output is concentrated at zero, and the theorem transports this
fact through the Bernoulli subset weight in the noisy-transform setting of [Cornwell2014].

## Main statements

* `topLevelAllMarkedGain_answer`: Proves `TopLevelAllMarkedGain`: marking a set and its
  complement yields a unitary circuit with output concentrated at zero and the stated
  Bernoulli-weighted probabilities; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

/-- Proves `TopLevelAllMarkedGain`: marking a set and its complement yields a unitary circuit
with output concentrated at zero and the stated Bernoulli-weighted probabilities; see
[Cornwell2014]. -/
theorem topLevelAllMarkedGain_answer : TopLevelAllMarkedGain := by
  intro N k _ p _hp0 _hp1 d hd A
  (try dsimp only)
  have hU := zmodQFTGate_unitary (N := N) (NeZero.pos N)
  have hw := prepared_aa_actual_circuit (zmodQFTGate (N := N)) 0 Finset.univ k hU
  have hsets : A ∪ (Finset.univ \ A) = Finset.univ := by ext x; simp
  have he := (prepared_aa_endpoint_states (zmodQFTGate (N := N)) 0 Finset.univ k hU).2
    (measureProb_univ (prepared_aa_reflection_and_access
      (zmodQFTGate (N := N)) 0 Finset.univ hU).2.1)
  have hentry (x : ZMod N) : preparedAAState (zmodQFTGate (N := N)) 0 x =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by
    simp [preparedAAState, ApplyGate, Matrix.mulVec, dotProduct, Ket, zmodQFTGate_apply]
  have hsq : (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (N : ℝ) : ℂ)⁻¹ =
      (N : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  have hq (y : ZMod N) : ApplyGate zmodQFTGate
      (preparedAAState (zmodQFTGate (N := N)) 0) y = if y = 0 then 1 else 0 := by
    simp only [ApplyGate, Matrix.mulVec, dotProduct, zmodQFTGate_apply, hentry]
    simp_rw [mul_right_comm _ _ ((Real.sqrt (N : ℝ) : ℂ)⁻¹), hsq]
    rw [← Finset.mul_sum, sum_stdAddChar_mul]
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    split_ifs <;> simp [hn]
  have hb (y : ZMod N) : BornProb
      (Run (preparedMark (A ∪ (Finset.univ \ A)))
        (conditionalAmplifiedQFTCircuit N k) (Ket 0)) y = if y = 0 then 1 else 0 := by
    rw [hsets, conditionalAmplifiedQFTCircuit, run_append, run_gate, run_nil, he]
    simp only [ApplyGate, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, BornProb]
    change ‖(-1 : ℂ)^k * ApplyGate zmodQFTGate (preparedAAState zmodQFTGate 0) y‖^2 = _
    rw [hq]
    split_ifs <;> simp [norm_pow]
  have hm : d.prob (Finset.univ \ A) =
      p^(Finset.univ \ A).card * (1-p)^A.card := by
    rw [hd, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, ZMod.card]
    have hA : A.card ≤ N := by simpa using Finset.card_le_univ A
    rw [Nat.sub_sub_self hA]
  refine ⟨by simp [conditionalAmplifiedQFTCircuit, hw.1, hU], hb, hm, ?_, ?_⟩
  · rw [hb, if_pos rfl, mul_one, hm]
  · intro y hy
    rw [hb, if_neg hy, mul_zero]

end Qatlib.Concepts.AmpTransform.ErrorStream

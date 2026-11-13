/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder

/-!
# Concrete consumers of the Simon decoder

This module checks Gaussian Simon decoding on explicit two-bit records and verifies concrete
Simon promises for a projection oracle and the identity oracle.
`simon_gaussian_actual_secret_consumers` transfers the decoder success estimates and resource
ledger to these examples. For background, see [Simon1997].

## Main statements

* `simon_gaussian_concrete_records`: The Simon decoder has the stated outputs on a single basis
  row, two independent rows, repeated rows, and empty records in dimensions two and zero.
* `simon_gaussian_actual_secret_consumers`: For the projection and identity oracles, `2 + k`
  samples recover the respective secrets with probability at least `1 - (1/2)^k`; the
  four-sample projection run has ledger `(4, 8, 4)`.

## References

* [Simon, 1997][Simon1997]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.AbelianDecoders.SimonDecoding

/-- The two-bit register with its only true coordinate at index one. -/
def simonSampleE1 : Reg 2 := fun i => decide (i = 1)

/-- The two-bit register with its only true coordinate at index zero. -/
def simonSecretE0 : Reg 2 := fun i => decide (i = 0)

/-- The oracle that returns coordinate one of a two-bit Boolean vector. -/
def simonProjectionOracle : BooleanVec 2 → ZMod 2 := fun x => x 1

/-- At coordinate `i`, `simonSampleE1` equals `decide (i = 1)`. -/
@[simp] theorem simonSampleE1_apply (i : Fin 2) :
    simonSampleE1 i = decide (i = 1) := rfl

/-- At coordinate `i`, `simonSecretE0` equals `decide (i = 0)`. -/
@[simp] theorem simonSecretE0_apply (i : Fin 2) :
    simonSecretE0 i = decide (i = 0) := rfl

/-- The Simon decoder has the stated outputs on a single basis row, two independent rows,
repeated rows, and empty records in dimensions two and zero. -/
theorem simon_gaussian_concrete_records :
    decodeSimonSecret (fun _ : Fin 1 => simonSampleE1) = some simonSecretE0 ∧
      decodeSimonSecret (fun i : Fin 2 => if i = 0 then simonSecretE0 else simonSampleE1) =
        some (ZeroStr 2) ∧
      decodeSimonSecret (fun i : Fin 2 => if i = 0 then simonSampleE1 else simonSampleE1) =
        some simonSecretE0 ∧
      decodeSimonSecret (Fin.elim0 : Fin 0 → Reg 2) = none ∧
      decodeSimonSecret (Fin.elim0 : Fin 0 → Reg 0) = some (ZeroStr 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The Boolean-vector image of `simonSecretE0` is one at index zero and zero elsewhere. -/
theorem regBooleanEquiv_simonSecretE0 (i : Fin 2) :
    regBooleanEquiv 2 simonSecretE0 i = if i = 0 then 1 else 0 := by
  rw [regBooleanEquiv_apply, simonSecretE0_apply]
  by_cases hi : i = 0 <;> simp [hi]

/-- The projection oracle satisfies the Boolean Simon promise with secret `simonSecretE0` under
`regBooleanEquiv`. -/
theorem booleanSimonPromise_simonProjectionOracle :
    BooleanSimonPromise simonProjectionOracle (regBooleanEquiv 2 simonSecretE0) := by
  intro x y
  constructor
  · intro h
    by_cases h0 : x 0 = y 0
    · left
      funext i
      fin_cases i
      · exact h0
      · exact h
    · right
      funext i
      fin_cases i
      · show x 0 = y 0 + regBooleanEquiv 2 simonSecretE0 0
        rw [regBooleanEquiv_simonSecretE0, if_pos rfl]
        rcases zmod2_eq_zero_or_one (x 0) with hx | hx <;>
          rcases zmod2_eq_zero_or_one (y 0) with hy | hy
        · rw [hx, hy] at h0; simp at h0
        · rw [hx, hy]; decide
        · rw [hx, hy]; decide
        · rw [hx, hy] at h0; simp at h0
      · show x 1 = y 1 + regBooleanEquiv 2 simonSecretE0 1
        rw [regBooleanEquiv_simonSecretE0,
          if_neg (show (1 : Fin 2) ≠ 0 by decide), add_zero]
        exact h
  · intro h
    rcases h with rfl | h
    · rfl
    · rw [h]
      show (y + regBooleanEquiv 2 simonSecretE0) 1 = y 1
      rw [Pi.add_apply, regBooleanEquiv_simonSecretE0,
        if_neg (show (1 : Fin 2) ≠ 0 by decide), add_zero]

/-- The identity oracle on two-bit Boolean vectors satisfies the Simon promise with zero secret. -/
theorem booleanSimonPromise_id_zero :
    BooleanSimonPromise (fun x : BooleanVec 2 => x) (regBooleanEquiv 2 (ZeroStr 2)) := by
  rw [regBooleanEquiv_zeroStr, booleanSimonPromise_zero_iff]
  exact Function.injective_id

/-- For the projection and identity oracles, `2 + k` samples recover the respective secrets with
probability at least `1 - (1/2)^k`; the four-sample projection run has ledger `(4, 8, 4)`. -/
theorem simon_gaussian_actual_secret_consumers :
    (∀ k : ℕ, ENNReal.ofReal (1-(1/2:ℝ)^k) ≤
      (simonDecodedRun simonProjectionOracle (2+k)).1 (some simonSecretE0)) ∧
      (∀ k : ℕ, ENNReal.ofReal (1-(1/2:ℝ)^k) ≤
        (simonDecodedRun (fun x : BooleanVec 2 => x) (2+k)).1 (some (ZeroStr 2))) ∧
      (simonDecodedRun simonProjectionOracle 4).2 = (4,8,4) := by
  refine ⟨fun k => (simon_gaussian_accessible_budget simonProjectionOracle simonSecretE0 k
      booleanSimonPromise_simonProjectionOracle).1,
    fun k => (simon_gaussian_accessible_budget (fun x : BooleanVec 2 => x) (ZeroStr 2) k
      booleanSimonPromise_id_zero).1,
    (simon_actual_preparation_and_quantum_cost simonProjectionOracle 4).2.2.2.2⟩

end Qatlib.Concepts.AbelianDecoders.SimonDecoding

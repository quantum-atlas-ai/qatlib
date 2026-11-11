/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarGeneralWNStat
import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarLocalDecisionAmpl

/-!
# General Haar pair readout and orientation preservation

This module proves that unitary transformations acting separately on the two orientation sectors
preserve their measurement probabilities. `haarGeneralWN_answer` combines this invariance with
dyadic state preparation, amplified pair readout, and the empty-marked-set case in the
Haar-transform setting of [Cornwell2014].

## Main statements

* `haar_full_tail_decision`: After the prescribed amplification rounds, a common marked-pair
  orientation is observed with probability at least 1−M/|I|, even after sector-preserving
  unitary processing; this is at least 2/3 when 3M ≤ |I|.
* `haarGeneralWN_answer`: Proves `HaarGeneralWN`, including dyadic preparation, exact circuit
  counts, amplified orientation guarantees, the empty-set readout, and invariance under
  sector-preserving unitaries; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
set_option autoImplicit false
open Qatlib.Concepts.PhaseGeometry.Phase Matrix
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.HaarPairTest

/-- A block-diagonal unitary acting separately on the two Boolean sectors preserves the
probability of each sector. -/
theorem haar_orientation_half_preserved {I : Type} [Fintype I] [DecidableEq I]
    (U : Bool → Matrix I I ℂ) (hU : ∀ b, U b ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState (I × Bool)) (b : Bool) :
    let W : Matrix (I × Bool) (I × Bool) ℂ := fun i j =>
      if i.2 = j.2 then U i.2 i.1 j.1 else 0
    MeasureProb (W *ᵥ ψ) (Finset.univ.filter (fun z => z.2 = b)) =
      MeasureProb ψ (Finset.univ.filter (fun z => z.2 = b)) := by
  intro W
  have ha (i : I) (c : Bool) : (W *ᵥ ψ) (i, c) =
      (U c *ᵥ (fun j => ψ (j, c))) i := by
    cases c <;> simp [W, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have he (φ : QState (I × Bool)) :
      MeasureProb φ (Finset.univ.filter (fun z => z.2 = b)) =
        ∑ i, Complex.normSq (φ (i, b)) := by
    cases b <;> simp [MeasureProb, BornProb, Finset.sum_filter,
      Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]
  rw [he, he]
  simp only [ha]
  exact sum_normSq_mulVec_of_mem_unitaryGroup (hU b) (fun j => ψ (j, b))

/-- For M > 0, the event that `haarSourceReadout` returns b is exactly the Boolean sector b, so
their measurement probabilities agree. -/
theorem haarSourceReadout_nonempty {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (ψ : QState (I × Bool)) (b : Bool) :
    MeasureProb ψ (Finset.univ.filter (fun z => haarSourceReadout M z = some b)) =
      MeasureProb ψ (Finset.univ.filter (fun z => z.2 = b)) := by
  congr 1
  ext z
  simp [haarSourceReadout, Nat.ne_of_gt hM]

/-- After the prescribed amplification rounds, a common marked-pair orientation is observed with
probability at least 1−M/|I|, even after sector-preserving unitary processing; this is at
least 2/3 when 3M ≤ |I|. -/
theorem haar_full_tail_decision {I : Type} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (T' : Matrix (I × Bool) (I × Bool) ℂ)
    (seed : I × Bool) (hT : T' ∈ Matrix.unitaryGroup (I × Bool) ℂ)
    (hprep : T' *ᵥ Ket seed = Uniform (I × Bool)) (M : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθupper : θ ≤ Real.pi / 2)
    (hsin : (Real.sin θ) ^ 2 = (M : ℝ) / (Fintype.card I : ℝ))
    (E : Finset I) (hE : E.card = M) (S : I × Bool → Bool) (b : Bool)
    (horient : ∀ i ∈ E, (S (i, false) != S (i, true)) = b)
    (U : Bool → Matrix I I ℂ) (hU : ∀ c, U c ∈ Matrix.unitaryGroup I ℂ) :
    let k := Nat.floor (Real.pi / (4 * θ))
    let W : Matrix (I × Bool) (I × Bool) ℂ := fun i j =>
      if i.2 = j.2 then U i.2 i.1 j.1 else 0
    1 - (M : ℝ) / (Fintype.card I : ℝ) ≤
      MeasureProb (W *ᵥ aqHaarPairOutput T' seed k E S)
        (Finset.univ.filter (fun z => z.2 = b)) ∧
    (3 * M ≤ Fintype.card I → (2 / 3 : ℝ) ≤
      MeasureProb (W *ᵥ aqHaarPairOutput T' seed k E S)
        (Finset.univ.filter (fun z => z.2 = b))) := by
  (try dsimp only)
  rw [haar_orientation_half_preserved U hU]
  have hs := (haarLocalDecision I hI T' seed hT hprep M θ hθ hθupper hsin).2.2.2.2
    E hE S b horient
  exact hs.2

/-- The dyadic preparation matrix is unitary and maps `haarDyadicSeed n` to the uniform state. -/
theorem haarDyadicPreparation_spec (n : ℕ) :
    haarDyadicPreparation n ∈ Matrix.unitaryGroup (Reg (n-1) × Bool) ℂ ∧
    haarDyadicPreparation n *ᵥ Ket (haarDyadicSeed n) = Uniform (Reg (n-1) × Bool) := by
  refine ⟨tensorGate_unitary (hadamardN_unitary (n-1)) hadamard_unitary, ?_⟩
  change TensorGate (HadamardN (n-1)) Hadamard *ᵥ Ket (ZeroStr (n-1), false) = _
  rw [← tensorState_ket_ket]
  change ApplyGate (TensorGate (HadamardN (n-1)) Hadamard)
    (TensorState (Ket (ZeroStr (n-1))) (Ket false)) = _
  rw [applyGate_tensorGate, applyGate_hadamardN_ket_zero, applyGate_hadamard_ket_false]
  funext z
  have he : Hadamard z.2 false = (Real.sqrt 2 : ℂ)⁻¹ := by
    cases z.2 <;> simp [Hadamard]
  simp only [TensorState, Uniform, Plus, Fintype.card_prod, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [he, Real.sqrt_mul (by positivity), Complex.ofReal_mul, _root_.mul_inv_rev]
  exact mul_comm _ _

/-- Proves `HaarGeneralWN`, including dyadic preparation, exact circuit counts, amplified
orientation guarantees, the empty-set readout, and invariance under sector-preserving
unitaries; see [Cornwell2014]. -/
theorem haarGeneralWN_answer : HaarGeneralWN := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _hn
    have hT := haarDyadicPreparation_spec n
    refine ⟨hT.1, hT.2, ?_⟩
    exact haarLocalDecision (Reg (n-1)) (by simp [Reg]) _ _ hT.1 hT.2
  · intro n _hn S
    have hT := haarDyadicPreparation_spec n
    have hs := haarPairWordSemantics (Reg (n-1)) _ _ hT.1 hT.2 0
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    have hn := (hs.2.2.2.2 ∅ S).2
    simpa [haarSourceReadout] using measureProb_univ hn
  · intro I _ _ U hU ψ b
    exact haar_orientation_half_preserved U hU ψ b

end Qatlib.Concepts.AmpTransform.HaarPairTest

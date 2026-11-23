module

import Qatlib.Papers.NegWeights06.MainResults.Automorphism
import Qatlib.Papers.NegWeights06.MainResults.CompositionEigenvector
import Qatlib.Papers.NegWeights06.MainResults.Distinguishability
import Qatlib.Papers.NegWeights06.MainResults.NonnegativeComposition

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComposition (weightedAdvGamma)
open Qatlib.Foundations.PureStateMath (Inner Ket MeasureProb bornProb_ket normalized_ket)
open Qatlib.Papers.NegWeights06.MainResults

private def word (x : Bool × Bool) (i : Fin 2) : Bool :=
  if i = 0 then x.1 else x.2

private def parity (x : Bool × Bool) : Bool := xor x.1 x.2

private def parityMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if parity x = parity y then 0 else 1

example :
    ‖genAdvFilter word (parityMatrix.submatrix (Equiv.prodComm Bool Bool) (Equiv.prodComm Bool Bool))
      (0 : Fin 2)‖ = ‖genAdvFilter word parityMatrix (1 : Fin 2)‖ :=
  adversary_filter_norm_relabel word parityMatrix (Equiv.prodComm Bool Bool) 0 1
    (fun _ _ => Iff.rfl)

example : ∃ B : ℝ, 0 < B ∧ ∀ i, ‖genAdvFilter word parityMatrix i‖ = B := by
  apply adversary_filter_common_norm_of_index_transitive word parityMatrix
    {Equiv.refl _, Equiv.prodComm Bool Bool}
  · intro x y h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro h
    have hentry := congrArg (fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ =>
      M (false, false) (true, false)) h
    change (1 : ℂ) = 0 at hentry
    exact one_ne_zero hentry
  · intro x
    simp [parityMatrix]
  · intro π hπ x y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
    rcases hπ with rfl | rfl
    · rfl
    · have hpar (a : Bool × Bool) : parity (Equiv.prodComm Bool Bool a) = parity a := by
        rcases a with ⟨a, b⟩
        cases a <;> cases b <;> rfl
      simp only [parityMatrix, hpar]
  · intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨Equiv.refl _, by simp, fun _ _ => Iff.rfl⟩
    · exact ⟨Equiv.prodComm Bool Bool, by simp, fun _ _ => Iff.rfl⟩
    · exact ⟨Equiv.prodComm Bool Bool, by simp, fun _ _ => Iff.rfl⟩
    · exact ⟨Equiv.refl _, by simp, fun _ _ => Iff.rfl⟩

private def zeroBlockOuter : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ :=
  fun x y => if x 0 = y 0 then 0 else 1

example : ∃ (u : (Fin 1 → Bool) → ℂ) (v : Fin 1 → Bool → ℂ),
    let w : (Fin 1 → Bool) → ℂ := fun x => u x * ∏ i, v i (x i)
    w ≠ 0 ∧ weightedAdvGamma (fun _ : Fin 1 => id) (fun x => x 0)
      zeroBlockOuter (fun _ => 0) *ᵥ w = 0 := by
  have houter : zeroBlockOuter.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x y
    change star (if y 0 = x 0 then (0 : ℂ) else 1) = if x 0 = y 0 then 0 else 1
    by_cases h : x 0 = y 0
    · rw [ite_eq_left h.symm, ite_eq_left h, star_zero]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_one]
  obtain ⟨u, v, _, _, _, hne, he⟩ := composed_adversary_has_principal_product_eigenvector
    (X := fun _ : Fin 1 => Bool) (fun _ => id) (fun x => x 0) zeroBlockOuter (fun _ => 0)
    houter (fun _ => Matrix.isHermitian_zero) (fun x y h => by simp [zeroBlockOuter, h])
    (fun _ _ _ _ => rfl) (fun _ => Function.surjective_id)
  have hz : weightedAdvGamma (fun _ : Fin 1 => (@id Bool)) (fun x => x 0)
      zeroBlockOuter (fun _ => 0) = 0 := by
    ext x y
    simp [weightedAdvGamma]
  exact ⟨u, v, hne, by simpa only [id_eq, hz, norm_zero, Complex.ofReal_zero, zero_smul] using he⟩

example : ‖Inner (Ket true) (Ket false)‖ ≤ 0 := by
  have hsuccess (b : Bool) : 1 - (0 : ℝ) ≤ povmProb (labelPovm (id : Bool → Bool)) b (Ket b) := by
    rw [labelPovm_povmProb]
    cases b <;> norm_num [MeasureProb, outcomeEvent, Finset.sum_filter, bornProb_ket, Fintype.sum_bool]
  simpa using pure_overlap_le_of_binary_povm_success (Ket true) (Ket false)
    (normalized_ket true) (normalized_ket false) (labelPovm id) (isPovm_labelPovm id)
    0 le_rfl (by norm_num) (hsuccess true) (hsuccess false)

private def oneBitInput (_ : Fin 1) (x : Bool) (_ : Fin 1) : Bool := x

example : advValue (composedInput oneBitInput) (composedFunction (fun _ => id) (fun w => w 0)) =
    advValue (oneBitInput 0) id * advValue id (fun w : Fin 1 → Bool => w 0) := by
  let a := (advValue (oneBitInput 0) id).toReal
  have hobs : OutputObservable (oneBitInput 0) id := fun x y h => ⟨0, h⟩
  have hinner : ∃ x y : Bool, id x ≠ id y := ⟨false, true, by decide⟩
  have hfinite : advValue (oneBitInput 0) id < ⊤ :=
    (advAlphaR_finite_iff_observable _ _ (fun _ => 1) (fun _ => zero_lt_one) hinner).mpr hobs
  have hbound (i : Fin 1) : ENNReal.ofReal a = advValue (oneBitInput i) id :=
    ENNReal.ofReal_toReal hfinite.ne
  have houter : ∃ u v : Fin 1 → Bool, u 0 ≠ v 0 := ⟨fun _ => false, fun _ => true, by decide⟩
  have hlo := nonnegative_adversary_composition_lower oneBitInput
    (fun _ => id) (fun w => w 0) a houter (fun _ => hinner)
    (fun _ => hobs) (fun i => (hbound i).le)
  have ⟨_, hhi⟩ := nonnegative_adversary_composition_sandwich oneBitInput
    (fun _ => id) (fun w => w 0) a a houter (fun _ => hinner)
    (fun i => (hbound i).le) (fun i => (hbound i).ge)
  rw [hbound 0] at hlo hhi
  exact le_antisymm hhi hlo

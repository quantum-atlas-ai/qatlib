/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutator
public import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutatorConsumers
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.NestedCommutatorScalingCorrected
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrected
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterGeneralOperatorScalingCorrected
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterOrderedCommutator
public import Qatlib.Concepts.TrotterFormula.ImaginaryTime.FiniteImaginaryProductConsumers
public import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
public import Qatlib.Concepts.TrotterFormula.LieStrang.ProductFormulaConsumers
public import Qatlib.Concepts.TrotterFormula.LieStrang.TrotterFirstOrderTailSum
public import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
public import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrderConsumers
public import Qatlib.Concepts.TrotterFormula.TimeOrdered.TypesOfTrotterError
public import Qatlib.Papers.TrotterError19.MainResults.SourceModel
public import Qatlib.Papers.TrotterError19.GroupedError.TrotterCommutatorScalingStepsAthe

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section


open Matrix Filter Asymptotics
open scoped Matrix.Norms.L2Operator BigOperators ContDiff Topology ComplexOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.FiniteStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.ImaginaryTime
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Papers.TrotterError19.MainResults

namespace Qatlib.Papers.TrotterError19.MainResults

/-- The corrected selected-step theorem includes a positive segment count, error budget and exact exponential visits. -/
theorem corollary12_trotter_number_commutator :
    Qatlib.Papers.TrotterError19.GroupedError.TrotterCommutatorScalingStepsCorrected :=
  Qatlib.Papers.TrotterError19.GroupedError.trotterCommutatorScalingStepsCorrected

section

/-- **Theorem 8** (arXiv:1912.08854v3, Eq. (32)--(34), printed p. 17).
Bridge to the frozen FQN
`Qatlib.Concepts.TrotterFormula.TimeOrdered.typesOfTrotterError`:
the additive, exponentiated and multiplicative error forms for the actual
supplied exponential word, with the explicit right-suffix and left-prefix
conjugation sums. -/
theorem theorem8_types_of_trotter_error :
    Qatlib.Concepts.TrotterFormula.TimeOrdered.TypesOfTrotterError :=
  Qatlib.Concepts.TrotterFormula.TimeOrdered.typesOfTrotterError

/-- **Theorem 9** (arXiv:1912.08854v3, Eq. (36), printed p. 18).
Bridge to the frozen FQN
`Qatlib.Concepts.TrotterFormula.GeneralOrder.general_trotter_four_order_conditions`:
the additive error, right differential defect, left differential defect and
multiplicative error have equivalent orders. -/
theorem theorem9_order_conditions :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ)
      (S : ℝ → Matrix I I ℂ) (p : ℕ), ContDiff ℝ ∞ S → S 0 = 1 →
      let D := fun t => deriv S t - H * S t
      let T := fun t => Ring.inverse (S t) * D t
      let E := fun t => D t * Ring.inverse (S t)
      let M := fun t => NormedSpace.exp ((-t) • H) * S t - 1
      let O := fun (F : ℝ → Matrix I I ℂ) (n : ℕ) =>
        ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∀ t : ℝ, |t| ≤ t₀ → ‖F t‖ ≤ c * |t| ^ n
      (O (fun t => S t - NormedSpace.exp (t • H)) (p + 1) ↔ O T p) ∧
      (O T p ↔ O E p) ∧ (O E p ↔ O M (p + 1)) :=
  general_trotter_four_order_conditions

/-- **Theorem 10, general-operator remainder, Eq. (48)**
(arXiv:1912.08854v3, printed p. 19).  Bridge to
`pf_conjugation_expansion_general_corrected`. -/
theorem theorem10_conjugation_expansion_general {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    ‖suzukiExponentialWord xs t * B * Ring.inverse (suzukiExponentialWord xs t) -
        pfTaylorBefore
          (fun u => suzukiExponentialWord xs u * B * Ring.inverse (suzukiExponentialWord xs u))
          p t‖ ≤
      pfCommAlphaInner xs B p * |t| ^ p * Real.exp (2 * |t| * suzukiMass xs) :=
  pf_conjugation_expansion_general_corrected xs B p t

/-- **Theorem 10, anti-Hermitian remainder, Eq. (49)**
(arXiv:1912.08854v3, printed p. 19).  Bridge to
`pf_conjugation_expansion_skew_corrected`. -/
theorem theorem10_conjugation_expansion_skew {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hxs : ∀ X ∈ xs, Xᴴ = -X) :
    ‖suzukiExponentialWord xs t * B * Ring.inverse (suzukiExponentialWord xs t) -
        pfTaylorBefore
          (fun u => suzukiExponentialWord xs u * B * Ring.inverse (suzukiExponentialWord xs u))
          p t‖ ≤
      pfCommAlphaInner xs B p * |t| ^ p :=
  pf_conjugation_expansion_skew_corrected xs B p t hxs

/-- **Theorem 10, exact ordered jets, Eq. (46)** (arXiv:1912.08854v3, printed
p. 19).  Bridge to `trotterOrderedCommutator`, which packages Eq. (46)--(49). -/
theorem theorem10_ordered_commutator :
    Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterOrderedCommutator :=
  Qatlib.Concepts.TrotterFormula.GeneralOrder.trotterOrderedCommutator

/-- **Theorem 11, anti-Hermitian case, Eq. (54)** (arXiv:1912.08854v3,
printed p. 22).  Bridge to the frozen FQN
`Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrected`. -/
theorem theorem11_commutator_scaling_antihermitian :
    Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrected :=
  Qatlib.Concepts.TrotterFormula.GeneralOrder.trotterCommutatorScalingCorrected

/-- **Theorem 11, general-operator case** (arXiv:1912.08854v3, Eq. (54),
printed p. 22).  Bridge to the frozen FQN
`Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterGeneralOperatorScalingCorrected`
(nested-commutator scaling with exponential inflation). -/
theorem theorem11_commutator_scaling_general :
    Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterGeneralOperatorScalingCorrected :=
  Qatlib.Concepts.TrotterFormula.GeneralOrder.trotterGeneralOperatorScalingCorrected

/-- An operator with a certified support radius (the paper's `S(B)` ball). -/
structure LocatedOperator (D : ℕ) where
  /-- The operator itself. -/
  op : Op D
  /-- Radius of a `d`-dimensional ball containing its support. -/
  radius : ℝ

/-- **Proposition 15, Eq. (145)** (arXiv:1912.08854v3, printed p. 38).
Bridge to the frozen FQN
`Qatlib.Concepts.TrotterFormula.LieStrang.trotterFirstOrderTailSum`:
the first-order Lie-Trotter error is bounded by `t²/2` times the tail-sum
commutator `Σ_γ ‖[Σ_{γ'>γ} H_{γ'}, H_γ]‖`. -/
theorem proposition15_lie_trotter_tail_sum :
    Qatlib.Concepts.TrotterFormula.LieStrang.TrotterFirstOrderTailSum :=
  Qatlib.Concepts.TrotterFormula.LieStrang.trotterFirstOrderTailSum

/-- **Proposition 16, Eq. (152)** (arXiv:1912.08854v3, printed p. 39).
Bridge to the frozen FQN
`finite_strang_tight_nested_commutator`: the second-order Strang error is
bounded by `|t|³` times the tight nested-commutator constant
`finiteStrangConstant H`, which aggregates each tail before taking the nested
commutator norm. -/
theorem proposition16_suzuki_second_tail (D m : ℕ) (H : Fin m → Operator D) (t : ℝ)
    (hH : ∀ j, (H j).IsHermitian) :
    ‖pfInterpret (finiteStrangWord H t 1) - HamiltonianEvolution (∑ j, H j) t‖ ≤
      |t| ^ 3 * finiteStrangConstant H :=
  finite_strang_tight_nested_commutator D m H t hH

/-- **Section 4.1 (digital quantum simulation, finite Strang word)**
(arXiv:1912.08854v3, §4.1).  Bridge to
`finite_strang_same_word_error_and_tariffs`: the actual repeated Strang word
is unitary, has the exact visit ledger, and obeys the tight second-order
error with `r` segments. -/
theorem section41_strang_word_and_tariffs (D m r : ℕ) (H : Fin m → Operator D)
    (t : ℝ) (price : ℕ → ℕ) (hH : ∀ j, (H j).IsHermitian) (hr : 0 < r) :
    let w := finiteStrangWord H t r
    pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ w.length = 2 * m * r ∧
    (∀ j : Fin m, (w.map Prod.snd).count j.val = 2 * r) ∧
    (w.map (fun x => price x.2)).sum = 2 * r * (∑ j : Fin m, price j.val) ∧
    ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) t‖ ≤
      |t| ^ 3 * finiteStrangConstant H / (r : ℝ) ^ 2 :=
  finite_strang_same_word_error_and_tariffs D m r H t price hH hr

/-- **Section 4.1 (selected accuracy and observable transport)**
(arXiv:1912.08854v3, §4.1).  Bridge to
`finite_strang_selected_accuracy_and_observable`. -/
theorem section41_strang_selected_accuracy (D m : ℕ) (H : Fin m → Operator D)
    (t ε : ℝ) (O : Operator D) (hH : ∀ j, (H j).IsHermitian) (hε : 0 < ε) :
    let r := finiteStrangSegments H t ε
    let w := finiteStrangWord H t r
    0 < r ∧ w.length = 2 * m * r ∧
    pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
    ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) t‖ ≤ ε ∧
    ‖(pfInterpret w)ᴴ * O * pfInterpret w -
      (HamiltonianEvolution (∑ j, H j) t)ᴴ * O * HamiltonianEvolution (∑ j, H j) t‖ ≤
        2 * ‖O‖ * ε :=
  finite_strang_selected_accuracy_and_observable D m H t ε O hH hε

/-- **Section 4.2 (local-observable simulation, Suzuki word)**
(arXiv:1912.08854v3, §4.2).  Bridge to
`suzuki_fourth_order_same_word_observable_consumer`. -/
theorem section42_suzuki_observable (I : Type) [Fintype I] [DecidableEq I]
    (A B O : Matrix I I ℂ) (t : ℝ) (r : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hr : 0 < r) :
    let V := suzuki4Run A B t r
    let U := HamiltonianEvolution (A + B) t
    ‖Vᴴ * O * V - Uᴴ * O * U‖ ≤
      200 * ‖O‖ * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / (r : ℝ) ^ 4 :=
  suzuki_fourth_order_same_word_observable_consumer I A B O t r hA hB hr

/-- **Section 4.2 (noisy recursive Suzuki word)**
(arXiv:1912.08854v3, §4.2).  Bridge to
`recursive_suzuki_noisy_same_word_observable`. -/
theorem section42_recursive_suzuki_noisy_observable (I : Type) [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t δ : ℝ)
    (V : List (Matrix I I ℂ)) (O : Matrix I I ℂ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hlen : V.length = (recursiveSuzukiWord hs k t r).length)
    (hV : ∀ U ∈ V, U ∈ Matrix.unitaryGroup I ℂ)
    (hn : ∀ j : ℕ, j < V.length →
      ‖V.getD j 0 - (recursiveSuzukiWord hs k t r).getD j 0‖ ≤ δ) :
    let U := NormedSpace.exp (t • hs.sum)
    let η := recursiveSuzukiError hs k t r + (V.length : ℝ) * δ
    V.prod ∈ Matrix.unitaryGroup I ℂ ∧ ‖V.prod - U‖ ≤ η ∧
      ‖V.prodᴴ * O * V.prod - Uᴴ * O * U‖ ≤ 2 * ‖O‖ * η :=
  recursive_suzuki_noisy_same_word_observable I hs k r t δ V O hhs hr hδ hlen hV hn

/-- **Section 4.3 (quantum Monte Carlo, imaginary-time family)**
(arXiv:1912.08854v3, §4.3).  Bridge to
`imaginary_family_selected_accuracy`: the selected segment count gives an
explicit `ε`-accurate imaginary-time product formula. -/
theorem section43_imaginary_family_selected_accuracy {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin m → Matrix I I ℂ) (t ε : ℝ)
    (hH : ∀ j : Fin m, (H j).PosSemidef) (ht : 0 ≤ t) (hε : 0 < ε) :
    let r := finiteImaginarySegments H t ε
    0 < r ∧ (imaginaryFamilyWord H t r).length = m * r ∧
    ‖imaginaryFamilyRun H t r‖ ≤ 1 ∧
    ‖imaginaryFamilyRun H t r - NormedSpace.exp (-t • ∑ j : Fin m, H j)‖ ≤ ε :=
  imaginary_family_selected_accuracy H t ε hH ht hε

end

end Qatlib.Papers.TrotterError19.MainResults

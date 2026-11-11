/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.ImaginaryTime.FiniteImaginaryProduct

/-!
# Imaginary-time output and accuracy bounds

This module transfers finite-family imaginary-time operator error bounds to normalized output
vectors and selects a segment count for a requested positive tolerance. It uses the first-order
commutator estimates associated with [ChildsEtAl2021Trotter].

## Main statements

* `imaginary_family_actual_postselection_consumer`: success-norm and normalized-output bounds
  under a positive output gap.
* `imaginary_family_selected_accuracy`: a positive segment count, exact word length,
  contraction, and tolerance bound.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.TrotterFormula.ImaginaryTime
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For a normalized input, positive-semidefinite terms, nonnegative time, and positive segment
count, an error budget `η < ‖v‖` gives success norm squared at least `(‖v‖ - η)²`,
normalized-output error at most `2 * η / ‖v‖`, and output norm at most one. The budget comes
from the finite first-order commutator bound of [ChildsEtAl2021Trotter]. -/
theorem imaginary_family_actual_postselection_consumer :
  ∀ {I : Type} [Fintype I] [DecidableEq I] {m : ℕ} (H : Fin m → Matrix I I ℂ)
    (t : ℝ) (r : ℕ) (ψ : I → ℂ),
    (∀ j : Fin m, (H j).PosSemidef) → 0 ≤ t → 0 < r →
    ‖toEuclidean_fromVec ψ‖ = 1 →
    let v := toEuclidean_fromVec ((NormedSpace.exp (-t • ∑ j : Fin m, H j)).mulVec ψ)
    let y := toEuclidean_fromVec ((imaginaryFamilyRun H t r).mulVec ψ)
    let η := t ^ 2 * imaginaryCommutatorSum H / (2 * (r : ℝ))
    η < ‖v‖ → (‖v‖ - η) ^ 2 ≤ ‖y‖ ^ 2 ∧
      ‖NormedSpace.normalize y - NormedSpace.normalize v‖ ≤ 2 * η / ‖v‖ ∧ ‖y‖ ≤ 1 := by
  intro I _ _ m H t r ψ hH ht hr hψ v y η hgap
  have h := imaginary_family_actual_word_error_and_tariffs H t r (fun _ => 0) hH ht hr
  exact contractive_mulVec_output_of_gap (imaginaryFamilyRun H t r)
    (NormedSpace.exp (-t • ∑ j, H j)) ψ η h.1 h.2.2.2.2 hψ hgap

/-- For positive-semidefinite terms, nonnegative time, and positive tolerance `ε`,
`finiteImaginarySegments` gives a positive segment count, word length `m * r`, a contractive
run, and error at most `ε`; see [ChildsEtAl2021Trotter] for the underlying error framework. -/
theorem imaginary_family_selected_accuracy :
  ∀ {I : Type} [Fintype I] [DecidableEq I] {m : ℕ} (H : Fin m → Matrix I I ℂ)
    (t ε : ℝ),
    (∀ j : Fin m, (H j).PosSemidef) → 0 ≤ t → 0 < ε →
    let r := finiteImaginarySegments H t ε
    0 < r ∧ (imaginaryFamilyWord H t r).length = m * r ∧
    ‖imaginaryFamilyRun H t r‖ ≤ 1 ∧
    ‖imaginaryFamilyRun H t r - NormedSpace.exp (-t • ∑ j : Fin m, H j)‖ ≤ ε := by
  intro I _ _ m H t ε hH ht hε
  (try dsimp only)
  let r := finiteImaginarySegments H t ε
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hceil : t^2*imaginaryCommutatorSum H/(2*ε) ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hn : Nat.ceil (t^2*imaginaryCommutatorSum H/(2*ε)) ≤ r := le_max_right _ _
      exact_mod_cast hn)
  have he : t^2*imaginaryCommutatorSum H/(2*(r : ℝ)) ≤ ε := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrR)).mpr
    have hbound := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hε)).mp hceil
    nlinarith
  have h := imaginary_family_actual_word_error_and_tariffs H t r (fun _ => 0) hH ht hr
  exact ⟨hr, h.2.1, h.1, h.2.2.2.2.trans he⟩

end Qatlib.Concepts.TrotterFormula.ImaginaryTime

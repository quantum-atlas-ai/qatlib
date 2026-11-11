/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.EqualityOracle
import Qatlib.Concepts.AdversaryBounds.LabelProgress.RelabelGram

/-!
# Label symmetry of equality-oracle states

This module expresses equality-oracle algorithm states as weighted input amplitude matrices and
proves invariance under permutations of output labels. The resulting commutation and
orbit-dimension bounds provide the label-symmetry setting considered in [MagniezZur2026].

## Main statements

* `amplitudes_relabel`: invariance of amplitude rows under label permutations.
* `equality_label_symmetric`: commutation of the reduced input operator with relabeling.
* `equality_orbit_bound`: an orbit-span dimension bound from the algorithm basis size.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix Module
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.EqualityDefs
open Qatlib.Concepts.QueryComplexity.EqualityOracle
open Qatlib.Concepts.AdversaryBounds.LabelProgress
variable {A : Type*} [Fintype A] {M N : ℕ}

/-- The type of functions from `Fin M` to `Fin N` used as oracle inputs. -/
abbrev Input (M N : ℕ) := Fin M → Fin N

/-- The permutation of input functions induced by postcomposition with a permutation of the
output labels. -/
def tableRelabel (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Input M N) where
  toFun f := σ ∘ f
  invFun f := σ.symm ∘ f
  left_inv f := by funext x;exact σ.symm_apply_apply (f x)
  right_inv f := by funext x;exact σ.apply_symm_apply (f x)

/-- The reciprocal square root of the number of input functions. -/
def uniformAmplitude (M N : ℕ) : ℝ := 1/Real.sqrt (Fintype.card (Input M N))

/-- The matrix of equality-oracle state amplitudes at time `t`, weighted by `uniformAmplitude M
N` across inputs. -/
def amplitudes
    (gates : ℕ → EuclideanSpace ℂ (Basis A (Fin M)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A (Fin M)))
    (initial : EuclideanSpace ℂ (Basis A (Fin M))) (t : ℕ) : Matrix (Input M N) (Basis A (Fin M)) ℂ :=
  fun f a => (uniformAmplitude M N : ℂ)*state f gates initial t a

/-- Relabeling the output values of an input function leaves its weighted equality-oracle
amplitude row unchanged. -/
theorem amplitudes_relabel
    (gates : ℕ → EuclideanSpace ℂ (Basis A (Fin M)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A (Fin M)))
    (initial : EuclideanSpace ℂ (Basis A (Fin M))) (t : ℕ) (σ : Equiv.Perm (Fin N)) (f : Input M N) :
    amplitudes gates initial t (tableRelabel σ f)=amplitudes gates initial t f := by
  funext a
  change (uniformAmplitude M N : ℂ)*state (σ ∘ f) gates initial t a=
    (uniformAmplitude M N : ℂ)*state f gates initial t a
  rw [state_relabel]

/-- The reduced input operator of the equality-oracle amplitude matrix commutes with every
output-label relabeling; see [MagniezZur2026]. -/
theorem equality_label_symmetric
    (gates : ℕ → EuclideanSpace ℂ (Basis A (Fin M)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A (Fin M)))
    (initial : EuclideanSpace ℂ (Basis A (Fin M))) (t : ℕ) (σ : Equiv.Perm (Fin N)) :
    (reducedInput (amplitudes (N := N) gates initial t)).mulVecLin.comp
        (inputRelabel (tableRelabel σ)).toLinearMap=
      (inputRelabel (tableRelabel σ)).toLinearMap.comp
        (reducedInput (amplitudes gates initial t)).mulVecLin :=
  invariant_of_equal_rows (amplitudes gates initial t) (tableRelabel σ)
    (amplitudes_relabel gates initial t σ)

/-- If the algorithm basis has at most `2^S` elements, every vector in the amplitude support has
a label-permutation orbit span of complex dimension at most `2^S`. -/
theorem equality_orbit_bound
    (gates : ℕ → EuclideanSpace ℂ (Basis A (Fin M)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A (Fin M)))
    (initial : EuclideanSpace ℂ (Basis A (Fin M))) (t S : ℕ)
    (hspace : Fintype.card (Basis A (Fin M)) ≤ 2^S)
    (v : Input M N → ℂ) (hv : v ∈ support (amplitudes gates initial t)) :
    finrank ℂ (orbitSpan (fun σ : Equiv.Perm (Fin N) => inputRelabel (tableRelabel σ)) v) ≤ 2^S :=
  actual_qubit_orbit (amplitudes gates initial t) _
    (equality_label_symmetric gates initial t) S hspace v hv

/-- Simultaneously permuting the output labels of two input functions preserves the inner
product of their equality-oracle states at every checkpoint. -/
theorem equality_checkpoint_gram
    (gates : ℕ → EuclideanSpace ℂ (Basis A (Fin M)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A (Fin M)))
    (initial : EuclideanSpace ℂ (Basis A (Fin M))) (t : ℕ)
    (σ : Equiv.Perm (Fin N)) (f g : Input M N) :
    inner ℂ (state (σ ∘ f) gates initial t) (state (σ ∘ g) gates initial t)=
      inner ℂ (state f gates initial t) (state g gates initial t) := by
  rw [state_relabel,state_relabel]
end Qatlib.Papers.CollisionLB26.EqualityDefs

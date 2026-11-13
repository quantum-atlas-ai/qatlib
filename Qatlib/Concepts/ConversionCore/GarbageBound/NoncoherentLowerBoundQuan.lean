/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.GarbageBound.NoncoherentLowerBoundStat
import Qatlib.Concepts.GramQueryCore.GramRealization.NoncoherentStateConversion
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound

/-!
# Query lower bounds with garbage states

`stateConversionNoncoherentLowerBound` constructs certificates for noncoherent conversion, where
target Gram matrices may be multiplied entrywise by a positive semidefinite matrix with diagonal
one. Phase alignment converts an absolute overlap guarantee into the certificate bounds `2 *
Real.sqrt (2 * ε)` and `2 * T`.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `stateConversionNoncoherentLowerBound`: The intermediate Gram matrix and adjusted garbage
  matrix certificates.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped ComplexOrder MatrixOrder BigOperators
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.GarbageBound

/-- A unitary `T`-query circuit with absolute overlaps at least √(1 − ε) with the specified
garbage target family yields positive semidefinite matrices `σ'` and `S'`, with diagonal one
for `S'`, and unfiltered and query-filtered certificate budgets 2√(2ε) and 2T for 0 < ε ≤ 1
[Lee et al., Theorem 4.9][LeeEtAl2011]. -/
theorem stateConversionNoncoherentLowerBound : StateConversionNoncoherentLowerBound := by
  classical
  intro X _ _ n T R input ε hε hε1 ρ σ hρ hσ χ hχ S hS hSdiag hgram C hT hC hov
  let φ (x : X) := Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)
  have hφ (x : X) : Normalized (φ x) :=
    hC.normalized_run (workspaceBitOracle_unitary (input x)) (hρ x)
  let a (x : X) := overlapPhase (Inner (φ x) (χ x))
  let χ' (x : X) : QState ((Fin n × Bool) × Fin R) := fun i => a x * χ x i
  let S' : Matrix X X ℂ := fun x y => (starRingEnd ℂ) (a x) * a y * S x y
  have ha (x : X) : ‖a x‖ = 1 := overlapPhase_norm _
  have hχ' (x : X) : Normalized (χ' x) := normalized_phase (χ x) (hχ x) (a x) (ha x)
  have hinner (x : X) : Inner (φ x) (χ' x) = (‖Inner (φ x) (χ x)‖ : ℂ) := by
    calc
      _ = a x * Inner (φ x) (χ x) := by
        simp only [Qatlib.Foundations.PureStateMath.inner_apply, χ']
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := overlapPhase_mul _
  have hov' (x : X) : Real.sqrt (1 - ε) ≤ (Inner (φ x) (χ' x)).re := by
    rw [hinner]
    exact hov x
  have hgram' : gramStateMatrix χ' = gramStateMatrix σ ⊙ S' := by
    rw [show gramStateMatrix χ' =
      (fun x y => (starRingEnd ℂ) (a x) * a y * gramStateMatrix χ x y) from
        gramStateMatrix_phase χ a]
    rw [hgram]
    ext x y
    simp only [hadamard_apply, S']
    ring
  refine ⟨gramStateMatrix φ, S', gramStateMatrix_posSemidef φ,
    posSemidef_phase S hS a, ?_, ?_, ?_⟩
  · intro x
    change (starRingEnd ℂ) (a x) * a x * S x x = 1
    rw [hSdiag, mul_one]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  · rw [← hgram']
    exact gramFilteredCert_mono
      (gramFilteredCert_of_realPart_overlap hε.le hε1 φ χ' hφ hχ' hov')
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : ε ≤ 2 * ε))
        (by norm_num))
  · exact gram_exact_state_conversion_filteredCert input ρ φ C hT hC hρ (fun _ _ => rfl)

end Qatlib.Concepts.ConversionCore.GarbageBound

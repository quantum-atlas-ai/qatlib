/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QShannonWilde11.MainResults.EntanglementDefs

/-!
# Separability witnesses and pure-state entanglement entropy

The singlet has a negative partial-transpose quadratic form and is therefore
entangled. More generally, separable states have positive partial transpose,
and a normalized pure state is separable exactly when its vector is a product
state. The module also records nonnegative entanglement entropy, bounds by the
logarithms of both subsystem dimensions, and the Bell-state value `log 2`.

The information-theoretic setting is [Wilde2017]. The partial-transpose test is
[Peres, separability criterion][Peres1996]; a broader survey is [HorodeckiEtAl2009].
-/
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.QShannonWilde11.MainResults

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The specified Bell state has partial transpose expectation −1 on the given witness vector
and is not separable. -/
theorem clause17_witness_certifies :
    (star (Ket (0 : Fin 2 × Fin 2) + Ket (1, 1)) ⬝ᵥ
      (PartialTranspose (outerProduct (bell (true, true))) *ᵥ
        (Ket (0 : Fin 2 × Fin 2) + Ket (1, 1))) = (-1 : ℂ)) ∧
    ¬ IsSeparableState (outerProduct (bell (true, true))) :=
  ⟨singlet_partialTranspose_form, bell_singlet_not_isSeparableState⟩

/-- For a normalized bipartite pure state, its outer product is separable exactly when the state
is a product state. -/
theorem clause17_product_criterion (D E : ℕ) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    IsSeparableState (outerProduct ψ) ↔ IsProductState ψ :=
  isSeparableState_outerProduct_iff_isProductState ψ hψ

/-- Separability implies positivity of the partial transpose, the necessary
criterion of [Peres][Peres1996]. -/
theorem clause17_ppt_necessary (D E : ℕ) (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hρ : IsSeparableState ρ) : (PartialTranspose ρ).PosSemidef :=
  partialTranspose_posSemidef_of_isSeparableState ρ hρ

/-- Pure-state entanglement entropy lies between zero and the logarithm of
either subsystem dimension; see [Wilde, entanglement entropy][Wilde2017]. -/
theorem clause17_entropy_values (D E : ℕ) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    0 ≤ entropy ψ hψ ∧ entropy ψ hψ ≤ Real.log D ∧ entropy ψ hψ ≤ Real.log E := by
  refine And.intro ?_ (And.intro (entropy_le_log_left ψ hψ) (entropy_le_log_right ψ hψ))
  exact entropy_nonneg ψ hψ

/-- Every Bell state has entanglement entropy log 2. -/
theorem clause17_entropy_bell (s : Bool × Bool) :
    entropy (bell s) (bell_normalized s) = Real.log 2 :=
  entropy_bell s

/-- Collects Bell state nonseparability, the pure state product criterion for separability, and
positivity of the partial transpose of every separable state. See [Wilde2017]. -/
theorem clause4_endpoint :
    (¬ IsSeparableState (outerProduct (bell (true, true))) ∧
    (∀ (D E : ℕ) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
      IsSeparableState (outerProduct ψ) ↔ IsProductState ψ) ∧
    (∀ (D E : ℕ) (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : IsSeparableState ρ),
      (PartialTranspose ρ).PosSemidef)) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · exact bell_singlet_not_isSeparableState
  · exact clause17_product_criterion
  · intro D E ρ hρ
    exact clause17_ppt_necessary D E ρ hρ

end Qatlib.Papers.QShannonWilde11.MainResults

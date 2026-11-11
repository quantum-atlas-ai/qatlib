/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryLearn09.MainResults.MeasureRotate

set_option backward.isDefEq.respectTransparency false

/-!
# UnitaryLearn09 — optimal inversion of an unknown unitary (Sec. IV)

Fixed source: Bisio–Chiribella–D'Ariano–Facchini–Perinotti,
*Optimal quantum learning of a unitary transformation*, arXiv:0903.0543v2
(PDF SHA-256 7740f8bf94c88b19a046c4c627cda8edf148bf92fe178c381fd20bceede57048),
Section IV (optimal inversion), p. 6.

Section IV considers producing `M` copies of `U†` instead of `U`.  Its argument
is a substitution: the inversion fidelity is obtained from the learning
fidelity by replacing the target `U` with `U†` (`F′ = 1/d² ∫ ⟨⟨U†|⊗M ⟨⟨U*|⊗N L′
|U†⟩⟩⊗M |U*⟩⟩⊗N dU`), so the optimal inversion is achieved by the same
measure-and-rotate strategy — measure the optimal POVM `P_Û` on the optimal
state `|φ_U⟩` and apply `Û^{†⊗M}` conditionally.

This file formalizes the scalar content of that substitution: the fidelity of
the measure-and-rotate inversion strategy with estimate `Û†` equals the
learning fidelity with estimate `Û`, for every `M`, because passing to adjoints
leaves the unitary channel fidelity unchanged (`unitaryChannelFidelity_adjoint`).
The reference-frame-realignment application to Ref. [11] is not formalized.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.UnitaryLearn09.MainResults

variable {Ξ : Type*} [Fintype Ξ] {d : ℕ}

/-- The inversion strategy of Sec. IV: measure the POVM `P_Û` on the memory
state and apply `Û^{†⊗M}` conditionally; its fidelity is the POVM average of
the `M`-th powers of `F(U†, Û†)`. -/
def inversionEstimateFidelity (P : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) (M : ℕ) : ℝ :=
  ∑ ξ, bornProb P ψ ξ *
    (unitaryChannelFidelity (I := Fin d) Uᴴ ((V ξ)ᴴ)) ^ M

/-- Sec. IV's substitution: the inversion strategy with estimate `Û†` has
exactly the fidelity of the learning strategy with estimate `Û`, because
`F(U†, Û†) = F(U, Û)`.  Hence the same POVM and memory state are optimal for
both tasks, which is the content of the paper's claim that optimal inversion is
obtained by substituting `U → U†`. -/
theorem inversionEstimateFidelity_eq_learning (P : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) (M : ℕ) :
    inversionEstimateFidelity P V U ψ M = globalEstimateFidelity P V U ψ M := by
  unfold inversionEstimateFidelity globalEstimateFidelity
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [unitaryChannelFidelity_adjoint]

end Qatlib.Papers.UnitaryLearn09.MainResults

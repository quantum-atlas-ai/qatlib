/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MetropWeak24.SamplerImpl.Basic
public import Qatlib.Papers.MetropWeak24.SamplerImpl.NormTheory
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# Closed trace-norm consequences for MetropWeak24

The variational formula and linear-map perturbation chain are preserved from
arXiv:2406.16023v1, Lemmas 34 and 23, with their full original hypotheses.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Papers.MetropWeak24.SamplerImpl
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-
namespace Qatlib.Papers.MetropWeak24.SamplerImpl.NormTheory

/-- The trace norm is the greatest real trace pairing with a unitary, in the paper's right-pairing convention. -/
theorem lemma34_variational {D : ℕ} (M : Operator D) :
    IsGreatest
      {x : ℝ | ∃ U : @Matrix.unitaryGroup (Fin D) (Classical.decEq (Fin D))
          (Fin.fintype D) ℂ Complex.commRing Complex.instStarRing,
        Complex.re ((M * U.val).trace) = x}
      (SchattenOne M) := by
  have h := Matrix.traceNorm_eq_max_re_tr_U M
  have hset : {x : ℝ | ∃ U : @Matrix.unitaryGroup (Fin D) (Classical.decEq (Fin D))
        (Fin.fintype D) ℂ Complex.commRing Complex.instStarRing,
        Complex.re ((M * U.val).trace) = x}
      = {x : ℝ | ∃ U : @Matrix.unitaryGroup (Fin D) (Classical.decEq (Fin D))
        (Fin.fintype D) ℂ Complex.commRing Complex.instStarRing,
        Complex.re ((U.val * M).trace) = x} := by
    ext x
    constructor
    · rintro ⟨U, hU⟩
      exact ⟨U, by rw [Matrix.trace_mul_comm]; exact hU⟩
    · rintro ⟨U, hU⟩
      exact ⟨U, by rw [Matrix.trace_mul_comm]; exact hU⟩
  rw [hset, schattenOne_eq_traceNorm]
  exact h

end Qatlib.Papers.MetropWeak24.SamplerImpl.NormTheory
-/

namespace Qatlib.Papers.MetropWeak24.SamplerImpl.DriftBounds

/-- **Lemma 23 (arXiv:2406.16023v1, p. 19).**
`|𝓛(ρ_β)|_1 ≤ |𝓛(ρ_{β0})|_1 + |𝓛(ρ_β - ρ_{β0})|_1 ≤ |𝓛(ρ_{β0})|_1 + 4·2βw`.

The hypothesis `hLip` is the unfolding of `|𝓛|_⋆ ≤ 4` (Lemma 16): a linear map
whose induced trace norm is at most `4` satisfies
`|𝓛(N)|_1 ≤ 4 |N|_1` for every `N`. -/
theorem lemma23 {n : ℕ} (L : SuperOp n) (ρβ ρβ0 : QOp n) (b : ℝ)
    (hLip : ∀ N : QOp n, SchattenOne (L N) ≤ 4 * SchattenOne N)
    (hsmall : SchattenOne (ρβ - ρβ0) ≤ 2 * b) :
    SchattenOne (L ρβ) ≤ SchattenOne (L ρβ0) + 4 * (2 * b) := by
  have hab : ρβ0 + (ρβ - ρβ0) = ρβ := by abel
  have hsplit : L ρβ = L ρβ0 + L (ρβ - ρβ0) := by
    rw [← map_add, hab]
  calc SchattenOne (L ρβ)
      = SchattenOne (L ρβ0 + L (ρβ - ρβ0)) := by rw [hsplit]
    _ ≤ SchattenOne (L ρβ0) + SchattenOne (L (ρβ - ρβ0)) := schattenOne_add_le _ _
    _ ≤ SchattenOne (L ρβ0) + 4 * (2 * b) := by
        have h1 := hLip (ρβ - ρβ0)
        nlinarith [h1, hsmall]

end Qatlib.Papers.MetropWeak24.SamplerImpl.DriftBounds

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9MaxEntCharacterizationStat

/-!
# Constructing the Eq. (9) resource form

The theorem `eq9MaxEntCharacterization` constructs the two-orthonormal-pair representation of a
normalized pure state with maximally mixed first marginal. The construction uses the
computational basis for the first pair and scaled resource rows for the second. The resource
setting is the qubit teleportation protocol of [BennettEtAl1993Teleportation].

## Main statements

* `scaledRow_inner`: The inner product of rows `i` and `j` of `Ψ`, each scaled by `√2`, equals
  twice entry `(j, i)` of `PartialTrace (outerProduct Ψ)`.
* `eq9MaxEntCharacterization`: Every normalized pure two-qubit state with first marginal `(1 /
  2) • 1` has a two-orthonormal-pair resource representation. See [Bennett et al., 1993, Eq.
  (9)][BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix

/-- The complex coercion of `√2` multiplied by itself equals two. -/
private theorem sqrtTwo_mul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- The inner product of rows `i` and `j` of `Ψ`, each scaled by `√2`, equals twice entry `(j,
i)` of `PartialTrace (outerProduct Ψ)`. -/
private theorem scaledRow_inner (Ψ : QState (Fin 2 × Fin 2)) (i j : Fin 2) :
    Qatlib.Foundations.PureStateMath.Inner (fun c => (Real.sqrt 2 : ℂ) * Ψ (i,c))
      (fun c => (Real.sqrt 2 : ℂ) * Ψ (j,c)) =
      2 * PartialTrace (outerProduct Ψ) j i := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, map_mul, Complex.star_def,
    Complex.conj_ofReal, PartialTrace, outerProduct_apply,
    Fin.sum_univ_two]
  calc
    _ = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) *
      (Ψ (j,0) * starRingEnd ℂ (Ψ (i,0)) + Ψ (j,1) * starRingEnd ℂ (Ψ (i,1))) := by ring
    _ = _ := by rw [sqrtTwo_mul]

/-- Every normalized pure two-qubit state with first marginal `(1 / 2) • 1` has a
two-orthonormal-pair resource representation. See [Bennett et al., 1993, Eq.
(9)][BennettEtAl1993Teleportation]. -/
theorem eq9MaxEntCharacterization : Eq9MaxEntCharacterization := by
  intro Ψ _ hm
  let p : QState (Fin 2) := fun c => (Real.sqrt 2 : ℂ) * Ψ (0,c)
  let q : QState (Fin 2) := fun c => (Real.sqrt 2 : ℂ) * Ψ (1,c)
  refine ⟨Qatlib.Foundations.PureStateMath.Ket 0, Qatlib.Foundations.PureStateMath.Ket 1,
      p, q, ?_, ?_⟩
  · refine ⟨normalized_ket 0, normalized_ket 1, ?_, ?_, ?_, ?_⟩
    · rw [normalized_iff_inner_self, scaledRow_inner, hm]
      norm_num
    · rw [normalized_iff_inner_self, scaledRow_inner, hm]
      norm_num
    · norm_num [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Qatlib.Foundations.PureStateMath.Ket, Fin.sum_univ_two]
    · change Qatlib.Foundations.PureStateMath.Inner (fun c => (Real.sqrt 2 : ℂ) * Ψ (0,c))
        (fun c => (Real.sqrt 2 : ℂ) * Ψ (1,c)) = 0
      rw [scaledRow_inner, hm]
      norm_num [Matrix.one_apply]
  · have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
    funext ⟨i,c⟩
    fin_cases i <;> simp [eq9Resource, Qatlib.Foundations.PureStateMath.Ket, p, q, hn]

end Qatlib.Concepts.QuditTeleport.ResourceIff

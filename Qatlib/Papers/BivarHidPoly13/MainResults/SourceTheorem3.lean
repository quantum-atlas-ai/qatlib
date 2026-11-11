/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BivarHidPoly13.MainResults.HiddenPolyModel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# BivarHidPoly13 — Theorem 3 (c003)

Fixed source: arXiv:1305.1543v2 (9 Oct 2013), Theorem 3, p.7; proof route in
Section 2.2–2.6 (p.7–14).

Theorem 3 (p.7). *Let `m`, `r` and `D` be constants and let `f : F → Fᵐ` be a
function as defined in (6),*

`f(x) = (f_1(x), …, f_m(x))`, `f_i(x) = Σ_{s=1}^{D} a_{is}(v) x^s`,
`a_{is}(v) = Σ_{j=1}^{r} a_{isj} v_j`,

*then there is a quantum algorithm which, given `O(1)` states of the form
`Σ_{x∈F} |w + f(x)⟩|x⟩` for various unknown vectors `w ∈ Fᵐ`, determines the
unknown parameters `v_1, …, v_r` efficiently.*

The paper's algorithm is a recursion on `r` (Section 2.4, p.8–9): the inner
procedure produces a **linear constraint** `Σ_j α_j v_j = β` with some
`α_i ≠ 0` (Eq. (7), p.8).  If `α_{i0} ≠ 0`, one solves for `v_{i0}`,
`v_{i0} = (β − Σ_{j≠i0} α_j v_j)/α_{i0}`, and recurses on the remaining `r − 1`
parameters.  In the base case the single constraint gives `v_1`.  Collecting
`r` independent constraints is therefore exactly an invertible `r × r` linear
system in `v`.

Formalized here (the mathematical kernel of the recursion):

* `vectorHiddenPoly` — the source shape (6);
* `theorem3_recursion_step` — the substitution solving for `v_{i0}` under one
  constraint (p.8–9);
* `theorem3_parameters_determined` — `r` independent constraints (an invertible
  constraint matrix `A`) determine `v` uniquely, so the recursion's output is
  the true parameter vector.

Modeled residue (not discharged): the quantum inner procedure that fabricates
the `r` independent constraints in `polylog(|F|)` time (QFT, the Las Vegas
`δ`-search via [7], the power-of-`p` degree elimination of Section 2.6).  This
is where the gate-level circuit and the `UniformBqp.FiniteGateWord` model would
enter.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Matrix

namespace Qatlib.Papers.BivarHidPoly13.MainResults

variable {F : Type*} [Field F]

/-- Source Equation (6), p.7: the vector-valued hidden function
`f_i(x) = Σ_{s=1}^{D} a_{is}(v) x^s` with `a_{is}(v) = Σ_{j=1}^{r} a_{isj} v_j`,
encoded by `a : Fin m → Fin D → Fin r → F`. -/
def vectorHiddenPoly (m D r : ℕ) (a : Fin m → Fin D → Fin r → F)
    (v : Fin r → F) (x : F) : Fin m → F :=
  fun i => ∑ s : Fin D, (∑ j : Fin r, a i s j * v j) * x ^ (s.val + 1)

/-- Equation (7), p.8: a linear constraint `Σ_j α_j v_j = β` for the unknown
parameters, with some `α_i ≠ 0`. -/
def LinearConstraint (r : ℕ) : Type _ := (Fin r → F) × F

/-- Section 2.4, p.8–9: from a linear constraint `Σ_j α_j v_j = β` with
`α_{i0} ≠ 0`, the parameter `v_{i0}` is *determined*:
`v_{i0} = (β − Σ_{j≠i0} α_j v_j)/α_{i0}`.  This is the substitution that drives
the outer recursion. -/
theorem theorem3_recursion_step {r : ℕ} (α : Fin r → F) (v : Fin r → F) (β : F)
    (i0 : Fin r) (hα : α i0 ≠ 0)
    (hv : ∑ j : Fin r, α j * v j = β) :
    v i0 =
      (β - ∑ j ∈ (Finset.univ : Finset (Fin r)) \ {i0}, α j * v j) / α i0 := by
  have hsplit : ∑ j : Fin r, α j * v j
      = (∑ j ∈ (Finset.univ : Finset (Fin r)) \ {i0}, α j * v j) + α i0 * v i0 := by
    rw [Finset.sdiff_singleton_eq_erase]
    exact (Finset.sum_erase_add Finset.univ (fun j => α j * v j)
      (Finset.mem_univ i0)).symm
  rw [hsplit] at hv
  field_simp
  linear_combination hv

/-- **Theorem 3 (c003), parameter determination by the constraint system.**
The recursion of Section 2.4 collects `r` linear constraints on `v`; when their
coefficient matrix `A` (rows `α^{(1)}, …, α^{(r)}`) is invertible and the right
side is `β = A v`, the parameter vector `v` is the unique solution.  Thus the
unknown parameters are determined, which is the content of Theorem 3 once the
inner procedure has produced the constraints.

Fixed arXiv:1305.1543v2, Theorem 3, p.7; recursion p.8–9. -/
theorem theorem3_parameters_determined {r : ℕ}
    (A : Matrix (Fin r) (Fin r) F) (β : Fin r → F)
    (hA : IsUnit A) {v v' : Fin r → F}
    (hv : A *ᵥ v = β) (hv' : A *ᵥ v' = β) :
    v = v' := by
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hA
  apply hinj
  rw [hv, hv']

end Qatlib.Papers.BivarHidPoly13.MainResults

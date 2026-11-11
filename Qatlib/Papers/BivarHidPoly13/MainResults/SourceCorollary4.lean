/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BivarHidPoly13.MainResults.SourceTheorem3
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-!
# BivarHidPoly13 — Corollary 4 (c004)

Fixed source: arXiv:1305.1543v2 (9 Oct 2013), Corollary 4, p.7.

Corollary 4 (p.7). *Let `f(x) = (Σ_{s=1}^{D} ν_{1s} x^s, …, Σ_{s=1}^{D} ν_{ms} x^s)`.
Then there is a quantum algorithm which, given `O(1)` states of the form
`Σ_{x∈F} |w + f(x)⟩|x⟩` for various unknown `w ∈ Fᵐ`, determines efficiently
the unknown coefficients `ν_{is}` for `i = 1, …, m` and `s = 1, …, D`.*

The paper notes (p.7, after the corollary) that Corollary 4 is the special case
of Theorem 3 with `r = mD` and `a_{is}(v) = v_{(i−1)D+s} = ν_{is}`.  Hence the
coefficient tensor is the indicator of the index map `(i,s) ↦ (i−1)D+s`; the
vector `v` *is* the flattened coefficient table `ν`.

Formalized here: the indicator tensor `corollaryCoeffs`, the identification
`corollary4_hiddenFunction_eq` (the generalized `f` of (6) with this tensor is
exactly the Corollary 4 polynomial), and the reduction
`corollary4_coefficients_determined`, which instantiates Theorem 3 at
`r = mD`.  The same modeled residue as Theorem 3 applies (the quantum
constraint-finding procedure).
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Matrix

namespace Qatlib.Papers.BivarHidPoly13.MainResults

variable {F : Type*} [Field F]

/-- The index `(i,s) ↦ (i−1)D+s` (0-based: `i·D + s`) as an element of
`Fin (m·D)`, i.e. the flattening of the coefficient table `ν_{is}`. -/
def corollaryIndex {m D : ℕ} (i : Fin m) (s : Fin D) : Fin (m * D) :=
  ⟨i.val * D + s.val, by
    have hi : i.val < m := i.isLt
    have hs : s.val < D := s.isLt
    have h1 : i.val * D + s.val < (i.val + 1) * D := by
      calc i.val * D + s.val < i.val * D + D := by omega
        _ = (i.val + 1) * D := by ring
    have hle : (i.val + 1) * D ≤ m * D :=
      Nat.mul_le_mul_right D (by omega)
    omega⟩

/-- Corollary 4, p.7: `a_{is}(v) = v_{(i−1)D+s} = ν_{is}`.  As a tensor over the
flattened index it is the indicator of `(i,s) ↦ (i−1)D+s`. -/
def corollaryCoeffs (m D : ℕ) : Fin m → Fin D → Fin (m * D) → F :=
  fun i s j => if j.val = i.val * D + s.val then 1 else 0

/-- The indicator tensor picks out the flattened coefficient `ν_{is}`. -/
theorem corollaryCoeffs_apply (m D : ℕ) (i : Fin m) (s : Fin D)
    (v : Fin (m * D) → F) :
    (∑ j : Fin (m * D), corollaryCoeffs m D i s j * v j) =
      v (corollaryIndex i s) := by
  unfold corollaryCoeffs
  rw [Finset.sum_eq_single (corollaryIndex i s)]
  · simp [corollaryIndex]
  · intro b _ hb
    have hne : b.val ≠ i.val * D + s.val := by
      intro h
      exact hb (Fin.ext h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Corollary 4 reduction (p.7): the generalized hidden function (6) with the
indicator tensor is exactly the Corollary 4 polynomial
`f_i(x) = Σ_{s=1}^{D} ν_{is} x^s`, with `ν_{is} = v_{(i−1)D+s}`. -/
theorem corollary4_hiddenFunction_eq (m D : ℕ) (v : Fin (m * D) → F) (x : F) :
    vectorHiddenPoly m D (m * D) (corollaryCoeffs (F := F) m D) v x =
      fun i => ∑ s : Fin D, v (corollaryIndex i s) * x ^ (s.val + 1) := by
  funext i
  simp only [vectorHiddenPoly]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [corollaryCoeffs_apply]

/-- **Corollary 4 (c004).**  In the Corollary 4 specialization (`r = mD`,
`a_{is}(v) = v_{(i−1)D+s}`), `r` independent linear constraints determine the
whole coefficient table `ν_{is}`: any two parameter vectors satisfying the same
invertible constraint system `A v = β` yield the same flattened coefficients
`ν_{is} = v_{(i−1)D+s}`.  This is the Theorem 3 kernel instantiated at the
Corollary 4 index map.

Fixed arXiv:1305.1543v2, Corollary 4, p.7. -/
theorem corollary4_coefficients_determined (m D : ℕ)
    (A : Matrix (Fin (m * D)) (Fin (m * D)) F) (β : Fin (m * D) → F)
    (hA : IsUnit A) {v v' : Fin (m * D) → F}
    (hv : A *ᵥ v = β) (hv' : A *ᵥ v' = β) :
    (fun (i : Fin m) (s : Fin D) => v (corollaryIndex i s))
      = fun (i : Fin m) (s : Fin D) => v' (corollaryIndex i s) := by
  have hvv : v = v' := theorem3_parameters_determined A β hA hv hv'
  rw [hvv]

end Qatlib.Papers.BivarHidPoly13.MainResults

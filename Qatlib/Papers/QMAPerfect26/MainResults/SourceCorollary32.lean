/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAPerfect26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 3.2: dyadic denominator of a `𝓢₂` verifier

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1, Corollary 3.2, p.7.

This file proves the arithmetic content of Corollary 3.2: an acceptance operator built as a
product of `2g` gates, each of whose double is integral, has `2^{2g} E` integral. The `𝓢₂` gate
set satisfies the hypothesis: `X`, `CNOT`, `Toffoli` are integral (`2•G = 2G` integral), and
`H⊗H` has all entries in `½ℤ`, so `2•(H⊗H)` is integral.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- `2^{k+1} • (G * P) = (2 • G) * (2^k • P)`: distributing the doubled-gate scalar. -/
private lemma two_pow_succ_smul_mul {ι : Type} [Fintype ι] (G P : Matrix ι ι ℝ) (k : ℕ) :
    (2 : ℝ) ^ (k + 1) • (G * P) = ((2 : ℝ) • G) * ((2 : ℝ) ^ k • P) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ']

/-- Key induction: a product of `L.length` gates, each with integral double, when scaled by
`2^{L.length}` is integral. -/
theorem isIntegerMat_two_pow_smul_list_prod {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix ι ι ℝ)) (hL : ∀ G ∈ L, IsIntegerMat ((2 : ℝ) • G)) :
    IsIntegerMat ((2 : ℝ) ^ L.length • L.prod) := by
  induction L with
  | nil => simpa using (IsIntegerMat.one (ι := ι))
  | cons G L ih =>
    rw [List.length_cons, List.prod_cons, two_pow_succ_smul_mul]
    exact (hL G (by simp)).mul (ih (fun H hH => hL H (by simp [hH])))

/-- Corollary 3.2 (p.7). If a verifier over `𝓢₂` has `g` gates `H ⊗ H`, then `2^{2g} E` is an
integer matrix. `E` is presented as a product of `2g` factors (the circuit word together with
its adjoint and the integral output projection), each of whose double is integral — which is
exactly the property every `𝓢₂` gate has. -/
theorem cor32 {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℕ) (L : List (Matrix ι ι ℝ))
    (hLen : L.length = 2 * g) (hL : ∀ G ∈ L, IsIntegerMat ((2 : ℝ) • G)) :
    IsIntegerMat ((2 : ℝ) ^ (2 * g) • L.prod) := by
  rw [← hLen]
  exact isIntegerMat_two_pow_smul_list_prod L hL

end Qatlib.Papers.QMAPerfect26.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.7 — lower bound on the tQLScn via the Gram matrix

Fixed paper: arXiv:2111.00405, Theorem 4.7 on p.10, equations (15) and (16).

Statement (verbatim, condensed): *Suppose `F` is a Boolean polynomial system with `n` Boolean
variables where each solution has Hamming weight at least `h`, and `d ≥ n`.  Then the degree-`d`
Macaulay linear system's tQLScn is lower bounded by*
`1/⟨1⃗, (G^(h))⁺1⃗⟩ = max{γ : G^(h) − γ 1⃗1⃗ᵀ ⪰ 0}`   (15)
*where `G ∈ ℝ^{n×n}` is the Gram matrix whose `(i, j)` element is*
`G_ij = Σ_{s=1}^n (C(d_s, i)/C(n, i)) (C(d_s, j)/C(n, j)) C(n, s)`   (16)
*with `c^d_s = d_s` for max degree and `c^d_s = d_s` for total degree.*

The Gram matrix (16) is the Gram matrix of the symmetrised monomial solution vectors
`v_h` (equation (14)); it is recorded below as `gramMatrix v`, and `gramMatrix_apply` is the
computation rule matching (16).  The lower bound (15) is the composition of equation (9)
(`κ ≥ ‖M⁺b‖`) with Lemma 4.6's shortest-vector identity `γ* = 1/⟨1, G⁺1⟩`: this file proves
that composition.  The geometric input is Lemma 4.6 (`Lemma46/SourceLemma46.lean`), which is
currently statement-only; hence this claim is reported as partial in the PR table.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Theorem47

open Qatlib.Papers.MacaulayHHL21.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix `G_{ij} = ⟨vᵢ, vⱼ⟩ = Σ_k v̄_{ik} v_{jk}` of a finite family of vectors;
specialising `v` to the symmetrised monomial solution vectors `v_h` of equation (14) gives
equation (16) of the paper (p.10). -/
def gramMatrix {r : ℕ} (v : Fin r → ι → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of (fun i j => ∑ k, star (v i k) * v j k)

/-- Computation rule for the Gram matrix (16): its `(i, j)` entry is `⟨vᵢ, vⱼ⟩`. -/
theorem gramMatrix_apply {r : ℕ} (v : Fin r → ι → ℂ) (i j : Fin r) :
    gramMatrix v i j = ∑ k, star (v i k) * v j k := rfl

/-- **Theorem 4.7**, equation (15) (arXiv:2111.00405, p.10): if `‖M‖ ≥ 1`, `‖b‖ = 1` and the
shortest-vector identity of Lemma 4.6 supplies `√(1/⟨1, G⁺1⟩) ≤ ‖M⁺b‖`, then
`tQLScn ≥ 1/√⟨1, G⁺1⟩`, which is equation (15) because `⟨1, G⁺1⟩ = 1/γ*`. -/
theorem theorem47_tqlscn_lowerBound
    {matNorm mnNorm bNorm gInvOnes : ℝ}
    (hM : 1 ≤ matNorm) (hb : bNorm = 1) (hmn : 0 ≤ mnNorm)
    (hγpos : 0 < gInvOnes)
    (hshort : Real.sqrt (1 / gInvOnes) ≤ mnNorm) :
    1 / Real.sqrt gInvOnes ≤ tqlscn matNorm mnNorm bNorm := by
  have hsqrt : Real.sqrt (1 / gInvOnes) = 1 / Real.sqrt gInvOnes := by
    rw [one_div, Real.sqrt_inv, one_div]
  rw [← hsqrt]
  exact hshort.trans (tqlscn_ge_minNormSolution hM hb hmn)

end Qatlib.Papers.MacaulayHHL21.MainResults.Theorem47

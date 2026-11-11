/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceBeurlingWeight

/-!
# SU(2)-valued nonlinear Fourier transform: source model

Fixed source: arXiv:2603.02021v1 (2026-03-02), §1 p.1 and §2 pp.4–5.

The paper defines, for a sequence `F : ℤ → ℂ`, the `SU(2)`-valued nonlinear Fourier
transform (NLFT) as the ordered product (1.1)

```
G(z) = ∏_{k = -∞}^{∞} (1 + |F_k|²)^{-1/2} · [[1, F_k z^k], [-F̄_k z^{-k}, 1]],
```

with lower indices to the left, and then `(a, b)` denotes the first row, i.e.
`G(z) = [[a(z), b(z)], [-b*(z), a*(z)]]`, with `a a* + b b* = 1` on `𝕋` (1.2).

We model:

* `nlftFactor F k z` — the `k`-th factor of (1.1);
* `nlftPartial F N M z` — the ordered product `∏_{k=N}^{M}` (increasing `k`, left to right);
* `IsNLFTImage F a b` — the two-sided product converges to `[[a, b], [-b*, a*]]`
  at every point of the circle (the paper's limit definition for `ℓ²` data, p.1),
  together with the normalization (1.2);
* `truncBelow F n` — the truncated sequence `(F_j)_{j ≤ n}` used in Lemma 5 (p.12).

All objects are the paper's, at the level of the fixed v1 PDF.
-/

open scoped BigOperators Matrix
open Matrix Filter Topology

set_option autoImplicit false

namespace Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

noncomputable section

/-- The `k`-th factor of the NLFT product (1.1) at the point `z ∈ 𝕋`. -/
def nlftFactor (F : ℤ → ℂ) (k : ℤ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Real.sqrt (1 + ‖F k‖ ^ 2))⁻¹ : ℝ) : ℂ) •
    !![1, F k * z ^ k; -(starRingEnd ℂ (F k)) * z ^ (-k), 1]

/-- The ordered product `∏_{k=N}^{M}` of the factors (1.1), lower indices to the left.
Returns the empty product when `M < N`. -/
def nlftPartial (F : ℤ → ℂ) (N M : ℤ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((List.range (M - N + 1).toNat).map fun i : ℕ => nlftFactor F (N + (i : ℤ)) z).prod

/-- The `SU(2)`-NLFT matrix `[[a, b], [-b*, a*]]` associated with a pair `(a, b)` of
circle functions (p.1). -/
def nlftMatrix (a b : CircleT → ℂ) (x : CircleT) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a x, b x; -(starFun b x), starFun a x]

/-- `(a, b)` is the NLFT image of `F` (arXiv:2603.02021v1, (1.1) and p.1):
the two-sided ordered product converges pointwise on `𝕋` to the `SU(2)` matrix
`[[a, b], [-b*, a*]]`, and the normalization `a a* + b b* = 1` of (1.2) holds. -/
def IsNLFTImage (F : ℤ → ℂ) (a b : CircleT → ℂ) : Prop :=
  (∀ x : CircleT, a x * starFun a x + b x * starFun b x = 1) ∧
    ∀ x : CircleT,
      Tendsto (fun N : ℕ => nlftPartial F (-(N : ℤ)) (N : ℤ) ((AddCircle.toCircle x : Circle))) atTop
        (nhds (nlftMatrix a b x))

/-- The truncated sequence `(F_j)_{j ≤ n}` of Lemma 5 (p.12). -/
def truncBelow (F : ℤ → ℂ) (n : ℤ) : ℤ → ℂ := fun j => if j ≤ n then F j else 0

/-- The sequence of a finitely supported tail beyond `n`. -/
def truncAbove (F : ℤ → ℂ) (n : ℤ) : ℤ → ℂ := fun j => if n < j then F j else 0

/-- The weighted `ℓ¹` norm of the NLFT data regarded as the pair `(a, b)` (p.7). -/
def pairAWnorm (W : StrongBeurlingWeight) (a b : CircleT → ℂ) : ℝ :=
  AWnorm W a + AWnorm W b

end

end Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

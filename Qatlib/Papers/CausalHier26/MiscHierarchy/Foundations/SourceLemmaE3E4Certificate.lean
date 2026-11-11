/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemmaE3E4Certificate — Lemmas E.3 and E.4 (sequential certificate)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Appendix E,
pp. 37-39 (txt lines 1964-2100), Eqs. (190)-(202).

**Lemma E.3 (positivity), Eq. (194).**  With

```
n± = (1, ∓s/μ, 0, ∓s^2/μ),      e3 = (0,0,1,0),
A± = μ(1 ∓ μ)/2,                B± = s(μ ∓ 1)/2,
c+ = s^2(1-μ)/(2μ),             c- = s^2(1+μ)/(2μ) + Δ,
P± = A± n± n±^T + B± (n± e3^T + e3 n±^T) + c± e3 e3^T,
Q+ = α [z,-y]^T [z,-y],         Q- = β [z,y]^T [z,y],
R± = (εs/2) [[1,∓1],[∓1,1]],
α = (εs/(2yz))(1 - s z/y),      β = (εs/(2yz))(1 + s z/y),
```

one has `P± ⪰ 0`, `Q± ⪰ 0`, `R± ⪰ 0`, and `P- ⪰ Δ e3 e3^T`.

**Lemma E.4 (certificate identity), Eq. (200).**  For every feasible block tuple
of Lemma E.1,

```
μ - x_c = <P+, S00 + C00> + <P-, S00 - C00>
        + <Q+, S_{0,-1} + K(r)> + <Q-, S_{0,-1} - K(r)>
        + <R+, S_{-1,0} + K(t)> + <R-, S_{-1,0} - K(t)>,
```

where `<·,·>` is the Hilbert–Schmidt inner product.  Together with Lemma E.3 and
the block positivity of Lemma E.1 this gives `x_c ≤ μ`.

**Modelling boundary.**  The certificate matrices are the explicit objects of
Eqs. (190)-(193) with the natural identification `Q± = α/β · [z,∓y]^T[z,∓y]`
(the typeset Eq. (192) is `α (z, -y) ⊗ (z, -y)`; the rank-one form is the one
used in the proof, cf. `⟨Q-, diag(b,0)⟩ = β z^2 b` in Eq. (202)).  The positivity
proof (Gram-matrix / rank-one arguments, Eq. (195)-(199)) and the expansion of
the six pairings (Eq. (200) proof) are not formalised; their statements live in
the branch history of this file.  The objects they operate on are recorded here
as definitions.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- Hilbert–Schmidt inner product `∑_{i,j} A_{ij} B_{ij}`. -/
def hs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- Outer product `v w^T`. -/
def outer4 (v w : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => v i * w j

/-- `e3 = (0,0,1,0)` of Eq. (190), p. 38. -/
def e3v : Fin 4 → ℝ := ![0, 0, 1, 0]

/-- `n± = (1, ∓s/μ, 0, ∓s^2/μ)` of Eq. (190), p. 38; `c = 1` is `n+`,
`c = -1` is `n-`. -/
def nvec (ε μ c : ℝ) : Fin 4 → ℝ := ![1, -c * s ε / μ, 0, -c * (s ε) ^ 2 / μ]

/-- `A± = μ(1 ∓ μ)/2` of Eq. (191), p. 38 (`c = 1` for `+`, `c = -1` for `-`). -/
def Acoef (μ c : ℝ) : ℝ := μ * (1 - c * μ) / 2

/-- `B± = s(μ ∓ 1)/2` of Eq. (191), p. 38. -/
def Bcoef (ε μ c : ℝ) : ℝ := s ε * (μ - c) / 2

/-- `c±` of Eq. (191), p. 38: `c+ = s^2(1-μ)/(2μ)`, `c- = s^2(1+μ)/(2μ) + Δ`. -/
def Ccoef (ε μ Δ c : ℝ) : ℝ :=
  if c = 1 then (s ε) ^ 2 * (1 - μ) / (2 * μ)
  else (s ε) ^ 2 * (1 + μ) / (2 * μ) + Δ

/-- The four-dimensional certificate block built from the signed rank-one terms of Eq. (190). -/
noncomputable def Pmat (ε μ Δ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Acoef μ c • outer4 (nvec ε μ c) (nvec ε μ c)
    + Bcoef ε μ c • (outer4 (nvec ε μ c) e3v + outer4 e3v (nvec ε μ c))
    + Ccoef ε μ Δ c • outer4 e3v e3v

/-- `α = (εs/(2yz))(1 - s z/y)` of Eq. (193), p. 38. -/
def alphaQ (ε sε z y : ℝ) : ℝ := ε * sε / (2 * y * z) * (1 - sε * z / y)

/-- `β = (εs/(2yz))(1 + s z/y)` of Eq. (193), p. 38. -/
def betaQ (ε sε z y : ℝ) : ℝ := ε * sε / (2 * y * z) * (1 + sε * z / y)

/-- The two-dimensional certificate block with the signed coefficient of Eq. (193). -/
noncomputable def Qmat (ε sε z y c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (if c = 1 then alphaQ ε sε z y else betaQ ε sε z y)
    • !![z ^ 2, -c * z * y; -c * z * y, y ^ 2]

/-- The signed two-dimensional remainder block of the positivity certificate. -/
noncomputable def Rmat (ε sε c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (ε * sε / 2) • !![1, -c; -c, 1]

end Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceCor42Spectral — Corollary 4.2 (spectral expression for the fixed-order optimum)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Corollary 4.2,
p. 14 (txt lines 688-712), Eqs. (63)-(66).

**Statement.**  For `0 < ε < 1` let `s = sqrt (1 - ε)` and

```
H_ε = [[0,0,s,0],[0,0,0,s^2],[s,0,0,εs],[0,s^2,εs,εs]].
```

Then `mu_MISC,seq (N^ε, N^ε) = λ_max(H_ε)`, hence
`D^Seq_MISC = (1 - λ_max(H_ε))/2`.  Equivalently `mu_MISC,seq` is the largest
real root of `p_ε(μ) = (μ^2 - s^2)(μ^2 - ε s μ - s^4) - ε^2 s^2 μ^2`.

**Paper proof.**  The fixed-order variational problem of Proposition 4.1 is
rewritten as a matrix Rayleigh quotient for `H_ε`; the maximiser of `F_ε` is the
top eigenvector, so the maximum equals `λ_max(H_ε)`.  A determinant expansion of
`μ I - H_ε` gives `p_ε(μ)`, whose largest real root is `λ_max(H_ε)`.

**Modelling boundary.**  `Hmat` and `pEps` are the explicit objects of
Eqs. (63) and (66) (in `Model/AmplitudeDamping.lean`).  The eigenvalue/
eigenvector identification `muSeq ε = λ_max(H_ε)` and the determinant expansion
`det (μ I - H_ε) = p_ε(μ)` are not rebuilt here; their statements live in the
branch history of this file.  What is recorded is the error-bridge Eq. (65).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- Fixed arXiv:2609.08639v1, Corollary 4.2, Eq. (65), p. 14: the fixed-order
error in spectral form `(1 - λ_max(H_ε))/2`, with `muSeq ε` in place of
`λ_max(H_ε)` per Eq. (64); the eigenvalue identification itself is not rebuilt
(see the modelling boundary above). -/
theorem source_cor_42_error_spectral (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    Dseq ε = (1 - muSeq ε) / 2 := rfl

end Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder

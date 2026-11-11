/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 3 — large-degree limits of the Bethe-lattice Gram matrices

Fixed source: arXiv:2505.07929v2, Proposition 3, Appendix VI, PDF pp. 30–31,
eqs. (B17)–(B20).

On the depth-`Δ` Bethe lattice of degree `D`, the QAOA dynamics induces the symmetric and
Hermitian Gram matrices `G^(sym,Δ,D)` and `G^(herm,Δ,D)`.  As `D → ∞` with `p`, `Δ` and
the angles `γ, β` fixed, these matrices converge entrywise (eqs. (B17), (B18)) to limit
matrices `G^(sym,Δ)` and `G^(herm,Δ)` that are identified with the depth-`Δ` correlation
matrix `G^(Δ)` of eq. (130) by

  `G^(sym,Δ)_{j,k} = G^(Δ)_{-j,-k}`  and  `G^(herm,Δ)_{j,k} = G^(Δ)_{j,-k}`  (B19, B20).

The tree recursion that defines `G^(sym,Δ,D)` is not modelled here (it requires the random
regular tree combinatorics of Appendix VI); the two matrix families are carried as the
data `BetheData.GsymD`, `BetheData.GhermD` of an abstract `BetheData`, exactly as the paper
uses them in Proposition 3.
The convergence claim is not formalized: `BetheData` stores `GsymD`, `GhermD` and `G` as
independent arbitrary data (the Bethe-tree recursion is not modelled), so neither
convergence nor the block identifications follow (a non-convergent `GsymD` is a
counterexample).  The `BetheData` structure is kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Filter Topology
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.GMatrixLimit

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

/-- The correlation-matrix data of Proposition 3 (arXiv:2505.07929v2, Appendix VI,
eqs. (B17)–(B20)): for every degree `D` the depth-`Δ` symmetric and Hermitian Gram
matrices of the Bethe lattice, and the depth-`Δ` correlation matrix `G^(Δ)` of eq. (130)
in the `(2p+1) × (2p+1)` index layout of eq. (121). -/
structure BetheData (p : ℕ) where
  /-- `G^(sym,Δ,D)` for each degree `D` (eqs. (B13)–(B15)). -/
  GsymD : ℕ → Matrix (Fin p) (Fin p) ℂ
  /-- `G^(herm,Δ,D)` for each degree `D` (eqs. (B13)–(B16)). -/
  GhermD : ℕ → Matrix (Fin p) (Fin p) ℂ
  /-- The depth-`Δ` correlation matrix `G^(Δ)` of eq. (130), in the index layout of
  `posIdx`/`negIdx` (eq. (121)). -/
  G : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℂ


end Qatlib.Papers.SpinBosonQAOA26.MainResults.GMatrixLimit

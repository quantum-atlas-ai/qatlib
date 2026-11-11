/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor-network / q-state-model vocabulary (TensorNetwork08)

Paper: *Quantum computation and the evaluation of tensor networks*
(Itai Arad, Zephyr Landau), arXiv:0805.0040.

This file fixes the small amount of vocabulary shared by the paper-layer theorems:
the partition function of a `q`-state model on a finite graph (Eq. (1)/(37)), the
partition function of a `q`-state *difference* model (Sec. 5.2), the value of a
fully contracted tensor network as a sum over edge labelings (Def. 2.2 / Eq. (1)),
and the additive-approximation scale `Δ = ∏_v ‖O_v‖` of Theorem 3.4 (Eq. (13)).

A graph is presented by an oriented edge type `E` together with endpoint maps
`src dst : E → V`; undirected graphs are oriented arbitrarily.  The colour type
`C` is left abstract (instances `C = Fin q` or `C = ZMod q` recover the paper).
-/

namespace Qatlib.Papers.TensorNetwork08.MainResults.StatModel

open scoped Classical BigOperators

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

/-- Value of a fully contracted tensor network with vertex set `W`, edge set `E`
and colours `C`: the sum over all edge labelings `l : E → C` of the product of the
vertex tensors `tensor w l` (Def. 2.2, Eq. (1)).  Each `tensor w` reads the labels
of the edges incident to `w` out of the global labeling `l`. -/
noncomputable def tensorNetworkValue {W : Type*} [Fintype W]
    (tensor : W → (E → C) → ℂ) : ℂ :=
  ∑ l : E → C, ∏ w : W, tensor w l

/-- The partition function `Z_G(β) = ∑_σ ∏_e exp(-β · h_e(σ_{src e}, σ_{dst e}))`
of a `q`-state statistical model on a finite graph (Eq. (37)). -/
noncomputable def partitionFunction (src dst : E → V) (h : E → C → C → ℂ) (β : ℂ) : ℂ :=
  ∑ σ : V → C, ∏ e : E, Complex.exp (-(β * h e (σ (src e)) (σ (dst e))))

/-- The partition function of a `q`-state *difference* model: the coupling depends
only on the difference `σ_{src e} - σ_{dst e}` of the two endpoint colours
(Sec. 5.2, Eq. (41)). -/
noncomputable def differencePartitionFunction [AddCommGroup C]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ) : ℂ :=
  ∑ σ : V → C, ∏ e : E, Complex.exp (-(β * h e (σ (src e) - σ (dst e))))

/-- The additive-approximation scale `Δ = ∏_{v ∈ V} ‖O_v‖` of Theorem 3.4,
Eq. (13), where `O_v` are the swallowing operators of Def. 3.2. -/
noncomputable def approximationScale (norm : V → ℝ) : ℝ := ∏ v : V, norm v

/-- A `q`-state difference model is *consistent* on `G` if it is the coboundary of a
vertex colouring: there is `σ : V → C` with `δ e = σ (src e) - σ (dst e)`. -/
def IsConsistentLabeling [AddCommGroup C] (src dst : E → V) (δ : E → C) : Prop :=
  ∃ σ : V → C, ∀ e : E, δ e = σ (src e) - σ (dst e)

/-- The `q`-state Potts edge weight `e^{-β h(δ)}` written as a function of the
difference `δ`: it is `exp (β J)` when the two colours agree and `1` otherwise
(Sec. 5.5, used in Corollary 5.11). -/
noncomputable def pottsEdgeWeight (β J : ℝ) {C : Type*} [Zero C] [DecidableEq C]
    (δ : C) : ℝ := if δ = 0 then Real.exp (β * J) else 1

end Qatlib.Papers.TensorNetwork08.MainResults.StatModel

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-!
# Corollary 4.2 — tensor-network characterization of BQP

Paper: *Quantum computation and the evaluation of tensor networks*
(Arad, Landau), arXiv:0805.0040, Section 4.3, Corollary 4.2, Eqs. (25)–(26), p. 15.

Corollary 4.2: *a decision problem is in BQP if and only if there is an efficient classical
transformation mapping each instance `x` to a tensor network `T_x(G_x, M_x)` (bounded `q`,
max degree `d`) and a bubbling `B_x` such that*

  `x` is YES  ⇒  `|T_x|/Δ_x ≥ 2/poly(|x|)`   (25)
  `x` is NO   ⇒  `|T_x|/Δ_x ≤ 1/poly(|x|)`   (26)

with `Δ_x` as in Theorem 3.4.  The "if" direction follows from Theorem 3.4 (distinguish the
two ratio regimes by additive approximation), the "only if" from the Fig. 6 circuit-to-network
construction.

Quantum circuits and BQP are not modelled here; the corollary is recorded as the
biconditional over opaque predicates `InBQP` and `HasTensorNetworkEncoding`, with the two
directions of the paper's proof taken as hypotheses.  The logical skeleton is proved, the
complexity content is not formalised.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor42

/-- **Corollary 4.2 (schematic).**  If every BQP instance admits the tensor-network encoding
(25)–(26) (`hforward`, the Fig. 6 construction) and, conversely, every encoded instance is in
BQP (`hbackward`, via Theorem 3.4), then a decision problem is in BQP iff it admits such an
efficient tensor-network encoding. -/
theorem corollary4_2_completeness
    (Instance : Type)
    (InBQP HasTensorNetworkEncoding : Instance → Prop)
    (hforward : ∀ x, InBQP x → HasTensorNetworkEncoding x)
    (hbackward : ∀ x, HasTensorNetworkEncoding x → InBQP x) :
    ∀ x, InBQP x ↔ HasTensorNetworkEncoding x :=
  fun x => ⟨hforward x, hbackward x⟩

end Qatlib.Papers.TensorNetwork08.MainResults.Cor42

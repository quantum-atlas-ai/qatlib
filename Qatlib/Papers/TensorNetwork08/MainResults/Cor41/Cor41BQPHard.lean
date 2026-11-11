/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-!
# Corollary 4.1 — BQP-hardness of the additive tensor-network approximation

Paper: *Quantum computation and the evaluation of tensor networks*
(Arad, Landau), arXiv:0805.0040, Section 4.2, Corollary 4.1, pp. 13–14.

Corollary 4.1: *there exist families of tensor networks for which the additive
approximation of Theorem 3.4 is BQP-hard; in particular all families that correspond to
families of universal quantum circuits by the Fig. 6 construction.*

The Fig. 6 construction maps a universal circuit `Q` to a tensor network with value
`⟨0|U|0⟩ = p0` and approximation scale `Δ = 1` (Eqs. (22)–(24)); distinguishing the BQP
promise `p0 ≤ 1/3` vs `p0 ≥ 2/3` then reduces to additive approximation.  Neither quantum
circuits nor the complexity class BQP are modelled in this library, so the corollary is
recorded over two opaque family predicates `FromUniversalCircuit` and `BQPHard`, with the
paper's two ingredients (a universal-circuit family exists, and every such family is
BQP-hard) taken as hypotheses.  The logical skeleton is proved; the complexity-theoretic
content is not formalised.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor41

/-- **Corollary 4.1 (schematic).**  Given that every tensor-network family arising from a
universal quantum circuit is BQP-hard (`hconstruction`, the content of Eqs. (22)–(24) and
the Fig. 6 reduction) and that such a family exists (`hfamily`), there is a family whose
additive approximation is BQP-hard. -/
theorem corollary4_1_bqp_hard
    (NetworkFamily : Type)
    (FromUniversalCircuit BQPHard : NetworkFamily → Prop)
    (hconstruction : ∀ f, FromUniversalCircuit f → BQPHard f)
    (hfamily : ∃ f, FromUniversalCircuit f) :
    ∃ f, BQPHard f := by
  obtain ⟨f, hf⟩ := hfamily
  exact ⟨f, hconstruction f hf⟩

end Qatlib.Papers.TensorNetwork08.MainResults.Cor41

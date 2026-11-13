/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Detectability of Pauli group influence (Lemma 2.2)

Paper: arXiv:2608.18839v3, Lemma 2.2 (page 5 of the PDF) and its proof in
Appendix A.1:

> Consider a mixed state `ρ` with Pauli decomposition `{α_Q}_{Q∈𝒬}`.  Let
> `L_P = Σ_{Q◁P} 3^{w(Q)} α_Q²` and `L = Σ_{Q∈𝒬} α_Q²`.  Then there exists
> `i ∈ [N]` such that
> `Pr[L_P ≥ 3^{i-2} L] ≥ 3^{-i}/N`,
> where `P ∼ u[{X,Y,Z}^{⊗N}]`.

The Pauli vocabulary (`pauliMatches`, `pauliWeight`, `pauliInfluence`,
`pauliNormSq`) lives in `Model/SourceModel.lean`; the quoted statement uses the
cardinality form of the uniform probability, `#(filter …)/3^N`, and the
equivalent threshold `(3^i/9)·L = 3^{i-2}·L`.

## Mathematical background and scope

* Fixed source: arXiv:2608.18839v3, Lemma 2.2, proof in Appendix A.1 via
  Lemma A.1 (Levin's work-investment strategy).
* Proof outline (all finite, no probability spaces needed):
  1. Fiber counting: for every `Q ≠ Id`, exactly `3^{N-w(Q)}` of the `3^N`
     bases satisfy `Q ◁ P` (each support coordinate is forced to `Q i`, the
     complement is free).  Hence
     `Σ_P L_P = Σ_Q 3^{w(Q)} α_Q² · 3^{N-w(Q)} = 3^N · L`, i.e. the uniform
     mean of `L_P` is `L`.
  2. Levin's lemma: for `f ≥ 0` on `3^N` equally likely points with mean `≥ µ`,
     some level `i ∈ [1,N]` has `Pr[f ≥ 3^{i-2}µ] ≥ 3^{-i}/N`.  Proof by
     contradiction: if all counts `c_i = #{f ≥ 3^{i-2}µ}` satisfied
     `c_i < 3^{N-i}/N`, then `c_N = 0`, so `f < 3^{N-2}µ` everywhere; binning
     each point into the interval `[3^{i-2}µ, 3^{i-1}µ)` and telescoping gives
     `Σ_P f < (µ/3)3^N + Σ_{i=1}^{N-1} 2·3^{i-2}µ·c_i
        < µ3^{N-2}(3 + 2) = 5µ3^{N-2} < 9µ3^{N-2} = 3^N µ`,
     contradicting the mean identity.
  3. Apply step 2 with `f = L_P` and `µ = L`; `f ≥ 0` is immediate from the
     squares, and step 1 gives the mean hypothesis.
* The combinatorial ingredients are the fiber equivalence
  `{P // Q ◁ P} ≃ ({i // i ∉ pauliSupport Q} → Fin 3)` and the cardinality
  computation `card {i // i ∉ supp Q} = N - w(Q)`, followed by binning and
  telescoping over the largest threshold below each `f P`. The fiber
  equivalence fixes coordinates in the support and leaves the others free;
  equality of cardinalities gives the count. The contradiction in Levin's
  argument ends with the geometric comparison `5·3^{N-2} < 3^N`.
  (The identical argument is carried out for Pauli bases in Appendix A.1.)
* Scope note: this module defines the literal influence and coefficient norm,
  including the identity observable, and proves their nonnegativity. The fiber
  count, telescoping argument, and detectability theorem are outside the scope
  of this file.
* Related definitions: `SourceModel.pauliInfluence`, `pauliNormSq`,
  `pauliMatches`, `pauliWeight`, `pauliSupport`, and `pauliEmbed`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.Influence

open scoped BigOperators

/-- Paper Definition 2.1, literal form: `L_P = Σ_{Q◁P} 3^{w(Q)} α_Q²`, summing
over *all* Pauli observables `Q` (the identity term `α_Id²` contributes to every
`L_P`, as in the paper where `α_Id` is a fixed normalization constant). -/
noncomputable def pauliInfluenceAll {N : ℕ} (α : PauliObservable N → ℝ)
    (P : PauliBasis N) : ℝ := by
  classical
  exact ∑ Q : PauliObservable N,
    if pauliMatches Q P then (3 : ℝ) ^ pauliWeight Q * (α Q) ^ 2 else 0

/-- Paper Lemma 2.2, literal form: `L = Σ_{Q∈𝒬} α_Q²`, summing over all Pauli
observables (including the identity). -/
noncomputable def pauliNormSqAll {N : ℕ} (α : PauliObservable N → ℝ) : ℝ :=
  ∑ Q : PauliObservable N, (α Q) ^ 2

/-- The literal Pauli influence is nonnegative for every coefficient function. -/
theorem pauliInfluenceAll_nonneg {N : ℕ} (α : PauliObservable N → ℝ)
    (P : PauliBasis N) : 0 ≤ pauliInfluenceAll α P := by
  unfold pauliInfluenceAll
  classical
  refine Finset.sum_nonneg (fun Q _ => ?_)
  split_ifs <;> positivity

/-- The literal coefficient norm `L = Σ_{Q∈𝒬} α_Q²` is nonnegative. -/
theorem pauliNormSqAll_nonneg {N : ℕ} (α : PauliObservable N → ℝ) :
    0 ≤ pauliNormSqAll α := by
  unfold pauliNormSqAll
  classical
  refine Finset.sum_nonneg (fun Q _ => ?_)
  positivity


end Qatlib.Papers.MixednessTest26.MainResults.Influence

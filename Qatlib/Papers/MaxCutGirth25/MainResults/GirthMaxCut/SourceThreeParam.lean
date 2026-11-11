/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut.SourceIndependence
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The three-parameter QAOA ansatz and the independence-ratio bound
(Sec. 7, Eq. (26)--(28), Table 2, p. 11--12)

Fixed version: arXiv:2503.12789v2 (2026-01-27), Farhi--Gutmann--Ranard--Villalonga.

The paper considers a variant of the QAOA whose driver Hamiltonian at each layer
may differ from the MaxCut cost function, with parameters `(γ, γ′, β)` per layer,
hence `3p` real parameters in total (Eq. (26)--(28)).  Two special sub-families
are:

* `γ′ = 0`: the driver is the MaxCut cost function, so the construction reduces to
  the MaxCut-driven ansatz of the earlier sections;
* `γ / γ′` fixed to the constant of Eq. (26): the driver coincides with the local
  MIS objective.

The paper's monotonicity claim is: optimising over the larger `3p`-parameter
family is at least as good as optimising over either restricted family.  Because
the parameter spaces are continuous, the optimum is a supremum over a set of real
values (`optimalValue`), and the claim is the order-theoretic lemma
`optimalValue_mono` plus the two explicit embeddings `embedMaxCutDriver` and
`embedMatchingDriver`.  The numerical Table 2 values are recorded in
`table2ThreeParam17` and `table2TwoParam17`; the headline fact `0.4228 ≤ 0.4244`
is proved.

The quantum expectation for the three-parameter ansatz itself (the analogue of
Eq. (7)) is not formalised; only the optimisation-set inclusion argument that the
paper states in prose is.  No `sorry` is used in this module.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

/-- The optimal value of a real objective over a set of achievable values, the
supremum of the objective over the parameter space (Eq. (28) discussion,
"optimize over all γs, γ′s and βs", p. 12). -/
noncomputable def optimalValue (S : Set ℝ) : ℝ := sSup S

/-- Every achievable value is at most the optimum (when the objective is bounded
above). -/
theorem le_optimalValue {S : Set ℝ} (hbdd : BddAbove S) {x : ℝ} (hx : x ∈ S) :
    x ≤ optimalValue S :=
  le_csSup hbdd hx

/-- **Paper Sec. 7, p. 12: optimising over a larger parameter set cannot hurt.**
If the achievable set of the restricted family is contained in that of the full
family, then the restricted optimum is at most the full optimum.  This is the
order-theoretic content of the sentence "if we optimize over all `γ`s and `γ′`s
and `β`s we do at least as well as using the MaxCut cost function as the driver or
the local MIS cost function as the driver" (p. 12). -/
theorem optimalValue_mono {S T : Set ℝ} (hST : S ⊆ T)
    (hSne : S.Nonempty) (hTbdd : BddAbove T) :
    optimalValue S ≤ optimalValue T :=
  csSup_le_csSup hTbdd hSne hST

/-- If the objective of a restricted parameter family is the full objective along
an embedding `e`, then the restricted optimum is at most the full optimum. -/
theorem optimalValue_mono_of_embedding {ι κ : Type*}
    (objective : κ → ℝ) (restricted : ι → ℝ) (embed : ι → κ)
    (hrestrict : ∀ i, restricted i = objective (embed i))
    (hne : (Set.range restricted).Nonempty)
    (hbdd : BddAbove (Set.range objective)) :
    optimalValue (Set.range restricted) ≤ optimalValue (Set.range objective) := by
  refine optimalValue_mono ?_ hne hbdd
  rintro x ⟨i, rfl⟩
  exact ⟨embed i, (hrestrict i).symm⟩

/-- The `3p`-parameter ansatz of Eq. (26)--(28): per layer a triple
`(γ, γ′, β)`, so the parameter type is `Fin p → ℝ × ℝ × ℝ`. -/
abbrev ThreeParam (p : ℕ) := Fin p → ℝ × ℝ × ℝ

/-- The two-parameter (`γ, β`) family of the earlier sections: `Fin p → ℝ × ℝ`. -/
abbrev TwoParam (p : ℕ) := Fin p → ℝ × ℝ

/-- The special sub-family with `γ′ = 0` per layer: the MaxCut cost function is the
driver (p. 12). -/
def embedMaxCutDriver {p : ℕ} (θ : TwoParam p) : ThreeParam p :=
  fun i => ((θ i).1, (0 : ℝ), (θ i).2)

/-- The special sub-family where `γ / γ′` is a fixed constant `r`: the driver
coincides with the local MIS objective (Eq. (26), p. 12). -/
def embedMatchingDriver {p : ℕ} (r : ℝ) (θ : TwoParam p) : ThreeParam p :=
  fun i => (r * (θ i).1, (θ i).1, (θ i).2)

/-- **Paper Sec. 7, p. 12.** Optimising the `3p`-parameter objective is at least as
good as optimising the MaxCut-driven (`γ′ = 0`) sub-family. -/
theorem three_param_at_least_maxcut_driver {p : ℕ}
    (objective : ThreeParam p → ℝ) (restricted : TwoParam p → ℝ)
    (hrestrict : ∀ θ, restricted θ = objective (embedMaxCutDriver θ))
    (hne : (Set.range restricted).Nonempty)
    (hbdd : BddAbove (Set.range objective)) :
    optimalValue (Set.range restricted) ≤ optimalValue (Set.range objective) :=
  optimalValue_mono_of_embedding objective restricted embedMaxCutDriver hrestrict hne hbdd

/-- **Paper Sec. 7, p. 12.** Optimising the `3p`-parameter objective is at least as
good as optimising the constant-ratio (`γ / γ′ = r`) sub-family. -/
theorem three_param_at_least_matching_driver {p : ℕ} (r : ℝ)
    (objective : ThreeParam p → ℝ) (restricted : TwoParam p → ℝ)
    (hrestrict : ∀ θ, restricted θ = objective (embedMatchingDriver r θ))
    (hne : (Set.range restricted).Nonempty)
    (hbdd : BddAbove (Set.range objective)) :
    optimalValue (Set.range restricted) ≤ optimalValue (Set.range objective) :=
  optimalValue_mono_of_embedding objective restricted (embedMatchingDriver r) hrestrict hne hbdd

/-- Table 2, p. 12: the two-parameter (`γ, β`) independence-ratio value at `p = 17`
is `0.4228`, the same value as the girth-36 bound of Eq. (24). -/
noncomputable def table2TwoParam17 : ℝ := 4228 / 10000

/-- Table 2, p. 12: the three-parameter value at `p = 17` is `0.4244`, the largest
entry of the table. -/
noncomputable def table2ThreeParam17 : ℝ := 4244 / 10000

/-- Table 2, p. 12: the three-parameter bound at `p = 17` is at least the
two-parameter bound at `p = 17` (`0.4228 ≤ 0.4244`), illustrating the monotonicity
of `three_param_at_least_maxcut_driver`. -/
theorem table2_three_ge_two_at_17 : table2TwoParam17 ≤ table2ThreeParam17 := by
  unfold table2TwoParam17 table2ThreeParam17
  norm_num

/-- Table 2, p. 12: the three-parameter value at `p = 17` is `0.4244`, quoted as
the best entry of the table. -/
theorem table2ThreeParam17_eq : table2ThreeParam17 = (4244 : ℝ) / 10000 := rfl

end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

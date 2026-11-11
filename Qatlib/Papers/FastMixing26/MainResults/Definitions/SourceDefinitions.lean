/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# FastMixing26.MainResults.Definitions — paper-level objects

Bergamaschi, *Fast mixing of all-to-all quantum systems at high temperatures*,
fixed arXiv:2606.26090v2 (PDF SHA-256 70f1cf62dfec60d72f2d721539a6ffc9447afb15b950de72411b8b3b06ed2b7a).

This file records the scalar/combinatorial objects that sections 3–5 of the paper attach
their estimates to:

* `InteractionGraph` — Definition 1.1 (all-to-all Hamiltonian data): a finite set of
  interaction terms `Γ`, uniform support size `k`, degree ≤ `d`, pairwise interaction
  strength ≤ `J`, and the interaction-term norm `‖h_e‖`.
* `InteractionGraph.supportOf` — Remark 3.3: the sites incident to a cluster `F ⊆ Γ`.
* `InteractionGraph.clusterProd` — the cluster weight `∏_{e∈F}(e^{c‖h_e‖} − 1)` of
  Lemma 3.4 (32), used with `c = 2|z|` for the complex-time expansion and with
  `c = 4|z|` for pairwise correlations (Corollary 3.8 (36)).
* `supOver` — the "max over a finite family" shape used in Definitions 3.5/3.7.

Operator-level content (the actual `e^{izH}Ae^{-izH}` and the KMS inner product) is
attached in the individual claim files; here we only keep the combinatorial skeleton so
that the local estimates of Section 3 can be stated and proved independently.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.FastMixing26.MainResults

/-- Definition 1.1 (All-to-all Hamiltonians), reified as abstract data.

`E` is the index type of interaction terms (the paper's `Γ`), `supp e` is
`supp(h_e) ⊆ [n]`, `hnorm e = ‖h_e‖`. `k` is the uniform locality (every term has
support size `k`), `d` bounds the number of terms incident to any site, and `J` bounds
the pairwise interaction strength `∑_{e ⊇ {u,v}} ‖h_e‖ ≤ J` (in particular each
`‖h_e‖ ≤ J`). -/
structure InteractionGraph (n : ℕ) (E : Type) [Fintype E] [DecidableEq E] where
  /-- Support `supp(h_e) ⊆ [n]` of each interaction term. -/
  supp : E → Finset (Fin n)
  /-- Uniform locality `k`. -/
  k : ℕ
  /-- `k ≥ 1`. -/
  hk : 0 < k
  /-- Degree bound `d`. -/
  d : ℕ
  /-- Maximum pairwise interaction strength `J`. -/
  J : ℝ
  /-- `J ≥ 0`. -/
  hJ : 0 ≤ J
  /-- The norm `‖h_e‖` of each interaction term. -/
  hnorm : E → ℝ
  /-- Norms are nonnegative. -/
  hnorm_nonneg : ∀ e, 0 ≤ hnorm e
  /-- Locality: `|supp(h_e)| = k`. -/
  supp_card : ∀ e, (supp e).card = k
  /-- Degree: each site is incident to at most `d` terms. -/
  degree : ∀ u : Fin n, (Finset.univ.filter (fun e => u ∈ supp e)).card ≤ d
  /-- Every term norm is bounded by the pairwise strength `J`. -/
  hnorm_le_J : ∀ e, hnorm e ≤ J
  /-- Pairwise interaction strength bound (Definition 1.1). -/
  pair_strength : ∀ u v : Fin n, u ≠ v →
    ∑ e ∈ Finset.univ.filter (fun e => u ∈ supp e ∧ v ∈ supp e), hnorm e ≤ J

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- Remark 3.3: the support of a cluster `F ⊆ Γ` is the set of distinct sites incident
on some term of `F`. -/
def InteractionGraph.supportOf (g : InteractionGraph n E) (F : Finset E) : Finset (Fin n) :=
  F.biUnion g.supp

/-- The cluster weight `∏_{e ∈ F} (e^{c‖h_e‖} − 1)` appearing in Lemma 3.4 (32) and
Corollary 3.8 (36). `c = 2|z|` for the complex-time expansion, `c = 4|z|` for
correlations. -/
def InteractionGraph.clusterProd (g : InteractionGraph n E) (c : ℝ) (F : Finset E) : ℝ :=
  ∏ e ∈ F, (Real.exp (c * g.hnorm e) - 1)

/-- Each cluster weight is nonnegative. -/
lemma InteractionGraph.clusterProd_nonneg (g : InteractionGraph n E) (c : ℝ) (hc : 0 ≤ c)
    (F : Finset E) : 0 ≤ g.clusterProd c F := by
  unfold InteractionGraph.clusterProd
  refine Finset.prod_nonneg (fun e _ => ?_)
  have h1 : Real.exp 0 ≤ Real.exp (c * g.hnorm e) :=
    Real.exp_le_exp.mpr (mul_nonneg hc (g.hnorm_nonneg e))
  simpa using h1

/-- The cluster weight is monotone in the exponential rate `c ≥ 0`. -/
lemma InteractionGraph.clusterProd_mono (g : InteractionGraph n E) {c c' : ℝ}
    (hc : 0 ≤ c) (hcc : c ≤ c') (F : Finset E) :
    g.clusterProd c F ≤ g.clusterProd c' F := by
  unfold InteractionGraph.clusterProd
  refine Finset.prod_le_prod₀ (fun e _ => ?_) (fun e _ => ?_)
  · have h1 : Real.exp 0 ≤ Real.exp (c * g.hnorm e) :=
      Real.exp_le_exp.mpr (mul_nonneg hc (g.hnorm_nonneg e))
    simpa using h1
  · have hle : c * g.hnorm e ≤ c' * g.hnorm e :=
      mul_le_mul_of_nonneg_right hcc (g.hnorm_nonneg e)
    have := Real.exp_le_exp.mpr hle
    linarith

/-- The "maximum over a finite family" used in Definitions 3.5 and 3.7. -/
def supOver {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- Every member of the family is bounded by its supremum. -/
lemma le_supOver {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (a : ι) :
    f a ≤ supOver f := by
  rw [supOver]
  exact Finset.le_sup' f (Finset.mem_univ a)

/-- A uniform bound bounds the supremum. -/
lemma supOver_le {ι : Type} [Fintype ι] [Nonempty ι] {f : ι → ℝ} {r : ℝ}
    (h : ∀ a, f a ≤ r) : supOver f ≤ r := by
  rw [supOver]
  exact Finset.sup'_le Finset.univ_nonempty f (fun a _ => h a)

end Qatlib.Papers.FastMixing26.MainResults

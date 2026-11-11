/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastMixing26.MainResults.Definitions.SourceDefinitions
import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# FastMixing26.MainResults.ClusterExpansion — Section 3

Bergamaschi, *Fast mixing of all-to-all quantum systems at high temperatures*,
fixed arXiv:2606.26090v2 (PDF SHA-256 70f1cf62dfec60d72f2d721539a6ffc9447afb15b950de72411b8b3b06ed2b7a).

Source moments covered here:

* Corollary 3.6 (34), p. 13: `conv_β ≤ max_i Σ_{F∋i} ∏_{e∈F}(e^{2|β|‖h_e‖}−1)` (sup step).
* Corollary 3.8 (36), p. 13: `Σ_{j≠i} corr_β(i,j) ≤ 2 Σ_{F∋i} |supp(F)| ∏_{e∈F}(e^{4|β|‖h_e‖}−1)`
  (per-pair input as hypothesis; the summation core `sum_corr_bound` is proved).
* Lemma 3.12 (58), p. 16: `max_{e} Σ_{e'∩e≠∅}(e^{4|z|‖h_{e'}‖}−1) ≤ kd(e^{4|z|J}−1)` (fully proved).

The cluster expansion itself (Lemma 3.4, c003) and the resummed tree count
(Lemma 3.10, c006) are not formalized; their statements are preserved in this branch's
history.  `source_lemma_3_4_norm` proves the norm consequence of the (hypothetical)
deposition.

The operator-level cluster expansion is kept abstract (`complexTimeEvolve` plus an explicit
`SingleSitePauliFamily`), since the paper works in a concrete Pauli product basis; the
scalar locality estimates (which are what Sections 4–5 consume) are formalized and, where
elementary, proved.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Finset
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.FastMixing26.MainResults.ClusterExpansion

open Qatlib.Papers.FastMixing26.MainResults

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- `A(z) = e^{izH} A e^{-izH}`: the complex-time evolution of Lemma 3.4 (32). -/
noncomputable def complexTimeEvolve {D : ℕ} (H A : Operator D) (z : ℂ) : Operator D :=
  NormedSpace.exp ((z * Complex.I) • H) * A * NormedSpace.exp ((-(z * Complex.I)) • H)

/-- Norm consequence of Lemma 3.4 (32), pp. 12–13: given a cluster decomposition of
`A(z) − A` with per-cluster bounds `‖AF F‖ ≤ clusterProd (2‖z‖) F` supported on the
clusters through site `i`, the triangle inequality gives the norm bound. -/
theorem source_lemma_3_4_norm {D : ℕ} (g : InteractionGraph n E) (CC : Finset (Finset E))
    (H A : Operator D) (i : Fin n) (z : ℂ)
    (hdecomp : ∃ AF : Finset E → Operator D,
      (∀ F, ‖AF F‖ ≤ g.clusterProd (2 * ‖z‖) F) ∧
      complexTimeEvolve H A z - A =
        ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F), AF F) :
    ‖complexTimeEvolve H A z - A‖
      ≤ ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F),
          g.clusterProd (2 * ‖z‖) F := by
  obtain ⟨AF, hAF, hsum⟩ := hdecomp
  rw [hsum]
  calc ‖∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F), AF F‖
      ≤ ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F), ‖AF F‖ :=
        norm_sum_le _ _
    _ ≤ ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F),
          g.clusterProd (2 * ‖z‖) F :=
        Finset.sum_le_sum (fun F _ => hAF F)

/-- Corollary 3.6 (34), p. 13, fixed arXiv:2606.26090v2. In the context of Lemma 3.4,

`conv_β = max_{a ∈ S^1_[n]} sup_{|z|≤β} ‖A_a(z) − A_a‖ ≤ max_{i∈[n]} Σ_{F∋i} ∏_{e∈F}(e^{2|β|‖h_e‖}−1)`.

Formalised with `dev a` the inner `sup_{|z|≤β}‖A_a(z) − A_a‖` and `siteOf a` the site of
`A_a`; the hypothesis is the pointwise Lemma 3.4 bound, and the conclusion is the maximum
bound. Proved by `sup'_le`/`le_sup'` and the triangle inequality. -/
theorem source_corollary_3_6 [NeZero n] (g : InteractionGraph n E) (CC : Finset (Finset E))
    (β : ℝ) (hβ : 0 ≤ β) {P : Type} [Fintype P] [Nonempty P]
    (siteOf : P → Fin n) (dev : P → ℝ)
    (hdev : ∀ a, dev a
      ≤ ∑ F ∈ CC.filter (fun F => siteOf a ∈ g.supportOf F),
          g.clusterProd (2 * β) F) :
    supOver dev
      ≤ supOver (fun i : Fin n =>
          ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F), g.clusterProd (2 * β) F) := by
  apply supOver_le
  intro a
  exact (hdev a).trans (le_supOver
    (f := fun i : Fin n =>
      ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F), g.clusterProd (2 * β) F)
    (siteOf a))

/-- Combinatorial summation step behind Corollary 3.8 (36): summing the per-pair bound
`corr(i,j) ≤ 2 Σ_{F ∋ i, j∈supp(F)} ∏(…)` over `j ≠ i` reindexes as a sum over clusters
`F ∋ i`, and the number of sites `j ≠ i` incident to `F` is at most `|supp(F)|`. -/
lemma sum_corr_bound {A B : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (CC : Finset B) (i : A) (supp : B → Finset A) (c : B → ℝ) (hc : ∀ b, 0 ≤ c b)
    (corr : A → ℝ)
    (hcorr : ∀ j, j ≠ i →
      corr j ≤ 2 * ∑ b ∈ CC.filter (fun b => i ∈ supp b ∧ j ∈ supp b), c b) :
    ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), corr j
      ≤ 2 * ∑ b ∈ CC.filter (fun b => i ∈ supp b),
          ((supp b).card : ℝ) * c b := by
  classical
  set J : Finset A := Finset.univ.filter (fun j => j ≠ i) with hJ
  set B0 : Finset B := CC.filter (fun b => i ∈ supp b) with hB0
  have hUj : ∀ j, CC.filter (fun b => i ∈ supp b ∧ j ∈ supp b)
      = B0.filter (fun b => j ∈ supp b) := by
    intro j
    rw [hB0]
    rw [← Finset.filter_filter]
  have hstep1 : ∑ j ∈ J, corr j
      ≤ ∑ j ∈ J, 2 * ∑ b ∈ CC.filter
          (fun b => i ∈ supp b ∧ j ∈ supp b), c b := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact hcorr j (by simpa using (Finset.mem_filter.mp hj).2)
  have hstep2 : ∑ j ∈ J, 2 * (∑ b ∈ CC.filter
        (fun b => i ∈ supp b ∧ j ∈ supp b), c b)
      = 2 * ∑ j ∈ J, ∑ b ∈ CC.filter
          (fun b => i ∈ supp b ∧ j ∈ supp b), c b := by
    rw [Finset.mul_sum]
  have hswap : ∑ j ∈ J, ∑ b ∈ CC.filter
        (fun b => i ∈ supp b ∧ j ∈ supp b), c b
      = ∑ b ∈ B0, ((J.filter (fun j => j ∈ supp b)).card : ℝ) * c b := by
    have e1 : ∑ j ∈ J, ∑ b ∈ CC.filter
          (fun b => i ∈ supp b ∧ j ∈ supp b), c b
        = ∑ j ∈ J, ∑ b ∈ B0, (if j ∈ supp b then c b else 0) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hUj j, Finset.sum_filter]
    rw [e1]
    calc ∑ j ∈ J, ∑ b ∈ B0, (if j ∈ supp b then c b else 0)
        = ∑ b ∈ B0, ∑ j ∈ J, (if j ∈ supp b then c b else 0) :=
          Finset.sum_comm
      _ = ∑ b ∈ B0, ∑ j ∈ J.filter (fun j => j ∈ supp b), c b := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_filter (s := J) (p := fun j => j ∈ supp b)
            (f := fun _ => c b)]
      _ = ∑ b ∈ B0, ((J.filter (fun j => j ∈ supp b)).card : ℝ) * c b := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ∀ b, (J.filter (fun j => j ∈ supp b)).card ≤ (supp b).card := by
    intro b
    refine Finset.card_le_card (fun j hj => ?_)
    exact (Finset.mem_filter.mp hj).2
  have hstep3 : ∑ b ∈ B0, ((J.filter (fun j => j ∈ supp b)).card : ℝ) * c b
      ≤ ∑ b ∈ B0, ((supp b).card : ℝ) * c b := by
    refine Finset.sum_le_sum (fun b _ => ?_)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard b) (hc b)
  calc ∑ j ∈ J, corr j
      ≤ ∑ j ∈ J, 2 * (∑ b ∈ CC.filter
          (fun b => i ∈ supp b ∧ j ∈ supp b), c b) := hstep1
    _ = 2 * ∑ j ∈ J, ∑ b ∈ CC.filter
          (fun b => i ∈ supp b ∧ j ∈ supp b), c b := hstep2
    _ = 2 * ∑ b ∈ B0, ((J.filter (fun j => j ∈ supp b)).card : ℝ) * c b := by
        rw [hswap]
    _ ≤ 2 * ∑ b ∈ B0, ((supp b).card : ℝ) * c b := by
        exact mul_le_mul_of_nonneg_left hstep3 (by norm_num)

/-- Corollary 3.8 (36), p. 13, fixed arXiv:2606.26090v2. In the context of Lemma 3.4,

`Σ_{j≠i} corr_β(i,j) ≤ 2 Σ_{F∋i} |supp(F)| ∏_{e∈F}(e^{4|β|‖h_e‖}−1)`,

where `|supp(F)|` is the number of distinct sites incident on `F`. The per-pair input
`hpair` is the per-pair estimate obtained in the paper from the cluster expansion (the
argument between (36) and its proof); the summation is proved in `sum_corr_bound`. -/
theorem source_corollary_3_8 (g : InteractionGraph n E) (CC : Finset (Finset E))
    (β : ℝ) (hβ : 0 ≤ β) (corr : Fin n → Fin n → ℝ)
    (hpair : ∀ i j, i ≠ j →
      corr i j ≤ 2 * ∑ F ∈ CC.filter
          (fun F => i ∈ g.supportOf F ∧ j ∈ g.supportOf F),
          g.clusterProd (4 * β) F) :
    ∀ i : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), corr i j
        ≤ 2 * ∑ F ∈ CC.filter (fun F => i ∈ g.supportOf F),
            ((g.supportOf F).card : ℝ) * g.clusterProd (4 * β) F := by
  intro i
  simpa using sum_corr_bound (CC := CC) (i := i) (supp := g.supportOf)
    (c := fun F => g.clusterProd (4 * β) F)
    (hc := fun F => g.clusterProd_nonneg (4 * β) (by positivity) F)
    (corr := fun j => corr i j) (hcorr := fun j hj => hpair i j (Ne.symm hj))

/-- Lemma 3.12 (58), p. 16: the sum of `e^{4|z|‖h_e‖} − 1` over the edges intersecting a
fixed edge `e0` is at most `k·d·(e^{4|z|J} − 1)` — counting via `biUnion` over the sites
of `e0` and the degree bound, with `exp` monotonicity in `‖h_e‖ ≤ J`. -/
theorem source_lemma_3_12 (g : InteractionGraph n E) (z : ℂ) (e0 : E) :
    ∑ e ∈ Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty),
        (Real.exp (4 * ‖z‖ * g.hnorm e) - 1)
      ≤ ((g.k : ℝ) * (g.d : ℝ))
          * (Real.exp (4 * ‖z‖ * g.J) - 1) := by
  classical
  set c : ℝ := 4 * ‖z‖ with hcdef
  have hc : 0 ≤ c := by
    rw [hcdef]; positivity
  set B : ℝ := Real.exp (c * g.J) - 1 with hBdef
  have hB : 0 ≤ B := by
    have h1 : Real.exp 0 ≤ Real.exp (c * g.J) :=
      Real.exp_le_exp.mpr (mul_nonneg hc g.hJ)
    rw [hBdef]; simpa using sub_nonneg.mpr h1
  have hterm : ∀ e, Real.exp (c * g.hnorm e) - 1 ≤ B := by
    intro e
    have hle : c * g.hnorm e ≤ c * g.J :=
      mul_le_mul_of_nonneg_left (g.hnorm_le_J e) hc
    have hexp : Real.exp (c * g.hnorm e) ≤ Real.exp (c * g.J) :=
      Real.exp_le_exp.mpr hle
    rw [hBdef]; linarith
  have hcard : (Finset.univ.filter
      (fun e => (g.supp e ∩ g.supp e0).Nonempty)).card ≤ g.k * g.d := by
    have hsub : Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty) ⊆
        (g.supp e0).biUnion (fun u => Finset.univ.filter (fun e => u ∈ g.supp e)) := by
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨_, hne⟩ := he
      obtain ⟨u, hu⟩ := hne
      rw [Finset.mem_inter] at hu
      obtain ⟨hu_e, hu_e0⟩ := hu
      exact Finset.mem_biUnion.mpr ⟨u, hu_e0, by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ e, hu_e⟩⟩
    calc (Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty)).card
        ≤ ((g.supp e0).biUnion
            (fun u => Finset.univ.filter (fun e => u ∈ g.supp e))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ g.supp e0,
            (Finset.univ.filter (fun e => u ∈ g.supp e)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ u ∈ g.supp e0, g.d := Finset.sum_le_sum (fun u _ => g.degree u)
      _ = (g.supp e0).card * g.d := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ = g.k * g.d := by rw [g.supp_card e0]
  calc ∑ e ∈ Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty),
        (Real.exp (4 * ‖z‖ * g.hnorm e) - 1)
      = ∑ e ∈ Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty),
          (Real.exp (c * g.hnorm e) - 1) := by rw [hcdef]
    _ ≤ ∑ e ∈ Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty), B :=
        Finset.sum_le_sum (fun e _ => hterm e)
    _ = ((Finset.univ.filter (fun e => (g.supp e ∩ g.supp e0).Nonempty)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((g.k : ℝ) * (g.d : ℝ)) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        exact_mod_cast hcard
    _ = ((g.k : ℝ) * (g.d : ℝ))
          * (Real.exp (4 * ‖z‖ * g.J) - 1) := by
        rw [hBdef, hcdef]

end Qatlib.Papers.FastMixing26.MainResults.ClusterExpansion

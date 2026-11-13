/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.PairwiseLoss.Basic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PairwiseLoss/Concentration — concentration of the pairwise explicit loss

Paper: Rudolph–Lerch–Thanasilp–Kiss–Shaya–Vallecorsa–Grossi–Holmes, *Trainability barriers and
opportunities in quantum generative modeling*, fixed arXiv:2305.02881v2.

* `collisionMass` — the model mass that the training support `P` carries at parameter `θ`, i.e.
  `s(θ) = Σ_{x ∈ P} q_θ(x)` of Eqs. (64)–(66);
* `noOverlapProb` — the probability that `N` independent model samples all avoid `P`:
  `E_θ[(1 - s(θ))^N]`, the left-hand side of Eq. (66);
* `noOverlapProb_ge_of_no_overlap` — Theorem 1, Eq. (24) / Eq. (63): the probability that the
  estimated pairwise loss equals its fixed point is at least `1 - δ` with
  `δ = N · |P| · μ`, where `μ` bounds every training bitstring's model probability.  Under the
  exponential concentration of Definition 1 (`μ = b^{-n}`, `b > 1`) this is
  `δ ∈ O(poly(n)/c^n)`, the paper's conclusion;
* `theorem1_loss_eq_fixedPoint_of_noOverlap` — the deterministic half of Theorem 1: disjoint
  supports make the empirical pairwise loss equal the fixed point of Eq. (23), citing
  `Qatlib.Papers.Trainability23.PairwiseLoss.pairwiseLoss_eq_lossFixedPoint`;
* `corollary3_fixedPoint_param_difference` — Corollary 3, Eqs. (94)–(95): the difference of the
  fixed points at two parameter values is the difference of the model-side sums and therefore
  carries no dependence on the training distribution;
* `disjointProb` and `suppProp1_disjointProb_lower` — Supplemental Proposition 1, Eqs. (88)–(93):
  for randomly chosen model support the no-overlap probability is bounded below by
  `1 - N_Q N_P / (2^n - N_P + 1)`.

The paper's own route to Eq. (24) goes through the averaged collision mass `μ_s`, its variance
`σ_s` and Chebyshev's inequality (Eqs. (64)–(85), pp. 29–30).  The formal version below uses the
pointwise bound supplied by Definition 1 instead, which is the same hypothesis the paper's final
estimate (74)/(84) uses; this replaces the Chebyshev step by Bernoulli's inequality, a strictly
cleaner argument that yields the same `δ = poly(n)/c^n`.
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.PairwiseLoss

namespace Qatlib.Papers.Trainability23.PairwiseLoss.Concentration

open scoped BigOperators

/-- The model mass carried by the training support `P` at parameter `θ`: the `s` of
Eqs. (64)–(66), `s(θ) = Σ_{x ∈ P} q_θ(x)`. -/
noncomputable def collisionMass {X Θ : Type*} [Fintype X] (q : Θ → FinDist X)
    (P : Finset X) (θ : Θ) : ℝ :=
  ∑ x ∈ P, (q θ).prob x

/-- The probability that `N` independent samples from the model at a random parameter `θ` all lie
outside the training support `P`. This is `E_θ[(1 - s(θ))^N]`, the integral of Eq. (66). -/
noncomputable def noOverlapProb {X Θ : Type*} [Fintype X] [Fintype Θ]
    (pθ : FinDist Θ) (q : Θ → FinDist X) (P : Finset X) (N : ℕ) : ℝ :=
  ∑ θ, pθ.prob θ * (1 - collisionMass q P θ) ^ N

/-- The collision mass is nonnegative — it is a sum of probabilities. -/
theorem collisionMass_nonneg {X Θ : Type*} [Fintype X] (q : Θ → FinDist X)
    (P : Finset X) (θ : Θ) : 0 ≤ collisionMass q P θ :=
  Finset.sum_nonneg fun x _ => (q θ).nonneg x

/-- The collision mass is at most one. -/
theorem collisionMass_le_one {X Θ : Type*} [Fintype X] (q : Θ → FinDist X)
    (P : Finset X) (θ : Θ) : collisionMass q P θ ≤ 1 := by
  unfold collisionMass
  calc ∑ x ∈ P, (q θ).prob x ≤ ∑ x : X, (q θ).prob x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
          fun x _ _ => (q θ).nonneg x
    _ = 1 := (q θ).sum_one

/-- Bernoulli's inequality in the form needed here: `1 - N·m ≤ (1 - m)^N` for `0 ≤ m ≤ 1`. -/
theorem one_sub_pow_ge {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (N : ℕ) :
    1 - (N : ℝ) * m ≤ (1 - m) ^ N := by
  have h := one_add_mul_le_pow (a := -m) (by linarith [hm0, hm1]) N
  have e1 : (1 : ℝ) + (N : ℝ) * (-m) = 1 - (N : ℝ) * m := by ring
  have e2 : (1 : ℝ) + (-m) = 1 - m := by ring
  rwa [e1, e2] at h

/-- **Theorem 1, Eq. (24)/(63), core estimate.**  If every training bitstring has model
probability at most `μ`, the probability that `N` samples all avoid the training support is at
least `1 - N·|P|·μ`.  With `μ = b^{-n}` and `N, |P| ∈ O(poly n)` this is the paper's
`δ ∈ O(poly(n)/c^n)`. -/
theorem noOverlapProb_ge_one_sub {X Θ : Type*} [Fintype X] [Fintype Θ]
    (pθ : FinDist Θ) (q : Θ → FinDist X) (P : Finset X) (N : ℕ) (μ : ℝ)
    (hμ : ∀ θ, ∀ x ∈ P, (q θ).prob x ≤ μ) :
    1 - noOverlapProb pθ q P N ≤ (N : ℝ) * ((P.card : ℝ) * μ) := by
  have hm0 : ∀ θ, 0 ≤ collisionMass q P θ := fun θ => collisionMass_nonneg q P θ
  have hm1 : ∀ θ, collisionMass q P θ ≤ 1 := fun θ => collisionMass_le_one q P θ
  have hmμ : ∀ θ, collisionMass q P θ ≤ (P.card : ℝ) * μ := by
    intro θ
    unfold collisionMass
    calc ∑ x ∈ P, (q θ).prob x ≤ ∑ _x ∈ P, μ :=
          Finset.sum_le_sum fun x hx => hμ θ x hx
      _ = (P.card : ℝ) * μ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hid : 1 - noOverlapProb pθ q P N
      = ∑ θ, pθ.prob θ * (1 - (1 - collisionMass q P θ) ^ N) := by
    unfold noOverlapProb
    have h1 : (1 : ℝ) = ∑ θ, pθ.prob θ := pθ.sum_one.symm
    nth_rewrite 1 [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun θ _ => by ring
  have hterm : ∑ θ, pθ.prob θ * (1 - (1 - collisionMass q P θ) ^ N)
      ≤ ∑ θ, pθ.prob θ * ((N : ℝ) * collisionMass q P θ) := by
    refine Finset.sum_le_sum fun θ _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (pθ.nonneg θ)
    have hB := one_sub_pow_ge (hm0 θ) (hm1 θ) N
    linarith
  have hsumμ : ∑ θ, pθ.prob θ * collisionMass q P θ ≤ (P.card : ℝ) * μ := by
    calc ∑ θ, pθ.prob θ * collisionMass q P θ
        ≤ ∑ θ, pθ.prob θ * ((P.card : ℝ) * μ) :=
          Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hmμ θ) (pθ.nonneg θ)
      _ = (P.card : ℝ) * μ := by
          rw [← Finset.sum_mul, pθ.sum_one, one_mul]
  calc 1 - noOverlapProb pθ q P N
      = ∑ θ, pθ.prob θ * (1 - (1 - collisionMass q P θ) ^ N) := hid
    _ ≤ ∑ θ, pθ.prob θ * ((N : ℝ) * collisionMass q P θ) := hterm
    _ = (N : ℝ) * ∑ θ, pθ.prob θ * collisionMass q P θ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun θ _ => by ring
    _ ≤ (N : ℝ) * ((P.card : ℝ) * μ) :=
        mul_le_mul_of_nonneg_left hsumμ (by positivity)

/-- **Theorem 1, Eq. (24)/(63), exponential form.**  Under the deterministic exponential
concentration of Definition 1 with fixed point `b^{-n}` (`b > 1`), the failure probability is at
most `N · |P| · b^{-n}`, i.e. `δ ∈ O(poly(n)/c^n)` with `c = b > 1`. -/
theorem noOverlapProb_ge_one_sub_exponential {X Θ : Type*} [Fintype X] [Fintype Θ]
    (pθ : FinDist Θ) (q : Θ → FinDist X) (P : Finset X) (N n : ℕ) (b : ℝ)
    (hb : 1 < b) (hμ : ∀ θ, ∀ x ∈ P, (q θ).prob x ≤ b ^ (-(n : ℤ))) :
    1 - noOverlapProb pθ q P N ≤ (N : ℝ) * ((P.card : ℝ) * b ^ (-(n : ℤ))) :=
  noOverlapProb_ge_one_sub pθ q P N _ hμ

/-- **Theorem 1, deterministic half.**  When the model support and the training support are
disjoint, the empirical pairwise loss of Eq. (3) equals the fixed point of Eq. (23).  This is the
implication behind "`L̃ = L₀` iff there is no overlap" used at the start of the appendix proof
(p.~28); it uses the shared development of the same statement. -/
theorem theorem1_loss_eq_fixedPoint_of_noOverlap {X : Type*} [Fintype X] [DecidableEq X]
    (f : ℝ → ℝ → ℝ) (hf : f 0 0 = 0) (p q : FinDist X)
    (hdisj : Disjoint (support p) (support q)) :
    pairwiseLoss f p.prob q.prob
      = lossFixedPoint f p.prob (support p) q.prob (support q) :=
  pairwiseLoss_eq_lossFixedPoint f hf p q hdisj

/-- **Corollary 3, Eqs. (94)–(95)/(96).**  The difference of the fixed points at two parameter
values is the difference of the model-side sums
`Σ_{x ∈ Q_{θ₁}} f(0, q_{θ₁}(x)) - Σ_{x ∈ Q_{θ₂}} f(0, q_{θ₂}(x))`,
in which the target's frequencies `p̃(x)` have cancelled.  Hence the difference of two statistical
estimates at different parameters carries no information about the training distribution. -/
theorem corollary3_fixedPoint_param_difference {X : Type*} [Fintype X]
    (f : ℝ → ℝ → ℝ) (p : FinDist X) (q1 q2 : FinDist X) :
    lossFixedPoint f p.prob (support p) q1.prob (support q1)
        - lossFixedPoint f p.prob (support p) q2.prob (support q2)
      = (∑ x ∈ support q1, f 0 (q1.prob x)) - (∑ x ∈ support q2, f 0 (q2.prob x)) := by
  unfold lossFixedPoint
  ring

/-- The complementary (no-overlap) probability of Eqs. (90)–(91) for a randomly drawn model
support of size `NQ` inside the `2^n` bitstrings, when the training support has size `NP`:
`∏_{k<NP} (2^n - NQ - k)/(2^n - k) = ∏_{k<NP} (1 - NQ/(2^n - k))`. -/
noncomputable def disjointProb (n NP NQ : ℕ) : ℝ :=
  ∏ k ∈ Finset.range NP, (((2 : ℝ) ^ n - (NQ : ℝ) - (k : ℝ)) / ((2 : ℝ) ^ n - (k : ℝ)))

/-- Eq. (92): every factor of the product is at least `1 - NQ/(2^n - NP + 1)`, since
`2^n - k ≥ 2^n - NP + 1` for `k ≤ NP - 1`. -/
theorem disjointProb_ge_pow {n NP NQ : ℕ}
    (hle : (NQ : ℝ) + (NP : ℝ) ≤ (2 : ℝ) ^ n) :
    (1 - (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)) ^ NP ≤ disjointProb n NP NQ := by
  have hNP : (NP : ℝ) ≤ (2 : ℝ) ^ n := by
    have h0 : (0 : ℝ) ≤ (NQ : ℝ) := by positivity
    linarith
  have hD : 0 < (2 : ℝ) ^ n - (NP : ℝ) + 1 := by linarith
  have hratio1 : (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hD]
    linarith
  have hconst : (1 - (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)) ^ NP
      = ∏ _k ∈ Finset.range NP, (1 - (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hconst]
  unfold disjointProb
  refine Finset.prod_le_prod₀ (fun k _ => by linarith) ?_
  intro k hk
  have hklt : (k : ℝ) < (NP : ℝ) := by
    have := Finset.mem_range.mp hk
    exact_mod_cast this
  have hk1 : k + 1 ≤ NP := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
  have hk1' : (k : ℝ) + 1 ≤ (NP : ℝ) := by exact_mod_cast hk1
  have hdk : 0 < (2 : ℝ) ^ n - (k : ℝ) := by linarith
  have hden : (2 : ℝ) ^ n - (NP : ℝ) + 1 ≤ (2 : ℝ) ^ n - (k : ℝ) := by linarith
  have hfactor : ((2 : ℝ) ^ n - (NQ : ℝ) - (k : ℝ)) / ((2 : ℝ) ^ n - (k : ℝ))
      = 1 - (NQ : ℝ) / ((2 : ℝ) ^ n - (k : ℝ)) := by
    field_simp
    ring
  rw [hfactor]
  have hmono : (NQ : ℝ) / ((2 : ℝ) ^ n - (k : ℝ))
      ≤ (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) hD hden
  linarith

/-- **Supplemental Proposition 1, Eq. (93).**  If the training and model supports fit inside the
`2^n` bitstrings, the no-overlap probability is at least
`1 - NQ·NP/(2^n - NP + 1)`, which is exponentially close to one for polynomial `NQ, NP`. -/
theorem suppProp1_disjointProb_lower {n NP NQ : ℕ}
    (hle : (NQ : ℝ) + (NP : ℝ) ≤ (2 : ℝ) ^ n) :
    1 - disjointProb n NP NQ ≤ (NQ : ℝ) * (NP : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) := by
  have hNP : (NP : ℝ) ≤ (2 : ℝ) ^ n := by
    have h0 : (0 : ℝ) ≤ (NQ : ℝ) := by positivity
    linarith
  have hD : 0 < (2 : ℝ) ^ n - (NP : ℝ) + 1 := by linarith
  have hratio0 : 0 ≤ (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) := by positivity
  have hratio2 : (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ hD]
    linarith
  have hbern := one_add_mul_le_pow (a := -((NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)))
    (by linarith) NP
  have hbern' : 1 - (NP : ℝ) * ((NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1))
      ≤ (1 - (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)) ^ NP := by
    have e1 : (1 : ℝ) + (NP : ℝ) * (-((NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)))
        = 1 - (NP : ℝ) * ((NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)) := by ring
    have e2 : (1 : ℝ) + (-((NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1)))
        = 1 - (NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) := by ring
    rwa [e1, e2] at hbern
  have hpow := disjointProb_ge_pow (n := n) (NP := NP) (NQ := NQ) hle
  have hmul : (NP : ℝ) * ((NQ : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1))
      = (NQ : ℝ) * (NP : ℝ) / ((2 : ℝ) ^ n - (NP : ℝ) + 1) := by
    rw [← mul_div_assoc]
    ring
  linarith

end Qatlib.Papers.Trainability23.PairwiseLoss.Concentration

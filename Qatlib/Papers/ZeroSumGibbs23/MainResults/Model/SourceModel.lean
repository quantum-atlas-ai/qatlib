/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGibbs23 — shared source model

Bouland, Getachew, Jin, Sidford, Tian, *Quantum Speedups for Zero-Sum Games via
Improved Dynamic Gibbs Sampling*, fixed arXiv:2301.03763v1 (10 Jan 2023).

This file fixes the finite-dimensional vocabulary used by every claim of the
`MainResults` block:

* the simplices `Δ_m, Δ_n` (Section 1.1, p.1),
* the payoff `uᵀ A v` and the `ε`-approximate Nash equilibrium duality gap
  (Section 1.1, p.1),
* the Gibbs distribution `p ∝ exp(Aᵀx)`, the partition function `Z`, and the
  approximate Gibbs oracle distance (Definition 1 and Problem 1, p.3),
* ℓ1 distance, used for the approximate-oracle and stability bounds,
* a finite probability-space model of a randomized solver, used to state the
  paper's "with probability at least `1 - α`" guarantees together with
  per-run runtime bounds.

The `ε`-approximate NE is stated with explicit quantifiers over `Δ_m × Δ_n`;
`approxNE_of_pure` and `pure_check_of_approxNE` show it coincides with checking
all pure strategies, which is the `max_{u∈Δ_m} uᵀAv - min_{v∈Δ_n} uᵀAv ≤ ε`
form used throughout the paper.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.Model

variable {m n : ℕ}

/-! ### Simplices, payoff and approximate Nash equilibria -/

/-- The paper's simplex `Δ_n = {x ∈ ℝ^n_{≥0} : ∑_i x_i = 1}` (Section 1.1, p.1). -/
def IsDist (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- ℓ1 norm of a finite real vector. -/
def l1Norm (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

/-- The paper's assumption `‖A‖_max ≤ 1` (Section 1.1, p.2), stated with a general
entry bound `b` so that rescalings are expressible. -/
def MaxEntryBound (A : Matrix (Fin m) (Fin n) ℝ) (b : ℝ) : Prop :=
  ∀ i j, |A i j| ≤ b

/-- The payoff `uᵀ A v` of the zero-sum game `(5)` (Appendix A, p.19). -/
def payoff (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * A i j * v j

/-- The column combination `Aᵀ u`, i.e. `(Aᵀ u)_j = ∑_i A_{ij} u_i`. -/
def colSum (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (j : Fin n) : ℝ :=
  ∑ i, A i j * u i

/-- The row combination `A v`, i.e. `(A v)_i = ∑_j A_{ij} v_j`. -/
def rowSum (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j * v j

/-- `(u, v) ∈ Δ_m × Δ_n` is an `ε`-approximate Nash equilibrium for `A`
(Section 1.1, p.1): the maximizer's best response against `v` exceeds the
minimizer's best response against `u` by at most `ε`. This is the paper's
`max_{v'∈Δ_n} uᵀAv' - min_{u'∈Δ_m} (u')ᵀAv ≤ ε` with explicit quantifiers. -/
def ApproxNE (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Prop :=
  IsDist u ∧ IsDist v ∧
    ∀ (u' : Fin m → ℝ) (v' : Fin n → ℝ), IsDist u' → IsDist v' →
      payoff A u' v - payoff A u v' ≤ ε

/-- One half of the simplex sum: a delta at a basis vector. -/
theorem isDist_basis_m (i : Fin m) : IsDist (fun i' : Fin m => if i' = i then (1 : ℝ) else 0) := by
  constructor
  · intro i'
    by_cases h : i' = i
    · simp [h]
    · simp [h]
  · simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- One half of the simplex sum: a delta at a basis vector. -/
theorem isDist_basis_n (j : Fin n) : IsDist (fun j' : Fin n => if j' = j then (1 : ℝ) else 0) := by
  constructor
  · intro j'
    by_cases h : j' = j
    · simp [h]
    · simp [h]
  · simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Payoff as a weighted sum of row combinations. -/
theorem payoff_eq_sum_mul_row (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    payoff A u v = ∑ i, u i * rowSum A v i := by
  unfold payoff rowSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Payoff as a weighted sum of column combinations. -/
theorem payoff_eq_sum_mul_col (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    payoff A u v = ∑ j, colSum A u j * v j := by
  unfold payoff colSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Payoff against a basis vector on the left is the corresponding row sum. -/
theorem payoff_basis_left (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (v : Fin n → ℝ) :
    payoff A (fun i' : Fin m => if i' = i then (1 : ℝ) else 0) v = rowSum A v i := by
  rw [payoff_eq_sum_mul_row]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'; simp [hi']
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Payoff against a basis vector on the right is the corresponding column sum. -/
theorem payoff_basis_right (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (j : Fin n) :
    payoff A u (fun j' : Fin n => if j' = j then (1 : ℝ) else 0) = colSum A u j := by
  rw [payoff_eq_sum_mul_col]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; simp [hj']
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Against a distribution `v ≥ 0`, no mixed strategy beats the best pure strategy. -/
theorem payoff_le_max_pure {A : Matrix (Fin m) (Fin n) ℝ} {u : Fin m → ℝ} {v : Fin n → ℝ}
    {B : ℝ} (hu : IsDist u) (hB : ∀ i, rowSum A v i ≤ B) :
    payoff A u v ≤ B := by
  rw [payoff_eq_sum_mul_row]
  calc
    ∑ i, u i * rowSum A v i ≤ ∑ i, u i * B :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i) (hu.1 i)
    _ = B := by rw [← Finset.sum_mul, hu.2, one_mul]

/-- Against a distribution `u ≥ 0`, the worst pure strategy is no better than any mixed one. -/
theorem min_pure_le_payoff {A : Matrix (Fin m) (Fin n) ℝ} {u : Fin m → ℝ} {v : Fin n → ℝ}
    {B : ℝ} (hv : IsDist v) (hB : ∀ j, B ≤ colSum A u j) :
    B ≤ payoff A u v := by
  rw [payoff_eq_sum_mul_col]
  calc
    B = ∑ j, B * v j := by rw [← Finset.mul_sum, hv.2, mul_one]
    _ ≤ ∑ j, colSum A u j * v j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hB j) (hv.1 j)

/-- If all pure strategies violate the gap bound, `(u, v)` is an approximate NE. -/
theorem approxNE_of_pure {A : Matrix (Fin m) (Fin n) ℝ} {ε : ℝ} {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : IsDist u) (hv : IsDist v) (hm : 0 < m) (hn : 0 < n)
    (h : ∀ i j, rowSum A v i - colSum A u j ≤ ε) :
    ApproxNE A ε u v := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, _hi0mem, hi0⟩ :=
    Finset.exists_max_image Finset.univ (fun i => rowSum A v i) Finset.univ_nonempty
  obtain ⟨j0, _hj0mem, hj0⟩ :=
    Finset.exists_min_image Finset.univ (fun j => colSum A u j) Finset.univ_nonempty
  have hgap : rowSum A v i0 - colSum A u j0 ≤ ε := h i0 j0
  refine ⟨hu, hv, ?_⟩
  intro u' v' hu' hv'
  have h1 : payoff A u' v ≤ rowSum A v i0 :=
    payoff_le_max_pure hu' fun i => hi0 i (Finset.mem_univ i)
  have h2 : colSum A u j0 ≤ payoff A u v' :=
    min_pure_le_payoff hv' fun j => hj0 j (Finset.mem_univ j)
  linarith

/-- The pure-strategy check implied by an approximate NE. -/
theorem pure_check_of_approxNE {A : Matrix (Fin m) (Fin n) ℝ} {ε : ℝ} {u : Fin m → ℝ}
    {v : Fin n → ℝ} (h : ApproxNE A ε u v) (i : Fin m) (j : Fin n) :
    rowSum A v i - colSum A u j ≤ ε := by
  have h' := h.2.2 (fun i' : Fin m => if i' = i then (1 : ℝ) else 0)
    (fun j' : Fin n => if j' = j then (1 : ℝ) else 0) (isDist_basis_m i) (isDist_basis_n j)
  rwa [payoff_basis_left, payoff_basis_right] at h'

/-! ### Gibbs distributions -/

/-- The unnormalised Gibbs weights `exp(w_j)` of `w = Aᵀx`. -/
def gibbsWeight (w : Fin n → ℝ) (j : Fin n) : ℝ := Real.exp (w j)

/-- The partition function `Z = ∑_j exp(w_j)`. -/
def gibbsZ (w : Fin n → ℝ) : ℝ := ∑ j, Real.exp (w j)

/-- The Gibbs distribution `p_j = exp(w_j)/Z` of Definition 1 (p.3). -/
def gibbsP (w : Fin n → ℝ) (j : Fin n) : ℝ := Real.exp (w j) / gibbsZ w

/-- The Gibbs logits `Aᵀ x` associated with an iterate `x`. -/
def gibbsLogit (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => colSum A x j

/-- The partition function is strictly positive on a nonempty index set. -/
theorem gibbsZ_pos (w : Fin n → ℝ) (hn : 0 < n) : 0 < gibbsZ w := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun j _ => Real.exp_pos (w j)) Finset.univ_nonempty

/-- Gibbs probabilities are nonnegative. -/
theorem gibbsP_nonneg (w : Fin n → ℝ) (hn : 0 < n) (j : Fin n) : 0 ≤ gibbsP w j :=
  div_nonneg (le_of_lt (Real.exp_pos (w j))) (le_of_lt (gibbsZ_pos w hn))

/-- Gibbs probabilities sum to one. -/
theorem gibbsP_sum (w : Fin n → ℝ) (hn : 0 < n) : ∑ j, gibbsP w j = 1 := by
  unfold gibbsP
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (gibbsZ_pos w hn))

/-- The Gibbs distribution is a simplex point. -/
theorem gibbsP_isDist (w : Fin n → ℝ) (hn : 0 < n) : IsDist (gibbsP w) :=
  ⟨gibbsP_nonneg w hn, gibbsP_sum w hn⟩

/-- A `δ`-approximate Gibbs oracle samples from a distribution `p̃ ∈ Δ_n` with
`‖p̃ - p‖₁ ≤ δ` (Definition 1, p.3). -/
def IsApproxGibbs (p p' : Fin n → ℝ) (δ : ℝ) : Prop :=
  l1Norm (fun j => p' j - p j) ≤ δ

/-- The ℓ1 norm is nonnegative. -/
theorem l1Norm_nonneg (x : Fin n → ℝ) : 0 ≤ l1Norm x :=
  Finset.sum_nonneg fun i _ => abs_nonneg (x i)

/-- ℓ1 distance is monotone in the coordinatewise error bound `δ`. -/
theorem l1Norm_le_of_abs_le {x : Fin n → ℝ} {δ : ℝ} (h : ∀ i, |x i| ≤ δ) :
    l1Norm x ≤ δ * n := by
  unfold l1Norm
  calc
    ∑ i, |x i| ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => h i
    _ = δ * n := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### Finite probability spaces and randomized solvers -/

/-- A finite probability space, used to state "with probability at least `1 - α`". -/
structure FinProbSpace where
  Ω : Type
  instFintype : Fintype Ω
  instNonempty : Nonempty Ω
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1

attribute [instance] FinProbSpace.instFintype FinProbSpace.instNonempty

/-- Probability of an event in a finite probability space. -/
def Pr (P : FinProbSpace) (E : P.Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then P.prob ω else 0

/-- Probabilities are nonnegative. -/
theorem Pr_nonneg (P : FinProbSpace) (E : P.Ω → Prop) : 0 ≤ Pr P E := by
  unfold Pr
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> [exact P.prob_nonneg ω; exact le_refl 0]

/-- The probability of the universal event is one. -/
theorem Pr_true (P : FinProbSpace) : Pr P (fun _ => True) = 1 := by
  unfold Pr
  classical
  simpa using P.prob_sum

/-- Monotonicity of finite probability under implication. -/
theorem Pr_mono (P : FinProbSpace) {E F : P.Ω → Prop} (h : ∀ ω, E ω → F ω) :
    Pr P E ≤ Pr P F := by
  unfold Pr
  classical
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hE : E ω
  · have hF : F ω := h ω hE
    simp [if_pos hE, if_pos hF]
  · by_cases hF : F ω
    · simp [if_neg hE, if_pos hF, P.prob_nonneg ω]
    · simp [if_neg hE, if_neg hF]

/-- A randomized solver: a finite family of classical outputs `(u, v)`, each on
the simplex, with a per-run cost. This is the paper's "quantum algorithm with
classical output" at the level of its mathematical guarantee (Theorem 4, p.8). -/
structure RandomizedSolver (m n : ℕ) where
  space : FinProbSpace
  outU : space.Ω → Fin m → ℝ
  outV : space.Ω → Fin n → ℝ
  outU_dist : ∀ ω, IsDist (outU ω)
  outV_dist : ∀ ω, IsDist (outV ω)
  cost : space.Ω → ℝ
  cost_nonneg : ∀ ω, 0 ≤ cost ω

/-- Success probability of a solver on a game `A` at accuracy `ε`. -/
def RandomizedSolver.successProb {m n : ℕ} (S : RandomizedSolver m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) : ℝ :=
  Pr S.space fun ω => ApproxNE A ε (S.outU ω) (S.outV ω)

/-! ### IID product spaces and empirical distributions -/

/-- The weight of a tuple of `N` iid draws from `p`: `∏_t p(ω t)`. -/
def sampleProb {n : ℕ} (p : Fin n → ℝ) {N : ℕ} (ω : Fin N → Fin n) : ℝ :=
  ∏ t, p (ω t)

/-- Weights of an iid sampling tuple are nonnegative. -/
theorem sampleProb_nonneg {p : Fin n → ℝ} (hp : ∀ j, 0 ≤ p j) {N : ℕ}
    (ω : Fin N → Fin n) : 0 ≤ sampleProb p ω :=
  Finset.prod_nonneg fun t _ => hp (ω t)

/-- The total weight of the product distribution of `N` draws from a simplex
point is one. -/
theorem iid_weight_sum (p : Fin n → ℝ) (hp : ∑ j, p j = 1) (N : ℕ) :
    ∑ ω : Fin N → Fin n, sampleProb p ω = 1 := by
  have h := Finset.sum_prod_piFinset (ι := Fin N) (κ := Fin n)
    (s := (Finset.univ : Finset (Fin n))) (g := fun (_ : Fin N) (j : Fin n) => p j)
  rw [Fintype.piFinset_univ] at h
  have h' : (∑ ω : Fin N → Fin n, sampleProb p ω) = ∏ _t : Fin N, ∑ j, p j := by
    simpa [sampleProb] using h
  rw [h']
  simp [hp]

/-- The product probability space of `N` independent draws from `p`, used to
state the paper's sampling lemmas (Lemma 3, Lemma 4, Lemma 6, p.12–21). -/
def iidSpace (p : Fin n → ℝ) (hp : IsDist p) (N : ℕ) : FinProbSpace where
  Ω := Fin N → Fin n
  instFintype := inferInstance
  instNonempty := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      exact ⟨fun t => t.elim0⟩
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have h0 : (∑ j : Fin 0, p j) = 0 := by simp
          linarith [hp.2, h0]
        · exact hn
      exact ⟨fun _ => ⟨0, hn⟩⟩
  prob := fun ω => sampleProb p ω
  prob_nonneg := fun ω => sampleProb_nonneg hp.1 ω
  prob_sum := iid_weight_sum p hp.2 N

/-- The empirical distribution of a sample tuple `ω : Fin N → Fin n`. -/
def empiricalDist {n : ℕ} (N : ℕ) (ω : Fin N → Fin n) (j : Fin n) : ℝ :=
  ((Finset.univ.filter fun t => ω t = j).card : ℝ) / N

/-- The fibre-cardinality identity behind the empirical distribution:
`∑_j |{t | ω t = j}| = N`. -/
theorem sum_card_fiber {n : ℕ} {N : ℕ} (ω : Fin N → Fin n) :
    (∑ j : Fin n, ((Finset.univ.filter fun t => ω t = j).card : ℝ)) = (N : ℝ) := by
  have h := Finset.sum_fiberwise (s := (Finset.univ : Finset (Fin N))) (g := ω)
    (f := fun _ : Fin N => (1 : ℝ))
  have h1 : ∀ j : Fin n,
      (∑ t ∈ Finset.univ.filter (fun t => ω t = j), (1 : ℝ)) =
        ((Finset.univ.filter fun t => ω t = j).card : ℝ) := by
    intro j
    simp
  simp only [h1] at h
  rw [h]
  simp

/-- Empirical probabilities are nonnegative. -/
theorem empiricalDist_nonneg {n N : ℕ} (ω : Fin N → Fin n) (j : Fin n) :
    0 ≤ empiricalDist N ω j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The empirical distribution of `N ≥ 1` samples sums to one. -/
theorem empiricalDist_sum {n N : ℕ} (hN : 0 < N) (ω : Fin N → Fin n) :
    ∑ j, empiricalDist N ω j = 1 := by
  unfold empiricalDist
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, sum_card_fiber]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  exact mul_inv_cancel₀ hNne

/-- The empirical distribution is a simplex point. -/
theorem empiricalDist_isDist {n N : ℕ} (hN : 0 < N) (ω : Fin N → Fin n) :
    IsDist (empiricalDist N ω) :=
  ⟨fun j => empiricalDist_nonneg ω j, empiricalDist_sum hN ω⟩

/-- The ℓ1 norm of a simplex point is one. -/
theorem l1Norm_eq_one_of_isDist {x : Fin n → ℝ} (h : IsDist x) : l1Norm x = 1 := by
  unfold l1Norm
  rw [← h.2]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (h.1 i)

/-! ### Problem 1: dynamic approximate Gibbs sampling -/

/-- A solution to Problem 1 (p.4): it returns, at every iteration `t`, a sample
law `sampleLaw t ω ∈ Δ_n` that is `δ`-close in ℓ1 to the Gibbs distribution of
the dynamic vector `Aᵀ x_t`, together with a per-iteration sampling cost and a
per-iteration update cost. -/
structure MaintenanceSolver (m n : ℕ) where
  space : FinProbSpace
  sampleLaw : ℕ → space.Ω → Fin n → ℝ
  sampleLaw_dist : ∀ t ω, IsDist (sampleLaw t ω)
  samplingCost : space.Ω → ℝ
  updateCost : space.Ω → ℝ
  samplingCost_nonneg : ∀ ω, 0 ≤ samplingCost ω
  updateCost_nonneg : ∀ ω, 0 ≤ updateCost ω

/-- The per-run success event of a maintenance solver on the update stream `x_t`:
every returned sample law up to time `T` is a `δ`-approximate Gibbs distribution
of `Aᵀ x_t` (Definition 1, p.3). -/
def MaintenanceSolver.SucceedsOn {m n : ℕ} (S : MaintenanceSolver m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (x : ℕ → Fin m → ℝ) (δ : ℝ) (T : ℕ)
    (ω : S.space.Ω) : Prop :=
  ∀ t, t < T → l1Norm (fun j => S.sampleLaw t ω j - gibbsP (gibbsLogit A (x t)) j) ≤ δ

end Qatlib.Papers.ZeroSumGibbs23.MainResults.Model

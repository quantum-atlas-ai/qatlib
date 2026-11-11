/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs

set_option backward.isDefEq.respectTransparency false

/-!
# WeldedTree26 — shared paper-layer model

Fixed source: arXiv:2609.26712v1, *A quantum lower bound for path finding in welded trees*
(Carolan, Childs, Coudron, Gilani).  The PDF/text used for this layer are the task assets
`assets/2609.26712v1.pdf` and `assets/2609.26712v1.txt`; the qatlas markdown endpoint was
unavailable (HTTP 503) and is not used.

This module pins the parameters and the explicitly displayed formulas that the claim
statements below refer to:

* `paperN n = 2^n`, `paperM n = 2^(2n) = N^2`, `paperK n = 4N - 2` (§3.2, eq. (50),
  together with `K_c = |L_{¬c}|` kept as an explicit parameter);
* `coreDepth n = n/2 + 1` and `pathS n q = (n+2) q = 2 d q` (Lemma 4.2, Theorem 4.3);
* `epsilonBound`, `nuBound`, `sigmaPerm` (eqs. (37)–(39), with `sigmaPerm` the finite sum
  of `nuPerm` from eq. (36));
* `EQ` and `VQ` (Theorem 4.3, eq. (95)), `DeltaQ` (Lemma 4.2, before eq. (95)),
  `deltaClip` (Lemma 3.16, eq. (71)), `etaPlacement` (Lemma 3.17, eq. (79));
* the Euclidean state norm `stateNorm` and distance `stateDist` on `QState (Fin D)`.

`stateNorm` is the norm of the Hilbert-space vector `|ψ⟩` used throughout the paper, i.e. the
Euclidean (`ℓ²`) norm `sqrt (∑ i, ‖ψ i‖^2)`, not the default Pi sup norm on functions.

Everything in this module is proved; the deep quantum/operator claims live in sibling modules
and are statement-level with explicit modeling boundaries documented there.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeldedTree26.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators ComplexOrder

/-! ## Paper parameters -/

/-- `N = 2^n` (paper §3.2). -/
def paperN (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- `M = |{0,1}^{2n}| = 2^{2n} = N^2` (paper §3.2, eq. (50)). -/
def paperM (n : ℕ) : ℝ := (2 : ℝ) ^ (2 * n)

/-- `K = |V| = 2 (2^{n+1} - 1) = 4N - 2`, the number of vertices of the two depth-`n` binary
trees (paper §3.1/§3.2, eq. (50)). -/
def paperK (n : ℕ) : ℝ := 4 * paperN n - 2

/-- `d = n/2 + 1` (Lemma 4.2, Lemma 4.1). -/
def coreDepth (n : ℕ) : ℝ := (n : ℝ) / 2 + 1

/-- `S = 2 d q = (n + 2) q` (Lemma 4.2, Theorem 4.3). -/
def pathS (n : ℕ) (q : ℝ) : ℝ := (n + 2 : ℝ) * q

/-- `ε_perm(q, L) = O(q / L^{1/2})` (eq. (37)): an abstract soundness bound with the paper's
explicit shape, an explicit constant `C ≥ 0`. -/
noncomputable def epsilonBound (C : ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  C * (q : ℝ) / Real.sqrt L

/-- `ν_perm(r, L) = O((r + 1) / L^{1/2})` (eq. (38)), with an explicit constant. -/
noncomputable def nuBound (C : ℝ) (r : ℕ) (L : ℝ) : ℝ :=
  C * (r + 1 : ℝ) / Real.sqrt L

/-- `σ_perm(Q, L) = 2 ∑_{r=1}^{Q} ν_perm(r, L)` (eq. (36)); the sum starts at `r = 1`. -/
noncomputable def sigmaPerm (nu : ℕ → ℝ → ℝ) (Q : ℕ) (L : ℝ) : ℝ :=
  2 * ∑ r ∈ Finset.range Q, nu (r + 1) L

/-- `E_Q = ε_perm(Q, M) + ∑_{c∈{r,g,b}} ε_perm(Q, K_c)` (Theorem 4.3).  The three colours are
indexed by `Fin 3`. -/
noncomputable def EQ (eps : ℕ → ℝ → ℝ) (Q : ℕ) (M : ℝ) (Kc : Fin 3 → ℝ) : ℝ :=
  eps Q M + ∑ c : Fin 3, eps Q (Kc c)

/-- `V_Q = Q sqrt(K/(M−Q)) + Q sqrt(Q/(K_min−Q))` (Theorem 4.3). -/
noncomputable def VQ (Q K M Kmin : ℝ) : ℝ :=
  Q * Real.sqrt (K / (M - Q)) + Q * Real.sqrt (Q / (Kmin - Q))

/-- `Δ_Q = σ_perm(Q,M) + ∑_c σ_perm(Q,K_c) + q sqrt(K/(M−Q)) + q sqrt(Q/(K_min−Q))`
(Lemma 4.2). -/
noncomputable def DeltaQ (sig : ℕ → ℝ → ℝ) (Q : ℕ) (M K : ℝ) (Kc : Fin 3 → ℝ)
    (Kmin q : ℝ) : ℝ :=
  sig Q M + ∑ c : Fin 3, sig Q (Kc c)
    + q * Real.sqrt (K / (M - Q)) + q * Real.sqrt (Q / (Kmin - Q))

/-- `δ_t = 64 t^2 N^{-1/4}` (Lemma 3.16, eq. (71)). -/
noncomputable def deltaClip (N t : ℝ) : ℝ :=
  64 * t ^ 2 * N ^ (-(1 / 4 : ℝ))

/-- `η_t = 4 t^2 N^{-1/4} + t^2 / N` (Lemma 3.17, eq. (79)). -/
noncomputable def etaPlacement (N t : ℝ) : ℝ :=
  4 * t ^ 2 * N ^ (-(1 / 4 : ℝ)) + t ^ 2 / N

/-! ## State norms and distances

The paper writes `‖|ψ⟩‖` for the Euclidean norm of a joint state vector.  `QState (Fin D)` is
a function type, so we expose the `ℓ²` norm explicitly instead of the Pi sup norm. -/

/-- Squared Euclidean norm `∑ i, ‖ψ i‖^2` of a state vector. -/
def stateNormSq {D : ℕ} (ψ : QState (Fin D)) : ℝ := ∑ i, ‖ψ i‖ ^ 2

/-- Euclidean norm `‖|ψ⟩‖ = sqrt(∑ i, ‖ψ i‖^2)`. -/
noncomputable def stateNorm {D : ℕ} (ψ : QState (Fin D)) : ℝ := Real.sqrt (stateNormSq ψ)

/-- Euclidean distance `‖|ψ⟩ − |ψ'⟩‖` between two state vectors. -/
noncomputable def stateDist {D : ℕ} (ψ ψ' : QState (Fin D)) : ℝ :=
  stateNorm (ψ - ψ')

/-- The squared Euclidean norm of the zero state vector is zero. -/
@[simp] theorem stateNormSq_zero {D : ℕ} : stateNormSq (0 : QState (Fin D)) = 0 := by
  simp [stateNormSq]

/-- The squared Euclidean norm of a state vector is nonnegative. -/
theorem stateNormSq_nonneg {D : ℕ} (ψ : QState (Fin D)) : 0 ≤ stateNormSq ψ := by
  unfold stateNormSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The Euclidean norm of a state vector is nonnegative. -/
theorem stateNorm_nonneg {D : ℕ} (ψ : QState (Fin D)) : 0 ≤ stateNorm ψ :=
  Real.sqrt_nonneg _

/-- The Euclidean distance between two state vectors is nonnegative. -/
theorem stateDist_nonneg {D : ℕ} (ψ ψ' : QState (Fin D)) : 0 ≤ stateDist ψ ψ' :=
  stateNorm_nonneg _

/-- The distance from a state vector to itself is zero. -/
@[simp] theorem stateDist_self {D : ℕ} (ψ : QState (Fin D)) : stateDist ψ ψ = 0 := by
  simp [stateDist, stateNorm, stateNormSq, sub_self]

/-! ## Arithmetic helpers for the displayed constants -/

/-- `M = N^2`: the label universe has `2^{2n} = (2^n)^2` elements. -/
theorem paperM_eq_paperN_sq (n : ℕ) : paperM n = paperN n ^ 2 := by
  unfold paperM paperN
  rw [show 2 * n = n * 2 from by omega, pow_mul]

/-- `N = 2^n` is positive. -/
theorem paperN_pos (n : ℕ) : 0 < paperN n := by
  unfold paperN
  exact pow_pos (by norm_num) _

/-- `N = 2^n` is at least one. -/
theorem paperN_one_le (n : ℕ) : 1 ≤ paperN n := by
  unfold paperN
  exact one_le_pow₀ (by norm_num)

/-- `S = 2 d q`: `(n+2) q = 2 (n/2 + 1) q` (Lemma 4.2). -/
theorem pathS_eq_two_coreDepth (n : ℕ) (q : ℝ) :
    pathS n q = 2 * coreDepth n * q := by
  unfold pathS coreDepth
  ring

/-- `δ_t` is nonnegative for `N > 0` and `t ≥ 0` (Lemma 3.16). -/
theorem deltaClip_nonneg {N t : ℝ} (hN : 0 < N) (_ht : 0 ≤ t) : 0 ≤ deltaClip N t := by
  unfold deltaClip
  have hpow : 0 ≤ N ^ (-(1 / 4 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hN _)
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith [mul_nonneg ht2 hpow]

/-- `η_t` is nonnegative for `N > 0` and `t ≥ 0` (Lemma 3.17). -/
theorem etaPlacement_nonneg {N t : ℝ} (hN : 0 < N) (_ht : 0 ≤ t) :
    0 ≤ etaPlacement N t := by
  unfold etaPlacement
  have hpow : 0 ≤ N ^ (-(1 / 4 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hN _)
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have hN1 : 0 ≤ N := le_of_lt hN
  have hdiv : 0 ≤ t ^ 2 / N := div_nonneg ht2 hN1
  nlinarith [mul_nonneg ht2 hpow]

/-- `σ_perm(Q, L) ≥ 0` whenever `ν_perm(·, L) ≥ 0` (eq. (36)). -/
theorem sigmaPerm_nonneg {nu : ℕ → ℝ → ℝ} {Q : ℕ} {L : ℝ}
    (hnu : ∀ r, 0 ≤ nu r L) : 0 ≤ sigmaPerm nu Q L := by
  unfold sigmaPerm
  have hsum : 0 ≤ ∑ r ∈ Finset.range Q, nu (r + 1) L :=
    Finset.sum_nonneg fun r _ => hnu (r + 1)
  nlinarith

/-- `E_Q ≥ 0` whenever the component soundness bounds are nonnegative (Theorem 4.3). -/
theorem EQ_nonneg {eps : ℕ → ℝ → ℝ} {Q : ℕ} {M : ℝ} {Kc : Fin 3 → ℝ}
    (hM : 0 ≤ eps Q M) (hK : ∀ c, 0 ≤ eps Q (Kc c)) : 0 ≤ EQ eps Q M Kc := by
  unfold EQ
  exact add_nonneg hM (Finset.sum_nonneg fun c _ => hK c)

/-- `V_Q ≥ 0` under the paper's side conditions `M > Q`, `K_min > Q` (Theorem 4.3). -/
theorem VQ_nonneg {Q K M Kmin : ℝ}
    (hQ0 : 0 ≤ Q) (_hK0 : 0 ≤ K) (_hM : Q < M) (_hKmin : Q < Kmin)
    (_hMQ : 0 ≤ M - Q) (_hKQ : 0 ≤ Kmin - Q) :
    0 ≤ VQ Q K M Kmin := by
  unfold VQ
  have h1 : 0 ≤ Real.sqrt (K / (M - Q)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (Q / (Kmin - Q)) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hQ0 h1, mul_nonneg hQ0 h2]

/-- `Δ_Q ≥ 0` whenever the soundness bounds are nonnegative and `M > Q`, `K_min > Q`
(Lemma 4.2). -/
theorem DeltaQ_nonneg {sig : ℕ → ℝ → ℝ} {Q : ℕ} {M K : ℝ} {Kc : Fin 3 → ℝ}
    {Kmin q : ℝ}
    (hM : 0 ≤ sig Q M) (hK : ∀ c, 0 ≤ sig Q (Kc c))
    (hq0 : 0 ≤ q) (_hK0 : 0 ≤ K) (_hKmin0 : 0 ≤ Q)
    (_hMQ : 0 ≤ M - Q) (_hKQ : 0 ≤ Kmin - Q) :
    0 ≤ DeltaQ sig Q M K Kc Kmin q := by
  unfold DeltaQ
  have hsum : 0 ≤ ∑ c : Fin 3, sig Q (Kc c) :=
    Finset.sum_nonneg fun c _ => hK c
  have h1 : 0 ≤ Real.sqrt (K / (M - Q)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (Q / (Kmin - Q)) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hq0 h1, mul_nonneg hq0 h2]

/-- The explicit bounds of eqs. (37)–(38) have the monotone shapes quoted in the paper:
`ε_perm(q,L) ≤ ε_perm(q',L)` for `q ≤ q'` and `C ≥ 0`, and likewise for `ν_perm`. -/
theorem epsilonBound_mono (C : ℝ) (hC : 0 ≤ C) {q q' : ℕ} {L : ℝ}
    (hqq' : q ≤ q') (_hL : 0 ≤ L) :
    epsilonBound C q L ≤ epsilonBound C q' L := by
  unfold epsilonBound
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have : (q : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hqq'
  gcongr

end Qatlib.Papers.WeldedTree26.MainResults

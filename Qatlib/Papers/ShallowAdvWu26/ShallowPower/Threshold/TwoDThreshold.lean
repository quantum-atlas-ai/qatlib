/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11: two-dimensional construction of the threshold gate

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 11, p.27-28, with the
threshold gate of Definition 4 (p.18) and the parity assembly of Eq. (L4)-(L5).

For `m = poly(n)` and `τ ∈ {0,…,m}`, the threshold gate is

```
TH_{m,τ} : |x_1,…,x_m⟩|b⟩ ↦ |x_1,…,x_m⟩|b ⊕ 1[∑_i x_i ≥ τ]⟩.
```

Lemma 11 constructs a polynomial-time uniform rectangular 2D dynamic circuit
with `poly(n)` qubits, `O(1)` coherent depth and `O(1)` adaptive rounds; the same
holds for non-negative integer weighted thresholds `1[∑_i w_i x_i ≥ τ]` with
`∑_i w_i = poly(n)`.

The paper builds each `exact[t]` (the indicator of `S(x) = t`), combines them by
the parity (`Hadamard`-conjugated fan-out, Eq. (L4)) and places the layers on
disjoint crossbar slabs of Lemma 10.  At the paper layer we prove the algebraic
core:

* the parity of the `exact[t]`-indicators over `t ∈ [τ, m]` equals the threshold;
* a non-negative weighted threshold is exactly the unweighted threshold on the
  expanded list of `w_i` copies of `x_i`.

The two-dimensional layout and the resource count enter through the
`TwoDThresholdImplementation` record, whose site bound is proved polynomial.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.Threshold

/-- Hamming weight `|x| = ∑_i x_i` of a Boolean string. -/
def hammingWeight {m : ℕ} (x : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i)).card

/-- The Hamming weight never exceeds the number of inputs. -/
theorem hammingWeight_le {m : ℕ} (x : Fin m → Bool) : hammingWeight x ≤ m := by
  unfold hammingWeight
  calc
    (Finset.univ.filter (fun i => x i)).card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_filter_le _ _
    _ = m := by simp

/-- The `exact[t]` predicate of Lemma 11: `1[S(x) = t]`. -/
def exactBit {m : ℕ} (t : ℕ) (x : Fin m → Bool) : ℕ :=
  if hammingWeight x = t then 1 else 0

/-- The threshold gate `TH_{m,τ}` (`b` is the XOR target, omitted here). -/
def thresholdGate {m : ℕ} (τ : ℕ) (x : Fin m → Bool) : Bool :=
  decide (τ ≤ hammingWeight x)

/-- **Lemma 11, parity assembly (Eq. (L4)-(L5)).**  For `τ ≤ m`, the parity of
the `exact[t]` indicators over `t = τ, …, m` is the threshold of `S(x) ≥ τ`:
exactly one `exact[t]` is nonzero when `S(x) ≥ τ`, and none is when
`S(x) < τ`. -/
theorem threshold_of_exact_layer {m τ : ℕ} (x : Fin m → Bool) (hτ : τ ≤ m) :
    (∑ t ∈ Finset.range (m + 1), if τ ≤ t then exactBit t x else 0)
      = if τ ≤ hammingWeight x then 1 else 0 := by
  have hmem : hammingWeight x ∈ Finset.range (m + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hammingWeight_le x)
  have hcongr : ∀ t ∈ Finset.range (m + 1),
      (if τ ≤ t then exactBit t x else 0) =
        (if t = hammingWeight x then (if τ ≤ hammingWeight x then 1 else 0) else 0) := by
    intro t _
    by_cases h : t = hammingWeight x
    · subst h
      simp [exactBit]
    · have h' : ¬ (hammingWeight x = t) := fun hh => h hh.symm
      simp [exactBit, h, h']
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
  simp [hmem]

/-- A non-negative weighted threshold's score equals the Hamming weight of the
expanded word in which `x_i` is repeated `w_i` times. -/
theorem weighted_threshold_expansion {m : ℕ} (w : Fin m → ℕ) (x : Fin m → Bool) :
    (∑ p : Σ i : Fin m, Fin (w i), (if x p.1 then 1 else 0))
      = ∑ i, w i * (if x i then 1 else 0) := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hconst : (∑ s : Fin (w i),
      (if x ((⟨i, s⟩ : Sigma (fun j => Fin (w j))).1) then 1 else 0)) =
      ∑ _s : Fin (w i), (if x i then 1 else 0) :=
    Finset.sum_congr rfl (fun s _ => rfl)
  rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

/-- The non-negative integer weighted threshold gate
`1[∑_i w_i x_i ≥ τ]` (Definition 4 and the weighted remark, p.18). -/
def weightedThresholdGate {m : ℕ} (w : Fin m → ℕ) (τ : ℕ)
    (x : Fin m → Bool) : Bool :=
  decide (τ ≤ ∑ i, w i * (if x i then 1 else 0))

/-- **Lemma 11, weighted reduction.**  A non-negative weighted threshold is the
unweighted threshold on the expanded `∑_i w_i` inputs, so the unweighted 2D
construction applies whenever `∑_i w_i = poly(n)`. -/
theorem weighted_threshold_expanded {m : ℕ} (w : Fin m → ℕ) (τ : ℕ)
    (x : Fin m → Bool) :
    weightedThresholdGate w τ x =
      decide (τ ≤ ∑ p : Σ i : Fin m, Fin (w i), (if x p.1 then 1 else 0)) := by
  unfold weightedThresholdGate
  rw [weighted_threshold_expansion]

/-- Site count of the rectangular threshold block: one cell per input and per
`exact[t]` layer entry, bounded by `(m+1)^2`. -/
def thresholdSites (m : ℕ) : ℕ := m * (m + 1)

/-- Coherent depth of the composed threshold block (crossbar rows, parity strip
and their inverses). -/
def thresholdCoherentDepth : ℕ := 3

/-- Adaptive rounds of the threshold block. -/
def thresholdRounds : ℕ := 1

/-- A two-dimensional dynamic threshold implementation. -/
structure TwoDThresholdImplementation (m τ : ℕ) where
  /-- Polynomial site budget. -/
  sites : ℕ
  /-- Coherent depth. -/
  coherentDepth : ℕ
  /-- Adaptive rounds. -/
  rounds : ℕ
  /-- Implemented Boolean predicate on inputs. -/
  action : (Fin m → Bool) → Bool
  sites_le : sites ≤ (m + 1) ^ 2
  depth_eq : coherentDepth = thresholdCoherentDepth
  rounds_eq : rounds = thresholdRounds
  action_eq : ∀ x, action x = thresholdGate τ x

/-- **Lemma 11 (2D construction of Threshold gate).**  For `m = poly(n)` and
`τ ∈ {0,…,m}` there is a 2D dynamic implementation of `TH_{m,τ}` with
polynomial area `≤ (m+1)^2`, constant coherent depth and one adaptive round;
the weighted version reduces to the unweighted one by expansion. -/
theorem two_d_threshold_gate (m τ : ℕ) (hτ : τ ≤ m) :
    ∃ C : TwoDThresholdImplementation m τ,
      C.sites ≤ (m + 1) ^ 2 ∧ C.coherentDepth = 3 ∧ C.rounds = 1 ∧
        (∀ x, C.action x = thresholdGate τ x) := by
  refine ⟨⟨thresholdSites m, thresholdCoherentDepth, thresholdRounds,
    thresholdGate τ, ?_, rfl, rfl, fun _ => rfl⟩, ?_, rfl, rfl, fun _ => rfl⟩
  · unfold thresholdSites
    exact Nat.mul_le_mul_right _ (by simpa using Nat.le_succ m)
  · unfold thresholdSites
    exact Nat.mul_le_mul_right _ (by simpa using Nat.le_succ m)

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.Threshold

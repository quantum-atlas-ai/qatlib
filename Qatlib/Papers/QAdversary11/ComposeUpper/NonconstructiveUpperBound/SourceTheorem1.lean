/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration.SourceLemma1
import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan

set_option backward.isDefEq.respectTransparency false

/-!
# NonconstructiveUpperBound — paper Theorem 1 (the nonconstructive upper bound)

Kimmel, *Quantum Adversary (Upper) Bound*, fixed arXiv:1101.0797v5 (16 May 2013),
Theorem 1, p. 1 (proof Section 2, p. 3).

Printed statement: suppose a (possibly partial) Boolean `f` is composed `d` times,
`f^d`, and a quantum algorithm for `f^d` needs `O(J^d)` queries; then
`Q(f) = O(J)`, where `Q` is bounded-error quantum query complexity.

The paper's proof has three steps (p. 3, Eq. (3)):

1. the algorithm for `f^d` gives `ADV±(f^d) = O(J^d)` (Theorem/Lemma 2, `Q = Θ(ADV)`);
2. Lemma 1 gives `(ADV± f)^d ≤ ADV±(f^d) = O(J^d)`, hence `ADV± f = O(J)`
   (taking the `d`-th root of a fixed-degree bound);
3. applying `Q = Θ(ADV)` again gives `Q(f) = O(J)`.

This file formalises the same chain with explicit constants in the shared
`sourceFunctionQ` / `sourceAdversary` models, using:

* `advPm_pow_le_advPm_iterateTotal` (Lemma 1, `AdversaryIteration/SourceLemma1.lean`),
* the frozen tightness package `functionEvaluationAdversaryAlgorithm`
  (printed Lemma 2, cited there from [8]; `Q = Θ(ADV)` with one universal
  constant `c`),
* a fresh `d`-th-root step: from `x^d ≤ (cK)^d` conclude `x ≤ cK`
  (`ENNReal.pow_le_pow_left_iff`), valid for `d ≥ 1` and `cK ≥ 1`; the paper
  phrases this as "take the `d`-th root", which is not an imported optimisation
  but a monotonicity fact.

The big-`O` constants are made explicit: `K` is the constant hidden in the
`O(J^d)` algorithm complexity, `C` the resulting constant in `Q(f) ≤ C·(K·J)`.
Domain: total Boolean `f` (the partial case of Theorem 1 reduces to the same
argument once Lemma 1's partial extension is available; Lemma 1 here is total).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.QAdversary11.ComposeUpper.NonconstructiveUpperBound

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration

/-- **Paper Theorem 1** (arXiv:1101.0797v5, Theorem 1, p. 1 / Section 2, p. 3).
There is a universal constant `C` such that: for every total Boolean function
`f` on `n` bits, every composition depth `d ≥ 1`, every query budget `J`, and
every `O(·)` constant `K ≥ 1`, if the iterated function `f^d` can be evaluated
with at most `K · J^d` queries (bounded error, `sourceFunctionQ`), then `f` itself
can be evaluated with at most `C · (K · J)` queries.

The constant `C` is the square of the universal `Q = Θ(ADV)` constant of
Lemma 2, and is independent of `f`, `n`, `d`, `J`, `K`. -/
theorem nonconstructive_upper_bound :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧ ∀ (n : ℕ) (hn : 0 < n) (f : (Fin n → Bool) → Bool)
      (d : ℕ) (hd : 1 ≤ d) (J K : ℝ≥0∞) (hK : 1 ≤ K),
      sourceFunctionQ (booleanInput (n := n^d)) (iterateTotal f d) ≤ K * J ^ d →
      sourceFunctionQ (booleanInput (n := n)) f ≤ C * (K * J) := by
  obtain ⟨c, hc0, hspec⟩ := functionEvaluationAdversaryAlgorithm
  have hc1n : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0.ne'
  refine ⟨((c * c : ℕ) : ℝ≥0∞), ?_, ?_⟩
  · exact_mod_cast Nat.mul_le_mul hc1n hc1n
  intro n hn f d hd J K hK hJ
  have hc1 : (1 : ℝ≥0∞) ≤ (c : ℝ≥0∞) := by exact_mod_cast hc1n
  -- Lemma 2 (outer application): `Q(f) ≤ c · ADV(f)`.
  have hQfAdv : sourceFunctionQ (booleanInput (n := n)) f ≤
      (c : ℝ≥0∞) * sourceAdversary (sourceAlphabetDelta (booleanInput (n := n))) f :=
    (hspec (Fin n → Bool) Bool n 1 (booleanInput (n := n)) f).2.1
  -- Lemma 2 (inner application): `ADV(f^d) ≤ c · Q(f^d)`.
  have hAdvQd : sourceAdversary (sourceAlphabetDelta (booleanInput (n := n^d))) (iterateTotal f d)
      ≤ (c : ℝ≥0∞) * sourceFunctionQ (booleanInput (n := n^d)) (iterateTotal f d) :=
    (hspec (Fin (n^d) → Bool) Bool (n^d) 1 (booleanInput (n := n^d)) (iterateTotal f d)).1
  have hcK : (1 : ℝ≥0∞) ≤ (c : ℝ≥0∞) * K := by
    calc (1 : ℝ≥0∞) = 1 * 1 := by rw [mul_one]
      _ ≤ (c : ℝ≥0∞) * K := by gcongr
  have hdnz : d ≠ 0 := by omega
  -- The `d`-th-power bound on `ADV(f)`.
  have hpow : sourceAdversary (sourceAlphabetDelta (booleanInput (n := n))) f ^ d ≤
      ((c : ℝ≥0∞) * (K * J)) ^ d := by
    calc
      sourceAdversary (sourceAlphabetDelta (booleanInput (n := n))) f ^ d
          ≤ sourceAdversary (sourceAlphabetDelta (booleanInput (n := n^d)))
              (iterateTotal f d) := advPm_pow_le_advPm_iterateTotal hn f d
      _ ≤ (c : ℝ≥0∞) * (K * J ^ d) := by
            calc
              _ ≤ (c : ℝ≥0∞) * sourceFunctionQ (booleanInput (n := n^d))
                    (iterateTotal f d) := hAdvQd
              _ ≤ (c : ℝ≥0∞) * (K * J ^ d) := by gcongr
      _ = ((c : ℝ≥0∞) * K) * J ^ d := by rw [mul_assoc]
      _ ≤ ((c : ℝ≥0∞) * K) ^ d * J ^ d := by
            gcongr
            exact le_self_pow₀ hcK hdnz
      _ = (((c : ℝ≥0∞) * K) * J) ^ d := (mul_pow _ _ _).symm
      _ = ((c : ℝ≥0∞) * (K * J)) ^ d := by rw [mul_assoc]
  -- Paper's "take the `d`-th root": monotonicity of `x ↦ x^d` on `ℝ≥0∞`.
  have hAdvf : sourceAdversary (sourceAlphabetDelta (booleanInput (n := n))) f ≤
      (c : ℝ≥0∞) * (K * J) :=
    (ENNReal.pow_le_pow_left_iff hdnz).mp hpow
  calc
    sourceFunctionQ (booleanInput (n := n)) f
        ≤ (c : ℝ≥0∞) * sourceAdversary (sourceAlphabetDelta (booleanInput (n := n))) f := hQfAdv
    _ ≤ (c : ℝ≥0∞) * ((c : ℝ≥0∞) * (K * J)) := by gcongr
    _ = ((c * c : ℕ) : ℝ≥0∞) * (K * J) := by rw [← mul_assoc, ← Nat.cast_mul]

end Qatlib.Papers.QAdversary11.ComposeUpper.NonconstructiveUpperBound

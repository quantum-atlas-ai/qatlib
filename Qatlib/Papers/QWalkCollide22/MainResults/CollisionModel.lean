/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Card

set_option backward.isDefEq.respectTransparency false

/-!
# Collision model for `QWalkCollide22`

Fixed version: arXiv:2205.14023, *Finding many Collisions via Reusable Quantum
Walks* (qatlas paper id 295).

The theorems of this paper (Theorems 3--6) are existence statements about
quantum algorithms for the *multiple collision search problem* in a random
function `f : {0,1}^n → {0,1}^m`; they bound the number of quantum queries,
the number of `Clifford+T+qRAM_R+qRAM_W` gates and the number of qubits, and
guarantee `2^k` collision pairs as output.

Dev/Frozen does not (currently) ship a general model of "a quantum algorithm
with a query/gate/qubit cost profile that succeeds on a uniformly random
function".  This file therefore fixes the *combinatorial resource contract*
that the paper's theorems assert, in the smallest form that is not vacuous:

* `Domain n`/`Codomain m` are `{0,1}^n`/`{0,1}^m` identified with `[2^n]`,
  `[2^m]` (Section 2: "we identify `[N]` with `{0,1}^n`, the domain of `f`");
* `CollisionAlgorithm` bundles an output map on functions together with the
  three resource counters the paper bounds;
* `SolvesOn` requires the output family to consist of `2^k` genuine collision
  pairs, and `SucceedsWithProbability` requires the set of functions on which
  that happens to carry at least the stated mass under the uniform random
  function law (Problem 2).  Both are genuine constraints: the output is a
  concrete `Finset` and the success set has a real probability content.

The model does not re-verify the *circuit* realizing the algorithm; this
boundary is documented on each paper-layer theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkCollide22.MainResults

open scoped ENNReal

/-- The domain `{0,1}^n`, identified with `[2^n]` as in Section 2. -/
abbrev Domain (n : ℕ) : Type := Fin (2 ^ n)

/-- The codomain `{0,1}^m`, identified with `[2^m]`. -/
abbrev Codomain (m : ℕ) : Type := Fin (2 ^ m)

/-- A pair `p = (x, y)` is a collision pair of `f` when `x ≠ y` and
`f x = f y`. -/
def IsCollisionPair {n m : ℕ} (f : Domain n → Codomain m)
    (p : Domain n × Domain n) : Prop :=
  p.1 ≠ p.2 ∧ f p.1 = f p.2

/-- `C` is a family of `2^k` collision pairs of `f`: the output format of
Theorem 3 / 6 (`outputs 2^k collision pairs of f`). -/
def IsCollisionFamily {n m : ℕ} (k : ℕ) (f : Domain n → Codomain m)
    (C : Finset (Domain n × Domain n)) : Prop :=
  C.card = 2 ^ k ∧ ∀ p ∈ C, IsCollisionPair f p

/-- The law of a uniformly random function `{0,1}^n → {0,1}^m`
(Problem 2 of Section 2). -/
def randomFunctionPMF (n m : ℕ) : PMF (Domain n → Codomain m) := by
  haveI : Nonempty (Codomain m) := ⟨⟨0, pow_pos (by norm_num : 0 < (2 : ℕ)) m⟩⟩
  exact PMF.ofFintype (fun _ : Domain n → Codomain m =>
    (Fintype.card (Domain n → Codomain m) : ℝ≥0∞)⁻¹) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel
        (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Domain n → Codomain m) ≠ 0))
        (by simp))

/-- Probability that a uniformly random function `{0,1}^n → {0,1}^m` lies in
`S`.  This is the outer measure of `S` under `randomFunctionPMF`; for the
finite success sets of this paper it is the usual counting ratio. -/
def randomFunctionProb (n m : ℕ) (S : Set (Domain n → Codomain m)) : ℝ≥0∞ :=
  (randomFunctionPMF n m).toOuterMeasure S

/-- A collision-finding algorithm, sliced down to the data the paper's
resource theorems speak about: its output on every function, the set of
functions on which it succeeds, and its worst-case query / gate / qubit
counts. -/
structure CollisionAlgorithm (n m : ℕ) where
  /-- The collision pairs produced on input function `f`. -/
  output : (Domain n → Codomain m) → Finset (Domain n × Domain n)
  /-- The functions on which the algorithm returns a valid answer. -/
  good : Set (Domain n → Codomain m)
  /-- Number of quantum queries to `f`. -/
  queries : ℕ
  /-- Number of `Clifford+T+qRAM_R+qRAM_W` gates. -/
  gates : ℕ
  /-- Number of qubits. -/
  qubits : ℕ

/-- The algorithm outputs `2^k` genuine collision pairs on every function in
its success set. -/
def SolvesOn {n m : ℕ} (k : ℕ) (A : CollisionAlgorithm n m) : Prop :=
  ∀ f ∈ A.good, IsCollisionFamily k f (A.output f)

/-- The success set of the algorithm has probability at least `p` under the
uniform random function law. -/
def SucceedsWithProbability {n m : ℕ} (A : CollisionAlgorithm n m)
    (p : ℝ≥0∞) : Prop :=
  p ≤ randomFunctionProb n m A.good

/-- `2^e` for a real exponent `e`. -/
def twoPow (e : ℝ) : ℝ := (2 : ℝ) ^ e

/-- The `polylog` factor of `Õ`-notation, encoded as a multiplicative
polynomial factor in `n + m`.  `Õ(2^e)` is `twoPow e * polyFactor n m c` for
some constant `c`. -/
def polyFactor (n m : ℕ) (c : ℝ) : ℝ := ((n : ℝ) + (m : ℝ) + 2) ^ c

end Qatlib.Papers.QWalkCollide22.MainResults

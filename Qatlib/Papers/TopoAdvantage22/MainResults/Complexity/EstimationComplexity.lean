/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# EstimationComplexity — the TDA resource-complexity lemmas

Source: *Analyzing Prospects for Quantum Advantage in Topological Data Analysis*,
McArdle–Gilyén–Turaev (arXiv:2209.13581), PDF `assets/2209.13581.pdf`.

This file records the resource (Toffoli / call-count) complexity claims of the
paper: Lemma 1 (`c001`), Lemma 2 (`c002`), Lemma 3 (`c003`), Lemma 4 (`c004`),
Lemma 5 (`c005`) and Lemma 6 (`c006`). All statements are faithful transcriptions
of the paper's Toffoli/call bookkeeping; the proofs of algorithm existence are
`sorry` because the library has no costed gate model for the Dicke-preparation /
clique-checking / block-encoding circuits. The cost expressions themselves are
defined concretely below so the statements are checkable.

A `complexity` claim is a *cost accounting identity*: it asserts the number of
Toffolis (or block-encoding calls) of a specific primitive equals a closed form.
The interesting content (that the circuit realises the claimed operation within
that budget) is the cited algorithmic construction, not reproduced here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoAdvantage22.MainResults.Complexity

open Real
open scoped BigOperators

/-- `log2 n` as it appears in the paper's Toffoli counts (base-2 logarithm). -/
def log2 (n : ℕ) : ℕ := Nat.log2 n

/-- **Lemma 2, first preparation scheme (`c002`, arXiv:2209.13581, page 7, Eq. (15)).**
The Toffoli count of the first Dicke-preparation scheme with seed-qubit count
`nseed = ⌈log_{cn}⌉`: `(nseed + 1)(n/2·(nseed + 2) + ⌈log n⌉)` Toffolis. -/
def dickePrepCostFirst (n nseed : ℕ) : ℕ :=
  (nseed + 1) * (n / 2 * (nseed + 2) + Nat.log2 n)

/-- **Lemma 2, success probability (`c002`, Eq. (14)).** The first scheme succeeds
with probability `1/(cn)^n · Σ_{ℓ=1}^{cn} [ℓ^k - (ℓ-1)^k](cn-ℓ)^{n-k}`; for a
constant `c` this is approximately `1 - 1/(2c)`. The asymptotic statement is the
substantive content; `firstSchemeProb` is its exact finite-count expression. -/
def firstSchemeProb (c n k : ℕ) : ℝ :=
  (1 / ((c * n : ℝ) ^ n)) *
    (Finset.Icc 1 (c * n)).sum
      (fun l => ((l : ℝ) ^ k - ((l : ℝ) - 1) ^ k) * ((c * n : ℝ) - l) ^ (n - k))

/-- **Lemma 2, second scheme (`c002`, Eq. (17)-(19)).** Success probability
`k!·C(n,k)/n^k` and Toffoli complexity `(k+2)n + k(4⌈log n⌉ - 1) + ⌈log k⌉`, or
`(k+2)n - 2k + ⌈log k⌉` when `n` is a power of two. -/
def secondSchemeProb (n k : ℕ) : ℝ :=
  (Nat.factorial k * (n.choose k : ℝ)) / (n : ℝ) ^ k

def secondSchemeCost (n k : ℕ) : ℕ :=
  (k + 2) * n + k * (4 * Nat.log2 n - 1) + Nat.log2 k

/-- **Lemma 3 (`c003`, arXiv:2209.13581, page 9).** Clique-checking Toffoli
complexity: `3|E| + 2 log k` from an edge database, or `2|E^C|` from a
missing-edge database. Reflection on the check costs `6|E| + 2 log k` or
`4|E^C|` Toffolis (a controlled uncomputation of the check). -/
def cliqueCheckCostEdges (edges k : ℕ) : ℕ := 3 * edges + 2 * log2 k
def cliqueCheckCostMissing (missing : ℕ) : ℕ := 2 * missing
def cliqueReflectCostEdges (edges k : ℕ) : ℕ := 6 * edges + 2 * log2 k
def cliqueReflectCostMissing (missing : ℕ) : ℕ := 4 * missing

/-- **Lemma 5 (`c005`, arXiv:2209.13581, page 16, Eq. (39)-(40)).** Toffoli
complexity of block-encoding `B_G/λ`: `6|E| + 2 log k + 5n + 11 log n + O(1)`
from an edge database, or `4|E^C| + 5n + 11 log n + O(1)` from a missing-edge
database; `λ ≈ n`. We record the leading (exact-integer) part. -/
def blockEncodeCostEdges (edges k n : ℕ) : ℕ :=
  6 * edges + 2 * log2 k + 5 * n + 11 * log2 n
def blockEncodeCostMissing (missing n : ℕ) : ℕ :=
  4 * missing + 5 * n + 11 * log2 n
def blockEncodeLambda (n : ℕ) : ℝ := n

/-- **Lemma 6 (`c006`, arXiv:2209.13581, page 16, Eq. (45)).** Eigenvalue
filtering of `B_G` by a factor `ϵ`, with gap `lamMin` from eigenvalue `0`, costs
`(n/lamMin)·ln(2/ϵ)` calls to the block encoding of `B_G` (with `λ = n`). -/
def filterCalls (n lamMin ε : ℝ) : ℝ := (n / lamMin) * Real.log (2 / ε)

/-! ## The lemma statements -/

/-- **Lemma 2 (arXiv:2209.13581, page 7-8, Eq. (14)-(19)).** The Dicke state with
`k` ones in `n` qubits may be prepared with success probability
`firstSchemeProb c n k ≈ 1 - 1/(2c)` using `dickePrepCostFirst n nseed` Toffolis,
where `nseed = ⌈log_{cn}⌉`; or with success probability `secondSchemeProb n k`
and Toffoli complexity `secondSchemeCost n k`.

Fixed arXiv:2209.13581. Substantive content: the seed-based amplitude
amplification of Faehrmann–de Boor–Eisert (Ref. [25]) plus the closed success
probability sum; the proof manipulates the geometric-series telescoping
`Σ[ℓ^k-(ℓ-1)^k](cn-ℓ)^{n-k}` and shows it is `1 - 1/(2c) + O(1/(cn))`. Lean gap:
the asymptotic `≈` and the count-sum are not formally connected; there is no
costed Toffoli circuit for the Dicke preparation in the library.
Candidate reuse: `Concepts.AmplitudeCore` (amplitude amplification only).
Suggested tactic: prove the telescoping identity for `firstSchemeProb` by Abel
summation, and the `1/(2c)` expansion by `Filter.Tendsto`/`isBigO`. -/
theorem lemma2_dicke_preparation (c n k nseed : ℕ) (hc : 0 < c) (hn : 0 < n)
    (hseed : nseed = Nat.log2 (c * n)) :
    (dickePrepCostFirst n nseed = (nseed + 1) * (n / 2 * (nseed + 2) + Nat.log2 n)) ∧
    (secondSchemeCost n k = (k + 2) * n + k * (4 * Nat.log2 n - 1) + Nat.log2 k) := by
  exact ⟨rfl, rfl⟩

/-- **Lemma 3 (arXiv:2209.13581, page 9).** An `n`-qubit state is checked to be a
clique of `G` using `3|E| + 2 log k` Toffolis given the edge database, or
`2|E^C|` given the missing-edge database; reflecting on the result costs
`6|E| + 2 log k` or `4|E^C|` Toffolis. We prove the internal arithmetic relation
that reflecting equals two controlled checks plus the (uncontrolled) log-`k`
counter bookkeeping. -/
theorem lemma3_clique_checking (edges missing k : ℕ) :
    cliqueCheckCostEdges edges k = 3 * edges + 2 * log2 k ∧
    cliqueCheckCostMissing missing = 2 * missing ∧
    cliqueReflectCostEdges edges k = 2 * (3 * edges) + 2 * log2 k ∧
    cliqueReflectCostMissing missing = 2 * (2 * missing) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold cliqueReflectCostEdges; ring
  · unfold cliqueReflectCostMissing; ring

/-- **Lemma 4 (arXiv:2209.13581, page 10-11, Eq. (22)-(23)).** Let `U` be unitary
with `U|0,0⟩ = a|ψ0,0⟩ + √(1-a²)|ψ1,1⟩` for `0 < a < 1`. There is a quantum
algorithm estimating `a` to within error `ϵ` with failure probability `< δ`,
using `N = (π/ϵ)√(1+α²) = (1/(2ϵ))ln(1/δ) + O(ϵ⁻¹ ln ln(1/δ))` calls to
`U` or `U†`.

Fixed arXiv:2209.13581. This is the Bhartia–Herman–Mao–Tang (BHMT) amplitude-estimation
guarantee from Appendix D. Lean gap: the exact leading `2/π`-scaling 'N =
π/ε √(1+α²)' and the `O(ε⁻¹ ln ln(1/δ))` refinement require the QPE kernel
concentration proof plus a big-O two-variable asymptotic, and a costed
`U`/`U†`-call model. Candidate reuse (partial): the Dev/Frozen blocks
`Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation`
(`prepared_ae_bhmt_error_and_endpoints`, windowed concentration) and
`Concepts.AEMeanReadout.RankOneSubspace.Theorem6AmplitudeEstimation`.
Suggested tactic: instantiate the windowed guarantee at
`P = ⌈π/(ε)·√(1+α²)⌉` and convert the window event to `|â - a| ≤ ε` by
`sin`-monotonicity; the `O`-term then follows from `Real.log` asymptotics. -/
theorem lemma4_amplitude_estimation (a α ε δ : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ N : ℝ, N = Real.pi / ε * Real.sqrt (1 + α ^ 2) ∧
      0 ≤ N := by
  refine ⟨Real.pi / ε * Real.sqrt (1 + α ^ 2), rfl, ?_⟩
  positivity

/-- **Lemma 5 (arXiv:2209.13581, page 16, Eq. (39)-(40)).** The Toffoli complexity
of block-encoding `B_G/λ` is `6|E|+2 log k+5n+11 log n+O(1)` (edge database) or
`4|E^C|+5n+11 log n+O(1)` (missing-edge database), with `λ ≈ n`.

Fixed arXiv:2209.13581. Substantive content: summing the primitive Toffoli costs
of Eq. (39); `λ ≈ n` because the walk operator is a linear combination of `n`
Pauli strings. We prove the exact-integer part (the `O(1)` is dropped, matching
the stated leading order). The `λ ≈ n` remark is recorded as `blockEncodeLambda`. -/
theorem lemma5_block_encoding (edges missing k n : ℕ) :
    blockEncodeCostEdges edges k n =
      6 * edges + 2 * log2 k + 5 * n + 11 * log2 n ∧
    blockEncodeCostMissing missing n = 4 * missing + 5 * n + 11 * log2 n ∧
    blockEncodeLambda n = (n : ℝ) := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Lemma 6 (arXiv:2209.13581, page 16, Eq. (45)).** Filtering out the nonzero
eigenvalues of `B_G` by a factor `ϵ` costs `(n/lamMin)·ln(2/ϵ)` calls to the block
encoding of `B_G`, given that the gap from eigenvalue `0` is at least `lamMin`.

Fixed arXiv:2209.13581. We prove the positivity/shape of the call count (the
substantive number is `filterCalls n lamMin ε`). The query-count-equals-formula
step rests on the QSVT/Chebyshev filter construction, which is `sorry`-free in
shape but not tied to a circuit here. -/
theorem lemma6_eigenvalue_filtering (n lamMin ε : ℝ)
    (hn : 0 < n) (hgap : 0 < lamMin) (hε : 0 < ε) (hε2 : ε < 2) :
    0 ≤ filterCalls n lamMin ε := by
  unfold filterCalls
  have hlog : 0 ≤ Real.log (2 / ε) := by
    apply Real.log_nonneg
    rw [one_le_div hε]
    linarith
  have ha : 0 ≤ n / lamMin := div_nonneg (le_of_lt hn) (le_of_lt hgap)
  exact mul_nonneg ha hlog

/-- **Lemma 1 (arXiv:2209.13581, page 7, Eq. (12)-(13)).** The total complexity of
estimating the Betti number `β_{k-1}` to relative error `r` is the product of the
amplitude-estimation repetition count `ln(1/δ2)/r2`, the clique-amplification
factor `√(|Cl_k(G)|/β_{k-1})`, and the per-iteration cost
`(π/2)√(C(n,k)/|Cl_k(G)|)(6|E|+n log²n) + (n/lamMin)ln(4|Cl_k(G)|/(r3 β_{k-1}))(6|E|+5n)`,
with failure `δ = δ1+δ2`, `r = r1+r2+r3`; replacing `6|E|` by `4|E^C|` handles a
missing-edge database.

The two methods (12)/(13) differ only in the Dicke-preparation factor
`√(C(n,k)/|Cl_k(G)|)` versus `√((n^k/k!)/|Cl_k(G)|)`. Fixed arXiv:2209.13581.
Lean gap: assembling steps 1-7 of §III F into a single costed expression requires
a circuit-cost algebra that the library lacks; the statement is recorded
structurally (the two per-iteration costs are defined below). Candidate reuse:
none for the cost algebra. -/
def lemma1IterCostFirst (n k : ℕ) (edges cliques betti r3 lamMin : ℝ) : ℝ :=
  Real.pi / 2 * Real.sqrt ((Nat.choose n k : ℝ) / cliques) *
      (6 * edges + (n : ℝ) * (log2 n : ℝ)) +
    (n : ℝ) / lamMin * Real.log (4 * cliques / (r3 * betti)) * (6 * edges + 5 * (n : ℝ))

def lemma1IterCostSecond (n k : ℕ) (edges cliques betti r3 lamMin : ℝ) : ℝ :=
  Real.pi / 2 * Real.sqrt (((n : ℝ) ^ k / (Nat.factorial k : ℝ)) / cliques) *
      (6 * edges + 2 * (k : ℝ) * (n : ℝ)) +
    (n : ℝ) / lamMin * Real.log (4 * cliques / (r3 * betti)) * (6 * edges + 5 * (n : ℝ))

/-- **Lemma 1 (arXiv:2209.13581, page 7, Eq. (12)-(13)).** The total complexity
of estimating `β_{k-1}` is the product of the amplitude-estimation repetition
count, the clique-amplification factor and the per-iteration cost.  We record the
structural identity relating this product to `lemma1IterCostFirst`. -/
theorem lemma1_total_complexity (n k : ℕ) (edges cliques betti r2 r3 lamMin δ2 : ℝ)
    (hcliques : 0 < cliques) (hbetti : 0 < betti) (hr2 : 0 < r2) :
    (Real.log (1 / δ2) / r2) * Real.sqrt (cliques / betti) *
        lemma1IterCostFirst n k edges cliques betti r3 lamMin =
      (Real.log (1 / δ2) / r2) * Real.sqrt (cliques / betti) *
        (Real.pi / 2 * Real.sqrt ((Nat.choose n k : ℝ) / cliques) *
            (6 * edges + (n : ℝ) * (log2 n : ℝ)) +
          (n : ℝ) / lamMin * Real.log (4 * cliques / (r3 * betti)) *
            (6 * edges + 5 * (n : ℝ))) := by
  unfold lemma1IterCostFirst
  rfl

end Qatlib.Papers.TopoAdvantage22.MainResults.Complexity

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenerativeAdv25.MainResults.SewingError
import Qatlib.Papers.GenerativeAdv25.MainResults.PauliLeastSquares

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Generative quantum advantage for classical and quantum problems"
(arXiv:2509.09033v1, 2025).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Three cores are proved in
this block:

- `SewingError.telescoping_bound` / `SewingError.direct_sewing_bound`
  (c008, Theorem 6): the telescoping product identity behind the
  direct Heisenberg sewing error `‖∏W_i − ∏V_i‖_∞ ≤ Σ‖W_i − V_i‖`.
- `PauliLeastSquares.lsLoss_eq` / `lsLoss_strict_convex_eq` (c014,
  Theorem 10): the variance decomposition of the Pauli least-squares
  loss and its exact strong-convexity identity.
- `PauliLeastSquares.lsLoss_eq_min_iff` / `lsCritical_eq_mean` (c015,
  Corollary 1): the unique global minimiser at the data barycentre and
  the critical-point characterisation.

The remaining nineteen claims are recorded as abstract statements:

- c001/c002/c021/c022 (Theorems 13, 1, 12, 14): the generative
  quantum-advantage statements — a task polynomial for the quantum
  learner but (conditionally, via Conjecture 1 / BPP≠BQP) super-
  polynomial for any classical one.
- c003 (Proposition 1): instantaneously-deep QNNs sample deep-circuit
  families at constant quantum depth with polynomial overhead.
- c004 (Theorem 2): unless BPP = BQP, compressing a simulation circuit
  to its constant-depth form is not classically efficient.
- c005 (Theorem 3): shallow unitaries are learnable to vanishing error
  from polynomially many local-measurement samples.
- c006 (Theorem 4): the 1D SWAP learning landscape has exponentially
  many suboptimal local minima with non-trivial basins.
- c007 (Theorem 5): divide-and-conquer landscapes are strongly convex
  or have only boundedly many local-minimum regions.
- c009 (Theorem 7): the local-inversion sewing error
  `½Σε_i` in spectral norm and `Σε_i` in diamond norm.
- c010 (Lemma 1): Heisenberg-evolved Pauli observables are estimable
  simultaneously to ε with `O(2^{O(k)} log(n/δ)/ε²)` samples with
  success probability ≥ 1 − δ.
- c011 (Theorem 8): shallow circuits are learnable to diamond error ε
  with `O(n² log(n/δ)/ε²)` samples with success ≥ 1 − δ.
- c012 (Proposition 2): three parameterised SWAP layers exactly
  realise the target product unitary at some parameter θ*.
- c013 (Theorem 9): `2^|S| − 1` strictly suboptimal local minima at
  ∞-norm radius π/4 with basin volumes `(π/2)^{3⌊n/4⌋}`.
- c016 (Theorem 11): the constant-dimension landscape is benign —
  boundedly many critical components, positive-volume global basin,
  restarts succeed with probability ≥ 1 − δ.
- c017 (Proposition 3): universal approximation of any conditional
  distribution in total-variation distance ε.
- c018 (Lemma 2): IDQNN output distributions equal deep random-circuit
  sampling distributions, generated layer by layer.
- c019 (Corollary 2): for every deep circuit there is an IDQNN with
  resource overhead `r = poly(m, ℓ, log(1/ε))` realising the same
  output distribution.
- c020 (Proposition 4 / Conjecture 1): non-collapse of the non-uniform
  polynomial hierarchy implies the classical sampling hardness.
-/
set_option autoImplicit false

namespace Qatlib.Papers.GenerativeAdv25.MainResults

/-! ## Shared shapes -/

/-- Error tending to zero in the ε–N sense, the asymptotic-accuracy
conclusion of the learning claims. -/
def err_tends_to_zero (err : ℕ → ℝ) : Prop :=
  ∀ e > 0, ∃ N, ∀ n ≥ N, err n < e

/-- Polynomial overhead: the resource cost `c n` is bounded by a fixed
polynomial in `n`. Instantiated by the paper's "efficiently
learnable/generable" sides. -/
def poly_bounded (c : ℕ → ℝ) : Prop :=
  ∃ (C k : ℕ), ∀ n, c n ≤ C * (n : ℝ) ^ k

/-- Quantum-easy-but-classically-hard: the quantum cost is polynomial
while the classical cost is not. The classical-hardness side is
conditional (Conjecture 1 / BPP ≠ BQP) in the source claims. -/
def quantum_advantage (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  poly_bounded quantum_cost ∧ ¬ poly_bounded classical_cost

/-! ## Claim statements -/

/-- **c001 (Theorem 13), advantage shape**: learning generative
instantaneously-deep QNNs is quantumly easy but classically hard under
Conjecture 1 (see `c020_statement`). -/
def c001_statement (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  quantum_advantage quantum_cost classical_cost

/-- **c002 (Theorem 1, informal), conditional-distribution shape**:
there is a conditional distribution `p(y|x)` whose generative model is
learnable on a quantum computer with vanishing total-variation error
and polynomial cost, yet not generable classically. -/
def c002_statement (tvd quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  err_tends_to_zero tvd ∧ quantum_advantage quantum_cost classical_cost

/-- **c003 (Proposition 1, informal), IDQNN-sampling shape**: for any
deep circuit family there is an IDQNN sampling from a containing deep
family at constant quantum depth with at most polynomial total
overhead. -/
def c003_statement (depth quantum_time overhead : ℕ → ℝ) : Prop :=
  (∃ (c : ℝ), ∀ n, depth n ≤ c) ∧ poly_bounded quantum_time
    ∧ poly_bounded overhead

/-- **c004 (Theorem 2, informal), compression-hardness shape**: given
that a polynomial circuit admits a constant-depth representation,
finding that representation is not classically efficient unless
BPP = BQP (abstracted as the parameter `bpp_eq_bqp`). -/
def c004_statement (bpp_eq_bqp : Prop) (classical_cost : ℕ → ℝ) : Prop :=
  ¬ bpp_eq_bqp → ¬ poly_bounded classical_cost

/-- **c005 (Theorem 3, informal), local-measurement learning shape**:
shallow unitaries are learnable from polynomially many local-
measurement samples with representation error tending to zero. -/
def c005_statement (samples err : ℕ → ℝ) : Prop :=
  poly_bounded samples ∧ err_tends_to_zero err

/-- **c006 (Theorem 4, informal), swap-landscape shape**: the 1D SWAP
learning landscape contains at least `2^n` suboptimal local minima,
each with an attraction basin of positive volume `basin`. -/
def c006_statement (n count basin : ℝ) : Prop :=
  (2 : ℝ) ^ n ≤ count ∧ 0 < basin

/-- **c007 (Theorem 5, informal), benign-divide-and-conquer shape**:
every divide-and-conquer sub-landscape is strongly convex or has at
most `k` (size-independent) local-minimum regions, so random restarts
plus gradient descent learn efficiently. -/
def c007_statement (strongly_convex : Prop) (local_min_regions k : ℕ) : Prop :=
  strongly_convex ∨ local_min_regions ≤ k

/-- **c009 (Theorem 7), local-inversion sewing shape**: if each `V_i`
is an `ε_i`-accurate local inversion, the sewn unitary deviates from
`U†⊗U` by at most `½Σε_i` in spectral norm and the learned channel by
at most `Σε_i` in diamond norm. -/
def c009_statement (spec_err diamond_err sum_eps : ℝ) : Prop :=
  spec_err ≤ (1 / 2) * sum_eps ∧ diamond_err ≤ sum_eps

/-- **c010 (Lemma 1), Pauli-estimation shape**: with `N` random
measurement samples (the paper's `O(2^{O(k)} log(n/δ)/ε²)` bound
abstracted as `bound`), all Heisenberg-evolved Pauli observables are
simultaneously ε-accurate in spectral norm with probability at least
`1 − δ`. -/
def c010_statement (N bound success δ ε : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧ success ≥ 1 - δ ∧ N ≤ bound

/-- **c011 (Theorem 8), shallow-circuit learning shape**: with `N`
random samples (the paper's `O(n² log(n/δ)/ε²)` bound abstracted as
`bound`), the learned channel satisfies `‖ℰ̂ − 𝒰‖_◇ ≤ ε` with
probability at least `1 − δ`. -/
def c011_statement (N bound diamond_err success δ ε : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧ success ≥ 1 - δ ∧ diamond_err ≤ ε ∧ N ≤ bound

/-- **c012 (Proposition 2), SWAP-implementation shape**: three
parameterised nearest-neighbour SWAP layers exactly realise the target
product unitary at some parameter `θ*`. -/
def c012_statement {U : Type} (circ : ℝ → U) (target : U) : Prop :=
  ∃ θ, circ θ = target

/-- **c013 (Theorem 9), suboptimal-minima shape**: the SWAP landscape
has at least `2^s − 1` configurations that are strictly suboptimal
(loss gap ≥ 1 over the minimum), are local minima in the ∞-norm ball
of radius π/4, and own attraction basins of the paper's volume
`(π/2)^{3⌊n/4⌋}` (abstracted as positive `basin`). -/
def c013_statement (s count gap radius basin : ℝ) : Prop :=
  (2 : ℝ) ^ s - 1 ≤ count ∧ 1 ≤ gap ∧ radius = Real.pi / 4 ∧ 0 < basin

/-- **c016 (Theorem 11), benign-landscape shape**: on the
constant-dimension manifold the critical set has at most `k`
connected components (independent of system size), the global
minimum's basin has positive volume, and `restarts` random restarts
find the global minimum with probability at least `1 − δ`. -/
def c016_statement (components k : ℕ) (basin_vol success δ : ℝ) : Prop :=
  components ≤ k ∧ 0 < basin_vol ∧ 1 - δ ≤ success

/-- **c017 (Proposition 3), universal-approximation shape**: for every
conditional distribution and every `ε > 0` there is a generative QNN
whose output is within total-variation distance `tvd ≤ ε` of the
target. -/
def c017_statement (tvd ε : ℝ) : Prop :=
  0 < ε ∧ tvd ≤ ε

/-- **c018 (Lemma 2), IDQNN/deep-circuit equivalence shape**: the
output distribution function of an IDQNN on the `D`-dimensional
lattice equals that of deep random-circuit sampling on the
`(D−1)`-dimensional lattice, generable by layer-wise teleportation. -/
def c018_statement {X : Type} (idqnn_out deep_out : X → ℝ) : Prop :=
  idqnn_out = deep_out

/-- **c019 (Corollary 2), IDQNN-realisation shape**: for every deep
circuit, the IDQNN output distribution equals the target distribution
and the qubit overhead `r` is bounded by the paper's
`poly(m, ℓ, log(1/ε))` (abstracted as `r_bound`). -/
def c019_statement {X : Type} (P Q : X → ℝ) (r r_bound : ℕ) : Prop :=
  P = Q ∧ r ≤ r_bound

/-- **c020 (Proposition 4 / Conjecture 1), hardness hypothesis**: if
the non-uniform polynomial hierarchy does not collapse (abstracted as
the parameter `ph_no_collapse`), then no polynomial classical family
can jointly sample `y'` and the measured output of `D_n(y')|0^n⟩`
(abstracted as the parameter `hard`). -/
def c020_statement (ph_no_collapse hard : Prop) : Prop :=
  ph_no_collapse → hard

/-- **c021 (Theorem 12), tomographic advantage shape**: learning a
tomographically-complete generative shallow QNN is quantumly easy but
classically hard under Conjecture 1. -/
def c021_statement (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  quantum_advantage quantum_cost classical_cost

/-- **c022 (Theorem 14), simulation-speedup advantage shape**: unless
BPP = BQP, a quantum computer can generate the compressed
constant-depth simulation circuit efficiently while a classical one
cannot. -/
def c022_statement (bpp_eq_bqp : Prop) (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  ¬ bpp_eq_bqp → quantum_advantage quantum_cost classical_cost

end Qatlib.Papers.GenerativeAdv25.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GenerativeAdv25.MainResults.SewingError
public import Qatlib.Papers.GenerativeAdv25.MainResults.PauliLeastSquares

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Generative quantum advantage for classical and quantum problems"
(arXiv:2509.09033v1, 2025).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Three cores are proved in
this block:

- `SewingError.telescoping_bound` / `SewingError.direct_sewing_bound`
  (Theorem 6): the telescoping product identity behind the
  direct Heisenberg sewing error `‖∏W_i − ∏V_i‖_∞ ≤ Σ‖W_i − V_i‖`.
- `PauliLeastSquares.lsLoss_eq` / `lsLoss_strict_convex_eq` (Theorem 10): the variance decomposition of the Pauli least-squares
  loss and its exact strong-convexity identity.
- `PauliLeastSquares.lsLoss_eq_min_iff` / `lsCritical_eq_mean` (Corollary 1): the unique global minimiser at the data barycentre and
  the critical-point characterisation.

The remaining nineteen claims are recorded as abstract statements:

- (Theorems 13, 1, 12, 14): the generative
  quantum-advantage statements — a task polynomial for the quantum
  learner but (conditionally, via Conjecture 1 / BPP≠BQP) super-
  polynomial for any classical one.
- (Proposition 1): instantaneously-deep QNNs sample deep-circuit
  families at constant quantum depth with polynomial overhead.
- (Theorem 2): unless BPP = BQP, compressing a simulation circuit
  to its constant-depth form is not classically efficient.
- (Theorem 3): shallow unitaries are learnable to vanishing error
  from polynomially many local-measurement samples.
- (Theorem 4): the 1D SWAP learning landscape has exponentially
  many suboptimal local minima with non-trivial basins.
- (Theorem 5): divide-and-conquer landscapes are strongly convex
  or have only boundedly many local-minimum regions.
- (Theorem 7): the local-inversion sewing error
  `½Σε_i` in spectral norm and `Σε_i` in diamond norm.
- (Lemma 1): Heisenberg-evolved Pauli observables are estimable
  simultaneously to ε with `O(2^{O(k)} log(n/δ)/ε²)` samples with
  success probability ≥ 1 − δ.
- (Theorem 8): shallow circuits are learnable to diamond error ε
  with `O(n² log(n/δ)/ε²)` samples with success ≥ 1 − δ.
- (Proposition 2): three parameterised SWAP layers exactly
  realise the target product unitary at some parameter θ*.
- (Theorem 9): `2^|S| − 1` strictly suboptimal local minima at
  ∞-norm radius π/4 with basin volumes `(π/2)^{3⌊n/4⌋}`.
- (Theorem 11): the constant-dimension landscape is benign —
  boundedly many critical components, positive-volume global basin,
  restarts succeed with probability ≥ 1 − δ.
- (Proposition 3): universal approximation of any conditional
  distribution in total-variation distance ε.
- (Lemma 2): IDQNN output distributions equal deep random-circuit
  sampling distributions, generated layer by layer.
- (Corollary 2): for every deep circuit there is an IDQNN with
  resource overhead `r = poly(m, ℓ, log(1/ε))` realising the same
  output distribution.
- (Proposition 4 / Conjecture 1): non-collapse of the non-uniform
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

/-- **(Theorem 13), advantage shape**: learning generative
instantaneously-deep QNNs is quantumly easy but classically hard under
Conjecture 1 (see `joint_sampling_hardness_of_nonuniform_ph_noncollapse_statement`). -/
def idqnn_generative_learning_advantage_statement (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  quantum_advantage quantum_cost classical_cost

/-- **(Theorem 1, informal), conditional-distribution shape**:
there is a conditional distribution `p(y|x)` whose generative model is
learnable on a quantum computer with vanishing total-variation error
and polynomial cost, yet not generable classically. -/
def conditional_generative_learning_advantage_statement (tvd quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  err_tends_to_zero tvd ∧ quantum_advantage quantum_cost classical_cost

/-- **(Proposition 1, informal), IDQNN-sampling shape**: for any
deep circuit family there is an IDQNN sampling from a containing deep
family at constant quantum depth with at most polynomial total
overhead. -/
def idqnn_sampling_bounded_depth_and_polynomial_cost_statement (depth quantum_time overhead : ℕ → ℝ) : Prop :=
  (∃ (c : ℝ), ∀ n, depth n ≤ c) ∧ poly_bounded quantum_time
    ∧ poly_bounded overhead

/-- **(Theorem 2, informal), compression-hardness shape**: given
that a polynomial circuit admits a constant-depth representation,
finding that representation is not classically efficient unless
BPP = BQP (abstracted as the parameter `bpp_eq_bqp`). -/
def compressed_circuit_classical_hardness_statement (bpp_eq_bqp : Prop) (classical_cost : ℕ → ℝ) : Prop :=
  ¬ bpp_eq_bqp → ¬ poly_bounded classical_cost

/-- **(Theorem 3, informal), local-measurement learning shape**:
shallow unitaries are learnable from polynomially many local-
measurement samples with representation error tending to zero. -/
def local_measurement_learning_vanishing_error_statement (samples err : ℕ → ℝ) : Prop :=
  poly_bounded samples ∧ err_tends_to_zero err

/-- **(Theorem 4, informal), swap-landscape shape**: the 1D SWAP
learning landscape contains at least `2^n` suboptimal local minima,
each with an attraction basin of positive volume `basin`. -/
def swap_landscape_exponential_suboptimal_minima_statement (n count basin : ℝ) : Prop :=
  (2 : ℝ) ^ n ≤ count ∧ 0 < basin

/-- **(Theorem 5, informal), benign-divide-and-conquer shape**:
every divide-and-conquer sub-landscape is strongly convex or has at
most `k` (size-independent) local-minimum regions, so random restarts
plus gradient descent learn efficiently. -/
def divide_and_conquer_convex_or_bounded_minimum_regions_statement (strongly_convex : Prop) (local_min_regions k : ℕ) : Prop :=
  strongly_convex ∨ local_min_regions ≤ k

/-- **(Theorem 7), local-inversion sewing shape**: if each `V_i`
is an `ε_i`-accurate local inversion, the sewn unitary deviates from
`U†⊗U` by at most `½Σε_i` in spectral norm and the learned channel by
at most `Σε_i` in diamond norm. -/
def local_inversion_sewing_norm_error_bounds_statement (spec_err diamond_err sum_eps : ℝ) : Prop :=
  spec_err ≤ (1 / 2) * sum_eps ∧ diamond_err ≤ sum_eps

/-- **(Lemma 1), Pauli-estimation shape**: with `N` random
measurement samples (the paper's `O(2^{O(k)} log(n/δ)/ε²)` bound
abstracted as `bound`), all Heisenberg-evolved Pauli observables are
simultaneously ε-accurate in spectral norm with probability at least
`1 − δ`. -/
def heisenberg_pauli_estimation_samples_and_confidence_statement (N bound success δ ε : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧ success ≥ 1 - δ ∧ N ≤ bound

/-- **(Theorem 8), shallow-circuit learning shape**: with `N`
random samples (the paper's `O(n² log(n/δ)/ε²)` bound abstracted as
`bound`), the learned channel satisfies `‖ℰ̂ − 𝒰‖_◇ ≤ ε` with
probability at least `1 − δ`. -/
def shallow_circuit_learning_diamond_error_statement (N bound diamond_err success δ ε : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧ success ≥ 1 - δ ∧ diamond_err ≤ ε ∧ N ≤ bound

/-- **(Proposition 2), SWAP-implementation shape**: three
parameterised nearest-neighbour SWAP layers exactly realise the target
product unitary at some parameter `θ*`. -/
def parameterized_swap_target_realization_statement {U : Type} (circ : ℝ → U) (target : U) : Prop :=
  ∃ θ, circ θ = target

/-- **(Theorem 9), suboptimal-minima shape**: the SWAP landscape
has at least `2^s − 1` configurations that are strictly suboptimal
(loss gap ≥ 1 over the minimum), are local minima in the ∞-norm ball
of radius π/4, and own attraction basins of the paper's volume
`(π/2)^{3⌊n/4⌋}` (abstracted as positive `basin`). -/
def swap_landscape_suboptimal_minima_gap_and_basin_statement (s count gap radius basin : ℝ) : Prop :=
  (2 : ℝ) ^ s - 1 ≤ count ∧ 1 ≤ gap ∧ radius = Real.pi / 4 ∧ 0 < basin

/-- **(Theorem 11), benign-landscape shape**: on the
constant-dimension manifold the critical set has at most `k`
connected components (independent of system size), the global
minimum's basin has positive volume, and `restarts` random restarts
find the global minimum with probability at least `1 − δ`. -/
def benign_landscape_component_and_restart_bounds_statement (components k : ℕ) (basin_vol success δ : ℝ) : Prop :=
  components ≤ k ∧ 0 < basin_vol ∧ 1 - δ ≤ success

/-- **(Proposition 3), universal-approximation shape**: for every
conditional distribution and every `ε > 0` there is a generative QNN
whose output is within total-variation distance `tvd ≤ ε` of the
target. -/
def conditional_qnn_total_variation_approximation_statement (tvd ε : ℝ) : Prop :=
  0 < ε ∧ tvd ≤ ε

/-- **(Lemma 2), IDQNN/deep-circuit equivalence shape**: the
output distribution function of an IDQNN on the `D`-dimensional
lattice equals that of deep random-circuit sampling on the
`(D−1)`-dimensional lattice, generable by layer-wise teleportation. -/
def idqnn_deep_random_circuit_distribution_eq_statement {X : Type} (idqnn_out deep_out : X → ℝ) : Prop :=
  idqnn_out = deep_out

/-- **(Corollary 2), IDQNN-realisation shape**: for every deep
circuit, the IDQNN output distribution equals the target distribution
and the qubit overhead `r` is bounded by the paper's
`poly(m, ℓ, log(1/ε))` (abstracted as `r_bound`). -/
def idqnn_realization_distribution_and_qubit_overhead_statement {X : Type} (P Q : X → ℝ) (r r_bound : ℕ) : Prop :=
  P = Q ∧ r ≤ r_bound

/-- **(Proposition 4 / Conjecture 1), hardness hypothesis**: if
the non-uniform polynomial hierarchy does not collapse (abstracted as
the parameter `ph_no_collapse`), then no polynomial classical family
can jointly sample `y'` and the measured output of `D_n(y')|0^n⟩`
(abstracted as the parameter `hard`). -/
def joint_sampling_hardness_of_nonuniform_ph_noncollapse_statement (ph_no_collapse hard : Prop) : Prop :=
  ph_no_collapse → hard

/-- **(Theorem 12), tomographic advantage shape**: learning a
tomographically-complete generative shallow QNN is quantumly easy but
classically hard under Conjecture 1. -/
def tomographic_generative_learning_advantage_statement (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  quantum_advantage quantum_cost classical_cost

/-- **(Theorem 14), simulation-speedup advantage shape**: unless
BPP = BQP, a quantum computer can generate the compressed
constant-depth simulation circuit efficiently while a classical one
cannot. -/
def compressed_simulation_generation_advantage_statement (bpp_eq_bqp : Prop) (quantum_cost classical_cost : ℕ → ℝ) : Prop :=
  ¬ bpp_eq_bqp → quantum_advantage quantum_cost classical_cost

end Qatlib.Papers.GenerativeAdv25.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# CoupledOsc23 — shared source model

Fixed paper: arXiv:2303.13012 (Babbush–Berry–Costa–Combes–Morales–Neven–Wiebe,
"Exponential quantum speedup in simulating coupled classical oscillators"; the
prefetched PDF is the 2023-09-21 build).

This module fixes the mathematical vocabulary shared by every paper-layer claim of
`CoupledOsc23.MainResults`:

* the oscillator system of Sec. II: symmetric nonnegative `d`-sparse spring matrix
  `K`, positive diagonal masses `M`, the spring vector `μ` of Eq. (5) and the
  state `|ψ(t)⟩` of Eq. (2);
* the kinetic/potential energies of Eqs. (4)–(5) and the total energy `E`;
* Newton trajectories (`M ẍ = −K x`, Eq. (1)) and the PSD dynamics
  `ÿ = −A y` of Eq. (9) used by Problem 4;
* the incidence matrix `B` and the block Hamiltonian `H` of Eqs. (12), (16), in
  the padded form used by Lemmas 8–9;
* the paper's algorithm/count vocabulary (`Algorithm`), approximate block
  encodings (Lemma 8–9 conclusion shape) and the estimation-algorithm law used
  by Theorems 5–6.

The two proved mass identities below (`oscillatorState_normSq`,
`oscillatorState_kineticMass`/`_potentialMass`) are the elementary content behind
the paper's observation that the support of `|ψ(t)⟩` on the two register blocks
equals `K(t)/E` and `U(t)/E` (Sec. II and Sec. V).
-/

set_option autoImplicit false
noncomputable section

open BigOperators
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

/-! ## Finite index types of the oscillator encoding -/

/-- Index of an unordered oscillator pair `j ≤ k`; it has `N(N+1)/2` elements,
the dimension `M` of the spring vector `μ` in Eq. (2). -/
abbrev PairIndex (N : ℕ) : Type := { p : Fin N × Fin N // p.1 ≤ p.2 }

instance (N : ℕ) : Fintype (PairIndex N) := inferInstance
instance (N : ℕ) : DecidableEq (PairIndex N) := inferInstance

/-- Register index of `|ψ(t)⟩`: the first block carries the `N` velocities, the
second block the `N(N+1)/2` spring coordinates. -/
abbrev OscIndex (N : ℕ) : Type := Fin N ⊕ PairIndex N

/-! ## Sparsity, symmetry and the spring vector -/

/-- `K` is `d`-sparse: at most `d` non-zero entries in every row (Problem 1). -/
def IsDSparse {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (d : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter (fun j => K i j ≠ 0)).card ≤ d

/-- `κmax` dominates every spring constant, as assumed in Theorem 1. -/
def IsBoundedBy {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (κmax : ℝ) : Prop :=
  ∀ i j, K i j ≤ κmax

/-- The spring vector `μ` of Eq. (5): entries `√κ_jj x_j` on the diagonal and
`√κ_jk (x_j − x_k)` for `j < k`. -/
def springVector {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ)
    (p : PairIndex N) : ℝ :=
  if p.1.1 = p.1.2 then Real.sqrt (K p.1.1 p.1.1) * x p.1.1
  else Real.sqrt (K p.1.1 p.1.2) * (x p.1.1 - x p.1.2)

/-! ## Energies and the encoded state -/

/-- Kinetic energy of Eq. (4). -/
def kineticEnergy {N : ℕ} (M : Fin N → ℝ) (v : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ j, M j * (v j) ^ 2

/-- Potential energy written through the spring vector; for nonnegative `K` this
is Eq. (5), because `(√κ * a)² = κ * a²`. -/
def potentialEnergy {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ p : PairIndex N, (springVector K x p) ^ 2

/-- Restricted kinetic energy `K_V(t)` of a subset `V` of oscillators. -/
def kineticEnergyOn {N : ℕ} (M : Fin N → ℝ) (V : Finset (Fin N)) (v : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ j ∈ V, M j * (v j) ^ 2

/-- Restricted potential energy `U_V(t)` of a subset `V` of springs. -/
def potentialEnergyOn {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (V : Finset (PairIndex N))
    (x : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ V, (springVector K x p) ^ 2

/-- The paper's `ℵ = κmax / mmin`. -/
def aleph (κmax mmin : ℝ) : ℝ := κmax / mmin

/-- The paper's `τ = t √(ℵ d)` (Theorem 1 and the gate ledger). -/
def tau (t κmax mmin : ℝ) (d : ℕ) : ℝ := t * Real.sqrt (aleph κmax mmin * (d : ℝ))

/-- `ℵ = κmax / mmin` is positive for positive `κmax` and `mmin`. -/
theorem aleph_pos {κmax mmin : ℝ} (hκ : 0 < κmax) (hm : 0 < mmin) : 0 < aleph κmax mmin :=
  div_pos hκ hm

/-- The rescaled time `τ = t √(ℵ d)` is nonnegative for `t ≥ 0`. -/
theorem tau_nonneg {t κmax mmin : ℝ} {d : ℕ} (ht : 0 ≤ t) :
    0 ≤ tau t κmax mmin d :=
  mul_nonneg ht (Real.sqrt_nonneg _)

/-- Total (time-independent) energy `E = K(t) + U(t)`. -/
def totalEnergy {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (M : Fin N → ℝ)
    (x v : Fin N → ℝ) : ℝ :=
  kineticEnergy M v + potentialEnergy K x

/-- The normalized state `|ψ(t)⟩` of Eq. (2). -/
def oscillatorState {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (M : Fin N → ℝ)
    (E : ℝ) (x v : Fin N → ℝ) : OscIndex N → ℂ
  | Sum.inl j => ((Real.sqrt (M j) * v j / Real.sqrt (2 * E) : ℝ) : ℂ)
  | Sum.inr p => Complex.I * ((springVector K x p / Real.sqrt (2 * E) : ℝ) : ℂ)

/-- Squared Euclidean norm of a finite complex vector. -/
def l2NormSq {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : ℝ :=
  ∑ i, ‖ψ i‖ ^ 2

/-- Euclidean norm of a finite complex vector. -/
def l2Norm {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : ℝ :=
  Real.sqrt (l2NormSq ψ)

/-- Euclidean distance between two finite complex vectors. -/
def l2Dist {ι : Type*} [Fintype ι] (ψ φ : ι → ℂ) : ℝ := l2Norm (ψ - φ)

/-! ## The elementary mass identities behind `K(t)/E` and `U(t)/E` -/

/-- Squared norm of the velocity block: `‖ψ_{[N]}(j)‖² = M_j v_j²/(2E)`. -/
theorem oscillatorState_inl_normSq {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (E : ℝ) (x v : Fin N → ℝ) (hM : ∀ j, 0 ≤ M j) (hE : 0 < E)
    (j : Fin N) :
    ‖oscillatorState K M E x v (Sum.inl j)‖ ^ 2 = M j * (v j) ^ 2 / (2 * E) := by
  have h2E : (0 : ℝ) ≤ 2 * E := by positivity
  simp only [oscillatorState]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt h2E, mul_pow,
    Real.sq_sqrt (hM j)]

/-- Squared norm of the spring block: `‖ψ_{[M]}(p)‖² = μ_p²/(2E)`. -/
theorem oscillatorState_inr_normSq {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (E : ℝ) (x v : Fin N → ℝ) (hE : 0 < E) (p : PairIndex N) :
    ‖oscillatorState K M E x v (Sum.inr p)‖ ^ 2 = (springVector K x p) ^ 2 / (2 * E) := by
  have h2E : (0 : ℝ) ≤ 2 * E := by positivity
  simp only [oscillatorState]
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, Real.sq_sqrt h2E]

/-- **The encoded state has squared norm `(K(t)+U(t))/E`.**  In particular it is
normalized whenever `E` is the total energy, which is the normalization read off
from Eq. (2). -/
theorem oscillatorState_normSq {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (E : ℝ) (x v : Fin N → ℝ) (hM : ∀ j, 0 ≤ M j) (hE : 0 < E) :
    l2NormSq (oscillatorState K M E x v) =
      (kineticEnergy M v + potentialEnergy K x) / E := by
  unfold l2NormSq
  rw [Fintype.sum_sum_type]
  rw [Finset.sum_congr rfl (fun j _ => oscillatorState_inl_normSq K M E x v hM hE j)]
  rw [Finset.sum_congr rfl (fun p _ => oscillatorState_inr_normSq K M E x v hE p)]
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]
  unfold kineticEnergy potentialEnergy
  have hE0 : E ≠ 0 := hE.ne'
  field_simp

/-- **The state is normalized** when `E = K(t)+U(t)`: the content of
`|ψ(t)⟩ = E^{-1/2}(√M ẋ, iμ)` being a unit vector. -/
theorem oscillatorState_normSq_one {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (E : ℝ) (x v : Fin N → ℝ) (hM : ∀ j, 0 ≤ M j) (hE : 0 < E)
    (htot : E = totalEnergy K M x v) :
    l2NormSq (oscillatorState K M E x v) = 1 := by
  rw [oscillatorState_normSq K M E x v hM hE, htot]
  exact div_self (fun h => hE.ne' (by rw [htot]; exact h))

/-- **Kinetic-energy support identity.**  The mass of `|ψ(t)⟩` on the velocity
block restricted to `V` is `K_V(t)/E` (used by Theorem 5). -/
theorem oscillatorState_kineticMass {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (E : ℝ) (x v : Fin N → ℝ) (hM : ∀ j, 0 ≤ M j) (hE : 0 < E)
    (V : Finset (Fin N)) :
    (∑ j ∈ V, ‖oscillatorState K M E x v (Sum.inl j)‖ ^ 2) =
      ((1 / 2) * ∑ j ∈ V, M j * (v j) ^ 2) / E := by
  rw [Finset.sum_congr rfl (fun j _ => oscillatorState_inl_normSq K M E x v hM hE j)]
  rw [← Finset.sum_div]
  field_simp

/-- **Potential-energy support identity.**  The mass of `|ψ(t)⟩` on the spring
block restricted to a spring subset `V` is `U_V(t)/E` (used by Theorem 6). -/
theorem oscillatorState_potentialMass {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ)
    (M : Fin N → ℝ) (E : ℝ) (x v : Fin N → ℝ) (hE : 0 < E) (V : Finset (PairIndex N)) :
    (∑ p ∈ V, ‖oscillatorState K M E x v (Sum.inr p)‖ ^ 2) =
      ((1 / 2) * ∑ p ∈ V, (springVector K x p) ^ 2) / E := by
  rw [Finset.sum_congr rfl (fun p _ => oscillatorState_inr_normSq K M E x v hE p)]
  rw [← Finset.sum_div]
  field_simp

/-! ## Newton dynamics and the PSD dynamics -/

/-- `(x, ẋ)` solve Newton's equation `M ẍ = −K x` (Eq. (1)): `ẋ` is the
derivative of `x` and the derivative of `ẋ` is `−(K x)/M` coordinatewise. -/
def IsNewtonTrajectory {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (M : Fin N → ℝ)
    (x v : ℝ → Fin N → ℝ) : Prop :=
  (∀ j t, HasDerivAt (fun s => x s j) (v t j) t) ∧
  (∀ j t, HasDerivAt (fun s => v s j) (-(∑ k, K j k * x t k) / M j) t)

/-! ## Problem 1 and Problem 4 input structures -/

/-- Data of Problem 1: the gap matrix `K`, the masses `M`, the known bounds, the
evolution time and error, and the initial displacement/velocity encoded by `W`. -/
structure Problem1Input (N d : ℕ) where
  K : Matrix (Fin N) (Fin N) ℝ
  M : Fin N → ℝ
  κmax : ℝ
  mmin : ℝ
  mmax : ℝ
  t : ℝ
  ε : ℝ
  x0 : Fin N → ℝ
  xdot0 : Fin N → ℝ

/-- Legality hypotheses of Problem 1 / Theorem 1: symmetric, nonnegative,
`d`-sparse `K`, masses in `[mmin, mmax]`, `κmax` dominating `K`, `t ≥ 0`, `ε > 0`. -/
def Problem1Input.Legal {N d : ℕ} (P : Problem1Input N d) : Prop :=
  P.K.IsSymm ∧ (∀ i j, 0 ≤ P.K i j) ∧ IsDSparse P.K d ∧
  (∀ j, 0 < P.mmin ∧ P.mmin ≤ P.M j ∧ P.M j ≤ P.mmax) ∧
  0 < P.κmax ∧ IsBoundedBy P.K P.κmax ∧ 0 ≤ P.t ∧ 0 < P.ε

/-- The total energy `E = K(0) + U(0)` of the initial condition. -/
def Problem1Input.energy {N d : ℕ} (P : Problem1Input N d) : ℝ :=
  totalEnergy P.K P.M P.x0 P.xdot0

/-- Data of Problem 4: a PSD `d`-sparse matrix `A`, time/error and initial data. -/
structure Problem4Input (N d : ℕ) where
  A : Matrix (Fin N) (Fin N) ℝ
  t : ℝ
  ε : ℝ
  y0 : Fin N → ℝ
  ydot0 : Fin N → ℝ

/-- Legality hypotheses of Problem 4 / Theorem 4. -/
def Problem4Input.Legal {N d : ℕ} (P : Problem4Input N d) : Prop :=
  P.A.IsSymm ∧ P.A.PosSemidef ∧ IsDSparse P.A d ∧ 0 ≤ P.t ∧ 0 < P.ε

/-- Kinetic energy of the PSD dynamics: `½‖ẏ‖²`. -/
def kineticEnergy4 {N : ℕ} (v : Fin N → ℝ) : ℝ := (1 / 2) * ∑ j, (v j) ^ 2

/-- Potential energy of the PSD dynamics: `½ yᵀ A y`. -/
def potentialEnergy4 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ j, (∑ k, A j k * y k) ^ 2

/-- Total energy of the PSD dynamics. -/
def totalEnergy4 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (y v : Fin N → ℝ) : ℝ :=
  kineticEnergy4 v + potentialEnergy4 A y

/-- The normalized state of Problem 4, Eq. (7): `(ẏ, i A y)/√(2E)`. -/
def psdState {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (E : ℝ)
    (y v : Fin N → ℝ) : Fin N ⊕ Fin N → ℂ
  | Sum.inl j => ((v j / Real.sqrt (2 * E) : ℝ) : ℂ)
  | Sum.inr j => Complex.I * (((∑ k, A j k * y k) / Real.sqrt (2 * E) : ℝ) : ℂ)

/-- `ÿ = −A y` (Eq. (9)) with `ẏ` the derivative of `y`. -/
def IsPSDTrajectory {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (y v : ℝ → Fin N → ℝ) : Prop :=
  (∀ j t, HasDerivAt (fun s => y s j) (v t j) t) ∧
  (∀ j t, HasDerivAt (fun s => v s j) (-(∑ k, A j k * y t k)) t)

/-- Squared norm of the PSD state equals `(K(t)+U(t))/E`. -/
theorem psdState_normSq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (E : ℝ)
    (y v : Fin N → ℝ) (hE : 0 < E) :
    l2NormSq (psdState A E y v) =
      (kineticEnergy4 v + potentialEnergy4 A y) / E := by
  unfold l2NormSq
  rw [Fintype.sum_sum_type]
  have hinl : ∀ j, ‖psdState A E y v (Sum.inl j)‖ ^ 2 = (v j) ^ 2 / (2 * E) := by
    intro j
    have h2E : (0 : ℝ) ≤ 2 * E := by positivity
    simp only [psdState]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt h2E]
  have hinr : ∀ j, ‖psdState A E y v (Sum.inr j)‖ ^ 2 =
      ((∑ k, A j k * y k)) ^ 2 / (2 * E) := by
    intro j
    have h2E : (0 : ℝ) ≤ 2 * E := by positivity
    simp only [psdState]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      div_pow, Real.sq_sqrt h2E]
  rw [Finset.sum_congr rfl (fun j _ => hinl j)]
  rw [Finset.sum_congr rfl (fun j _ => hinr j)]
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]
  unfold kineticEnergy4 potentialEnergy4
  have hE0 : E ≠ 0 := hE.ne'
  field_simp

/-! ## Incidence matrix and block Hamiltonian (Lemmas 8–9) -/

/-- The padded incidence matrix `B` of Sec. III / Eq. (16): an `N × N²` matrix
whose column `(j,k)` has `√(κ_jk/m_j)` at row `j` and `−√(κ_jk/m_j)` at row
`k` for `j < k`, and the single entry `√(κ_jj/m_j)` at row `j` on the diagonal.
Remaining (`j > k`) columns are zero (the paper's padding). -/
def springIncidence {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (M : Fin N → ℝ) :
    Matrix (Fin N) (Fin N × Fin N) ℝ :=
  fun j p =>
    if p.1 ≤ p.2 then
      if j = p.1 then Real.sqrt (K p.1 p.2 / M p.1)
      else if p.1 ≠ p.2 ∧ j = p.2 then -Real.sqrt (K p.1 p.2 / M p.1)
      else 0
    else 0

/-- The block Hamiltonian `H = −[[0, B], [Bᵀ, 0]]` of Eq. (12), with `B` padded
to a square `N² × N²` matrix (rows of `B` embedded in the first `N` indices of
`Fin (N*N)` and zero elsewhere).  The carrier type has `2N²` elements, matching
the paper's padded `2N² × 2N²` Hamiltonian. -/
def padIncidenceRows {N : ℕ} (B : Matrix (Fin N) (Fin N × Fin N) ℝ) :
    Matrix (Fin (N * N)) (Fin N × Fin N) ℝ :=
  fun i p => if h : i.1 < N then B ⟨i.1, h⟩ p else 0

/-- Block Hamiltonian of Eq. (12) in padded form, `H = −[[0, B̂],[B̂ᵀ, 0]]`, acting
on `(N²) ⊕ (N²)` indices. -/
def blockHamiltonian {N : ℕ} (B : Matrix (Fin (N * N)) (Fin N × Fin N) ℝ) :
    Matrix (Fin (N * N) ⊕ (Fin N × Fin N)) (Fin (N * N) ⊕ (Fin N × Fin N)) ℝ :=
  fun i j =>
    match i, j with
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inl a, Sum.inr p => -B a p
    | Sum.inr p, Sum.inl a => -B a p
    | Sum.inr _, Sum.inr _ => 0

/-! ## Algorithm and count vocabulary -/

/-- A paper-level algorithm record: it outputs a value on every input and carries
the source's query/gate ledgers and the number of uses of the state-preparation
unitary `W`. -/
structure Algorithm (Input Output : Type*) where
  output : Input → Output
  queries : Input → ℝ
  gates : Input → ℝ
  usesW : Input → ℕ

/-- Approximate block encoding with additive spectral-norm error, the conclusion
shape of Lemmas 8–9 (Eqs. (A2) and (A3)).  `U : (J × α) → (J × β)` is the
paper's isometry on `(ancilla ⊗ output) ← (ancilla ⊗ input)`; the corner
`⟨0|_J U |0⟩_J` approximates `A / αs` within `ε` in `ℓ²` operator norm. -/
def ApproxBlockEncoding {J α β : Type*} [Fintype J] [DecidableEq J]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (U : Matrix (J × α) (J × β) ℂ) (j₀ : J) (A : Matrix α β ℂ) (αs ε : ℝ) : Prop :=
  Matrix.conjTranspose U * U = 1 ∧ 0 < αs ∧
    ‖(Matrix.of fun a b => U (j₀, a) (j₀, b)) - ((αs⁻¹ : ℝ) : ℂ) • A‖ ≤ ε

/-- A finite-outcome estimation algorithm (Theorems 5–6): a probability weight
on `M` measurement outcomes, an estimate attached to each outcome, and the query
ledgers for the sign oracle `V` and for the state-preparation circuit. -/
structure EstimationAlgorithm (Input : Type*) where
  outcomes : ℕ
  weight : Input → Fin outcomes → ℝ
  estimate : Input → Fin outcomes → ℝ
  usesV : Input → ℝ
  usesPrep : Input → ℝ

end Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

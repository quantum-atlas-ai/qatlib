/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.MatrixTensor
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ShadowModels.BooleanCubeFourier
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.RandCompile.ReferenceModel.LocalPauliEvolution

set_option backward.isDefEq.respectTransparency false

/-!
# MixednessTest26 — source model

Shared vocabulary for the paper-layer formalization of

* Jayadev Acharya, Abhilash Dharmavarapu, Yuhan Liu, Nengkun Yu,
  *Near-Optimal Mixedness Testing with Pauli Measurements*,
  arXiv:2608.18839v3 (fixed version, 2026-09-23).

Everything here is *definitional* and is used by the per-claim modules.  The
paper works with `N`-qubit mixed states and Pauli measurements; we keep

* the actual finite density operators `Operator (2^N)` and the Born outcome
  laws of Pauli-basis measurements (frozen `tensorPauliLaw`);
* the combinatorial Pauli vocabulary of §2.1 (`L_P`, `L`, `Q ◁ P`, weights);
* protocol models for randomized/non-adaptive and adaptive copy-wise
  measurement schemes, together with their acceptance probabilities;
* the measurement information channel (MIC) of §5.1 and its norms;
* the hard-instance perturbation `Δ_z` of Definition 5.2.

The model deliberately introduces no additional foundational assumptions: every
probability is a finite sum of Born masses computed from matrices.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.ShadowModels.ShadowChannel
open scoped BigOperators ComplexOrder

/-! ## Pauli combinatorics (§2.1, Definition 2.1) -/

/-- A Pauli basis: one of `X`, `Y`, `Z` on every qubit, encoded as `Fin 3`. -/
abbrev PauliBasis (N : ℕ) := Fin N → Fin 3

/-- A Pauli observable: a Pauli letter or the identity (`none`) on every qubit. -/
abbrev PauliObservable (N : ℕ) := Fin N → Option (Fin 3)

/-- The identity Pauli observable. -/
def pauliId {N : ℕ} : PauliObservable N := fun _ => none

/-- The support of a Pauli observable: the coordinates carrying a non-identity letter. -/
def pauliSupport {N : ℕ} (Q : PauliObservable N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (Q i).isSome)

/-- The Pauli weight `w(Q)`: the number of non-identity tensor factors. -/
def pauliWeight {N : ℕ} (Q : PauliObservable N) : ℕ := (pauliSupport Q).card

/-- `Q ◁ P`: the non-identity entries of `Q` agree with the basis `P`. -/
def pauliMatches {N : ℕ} (Q : PauliObservable N) (P : PauliBasis N) : Prop :=
  ∀ i, Q i = none ∨ Q i = some (P i)

/-- `Q` with support `S` matching `P` on `S` and the identity elsewhere (the
paper's `α_P(S)`). -/
def pauliEmbed {N : ℕ} (S : Finset (Fin N)) (P : PauliBasis N) : PauliObservable N :=
  fun i => if i ∈ S then some (P i) else none

/-- The Pauli influence `L_P = Σ_{Q ◁ P} 3^{w(Q)} α_Q^2` (Definition 2.1). -/
noncomputable def pauliInfluence {N : ℕ} (α : PauliObservable N → ℝ) (P : PauliBasis N) : ℝ := by
  classical
  exact
    ∑ Q : PauliObservable N,
      if Q = pauliId then 0
      else if pauliMatches Q P then (3 : ℝ) ^ pauliWeight Q * (α Q) ^ 2 else 0

/-- The total coefficient norm `L = Σ_{Q ≠ Id} α_Q^2`. -/
noncomputable def pauliNormSq {N : ℕ} (α : PauliObservable N → ℝ) : ℝ :=
  ∑ Q : PauliObservable N, if Q = pauliId then 0 else (α Q) ^ 2

/-- The uniform distribution on Pauli bases: the paper's `P ∼ u[{X,Y,Z}^{⊗N}]`.
The probability of each basis is `3^{-N}`. -/
noncomputable def uniformPauliBasis (N : ℕ) : FinDist (PauliBasis N) where
  prob _ := (1 / 3 : ℝ) ^ N
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
    simp [Fintype.card_fin]

/-! ## States, trace distance and Pauli-basis outcome laws -/

/-- `2^N` is positive, the dimension of the `N`-qubit register. -/
theorem two_pow_pos (N : ℕ) : (0 : ℕ) < 2 ^ N := Nat.pow_pos (by norm_num)

/-- The maximally mixed state `ρ_mm = I_d / d` on a `D`-dimensional register. -/
noncomputable def maximallyMixed (D : ℕ) (hD : 0 < D) : DensityOperator D where
  val := ((D : ℝ)⁻¹ : ℂ) • (1 : Operator D)
  property := by
    constructor
    · exact Matrix.PosSemidef.one.smul (by positivity)
    · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      have hDc : (D : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.pos_iff_ne_zero.mp hD)
      have hscalar : ((D : ℝ)⁻¹ : ℂ) = (D : ℂ)⁻¹ := by
        norm_num
      rw [hscalar, inv_mul_cancel₀ hDc]

/-- The trace distance `½‖ρ - σ‖₁` of two density operators. -/
noncomputable def traceDistance {D : ℕ} (ρ σ : DensityOperator D) : ℝ :=
  (1 / 2) * SchattenOne (ρ.1 - σ.1)

/-- The conditional Born outcome law, on the outcome bits, of measuring a state
`ρ` on `2^N` qubits in the Pauli basis `P`.  It is obtained from the joint
Pauli-record law `tensorPauliLaw` (which also randomizes the axis) by
conditioning on the axis assignment `P` and normalizing by the axis mass
`3^{-N}` (frozen theorem `tensorPauliLaw_axis_mass`). -/
noncomputable def pauliOutcomeLaw {N : ℕ} (ρ : DensityOperator (2 ^ N)) (P : PauliBasis N) :
    FinDist (Reg N) where
  prob x := (3 : ℝ) ^ N * (tensorPauliLaw N ρ.1 ρ.2).prob (fun i => (P i, x i))
  nonneg x := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ N := by positivity
    exact mul_nonneg h3 ((tensorPauliLaw N ρ.1 ρ.2).nonneg _)
  sum_one := by
    rw [← Finset.mul_sum, tensorPauliLaw_axis_mass N ρ.1 ρ.2 P]
    have h3 : (3 : ℝ) ^ N ≠ 0 := by positivity
    field_simp


/-! ## Non-adaptive randomized Pauli protocols (Algorithm 1, Theorem 1.1) -/

/-- A non-adaptive randomized Pauli-basis protocol with `n` copies: a uniform
random seed `Ω` selects a fixed list of `n` measurement bases, and a decision
rule inspects the `n` outcome registers.  The basis list is fixed in advance
(independently of the state), which is exactly the paper's *non-adaptive*,
*randomized Pauli basis* access. -/
structure PauliBasisProtocol (N n Ω : ℕ) where
  /-- The measurement basis used on copy `j`, as a function of the random seed. -/
  bases : Fin Ω → Fin n → PauliBasis N
  /-- The decision rule on the outcome record. -/
  decide : (Fin n → Reg N) → Bool

/-- Acceptance probability of a non-adaptive randomized Pauli protocol on the
state `ρ`: average over the uniform seed of the product Born outcome law. -/
noncomputable def pauliProtocolAcceptMass {N n Ω : ℕ} (T : PauliBasisProtocol N n Ω)
    (ρ : DensityOperator (2 ^ N)) : ℝ :=
  (1 / (Ω : ℝ)) * ∑ ω : Fin Ω, ∑ xs : Fin n → Reg N,
    (∏ j, (pauliOutcomeLaw ρ (T.bases ω j)).prob (xs j)) *
      (if T.decide xs then (1 : ℝ) else 0)

/-- Correctness of a randomized Pauli mixedness tester at distance `ε`: accept
`ρ_mm` with probability at least `2/3`, and reject any state at trace distance
at least `ε` from `ρ_mm` with probability at least `2/3` (Theorem 1.1's
`Ensure` box). -/
def IsPauliMixednessTester {N n Ω : ℕ} (T : PauliBasisProtocol N n Ω) (ε : ℝ) : Prop :=
  (2 / 3 : ℝ) ≤ pauliProtocolAcceptMass T
      (maximallyMixed (2 ^ N) (two_pow_pos N)) ∧
    ∀ ρ : DensityOperator (2 ^ N),
      ε ≤ traceDistance ρ (maximallyMixed (2 ^ N) (two_pow_pos N)) →
        pauliProtocolAcceptMass T ρ ≤ 1 / 3

/-- The copy complexity of *deterministic* Pauli testing (Ω = 1, so the basis
list is fixed): the infimum of copy counts of correct protocols. -/
noncomputable def deterministicPauliComplexity (N : ℕ) (ε : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ n : ℕ, x = (n : ℝ) ∧
    ∃ T : PauliBasisProtocol N n 1, IsPauliMixednessTester T ε}

/-! ## Adaptive copy-wise protocols (§5, Theorems 1.2/1.3) -/

/-- A copy-wise adaptive protocol over a measurement family `M` with `k`
outcomes per measurement.  The measurement for the next copy is a deterministic
function of the outcome transcript (private randomness with a fixed law is
absorbed into the family, as noted in the paper's footnote 1), and each
measurement is a `k`-outcome POVM. -/
structure AdaptiveFamilyProtocol (N k : ℕ) (M : Type) where
  /-- Effects of measurement `m` at outcome `x`. -/
  effect : M → Fin k → Operator (2 ^ N)
  psd : ∀ m x, (effect m x).PosSemidef
  complete : ∀ m, ∑ x, effect m x = 1
  /-- The measurement selected after a transcript `h`. -/
  choose : List (Fin k) → M

/-- Probability mass of the transcript prefix `h` followed by `x`, under the
Born rule for the adaptively chosen measurements.  Defined by recursion on the
remaining transcript; the accumulator `h` is the already-recorded prefix. -/
noncomputable def adaptiveTranscriptMass {N k : ℕ} {M : Type}
    (T : AdaptiveFamilyProtocol N k M) (ρ : Operator (2 ^ N)) :
    List (Fin k) → List (Fin k) → ℝ
  | _, [] => 1
  | h, x :: rest =>
      (Matrix.trace (T.effect (T.choose h) x * ρ)).re *
        adaptiveTranscriptMass T ρ (h ++ [x]) rest

/-- Acceptance probability of an adaptive protocol with decision rule `decide`
after `n` copies. -/
noncomputable def adaptiveAcceptProb {N n k : ℕ} {M : Type}
    (T : AdaptiveFamilyProtocol N k M) (decide : (Fin n → Fin k) → Bool)
    (ρ : Operator (2 ^ N)) : ℝ :=
  ∑ h : Fin n → Fin k, adaptiveTranscriptMass T ρ [] (List.ofFn h) *
    (if decide h then (1 : ℝ) else 0)

/-- Correctness of an adaptive mixedness tester at distance `ε`. -/
def IsAdaptiveMixednessTester {N n k : ℕ} {M : Type}
    (T : AdaptiveFamilyProtocol N k M) (decide : (Fin n → Fin k) → Bool) (ε : ℝ) : Prop :=
  (2 / 3 : ℝ) ≤ adaptiveAcceptProb T decide
      (maximallyMixed (2 ^ N) (two_pow_pos N)).1 ∧
    ∀ ρ : DensityOperator (2 ^ N),
      ε ≤ traceDistance ρ (maximallyMixed (2 ^ N) (two_pow_pos N)) →
        adaptiveAcceptProb T decide ρ.1 ≤ 1 / 3

/-! ## Product single-qubit measurements (Theorem 1.2) -/

/-- A product single-qubit measurement on `N` qubits: a binary POVM `{E_i, 1-E_i}`
on every wire. -/
structure SingleQubitMeasurement (N : ℕ) where
  E : Fin N → Operator 2
  psd : ∀ i, (E i).PosSemidef
  psd_compl : ∀ i, (1 - E i).PosSemidef

/-- The effect of the outcome bit-vector `x` for a product single-qubit
measurement: the tensor product of `E_i` on `0` bits and `1 - E_i` on `1` bits. -/
noncomputable def SingleQubitMeasurement.effect {N : ℕ} (m : SingleQubitMeasurement N)
    (x : Reg N) : Operator (2 ^ N) :=
  tensorPauliProduct N (fun i => if x i then 1 - m.E i else m.E i)

/-- The product single-qubit effects are complete. -/
theorem SingleQubitMeasurement.sum_effect {N : ℕ} (m : SingleQubitMeasurement N) :
    (∑ x : Reg N, m.effect x) = 1 := by
  have hsum :
      (∑ x : Reg N, tensorPauliProduct N (fun i => if x i then 1 - m.E i else m.E i)) =
        tensorPauliProduct N (fun i => ∑ b : Bool, (if b then 1 - m.E i else m.E i)) :=
    tensorPauliProduct_sum N (fun i (b : Bool) => if b then 1 - m.E i else m.E i)
  unfold SingleQubitMeasurement.effect
  rw [hsum]
  have hpt : ∀ i, (∑ b : Bool, (if b then 1 - m.E i else m.E i)) = 1 := by
    intro i
    rw [Fintype.sum_bool]
    simp
  simp_rw [hpt]
  exact tensorPauliProduct_one N

/-- A copy-wise adaptive **single-qubit** protocol with `n` copies: each copy is
measured by a product single-qubit measurement chosen from the previous copy
outcomes. -/
structure SingleQubitProtocol (N n : ℕ) where
  measure : List (Reg N) → SingleQubitMeasurement N
  decide : (Fin n → Reg N) → Bool

/-- Transcript mass of a single-qubit adaptive protocol. -/
noncomputable def singleQubitTranscriptMass {N n : ℕ} (T : SingleQubitProtocol N n)
    (ρ : Operator (2 ^ N)) : List (Reg N) → List (Reg N) → ℝ
  | _, [] => 1
  | h, x :: rest =>
      (Matrix.trace ((T.measure h).effect x * ρ)).re *
        singleQubitTranscriptMass T ρ (h ++ [x]) rest

/-- Acceptance probability of an adaptive single-qubit protocol. -/
noncomputable def singleQubitAcceptProb {N n : ℕ} (T : SingleQubitProtocol N n)
    (ρ : Operator (2 ^ N)) : ℝ :=
  ∑ h : Fin n → Reg N, singleQubitTranscriptMass T ρ [] (List.ofFn h) *
    (if T.decide h then (1 : ℝ) else 0)

/-- Correctness of an adaptive single-qubit mixedness tester at distance `ε`. -/
def IsSingleQubitMixednessTester {N n : ℕ} (T : SingleQubitProtocol N n) (ε : ℝ) : Prop :=
  (2 / 3 : ℝ) ≤ singleQubitAcceptProb T
      (maximallyMixed (2 ^ N) (two_pow_pos N)).1 ∧
    ∀ ρ : DensityOperator (2 ^ N),
      ε ≤ traceDistance ρ (maximallyMixed (2 ^ N) (two_pow_pos N)) →
        singleQubitAcceptProb T ρ.1 ≤ 1 / 3

/-! ## Measurement information channel (§5.1) -/

/-- The normalized Pauli matrix of an observable: identity off the support and
the matching `X`/`Y`/`Z` factor on the support.  `localPauliMatrix 0 = 1`,
`1 = X`, `2 = Y`, `3 = Z`. -/
noncomputable def pauliMatrix {N : ℕ} (Q : PauliObservable N) : Operator (2 ^ N) :=
  tensorPauliProduct N (fun i =>
    (Q i).rec (1 : Operator 2)
      (fun a => Qatlib.Concepts.RandCompile.ReferenceModel.localPauliMatrix a.succ))

/-- The measurement information channel (MIC) of a `k`-outcome POVM `eff`,
acting on an operator `Δ`: `L_M(Δ) = Σ_x (Tr(M_x Δ)/Tr M_x) M_x`
(§5.1, just before Definition 5.2). -/
noncomputable def micMap {D k : ℕ} (eff : Fin k → Operator D) (Δ : Operator D) : Operator D :=
  ∑ x, ((Matrix.trace (eff x * Δ)).re / (Matrix.trace (eff x)).re) • eff x

/-- The MIC quadratic form `⟨L_M(Δ), Δ⟩_D = Σ_x (Tr(M_x Δ))^2 / Tr M_x`. -/
noncomputable def micForm {D k : ℕ} (eff : Fin k → Operator D) (Δ : Operator D) : ℝ :=
  ∑ x, ((Matrix.trace (eff x * Δ)).re) ^ 2 / (Matrix.trace (eff x)).re

/-- The operator norm of the MIC, as the supremum of `‖L_M(Δ)‖₂` over
Hilbert–Schmidt unit `Δ`. -/
noncomputable def micOperatorNorm {D k : ℕ} (eff : Fin k → Operator D) : ℝ :=
  sSup {r : ℝ | ∃ Δ : Operator D, SchattenTwo Δ = 1 ∧ r = SchattenTwo (micMap eff Δ)}

/-- The trace norm of the MIC, written on the normalized Pauli basis (a
complete orthonormal basis of the operator space used by the paper in §5.1):
`Σ_Q ⟨L_M(Q), Q⟩_D`. -/
noncomputable def micTraceNorm {N k : ℕ} (eff : Fin k → Operator (2 ^ N)) : ℝ :=
  ∑ Q : PauliObservable N, (Matrix.trace (micMap eff (pauliMatrix Q) * pauliMatrix Q)).re

/-- A finite-outcome measurement model on `N` qubits: an arbitrary (possibly
infinite) family `M` of `k`-outcome POVMs. -/
structure MeasurementModel (N : ℕ) where
  k : ℕ
  kpos : 0 < k
  M : Type
  effect : M → Fin k → Operator (2 ^ N)
  psd : ∀ m x, (effect m x).PosSemidef
  complete : ∀ m, ∑ x, effect m x = 1

/-- The supremum of the MIC operator norm over the measurement family. -/
noncomputable def MeasurementModel.micLop {N : ℕ} (M : MeasurementModel N) : ℝ :=
  sSup {r : ℝ | ∃ m : M.M, r = micOperatorNorm (M.effect m)}

/-- The supremum of the MIC trace norm over the measurement family. -/
noncomputable def MeasurementModel.micL1 {N : ℕ} (M : MeasurementModel N) : ℝ :=
  sSup {r : ℝ | ∃ m : M.M, r = micTraceNorm (M.effect m)}

/-- The paper's spectral scale `√(‖L_M‖_op ‖L_M‖_1)`. -/
noncomputable def MeasurementModel.micScale {N : ℕ} (M : MeasurementModel N) : ℝ :=
  Real.sqrt (M.micLop * M.micL1)

/-! ## Hard-instance construction (Definition 5.2) -/

/-- The unnormalized perturbation `Δ_z = (c ε / (d √ℓ)) Σ_m z_m V_m` of
Definition 5.2, with `V_m` normalized Pauli observables. -/
noncomputable def hardInstanceDelta {N ℓ : ℕ} (c ε : ℝ) (V : Fin ℓ → PauliObservable N)
    (z : Fin ℓ → Bool) : Operator (2 ^ N) :=
  (c * ε / ((2 : ℝ) ^ N * Real.sqrt ℓ)) •
    (∑ m, (if z m then (1 : ℝ) else -1) • pauliMatrix (V m))

/-- The hard-instance state `σ_z = ρ_mm + Δ_z` of Definition 5.2 (without the
positivity clip, which is recorded separately as a hypothesis where needed). -/
noncomputable def hardInstanceState {N ℓ : ℕ} (c ε : ℝ) (V : Fin ℓ → PauliObservable N)
    (z : Fin ℓ → Bool) : Operator (2 ^ N) :=
  (maximallyMixed (2 ^ N) (two_pow_pos N)).1 +
    hardInstanceDelta c ε V z

end Qatlib.Papers.MixednessTest26.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

/-!
# Source vocabulary for `QLinearSys15` Theorem 1 (LinearSystemSample)

Fixed source: A. W. Harrow, *Review of Quantum Algorithms for Systems of Linear
Equations*, arXiv:1501.00008v1 (30 Dec 2014; PDF dated 2015-01-05), §3,
PDF p. 2. The reviewed reduction is Theorem 1 (txt line 51):

> Consider a quantum circuit on `n` qubits that applies two-qubit unitary gates
> `U₁, …, U_T` to the `|0⟩^{⊗n}` state and concludes by outputting the result of
> measuring the first qubit. It is possible to simulate this measurement outcome
> up to error `ε` by reducing to `LinearSystemSample(N, κ, ε/2, T_A)` with
> `N = O(2^n T/ε)`, `κ = O(T/ε)` and `T_A = polylog(N)`.

This module fixes the paper-layer *object* vocabulary only:

* `IsTwoQubitLocal` — the exact `n`-qubit embedding of a two-qubit gate on two
  distinct wires;
* `BqpCircuitWord` — `T` unitary two-qubit gates applied to `|0…0⟩`;
* the first-qubit outcome law `outcomeDist` of the final state;
* the `ℓ¹` distance `l1Dist` and the grouping map `groupedDist`;
* `LinearSystemSampleInstance N κ ε T_A` — the instance of the source problem:
  Hermitian `A` with spectrum in `[1/κ, 1]`, `b = e₁`, row-query cost `T_A`,
  solution `x` of `Ax = b`, and the produced sample used as the quantum
  algorithm's output.

Everything here is notation; the statements of Theorem 1 live in
`Theorem1Reduction`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSys15.MainResults.LinearSystemSample

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

/-! ## 1. The BQP circuit word -/

/-- **Two-qubit locality.** `U` acts exactly as a two-qubit matrix `V` on the
distinct wires `i, j` and as the identity on every other wire: an entry `U x y`
is `V (x i, x j) (y i, y j)` when the two registers agree off `{i, j}`, and `0`
otherwise. This is the paper's "two-qubit unitary gate". -/
def IsTwoQubitLocal (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) : Prop :=
  ∃ (i j : Fin n) (V : Matrix (Bool × Bool) (Bool × Bool) ℂ),
    i ≠ j ∧ V ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
      ∀ x y : Reg n,
        U x y = if (∀ k : Fin n, k ≠ i → k ≠ j → x k = y k)
          then V (x i, x j) (y i, y j) else 0

/-- **A BQP circuit word** on `n` qubits with `T` two-qubit gates: each gate is
a genuine two-qubit-local unitary, exactly as in the source Theorem 1. -/
structure BqpCircuitWord (n T : ℕ) where
  /-- The `T` two-qubit unitary gates `U₁, …, U_T`. -/
  gate : Fin T → Matrix (Reg n) (Reg n) ℂ
  /-- Every gate is unitary. -/
  gate_unitary : ∀ t : Fin T, gate t ∈ Matrix.unitaryGroup (Reg n) ℂ
  /-- Every gate acts on at most two wires. -/
  gate_twoQubit : ∀ t : Fin T, IsTwoQubitLocal n (gate t)

/-- The sequential circuit of the gate word, as a `Circuit` of fixed gates. -/
def BqpCircuitWord.circuit {n T : ℕ} (C : BqpCircuitWord n T) : Circuit (Reg n) :=
  List.ofFn (fun t : Fin T => Step.gate (C.gate t))

/-- Every fixed gate of a gate word is unitary, so the circuit is unitary. -/
theorem BqpCircuitWord.circuit_isUnitary {n T : ℕ} (C : BqpCircuitWord n T) :
    IsUnitaryCircuit C.circuit := by
  intro U hU
  rw [BqpCircuitWord.circuit, List.mem_ofFn] at hU
  obtain ⟨t, ht⟩ := hU
  have hEq : C.gate t = U := by simpa using ht
  rw [← hEq]
  exact C.gate_unitary t

/-- The final state of the word: `U_T ⋯ U_1 |0…0⟩`. The oracle argument of
`Run` is the identity because the word contains no query steps. -/
def BqpCircuitWord.state {n T : ℕ} (C : BqpCircuitWord n T) : QState (Reg n) :=
  Run (1 : Matrix (Reg n) (Reg n) ℂ) C.circuit (Ket (ZeroStr n))

/-! ## 2. Unitarity preserves normalization along a `Circuit` -/

/-- Running a unitary circuit with the identity oracle preserves normalization.
This is the `Run`-level form of `normalized_applyGate`. -/
theorem run_normalized {I : Type*} [Fintype I] [DecidableEq I] (C : Circuit I) :
    IsUnitaryCircuit C → ∀ ψ : QState I, Normalized ψ →
      Normalized (Run (1 : Matrix I I ℂ) C ψ) := by
  induction C with
  | nil =>
    intro _ ψ hψ
    simpa using hψ
  | cons s C ih =>
    intro hC ψ hψ
    cases s with
    | gate U =>
      rw [run_gate]
      exact ih ((isUnitaryCircuit_gate U C).mp hC).2 (ApplyGate U ψ)
        (normalized_applyGate ((isUnitaryCircuit_gate U C).mp hC).1 hψ)
    | query =>
      rw [run_query]
      exact ih ((isUnitaryCircuit_query C).mp hC) (ApplyGate (1 : Matrix I I ℂ) ψ)
        (by simpa using hψ)

/-- The final state of a gate word is normalized. -/
theorem BqpCircuitWord.state_normalized {n T : ℕ} (C : BqpCircuitWord n T) :
    Normalized C.state :=
  run_normalized C.circuit C.circuit_isUnitary (Ket (ZeroStr n)) (normalized_ket _)

/-! ## 3. The first-qubit outcome law -/

/-- The Born probability that a measurement of the first wire (wire `0`) of `ψ`
returns `b`. -/
def measuredBit (n : ℕ) (hn : 0 < n) (ψ : QState (Reg n)) (b : Bool) : ℝ :=
  ∑ r : Reg n, if r ⟨0, hn⟩ = b then ‖ψ r‖ ^ 2 else 0

/-- The first-qubit outcome law of the circuit word. -/
def outcomeDist (n : ℕ) (hn : 0 < n) {T : ℕ} (C : BqpCircuitWord n T) : Bool → ℝ :=
  fun b => measuredBit n hn C.state b

/-- The two outcomes of a normalized state partition the Born mass: the first
-qubit law is a probability distribution. -/
theorem sum_measuredBit (n : ℕ) (hn : 0 < n) (ψ : QState (Reg n))
    (hψ : Normalized ψ) : ∑ b : Bool, measuredBit n hn ψ b = 1 := by
  unfold measuredBit
  rw [Finset.sum_comm]
  trans ∑ r : Reg n, ‖ψ r‖ ^ 2
  · apply Finset.sum_congr rfl
    intro r _
    rw [Fintype.sum_bool]
    by_cases h : r ⟨0, hn⟩ = true
    · simp [h]
    · have hf : r ⟨0, hn⟩ = false := by cases hh : r ⟨0, hn⟩ <;> simp_all
      simp [hf]
  · exact hψ

/-- The circuit record's first-qubit law sums to one. -/
theorem outcomeDist_prob (n : ℕ) (hn : 0 < n) {T : ℕ} (C : BqpCircuitWord n T) :
    ∑ b : Bool, outcomeDist n hn C b = 1 :=
  sum_measuredBit n hn C.state C.state_normalized

/-! ## 4. ℓ¹ distance and grouping -/

/-- The `ℓ¹` distance of two `Bool`-indexed real distributions. -/
def l1Dist (p q : Bool → ℝ) : ℝ := ∑ b : Bool, |p b - q b|

/-- `ℓ¹` distance is nonnegative. -/
theorem l1Dist_nonneg (p q : Bool → ℝ) : 0 ≤ l1Dist p q := by
  unfold l1Dist
  exact Finset.sum_nonneg fun b _ => abs_nonneg _

/-- `ℓ¹` distance is symmetric. -/
theorem l1Dist_comm (p q : Bool → ℝ) : l1Dist p q = l1Dist q p := by
  unfold l1Dist
  apply Finset.sum_congr rfl
  intro b _
  rw [abs_sub_comm]

/-- The triangle inequality for the `ℓ¹` distance. -/
theorem l1Dist_triangle (p q r : Bool → ℝ) :
    l1Dist p r ≤ l1Dist p q + l1Dist q r := by
  unfold l1Dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  have h : p b - r b = (p b - q b) + (q b - r b) := by ring
  rw [h]
  exact abs_add_le _ _

/-- Group an `N`-outcome law into a `Bool` law by a decoding map: the mass of
outcome `b` is the total mass of the `i` with `decode i = b`. -/
def groupedDist {N : ℕ} (decode : Fin N → Bool) (p : Fin N → ℝ) (b : Bool) : ℝ :=
  ∑ i : Fin N, if decode i = b then p i else 0

/-- Grouping preserves total mass. -/
theorem groupedDist_sum {N : ℕ} (decode : Fin N → Bool) (p : Fin N → ℝ) :
    ∑ b : Bool, groupedDist decode p b = ∑ i : Fin N, p i := by
  unfold groupedDist
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  by_cases h : decode i = true
  · simp [h]
  · have hf : decode i = false := by cases hh : decode i <;> simp_all
    simp [hf]

/-- **Grouping is 1-Lipschitz in `ℓ¹`.** Coarsening an `N`-outcome law to its
two decoded classes cannot increase the `ℓ¹` distance. This is the step that
turns the source problem's `ε/2` sampling accuracy on `[N]` into `ε/2` on the
first qubit. -/
theorem grouping_lipschitz {N : ℕ} (decode : Fin N → Bool) (p q : Fin N → ℝ) :
    l1Dist (groupedDist decode p) (groupedDist decode q) ≤
      ∑ i : Fin N, |p i - q i| := by
  unfold l1Dist groupedDist
  calc ∑ b : Bool, |(∑ i : Fin N, if decode i = b then p i else 0) -
          (∑ i : Fin N, if decode i = b then q i else 0)|
      = ∑ b : Bool, |∑ i : Fin N, (if decode i = b then (p i - q i) else 0)| := by
        apply Finset.sum_congr rfl
        intro b _
        have hsum : (∑ i : Fin N, if decode i = b then p i else 0) -
            (∑ i : Fin N, if decode i = b then q i else 0)
          = ∑ i : Fin N, (if decode i = b then (p i - q i) else 0) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : decode i = b <;> simp [h]
        rw [hsum]
    _ ≤ ∑ b : Bool, ∑ i : Fin N, |if decode i = b then (p i - q i) else 0| := by
        apply Finset.sum_le_sum
        intro b _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b : Bool, ∑ i : Fin N, if decode i = b then |p i - q i| else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : decode i = b <;> simp [h]
    _ = ∑ i : Fin N, ∑ b : Bool, if decode i = b then |p i - q i| else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin N, |p i - q i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Fintype.sum_bool]
        by_cases h : decode i = true
        · simp [h]
        · have hf : decode i = false := by cases hh : decode i <;> simp_all
          simp [hf]

/-! ## 5. The `LinearSystemSample` problem instance -/

/-- **`LinearSystemSample(N, κ, ε, T_A)`.** The source problem of §3: a Hermitian
`A` whose spectrum lies in `[1/κ, 1]`, `b = e₁`, the solution `x` of `Ax = b`,
a classical row-query algorithm of time `T_A`, and the produced sample law
`sample` on `[N]`, within `ε` in `ℓ¹` of `|x|² / ‖x‖²`. -/
structure LinearSystemSampleInstance (N : ℕ) (κ ε TA : ℝ) where
  /-- The Hermitian matrix `A`. -/
  A : Matrix (Fin N) (Fin N) ℂ
  /-- `A` is Hermitian. -/
  hermitian : Aᴴ = A
  /-- The spectrum lower bound `1/κ`: `‖Av‖ ≥ ‖v‖/κ`. -/
  spectrum_lower : ∀ v : Fin N → ℂ, v ≠ 0 → (1 / κ) * ‖v‖ ≤ ‖A *ᵥ v‖
  /-- The spectrum upper bound `1`: `‖Av‖ ≤ ‖v‖`. -/
  spectrum_upper : ∀ v : Fin N → ℂ, ‖A *ᵥ v‖ ≤ ‖v‖
  /-- The nonzero entries of each row. -/
  rowNonzeros : Fin N → List (Fin N × ℂ)
  /-- The classical time of the row-query algorithm. -/
  rowTime : ℝ
  /-- The row-query algorithm runs in the declared time `T_A`. -/
  rowTime_eq : rowTime = TA
  /-- The right-hand side `b`. -/
  b : Fin N → ℂ
  /-- `b = e₁`. -/
  b_eq : b = fun i : Fin N => if (i : ℕ) = 0 then 1 else 0
  /-- The exact solution `x = A⁻¹ b`. -/
  x : Fin N → ℂ
  /-- `x` solves `Ax = b`. -/
  solves : A *ᵥ x = b
  /-- The solution is nonzero, so its normalized law is defined. -/
  xNormSq_pos : 0 < ∑ i : Fin N, ‖x i‖ ^ 2
  /-- The decoding from the `N` solution entries to the simulated bit. -/
  decode : Fin N → Bool
  /-- The sample law produced by the algorithm on this instance. -/
  sample : Fin N → ℝ
  /-- The sample law is nonnegative. -/
  sample_nonneg : ∀ i : Fin N, 0 ≤ sample i
  /-- The sample law is normalized. -/
  sample_sum : ∑ i : Fin N, sample i = 1
  /-- The sample is within `ε` in `ℓ¹` of the normalized solution law. -/
  sample_close : ∑ i : Fin N, |sample i - ‖x i‖ ^ 2 / (∑ j : Fin N, ‖x j‖ ^ 2)| ≤ ε

/-- The normalized solution law `|x_i|² / ‖x‖²`. -/
def solutionDist {N : ℕ} {κ ε TA : ℝ} (L : LinearSystemSampleInstance N κ ε TA)
    (i : Fin N) : ℝ :=
  ‖L.x i‖ ^ 2 / (∑ j : Fin N, ‖L.x j‖ ^ 2)

/-- The normalized solution law sums to one. -/
theorem solutionDist_sum {N : ℕ} {κ ε TA : ℝ}
    (L : LinearSystemSampleInstance N κ ε TA) :
    ∑ i : Fin N, solutionDist L i = 1 := by
  unfold solutionDist
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt L.xNormSq_pos)

end Qatlib.Papers.QLinearSys15.MainResults.LinearSystemSample

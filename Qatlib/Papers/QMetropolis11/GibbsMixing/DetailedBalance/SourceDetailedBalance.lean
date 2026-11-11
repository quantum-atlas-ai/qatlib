/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointQuan
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceCriterionQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Detailed balance: definition, fixed point, criterion (Temme et al. 2011, Sec. 6)

Fixed source: arXiv:0911.3635v2 (*Quantum Metropolis sampling*), printed
pages 22-23.  This file is the paper-layer interface.  It bridges the paper's
Sec. 6 statements to the frozen semantic layer and adds the one *new* proof
that the paper uses in Sec. 4.2 but never isolates: the detailed-balance
criterion is linear in the superoperator (printed page 13: "The condition (25)
is linear in the superoperators.  We can therefore conclude that, when each of
the summands A and all the B's in (19) individually satisfy this condition, the
total cp-map E is detailed balanced.").

Reused frozen declarations (all in
`QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance`):

* `QuantumDetailedBalance` (definition, Eq. (Sec. 6 Definition)) —
  `QuantumAlgorithm/Concepts/QuantumGibbs/DetailedBalance/QuantumDetailedBalance/QuantumDetailedBalance.lean`;
* `quantumDetailedBalanceFixedPoint` Sec. 6 Lemma "fixed point" (strict CPTP
  domain; the printed hypothesis "completely positive" alone is refuted by a
  non-trace-preserving counterexample, recorded in the frozen statement file);
* `quantumDetailedBalanceCriterion` Sec. 6 Lemma "Detailed balance criterion"
  (Eq. (72), complete orthonormal basis, zero probabilities allowed).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.DetailedBalance

open Matrix
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.DetailedBalance

variable {D : ℕ}

/-- **c012, Sec. 6 Definition (printed p. 22).**  The paper defines quantum
detailed balance by Hilbert-Schmidt symmetry of
`E_σ[ρ] = E[σ^{1/2} ρ σ^{1/2}]`: `Tr[ρ† E_σ[φ]] = Tr[E_σ[ρ]† φ]` for all
complex square matrices `ρ φ`.  This theorem records that the frozen predicate
is exactly that conjunction over all complex matrices, with the positive
square root `densSqrt` supplied by functional calculus.  Reused FQN:
`QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance`. -/
theorem source_quantumDetailedBalance_iff_hilbertSchmidt
    (T : Operator D →ₗ[ℂ] Operator D) (σ : Operator D) :
    QuantumDetailedBalance T σ ↔
      ∀ ρ φ : Operator D,
        Matrix.trace (ρᴴ * T (densSqrt σ * φ * densSqrt σ))
          = Matrix.trace ((T (densSqrt σ * ρ * densSqrt σ))ᴴ * φ) :=
  Iff.rfl

/-- **c001, Sec. 6 Lemma "fixed point" (printed p. 22).**  Let `σ` be a state
and `E[ρ] = Σ_μ A_μ ρ A_μ†` a completely positive map obeying quantum detailed
balance with respect to `σ`; then `σ` is the steady state of `E`.  The paper's
own proof ends with `σ^{1/2} (Σ_μ A_μ† A_μ) σ^{1/2} = σ` and therefore uses
trace preservation; the frozen contract packages linearity, complete
positivity and trace preservation as a `QuantumChannel`, which is the honest
reading of the printed proof.  Reused FQN:
`QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance.quantumDetailedBalanceFixedPoint`. -/
theorem source_fixedPoint : QuantumDetailedBalanceFixedPoint :=
  quantumDetailedBalanceFixedPoint

/-- **c013, Sec. 6 Lemma "fixed point" (printed p. 22), CPTP reading.**
For every finite dimension, packaged channel `T` and density `σ`, detailed
balance of `T.map` with respect to `σ` forces `T.map σ = σ`.  Restates the
fixed-point lemma under the explicit CPTP domain, including singular `σ`
(the frozen proof never inverts `σ`).  Reused FQN:
`QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance.quantumDetailedBalanceFixedPoint`. -/
theorem source_fixedPoint_of_detailedBalance (T : QuantumChannel D D) (σ : Operator D)
    (hσ : IsDensityOperator σ) (hdb : QuantumDetailedBalance T.map σ) :
    T.map σ = σ :=
  quantumDetailedBalanceFixedPoint D T σ hσ hdb

/-- **c002/c014, Sec. 6 Lemma "Detailed balance criterion" (Eq. (72), printed
p. 22).**  For a complete orthonormal basis `{|ψ_i⟩}`, a probability
distribution `{p_i}`, and a completely positive map obeying
`√(p_n p_m) ⟨ψ_i|E[|ψ_n⟩⟨ψ_m|]|ψ_j⟩ = √(p_i p_j) ⟨ψ_m|E[|ψ_j⟩⟨ψ_i|]|ψ_n⟩`,
the state `σ = Σ_i p_i |ψ_i⟩⟨ψ_i|` and `E` obey detailed balance, hence `σ` is
a fixed point.  Reused FQN:
`QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance.quantumDetailedBalanceCriterion`. -/
theorem source_detailedBalanceCriterion : QuantumDetailedBalanceCriterion :=
  quantumDetailedBalanceCriterion

/-- **c014, Eq. (72), unpacked.**  The criterion stated in the paper's own
notation: complete basis, nonnegative normalized weights, matrix-element
condition (72) imply Hilbert-Schmidt detailed balance and stationarity of the
Gibbs-basis state.  Reused FQN:
`QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance.quantumDetailedBalanceCriterion`. -/
theorem source_detailedBalanceCriterion_unpacked
    (T : QuantumChannel D D) (ψ : Fin D → QState (Fin D)) (p : Fin D → ℝ)
    (horth : ∀ i j : Fin D, Inner (ψ i) (ψ j) = if i = j then 1 else 0)
    (hcomplete : ∀ x : QState (Fin D), ∑ i, Inner (ψ i) x • ψ i = x)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (h72 : ∀ i j n m : Fin D,
      Real.sqrt (p n * p m) * braKetElem (T.map (ketbra (ψ n) (ψ m))) (ψ i) (ψ j)
        = Real.sqrt (p i * p j) * braKetElem (T.map (ketbra (ψ j) (ψ i))) (ψ m) (ψ n)) :
    QuantumDetailedBalance T.map (gibbsBasis ψ p) ∧ T.map (gibbsBasis ψ p) = gibbsBasis ψ p :=
  quantumDetailedBalanceCriterion D T ψ p horth hcomplete hp hpsum h72

/-! ## c007: linearity of the detailed-balance criterion in the superoperator -/

/-- **c007 (Sec. 4.2, printed p. 13, Eqs. (25)-(36)).**  The condition (25) is
linear in the superoperators: if two superoperators both obey quantum detailed
balance with respect to the same `σ`, then so does their sum.  This is the step
the paper uses to reduce "verify A and all B_n individually" to "E = A + B_0 +
Σ B_n is detailed balanced".  New proof in this file; no frozen theorem
isolates it. -/
theorem quantumDetailedBalance_add
    {T₁ T₂ : Operator D →ₗ[ℂ] Operator D} {σ : Operator D}
    (h₁ : QuantumDetailedBalance T₁ σ) (h₂ : QuantumDetailedBalance T₂ σ) :
    QuantumDetailedBalance (T₁ + T₂) σ := by
  intro ρ φ
  simp only [LinearMap.add_apply, mul_add, add_mul, Matrix.conjTranspose_add,
    Matrix.trace_add]
  rw [h₁ ρ φ, h₂ ρ φ]

/-- **c007, zero summand.**  The zero superoperator is detailed balanced with
respect to every `σ` (its trace is zero on both sides). -/
theorem quantumDetailedBalance_zero (σ : Operator D) :
    QuantumDetailedBalance (0 : Operator D →ₗ[ℂ] Operator D) σ := by
  intro ρ φ
  simp only [LinearMap.zero_apply, mul_zero, Matrix.conjTranspose_zero,
    zero_mul, Matrix.trace_zero]

/-- **c007, finite sums.**  A finite sum of superoperators, each detailed
balanced with respect to `σ`, is detailed balanced with respect to `σ`.  This
is the exact statement needed for Eq. (19), `E = A + B_0 + Σ_n B_n`. -/
theorem quantumDetailedBalance_finset_sum {ι : Type*} (s : Finset ι)
    (T : ι → Operator D →ₗ[ℂ] Operator D) (σ : Operator D)
    (h : ∀ i ∈ s, QuantumDetailedBalance (T i) σ) :
    QuantumDetailedBalance (∑ i ∈ s, T i) σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using quantumDetailedBalance_zero σ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact quantumDetailedBalance_add
      (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **c007, the paper's accept + reject decomposition.**  If the accept term
`A` and every rejection term `B n` (`n` in a finite index set) individually
obey detailed balance with respect to `σ`, then the total map
`A + Σ_n B n` obeys detailed balance with respect to `σ`.  Source: Sec. 4.2,
printed page 13, Eq. (19) with the reductions (27)-(36). -/
theorem source_total_detailedBalance {ι : Type*} [Fintype ι]
    (A : Operator D →ₗ[ℂ] Operator D) (B : ι → Operator D →ₗ[ℂ] Operator D)
    (σ : Operator D)
    (hA : QuantumDetailedBalance A σ) (hB : ∀ n, QuantumDetailedBalance (B n) σ) :
    QuantumDetailedBalance (A + ∑ n, B n) σ :=
  quantumDetailedBalance_add hA
    (quantumDetailedBalance_finset_sum Finset.univ B σ (fun n _ => hB n))

end Qatlib.Papers.QMetropolis11.GibbsMixing.DetailedBalance

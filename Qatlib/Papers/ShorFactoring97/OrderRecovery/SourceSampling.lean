/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicPeriodSampling

@[expose] public section


/-!
# The source-sign order-finding state and joint Born law

Fixed source: quant-ph/9508027v2, section 5, Eqs. (5.1)--(5.5).
Both Fourier transforms have the positive sign used by the paper. The
modular-exponentiation oracle is the explicit reversible permutation
`(a, z) ↦ (a, z + x^a)` on the two registers. No divisibility assumption on
the clock and the order is imposed. In particular the construction applies
to the paper's power-of-two clock even when the order does not divide it.

The counts below charge a modular-exponentiation query and two Fourier
matrix gates. They are macro counts, not elementary gate or bit costs.
The off-grid probability lower bound, continued-fraction recovery and clean
workspace implementation remain separate obligations.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.ShorFactoring97.OrderRecovery

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.HspRecovery.CyclicRecovery

variable (N q : ℕ) [NeZero N]

/-- The modular-exponentiation function computed into the second register. -/
def sourcePower (x : (ZMod N)ˣ) (a : Fin q) : ZMod N := (x : ZMod N) ^ a.val

/-- The source circuit: positive Fourier preparation, reversible oracle, positive QFT. -/
noncomputable def sourceCirc : Circuit (Fin q × ZMod N) :=
  [Step.gate (TensorGate (QFTMatrix q) (1 : Matrix (ZMod N) (ZMod N) ℂ)),
    Step.query,
    Step.gate (TensorGate (QFTMatrix q) (1 : Matrix (ZMod N) (ZMod N) ℂ))]

/-- Every nonquery operation of the source circuit is unitary. -/
theorem source_unitary (hq : 0 < q) : IsUnitaryCircuit (sourceCirc N q) := by
  intro U hU
  simp only [sourceCirc, List.mem_cons, List.not_mem_nil, or_false] at hU
  rcases hU with hU | hU | hU
  · obtain rfl := Step.gate.inj hU
    exact tensorGate_unitary (qftMatrix_unitary hq) (Submonoid.one_mem _)
  · cases hU
  · obtain rfl := Step.gate.inj hU
    exact tensorGate_unitary (qftMatrix_unitary hq) (Submonoid.one_mem _)

omit [NeZero N] in
/-- The same circuit charges one modular-exponentiation query and two Fourier macros. -/
theorem source_counts : QueryCount (sourceCirc N q) = 1 ∧
    GateCount (sourceCirc N q) = 2 := ⟨rfl, rfl⟩

/-- Equation (5.1): the initial Fourier operation prepares the uniform register. -/
theorem source_prepare (hq : 0 < q) :
    ApplyGate (TensorGate (QFTMatrix q) (1 : Matrix (ZMod N) (ZMod N) ℂ))
      (TensorState (Ket (⟨0, hq⟩ : Fin q)) (Ket (0 : ZMod N))) =
      TensorState (Uniform (Fin q)) (Ket (0 : ZMod N)) := by
  rw [applyGate_tensorGate, applyGate_qftMatrix_ket_zero q hq, applyGate_one]

/-- Equation (5.2): the reversible permutation computes the coherent power table. -/
theorem source_compute (x : (ZMod N)ˣ) (a : Fin q) (z : ZMod N) :
    ApplyGate (AddOracle (sourcePower N q x))
      (TensorState (Uniform (Fin q)) (Ket (0 : ZMod N))) (a, z) =
      if z = sourcePower N q x a then (Real.sqrt (q : ℝ) : ℂ)⁻¹ else 0 := by
  rw [applyGate_addOracle]
  simp [TensorState, Ket, Uniform, sub_eq_zero]

/-- The output of executing the source circuit from the two zero registers. -/
noncomputable def sourceState (x : (ZMod N)ˣ) (hq : 0 < q) : QState (Fin q × ZMod N) :=
  Run (AddOracle (sourcePower N q x)) (sourceCirc N q)
    (TensorState (Ket (⟨0, hq⟩ : Fin q)) (Ket (0 : ZMod N)))

/-- Equations (5.1)--(5.3) compose into the executed positive-sign Fourier state. -/
theorem source_run (x : (ZMod N)ˣ) (hq : 0 < q) :
    sourceState N q x hq =
      ApplyGate (TensorGate (QFTMatrix q) (1 : Matrix (ZMod N) (ZMod N) ℂ))
        (ApplyGate (AddOracle (sourcePower N q x))
          (TensorState (Uniform (Fin q)) (Ket (0 : ZMod N)))) := by
  change ApplyGate _ (ApplyGate _ (ApplyGate _ _)) = _
  rw [source_prepare N q hq]

/-- The actual source circuit, including its reversible query, has unit norm. -/
theorem source_norm (x : (ZMod N)ˣ) (hq : 0 < q) :
    Normalized (sourceState N q x hq) :=
  (source_unitary N q hq).normalized_run (addOracle_unitary _)
    (normalized_tensorState (normalized_ket _) (normalized_ket _))

/-- Equation (5.4): each joint amplitude is the positive Fourier sum over its fibre. -/
theorem source_amp (x : (ZMod N)ˣ) (hq : 0 < q) (c : Fin q) (z : ZMod N) :
    sourceState N q x hq (c, z) = (q : ℂ)⁻¹ *
      ∑ a ∈ Finset.univ.filter (fun a => sourcePower N q x a = z),
        primRoot q ^ ((c.val : ℤ) * (a.val : ℤ)) := by
  rw [source_run, applyGate_tensorGate_one_left_slice]
  change (∑ a : Fin q, QFTMatrix q c a *
    ApplyGate (AddOracle (sourcePower N q x))
      (TensorState (Uniform (Fin q)) (Ket (0 : ZMod N))) (a, z)) = _
  have hterm (a : Fin q) :
      QFTMatrix q c a *
          ApplyGate (AddOracle (sourcePower N q x))
            (TensorState (Uniform (Fin q)) (Ket (0 : ZMod N))) (a, z) =
        if sourcePower N q x a = z then
          ((Real.sqrt (q : ℝ) : ℂ)⁻¹ * (Real.sqrt (q : ℝ) : ℂ)⁻¹) *
            primRoot q ^ ((c.val : ℤ) * (a.val : ℤ)) else 0 := by
    rw [qftMatrix_apply, source_compute]
    by_cases h : z = sourcePower N q x a
    · rw [ite_eq_left h, ite_eq_left h.symm]
      ring
    · rw [ite_eq_right h, ite_eq_right (fun hz => h hz.symm), mul_zero]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.sum_filter,
    ← Finset.mul_sum, inv_sqrt_mul_inv_sqrt hq]

/-- The Born distribution obtained by measuring both registers of the actual circuit. -/
noncomputable def sourceLaw (x : (ZMod N)ˣ) (hq : 0 < q) : PMF (Fin q × ZMod N) :=
  bornDistribution (sourceState N q x hq) (source_norm N q x hq)

/-- Equation (5.5): the joint measurement law is the norm square of the fibre sum. -/
theorem source_joint (x : (ZMod N)ˣ) (hq : 0 < q) (c : Fin q) (z : ZMod N) :
    sourceLaw N q x hq (c, z) = ENNReal.ofReal
      (‖(q : ℂ)⁻¹ * ∑ a ∈ Finset.univ.filter (fun a => sourcePower N q x a = z),
        primRoot q ^ ((c.val : ℤ) * (a.val : ℤ))‖ ^ 2) := by
  rw [sourceLaw, bornDistribution_apply, BornProb, source_amp]

/-- The clock marginal is the pushforward of the same joint Born distribution. -/
theorem source_marginal (x : (ZMod N)ˣ) (hq : 0 < q) (c : Fin q) :
    (sourceLaw N q x hq).map Prod.fst c =
      ∑ z : ZMod N, sourceLaw N q x hq (c, z) := by
  let : DecidableEq (Fin q) := Classical.decEq _
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  exact Fintype.sum_ite_eq c (fun a => sourceLaw N q x hq (a, z))

end Qatlib.Papers.ShorFactoring97.OrderRecovery

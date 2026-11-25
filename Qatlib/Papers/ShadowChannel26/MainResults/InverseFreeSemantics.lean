/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShadowChannel26.MainResults.SourceModel
public import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.InvFreeAESemantics
public import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetwork
public import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
public import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

@[expose] public section

/-!
# Inverse-free semantics: the trace form of the amplitude and the round ledger

Section 3.3 of the paper writes the amplitude estimated by an inverse-free protocol as
`a(U) = tr[Π U |0ⁿ⟩⟨0ⁿ| U†]` (p. 9-10, lines 642-648) and charges the direct-sampling baseline
`s` sequential rounds, each making one forward query to `U` (p. 10, lines 649-654, and Fact 4.3
`K = sL`). The shared amplitude module instead defines the amplitude through the Born mass of the
`true` projective branch of the state `U |0ⁿ⟩`.

This module supplies the two bridges:

* `invFreeAmplitude_eq_zeroProjector_trace`: the Born-mass amplitude of the branch `Π` on the
  state `U|0ⁿ⟩` equals the real part of `tr[Π U |0ⁿ⟩⟨0ⁿ| U†]`, which is the paper's matrix
  expression. The proof identifies `|0⟩⟨0|` with the outer product of the first basis vector, moves
  the trace into the cyclic position `tr[(U† Π U) |0⟩⟨0|]`, applies
  `Qatlib.Concepts.InstrumentCore.PovmBridge.trace_mul_outerProduct`, and then transfers the
  inner product through the unitary `U`.
* `queryCount_replicate_round`: `L` sequentially concatenated inverse-free rounds make exactly `L`
  oracle queries.

Boundary: only sequential repetition is modelled. The paper's parallel query architecture
(`U^{⊗s}` acting on `s` qudit probes) has no circuit-model counterpart here, and the round count
is not connected to the sample budget `invFreeSampleCount`. The trace identity is stated for the
anchor `|0⟩` only, which is the anchor used by the paper's amplitude target.

Paper: [arXiv:2606.13638v2](https://arxiv.org/abs/2606.13638v2), §3.3.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Papers.ShadowChannel26.MainResults.SourceModel

namespace Qatlib.Papers.ShadowChannel26.MainResults

/-- The paper's projector `|0⟩⟨0|` is the outer product of the first basis vector. -/
theorem zeroProjector_eq_outerProduct (d : ℕ) [NeZero d] :
    zeroProjector d = outerProduct (Ket (0 : Fin d)) := by
  ext i j
  rw [outerProduct_apply, ket_apply, ket_apply]
  show (if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℂ) else 0)
      = (if i = 0 then 1 else 0) * (starRingEnd ℂ) (if j = 0 then 1 else 0)
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

/-- The inverse-free amplitude of the projective branch `P` on the state `U |0⟩` is the real part
of `⟨U 0| P |U 0⟩`. -/
theorem invFreeAmplitude_eq_re_inner {d : ℕ} [NeZero d] (P U : Op d)
    (hP : IsOrthogonalProjector P) :
    invFreeAmplitude P (0 : Fin d) U
      = (Inner (U *ᵥ Ket (0 : Fin d)) (P *ᵥ (U *ᵥ Ket (0 : Fin d)))).re :=
  ((congrArg Complex.re (inner_projector_mass hP (ApplyGate U (Ket (0 : Fin d))))).trans
    (Complex.ofReal_re _)).symm

/-- The amplitude identity of §3.3: for a projector `P` and a unitary `U`, the Born-mass
amplitude equals the real part of `tr[P U |0⟩⟨0| U†]`. -/
theorem invFreeAmplitude_eq_zeroProjector_trace {d : ℕ} [NeZero d] (P U : Op d)
    (hP : IsOrthogonalProjector P) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    invFreeAmplitude P (0 : Fin d) U = ((P * U * zeroProjector d * Uᴴ).trace).re := by
  have hUU : U * Uᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hU
  have hmat : U * (Uᴴ * P * U) = P * U := by
    rw [Matrix.mul_assoc Uᴴ P U, ← Matrix.mul_assoc U Uᴴ (P * U), hUU, Matrix.one_mul]
  have hstep : U *ᵥ ((Uᴴ * P * U) *ᵥ Ket (0 : Fin d)) = P *ᵥ (U *ᵥ Ket (0 : Fin d)) :=
    calc U *ᵥ ((Uᴴ * P * U) *ᵥ Ket (0 : Fin d))
        = (U * (Uᴴ * P * U)) *ᵥ Ket (0 : Fin d) :=
          Matrix.mulVec_mulVec (Ket (0 : Fin d)) U (Uᴴ * P * U)
      _ = (P * U) *ᵥ Ket (0 : Fin d) := by rw [hmat]
      _ = P *ᵥ (U *ᵥ Ket (0 : Fin d)) :=
          (Matrix.mulVec_mulVec (Ket (0 : Fin d)) P U).symm
  have hassoc : Uᴴ * (P * U) * outerProduct (Ket (0 : Fin d))
      = (Uᴴ * P * U) * outerProduct (Ket (0 : Fin d)) := by
    rw [← Matrix.mul_assoc Uᴴ P U]
  have htrace : (P * U * zeroProjector d * Uᴴ).trace
      = Inner (U *ᵥ Ket (0 : Fin d)) (P *ᵥ (U *ᵥ Ket (0 : Fin d))) := by
    rw [zeroProjector_eq_outerProduct, Matrix.trace_mul_cycle, hassoc, trace_mul_outerProduct,
      ← hstep]
    exact (inner_applyGate hU (Ket (0 : Fin d)) _).symm
  rw [invFreeAmplitude_eq_re_inner P U hP, htrace]

/-- `L` sequentially concatenated inverse-free rounds make exactly `L` forward queries. -/
theorem queryCount_replicate_round {I : Type} [Fintype I] [DecidableEq I] (L : ℕ) :
    QueryCount (List.flatten (List.replicate L (invFreeRoundCircuit : Circuit I))) = L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.replicate_succ, List.flatten_cons, queryCount_append, ih,
      invFreeRoundCircuit_queryCount]
    omega

end Qatlib.Papers.ShadowChannel26.MainResults

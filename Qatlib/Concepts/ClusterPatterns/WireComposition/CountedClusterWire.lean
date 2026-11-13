/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.ClusterWireInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedBellTeleportation

/-!
# Counted cluster wire circuits

This module constructs the observed circuits `clusterWireProgram` and `clusterTwoProgram` for
one and two steps of cluster-state wire propagation. Their actual branch maps are obtained from
circuit leaf operators by embedding the input and tracing out measured registers, then
identified with the corresponding abstract instruments.

For unit-modulus phases, each one-step branch is one half of conjugation by `clusterJ ζ`, and
each two-step branch is one quarter of conjugation by `clusterJ ξ * clusterJ ζ`. The two-step
identity extends to finite reference registers; explicit gate, measurement, leaf, and feedback
counts accompany the wire propagation described in [RaussendorfBriegel2000].

## Main statements

* `cluster_wire_actual_program_bridge`: identifies the one-step circuit branches with the wire
  instrument.
* `cluster_two_sequential_instrument_bridge`: identifies the two-step branches with sequential
  composition.
* `cluster_two_actual_reference_output`: gives branch and summed outputs with a reference
  register.
* `cluster_two_actual_program_cost`: records eleven gates and two measurements per two-step
  leaf.
* `cluster_wire_classical_feedback_cost`: gives one-bit and two-bit feedback encodings.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

/-- Conjugating a matrix unit by `M` gives the outer product of the corresponding columns of
`M`. -/
theorem mul_matUnit_conj (M : Operator 2) (i j : Fin 2) :
    M * teleportMatUnit i j * M.conjTranspose
      = matOuter (M *ᵥ Qatlib.Foundations.PureStateMath.Ket i) (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
  have hu : teleportMatUnit i j = matOuter (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) := by
    ext r r'
    simp only [teleportMatUnit, Matrix.of_apply, matOuter, ket_apply]
    by_cases h1 : r = i <;> by_cases h2 : r' = j <;> simp [h1, h2]
  rw [hu, matOuter_sandwich]
  rfl

/-- Tracing out the first register of an outer product supported at a fixed basis label gives
`matOuter f g`. -/
theorem traceLeft_matOuter_supported {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (o : I) (f g : QState J) :
    Matrix.traceLeft
        (matOuter (fun q : I × J => if q.1 = o then f q.2 else 0)
          (fun q : I × J => if q.1 = o then g q.2 else 0))
      = matOuter f g := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, matOuter, Matrix.of_apply]
  rw [Fintype.sum_eq_single o (fun p hp => by rw [if_neg hp, if_neg hp, zero_mul]),
    if_pos rfl, if_pos rfl]

/-- The relabeled projector for Boolean outcome `k` retains exactly the amplitudes with `comp q
= k`. -/
theorem applyGate_relabelBoolProjector {I : Type*} [Fintype I] [DecidableEq I]
    {D : ℕ} (e : I ≃ Fin D) (comp : I → Bool) (k : Bool) (w : QState I) :
    ApplyGate (relabelGate e.symm
        (Projector (Finset.univ.filter
          (fun r : Fin D => (boolEquivFin2 ∘ comp ∘ e.symm) r = boolEquivFin2 k)))) w
      = fun q => if comp q = k then w q else 0 := by
  have hentry : ∀ q q' : I,
      (relabelGate e.symm
          (Projector (Finset.univ.filter
            (fun r : Fin D => (boolEquivFin2 ∘ comp ∘ e.symm) r = boolEquivFin2 k)))) q q'
        = if q' = q then (if comp q = k then (1 : ℂ) else 0) else 0 := by
    intro q q'
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Projector,
      Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply]
    by_cases hq : q' = q
    · rw [hq]
      by_cases hc : comp q = k <;> simp [hc]
    · rw [Equiv.symm_symm, if_neg (fun hc => hq (Equiv.injective _ hc).symm),
        if_neg hq]
  funext q
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single q (fun k' hk => by rw [hentry q k', if_neg hk, zero_mul]),
    hentry q q, if_pos rfl]
  simp

/-- The partial trace over the first Boolean register preserves addition. -/
theorem traceLeft_add2 (A B : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix.traceLeft (A + B) = Matrix.traceLeft A + Matrix.traceLeft B := by
  ext c c'
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- The partial trace over the first Boolean register commutes with complex scalar
multiplication. -/
theorem traceLeft_smul2 (r : ℂ) (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix.traceLeft (r • A) = r • Matrix.traceLeft A := by
  ext c' c''
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum,
    smul_eq_mul]

/-- The conditional Pauli X correction on the second Boolean register, controlled by the
classical bit `b`. -/
noncomputable def clusterWireXbB (b : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) (if b then PauliX else 1)

/-- The conditional output X correction for a cluster wire, relabeled as an operator on `Fin 4`. -/
noncomputable def clusterWireXbGate (b : Bool) : Operator 4 :=
  relabelGate teleportOutcomeEquiv (clusterWireXbB b)

/-- The first Boolean register label, expressed in `Fin 2`, for a basis index in `Fin 4`. -/
def clusterAliceLabel (r : Fin 4) : Fin 2 := boolEquivFin2 (teleportOutcomeEquiv.symm r).1

/-- The observed two-qubit cluster wire circuit with phase parameter `ζ`, one measurement, and
an outcome-dependent output X correction. -/
noncomputable def clusterWireProgram (ζ : ℂ) : ObservedCircuit (Fin 4) :=
  .step (.gate clusterWireHbGate) (.step (.gate (clusterWirePhaseGate ζ))
    (.step (.gate clusterCZ) (.step (.gate clusterWireHaGate)
      (.measure 2 clusterAliceLabel
        (fun k => .step (.gate (clusterWireXbGate (boolEquivFin2.symm k)))
          (.halt true))))))

/-- The execution leaf of `clusterWireProgram ζ` corresponding to Boolean measurement outcome
`b`. -/
noncomputable def clusterWireLeaf (ζ : ℂ) (b : Bool) :
    Fin (observedLeafCount (clusterWireProgram ζ)) :=
  Fin.cast (by rfl) (boolEquivFin2 b)

/-- The single-bit classical message containing the cluster wire measurement outcome. -/
def clusterWireMessage (b : Bool) : List Bool := [b]

/-- The output operator obtained by embedding the input, applying the selected cluster wire
leaf, and tracing out the measured register. -/
noncomputable def clusterWireActualBranchCore (ζ : ℂ) (b : Bool) (ρ : Operator 2) :
    Operator 2 :=
  relabelGate boolEquivFin2 (Matrix.traceLeft
    (relabelGate teleportOutcomeEquiv.symm
      ((observedLeaf (1 : Operator 4) (clusterWireProgram ζ) (clusterWireLeaf ζ b)).operator
        * (clusterWireInitialFrame * ρ * clusterWireInitialFrame.conjTranspose)
        * (observedLeaf (1 : Operator 4) (clusterWireProgram ζ)
            (clusterWireLeaf ζ b)).operator.conjTranspose)))

/-- The complex linear map associated with `clusterWireActualBranchCore`. -/
noncomputable def clusterWireActualBranchMap (ζ : ℂ) (b : Bool) :
    Operator 2 →ₗ[ℂ] Operator 2 where
  toFun := clusterWireActualBranchCore ζ b
  map_add' := by
    intro ρ σ
    unfold clusterWireActualBranchCore
    simp only [Matrix.mul_add, Matrix.add_mul, relabelGate_add', traceLeft_add2]
  map_smul' := by
    intro r ρ
    unfold clusterWireActualBranchCore
    simp only [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul', traceLeft_smul2,
      RingHom.id_apply]

/-- The conditional X correction flips the second Boolean argument when `b` is true and acts
identically otherwise. -/
theorem clusterWireXbB_apply' (b : Bool) (ψ : QState (Bool × Bool)) :
    ApplyGate (clusterWireXbB b) ψ
      = if b then fun p => ψ (p.1, !p.2) else fun p => ψ p := by
  rw [show clusterWireXbB b
      = TensorGate (1 : Matrix Bool Bool ℂ) (if b then PauliX else 1) from rfl,
    applyGate_secondFactor]
  funext p
  cases b
  · simp only [if_neg (by decide : ¬(false = true))]
    exact congrFun (applyGate_one _) p.2
  · simp only [if_true]
    exact applyGate_permMatrix Bool.not_not (fun j => ψ (p.1, j)) p.2

/-- The conditional X correction acts on amplitudes by XOR with `b` in the second Boolean
register. -/
theorem clusterWireXbB_apply (b : Bool) (ψ : QState (Bool × Bool)) :
    ApplyGate (clusterWireXbB b) ψ = fun p => ψ (p.1, p.2 ^^ b) := by
  rw [clusterWireXbB_apply']
  funext p
  cases b <;> simp

/-- The relabeled conditional output X correction is unitary. -/
theorem clusterWireXbGate_unitary (b : Bool) :
    clusterWireXbGate b ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  refine teleportRelabelGate_mem_unitaryGroup ?_ _
  unfold clusterWireXbB
  cases b
  · simp only [if_neg (by decide : ¬(false = true))]
    exact tensorGate_unitary (Submonoid.one_mem _) (Submonoid.one_mem _)
  · simp only [if_true]
    exact tensorGate_unitary (Submonoid.one_mem _) pauliX_unitary

/-- The operator of the selected cluster wire leaf is the ordered product of its preparation
gates, measurement projector, and output correction. -/
theorem clusterWireLeafOperator_eq (ζ : ℂ) (b : Bool) :
    (observedLeaf (1 : Operator 4) (clusterWireProgram ζ) (clusterWireLeaf ζ b)).operator
      = ((((((1 : Operator 4) * clusterWireXbGate (boolEquivFin2.symm (boolEquivFin2 b)))
            * Projector (Finset.univ.filter (fun i => clusterAliceLabel i = boolEquivFin2 b)))
          * clusterWireHaGate)
        * clusterCZ)
      * clusterWirePhaseGate ζ)
    * clusterWireHbGate := by
  cases b <;> rfl

/-- On an input basis vector with a zero ancilla, the corrected wire leaf is supported on
outcome `b` and has output amplitudes given by `clusterJ ζ / √2`. -/
theorem clusterWireLeafColumn (ζ : ℂ) (b : Bool) (i : Fin 2) :
    ApplyGate ((observedLeaf (1 : Operator 4) (clusterWireProgram ζ)
        (clusterWireLeaf ζ b)).operator)
      (relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm i, false)))
      = relabelState teleportOutcomeEquiv
          (fun q : Bool × Bool =>
            if q.1 = b then ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 q.2) i
              else 0) := by
  have hG : clusterWireHaGate * (clusterCZ * (clusterWirePhaseGate ζ * clusterWireHbGate))
      = relabelGate teleportOutcomeEquiv
          (clusterWireHaB * (clusterCZb * (clusterWirePhaseB ζ * clusterWireHbB))) := by
    unfold clusterWireHaGate clusterCZ clusterWirePhaseGate clusterWireHbGate
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul]
  have hPsymm : Projector (Finset.univ.filter (fun r : Fin 4 => clusterAliceLabel r
          = boolEquivFin2 b))
      = relabelGate teleportOutcomeEquiv
          (relabelGate teleportOutcomeEquiv.symm
            (Projector (Finset.univ.filter
              (fun r : Fin 4 => clusterAliceLabel r = boolEquivFin2 b)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPlab : relabelGate teleportOutcomeEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 4 => clusterAliceLabel r
          = boolEquivFin2 b)))
      = relabelGate teleportOutcomeEquiv.symm
          (Projector (Finset.univ.filter
            (fun r : Fin 4 => (boolEquivFin2 ∘ Prod.fst ∘ teleportOutcomeEquiv.symm) r
              = boolEquivFin2 b))) := rfl
  rw [clusterWireLeafOperator_eq ζ b,
    show boolEquivFin2.symm (boolEquivFin2 b) = b from Equiv.symm_apply_apply _ _,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, one_mul,
    hG, applyGate_mul, applyGate_mul, applyGate_relabelGate,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    clusterWireDecodedColumn, hPsymm, hPlab, applyGate_relabelGate,
    applyGate_relabelBoolProjector,
    show clusterWireXbGate b = relabelGate teleportOutcomeEquiv (clusterWireXbB b) from rfl,
    applyGate_relabelGate, clusterWireXbB_apply]
  funext r
  obtain ⟨⟨a', c'⟩, hr⟩ : ∃ p : Bool × Bool, r = teleportOutcomeEquiv p :=
    ⟨_, (Equiv.apply_symm_apply teleportOutcomeEquiv r).symm⟩
  subst hr
  cases a' <;> cases c' <;> cases b <;> fin_cases i <;>
    simp [relabelState, Equiv.symm_apply_apply, clusterJ_entry, boolEquivFin2,
      sqrt2_inv_sq, mul_comm, mul_left_comm]

/-- On a matrix unit, the actual wire branch is one half of conjugation by `clusterJ ζ`. -/
theorem clusterWireActualBranchCore_matUnit (ζ : ℂ) (b : Bool) (i j : Fin 2) :
    clusterWireActualBranchCore ζ b (teleportMatUnit i j)
      = (1 / 2 : ℂ) • (clusterJ ζ * teleportMatUnit i j * (clusterJ ζ).conjTranspose) := by
  have hcolI : (fun r : Fin 4 => clusterWireInitialFrame r i)
      = relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm i, false)) := by
    funext r
    exact clusterWireInitialFrame_column i r
  have hcolJ : (fun r : Fin 4 => clusterWireInitialFrame r j)
      = relabelState teleportOutcomeEquiv (Qatlib.Foundations.PureStateMath.Ket (boolEquivFin2.symm j, false)) := by
    funext r
    exact clusterWireInitialFrame_column j r
  have hframe : clusterWireInitialFrame * teleportMatUnit i j
        * clusterWireInitialFrame.conjTranspose
      = matOuter (fun r : Fin 4 => clusterWireInitialFrame r i)
          (fun r : Fin 4 => clusterWireInitialFrame r j) := by
    ext r r'
    have hinner : ∀ a : Fin 2,
        (∑ b' : Fin 2, clusterWireInitialFrame r b'
            * (if b' = i ∧ a = j then (1 : ℂ) else 0))
          = if a = j then clusterWireInitialFrame r i else 0 := by
      intro a
      rw [Fintype.sum_eq_single i]
      · by_cases haj : a = j
        · rw [if_pos ⟨rfl, haj⟩, mul_one, if_pos haj]
        · rw [if_neg (fun hc => haj hc.2), mul_zero, if_neg haj]
      · intro b' hb'
        rw [if_neg (fun hc => hb' hc.1), mul_zero]
    have houter : ∀ a : Fin 2,
        ((∑ b' : Fin 2, clusterWireInitialFrame r b'
              * (if b' = i ∧ a = j then (1 : ℂ) else 0))
            * (starRingEnd ℂ) (clusterWireInitialFrame r' a))
          = (if a = j then clusterWireInitialFrame r i else 0)
              * (starRingEnd ℂ) (clusterWireInitialFrame r' a) :=
      fun a => congrArg (· * (starRingEnd ℂ) (clusterWireInitialFrame r' a)) (hinner a)
    simp only [Matrix.mul_apply, conjTranspose_apply, teleportMatUnit, Matrix.of_apply,
      matOuter, Matrix.of_apply, RCLike.star_def]
    rw [Finset.sum_congr rfl fun a _ => houter a, Fintype.sum_eq_single j]
    · rw [if_pos rfl]
    · intro a ha
      rw [if_neg ha, zero_mul]
  have hJcol : ∀ m : Fin 2,
      relabelState boolEquivFin2.symm
        (((Real.sqrt 2 : ℂ)⁻¹) • ((clusterJ ζ) *ᵥ Qatlib.Foundations.PureStateMath.Ket m))
      = fun c : Bool => ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 c) m := by
    intro m
    funext c
    simp only [relabelState, Function.comp_apply, Equiv.symm_symm, Pi.smul_apply,
      smul_eq_mul, mulVec, dotProduct, ket_apply]
    rw [Fintype.sum_eq_single m (fun k hk => by rw [if_neg hk, mul_zero]),
      if_pos rfl, mul_one]
  have hreal : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    have h := Complex.conj_ofReal ((Real.sqrt 2 : ℝ)⁻¹)
    rw [Complex.ofReal_inv] at h
    exact h
  have htr := traceLeft_matOuter_supported (I := Bool) (J := Bool) b
    (fun c : Bool => ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 c) i)
    (fun c : Bool => ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 c) j)
  have hsymm : ∀ X : Matrix Bool Bool ℂ, relabelGate boolEquivFin2 X
      = relabelGate boolEquivFin2.symm.symm X := fun X =>
    (congrArg (fun e => relabelGate e X) (Equiv.symm_symm boolEquivFin2)).symm
  unfold clusterWireActualBranchCore
  rw [hframe, hcolI, hcolJ, matOuter_sandwich,
    clusterWireLeafColumn ζ b i, clusterWireLeafColumn ζ b j,
    relabelGate_matOuter, htr,
    show (fun c : Bool => ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 c) i)
      = relabelState boolEquivFin2.symm
          (((Real.sqrt 2 : ℂ)⁻¹) • ((clusterJ ζ) *ᵥ Qatlib.Foundations.PureStateMath.Ket i)) from (hJcol i).symm,
    show (fun c : Bool => ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 c) j)
      = relabelState boolEquivFin2.symm
          (((Real.sqrt 2 : ℂ)⁻¹) • ((clusterJ ζ) *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) from (hJcol j).symm,
    hsymm _, relabelGate_matOuter, matOuter_smul_smul, hreal, sqrt2_inv_sq, mul_matUnit_conj]

/-- Each actual wire branch sends `ρ` to one half of its conjugation by `clusterJ ζ`. -/
theorem clusterWireActualBranchMap_apply (ζ : ℂ) (b : Bool) (ρ : Operator 2) :
    clusterWireActualBranchMap ζ b ρ
      = (1 / 2 : ℂ) • conjBranch (clusterJ ζ) ρ := by
  have hsmul : ∀ p : Fin 2 × Fin 2,
      clusterWireActualBranchMap ζ b (ρ p.1 p.2 • teleportMatUnit p.1 p.2)
      = ((1 / 2 : ℂ) * ρ p.1 p.2)
          • (clusterJ ζ * teleportMatUnit p.1 p.2 * (clusterJ ζ).conjTranspose) := by
    intro p
    have h1 : clusterWireActualBranchMap ζ b (ρ p.1 p.2 • teleportMatUnit p.1 p.2)
        = ρ p.1 p.2 • clusterWireActualBranchCore ζ b (teleportMatUnit p.1 p.2) :=
      map_smul _ _ _
    rw [h1, clusterWireActualBranchCore_matUnit ζ b p.1 p.2, smul_smul,
      mul_comm (ρ p.1 p.2) (1 / 2 : ℂ)]
  have hsumdistr : clusterWireActualBranchMap ζ b
      (∑ p : Fin 2 × Fin 2, ρ p.1 p.2 • teleportMatUnit p.1 p.2)
      = ∑ p : Fin 2 × Fin 2, ((1 / 2 : ℂ) * ρ p.1 p.2)
          • (clusterJ ζ * teleportMatUnit p.1 p.2 * (clusterJ ζ).conjTranspose) := by
    show clusterWireActualBranchMap ζ b _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p _ => hsmul p)
  rw [teleportMatUnit_decomp ρ, hsumdistr,
    map_sum (conjBranch (clusterJ ζ))
      (fun p : Fin 2 × Fin 2 => ρ p.1 p.2 • teleportMatUnit p.1 p.2) Finset.univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjBranch_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- For a unit-modulus phase, the actual circuit branch equals the corresponding branch of
`clusterWireInstrument`. -/
theorem cluster_wire_actual_program_bridge :
    ∀ (ζ : ℂ) (hζ : ‖ζ‖ = 1) (b : Bool),
      clusterWireActualBranchMap ζ b = (clusterWireInstrument ζ hζ).branch b := by
  intro ζ hζ b
  apply LinearMap.ext
  intro ρ
  rw [clusterWireActualBranchMap_apply ζ b ρ,
    clusterWireInstrument_branch_apply ζ hζ ρ b]

/-- For a unit-modulus phase, the wire program is well formed with two leaves indexed
bijectively by Boolean outcomes. Each leaf accepts, uses five gates and one measurement with
no queries, and records its outcome. -/
theorem cluster_wire_actual_counts :
    ∀ ζ : ℂ, ‖ζ‖ = 1 →
      observedWellFormed (clusterWireProgram ζ) ∧
        observedLeafCount (clusterWireProgram ζ) = 2 ∧
        (∀ b : Bool, (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ b)).accepted
              = true ∧
            (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ b)).queries = 0 ∧
            (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ b)).gates = 5 ∧
            (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ b)).measurements = 1 ∧
            (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ b)).outcomes
              = [(2, (boolEquivFin2 b).val)]) ∧
        Function.Bijective (clusterWireLeaf ζ) := by
  intro ζ hζ
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp only [clusterWireProgram, observedWellFormed]
    exact ⟨clusterWireHbGate_unitary, clusterWirePhaseGate_unitary hζ, clusterCZ_unitary,
      clusterWireHaGate_unitary, fun k => ⟨clusterWireXbGate_unitary _, trivial⟩⟩
  · intro b
    cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · constructor
    · intro a b hab
      have hv : (clusterWireLeaf ζ a).val = (clusterWireLeaf ζ b).val :=
        congrArg Fin.val hab
      cases a <;> cases b <;> simp_all [clusterWireLeaf, boolEquivFin2, Fin.val_cast]
    · intro j
      refine ⟨boolEquivFin2.symm (j.cast (rfl : observedLeafCount (clusterWireProgram ζ) = 2)),
        ?_⟩
      have hval : (clusterWireLeaf ζ
          (boolEquivFin2.symm (j.cast (rfl : observedLeafCount (clusterWireProgram ζ) = 2)))).val
          = j.val := by
        fin_cases j <;> simp [clusterWireLeaf] <;> rfl
      exact Fin.eq_of_val_eq hval

/-- The permutation that flips the middle Boolean register and leaves the other two registers
fixed. -/
def clusterBobFlip : ((Bool × Bool) × Bool) → ((Bool × Bool) × Bool) :=
  fun p => ((p.1.1, !p.1.2), p.2)

/-- Flipping the middle Boolean register twice is the identity. -/
theorem clusterBobFlip_involutive : Function.Involutive clusterBobFlip := by
  intro ⟨⟨a1, a2⟩, a3⟩
  simp [clusterBobFlip]

/-- Conjugating a diagonal matrix by the permutation matrix of an involution composes its
diagonal entries with that involution. -/
theorem permMatrix_mul_diagonal_permMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (σ : I → I) (hσ : Function.Involutive σ) (d : I → ℂ) :
    permMatrix σ * Matrix.diagonal d * permMatrix σ = Matrix.diagonal (d ∘ σ) := by
  ext i j
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply, Matrix.diagonal_apply]
  rw [Fintype.sum_eq_single (σ j) (fun k hk => by rw [if_neg hk, mul_zero]),
    if_pos rfl, mul_one,
    Fintype.sum_eq_single (σ j) (fun k hk => by rw [if_neg hk, mul_zero]),
    if_pos rfl, hσ j]
  by_cases hij : i = j <;> simp [hij]

/-- The conditional Pauli X correction on the middle register of a three-qubit Boolean basis. -/
noncomputable def clusterBobXbB (a : Bool) :
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) (if a then PauliX else 1))
    (1 : Matrix Bool Bool ℂ)

/-- The conditional middle-register X correction, relabeled as an operator on `Fin 8`. -/
noncomputable def clusterBobXbGate (a : Bool) : Operator 8 :=
  relabelGate teleportRegisterEquiv (clusterBobXbB a)

/-- The conditional Pauli Z correction on the final register, relabeled as an operator on `Fin
8`. -/
noncomputable def clusterBobZcGate (a : Bool) : Operator 8 :=
  relabelGate teleportRegisterEquiv (teleportZcB a)

/-- The controlled-Z operator on the middle and final Boolean registers, with the first register
unchanged. -/
noncomputable def clusterCZbcB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1.2 && p.2 then (-1 : ℂ) else 1

/-- The controlled-Z operator on the middle and final registers, relabeled as an operator on
`Fin 8`. -/
noncomputable def clusterCZbcGate : Operator 8 :=
  relabelGate teleportRegisterEquiv clusterCZbcB

/-- With a true control bit, the middle-register X correction is the permutation matrix of
`clusterBobFlip`. -/
theorem clusterBobXbB_true_eq_permMatrix :
    clusterBobXbB true = permMatrix clusterBobFlip := by
  ext ⟨⟨a1, a2⟩, a3⟩ ⟨⟨b1, b2⟩, b3⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;>
    simp [clusterBobXbB, clusterBobFlip, tensorGate_apply, PauliX, permMatrix,
      Matrix.of_apply]

/-- The conditional middle-register X correction acts on amplitudes by XOR with `a` in the
middle argument. -/
theorem clusterBobXbB_apply (a : Bool) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (clusterBobXbB a) ψ = fun p => ψ ((p.1.1, p.1.2 ^^ a), p.2) := by
  cases a
  · funext p
    obtain ⟨⟨a1, a2⟩, a3⟩ := p
    simp [clusterBobXbB, applyGate_one, tensorGate_one]
  · rw [clusterBobXbB_true_eq_permMatrix]
    funext p
    rw [applyGate_permMatrix clusterBobFlip_involutive ψ p]
    simp [clusterBobFlip]

/-- The conditional middle-register X correction is unitary in the Boolean basis. -/
theorem clusterBobXbB_unitary (a : Bool) :
    clusterBobXbB a ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ := by
  cases a
  · exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) (Submonoid.one_mem _))
      (Submonoid.one_mem _)
  · exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) pauliX_unitary)
      (Submonoid.one_mem _)

/-- The relabeled conditional middle-register X correction is unitary. -/
theorem clusterBobXbGate_unitary (a : Bool) :
    clusterBobXbGate a ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (clusterBobXbB_unitary a) _

/-- The relabeled conditional final-register Z correction is unitary. -/
theorem clusterBobZcGate_unitary (a : Bool) :
    clusterBobZcGate a ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (teleportZcB_unitary a) _

/-- The controlled-Z operator on the middle and final Boolean registers is unitary. -/
theorem clusterCZbcB_unitary :
    clusterCZbcB ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  obtain ⟨⟨a1, a2⟩, a3⟩ := p
  cases a1 <;> cases a2 <;> cases a3 <;> simp

/-- The conditional X and Z corrections cancel the byproduct transported through the
middle-to-final controlled-Z gate in the Boolean basis. -/
theorem clusterBob_byproduct_transport_bool (a : Bool) :
    clusterBobXbB a * teleportZcB a * clusterCZbcB * clusterBobXbB a = clusterCZbcB := by
  cases a
  · simp only [clusterBobXbB, teleportZcB, if_neg (by decide : ¬(false = true)), tensorGate_one]
    rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  · have hX : clusterBobXbB true = permMatrix clusterBobFlip := clusterBobXbB_true_eq_permMatrix
    have hZ : teleportZcB true
        = Matrix.diagonal (fun p : ((Bool × Bool) × Bool) => if p.2 then (-1 : ℂ) else 1) := by
      ext ⟨⟨a1, a2⟩, a3⟩ ⟨⟨b1, b2⟩, b3⟩
      simp only [teleportZcB, if_true, tensorGate_apply, Matrix.one_apply, PauliZ,
        Matrix.diagonal_apply]
      cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> simp
    have hZC : Matrix.diagonal (fun p : ((Bool × Bool) × Bool) => if p.2 then (-1 : ℂ) else 1)
          * clusterCZbcB
        = Matrix.diagonal (fun p : ((Bool × Bool) × Bool) =>
            (if p.2 then (-1 : ℂ) else 1) * (if p.1.2 && p.2 then (-1 : ℂ) else 1)) := by
      rw [show clusterCZbcB = Matrix.diagonal
            (fun p : ((Bool × Bool) × Bool) => if p.1.2 && p.2 then (-1 : ℂ) else 1) from rfl,
        Matrix.diagonal_mul_diagonal]
    rw [hX, hZ, Matrix.mul_assoc (permMatrix clusterBobFlip), hZC,
      permMatrix_mul_diagonal_permMatrix clusterBobFlip clusterBobFlip_involutive _]
    ext p q
    simp only [Matrix.diagonal_apply, clusterCZbcB, Function.comp_apply]
    by_cases hpq : p = q
    · subst hpq
      obtain ⟨⟨a1, a2⟩, a3⟩ := p
      cases a2 <;> cases a3 <;> simp [clusterBobFlip]
    · rw [if_neg hpq, if_neg hpq]

/-- The relabeled conditional corrections satisfy the controlled-Z byproduct transport identity
and are unitary. This gives the preentangled wire correction law used in
[RaussendorfBriegel2000]. -/
theorem cluster_preentangled_byproduct_transport :
    ∀ a : Bool,
      clusterBobXbGate a * clusterBobZcGate a * clusterCZbcGate * clusterBobXbGate a
        = clusterCZbcGate ∧
      clusterBobXbGate a ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
      clusterBobZcGate a ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  intro a
  have hFin : clusterBobXbGate a * clusterBobZcGate a * clusterCZbcGate * clusterBobXbGate a
      = clusterCZbcGate := by
    unfold clusterBobXbGate clusterBobZcGate clusterCZbcGate
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul,
      clusterBob_byproduct_transport_bool a]
  exact ⟨hFin, clusterBobXbGate_unitary a, clusterBobZcGate_unitary a⟩

/-- The Hadamard operator on the final Boolean register, tensored with the identity on the first
two registers. -/
noncomputable def clusterTwoHcB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) Hadamard

/-- The final-register Hadamard operator, relabeled as an operator on `Fin 8`. -/
noncomputable def clusterTwoHcGate : Operator 8 :=
  relabelGate teleportRegisterEquiv clusterTwoHcB

/-- The diagonal phase operator with entries `1` and `ζ` on the first Boolean register, acting
identically on the other registers. -/
noncomputable def clusterTwoPhaseAB (ζ : ℂ) :
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (TensorGate (Matrix.diagonal fun a : Bool => if a then ζ else 1)
    (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ)

/-- The first-register phase operator with parameter `ζ`, relabeled as an operator on `Fin 8`. -/
noncomputable def clusterTwoPhaseAGate (ζ : ℂ) : Operator 8 :=
  relabelGate teleportRegisterEquiv (clusterTwoPhaseAB ζ)

/-- The controlled-Z operator on the first and middle Boolean registers. -/
noncomputable def clusterTwoCZabB : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1.1 && p.1.2 then (-1 : ℂ) else 1

/-- The controlled-Z operator on the first and middle registers, relabeled as an operator on
`Fin 8`. -/
noncomputable def clusterTwoCZabGate : Operator 8 :=
  relabelGate teleportRegisterEquiv clusterTwoCZabB

/-- The diagonal phase operator with entries `1` and `ξ` on the middle Boolean register. -/
noncomputable def clusterTwoPhaseBB (ξ : ℂ) :
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  TensorGate (TensorGate (1 : Matrix Bool Bool ℂ)
    (Matrix.diagonal fun b : Bool => if b then ξ else 1)) (1 : Matrix Bool Bool ℂ)

/-- The middle-register phase operator with parameter `ξ`, relabeled as an operator on `Fin 8`. -/
noncomputable def clusterTwoPhaseBGate (ξ : ℂ) : Operator 8 :=
  relabelGate teleportRegisterEquiv (clusterTwoPhaseBB ξ)

/-- The conditional final-register X correction, relabeled as an operator on `Fin 8`. -/
noncomputable def clusterTwoXcGate (b : Bool) : Operator 8 :=
  relabelGate teleportRegisterEquiv (teleportXcB b)

/-- The first Boolean register label, expressed in `Fin 2`, for a basis index in `Fin 8`. -/
def clusterTwoAliceLabel (r : Fin 8) : Fin 2 :=
  boolEquivFin2 (teleportRegisterEquiv.symm r).1.1

/-- The middle Boolean register label, expressed in `Fin 2`, for a basis index in `Fin 8`. -/
def clusterTwoBobLabel (r : Fin 8) : Fin 2 :=
  boolEquivFin2 (teleportRegisterEquiv.symm r).1.2

/-- The observed three-qubit circuit for two successive cluster wire steps, with phase
parameters `ζ` and `ξ` and outcome-dependent corrections. -/
noncomputable def clusterTwoProgram (ζ ξ : ℂ) : ObservedCircuit (Fin 8) :=
  .step (.gate teleportHbGate)
    (.step (.gate clusterTwoHcGate)
      (.step (.gate (clusterTwoPhaseAGate ζ))
        (.step (.gate clusterTwoCZabGate)
          (.step (.gate clusterCZbcGate)
            (.step (.gate teleportHaGate)
              (.measure 2 clusterTwoAliceLabel
                (fun k =>
                  .step (.gate (clusterBobXbGate (boolEquivFin2.symm k)))
                    (.step (.gate (clusterBobZcGate (boolEquivFin2.symm k)))
                      (.step (.gate (clusterTwoPhaseBGate ξ))
                        (.step (.gate teleportHbGate)
                          (.measure 2 clusterTwoBobLabel
                            (fun k' =>
                              .step (.gate (clusterTwoXcGate (boolEquivFin2.symm k')))
                                (.halt true)))))))))))))

/-- The execution leaf of the two-step cluster wire circuit corresponding to measurement
outcomes `a` and `b`. -/
noncomputable def clusterTwoLeaf (ζ ξ : ℂ) (a b : Bool) :
    Fin (observedLeafCount (clusterTwoProgram ζ ξ)) :=
  Fin.cast (by rfl) (teleportOutcomeEquiv (a, b))

/-- The two-bit classical message containing the successive wire measurement outcomes. -/
def clusterTwoMessage (a b : Bool) : List Bool := [a, b]

/-- The final-register Hadamard transforms each pair of amplitudes by their normalized sum and
difference. -/
theorem clusterTwoHcB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate clusterTwoHcB ψ
      = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
          (ψ (p.1, false) + (if p.2 then (-1 : ℂ) else 1) * ψ (p.1, true)) := by
  rw [show clusterTwoHcB
      = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) Hadamard from rfl,
    applyGate_secondFactor]
  funext p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply, Fintype.sum_bool]
  cases p.2 <;> simp <;> ring

/-- The first-register phase operator multiplies an amplitude by `ζ` exactly when its first
Boolean label is true. -/
theorem clusterTwoPhaseAB_apply (ζ : ℂ) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (clusterTwoPhaseAB ζ) ψ = fun p => (if p.1.1 then ζ else 1) * ψ p := by
  simp only [clusterTwoPhaseAB, applyGate_firstFactor, applyGate_firstFactor,
    applyGate_diagonal]

/-- The middle-register phase operator multiplies an amplitude by `ξ` exactly when its middle
Boolean label is true. -/
theorem clusterTwoPhaseBB_apply (ξ : ℂ) (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate (clusterTwoPhaseBB ξ) ψ = fun p => (if p.1.2 then ξ else 1) * ψ p := by
  simp only [clusterTwoPhaseBB, applyGate_firstFactor, applyGate_secondFactor,
    applyGate_diagonal]

/-- The first-to-middle controlled-Z operator negates precisely the amplitudes with both
corresponding Boolean labels true. -/
theorem clusterTwoCZabB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate clusterTwoCZabB ψ
      = fun p => (if p.1.1 && p.1.2 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterTwoCZabB = Matrix.diagonal
      (fun p : ((Bool × Bool) × Bool) => if p.1.1 && p.1.2 then (-1 : ℂ) else 1) from rfl,
    applyGate_diagonal]

/-- The middle-to-final controlled-Z operator negates precisely the amplitudes with both
corresponding Boolean labels true. -/
theorem clusterCZbcB_apply (ψ : QState ((Bool × Bool) × Bool)) :
    ApplyGate clusterCZbcB ψ
      = fun p => (if p.1.2 && p.2 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterCZbcB = Matrix.diagonal
      (fun p : ((Bool × Bool) × Bool) => if p.1.2 && p.2 then (-1 : ℂ) else 1) from rfl,
    applyGate_diagonal]

/-- The square of the inverse of `√2`, viewed in `ℂ`, is `1 / 2`. -/
theorem sqrt2_inv_pow_two : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
  rw [pow_two, sqrt2_inv_sq]

/-- An entry of `clusterJ ξ * clusterJ ζ` is the explicit half-scaled expression determined by
the input and output Boolean labels. -/
theorem clusterJ_mul_entry (ζ ξ : ℂ) (c i : Fin 2) :
    (clusterJ ξ * clusterJ ζ) c i
      = (1 / 2 : ℂ) * ((if boolEquivFin2.symm i then ζ else 1)
          * (1 + (if (boolEquivFin2.symm c) ^^ (boolEquivFin2.symm i) then -ξ else ξ))) := by
  fin_cases c <;> fin_cases i <;>
    simp [clusterJ_entry, Matrix.mul_apply, Fin.sum_univ_two, boolEquivFin2, sqrt2_inv_sq,
      mul_comm, mul_left_comm] <;>
    ring

/-- The selected two-step wire leaf operator expands as the ordered product of its gates,
measurement projectors, and conditional corrections. -/
theorem clusterTwoLeafOperator_eq (ζ ξ : ℂ) (a b : Bool) :
    (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).operator
      = (((((((((((((1 : Operator 8) * clusterTwoXcGate (boolEquivFin2.symm (boolEquivFin2 b)))
            * Projector (Finset.univ.filter (fun i => clusterTwoBobLabel i = boolEquivFin2 b)))
          * teleportHbGate)
        * clusterTwoPhaseBGate ξ)
      * clusterBobZcGate (boolEquivFin2.symm (boolEquivFin2 a)))
        * clusterBobXbGate (boolEquivFin2.symm (boolEquivFin2 a)))
      * Projector (Finset.univ.filter (fun i => clusterTwoAliceLabel i = boolEquivFin2 a)))
      * teleportHaGate)
        * clusterCZbcGate)
      * clusterTwoCZabGate)
        * clusterTwoPhaseAGate ζ)
      * clusterTwoHcGate)
    * teleportHbGate := by
  cases a <;> cases b <;> rfl

/-- The preparation and first decoding gates send an input basis state with two zero ancillas to
the stated Boolean amplitude formula. -/
theorem clusterTwoDecoded (ζ : ℂ) (x : Bool) :
    ApplyGate (teleportHaB * (clusterCZbcB * (clusterTwoCZabB * (clusterTwoPhaseAB ζ
        * (clusterTwoHcB * teleportHbB))))) (Qatlib.Foundations.PureStateMath.Ket ((x, false), false))
      = fun p => ((Real.sqrt 2 : ℂ)⁻¹) * (1 / 2 : ℂ)
          * (if x then (if p.1.1 then (-1 : ℂ) else 1) * ζ * (if p.1.2 then (-1 : ℂ) else 1)
              else 1)
          * (if p.1.2 && p.2 then (-1 : ℂ) else 1) := by
  rw [applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    teleportHbB_apply, clusterTwoHcB_apply, clusterTwoPhaseAB_apply, clusterTwoCZabB_apply,
    clusterCZbcB_apply, teleportHaB_apply]
  funext p
  obtain ⟨⟨a1, a2⟩, a3⟩ := p
  cases a1 <;> cases a2 <;> cases a3 <;> cases x <;>
    simp [Qatlib.Foundations.PureStateMath.Ket, sqrt2_inv_sq, mul_comm, mul_left_comm] <;>
    first
    | rfl
    | ring

set_option maxHeartbeats 2000000 in

/-- On an input basis vector with two zero ancillas, the corrected leaf is supported on outcomes
`(a, b)` with output amplitudes given by `(clusterJ ξ * clusterJ ζ) / 2`. -/
theorem clusterTwoLeafColumn (ζ ξ : ℂ) (a b : Bool) (i : Fin 2) :
    ApplyGate ((observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).operator)
      (relabelState teleportRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm i, false), false)))
      = relabelState teleportRegisterEquiv
          (fun q : ((Bool × Bool) × Bool) =>
            if q.1 = (a, b) then (1 / 2 : ℂ) * (clusterJ ξ * clusterJ ζ) (boolEquivFin2 q.2) i
              else 0) := by
  have hPAsymm : Projector (Finset.univ.filter
          (fun r : Fin 8 => clusterTwoAliceLabel r = boolEquivFin2 a))
      = relabelGate teleportRegisterEquiv
          (relabelGate teleportRegisterEquiv.symm
            (Projector (Finset.univ.filter
              (fun r : Fin 8 => clusterTwoAliceLabel r = boolEquivFin2 a)))) :=
    (relabelGate_relabelGate _ _).symm
  have hfiltA : (Finset.univ.filter (fun r : Fin 8 => clusterTwoAliceLabel r = boolEquivFin2 a))
      = Finset.univ.filter
          (fun r : Fin 8 => (boolEquivFin2 ∘ (fun q : ((Bool × Bool) × Bool) => q.1.1)
              ∘ teleportRegisterEquiv.symm) r = boolEquivFin2 a) :=
    Finset.filter_congr fun r _ => Iff.rfl
  have hPBsymm : Projector (Finset.univ.filter
          (fun r : Fin 8 => clusterTwoBobLabel r = boolEquivFin2 b))
      = relabelGate teleportRegisterEquiv
          (relabelGate teleportRegisterEquiv.symm
            (Projector (Finset.univ.filter
              (fun r : Fin 8 => clusterTwoBobLabel r = boolEquivFin2 b)))) :=
    (relabelGate_relabelGate _ _).symm
  have hfiltB : (Finset.univ.filter (fun r : Fin 8 => clusterTwoBobLabel r = boolEquivFin2 b))
      = Finset.univ.filter
          (fun r : Fin 8 => (boolEquivFin2 ∘ (fun q : ((Bool × Bool) × Bool) => q.1.2)
              ∘ teleportRegisterEquiv.symm) r = boolEquivFin2 b) :=
    Finset.filter_congr fun r _ => Iff.rfl
  rw [clusterTwoLeafOperator_eq ζ ξ a b,
    show boolEquivFin2.symm (boolEquivFin2 b) = b from Equiv.symm_apply_apply _ _,
    show boolEquivFin2.symm (boolEquivFin2 a) = a from Equiv.symm_apply_apply _ _,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, one_mul,
    show teleportHaGate * (clusterCZbcGate * (clusterTwoCZabGate
        * (clusterTwoPhaseAGate ζ * (clusterTwoHcGate * (teleportHbGate : Operator 8)))))
      = relabelGate teleportRegisterEquiv
          (teleportHaB * (clusterCZbcB * (clusterTwoCZabB * (clusterTwoPhaseAB ζ
            * (clusterTwoHcB * teleportHbB))))) from by
      unfold teleportHaGate clusterCZbcGate clusterTwoCZabGate clusterTwoPhaseAGate
        clusterTwoHcGate teleportHbGate
      rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul,
        ← teleportRelabelGate_mul, ← teleportRelabelGate_mul],
    applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    applyGate_mul, applyGate_mul,
    applyGate_relabelGate, clusterTwoDecoded ζ (boolEquivFin2.symm i),
    hPAsymm, hfiltA, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : ((Bool × Bool) × Bool) => q.1.1),
    show clusterBobXbGate a = relabelGate teleportRegisterEquiv (clusterBobXbB a) from rfl,
    applyGate_relabelGate, clusterBobXbB_apply,
    show clusterBobZcGate a = relabelGate teleportRegisterEquiv (teleportZcB a) from rfl,
    applyGate_relabelGate, teleportZcB_apply,
    show clusterTwoPhaseBGate ξ
      = relabelGate teleportRegisterEquiv (clusterTwoPhaseBB ξ) from rfl,
    applyGate_relabelGate, clusterTwoPhaseBB_apply,
    show (teleportHbGate : Operator 8) = relabelGate teleportRegisterEquiv teleportHbB from rfl,
    applyGate_relabelGate, teleportHbB_apply,
    hPBsymm, hfiltB, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : ((Bool × Bool) × Bool) => q.1.2),
    show clusterTwoXcGate b = relabelGate teleportRegisterEquiv (teleportXcB b) from rfl,
    applyGate_relabelGate, teleportXcB_apply']
  funext r
  obtain ⟨⟨⟨a', b'⟩, c'⟩, hr⟩ : ∃ p : ((Bool × Bool) × Bool), r = teleportRegisterEquiv p :=
    ⟨_, (Equiv.apply_symm_apply teleportRegisterEquiv r).symm⟩
  obtain ⟨x, hi⟩ : ∃ x : Bool, i = boolEquivFin2 x :=
    ⟨_, (Equiv.apply_symm_apply boolEquivFin2 i).symm⟩
  subst hr
  subst hi
  cases a' <;> cases b' <;> cases c' <;> cases a <;> cases b <;> cases x <;>
    simp [Function.comp_apply, relabelState, Equiv.symm_apply_apply, clusterJ_mul_entry] <;>
    first
    | rfl
    | (ring_nf; rw [sqrt2_inv_pow_two]; ring)

/-- For unit-modulus phases, the selected leaf composed with the input frame has entries equal
to one half of `clusterJ ξ * clusterJ ζ` at its recorded outcomes. This realizes two-step
wire propagation from [RaussendorfBriegel2000]. -/
theorem cluster_two_actual_leaf_frame :
    ∀ (ζ ξ : ℂ) (a b : Bool) (c i : Fin 2), ‖ζ‖ = 1 → ‖ξ‖ = 1 →
      ((observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).operator
          * teleportInitialFrame)
        (teleportRegisterEquiv ((a, b), boolEquivFin2.symm c)) i =
        (1 / 2 : ℂ) * (clusterJ ξ * clusterJ ζ) c i := by
  intro ζ ξ a b c i _ _
  rw [matrix_mul_column,
    show (fun r' : Fin 8 => teleportInitialFrame r' i)
      = relabelState teleportRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm i, false), false)) from by
      funext r'
      exact teleportInitialFrame_column i r',
    clusterTwoLeafColumn ζ ξ a b i]
  simp [relabelState]

/-- The output operator obtained by embedding the input, applying a selected two-step wire leaf,
and tracing out the measured registers. -/
noncomputable def clusterTwoActualBranchCore (ζ ξ : ℂ) (a b : Bool) (ρ : Operator 2) :
    Operator 2 :=
  relabelGate boolEquivFin2 (Matrix.traceLeft
    (relabelGate teleportRegisterEquiv.symm
      ((observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).operator
        * (teleportInitialFrame * ρ * teleportInitialFrame.conjTranspose)
        * (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).operator.conjTranspose)))

/-- The complex linear map associated with `clusterTwoActualBranchCore`. -/
noncomputable def clusterTwoActualBranchMap (ζ ξ : ℂ) (a b : Bool) :
    Operator 2 →ₗ[ℂ] Operator 2 where
  toFun := clusterTwoActualBranchCore ζ ξ a b
  map_add' := by
    intro ρ σ
    unfold clusterTwoActualBranchCore
    simp only [Matrix.mul_add, Matrix.add_mul, relabelGate_add', traceLeft_add']
  map_smul' := by
    intro r ρ
    unfold clusterTwoActualBranchCore
    simp only [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul', traceLeft_smul',
      RingHom.id_apply]

/-- Relabeling a half-scaled column of `clusterJ ξ * clusterJ ζ` gives its entrywise expression
in the Boolean basis. -/
theorem clusterTwoMcol (ζ ξ : ℂ) (m : Fin 2) :
    relabelState boolEquivFin2.symm
        ((1 / 2 : ℂ) • ((clusterJ ξ * clusterJ ζ) *ᵥ Qatlib.Foundations.PureStateMath.Ket m))
      = fun c : Bool => (1 / 2 : ℂ) * (clusterJ ξ * clusterJ ζ) (boolEquivFin2 c) m := by
  funext c
  simp only [relabelState, Function.comp_apply, Equiv.symm_symm, Pi.smul_apply, smul_eq_mul,
    mulVec, dotProduct, ket_apply]
  rw [Fintype.sum_eq_single m (fun k hk => by rw [if_neg hk, mul_zero]),
    if_pos rfl, mul_one]

/-- On a matrix unit, the actual two-step wire branch is one quarter of conjugation by `clusterJ
ξ * clusterJ ζ`. -/
theorem clusterTwoActualBranchCore_matUnit (ζ ξ : ℂ) (a b : Bool) (i j : Fin 2) :
    clusterTwoActualBranchCore ζ ξ a b (teleportMatUnit i j)
      = (1 / 4 : ℂ) • ((clusterJ ξ * clusterJ ζ) * teleportMatUnit i j
          * (clusterJ ξ * clusterJ ζ).conjTranspose) := by
  have hcolI : (fun r : Fin 8 => teleportInitialFrame r i)
      = relabelState teleportRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm i, false), false)) :=
    funext fun r => teleportInitialFrame_column i r
  have hcolJ : (fun r : Fin 8 => teleportInitialFrame r j)
      = relabelState teleportRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((boolEquivFin2.symm j, false), false)) :=
    funext fun r => teleportInitialFrame_column j r
  have hhalf : (starRingEnd ℂ) ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
    rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) from by push_cast; norm_num,
      Complex.conj_ofReal]
  have htr := traceLeft_matOuter_supported (I := Bool × Bool) (J := Bool) (a, b)
    (fun c : Bool => (1 / 2 : ℂ) * (clusterJ ξ * clusterJ ζ) (boolEquivFin2 c) i)
    (fun c : Bool => (1 / 2 : ℂ) * (clusterJ ξ * clusterJ ζ) (boolEquivFin2 c) j)
  have hsymm : ∀ X : Matrix Bool Bool ℂ, relabelGate boolEquivFin2 X
      = relabelGate boolEquivFin2.symm.symm X := fun X =>
    (congrArg (fun e => relabelGate e X) (Equiv.symm_symm boolEquivFin2)).symm
  unfold clusterTwoActualBranchCore
  rw [teleportFrame_matUnit i j, hcolI, hcolJ, matOuter_sandwich,
    clusterTwoLeafColumn ζ ξ a b i, clusterTwoLeafColumn ζ ξ a b j,
    relabelGate_matOuter, htr, (clusterTwoMcol ζ ξ i).symm, (clusterTwoMcol ζ ξ j).symm,
    hsymm _, relabelGate_matOuter, matOuter_smul_smul, hhalf, mul_matUnit_conj]
  congr 1
  norm_num

/-- Each actual two-step wire branch sends `ρ` to one quarter of its conjugation by `clusterJ ξ
* clusterJ ζ`. -/
theorem clusterTwoActualBranchMap_apply (ζ ξ : ℂ) (a b : Bool) (ρ : Operator 2) :
    clusterTwoActualBranchMap ζ ξ a b ρ
      = (1 / 4 : ℂ) • conjBranch (clusterJ ξ * clusterJ ζ) ρ := by
  have hsmul : ∀ p : Fin 2 × Fin 2,
      clusterTwoActualBranchMap ζ ξ a b (ρ p.1 p.2 • teleportMatUnit p.1 p.2)
      = ((1 / 4 : ℂ) * ρ p.1 p.2)
          • ((clusterJ ξ * clusterJ ζ) * teleportMatUnit p.1 p.2
              * (clusterJ ξ * clusterJ ζ).conjTranspose) := by
    intro p
    have h1 : clusterTwoActualBranchMap ζ ξ a b (ρ p.1 p.2 • teleportMatUnit p.1 p.2)
        = ρ p.1 p.2 • clusterTwoActualBranchCore ζ ξ a b (teleportMatUnit p.1 p.2) :=
      map_smul _ _ _
    rw [h1, clusterTwoActualBranchCore_matUnit ζ ξ a b p.1 p.2, smul_smul,
      mul_comm (ρ p.1 p.2) (1 / 4 : ℂ)]
  have hsumdistr : clusterTwoActualBranchMap ζ ξ a b
      (∑ p : Fin 2 × Fin 2, ρ p.1 p.2 • teleportMatUnit p.1 p.2)
      = ∑ p : Fin 2 × Fin 2, ((1 / 4 : ℂ) * ρ p.1 p.2)
          • ((clusterJ ξ * clusterJ ζ) * teleportMatUnit p.1 p.2
              * (clusterJ ξ * clusterJ ζ).conjTranspose) := by
    show clusterTwoActualBranchMap ζ ξ a b _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p _ => hsmul p)
  rw [teleportMatUnit_decomp ρ, hsumdistr,
    map_sum (conjBranch (clusterJ ξ * clusterJ ζ))
      (fun p : Fin 2 × Fin 2 => ρ p.1 p.2 • teleportMatUnit p.1 p.2) Finset.univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjBranch_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- For unit-modulus phases, each actual two-step branch equals the corresponding sequential
instrument branch and is one quarter of conjugation by the composite wire operator. -/
theorem cluster_two_sequential_instrument_bridge :
    ∀ (ζ ξ : ℂ) (hζ : ‖ζ‖ = 1) (hξ : ‖ξ‖ = 1) (a b : Bool),
      clusterTwoActualBranchMap ζ ξ a b =
        ((clusterWireInstrument ζ hζ).seq (clusterWireInstrument ξ hξ)).branch (a, b) ∧
      (∀ ρ : Operator 2, clusterTwoActualBranchMap ζ ξ a b ρ =
        (1 / 4 : ℂ) • conjBranch (clusterJ ξ * clusterJ ζ) ρ) := by
  intro ζ ξ hζ hξ a b
  refine ⟨?_, fun ρ => clusterTwoActualBranchMap_apply ζ ξ a b ρ⟩
  apply LinearMap.ext
  intro ρ
  rw [clusterTwoActualBranchMap_apply ζ ξ a b ρ]
  have hseq : ((clusterWireInstrument ζ hζ).seq (clusterWireInstrument ξ hξ)).branch (a, b) ρ
      = (1 / 4 : ℂ) • conjBranch (clusterJ ξ * clusterJ ζ) ρ := by
    show ((clusterWireInstrument ξ hξ).branch b).comp
        ((clusterWireInstrument ζ hζ).branch a) ρ = _
    rw [LinearMap.comp_apply, clusterWireInstrument_branch_apply ζ hζ ρ a,
      map_smul, clusterWireInstrument_branch_apply ξ hξ _ b, smul_smul,
      show (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 from by norm_num]
    have h2 : conjBranch (clusterJ ξ) (conjBranch (clusterJ ζ) ρ)
        = conjBranch (clusterJ ξ * clusterJ ζ) ρ := by
      have h3 : ((conjBranch (clusterJ ξ)).comp (conjBranch (clusterJ ζ))) ρ
          = conjBranch (clusterJ ξ * clusterJ ζ) ρ := by
        rw [conjBranch_comp]
      exact h3
    rw [h2]
  rw [hseq]

/-- For unit-modulus phases and any finite reference register, each extended wire branch is one
quarter of conjugation by the composite wire operator tensored with the reference identity.
Summing the four branches gives the full conjugation, expressing wire propagation as in
[RaussendorfBriegel2000]. -/
theorem cluster_two_actual_reference_output :
    ∀ (ζ ξ : ℂ), ‖ζ‖ = 1 → ‖ξ‖ = 1 → ∀ (r : ℕ)
      (ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (a b : Bool),
      tensorLeft (clusterTwoActualBranchMap ζ ξ a b) ρ =
        (1 / 4 : ℂ) • (TensorGate (clusterJ ξ * clusterJ ζ) (1 : Operator r) * ρ *
          (TensorGate (clusterJ ξ * clusterJ ζ) (1 : Operator r))ᴴ) ∧
      (∑ o : Bool × Bool, tensorLeft (clusterTwoActualBranchMap ζ ξ o.1 o.2) ρ) =
        TensorGate (clusterJ ξ * clusterJ ζ) (1 : Operator r) * ρ *
          (TensorGate (clusterJ ξ * clusterJ ζ) (1 : Operator r))ᴴ := by
  intro ζ ξ _ _ r ρ a b
  have hgen : ∀ (a' b' : Bool),
      tensorLeft (clusterTwoActualBranchMap ζ ξ a' b') ρ
        = (1 / 4 : ℂ) • tensorLeft (conjBranch (clusterJ ξ * clusterJ ζ)) ρ := by
    intro a' b'
    ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp only [tensorLeft, clusterTwoActualBranchMap_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · rw [hgen a b, tensorLeft_conjBranch]
  · rw [Finset.sum_congr rfl fun o _ => by rw [hgen o.1 o.2, tensorLeft_conjBranch],
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul]

/-- The relabeled final-register Hadamard gate is unitary. -/
theorem clusterTwoHcGate_unitary : clusterTwoHcGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary) _

/-- The first-register phase operator is unitary when `ζ` has unit modulus. -/
theorem clusterTwoPhaseAB_unitary (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    clusterTwoPhaseAB ζ ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ :=
  tensorGate_unitary (tensorGate_unitary (diagonal_mem_unitaryGroup _ fun a => by
    cases a <;> simp [hζ]) (Submonoid.one_mem _)) (Submonoid.one_mem _)

/-- The relabeled first-register phase operator is unitary when `ζ` has unit modulus. -/
theorem clusterTwoPhaseAGate_unitary (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    clusterTwoPhaseAGate ζ ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (clusterTwoPhaseAB_unitary ζ hζ) _

/-- The first-to-middle controlled-Z operator is unitary in the Boolean basis. -/
theorem clusterTwoCZabB_unitary :
    clusterTwoCZabB ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  obtain ⟨⟨a1, a2⟩, a3⟩ := p
  cases a1 <;> cases a2 <;> cases a3 <;> simp

/-- The relabeled first-to-middle controlled-Z operator is unitary. -/
theorem clusterTwoCZabGate_unitary : clusterTwoCZabGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterTwoCZabB_unitary _

/-- The relabeled middle-to-final controlled-Z operator is unitary. -/
theorem clusterCZbcGate_unitary : clusterCZbcGate ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZbcB_unitary _

/-- The middle-register phase operator is unitary when `ξ` has unit modulus. -/
theorem clusterTwoPhaseBB_unitary (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    clusterTwoPhaseBB ξ ∈ Matrix.unitaryGroup ((Bool × Bool) × Bool) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _)
    (diagonal_mem_unitaryGroup _ fun b => by cases b <;> simp [hξ])) (Submonoid.one_mem _)

/-- The relabeled middle-register phase operator is unitary when `ξ` has unit modulus. -/
theorem clusterTwoPhaseBGate_unitary (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    clusterTwoPhaseBGate ξ ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (clusterTwoPhaseBB_unitary ξ hξ) _

/-- The relabeled conditional final-register X correction is unitary. -/
theorem clusterTwoXcGate_unitary (b : Bool) :
    clusterTwoXcGate b ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (teleportXcB_unitary b) _

set_option maxHeartbeats 1000000 in

/-- For unit-modulus phases, the two-step wire program is well formed with four leaves. Each
leaf accepts, uses eleven gates and two measurements with no queries, and records the two
outcomes, giving explicit costs for the propagation in [RaussendorfBriegel2000]. -/
theorem cluster_two_actual_program_cost :
    ∀ (ζ ξ : ℂ), ‖ζ‖ = 1 → ‖ξ‖ = 1 →
      observedWellFormed (clusterTwoProgram ζ ξ) ∧
        observedLeafCount (clusterTwoProgram ζ ξ) = 4 ∧
        (∀ a b : Bool, (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).accepted
              = true ∧
            (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).queries = 0 ∧
            (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).gates = 11 ∧
            (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).measurements = 2 ∧
            (observedLeaf 1 (clusterTwoProgram ζ ξ) (clusterTwoLeaf ζ ξ a b)).outcomes
              = [(2, (boolEquivFin2 a).val), (2, (boolEquivFin2 b).val)]) := by
  intro ζ ξ hζ hξ
  refine ⟨?_, rfl, ?_⟩
  · simp only [clusterTwoProgram, observedWellFormed]
    exact ⟨teleportHbGate_unitary, clusterTwoHcGate_unitary, clusterTwoPhaseAGate_unitary ζ hζ,
      clusterTwoCZabGate_unitary, clusterCZbcGate_unitary, teleportHaGate_unitary,
      fun k => ⟨clusterBobXbGate_unitary _, ⟨clusterBobZcGate_unitary _,
        ⟨clusterTwoPhaseBGate_unitary ξ hξ, ⟨teleportHbGate_unitary,
          fun k' => ⟨clusterTwoXcGate_unitary _, trivial⟩⟩⟩⟩⟩⟩
  · intro a b
    cases a <;> cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One-step and two-step wire messages have lengths one and two and encode their outcomes
injectively; the two-step outcome map also indexes all leaves bijectively. These are the
classical feedback counts for wire propagation in [RaussendorfBriegel2000]. -/
theorem cluster_wire_classical_feedback_cost :
    (∀ b : Bool, (clusterWireMessage b).length = 1) ∧ Function.Injective clusterWireMessage ∧
      (∀ a b : Bool, (clusterTwoMessage a b).length = 2) ∧
      Function.Injective (fun o : Bool × Bool => clusterTwoMessage o.1 o.2) ∧
      (∀ ζ ξ : ℂ, Function.Bijective (fun o : Bool × Bool => clusterTwoLeaf ζ ξ o.1 o.2)) := by
  refine ⟨fun b => by simp [clusterWireMessage], ?_,
    fun a b => by simp [clusterTwoMessage], ?_, ?_⟩
  · intro a b hab
    simp [clusterWireMessage] at hab
    cases a <;> cases b <;> simp_all
  · intro a b hab
    simp [clusterTwoMessage] at hab
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    simp_all
  · intro ζ ξ
    constructor
    · intro a b hab
      have hv : (clusterTwoLeaf ζ ξ a.1 a.2).val = (clusterTwoLeaf ζ ξ b.1 b.2).val :=
        congrArg Fin.val hab
      rcases a with ⟨a1, a2⟩
      rcases b with ⟨b1, b2⟩
      simp only [clusterTwoLeaf, Fin.val_cast, teleportOutcomeEquiv_val] at hv
      cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp_all [boolEquivFin2]
    · intro j
      refine ⟨teleportOutcomeEquiv.symm
          (j.cast (rfl : observedLeafCount (clusterTwoProgram ζ ξ) = 4)), ?_⟩
      have hval : (clusterTwoLeaf ζ ξ
          (teleportOutcomeEquiv.symm
            (j.cast (rfl : observedLeafCount (clusterTwoProgram ζ ξ) = 4))).1
          (teleportOutcomeEquiv.symm
            (j.cast (rfl : observedLeafCount (clusterTwoProgram ζ ξ) = 4))).2).val = j.val := by
        fin_cases j <;> simp [clusterTwoLeaf] <;> rfl
      exact Fin.eq_of_val_eq hval

end Qatlib.Concepts.ClusterPatterns.WireComposition

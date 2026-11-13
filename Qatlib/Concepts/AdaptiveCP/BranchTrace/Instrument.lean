/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import QuantumInfo.Measurements.POVM

/-!
# Finite quantum instruments and their probability laws

This module develops `Instrument`, a finite family of completely positive, trace-nonincreasing
maps whose sum preserves trace. It defines outcome probabilities, conditional states, coarse
graining, sequential composition, feed-forward composition, and extension by an untouched
reference system.

Kraus, projective, unitary, and POVM constructions connect instruments to pure-state Born
probabilities and to `CPTPMap` channels retaining a classical outcome register. For background,
see [DaviesLewis1970].

## Main statements

* `Instrument`: A finite quantum instrument consists of completely positive, trace-nonincreasing
  branch maps whose total output trace equals the input trace.
* `Instrument.ofKraus`: Construct an instrument from one Kraus operator per outcome satisfying
  the completeness identity `∑ o, (K o).conjTranspose * K o = 1`.
* `Instrument.toCQChannel`: The channel retaining the quantum branch output together with a
  classical outcome register as a block-diagonal operator.
* `Instrument.ofPOVM`: The square-root instrument of a POVM, using the positive square root of
  each effect as its Kraus operator.

## References

* [Davies and Lewis, 1970][DaviesLewis1970]
* [Kraus, 1971][Kraus1971]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdaptiveCP.BranchTrace

open Matrix
open scoped ComplexOrder
open scoped Kronecker

variable {D E F R : ℕ}

/-- An operator map is trace-nonincreasing when the real trace of its output is at most the real
input trace on every positive semidefinite input. -/
def TraceNonIncreasing (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∀ ⦃A : Operator D⦄, A.PosSemidef → (Matrix.trace (T A)).re ≤ (Matrix.trace A).re

/-- The sum of two completely positive maps is completely positive. -/
theorem CompletelyPositive.add {S T : Operator D →ₗ[ℂ] Operator E}
    (hS : CompletelyPositive S) (hT : CompletelyPositive T) :
    CompletelyPositive (S + T) :=
  (Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mpr
    (((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp hS).add
      ((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp hT))

/-- A finite sum of completely positive maps is completely positive. -/
theorem CompletelyPositive.sum {O : Type*} [Fintype O] {T : O → (Operator D →ₗ[ℂ] Operator E)}
    {s : Finset O} (h : ∀ o ∈ s, CompletelyPositive (T o)) :
    CompletelyPositive (∑ o ∈ s, T o) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro r A _
    have hEq : ChannelAmplification (0 : Operator D →ₗ[ℂ] Operator E) r A = 0 := by
      ext x y
      simp [ChannelAmplification]
    rw [Finset.sum_empty, hEq]
    exact Matrix.PosSemidef.zero
  | insert o s ho ih =>
    rw [Finset.sum_insert ho]
    exact CompletelyPositive.add (h o (Finset.mem_insert_self o s)) (ih fun p hp =>
      h p (Finset.mem_insert_of_mem hp))

variable {O : Type*} [Fintype O]

/-- A finite quantum instrument consists of completely positive, trace-nonincreasing branch maps
whose total output trace equals the input trace. -/
structure Instrument (O : Type*) [Fintype O] (D E : ℕ) where

  branch : O → (Operator D →ₗ[ℂ] Operator E)

  cp : ∀ o, CompletelyPositive (branch o)

  tni : ∀ o, TraceNonIncreasing (branch o)

  total : ∀ A, Matrix.trace (∑ o, branch o A) = Matrix.trace A

/-- Construct an instrument from completely positive branch maps whose sum preserves trace; the
trace bound for each branch follows from positivity. -/
noncomputable def Instrument.ofBranches
    (B : O → (Operator D →ₗ[ℂ] Operator E))
    (hCP : ∀ o, CompletelyPositive (B o))
    (hTP : ∀ A, Matrix.trace (∑ o, B o A) = Matrix.trace A) : Instrument O D E where
  branch := B
  cp := hCP
  total := hTP
  tni o := by
    intro A hA
    have hm : ∀ p, 0 ≤ (Matrix.trace (B p A)).re :=
      fun p => (RCLike.nonneg_iff.mp ((hCP p).positive hA).trace_nonneg).1
    calc (Matrix.trace (B o A)).re ≤ ∑ p, (Matrix.trace (B p A)).re :=
        Finset.single_le_sum (fun p _ => hm p) (Finset.mem_univ o)
      _ = (Matrix.trace A).re := by
        rw [← Complex.re_sum, ← Matrix.trace_sum, hTP]

/-- The real trace of the unnormalized output of branch `o`, giving its probability on a density
operator. -/
noncomputable def instrumentProb (I : Instrument O D E) (ρ : Operator D) (o : O) : ℝ :=
  (Matrix.trace (I.branch o ρ)).re

/-- Instrument branch probabilities are nonnegative on positive semidefinite inputs. -/
theorem instrumentProb_nonneg (I : Instrument O D E) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (o : O) : 0 ≤ instrumentProb I ρ o :=
  (RCLike.nonneg_iff.mp ((I.cp o).positive hρ).trace_nonneg).1

/-- The sum of all instrument branch probabilities equals the real trace of the input operator. -/
theorem sum_instrumentProb (I : Instrument O D E) (ρ : Operator D) :
    ∑ o, instrumentProb I ρ o = (Matrix.trace ρ).re := by
  calc (∑ o, instrumentProb I ρ o)
      = (Matrix.trace (∑ o, I.branch o ρ)).re := by
          rw [Matrix.trace_sum, Complex.re_sum]
          rfl
    _ = (Matrix.trace ρ).re := congrArg Complex.re (I.total ρ)

/-- The instrument probabilities of a density operator sum to one. -/
theorem sum_instrumentProb_isDensityOperator (I : Instrument O D E) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) : ∑ o, instrumentProb I ρ o = 1 := by
  rw [sum_instrumentProb, hρ.2]
  rfl

/-- On a positive semidefinite input, a branch trace is the complex embedding of its real branch
probability. -/
theorem trace_branch_eq (I : Instrument O D E) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (o : O) :
    Matrix.trace (I.branch o ρ) = ((instrumentProb I ρ o : ℝ) : ℂ) := by
  have himg : (Matrix.trace (I.branch o ρ)).im = 0 :=
    (RCLike.nonneg_iff.mp ((I.cp o).positive hρ).trace_nonneg).2
  refine Complex.ext ?_ ?_
  · rfl
  · rw [himg, Complex.ofReal_im]

/-- For a positive semidefinite input, a branch has zero probability exactly when its output
operator is zero. -/
theorem instrumentProb_eq_zero_iff (I : Instrument O D E) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (o : O) :
    instrumentProb I ρ o = 0 ↔ I.branch o ρ = 0 := by
  constructor
  · intro hz
    apply (Matrix.PosSemidef.trace_eq_zero_iff ((I.cp o).positive hρ)).mp
    rw [trace_branch_eq I hρ o, hz]
    rfl
  · intro hz
    rw [instrumentProb, hz]
    simp


/-- The branch output divided by its strictly positive probability, defining the normalized
conditional operator. -/
noncomputable def Instrument.conditionalState (I : Instrument O D E) (ρ : Operator D)
    (o : O) (_h : 0 < instrumentProb I ρ o) : Operator E :=
  ((instrumentProb I ρ o : ℝ) : ℂ)⁻¹ • I.branch o ρ

/-- Conditioning an instrument outcome of positive probability on a density operator produces a
density operator. -/
theorem Instrument.isDensityOperator_conditionalState (I : Instrument O D E)
    {ρ : Operator D} (hρ : IsDensityOperator ρ) (o : O)
    (h : 0 < instrumentProb I ρ o) :
    IsDensityOperator (I.conditionalState ρ o h) := by
  have hpos : (I.branch o ρ).PosSemidef := (I.cp o).positive hρ.1
  have hinv : (0 : ℂ) ≤ (((instrumentProb I ρ o : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr h.le)
  have hne : ((instrumentProb I ρ o : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h
  refine ⟨Matrix.PosSemidef.smul hpos hinv, ?_⟩
  rw [Instrument.conditionalState, Matrix.trace_smul, trace_branch_eq I hρ.1 o,
    smul_eq_mul, inv_mul_cancel₀ hne]

/-- The quantum channel obtained by summing all instrument branches and discarding the outcome. -/
noncomputable def Instrument.forget (I : Instrument O D E) : QuantumChannel D E where
  map := ∑ o, I.branch o
  completelyPositive := CompletelyPositive.sum fun o _ => I.cp o
  tracePreserving := fun A => by
    rw [LinearMap.sum_apply]
    exact I.total A

/-- The channel obtained by forgetting an outcome applies as the sum of the branch outputs. -/
@[simp] theorem Instrument.forget_apply (I : Instrument O D E) (ρ : Operator D) :
    I.forget.map ρ = ∑ o, I.branch o ρ :=
  LinearMap.sum_apply _ _ ρ

/-- The sum of branch probabilities equals the real trace of the output of the channel that
forgets the outcome. -/
theorem instrumentProb_eq_forget_trace (I : Instrument O D E) (ρ : Operator D) :
    ∑ o, instrumentProb I ρ o = (Matrix.trace (I.forget.map ρ)).re := by
  rw [Instrument.forget_apply, I.total ρ]
  exact sum_instrumentProb I ρ

variable {P : Type*} [Fintype P] [instDecidableEqP : DecidableEq P]

/-- Coarse-grain an instrument along an outcome map by summing the branches with the same image. -/
noncomputable def Instrument.coarsen (I : Instrument O D E) (f : O → P) :
    Instrument P D E where
  branch p := ∑ o ∈ Finset.univ.filter (fun o => f o = p), I.branch o
  cp p := CompletelyPositive.sum fun o _ => I.cp o
  tni p := by
    intro A hA
    have hsum : Matrix.trace ((∑ o ∈ Finset.univ.filter (fun o => f o = p), I.branch o) A)
        = ∑ o ∈ Finset.univ.filter (fun o => f o = p), Matrix.trace (I.branch o A) := by
      rw [LinearMap.sum_apply, Matrix.trace_sum]
    calc (Matrix.trace ((∑ o ∈ Finset.univ.filter (fun o => f o = p), I.branch o) A)).re
        = ∑ o ∈ Finset.univ.filter (fun o => f o = p),
            instrumentProb I A o := by rw [hsum, Complex.re_sum]; rfl
      _ ≤ ∑ o : O, instrumentProb I A o :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (fun o _ _ => instrumentProb_nonneg I hA o)
      _ = (Matrix.trace A).re := sum_instrumentProb I A
  total := by
    intro A
    have h1 : ∀ p : P, Matrix.trace ((∑ o ∈ Finset.univ.filter (fun o => f o = p),
        I.branch o) A)
        = ∑ o ∈ Finset.univ.filter (fun o => f o = p), Matrix.trace (I.branch o A) := by
      intro p
      rw [LinearMap.sum_apply, Matrix.trace_sum]
    calc Matrix.trace (∑ p : P, (∑ o ∈ Finset.univ.filter (fun o => f o = p),
            I.branch o) A)
        = ∑ p : P, ∑ o ∈ Finset.univ.filter (fun o => f o = p),
            Matrix.trace (I.branch o A) := by
          rw [Matrix.trace_sum]
          exact Finset.sum_congr rfl fun p _ => h1 p
      _ = ∑ o : O, Matrix.trace (I.branch o A) :=
          Finset.sum_fiberwise Finset.univ f
            (fun o => Matrix.trace (I.branch o A))
      _ = Matrix.trace A := by
          rw [← Matrix.trace_sum]
          exact I.total A

/-- A coarse-grained outcome probability is the sum of the original probabilities over its
fiber. -/
theorem instrumentProb_coarsen (I : Instrument O D E) (f : O → P) (ρ : Operator D)
    (p : P) :
    instrumentProb (I.coarsen f) ρ p
      = ∑ o ∈ Finset.univ.filter (fun o => f o = p), instrumentProb I ρ o := by
  show (Matrix.trace ((∑ o ∈ Finset.univ.filter (fun o => f o = p), I.branch o) ρ)).re
      = ∑ o ∈ Finset.univ.filter (fun o => f o = p), instrumentProb I ρ o
  rw [LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum]
  rfl

/-- Forgetting the outcome after coarse graining gives the same output as forgetting the
original outcome. -/
theorem Instrument.forget_coarsen_apply (I : Instrument O D E) (f : O → P)
    (ρ : Operator D) : (I.coarsen f).forget.map ρ = I.forget.map ρ := by
  simp only [Instrument.forget_apply, Instrument.coarsen, LinearMap.sum_apply]
  exact Finset.sum_fiberwise Finset.univ f (fun o => I.branch o ρ)

/-- Sequentially compose two instruments, retaining the pair of outcomes and composing their
branch maps in execution order. -/
noncomputable def Instrument.seq (I : Instrument O D E) (J : Instrument P E F) :
    Instrument (O × P) D F where
  branch op := (J.branch op.2).comp (I.branch op.1)
  cp op := (J.cp op.2).comp (I.cp op.1)
  tni op := by
    intro A hA
    have hmid := (I.cp op.1).positive hA
    exact le_trans (J.tni op.2 hmid) (I.tni op.1 hA)
  total := by
    intro A
    have hsplit : (∑ op : O × P, ((J.branch op.2).comp (I.branch op.1)) A)
        = ∑ o : O, ∑ p : P, J.branch p (I.branch o A) := by
      calc (∑ op : O × P, ((J.branch op.2).comp (I.branch op.1)) A)
          = ∑ op : O × P, J.branch op.2 (I.branch op.1 A) :=
              Finset.sum_congr rfl fun op _ => rfl
        _ = ∑ o : O, ∑ p : P, J.branch p (I.branch o A) :=
              Fintype.sum_prod_type' (fun o p => J.branch p (I.branch o A))
    calc Matrix.trace (∑ op : O × P, ((J.branch op.2).comp (I.branch op.1)) A)
        = ∑ o : O, Matrix.trace (∑ p : P, J.branch p (I.branch o A)) := by
          rw [hsplit, Matrix.trace_sum]
      _ = ∑ o : O, Matrix.trace (I.branch o A) :=
          Finset.sum_congr rfl fun o _ => J.total (I.branch o A)
      _ = Matrix.trace A := by
          rw [← Matrix.trace_sum]
          exact I.total A

omit [DecidableEq P] in

/-- The joint branch probability of sequential instruments is the second branch probability
evaluated on the first unnormalized branch output. -/
theorem instrumentProb_seq (I : Instrument O D E) (J : Instrument P E F)
    (ρ : Operator D) (o : O) (p : P) :
    instrumentProb (I.seq J) ρ (o, p) = instrumentProb J (I.branch o ρ) p := rfl

/-- Summing a sequential instrument probability over the second outcome recovers the first
outcome probability. -/
theorem sum_instrumentProb_seq_snd (I : Instrument O D E) (J : Instrument P E F)
    (ρ : Operator D) (o : O) :
    ∑ p : P, instrumentProb (I.seq J) ρ (o, p) = instrumentProb I ρ o := by
  let _ := instDecidableEqP
  exact calc ∑ p : P, instrumentProb (I.seq J) ρ (o, p)
      = ∑ p : P, instrumentProb J (I.branch o ρ) p :=
          Finset.sum_congr rfl fun p _ => instrumentProb_seq I J ρ o p
    _ = instrumentProb I ρ o := sum_instrumentProb J (I.branch o ρ)

variable {Q : O → Type*} [∀ o, Fintype (Q o)]

/-- Compose an instrument with a second instrument chosen by its outcome, retaining a dependent
pair of outcomes. -/
noncomputable def Instrument.feedForward (I : Instrument O D E)
    (J : ∀ o, Instrument (Q o) E F) : Instrument ((o : O) × Q o) D F where
  branch σ := ((J σ.1).branch σ.2).comp (I.branch σ.1)
  cp σ := ((J σ.1).cp σ.2).comp (I.cp σ.1)
  tni σ := by
    intro A hA
    have hmid := (I.cp σ.1).positive hA
    exact le_trans ((J σ.1).tni σ.2 hmid) (I.tni σ.1 hA)
  total := by
    intro A
    have hsplit : (∑ σ : (o : O) × Q o, (((J σ.1).branch σ.2).comp (I.branch σ.1)) A)
        = ∑ o : O, ∑ p : Q o, (J o).branch p (I.branch o A) := by
      calc (∑ σ : (o : O) × Q o, (((J σ.1).branch σ.2).comp (I.branch σ.1)) A)
          = ∑ σ : (o : O) × Q o, (J σ.1).branch σ.2 (I.branch σ.1 A) :=
              Finset.sum_congr rfl fun σ _ => rfl
        _ = ∑ o : O, ∑ p : Q o, (J o).branch p (I.branch o A) := by
              exact Fintype.sum_sigma
                (fun σ : (o : O) × Q o => (J σ.1).branch σ.2 (I.branch σ.1 A))
    calc Matrix.trace (∑ σ : (o : O) × Q o, (((J σ.1).branch σ.2).comp (I.branch σ.1)) A)
        = ∑ o : O, Matrix.trace (∑ p : Q o, (J o).branch p (I.branch o A)) := by
          rw [hsplit, Matrix.trace_sum]
      _ = ∑ o : O, Matrix.trace (I.branch o A) :=
          Finset.sum_congr rfl fun o _ => (J o).total (I.branch o A)
      _ = Matrix.trace A := by
          rw [← Matrix.trace_sum]
          exact I.total A

/-- The probability of a feed-forward branch is the chosen second instrument probability on the
first unnormalized branch output. -/
theorem instrumentProb_feedForward (I : Instrument O D E) (J : ∀ o, Instrument (Q o) E F)
    (ρ : Operator D) (o : O) (p : Q o) :
    instrumentProb (I.feedForward J) ρ ⟨o, p⟩
      = instrumentProb (J o) (I.branch o ρ) p := rfl

/-- Summing the feed-forward branch probabilities over the second outcome recovers the first
outcome probability. -/
theorem sum_instrumentProb_feedForward_snd (I : Instrument O D E)
    (J : ∀ o, Instrument (Q o) E F) (ρ : Operator D) (o : O) :
    ∑ p : Q o, instrumentProb (I.feedForward J) ρ ⟨o, p⟩ = instrumentProb I ρ o :=
  calc ∑ p : Q o, instrumentProb (I.feedForward J) ρ ⟨o, p⟩
      = ∑ p : Q o, instrumentProb (J o) (I.branch o ρ) p :=
          Finset.sum_congr rfl fun p _ => instrumentProb_feedForward I J ρ o p
    _ = instrumentProb I ρ o := sum_instrumentProb (J o) (I.branch o ρ)

/-- A zero-probability first branch on a positive semidefinite input remains the zero operator
after every feed-forward branch. -/
theorem Instrument.feedForward_zero_branch (I : Instrument O D E)
    (J : ∀ o, Instrument (Q o) E F) {ρ : Operator D} (hρ : ρ.PosSemidef)
    {o : O} (ho : instrumentProb I ρ o = 0) (p : Q o) :
    (I.feedForward J).branch ⟨o, p⟩ ρ = 0 := by
  change (J o).branch p (I.branch o ρ) = 0
  rw [(instrumentProb_eq_zero_iff I hρ o).mp ho, map_zero]

/-- The partial trace over the first tensor factor, leaving the reference-system operator. -/
noncomputable abbrev partialTraceFirst {R : ℕ}
    (A : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) : Operator R :=
  Matrix.traceLeft A

/-- Apply an operator map to the first tensor factor while leaving the second factor unchanged. -/
noncomputable def tensorLeft (T : Operator D →ₗ[ℂ] Operator E) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ :=
  fun x y => T (fun i j => ρ (i, x.2) (j, y.2)) x.1 y.1

/-- Summing all instrument branches acting on the first system leaves the reference marginal
unchanged. -/
theorem Instrument.referenceMarginal (I : Instrument O D E) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    partialTraceFirst (∑ o, tensorLeft (I.branch o) ρ) = partialTraceFirst ρ := by
  ext r r'
  have hstep : ∀ o : O, ∑ a : Fin E, tensorLeft (I.branch o) ρ (a, r) (a, r')
      = Matrix.trace (I.branch o (fun i j => ρ (i, r) (j, r'))) := by
    intro o
    simp only [Matrix.trace, Matrix.diag_apply, tensorLeft]
  show (∑ a : Fin E, (∑ o : O, tensorLeft (I.branch o) ρ) (a, r) (a, r'))
      = ∑ a : Fin D, ρ (a, r) (a, r')
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]
  have h2 : (∑ o : O, ∑ a : Fin E, tensorLeft (I.branch o) ρ (a, r) (a, r'))
      = ∑ o : O, Matrix.trace (I.branch o (fun i j => ρ (i, r) (j, r'))) :=
    Finset.sum_congr rfl fun o _ => hstep o
  rw [h2, ← Matrix.trace_sum, I.total]
  rfl

/-- The blockwise definition of `tensorLeft` equals the tensor product of the operator map with
the identity map. -/
theorem tensorLeft_eq_physlib (T : Operator D →ₗ[ℂ] Operator E) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft T ρ =
      MatrixMap.kron T (LinearMap.id : MatrixMap (Fin R) (Fin R) ℂ) ρ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact (Qatlib.Concepts.ChannelTheory.Stinespring.kron_id_apply T R ρ i j a b).symm

/-- Extending a completely positive map by the identity on a reference system preserves positive
semidefiniteness. -/
theorem tensorLeft_posSemidef {T : Operator D →ₗ[ℂ] Operator E}
    (hT : CompletelyPositive T) {R : ℕ}
    {ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ} (hρ : ρ.PosSemidef) :
    (tensorLeft T ρ).PosSemidef := by
  rw [tensorLeft_eq_physlib]
  exact (Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib T).mp hT R hρ

/-- The sum of instrument branches extended by the reference identity preserves the full trace. -/
theorem Instrument.tensorLeft_total (I : Instrument O D E) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix.trace (∑ o, tensorLeft (I.branch o) ρ) = Matrix.trace ρ := by
  calc Matrix.trace (∑ o, tensorLeft (I.branch o) ρ)
      = Matrix.trace (partialTraceFirst (∑ o, tensorLeft (I.branch o) ρ)) :=
        (Matrix.traceLeft_trace _).symm
    _ = Matrix.trace (partialTraceFirst ρ) := congrArg Matrix.trace (I.referenceMarginal ρ)
    _ = Matrix.trace ρ := Matrix.traceLeft_trace _

/-- Each instrument branch extended by the reference identity is trace-nonincreasing on positive
semidefinite inputs. -/
theorem Instrument.tensorLeft_tni (I : Instrument O D E) {R : ℕ}
    {ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ} (hρ : ρ.PosSemidef) (o : O) :
    (Matrix.trace (tensorLeft (I.branch o) ρ)).re ≤ (Matrix.trace ρ).re := by
  have hm : ∀ p, 0 ≤ (Matrix.trace (tensorLeft (I.branch p) ρ)).re :=
    fun p => (RCLike.nonneg_iff.mp (tensorLeft_posSemidef (I.cp p) hρ).trace_nonneg).1
  calc (Matrix.trace (tensorLeft (I.branch o) ρ)).re
      ≤ ∑ p, (Matrix.trace (tensorLeft (I.branch p) ρ)).re :=
        Finset.single_le_sum (fun p _ => hm p) (Finset.mem_univ o)
    _ = (Matrix.trace ρ).re := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, I.tensorLeft_total]

/-- The conjugation map sending an operator `ρ` to `M * ρ * M.conjTranspose`. -/
noncomputable abbrev conjBranch (M : Matrix (Fin E) (Fin D) ℂ) :
    Operator D →ₗ[ℂ] Operator E := MatrixMap.conj M

/-- Applying `conjBranch M` gives the matrix product `M * ρ * M.conjTranspose`. -/
@[simp] theorem conjBranch_apply (M : Matrix (Fin E) (Fin D) ℂ) (ρ : Operator D) :
    conjBranch M ρ = M * ρ * M.conjTranspose := rfl

/-- Amplifying a conjugation branch by an identity factor gives conjugation by the Kronecker
product of that identity with `M`. -/
theorem channelAmplification_conjBranch (M : Matrix (Fin E) (Fin D) ℂ) (r : ℕ)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    ChannelAmplification (conjBranch M) r A
      = MatrixMap.conj ((1 : Operator r) ⊗ₖ M) A := by
  ext ⟨a, e⟩ ⟨b, e'⟩
  simp [ChannelAmplification, conjBranch, MatrixMap.conj, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, apply_ite]

/-- Conjugation by any rectangular complex matrix is completely positive. -/
theorem completelyPositive_conjBranch (M : Matrix (Fin E) (Fin D) ℂ) :
    CompletelyPositive (conjBranch M) :=
  (Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mpr (MatrixMap.congruence_CP M)

/-- Construct an instrument from one Kraus operator per outcome satisfying the completeness
identity `∑ o, (K o).conjTranspose * K o = 1`. -/
noncomputable def Instrument.ofKraus
    (K : O → Matrix (Fin E) (Fin D) ℂ)
    (hK : ∑ o, (K o).conjTranspose * K o = 1) : Instrument O D E :=
  Instrument.ofBranches (fun o => conjBranch (K o))
    (fun o => completelyPositive_conjBranch (K o)) (by
      intro A
      have h := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving K K hK A
      simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
        AddHom.coe_mk, conjBranch_apply] using h)

/-- The outcome branch of the Kraus instrument maps `ρ` to `K o * ρ * (K o).conjTranspose`. -/
@[simp] theorem Instrument.ofKraus_branch
    (K : O → Matrix (Fin E) (Fin D) ℂ)
    (hK : ∑ o, (K o).conjTranspose * K o = 1) (o : O) (ρ : Operator D) :
    (Instrument.ofKraus K hK).branch o ρ = K o * ρ * (K o).conjTranspose := rfl

/-- Composing conjugation branches for `N` and then `M` gives the conjugation branch for `M *
N`. -/
theorem conjBranch_comp (M : Matrix (Fin E) (Fin D) ℂ) (N : Matrix (Fin D) (Fin F) ℂ) :
    (conjBranch M).comp (conjBranch N) = conjBranch (M * N) := by
  apply LinearMap.ext
  intro ρ
  show conjBranch M (conjBranch N ρ) = (M * N) * ρ * (M * N).conjTranspose
  rw [Matrix.conjTranspose_mul]
  simp only [conjBranch_apply, Matrix.mul_assoc]

/-- Conjugation by `M` sends the outer product of `ψ` to the outer product of `M *ᵥ ψ`. -/
theorem conjBranch_outerProduct (M : Matrix (Fin E) (Fin D) ℂ) (ψ : QState (Fin D)) :
    conjBranch M (outerProduct ψ) = outerProduct (M *ᵥ ψ) := by
  change M * Matrix.vecMulVec ψ (fun i => star (ψ i)) * M.conjTranspose =
    Matrix.vecMulVec (M *ᵥ ψ) (fun i => star ((M *ᵥ ψ) i))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  funext j
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    mul_comm]

/-- Conjugation by the singleton coordinate projector keeps only the selected diagonal entry of
an operator. -/
theorem conjBranch_projector_apply (i : Fin D) (X : Operator D) :
    conjBranch (Projector ({i} : Finset (Fin D))) X
      = Matrix.diagonal fun j => if j = i then X i i else 0 := by
  have hP : Projector ({i} : Finset (Fin D))
      = Matrix.diagonal (fun k => if k = i then (1 : ℂ) else 0) := by
        simp only [Projector, Finset.mem_singleton]
  ext a b
  rw [conjBranch_apply, projector_conjTranspose, hP, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_apply]
  by_cases hai : a = i <;> by_cases hbi : b = i <;>
    simp_all
  aesop

/-- The computational-basis projective instrument, with each branch given by conjugation by a
singleton coordinate projector. -/
noncomputable def projectiveInstrument : Instrument (Fin D) D D where
  branch i := conjBranch (Projector ({i} : Finset (Fin D)))
  cp i := completelyPositive_conjBranch _
  tni i := by
    intro A hA
    have hdiag : ∀ j : Fin D, 0 ≤ A j j := fun j => hA.diag_nonneg
    have hre : ∀ j : Fin D, 0 ≤ (A j j).re := fun j => (RCLike.nonneg_iff.mp (hdiag j)).1
    have hentry : (Matrix.trace (conjBranch (Projector ({i} : Finset (Fin D))) A)).re
        = (A i i).re := by
      rw [conjBranch_projector_apply, Matrix.trace_diagonal, Finset.sum_ite_eq',
          ite_eq_left (Finset.mem_univ _)]
    have htotal : (Matrix.trace A).re = ∑ j : Fin D, (A j j).re := by
      simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    calc (Matrix.trace (conjBranch (Projector ({i} : Finset (Fin D))) A)).re
        = (A i i).re := hentry
      _ ≤ ∑ j : Fin D, (A j j).re := Finset.single_le_sum (fun j _ => hre j)
        (Finset.mem_univ i)
      _ = (Matrix.trace A).re := htotal.symm
  total := by
    intro A
    have hbranch : ∀ i : Fin D, Matrix.trace (conjBranch (Projector ({i} : Finset (Fin D))) A)
        = A i i := by
      intro i
      rw [conjBranch_projector_apply, Matrix.trace_diagonal, Finset.sum_ite_eq',
          ite_eq_left (Finset.mem_univ _)]
    calc Matrix.trace (∑ i, conjBranch (Projector ({i} : Finset (Fin D))) A)
        = ∑ i : Fin D, A i i := by
          rw [Matrix.trace_sum]
          exact Finset.sum_congr rfl fun i _ => hbranch i
      _ = Matrix.trace A := by simp only [Matrix.trace, Matrix.diag_apply]

/-- The probability of a computational-basis instrument outcome is the real part of the
corresponding diagonal entry. -/
theorem instrumentProb_projective (ρ : Operator D) (i : Fin D) :
    instrumentProb projectiveInstrument ρ i = (ρ i i).re := by
  rw [instrumentProb, projectiveInstrument, conjBranch_projector_apply,
    Matrix.trace_diagonal, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]

/-- On a pure-state outer product, the projective instrument probability equals the
corresponding Born probability. -/
theorem instrumentProb_projective_pure (ψ : QState (Fin D)) (i : Fin D) :
    instrumentProb projectiveInstrument (outerProduct ψ) i = BornProb ψ i := by
  rw [instrumentProb_projective, outerProduct, Matrix.of_apply]
  have hz : ∀ z : ℂ, (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
    intro z
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rfl
  exact hz (ψ i)

/-- For a pure state, coarse graining the projective instrument by `label` gives the projective
branch mass of the corresponding coordinate fiber. -/
theorem instrumentProb_coarsen_projective_pure {n : ℕ} (label : Fin D → Fin n)
    (ψ : QState (Fin D)) (o : Fin n) :
    instrumentProb (projectiveInstrument.coarsen label) (outerProduct ψ) o
      = ProjectiveBranchMass (Projector (Finset.univ.filter (fun i => label i = o))) true ψ := by
  rw [instrumentProb_coarsen]
  simp_rw [instrumentProb_projective_pure]
  change MeasureProb ψ (Finset.univ.filter (fun i => label i = o)) =
    MeasureProb (Collapse ψ (Finset.univ.filter (fun i => label i = o))) Finset.univ
  exact (sum_normSq_collapse ψ _).symm

/-- Conjugation by a unitary matrix preserves the trace of every operator. -/
theorem trace_conjBranch_unitary (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (A : Operator D) :
    Matrix.trace (conjBranch U A) = Matrix.trace A := by
  have hunit : U.conjTranspose * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [conjBranch_apply, Matrix.trace_mul_cycle, hunit, Matrix.one_mul]

/-- The instrument obtained by applying a unitary and then measuring in the computational basis. -/
noncomputable def measuredInstrument (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : Instrument (Fin D) D D :=
  Instrument.ofBranches
    (fun b => (projectiveInstrument.branch b).comp (conjBranch U))
    (fun b => (projectiveInstrument.cp b).comp (completelyPositive_conjBranch U)) (by
      intro A
      change Matrix.trace (∑ b, projectiveInstrument.branch b (conjBranch U A)) = _
      rw [projectiveInstrument.total, trace_conjBranch_unitary U hU])

/-- On a pure-state input, applying a unitary and then the measured instrument gives the Born
probability of the transformed state. -/
theorem instrumentProb_measured_pure (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (ψ : QState (Fin D)) (b : Fin D) :
    instrumentProb (measuredInstrument U hU) (outerProduct ψ) b
      = BornProb (U *ᵥ ψ) b := by
  change instrumentProb projectiveInstrument (conjBranch U (outerProduct ψ)) b = _
  rw [conjBranch_outerProduct, instrumentProb_projective_pure]

/-- The single-outcome instrument whose only branch is conjugation by the given unitary. -/
noncomputable def unitaryInstrument (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : Instrument (Fin 1) D D :=
  Instrument.ofBranches (fun _ => conjBranch U) (fun _ => completelyPositive_conjBranch U)
    (by
      intro A
      simpa only [Fin.sum_univ_one] using trace_conjBranch_unitary U hU A)

/-- The outcome probability mass function of an instrument applied to a density operator. -/
noncomputable def instrumentPMF (I : Instrument O D E) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) : PMF O :=
  PMF.ofFintype (fun o => ENNReal.ofReal (instrumentProb I ρ o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun o _ => instrumentProb_nonneg I hρ.1 o,
      sum_instrumentProb_isDensityOperator I hρ]
    simp)

/-- The outcome mass of `instrumentPMF` is `ENNReal.ofReal` of the corresponding instrument
probability. -/
@[simp] theorem instrumentPMF_apply (I : Instrument O D E) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (o : O) :
    instrumentPMF I hρ o = ENNReal.ofReal (instrumentProb I ρ o) := rfl

/-- The projective instrument probability mass function on a normalized pure state equals its
Born distribution. -/
theorem instrumentPMF_projective_pure {ψ : QState (Fin D)} (hψ : Normalized ψ) :
    instrumentPMF projectiveInstrument (isDensityOperator_outerProduct hψ)
      = bornDistribution ψ hψ := by
  ext o
  rw [instrumentPMF_apply, bornDistribution_apply, instrumentProb_projective_pure]

section ClassicalOutput

variable [instDecidableEqO : DecidableEq O]

/-- The channel retaining the quantum branch output together with a classical outcome register
as a block-diagonal operator. -/
noncomputable def Instrument.toCQChannel (I : Instrument O D E) :
    CPTPMap (Fin D) (Fin E × O) where
  toLinearMap := ∑ o, {
    toFun := fun ρ => I.branch o ρ ⊗ₖ Matrix.single o o (1 : ℂ)
    map_add' := by simp [map_add, add_mul, Matrix.kroneckerMap_add_left]
    map_smul' := by simp [Matrix.smul_kronecker]
  }
  cp := by
    apply MatrixMap.IsCompletelyPositive.finset_sum
    intro o
    let record : MatrixMap (Fin E) (Fin E × O) ℂ := {
      toFun := fun A => A ⊗ₖ Matrix.single o o (1 : ℂ)
      map_add' := by simp [add_mul, Matrix.kroneckerMap_add_left]
      map_smul' := by simp [Matrix.smul_kronecker]
    }
    have hr : record.IsCompletelyPositive :=
      MatrixMap.kron_kronecker_const
        ((Matrix.PosSemidef.stdBasisMatrix_iff_eq o o (zero_lt_one' ℂ)).mpr rfl)
    change MatrixMap.IsCompletelyPositive (record.comp (I.branch o))
    exact ((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp (I.cp o)).comp hr
  TP := by
    intro A
    simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sum,
      Matrix.trace_kronecker, Matrix.trace_single_eq_same, mul_one]
    rw [← Matrix.trace_sum]
    exact I.total A

/-- The channel retaining the outcome maps `ρ` to the sum of each branch output tensored with
its classical coordinate projector. -/
theorem Instrument.toCQChannel_apply (I : Instrument O D E) (ρ : Operator D) :
    I.toCQChannel.map ρ = ∑ o, I.branch o ρ ⊗ₖ Matrix.single o o (1 : ℂ) := by
  dsimp [Instrument.toCQChannel, HPMap.map]
  rw [LinearMap.sum_apply]
  rfl

/-- The diagonal outcome block of `Instrument.toCQChannel` is the corresponding instrument
branch output. -/
theorem Instrument.toCQChannel_block (I : Instrument O D E) (ρ : Operator D)
    (o : O) (i j : Fin E) :
    I.toCQChannel.map ρ (i, o) (j, o) = I.branch o ρ i j := by
  rw [I.toCQChannel_apply]
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single]

/-- Blocks of `Instrument.toCQChannel` between distinct classical outcomes are zero. -/
theorem Instrument.toCQChannel_off_diagonal (I : Instrument O D E) (ρ : Operator D)
    {o p : O} (hop : o ≠ p) (i j : Fin E) :
    I.toCQChannel.map ρ (i, o) (j, p) = 0 := by
  rw [I.toCQChannel_apply]
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxo : x = o
  · subst x
    simp [hop]
  · simp [hxo]

/-- Tracing out the quantum output of `Instrument.toCQChannel` gives the diagonal operator of
branch traces. -/
theorem Instrument.toCQChannel_classicalMarginal (I : Instrument O D E) (ρ : Operator D) :
    Matrix.traceLeft (I.toCQChannel.map ρ) =
      Matrix.diagonal (fun o => Matrix.trace (I.branch o ρ)) := by
  ext o p
  by_cases hop : o = p
  · subst p
    simp only [Matrix.traceLeft, Matrix.of_apply, I.toCQChannel_block,
      Matrix.diagonal_apply_eq, Matrix.trace, Matrix.diag_apply]
  · simp only [Matrix.traceLeft, Matrix.of_apply,
      I.toCQChannel_off_diagonal ρ hop, Finset.sum_const_zero,
      Matrix.diagonal_apply_ne _ hop]

omit [DecidableEq O] in

/-- The positive square roots of the effects of a POVM satisfy the Kraus completeness identity. -/
theorem povm_sqrt_complete (Λ : POVM O (Fin D)) :
    ∑ o, ((Λ.mats o ^ (1 / 2 : ℝ)).mat).conjTranspose *
      (Λ.mats o ^ (1 / 2 : ℝ)).mat = 1 := by
  simp_rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg _)]
  rw [← HermitianMat.mat_finset_sum, Λ.normalized]
  rfl

/-- The square-root instrument of a POVM, using the positive square root of each effect as its
Kraus operator. -/
noncomputable def Instrument.ofPOVM (Λ : POVM O (Fin D)) : Instrument O D D :=
  Instrument.ofKraus (fun o => (Λ.mats o ^ (1 / 2 : ℝ)).mat) (povm_sqrt_complete Λ)

/-- A branch of the POVM instrument conjugates the input by the positive square root of its
effect. -/
@[simp] theorem Instrument.ofPOVM_branch (Λ : POVM O (Fin D)) (o : O) (ρ : Operator D) :
    (Instrument.ofPOVM Λ).branch o ρ =
      (Λ.mats o ^ (1 / 2 : ℝ)).mat * ρ * (Λ.mats o ^ (1 / 2 : ℝ)).mat := by
  let _ := instDecidableEqO
  simp only [Instrument.ofPOVM, Instrument.ofKraus_branch, HermitianMat.conjTranspose_mat]

/-- The channel retaining the outcome of a POVM instrument agrees pointwise with the POVM
measurement map. -/
theorem Instrument.ofPOVM_toCQChannel_apply (Λ : POVM O (Fin D)) (ρ : Operator D) :
    (Instrument.ofPOVM Λ).toCQChannel.map ρ = Λ.measurementMap.map ρ := by
  rw [Instrument.toCQChannel_apply, Λ.measurementMap_apply_matrix]
  simp only [Instrument.ofPOVM_branch]

/-- The channel retaining the outcome of the square-root POVM instrument equals the POVM
measurement map. -/
theorem Instrument.ofPOVM_toCQChannel (Λ : POVM O (Fin D)) :
    (Instrument.ofPOVM Λ).toCQChannel = Λ.measurementMap := by
  apply CPTPMap.ext
  apply LinearMap.ext
  exact Instrument.ofPOVM_toCQChannel_apply Λ

/-- The probability of a POVM instrument branch is the real trace of its effect multiplied by
the input operator. -/
theorem instrumentProb_ofPOVM (Λ : POVM O (Fin D)) (ρ : Operator D) (o : O) :
    instrumentProb (Instrument.ofPOVM Λ) ρ o =
      (Matrix.trace ((Λ.mats o).mat * ρ)).re := by
  unfold instrumentProb
  rw [Instrument.ofPOVM_branch, Matrix.trace_mul_cycle,
    HermitianMat.pow_half_mul (Λ.nonneg o)]

/-- On a mixed state, the POVM instrument probability agrees with the probability given by
`POVM.measure`. -/
theorem instrumentProb_ofPOVM_measure (Λ : POVM O (Fin D)) (ρ : MState (Fin D)) (o : O) :
    instrumentProb (Instrument.ofPOVM Λ) ρ.m o = (Λ.measure ρ o : ℝ) := by
  rw [instrumentProb_ofPOVM]
  change (Matrix.trace ((Λ.mats o).mat * ρ.M.mat)).re = _
  exact (HermitianMat.inner_eq_re_trace (Λ.mats o) ρ.M).symm

/-- On a mixed state, the POVM instrument outcome mass equals `ENNReal.ofReal` of the POVM
measurement probability. -/
theorem instrumentPMF_ofPOVM_measure (Λ : POVM O (Fin D)) (ρ : MState (Fin D)) (o : O) :
    instrumentPMF (Instrument.ofPOVM Λ) ⟨ρ.psd, ρ.tr'⟩ o =
      ENNReal.ofReal (Λ.measure ρ o : ℝ) := by
  rw [instrumentPMF_apply, instrumentProb_ofPOVM_measure]

/-- A zero POVM effect gives the zero branch linear map in its square-root instrument. -/
theorem Instrument.ofPOVM_zero_effect_map (Λ : POVM O (Fin D)) {o : O}
    (ho : Λ.mats o = 0) : (Instrument.ofPOVM Λ).branch o = 0 := by
  have hs : (Λ.mats o ^ (1 / 2 : ℝ)).mat = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg o), ho]
    rfl
  apply LinearMap.ext
  intro ρ
  simp only [Instrument.ofPOVM_branch, hs, Matrix.zero_mul, LinearMap.zero_apply]

/-- A zero POVM effect gives zero branch output on every positive semidefinite input. -/
theorem Instrument.ofPOVM_zero_effect (Λ : POVM O (Fin D)) {o : O}
    (ho : Λ.mats o = 0) {ρ : Operator D} (hρ : ρ.PosSemidef) :
    (Instrument.ofPOVM Λ).branch o ρ = 0 := by
  apply (instrumentProb_eq_zero_iff _ hρ o).mp
  rw [instrumentProb_ofPOVM, ho]
  simp

end ClassicalOutput

end Qatlib.Concepts.AdaptiveCP.BranchTrace

open Matrix
open scoped ComplexOrder

namespace Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- If an operator map acts as scalar multiplication by `c`, extending it by a reference
identity also acts as scalar multiplication by `c`. -/
theorem tensorLeft_eq_smul {D : ℕ} {T : Operator D →ₗ[ℂ] Operator D} (c : ℂ)
    (hT : ∀ ρ : Operator D, T ρ = c • ρ) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft T ρ = c • ρ := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  show T (fun i j => ρ (i, x2) (j, y2)) x1 y1 = c * ρ (x1, x2) (y1, y2)
  rw [hT]
  simp
end Qatlib.Concepts.AdaptiveCP.BranchTrace

open Matrix
open scoped ComplexOrder

namespace Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- Coarse graining along an outcome equivalence relabels each branch by the inverse
equivalence. -/
theorem Instrument.coarsen_branch_equiv {O P : Type*} [Fintype O] [Fintype P] [DecidableEq O]
    [DecidableEq P] {D E : ℕ} (I : Instrument O D E) (e : O ≃ P) (p : P) :
    (I.coarsen e).branch p = I.branch (e.symm p) := by
  have hfiber : Finset.univ.filter (fun o : O => e o = p) = {e.symm p} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact e.injective (by rw [h, Equiv.apply_symm_apply])
    · intro h
      rw [h, Equiv.apply_symm_apply]
  show (∑ o ∈ Finset.univ.filter (fun o : O => e o = p), I.branch o) = I.branch (e.symm p)
  rw [hfiber, Finset.sum_singleton]

/-- Evaluating a branch coarse-grained along an equivalence gives the original branch at the
inverse image of the outcome. -/
theorem Instrument.coarsen_branch_equiv_apply {O P : Type*} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P] {D E : ℕ} (I : Instrument O D E) (e : O ≃ P) (p : P)
    (ρ : Operator D) :
    (I.coarsen e).branch p ρ = I.branch (e.symm p) ρ := by
  rw [Instrument.coarsen_branch_equiv I e p]
end Qatlib.Concepts.AdaptiveCP.BranchTrace

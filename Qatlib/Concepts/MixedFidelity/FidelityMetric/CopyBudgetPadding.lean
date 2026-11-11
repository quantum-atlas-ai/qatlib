/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
import QuantumInfo.Channels.Dual
import Mathlib.Analysis.Matrix.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Copy Budget Padding

All coordinates of q ordinary copies, including the unique zero-copy coordinate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder Kronecker

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding
open Qatlib.Concepts.MbqcFlow.FlowDecision

/-- All coordinates of q ordinary copies, including the unique zero-copy coordinate. -/
abbrev Copies (I : Type*) (q : ℕ) := Fin q → I

/-- The full ordinary-copy tensor amplitude contains every unknown input amplitude. -/
def copies {I : Type*} (v : I → ℂ) (q : ℕ) : Copies I q → ℂ := fun x => ∏ j,v (x j)

/-- A pure physical state has its literal rank-one density matrix. -/
def pure {I : Type*} (v : I → ℂ) : Matrix I I ℂ := fun x y => v x*star (v y)

/-- A known prefix/suffix basis splits copy coordinates without measuring them. -/
def splitCopies (I : Type*) (q r : ℕ) : Copies I (q+r) ≃ Copies I q × Copies I r :=
  (Fin.appendEquiv q r).symm

/-- The complete tensor amplitude factors through the known prefix/suffix basis. -/
theorem copies_split {I : Type*} (v : I → ℂ) (q r : ℕ) (x : Copies I (q+r)) :
    copies v (q+r) x=copies v q (splitCopies I q r x).1*copies v r (splitCopies I q r x).2 :=
  Fin.prod_univ_add (fun j => v (x j))

/-- Tensoring the prefix effect with the identity discards only unused copies at readout. -/
def pad {I : Type*} [Fintype I] [DecidableEq I] (q r : ℕ)
    (A : Matrix (Copies I q) (Copies I q) ℂ) : Matrix (Copies I (q+r)) (Copies I (q+r)) ℂ :=
  (A ⊗ₖ (1 : Matrix (Copies I r) (Copies I r) ℂ)).submatrix (splitCopies I q r) (splitCopies I q r)

/-- Padding is positive for arbitrary collective prefix effects, without any separability requirement on those effects. -/
theorem pad_positive {I : Type*} [Fintype I] [DecidableEq I] (q r : ℕ)
    (A : Matrix (Copies I q) (Copies I q) ℂ) (hA : A.PosSemidef) : (pad q r A).PosSemidef :=
  (hA.kronecker Matrix.PosSemidef.one).submatrix _

/-- Padding the identity gives the identity on all complete copy coordinates. -/
theorem pad_one {I : Type*} [Fintype I] [DecidableEq I] (q r : ℕ) :
    pad q r (1 : Matrix (Copies I q) (Copies I q) ℂ)=1 := by
  simp only [pad,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

/-- Zero stopping probability stays zero when copies are appended. -/
theorem pad_zero {I : Type*} [Fintype I] [DecidableEq I] (q r : ℕ) :
    pad q r (0 : Matrix (Copies I q) (Copies I q) ℂ)=0 := by
  simp [pad]

/-- Padding is additive on actual stopping and continuation effects. -/
theorem pad_add {I : Type*} [Fintype I] [DecidableEq I] (q r : ℕ)
    (A B : Matrix (Copies I q) (Copies I q) ℂ) : pad q r (A+B)=pad q r A+pad q r B := by
  ext x y
  simp [pad,Matrix.add_kronecker,Matrix.add_apply]

/-- The full pure density splits into the actual prefix and unused-copy densities, with no input registers removed. -/
theorem pure_copies_split {I : Type*} [Fintype I] (v : I → ℂ) (q r : ℕ) :
    pure (copies v (q+r))=
      (pure (copies v q) ⊗ₖ pure (copies v r)).submatrix (splitCopies I q r) (splitCopies I q r) := by
  ext x y
  simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,pure,copies_split,star_mul]
  ring

/-- Trace is invariant under a complete known basis bijection. -/
theorem trace_submatrix_equiv {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J J ℂ) (e : I ≃ J) : Matrix.trace (A.submatrix e e)=Matrix.trace A :=
  Equiv.sum_comp e (fun j => A j j)

/-- The unused ordinary copies have trace one, derived from the physical one-copy normalization. -/
theorem copies_trace_one {I : Type*} [Fintype I] (v : I → ℂ)
    (hv : ∑ i,v i*star (v i)=1) (q : ℕ) : Matrix.trace (pure (copies v q))=1 := by
  simp only [Matrix.trace,Matrix.diag,pure,copies,star_prod,←Finset.prod_mul_distrib]
  rw [show (∑ x : Fin q → I,∏ j,v (x j)*star (v (x j)))=
      ∏ _j : Fin q,∑ i : I,v i*star (v i) from
    (Fintype.prod_sum (fun (_j : Fin q) (i : I) => v i*star (v i))).symm]
  simp only [hv,Finset.prod_const_one]

/-- Padding unused ordinary copies preserves every actual complex Born event probability, uniformly in the unknown physical state. -/
theorem pad_probability {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℂ)
    (hv : ∑ i,v i*star (v i)=1) (q r : ℕ) (A : Matrix (Copies I q) (Copies I q) ℂ) :
    Matrix.trace (pad q r A*pure (copies v (q+r)))=Matrix.trace (A*pure (copies v q)) := by
  rw [pure_copies_split]
  simp only [pad,Matrix.submatrix_mul_equiv,trace_submatrix_equiv,
    ←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.trace_kronecker,copies_trace_one v hv,mul_one]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding

/-- A causal ordinary-copy stopping tester records actual prefix effects for arbitrary measurable real-output events. All quantum memory and classical histories may be integrated into these effects. -/
structure CausalStopping (I Ω : Type*) [Fintype I] [DecidableEq I] [MeasurableSpace Ω] (Q : ℕ) where
  /-- Event effects for stopping after exactly q physical copies. -/
  stop : (q : ℕ) → Set Ω → Matrix (Copies I q) (Copies I q) ℂ
  /-- Stopping effects are positive on measurable events. -/
  stop_positive : ∀ q s,MeasurableSet s → (stop q s).PosSemidef
  /-- The impossible output event has zero effect. -/
  stop_empty : ∀ q,stop q ∅=0
  /-- Disjoint measurable output events add without imposing finite outcomes. -/
  stop_add : ∀ q s t,MeasurableSet s → MeasurableSet t → Disjoint s t → stop q (s∪t)=stop q s+stop q t
  /-- Positive continuation effects after each prefix. -/
  continuation : (q : ℕ) → Matrix (Copies I q) (Copies I q) ℂ
  /-- Continuing branches have nonnegative physical probability. -/
  continuation_positive : ∀ q,(continuation q).PosSemidef
  /-- Before taking a copy, stopping and continuing exhaust all probability. -/
  initial : stop 0 Set.univ+continuation 0=1
  /-- Appending the next ordinary copy preserves the same continuation probability, split between stopping and continuing. -/
  causal : ∀ q,q<Q → pad q 1 (continuation q)=stop (q+1) Set.univ+continuation (q+1)
  /-- The maximum budget is an actual zero continuation effect at Q. -/
  terminal : continuation Q=0

/-- Earlier stopping effects are recursively padded through all subsequently unused copy registers. -/
def CausalStopping.cumulative {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) : (q : ℕ) → Set Ω → Matrix (Copies I q) (Copies I q) ℂ
  | 0,s => P.stop 0 s
  | q+1,s => pad q 1 (P.cumulative q s)+P.stop (q+1) s

/-- Every cumulative output event remains positive, without measuring any input address. -/
theorem CausalStopping.cumulative_positive {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) (s : Set Ω) (hs : MeasurableSet s) (q : ℕ) :
    (P.cumulative q s).PosSemidef := by
  induction q with
  | zero => exact P.stop_positive 0 s hs
  | succ q ih => exact (pad_positive q 1 _ ih).add (P.stop_positive (q+1) s hs)

/-- Padding and adding stopping probabilities preserve the impossible event. -/
theorem CausalStopping.cumulative_empty {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) (q : ℕ) : P.cumulative q ∅=0 := by
  induction q with
  | zero => exact P.stop_empty 0
  | succ q ih => simp only [cumulative,ih,pad_zero,P.stop_empty,add_zero]

/-- The final collective event map retains finite additivity on arbitrary measurable outcomes. -/
theorem CausalStopping.cumulative_add {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) (q : ℕ) :
    P.cumulative q (s∪t)=P.cumulative q s+P.cumulative q t := by
  induction q with
  | zero => exact P.stop_add 0 s t hs ht hst
  | succ q ih =>
    simp only [cumulative,ih,pad_add,P.stop_add (q+1) s t hs ht hst]
    abel

/-- The actual causal stopping/continuation equations imply normalization at every prefix. -/
theorem CausalStopping.cumulative_conservation {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) (q : ℕ) (hq : q≤Q) :
    P.cumulative q Set.univ+P.continuation q=1 := by
  induction q with
  | zero => exact P.initial
  | succ q ih =>
    have hprev := ih (by omega)
    calc
      _ = pad q 1 (P.cumulative q Set.univ)+(P.stop (q+1) Set.univ+P.continuation (q+1)) := by
        simp only [cumulative,add_assoc]
      _ = pad q 1 (P.cumulative q Set.univ)+pad q 1 (P.continuation q) := by rw [P.causal q (by omega)]
      _ = pad q 1 (P.cumulative q Set.univ+P.continuation q) := (pad_add q 1 _ _).symm
      _ = 1 := by rw [hprev,pad_one]

/-- A genuine maximum-Q stopping computation yields a normalized complete-input event effect, derived from causality and actual termination. -/
theorem CausalStopping.cumulative_total {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) : P.cumulative Q Set.univ=1 := by
  have h := P.cumulative_conservation Q le_rfl
  simpa only [P.terminal,add_zero] using h

/-- The operational output probability sums the actual branches that stop after each prefix, before any padding. -/
def CausalStopping.runProbability {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) (v : I → ℂ) (s : Set Ω) : ℕ → ℂ
  | 0 => Matrix.trace (P.stop 0 s*pure (copies v 0))
  | q+1 => P.runProbability v s q+Matrix.trace (P.stop (q+1) s*pure (copies v (q+1)))

/-- The common final-Q event map exactly preserves every actual branch-summed output probability for every normalized unknown input. -/
theorem CausalStopping.cumulative_probability {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : CausalStopping I Ω Q) (v : I → ℂ) (hv : ∑ i,v i*star (v i)=1)
    (s : Set Ω) (q : ℕ) :
    Matrix.trace (P.cumulative q s*pure (copies v q))=P.runProbability v s q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [cumulative,Matrix.add_mul,Matrix.trace_add,pad_probability v hv,ih,runProbability]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout

/-- Any complete known input basis names a causal stopping computation's final event effects. The basis does not depend on the unknown physical state or hypothesis. -/
def CausalStopping.toReadout {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q D : ℕ} (P : CausalStopping I Ω Q) (e : Fin D ≃ Copies I Q) : EventPOVM D Ω where
  effect s := (P.cumulative Q s).submatrix e e
  positive s hs := (P.cumulative_positive s hs Q).submatrix e
  empty := by rw [P.cumulative_empty]; rfl
  total := by rw [P.cumulative_total]; exact Matrix.submatrix_one_equiv e
  add s t hs ht hst := by rw [P.cumulative_add s t hs ht hst Q]; rfl

/-- Q ordinary copies in the same one known complete coordinate basis. -/
def encodedCopies {I : Type*} {Q D : ℕ} (e : Fin D ≃ Copies I Q) (v : I → ℂ) : QState (Fin D) :=
  fun i => copies v Q (e i)

/-- A maximum-Q causal stopping computation and its common full-input event readout have identical actual probabilities, for every unknown normalized input and every output event. -/
theorem CausalStopping.toReadout_probability {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q D : ℕ} (P : CausalStopping I Ω Q) (e : Fin D ≃ Copies I Q)
    (v : I → ℂ) (hv : ∑ i,v i*star (v i)=1) (s : Set Ω) :
    (P.toReadout e).born (outerProduct (encodedCopies e v)) s=(P.runProbability v s Q).re := by
  have hd : outerProduct (encodedCopies e v)=(pure (copies v Q)).submatrix e e := by
    ext i j
    rfl
  change (Matrix.trace ((P.cumulative Q s).submatrix e e*outerProduct (encodedCopies e v))).re=_
  rw [hd,Matrix.submatrix_mul_equiv,trace_submatrix_equiv,P.cumulative_probability v hv s Q]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding
open Qatlib.Concepts.LchsSimulation.StaticLchs

/-- The actual partial trace of appended ordinary-copy registers in the known complete prefix/suffix basis. -/
def discardRight {I : Type*} [Fintype I] (q r : ℕ)
    (R : Matrix (Copies I (q+r)) (Copies I (q+r)) ℂ) : Matrix (Copies I q) (Copies I q) ℂ :=
  (R.submatrix (splitCopies I q r).symm (splitCopies I q r).symm).traceRight

/-- Appending an untouched register and discarding that register are trace dual on every input matrix, not merely on a supplied testing witness. -/
theorem pad_discard_trace {I : Type*} [Fintype I] [DecidableEq I] (q r : ℕ)
    (E : Matrix (Copies I q) (Copies I q) ℂ) (R : Matrix (Copies I (q+r)) (Copies I (q+r)) ℂ) :
    Matrix.trace (pad q r E*R)=Matrix.trace (E*discardRight q r R) := by
  let e := splitCopies I q r
  have hR : (R.submatrix e.symm e.symm).submatrix e e=R := by
    ext x y
    simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]
  calc
    _ = Matrix.trace ((E ⊗ₖ (1 : Matrix (Copies I r) (Copies I r) ℂ)).submatrix e e*
        (R.submatrix e.symm e.symm).submatrix e e) := by rw [hR]; rfl
    _ = Matrix.trace ((E ⊗ₖ (1 : Matrix (Copies I r) (Copies I r) ℂ))*(R.submatrix e.symm e.symm)) := by
      rw [Matrix.submatrix_mul_equiv,trace_submatrix_equiv]
    _ = _ := by
      rw [Matrix.trace_mul_comm,Matrix.trace_mul_kron_one_right,Matrix.trace_mul_comm]
      rfl

/-- A complex-linear physical event probability is an actual one-dimensional-output operation; no retained memory dimension is imposed. -/
def scalarOperation {I : Type*} (ℓ : Matrix I I ℂ →ₗ[ℂ] ℂ) : MatrixMap I (Fin 1) ℂ :=
  (Matrix.diagonalLinearMap (R:=ℂ) (n:=Fin 1) (α:=ℂ)).comp (LinearMap.pi (fun _ : Fin 1 => ℓ))

/-- Finite-dimensional trace duality constructs an input event effect from its actual physical probability functional. -/
def probabilityEffect {I : Type*} [Fintype I] [DecidableEq I] (ℓ : Matrix I I ℂ →ₗ[ℂ] ℂ) : Matrix I I ℂ :=
  (scalarOperation ℓ).dual 1

/-- Physical positivity of event probabilities implies positivity of the internally constructed full-input effect. -/
theorem probabilityEffect_positive {I : Type*} [Fintype I] [DecidableEq I]
    (ℓ : Matrix I I ℂ →ₗ[ℂ] ℂ) (hℓ : ∀ R : Matrix I I ℂ,R.PosSemidef → 0≤ℓ R) :
    (probabilityEffect ℓ).PosSemidef := by
  have hp : (scalarOperation ℓ).IsPositive := by
    intro R hR
    exact Matrix.PosSemidef.diagonal (fun _ => hℓ R hR)
  unfold probabilityEffect
  exact hp.dual Matrix.PosSemidef.one

/-- The constructed event effect reproduces every actual linear branch probability, including arbitrary quantum memory traced at readout. -/
theorem probabilityEffect_trace {I : Type*} [Fintype I] [DecidableEq I]
    (ℓ : Matrix I I ℂ →ₗ[ℂ] ℂ) (R : Matrix I I ℂ) :
    Matrix.trace (probabilityEffect ℓ*R)=ℓ R := by
  unfold probabilityEffect
  rw [Matrix.trace_mul_comm,←MatrixMap.Dual.trace_eq,Matrix.mul_one]
  simp [scalarOperation,Matrix.trace,Matrix.diag]

/-- Operational branch-probability semantics for an ordinary-copy stopping computation. The independent prefix linear maps include all quantum memory and classical histories; only the actual output event remains. -/
structure OrdinaryCopyStopping (I Ω : Type*) [Fintype I] [DecidableEq I] [MeasurableSpace Ω] (Q : ℕ) where
  /-- The actual complex-linear probability operation for stopping after exactly q copies with an output in the given event. -/
  stop : (q : ℕ) → Set Ω → (Matrix (Copies I q) (Copies I q) ℂ →ₗ[ℂ] ℂ)
  /-- Physical event operations are positive on every positive input matrix. -/
  stop_positive : ∀ q s,MeasurableSet s → ∀ R : Matrix (Copies I q) (Copies I q) ℂ,R.PosSemidef → 0≤ stop q s R
  /-- The impossible event has zero operation. -/
  stop_empty : ∀ q,stop q ∅=0
  /-- Disjoint measurable output events add as actual input-independent linear operations. -/
  stop_add : ∀ q s t,MeasurableSet s → MeasurableSet t → Disjoint s t → stop q (s∪t)=stop q s+stop q t
  /-- Actual probability operations for continuing after each prefix. -/
  continuation : (q : ℕ) → (Matrix (Copies I q) (Copies I q) ℂ →ₗ[ℂ] ℂ)
  /-- Continuing branches are physically positive. -/
  continuation_positive : ∀ q (R : Matrix (Copies I q) (Copies I q) ℂ),R.PosSemidef → 0≤ continuation q R
  /-- With no copies consumed, stopping and continuing exhaust the input trace. -/
  initial : ∀ R,stop 0 Set.univ R+continuation 0 R=Matrix.trace R
  /-- Each ordinary-copy access splits the same physical continuation trace between stopping and continuing, after discarding only the new untouched input in the incoming branch. -/
  causal : ∀ q,q<Q → ∀ R,stop (q+1) Set.univ R+continuation (q+1) R=continuation q (discardRight q 1 R)
  /-- No positive probability branch can consume more than the maximum copy budget. -/
  terminal : ∀ R,continuation Q R=0

/-- The full causal prefix effects are derived from actual operational branch maps and ordinary-copy trace conservation. -/
def OrdinaryCopyStopping.toCausal {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : OrdinaryCopyStopping I Ω Q) : CausalStopping I Ω Q where
  stop q s := probabilityEffect (P.stop q s)
  stop_positive q s hs := probabilityEffect_positive _ (P.stop_positive q s hs)
  stop_empty q := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro R
    rw [probabilityEffect_trace,P.stop_empty]
    simp
  stop_add q s t hs ht hst := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro R
    rw [probabilityEffect_trace,Matrix.add_mul,Matrix.trace_add,probabilityEffect_trace,probabilityEffect_trace]
    exact congrArg (fun ℓ : Matrix (Copies I q) (Copies I q) ℂ →ₗ[ℂ] ℂ => ℓ R) (P.stop_add q s t hs ht hst)
  continuation q := probabilityEffect (P.continuation q)
  continuation_positive q := probabilityEffect_positive _ (P.continuation_positive q)
  initial := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro R
    rw [Matrix.add_mul,Matrix.trace_add,probabilityEffect_trace,probabilityEffect_trace,Matrix.one_mul]
    exact P.initial R
  causal q hq := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro R
    rw [pad_discard_trace,probabilityEffect_trace,Matrix.add_mul,Matrix.trace_add,
      probabilityEffect_trace,probabilityEffect_trace]
    exact (P.causal q hq R).symm
  terminal := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro R
    rw [probabilityEffect_trace,P.terminal]
    simp

/-- Operational output probability is the sum of the genuine branch operations at the prefix where the computation stops. -/
def OrdinaryCopyStopping.runProbability {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : OrdinaryCopyStopping I Ω Q) (v : I → ℂ) (s : Set Ω) : ℕ → ℂ
  | 0 => P.stop 0 s (pure (copies v 0))
  | q+1 => P.runProbability v s q+P.stop (q+1) s (pure (copies v (q+1)))

/-- The actual operational branch sum equals the derived stopping tester's branch sum, for every unknown input vector. -/
theorem OrdinaryCopyStopping.run_eq {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q : ℕ} (P : OrdinaryCopyStopping I Ω Q) (v : I → ℂ) (s : Set Ω) (q : ℕ) :
    P.toCausal.runProbability v s q=P.runProbability v s q := by
  induction q with
  | zero => exact probabilityEffect_trace _ _
  | succ q ih =>
    change P.toCausal.runProbability v s q+Matrix.trace (probabilityEffect (P.stop (q+1) s)*pure (copies v (q+1)))=_
    rw [ih,probabilityEffect_trace]
    rfl

/-- A normalized input's actual maximum-Q ordinary-copy computation has one common full-input real-event readout with exactly the same output law; padding and effect representation are derived internally. -/
theorem OrdinaryCopyStopping.readout_probability {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {Q D : ℕ} (P : OrdinaryCopyStopping I Ω Q) (e : Fin D ≃ Copies I Q)
    (v : I → ℂ) (hv : ∑ i,v i*star (v i)=1) (s : Set Ω) :
    (P.toCausal.toReadout e).born (outerProduct (encodedCopies e v)) s=(P.runProbability v s Q).re := by
  rw [P.toCausal.toReadout_probability e v hv s,P.run_eq]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.CopyBudgetPadding

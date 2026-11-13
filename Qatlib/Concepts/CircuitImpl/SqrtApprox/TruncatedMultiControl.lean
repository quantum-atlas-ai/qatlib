/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.SqrtApprox.ControlledWireNorm
import Qatlib.Foundations.OperatorErrors.OperatorError

/-!
# Truncated square-root synthesis of multi-controlled gates

This module develops the recursive controlled-gate construction underlying the approximation in
[BarencoEtAl1995]. `elementary_recursive_step` adds a control while squaring the target gate,
and `elementary_truncated_chain` iterates the construction along a coherent sequence of unitary
square roots.

## Main statements

* `elementary_recursive_step`: controlled action of the recursive toggle sequence.
* `elementary_truncated_chain`: a legal program with at most `(240 * (m + 1) + 20) * k` gates
  and error bounded by `‖seq (j + k) - 1‖`.

## References

* [Barenco et al., 1995, Section 7][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.SqrtApprox
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Boolean sequences agreeing on their first `m` entries have the same prefix conjunction. -/
private theorem truncated_prefix_congr (a b : ℕ → Bool) (m : ℕ)
    (h : ∀ i < m, a i=b i) : noWorkPrefixAnd a m=noWorkPrefixAnd b m := by
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd,List.all_eq_true,List.mem_range]
  constructor <;> intro hs i hi
  · rw [← h i hi]; exact hs i hi
  · rw [h i hi]; exact hs i hi

/-- Combining an `m`-controlled `V` with the specified toggle sequence gives an `(m +
1)`-controlled `V * V` on every target-wire state. -/
theorem elementary_recursive_step (N m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hct : ∀ i < m, c i≠t) (hccl : ∀ i < m, c i≠c m) (hlast : c m≠t)
    (V : Matrix Bool Bool ℂ) (hV : V∈unitaryGroup Bool ℂ)
    (xs : List (ReflectionGate N))
    (hx : ∀ x : Reg N, Run 1 (reflectionCompile xs) (Qatlib.Foundations.PureStateMath.Ket x)=
      Qatlib.Foundations.PureStateMath.Ket (Function.update x (c m) (x (c m) ^^ noWorkPrefixAnd (fun i => x (c i)) m)))
    (G : Matrix (Reg N) (Reg N) ℂ)
    (hG : ∀ x φ, ApplyGate G (multiWireState t x φ)=multiWireState t x
      (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then V else 1) φ)) :
    let p := knownQubitAnglesOfUnitary V
    let F := multiKnownPairSteps (c m) t p ++ xs ++
      multiKnownPairSteps (c m) t (knownQubitAngleAdjoint p) ++ xs
    ∀ x φ, ApplyGate (G*reflectionProgramMatrix F) (multiWireState t x φ)=
      multiWireState t x (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) (m+1) then V*V else 1) φ) := by
  (try dsimp only)
  intro x φ
  let p := knownQubitAnglesOfUnitary V
  have hp : knownQubitUnitary p=V := (knownQubitEuler_explicit_angles_cover_unitaries V hV).1
  have hpadj : knownQubitUnitary (knownQubitAngleAdjoint p)=Vᴴ := by
    rw [knownQubitUnitary_adjoint,hp]
  let a := noWorkPrefixAnd (fun i => x (c i)) m
  let q := Function.update x (c m) (x (c m) ^^ a)
  have hA : noWorkPrefixAnd (fun i => q (c i)) m=a := by
    rw [truncated_prefix_congr _ (fun i => x (c i)) m
      (fun i hi => Function.update_of_ne (hccl i hi) _ _)]
  have hq : q (c m)=(x (c m) ^^ a) := Function.update_self _ _ _
  have hrestore : Function.update q (c m)
      (q (c m) ^^ noWorkPrefixAnd (fun i => q (c i)) m)=x := by
    rw [hA,hq]
    simp [q]
  rw [applyGate_mul,← run_reflectionCompile]
  simp only [reflectionCompile_append,run_append]
  rw [multiKnownPairSteps_action (c m) t hlast p,hp,
    noWork_and_table_wireState c m (c m) t hlast hct xs hx,
    multiKnownPairSteps_action (c m) t hlast (knownQubitAngleAdjoint p),hpadj]
  change ApplyGate G (Run 1 (reflectionCompile xs)
    (multiWireState t q (ApplyGate (if q (c m) then Vᴴ else 1)
      (ApplyGate (if x (c m) then V else 1) φ))))=_
  rw [noWork_and_table_wireState c m (c m) t hlast hct xs hx,hrestore,hG,hq,noWorkPrefixAnd_succ]
  change multiWireState t x (ApplyGate (if a then V else 1)
    (ApplyGate (if x (c m) ^^ a then Vᴴ else 1) (ApplyGate (if x (c m) then V else 1) φ)))=
      multiWireState t x (ApplyGate (if a && x (c m) then V*V else 1) φ)
  cases a <;> cases x (c m) <;> simp [applyGate_one]
  · rw [← applyGate_mul,show Vᴴ*V=1 from hV.1,applyGate_one]
  · rw [← applyGate_mul,show V*Vᴴ=1 from hV.2,applyGate_one]
  · rw [← applyGate_mul]

/-- A coherent unitary square-root chain yields a legal program approximating the `m`-controlled
`seq j`, with at most `(240 * (m + 1) + 20) * k` gates and operator-norm error at most `‖seq
(j + k) - 1‖`. -/
theorem elementary_truncated_chain {N : ℕ} (seq : ℕ → Matrix Bool Bool ℂ)
    (hu : ∀ j, seq j∈unitaryGroup Bool ℂ) (hs : ∀ j,seq (j+1)*seq (j+1)=seq j)
    (m k j : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i≠t) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length≤(240*(m+1)+20)*k ∧
      ∃ G : Matrix (Reg N) (Reg N) ℂ, G∈unitaryGroup (Reg N) ℂ ∧
        ‖reflectionProgramMatrix gs-G‖≤‖seq (j+k)-1‖ ∧
        ∀ x φ, ApplyGate G (multiWireState t x φ)=multiWireState t x
          (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then seq j else 1) φ) := by
  induction k generalizing m j with
  | zero =>
    obtain ⟨es,hes,_hlen,he⟩ := noWork_multi_control_wire_table m c t hc hct (seq j) (hu j)
    let G := reflectionProgramMatrix es
    have hG : G∈unitaryGroup (Reg N) ℂ := reflectionProgramMatrix_unitary es hes
    have hsem : ∀ x φ,ApplyGate G (multiWireState t x φ)=multiWireState t x
        (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then seq j else 1) φ) := by
      intro x φ
      simpa only [run_reflectionCompile] using! he x φ
    refine ⟨[],by simp [reflectionLegal],by simp,G,hG,?_,hsem⟩
    simpa only [reflectionProgramMatrix,Nat.add_zero,norm_sub_rev] using!
      elementary_controlled_distance m c t hct (seq j) G hsem
  | succ k ih =>
    cases m with
    | zero =>
      let gs : List (ReflectionGate N) := [.inl (t,seq j)]
      have hgs : reflectionLegal gs := by
        intro g hg
        obtain rfl := List.mem_singleton.mp hg
        exact hu j
      refine ⟨gs,hgs,by change 1≤260*(k+1); omega,
        reflectionProgramMatrix gs,reflectionProgramMatrix_unitary gs hgs,?_,?_⟩
      · simp only [sub_self,norm_zero]; exact norm_nonneg _
      · intro x φ
        simpa [gs,reflectionProgramMatrix,reflectionGateMatrix,noWorkPrefixAnd] using!
            multiWireState_single t x (seq j) φ
    | succ m =>
      have hcm : Set.InjOn c (Set.Iio m) := by
        intro i hi l hl he
        exact hc (show i∈Set.Iio (m+1) from by change i < m at hi; change i < m+1; omega)
          (show l∈Set.Iio (m+1) from by change l < m at hl; change l < m+1; omega) he
      have hctm : ∀ i < m,c i≠t := fun i hi => hct i (by omega)
      have hccl : ∀ i < m,c i≠c m := by
        intro i hi he
        have h :=
            hc (show i∈Set.Iio (m+1) from by change i < m+1; omega)
            (show m∈Set.Iio (m+1) from by simp) he
        omega
      have hlast : c m≠t := hct m (by omega)
      obtain ⟨xs,hxs,hxlen,hx⟩ := noWork_single_dirty_and_table c t (c m) m hcm hctm hccl hlast.symm
      obtain ⟨rs,hrs,hrlen,G,hG,herr,hr⟩ := ih m (j+1) hcm hctm
      let p := knownQubitAnglesOfUnitary (seq (j+1))
      let vs := multiKnownPairSteps (c m) t p
      let ds := multiKnownPairSteps (c m) t (knownQubitAngleAdjoint p)
      let F := vs++xs++ds++xs
      have hF : reflectionLegal F := by
        simp only [F,reflectionLegal_append]
        exact ⟨⟨⟨multiKnownPairSteps_legal _ _ hlast p,hxs⟩,
          multiKnownPairSteps_legal _ _ hlast (knownQubitAngleAdjoint p)⟩,hxs⟩
      have hFlen : F.length≤240*(m+1)+20 := by
        have hv : vs.length=6 := rfl
        have hd : ds.length=6 := rfl
        simp only [F,List.length_append,hv,hd]
        omega
      let A := G*reflectionProgramMatrix F
      refine ⟨F++rs,by rw [reflectionLegal_append]; exact ⟨hF,hrs⟩,?_,A,
        (unitaryGroup (Reg N) ℂ).mul_mem hG (reflectionProgramMatrix_unitary F hF),?_,?_⟩
      · simp only [List.length_append]
        nlinarith
      · have hid : reflectionProgramMatrix (F++rs)-A=
            (reflectionProgramMatrix rs-G)*reflectionProgramMatrix F := by
          rw [reflectionProgramMatrix_append]
          exact (Matrix.sub_mul _ _ _).symm
        rw [hid]
        calc
          _ ≤ ‖reflectionProgramMatrix rs-G‖*‖reflectionProgramMatrix F‖ := Matrix.l2_opNorm_mul _ _
          _ ≤ ‖reflectionProgramMatrix rs-G‖*1 := mul_le_mul_of_nonneg_left
            (l2_norm_unitary_le_one (reflectionProgramMatrix_unitary F hF)) (norm_nonneg _)
          _ ≤ ‖seq (j+(k+1))-1‖ := by simpa only [mul_one,show j+(k+1)=(j+1)+k by omega] using! herr
      · intro x φ
        have he :=
            elementary_recursive_step N m c t hctm hccl hlast (seq (j+1)) (hu (j+1)) xs hx G hr x φ
        simpa only [hs j] using! he
end Qatlib.Concepts.CircuitImpl.SqrtApprox

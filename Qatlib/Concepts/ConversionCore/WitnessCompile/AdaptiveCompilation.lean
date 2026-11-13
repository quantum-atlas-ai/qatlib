/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.StateConversion
import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan

/-!
# Resource bounds for adaptive compilation

Adaptive source computations can be purified and compiled into source words while retaining
their branch records in an enlarged workspace. `sourceAdaptive_resource_compilation` bounds
oracle calls and known gates and gives an exact simulation of the recorded output;
`sourceAdaptive_resource_mixed_compilation` extends this identity to arbitrary input matrices.

The module compares coherent and noncoherent adaptive costs with word query costs within a
factor of two, in the state conversion setting of [LeeEtAl2011]. The retained-record example
distinguishes a successful branch record from a fixed zero record.

## Main statements

* `sourceAdaptive_resource_compilation`: exact simulation with explicit resource bounds.
* `sourceAdaptive_normalized_complexity_comparison`: comparison of adaptive and word costs.
* `sourceAdaptive_resource_mixed_compilation`: simulation for arbitrary input matrices.

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QueryComplexity.StateConversion
open scoped BigOperators Classical Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
set_option maxHeartbeats 300000 in
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
noncomputable section
/-- The adaptive computation obtained by reading a source word as a sequence of unary nodes. -/
def sourceWordAdaptive {S : Type} : SourceWord S → SourceAdaptive S
  | [] => .finish
  | .inl U :: C => .known U (sourceWordAdaptive C)
  | .inr adj :: C => .query adj (sourceWordAdaptive C)
end
noncomputable section

/-- Embedding a source word as an adaptive computation preserves its oracle-call count. -/
theorem sourceWordAdaptive_calls {S : Type} (C : SourceWord S) :
    sourceAdaptiveCalls (sourceWordAdaptive C) = sourceWordCalls C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp [sourceWordAdaptive, sourceAdaptiveCalls, sourceWordCalls,
      ih, sourceWordCalls] at *
    omega
end
noncomputable section

/-- The adaptive embedding of a legal source word is legal. -/
theorem sourceWordAdaptive_legal {S : Type} [Fintype S] [DecidableEq S]
    (C : SourceWord S) (hC : sourceWordLegal C) :
    sourceAdaptiveLegal (sourceWordAdaptive C) := by
  induction C with
  | nil => trivial
  | cons s C ih =>
    have ht : sourceWordLegal C := fun t ht => hC t (List.mem_cons_of_mem s ht)
    cases s with
    | inl U => exact ⟨hC (.inl U) (List.mem_cons_self), ih ht⟩
    | inr adj => exact ih ht
end
noncomputable section

/-- The adaptive embedding of a source word has the singleton branch list containing the word
output. -/
theorem sourceWordAdaptive_branches {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C : SourceWord S) (ψ : QState S) :
    sourceAdaptiveBranches O (sourceWordAdaptive C) ψ = [sourceWordMatrix O C *ᵥ ψ] := by
  induction C generalizing ψ with
  | nil => simp [sourceWordAdaptive, sourceAdaptiveBranches, sourceWordMatrix]
  | cons s C ih =>
    cases s <;> simp [sourceWordAdaptive, sourceAdaptiveBranches, ih, sourceWordMatrix,
      Matrix.mulVec_mulVec]
end
noncomputable section

/-- The tree frame maps a zero-record clean state to the corresponding clean state in the larger
workspace. -/
theorem sourceTreeFrame_clean {H : Type} [Fintype H] [DecidableEq H]
    (n q r L R : ℕ) (hr : 0 < r) (hL : 0 < L) (hR : 0 < R)
    (_hsize : L*r ≤ R) (tag : Bool) (ψ : QState H) :
    sourceTreeFrame n q r L R *ᵥ
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hL⟩ : Fin L)) (sourceClean n q r hr tag ψ) =
        sourceClean n q R hR tag ψ := by
  ext p
  rcases p with ⟨⟨a,b⟩,⟨⟨t,h⟩,k⟩⟩
  simp only [sourceTreeFrame, sourceClean, TensorState, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  simp only [Prod.mk.injEq, ite_and, mul_ite, ite_mul, zero_mul, mul_zero,
    one_mul]
  have hz (i : Fin L) : i.val = 0 ↔ i = ⟨0,hL⟩ := by simp [Fin.ext_iff]
  simp only [Fin.ext_iff, Fin.val_zero]
  simp
  simp only [hz, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp_all
end
noncomputable section

/-- The tree frame preserves inner products when the larger workspace can encode all record and
workspace pairs. -/
theorem sourceTreeFrame_inner {H : Type} [Fintype H] [DecidableEq H]
    (n q r L R : ℕ) (hsize : L*r ≤ R)
    (ψ φ : QState (Fin L × SourceSpace n q H r)) :
    Qatlib.Foundations.PureStateMath.Inner (sourceTreeFrame n q r L R *ᵥ ψ) (sourceTreeFrame n q r L R *ᵥ φ) =
      Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner,Matrix.star_mulVec,← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,sourceTreeFrame_isometry n q r L R hsize,Matrix.one_mulVec]
end
noncomputable section

/-- Coherent adaptive success means that every recorded output has real overlap at least `sqrt
(1-ε)` with the zero-record clean target. -/
def sourceAdaptiveCoherentSuccess {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (ε : ℝ) (T : SourceAdaptive (SourceSpace n q H r)) : Prop :=
  ∀ x, (Qatlib.Foundations.PureStateMath.Inner (sourceAdaptivePure (sourceAlphabetOracle input x) T
    (sourceClean n q r hr false (ρ x)))
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin (max 1 (sourceAdaptiveLeaves T))))
      (sourceClean n q r hr true (σ x)))).re ≥ Real.sqrt (1-ε)
end
noncomputable section

/-- A legal adaptive computation satisfying coherent success gives a coherent word query cost at
most twice its adaptive call count. -/
theorem sourceAdaptiveCoherentQ_le_twice_calls {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (T : SourceAdaptive (SourceSpace n q H r)) (hT : sourceAdaptiveLegal T)
    (hSuccess : sourceAdaptiveCoherentSuccess hr input ρ σ ε T) :
    sourceCoherentQ input ρ σ ε ≤ (2*sourceAdaptiveCalls T : ℕ) := by
  obtain ⟨R,hR,C,hsize,hC,hcalls,hIso,hSim⟩ :=
    adaptiveInstrumentPurification X H n q r hr input T hT
  apply le_trans (sourceCoherentQ_le_calls hR input ρ σ ε C hC ?_)
  · exact_mod_cast hcalls
  intro x
  have hL : 0 < max 1 (sourceAdaptiveLeaves T) := by omega
  have hin := sourceTreeFrame_clean n q r _ R hr hL hR hsize false (ρ x)
  have hout := sourceTreeFrame_clean n q r _ R hr hL hR hsize true (σ x)
  have hs := (hSim x (sourceClean n q r hr false (ρ x))).1
  rw [hin] at hs
  change (Qatlib.Foundations.PureStateMath.Inner _ _).re ≥ _
  rw [hs,← hout,sourceTreeFrame_inner n q r _ R hsize]
  exact hSuccess x
end
noncomputable section
/-- The address, value, tag, and workspace indices remaining after the payload is factored out
of a source space. -/
abbrev SourceGarbage (n q r : ℕ) := (Fin (n+1) × Fin (q+1)) × (Bool × Fin r)
end
noncomputable section
/-- The encoding of a branch record and garbage index into a larger garbage space by packing the
record into the workspace coordinate. -/
def sourceRecordGarbageCode (n q r L R : ℕ) (hsize : L*r ≤ R) :
    Fin L × SourceGarbage n q r → SourceGarbage n q R :=
  fun p => (p.2.1,(p.2.2.1,⟨p.1.val*r+p.2.2.2.val,by
    have hp : (p.1.val+1)*r ≤ L*r := Nat.mul_le_mul_right r p.1.isLt
    simp only [Nat.add_mul,Nat.one_mul] at hp
    omega⟩))
end
noncomputable section

/-- The record-and-garbage encoding is injective when `L*r ≤ R`. -/
theorem sourceRecordGarbageCode_injective (n q r L R : ℕ) (hsize : L*r ≤ R) :
    Function.Injective (sourceRecordGarbageCode n q r L R hsize) := by
  intro a b he
  let fa : Fin L × SourceSpace n q Unit r := (a.1,(a.2.1,((a.2.2.1,()),a.2.2.2)))
  let fb : Fin L × SourceSpace n q Unit r := (b.1,(b.2.1,((b.2.2.1,()),b.2.2.2)))
  have hab : sourceTreeCode n q r L R hsize fa = sourceTreeCode n q r L R hsize fb := by
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun p => p.2.1) he
    have h3 := congrArg (fun p => p.2.2) he
    exact Prod.ext h1 (Prod.ext (Prod.ext h2 rfl) h3)
  have hf := sourceTreeCode_injective n q r L R hsize hab
  simpa only [fa,fb,Prod.ext_iff,and_true] using! hf
end
noncomputable section
/-- The basis frame associated with `sourceRecordGarbageCode`. -/
def sourceRecordGarbageFrame (n q r L R : ℕ) (hsize : L*r ≤ R) :=
  sourceBasisFrame (sourceRecordGarbageCode n q r L R hsize)
end
noncomputable section

/-- The record-and-garbage frame preserves normalization. -/
theorem sourceRecordGarbageFrame_normalized (n q r L R : ℕ) (hsize : L*r ≤ R)
    (ξ : QState (Fin L × SourceGarbage n q r)) (hξ : Normalized ξ) :
    Normalized (sourceRecordGarbageFrame n q r L R hsize *ᵥ ξ) := by
  apply (normalized_iff_inner_self _).mpr
  have hIso := sourceBasisFrame_isometry _ (sourceRecordGarbageCode_injective n q r L R hsize)
  simp only [sourceRecordGarbageFrame, Qatlib.Foundations.PureStateMath.Inner,Matrix.star_mulVec,← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,hIso,Matrix.one_mulVec]
  exact (normalized_iff_inner_self _).mp hξ
end
noncomputable section

/-- The target state formed from payload `σ` and garbage `ξ`, with the branch record retained. -/
def sourceAdaptiveGarbageTarget {H : Type} (n q r L : ℕ) (σ : QState H)
    (ξ : QState (Fin L × SourceGarbage n q r)) : QState (Fin L × SourceSpace n q H r) :=
  fun p => σ p.2.2.1.2 * ξ (p.1,(p.2.1,(p.2.2.1.1,p.2.2.2)))
end
noncomputable section

/-- The tree frame maps an adaptive garbage target to the ordinary garbage target using the
encoded record-and-garbage state. -/
theorem sourceTreeFrame_garbage {H : Type} [Fintype H] [DecidableEq H]
    (n q r L R : ℕ) (hsize : L*r ≤ R) (σ : QState H)
    (ξ : QState (Fin L × SourceGarbage n q r)) :
    sourceTreeFrame n q r L R *ᵥ sourceAdaptiveGarbageTarget n q r L σ ξ =
      sourceGarbageTarget n q R σ (sourceRecordGarbageFrame n q r L R hsize *ᵥ ξ) := by
  ext p
  rcases p with ⟨a,⟨⟨t,h⟩,k⟩⟩
  simp only [sourceTreeFrame,sourceAdaptiveGarbageTarget,sourceGarbageTarget,
    sourceRecordGarbageFrame,sourceBasisFrame,sourceRecordGarbageCode,
    Matrix.mulVec,dotProduct,Matrix.of_apply,Fintype.sum_prod_type,Prod.mk.injEq]
  simp only [Fin.ext_iff,ite_and,ite_mul,zero_mul,one_mul]
  simp
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with ha
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k' _
    split_ifs <;> simp
  · simp
end
noncomputable section

/-- Noncoherent adaptive success means that every input possesses a normalized
record-and-garbage state giving target overlap norm at least `sqrt (1-ε)`. -/
def sourceAdaptiveNoncoherentSuccess {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (ε : ℝ) (T : SourceAdaptive (SourceSpace n q H r)) : Prop :=
  ∀ x, ∃ ξ : QState (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceGarbage n q r),
    Normalized ξ ∧ Real.sqrt (1-ε) ≤ ‖Qatlib.Foundations.PureStateMath.Inner
      (sourceAdaptivePure (sourceAlphabetOracle input x) T
        (sourceClean n q r hr false (ρ x)))
      (sourceAdaptiveGarbageTarget n q r _ (σ x) ξ)‖
end
noncomputable section

/-- A legal adaptive computation satisfying noncoherent success gives a noncoherent word query
cost at most twice its adaptive call count. -/
theorem sourceAdaptiveNoncoherentQ_le_twice_calls {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (T : SourceAdaptive (SourceSpace n q H r)) (hT : sourceAdaptiveLegal T)
    (hSuccess : sourceAdaptiveNoncoherentSuccess hr input ρ σ ε T) :
    sourceNoncoherentQ input ρ σ ε ≤ (2*sourceAdaptiveCalls T : ℕ) := by
  obtain ⟨R,hR,C,hsize,hC,hcalls,hIso,hSim⟩ :=
    adaptiveInstrumentPurification X H n q r hr input T hT
  apply le_trans (sourceNoncoherentQ_le_calls hR input ρ σ ε C hC ?_)
  · exact_mod_cast hcalls
  intro x
  obtain ⟨ξ,hξ,hsuccess⟩ := hSuccess x
  refine ⟨sourceRecordGarbageFrame n q r _ R hsize *ᵥ ξ,
    sourceRecordGarbageFrame_normalized n q r _ R hsize ξ hξ,?_⟩
  have hL : 0 < max 1 (sourceAdaptiveLeaves T) := by omega
  have hin := sourceTreeFrame_clean n q r _ R hr hL hR hsize false (ρ x)
  have hs := (hSim x (sourceClean n q r hr false (ρ x))).1
  rw [hin] at hs
  change Real.sqrt (1-ε) ≤ ‖Qatlib.Foundations.PureStateMath.Inner _ _‖
  rw [hs,← sourceTreeFrame_garbage n q r _ R hsize,
    sourceTreeFrame_inner n q r _ R hsize]
  exact hsuccess
end
noncomputable section

/-- The adaptive embedding of a source word has exactly one leaf. -/
theorem sourceWordAdaptive_leaves {S : Type} (C : SourceWord S) :
    sourceAdaptiveLeaves (sourceWordAdaptive C) = 1 := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> exact ih
end
noncomputable section

/-- The recorded pure output of an embedded source word equals its word output at the system
coordinate. -/
theorem sourceWordAdaptive_pure {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (C : SourceWord S) (ψ : QState S)
    (p : Fin (max 1 (sourceAdaptiveLeaves (sourceWordAdaptive C))) × S) :
    sourceAdaptivePure O (sourceWordAdaptive C) ψ p = (sourceWordMatrix O C *ᵥ ψ) p.2 := by
  have hp : p.1.val = 0 := by
    have h : p.1.val < 1 := by simpa only [sourceWordAdaptive_leaves,max_self] using! p.1.isLt
    omega
  simp [sourceAdaptivePure,sourceWordAdaptive_branches,hp]
end
noncomputable section

/-- A word satisfying the clean-target real-overlap bound satisfies coherent adaptive success
after embedding. -/
theorem sourceWordAdaptive_coherent_success {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (ε : ℝ) (C : SourceWord (SourceSpace n q H r))
    (hSuccess : ∀ x, (Qatlib.Foundations.PureStateMath.Inner (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)) (sourceClean n q r hr true (σ x))).re ≥ Real.sqrt (1-ε)) :
    sourceAdaptiveCoherentSuccess hr input ρ σ ε (sourceWordAdaptive C) := by
  intro x
  simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply]
  rw [Fintype.sum_prod_type]
  simp only [sourceWordAdaptive_pure,TensorState,Qatlib.Foundations.PureStateMath.Ket]
  simp only [mul_ite,ite_mul,zero_mul,one_mul,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact hSuccess x
end
noncomputable section

/-- A word satisfying the normalized garbage-target overlap bound satisfies noncoherent adaptive
success after embedding. -/
theorem sourceWordAdaptive_noncoherent_success {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (ε : ℝ) (C : SourceWord (SourceSpace n q H r))
    (hSuccess : ∀ x, ∃ ξ : QState (SourceGarbage n q r), Normalized ξ ∧
      Real.sqrt (1-ε) ≤ ‖Qatlib.Foundations.PureStateMath.Inner (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) (sourceGarbageTarget n q r (σ x) ξ)‖) :
    sourceAdaptiveNoncoherentSuccess hr input ρ σ ε (sourceWordAdaptive C) := by
  intro x
  obtain ⟨ξ,hξ,hs⟩ := hSuccess x
  refine ⟨TensorState (Qatlib.Foundations.PureStateMath.Ket ⟨0,by omega⟩) ξ,
    normalized_tensorState (normalized_ket _) hξ,?_⟩
  have he : Qatlib.Foundations.PureStateMath.Inner (sourceAdaptivePure (sourceAlphabetOracle input x) (sourceWordAdaptive C)
        (sourceClean n q r hr false (ρ x)))
      (sourceAdaptiveGarbageTarget n q r _ (σ x) (TensorState (Qatlib.Foundations.PureStateMath.Ket ⟨0,by omega⟩) ξ)) =
      Qatlib.Foundations.PureStateMath.Inner (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) (sourceGarbageTarget n q r (σ x) ξ) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply]
    rw [Fintype.sum_prod_type]
    simp only [sourceWordAdaptive_pure,sourceAdaptiveGarbageTarget,TensorState,Qatlib.Foundations.PureStateMath.Ket,
      mul_ite,ite_mul,zero_mul,one_mul,mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl
  rw [he]
  exact hs
end
noncomputable section
/-- The number of known-matrix instructions in a source word. -/
def sourceWordKnown {S : Type} (C : SourceWord S) : ℕ :=
  C.countP (fun s => match s with | .inl _ => true | .inr _ => false)
end
noncomputable section

/-- Relabeling a source word preserves its number of known-matrix instructions. -/
theorem sourceRelabelWord_known {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (C : SourceWord I) :
    sourceWordKnown (sourceRelabelWord e C) = sourceWordKnown C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [sourceWordKnown,sourceRelabelWord] at ih ⊢ <;> omega
end
noncomputable section

/-- The source word of a purification program has `1+2*P.layers.length` known-matrix
instructions. -/
theorem sourcePurificationProgramWord_known {S : Type} (P : SourcePurificationProgram S) :
    sourceWordKnown (sourcePurificationProgramWord P) = 1+2*P.layers.length := by
  rcases P with ⟨start,layers⟩
  induction layers with
  | nil => simp [sourcePurificationProgramWord,sourceWordKnown]
  | cons layer layers ih =>
    simp [sourcePurificationProgramWord,sourcePurificationLayerWord,sourceWordKnown] at ih ⊢
    omega
end
noncomputable section

/-- Every legal adaptive computation compiles exactly into a legal word with at most twice as
many oracle calls and at most one plus twice as many known gates. The enlarged workspace
also supports an isometric record embedding and preserves branch probabilities and the
output density. -/
theorem sourceAdaptive_resource_compilation :
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    let leaves := max 1 (sourceAdaptiveLeaves T)
    ∃ (R : ℕ) (hR : 0<R) (C : SourceWord (SourceSpace n q H R)),
      R = leaves*r*(n+1) ∧ leaves*r ≤ R ∧ sourceWordLegal C ∧
      sourceWordCalls C ≤ 2*sourceAdaptiveCalls T ∧
      sourceWordKnown C ≤ 1+2*sourceAdaptiveCalls T ∧
      let F := sourceTreeFrame (H := H) n q r leaves R
      Fᴴ * F=1 ∧ ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
      sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        (F *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by dsimp [leaves]; omega⟩ : Fin leaves)) ψ)=
      F *ᵥ sourceAdaptivePure (sourceAlphabetOracle input x) T ψ ∧
      (Normalized ψ →
        ((sourceAdaptiveBranches (sourceAlphabetOracle input x) T ψ).map
          (fun φ => ‖toEuclidean_fromVec φ‖^2)).sum=1) ∧
      (∀ p t, sourceAdaptiveDensity (sourceAlphabetOracle input x) T ψ p t=
        ∑ i : Fin leaves, sourceAdaptivePure (sourceAlphabetOracle input x) T ψ (i,p)*
          star (sourceAdaptivePure (sourceAlphabetOracle input x) T ψ (i,t))) := by
  intro X H _ _ _ _ _ n q r hr input T hT
  have hL : 0 < max 1 (sourceAdaptiveLeaves T) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  obtain ⟨P,hPleg,hPcalls,hPtrans⟩ :=
    sourceAdaptive_purify_program (X := X) (H := H) hr input T hT hL
  let e := sourcePurifySpaceEquiv (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) hr hL
  let R := (max 1 (sourceAdaptiveLeaves T))*r*(n+1)
  have hRpos : 0<R := Nat.mul_pos (Nat.mul_pos hL hr) (Nat.succ_pos n)
  have hRle : (max 1 (sourceAdaptiveLeaves T))*r≤R :=
    Nat.le_mul_of_pos_right (max 1 (sourceAdaptiveLeaves T)*r) (Nat.succ_pos n)
  have hIso : (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R)ᴴ*
      sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R=1 :=
    sourceTreeFrame_isometry (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R hRle
  have hcode : ∀ (l : Fin (max 1 (sourceAdaptiveLeaves T))) (s : SourceSpace n q H r),
      e (l,s,⟨n,Nat.lt_succ_self n⟩)=
        sourceTreeCode n q r (max 1 (sourceAdaptiveLeaves T)) R hRle (l,s) := by
    intro l s
    exact sourcePurifySpaceEquiv_code (H := H) (n := n) (q := q) (r := r)
      (L := max 1 (sourceAdaptiveLeaves T)) hr hL hRle l s
  refine ⟨R,hRpos,sourceRelabelWord e (sourcePurificationProgramWord P),rfl,hRle,
    sourceRelabelWord_legal e _ (sourcePurificationProgramWord_legal P hPleg),?_,?_,?_⟩
  · show sourceWordCalls (sourceRelabelWord e (sourcePurificationProgramWord P))≤_
    rw [sourceRelabelWord_calls]
    exact hPcalls
  · rw [sourceRelabelWord_known,sourcePurificationProgramWord_known]
    rw [sourcePurificationProgramWord_calls] at hPcalls
    omega
  · refine ⟨hIso,?_⟩
    intro x ψ
    have hOu : sourceAlphabetOracle (W := (Bool × H) × Fin r) input x ∈
        Matrix.unitaryGroup _ ℂ := by
      rw [sourceAlphabetOracle_eq_permMatrix]
      exact permMatrix_unitary_of_injective (Equiv.injective _)
    have hOconj : relabelGate e
        (sourcePurifyOracle (n := n) (q := q) input x (r := r)
          (L := max 1 (sourceAdaptiveLeaves T))) =
        sourceAlphabetOracle (W := (Bool × H) × Fin R) input x :=
      sourcePurifyRelabel_oracle (H := H) (n := n) (q := q) (r := r)
        (L := max 1 (sourceAdaptiveLeaves T)) hr hL input x
    have hM : sourceWordMatrix (sourceAlphabetOracle (W := (Bool × H) × Fin R) input x)
        (sourceRelabelWord e (sourcePurificationProgramWord P))=
        relabelGate e (sourceWordMatrix
          (sourcePurifyOracle (n := n) (q := q) input x (r := r)
            (L := max 1 (sourceAdaptiveLeaves T))) (sourcePurificationProgramWord P)) := by
      rw [← hOconj]
      exact sourceRelabelWord_matrix e _ _
    have hts : TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T)))) ψ=
        (sourceBasisFrame (fun s : SourceSpace n q H r =>
          ((⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T))),s)))*ᵥ ψ := by
      funext p
      rcases p with ⟨l,s⟩
      simp only [TensorState,Qatlib.Foundations.PureStateMath.Ket,sourceBasisFrame,Matrix.mulVec,dotProduct]
      rw [Finset.sum_eq_single s]
      · by_cases hl : l=(⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T)))
        · subst hl; simp
        · rw [if_neg hl,if_neg (fun h => hl (Prod.ext_iff.mp h).1)]
      · intro t _ ht
        rw [if_neg (fun h => ht (Prod.ext_iff.mp h).2.symm),zero_mul]
      · intro hs; exact absurd (Finset.mem_univ s) hs
    have hin : (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R)*ᵥ
        TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T)))) ψ=
        sourceBasisFrame (⇑e)*ᵥ
          (sourcePurifyIn (n := n) (q := q) (r := r)
            (L := max 1 (sourceAdaptiveLeaves T)) hL*ᵥ ψ) := by
      rw [sourceTreeFrame_eq_basis (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R hRle, hts]
      unfold sourcePurifyIn
      rw [Matrix.mulVec_mulVec,sourceBasisFrame_mul]
      have hfun : (sourceTreeCode n q r (max 1 (sourceAdaptiveLeaves T)) R hRle)∘
          (fun s : SourceSpace n q H r =>
            ((⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T))),s))=
          (⇑e)∘(fun s : SourceSpace n q H r =>
            ((⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T))),s,⟨n,Nat.lt_succ_self n⟩)) := by
        funext s
        exact (hcode ⟨0,hL⟩ s).symm
      rw [hfun]
      rw [Matrix.mulVec_mulVec,sourceBasisFrame_mul]
    have hout : sourceBasisFrame (⇑e)*ᵥ
        ((sourcePurifyOut (n := n) (q := q) (r := r)
          (L := max 1 (sourceAdaptiveLeaves T)))*ᵥ
        sourceAdaptivePure (sourceAlphabetOracle input x) T ψ)=
        (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R)*ᵥ
        sourceAdaptivePure (sourceAlphabetOracle input x) T ψ := by
      rw [sourceTreeFrame_eq_basis (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R hRle]
      unfold sourcePurifyOut
      rw [Matrix.mulVec_mulVec,sourceBasisFrame_mul]
      have hfun : (⇑e)∘(fun p : Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r =>
          (p.1,p.2,⟨n,Nat.lt_succ_self n⟩))=
        sourceTreeCode n q r (max 1 (sourceAdaptiveLeaves T)) R hRle := by
        funext p
        exact hcode p.1 p.2
      rw [hfun]
    refine ⟨?_,?_,?_⟩
    · rw [hM,hin]
      rw [Matrix.mulVec_mulVec,sourceRelabelGate_mul_basisFrame e _,← Matrix.mulVec_mulVec]
      rw [hPtrans x ψ]
      exact hout
    · intro hnorm
      rw [sourceAdaptive_branches_mass _ hOu T hT ψ,norm_toEuclidean_fromVec_sq]
      exact hnorm
    · exact fun p t => sourceAdaptive_density_pure _ T ψ p t
end
noncomputable section

/-- Tracing out the record of the adaptive pure output gives the adaptive output density matrix. -/
theorem source_adaptive_record_marginal {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (T : SourceAdaptive S) (ψ : QState S) :
    conversionRecordMarginal (sourceAdaptivePure O T ψ) = sourceAdaptiveDensity O T ψ := by
  ext h k
  exact (sourceAdaptive_density_pure O T ψ h k).symm
end
noncomputable section

/-- The target expectation of the adaptive output density equals the sum of squared norms of the
target projections of its recorded pure output. -/
theorem source_adaptive_record_fidelity {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (T : SourceAdaptive S) (ψ σ : QState S) :
    Qatlib.Foundations.PureStateMath.Inner σ (sourceAdaptiveDensity O T ψ *ᵥ σ) =
      ((∑ r, Complex.normSq (conversionRecordProjection (sourceAdaptivePure O T ψ) σ r) : ℝ) : ℂ) := by
  rw [← source_adaptive_record_marginal, conversionRecordMarginal_fidelity]
end
noncomputable section
/-- The infimum of oracle-call counts over legal adaptive computations satisfying coherent
success, allowing arbitrary positive workspace size. -/
def sourceAdaptiveCoherentCost {X H : Type} [Fintype H] [DecidableEq H]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (r : ℕ) (hr : 0<r) (T : SourceAdaptive (SourceSpace n q H r))
    (_ : sourceAdaptiveLegal T) (_ : sourceAdaptiveCoherentSuccess hr input ρ σ ε T),
    (sourceAdaptiveCalls T : ℝ≥0∞)
end
noncomputable section
/-- The infimum of oracle-call counts over legal adaptive computations satisfying noncoherent
success, allowing arbitrary positive workspace size. -/
def sourceAdaptiveNoncoherentCost {X H : Type} [Fintype H] [DecidableEq H]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (r : ℕ) (hr : 0<r) (T : SourceAdaptive (SourceSpace n q H r))
    (_ : sourceAdaptiveLegal T) (_ : sourceAdaptiveNoncoherentSuccess hr input ρ σ ε T),
    (sourceAdaptiveCalls T : ℝ≥0∞)
end
noncomputable section

/-- The coherent adaptive cost is at most the coherent source-word query cost. -/
theorem sourceAdaptiveCoherentCost_le_sourceCoherentQ {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceAdaptiveCoherentCost input ρ σ ε ≤ sourceCoherentQ input ρ σ ε := by
  apply le_sInf
  rintro b ⟨r,hr,C,hb,hC,hs⟩
  rw [hb]
  unfold sourceAdaptiveCoherentCost
  apply iInf_le_of_le r
  apply iInf_le_of_le hr
  apply iInf_le_of_le (sourceWordAdaptive C)
  apply iInf_le_of_le (sourceWordAdaptive_legal C hC)
  apply iInf_le_of_le (sourceWordAdaptive_coherent_success hr input ρ σ ε C hs)
  rw [sourceWordAdaptive_calls]
end
noncomputable section

/-- The noncoherent adaptive cost is at most the noncoherent source-word query cost. -/
theorem sourceAdaptiveNoncoherentCost_le_sourceNoncoherentQ {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceAdaptiveNoncoherentCost input ρ σ ε ≤ sourceNoncoherentQ input ρ σ ε := by
  apply le_sInf
  rintro b ⟨r,hr,C,hb,hC,hs⟩
  rw [hb]
  unfold sourceAdaptiveNoncoherentCost
  apply iInf_le_of_le r
  apply iInf_le_of_le hr
  apply iInf_le_of_le (sourceWordAdaptive C)
  apply iInf_le_of_le (sourceWordAdaptive_legal C hC)
  apply iInf_le_of_le (sourceWordAdaptive_noncoherent_success hr input ρ σ ε C hs)
  rw [sourceWordAdaptive_calls]
end
noncomputable section

/-- For nonempty payload space, the coherent word query cost is at most twice the coherent
adaptive cost. -/
theorem sourceCoherentQ_le_twice_adaptiveCost {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceCoherentQ input ρ σ ε ≤ 2*sourceAdaptiveCoherentCost input ρ σ ε := by
  unfold sourceAdaptiveCoherentCost
  simp_rw [ENNReal.mul_iInf_of_ne (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp)]
  refine le_iInf fun r => le_iInf fun hr => le_iInf fun T => le_iInf fun hT => le_iInf fun hs => ?_
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using!
    sourceAdaptiveCoherentQ_le_twice_calls hr input ρ σ ε T hT hs
end
noncomputable section

/-- For nonempty payload space, the noncoherent word query cost is at most twice the noncoherent
adaptive cost. -/
theorem sourceNoncoherentQ_le_twice_adaptiveCost {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceNoncoherentQ input ρ σ ε ≤ 2*sourceAdaptiveNoncoherentCost input ρ σ ε := by
  unfold sourceAdaptiveNoncoherentCost
  simp_rw [ENNReal.mul_iInf_of_ne (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp)]
  refine le_iInf fun r => le_iInf fun hr => le_iInf fun T => le_iInf fun hT => le_iInf fun hs => ?_
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using!
    sourceAdaptiveNoncoherentQ_le_twice_calls hr input ρ σ ε T hT hs
end
noncomputable section
/-- The two-outcome adaptive computation with Kraus matrices zero and identity, retaining the
outcome record. -/
def sourceRetainedRecordTree (S : Type) [Fintype S] [DecidableEq S] : SourceAdaptive S :=
  .instrument 2 (fun i => if i = (1 : Fin 2) then 1 else 0) (fun _ => .finish)
end
noncomputable section

/-- The retained-record computation is legal. -/
theorem sourceRetainedRecordTree_legal (S : Type) [Fintype S] [DecidableEq S] :
    sourceAdaptiveLegal (sourceRetainedRecordTree S) := by
  constructor
  · simp
  · intro i; trivial
end
noncomputable section

/-- The retained-record computation uses no oracle calls. -/
theorem sourceRetainedRecordTree_calls (S : Type) [Fintype S] [DecidableEq S] :
    sourceAdaptiveCalls (sourceRetainedRecordTree S) = 0 := by
  simp [sourceRetainedRecordTree,sourceAdaptiveCalls,List.ofFn_succ]
end
noncomputable section

/-- The retained-record computation has branch states zero and the original input state. -/
theorem sourceRetainedRecordTree_branches (S : Type) [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (ψ : QState S) :
    sourceAdaptiveBranches O (sourceRetainedRecordTree S) ψ = [0,ψ] := by
  simp [sourceRetainedRecordTree,sourceAdaptiveBranches,List.ofFn_succ]
end
noncomputable section

/-- The retained-record computation has two leaves. -/
theorem sourceRetainedRecordTree_leaves (S : Type) [Fintype S] [DecidableEq S] :
    sourceAdaptiveLeaves (sourceRetainedRecordTree S) = 2 := by
  simp [sourceRetainedRecordTree,sourceAdaptiveLeaves,List.ofFn_succ]
end
noncomputable section

/-- The retained-record pure output equals the input on record one and vanishes on every other
record. -/
theorem sourceRetainedRecordTree_pure (S : Type) [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (ψ : QState S)
    (p : Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))) × S) :
    sourceAdaptivePure O (sourceRetainedRecordTree S) ψ p =
      (if p.1.val = 1 then ψ p.2 else 0) := by
  have hp : p.1.val < 2 := by
    simpa only [sourceRetainedRecordTree_leaves,Nat.max_eq_right (by decide : 1 ≤ 2)] using!
      p.1.isLt
  unfold sourceAdaptivePure
  rw [sourceRetainedRecordTree_branches]
  interval_cases hval : p.1.val <;> simp
end
noncomputable section

/-- Inner product with a basis record tensored with `ψ` equals the inner product of the
corresponding record slice with `ψ`. -/
theorem sourceInner_record_ket {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    (v : QState (R × S)) (r : R) (ψ : QState S) :
    Qatlib.Foundations.PureStateMath.Inner v (TensorState (Qatlib.Foundations.PureStateMath.Ket r) ψ) = Qatlib.Foundations.PureStateMath.Inner (fun s => v (r,s)) ψ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp [TensorState,Qatlib.Foundations.PureStateMath.Ket,mul_ite,ite_mul]
end
noncomputable section

/-- For normalized input, the retained-record output has overlap zero with record zero and
overlap one with record one. -/
theorem sourceRetainedRecordTree_overlap (S : Type) [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (ψ : QState S) (hψ : Normalized ψ) :
    Qatlib.Foundations.PureStateMath.Inner (sourceAdaptivePure O (sourceRetainedRecordTree S) ψ)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by simp [sourceRetainedRecordTree_leaves]⟩ :
        Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))))) ψ) = 0 ∧
    Qatlib.Foundations.PureStateMath.Inner (sourceAdaptivePure O (sourceRetainedRecordTree S) ψ)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨1,by simp [sourceRetainedRecordTree_leaves]⟩ :
        Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))))) ψ) = 1 := by
  simp only [sourceInner_record_ket]
  constructor
  · simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct,sourceRetainedRecordTree_pure]
  · simpa only [sourceRetainedRecordTree_pure,ite_true] using! (normalized_iff_inner_self ψ).mp hψ
end
noncomputable section

/-- Coherent and noncoherent source-word query costs vanish when the input index type is empty. -/
theorem sourceWordCosts_empty_input {X H : Type} [Fintype X] [DecidableEq X]
    [IsEmpty X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceCoherentQ input ρ σ ε = 0 ∧ sourceNoncoherentQ input ρ σ ε = 0 := by
  constructor
  · apply le_antisymm ?_ bot_le
    apply le_trans (sourceCoherentQ_le_calls (r := 1) (by decide) input ρ σ ε []
      (by intro s hs; simp at hs) (fun x => isEmptyElim x))
    simp [sourceWordCalls]
  · apply le_antisymm ?_ bot_le
    apply le_trans (sourceNoncoherentQ_le_calls (r := 1) (by decide) input ρ σ ε []
      (by intro s hs; simp at hs) (fun x => isEmptyElim x))
    simp [sourceWordCalls]
end
noncomputable section

/-- Coherent and noncoherent adaptive query costs vanish when the input index type is empty. -/
theorem sourceAdaptiveCosts_empty_input {X H : Type} [Fintype H] [DecidableEq H]
    [IsEmpty X] {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (ε : ℝ) :
    sourceAdaptiveCoherentCost input ρ σ ε = 0 ∧
      sourceAdaptiveNoncoherentCost input ρ σ ε = 0 := by
  constructor
  · apply le_antisymm ?_ bot_le
    unfold sourceAdaptiveCoherentCost
    apply iInf_le_of_le 1
    apply iInf_le_of_le (by decide : 0<1)
    apply iInf_le_of_le SourceAdaptive.finish
    apply iInf_le_of_le
        (by trivial : sourceAdaptiveLegal (.finish : SourceAdaptive (SourceSpace n q H 1)))
    apply iInf_le_of_le (fun x => isEmptyElim x)
    simp [sourceAdaptiveCalls]
  · apply le_antisymm ?_ bot_le
    unfold sourceAdaptiveNoncoherentCost
    apply iInf_le_of_le 1
    apply iInf_le_of_le (by decide : 0<1)
    apply iInf_le_of_le SourceAdaptive.finish
    apply iInf_le_of_le
        (by trivial : sourceAdaptiveLegal (.finish : SourceAdaptive (SourceSpace n q H 1)))
    apply iInf_le_of_le (fun x => isEmptyElim x)
    simp [sourceAdaptiveCalls]
end
noncomputable section

/-- For normalized initial states, coherent and noncoherent adaptive costs each lie between half
the corresponding word query cost and that word query cost. This compares the computation
models used in [Lee et al., Theorem 4.9][LeeEtAl2011]. -/
theorem sourceAdaptive_normalized_complexity_comparison {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hρ : ∀ x, Normalized (ρ x)) :
    (sourceAdaptiveCoherentCost input ρ σ ε ≤ sourceCoherentQ input ρ σ ε ∧
      sourceCoherentQ input ρ σ ε ≤ 2*sourceAdaptiveCoherentCost input ρ σ ε) ∧
    (sourceAdaptiveNoncoherentCost input ρ σ ε ≤ sourceNoncoherentQ input ρ σ ε ∧
      sourceNoncoherentQ input ρ σ ε ≤ 2*sourceAdaptiveNoncoherentCost input ρ σ ε) := by
  have hforward : sourceCoherentQ input ρ σ ε ≤ 2*sourceAdaptiveCoherentCost input ρ σ ε ∧
      sourceNoncoherentQ input ρ σ ε ≤ 2*sourceAdaptiveNoncoherentCost input ρ σ ε := by
    cases isEmpty_or_nonempty X with
    | inl hX =>
      letI := hX
      rw [(sourceWordCosts_empty_input input ρ σ ε).1,
        (sourceWordCosts_empty_input input ρ σ ε).2]
      exact ⟨bot_le,bot_le⟩
    | inr hX =>
      letI := hX
      haveI : Nonempty H := by
        by_contra hn
        haveI : IsEmpty H := not_nonempty_iff.mp hn
        have hnρ := hρ (Classical.choice hX)
        simp [Normalized] at hnρ
      exact ⟨sourceCoherentQ_le_twice_adaptiveCost input ρ σ ε,
        sourceNoncoherentQ_le_twice_adaptiveCost input ρ σ ε⟩
  exact ⟨⟨sourceAdaptiveCoherentCost_le_sourceCoherentQ input ρ σ ε,hforward.1⟩,
    ⟨sourceAdaptiveNoncoherentCost_le_sourceNoncoherentQ input ρ σ ε,hforward.2⟩⟩
end
noncomputable section

/-- The basis embedding that initializes the record register to zero. -/
def sourceRecordInit {S : Type} [DecidableEq S] (L : ℕ) (hL : 0<L) :
    Matrix (Fin L × S) S ℂ := sourceBasisFrame (fun s => (⟨0,hL⟩,s))
end
noncomputable section

/-- Applying `sourceRecordInit` tensors the input with the zero basis record. -/
theorem sourceRecordInit_apply {S : Type} [Fintype S] [DecidableEq S]
    (L : ℕ) (hL : 0<L) (ψ : QState S) :
    sourceRecordInit L hL *ᵥ ψ = TensorState (Qatlib.Foundations.PureStateMath.Ket ⟨0,hL⟩) ψ := by
  ext ⟨l,s⟩
  simp [sourceRecordInit,sourceBasisFrame,Matrix.mulVec,dotProduct,TensorState,Qatlib.Foundations.PureStateMath.Ket,
    Prod.mk.injEq,ite_and]
end
noncomputable section

/-- Every legal adaptive computation possesses a resource-bounded word compilation whose matrix
intertwines record initialization with the adaptive pure matrix. The same identity holds
after conjugating any input matrix. -/
theorem sourceAdaptive_resource_mixed_compilation :
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    let L := max 1 (sourceAdaptiveLeaves T)
    ∃ (R : ℕ) (hR : 0<R) (C : SourceWord (SourceSpace n q H R)),
      R = L*r*(n+1) ∧ L*r ≤ R ∧ sourceWordLegal C ∧
      sourceWordCalls C ≤ 2*sourceAdaptiveCalls T ∧
      sourceWordKnown C ≤ 1+2*sourceAdaptiveCalls T ∧
      let F := sourceTreeFrame (H := H) n q r L R
      let J := sourceRecordInit (S := SourceSpace n q H r) L (by dsimp [L]; omega)
      Fᴴ*F=1 ∧ ∀ x,
        let M := sourceWordMatrix (sourceAlphabetOracle input x) C
        let A := sourceAdaptivePureMatrix (sourceAlphabetOracle input x) T
        M*(F*J) = F*A ∧ ∀ D : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ,
          M*((F*J)*D*(F*J)ᴴ)*Mᴴ = (F*A)*D*(F*A)ᴴ := by
  intro X H _ _ _ _ _ n q r hr input T hT
  obtain ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,hSim⟩ :=
    sourceAdaptive_resource_compilation X H n q r hr input T hT
  refine ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,?_⟩
  intro x
  (try dsimp only)
  have hm : sourceWordMatrix (sourceAlphabetOracle input x) C *
      (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R * sourceRecordInit (S := SourceSpace n q H r) (max 1 (sourceAdaptiveLeaves T)) (by omega)) =
      sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R * sourceAdaptivePureMatrix (sourceAlphabetOracle input x) T := by
    apply Matrix.mulVec_injective
    funext ψ
    simpa only [← Matrix.mulVec_mulVec,sourceRecordInit_apply,sourceAdaptivePureMatrix_apply]
      using! (hSim x ψ).1
  refine ⟨hm,?_⟩
  intro D
  calc
    _ = (sourceWordMatrix (sourceAlphabetOracle input x) C *
        (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R * sourceRecordInit (S := SourceSpace n q H r) (max 1 (sourceAdaptiveLeaves T)) (by omega))) * D *
        (sourceWordMatrix (sourceAlphabetOracle input x) C *
          (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R * sourceRecordInit (S := SourceSpace n q H r) (max 1 (sourceAdaptiveLeaves T)) (by omega)))ᴴ := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hm]
end
noncomputable section

/-- There exists a legal word on workspace size `2*r*(n+1)` with zero oracle calls and at most
one known gate. -/
theorem sourceRetainedRecordTree_compiled_resources {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1)) :
    ∃ C : SourceWord (SourceSpace n q H (2*r*(n+1))),
      sourceWordLegal C ∧ sourceWordCalls C = 0 ∧ sourceWordKnown C ≤ 1 := by
  obtain ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,hSim⟩ :=
    sourceAdaptive_resource_compilation X H n q r hr input
      (sourceRetainedRecordTree (SourceSpace n q H r))
      (sourceRetainedRecordTree_legal _)
  simp only [sourceRetainedRecordTree_leaves,Nat.max_eq_right (by decide : 1 ≤ 2)] at hReq
  subst R
  refine ⟨C,hC,?_,?_⟩
  · simpa only [sourceRetainedRecordTree_calls,Nat.mul_zero,Nat.le_zero] using! hcalls
  · simpa only [sourceRetainedRecordTree_calls,Nat.mul_zero,Nat.add_zero] using! hknown
end
end Qatlib.Concepts.ConversionCore.WitnessCompile

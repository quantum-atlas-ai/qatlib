/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NumericalWord.MixedWordError.HeterogeneousNumericalWordDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

/-!
# Errors for heterogeneous numerical gate words

Numerical implementations of known gates can be combined with exact oracle calls when controls
lie outside the oracle data register. The module proves unitarity and bounds the accumulated
operator, state, and measurement errors by the sum of local dyadic tolerances, following
standard circuit approximation principles described in [NielsenChuang2010]

## Main statements

* `g1`: proves unitarity of numerical steps and their word.
* `g2`: bounds operator and normalized state errors by `budget`.
* `g3`: preserves access bookkeeping and bounds event probability error by twice `budget`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.NumericalWord.MixedWordError

namespace Qatlib.Concepts.NumericalWord.MixedWordError
open Matrix Qatlib.Concepts.NumericalWord.MixedWordError
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

/-- Combines a data register of width `w` and an auxiliary register of width `n - w` into an `n`
bit register. -/
def join {n w : ℕ} (hw : w≤n) (d : Reg w) (a : Reg (n-w)) : Reg n :=
  fun i => if hi : i.val<w then d ⟨i.val,hi⟩ else a ⟨i.val-w,by omega⟩

/-- The equivalence separating an `n` bit register into its auxiliary suffix and data prefix. -/
def split {n w : ℕ} (hw : w≤n) : Reg n ≃ Reg (n-w) × Reg w where
  toFun z := (auxBits w z, dataBits w hw z)
  invFun p := join hw p.2 p.1
  left_inv z := by
    funext i
    by_cases hi : i.val<w
    · simp [join, dataBits, hi]
    · simp only [join, hi, ↓reduceDIte, auxBits]
      apply congrArg z
      apply Fin.ext
      change w+(i.val-w)=i.val
      omega
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [auxBits, join]
      rw [dif_neg (by omega)]
      apply congrArg p.1
      apply Fin.ext
      change w+i.val-w=i.val
      omega
    · funext i
      simp [dataBits, join, i.isLt]

/-- Equality of all bits at indices at least `w` is equivalent to equality of the auxiliary
suffixes. -/
private theorem tail_iff {n w : ℕ} (hw : w≤n) (p q : Reg n) :
    (∀ i : Fin n, w ≤ i.val → p i=q i) ↔ auxBits w p=auxBits w q := by
  constructor
  · intro h
    funext i
    apply h ⟨w+i.val,by omega⟩
    change w ≤ w+i.val
    omega
  · intro h i hi
    have he := congrFun h (⟨i.val-w,by omega⟩ : Fin (n-w))
    simpa [auxBits, Nat.add_sub_of_le hi] using he

/-- A call to a unitary oracle, optionally adjointed and controlled on an auxiliary bit, has a
unitary mixed step matrix. -/
private theorem call_unitary {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (s : S) (adj : Bool)
    (ctrl : Option (Fin n × Bool))
    (hc : match ctrl with | none => True | some (c,_) => w≤c.val)
    (hO : O s ∈ Matrix.unitaryGroup (Reg w) ℂ) :
    mixedStepMatrix hw O (.call s adj ctrl) ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  let Q : Matrix (Reg w) (Reg w) ℂ := if adj then (O s)ᴴ else O s
  have hQ : Q ∈ Matrix.unitaryGroup (Reg w) ℂ := by
    cases adj
    · exact hO
    · change (O s)ᴴ ∈ Matrix.unitaryGroup (Reg w) ℂ
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hO
  cases ctrl with
  | none =>
    have he : mixedStepMatrix hw O (.call s adj none) =
        relabelGate (split hw).symm (BlockDiag (fun _ : Reg (n-w) => Q)) := by
      ext p q
      simp only [mixedStepMatrix, relabelGate, Matrix.reindex_apply, BlockDiag, Matrix.submatrix_apply, Matrix.of_apply,
        split, Equiv.symm_symm]
      simp only [tail_iff hw]
      rfl
    rw [he]
    exact (relabelGate_mem_unitaryGroup _ _).2 (blockDiag_unitary _ (fun _ => hQ))
  | some cv =>
    rcases cv with ⟨c,v⟩
    let c' : Fin (n-w) := ⟨c.val-w,by omega⟩
    let B : Reg (n-w) → Matrix (Reg w) (Reg w) ℂ :=
      fun a => if a c'=v then Q else 1
    have hB : ∀ a, B a ∈ Matrix.unitaryGroup (Reg w) ℂ := by
      intro a
      dsimp only [B]
      split_ifs
      · exact hQ
      · exact Submonoid.one_mem _
    have hcoord (p : Reg n) : auxBits w p c' = p c := by
      simp only [auxBits, c']
      apply congrArg p
      apply Fin.ext
      change w+(c.val-w)=c.val
      omega
    have he : mixedStepMatrix hw O (.call s adj (some (c,v))) =
        relabelGate (split hw).symm (BlockDiag B) := by
      ext p q
      simp only [mixedStepMatrix, relabelGate, Matrix.reindex_apply, BlockDiag, Matrix.submatrix_apply, Matrix.of_apply,
        split, Equiv.symm_symm]
      simp only [tail_iff hw]
      by_cases ha : auxBits w p=auxBits w q
      · have hpq : p c=q c := (tail_iff hw p q).2 ha c hc
        by_cases hcv : q c=v <;> simp [ha, B, hcoord, hpq, Q, hcv, Matrix.one_apply]
      · simp [ha]
    rw [he]
    exact (relabelGate_mem_unitaryGroup _ _).2 (blockDiag_unitary B hB)

/-- For unitary oracles and valid controls, every ideal step in the mixed word is unitary. -/
private theorem ideal_step_unitary {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (hv : ValidControls W) (hO : ∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) :
    ∀ s ∈ W, mixedStepMatrix hw O s ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  intro s hs
  cases s with
  | known g k => exact localGateMatrix_unitary g
  | call s a c => exact call_unitary hw O s a c (by cases c <;> exact hv _ hs) (hO s)

/-- The reverse ordered product of a list of unitary matrices is unitary. -/
private theorem product_unitary {I : Type} [Fintype I] [DecidableEq I]
    {A : Type} (W : List A) (F : A → Matrix I I ℂ)
    (hF : ∀ s ∈ W, F s ∈ Matrix.unitaryGroup I ℂ) :
    (W.map F).reverse.prod ∈ Matrix.unitaryGroup I ℂ := by
  apply (Matrix.unitaryGroup I ℂ).list_prod_mem
  intro U hU
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hU)
  exact hF s hs

/-- For a mixed word with valid controls and unitary oracles, every numerical step and the
resulting numerical word are unitary. -/
theorem g1 : ∀ (n w : ℕ) (hw : w≤n) (S : Type)
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)),
    ValidControls W → (∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) →
    (∀ s ∈ W, step hw O s ∈ Matrix.unitaryGroup (Reg n) ℂ) ∧
    word hw O W ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  intro n w hw S O W hv hO
  have hs : ∀ s ∈ W, step hw O s ∈ Matrix.unitaryGroup (Reg n) ℂ := by
    intro s hmem
    cases s with
    | known g k => exact numericalGateMatrix_unitary k g
    | call s a c => exact call_unitary hw O s a c (by cases c <;> exact hv _ hmem) (hO s)
  exact ⟨hs, product_unitary W (step hw O) hs⟩

/-- The sum of operator norm differences between numerical and ideal steps is at most the word's
dyadic budget. -/
private theorem defect_sum {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)) :
    (W.map (fun s => ‖step hw O s-mixedStepMatrix hw O s‖)).sum ≤ budget W := by
  induction W with
  | nil => simp [budget, knownPrecs]
  | cons s W ih =>
    cases s with
    | known g k =>
      simp only [List.map_cons, List.sum_cons, step, mixedStepMatrix,
        budget, knownPrecs, List.filterMap_cons, List.map_cons, List.sum_cons]
      exact add_le_add (numericalGateMatrix_error k g) ih
    | call s a c => simpa [step, budget, knownPrecs] using ih

/-- For valid controls and unitary oracles, numerical word operator error and the output error
on every normalized state are at most the dyadic budget; see [Kitaev, Lemma 3][Kitaev1995]. -/
theorem g2 : ∀ (n w : ℕ) (hw : w≤n) (S : Type)
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)),
    ValidControls W → (∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) →
    ‖word hw O W-mixedWordMatrix hw O W‖ ≤ budget W ∧
    ∀ ψ : QState (Reg n), Normalized ψ →
      ‖toEuclidean_fromVec (ApplyGate (word hw O W) ψ-
        ApplyGate (mixedWordMatrix hw O W) ψ)‖ ≤ budget W := by
  intro n w hw S O W hv hO
  have ha := (g1 n w hw S O W hv hO).1
  have hi := ideal_step_unitary hw O W hv hO
  have h := l2_norm_list_map_prod_sub_prod_le W.reverse (step hw O) (mixedStepMatrix hw O)
    (fun s hs => l2_norm_unitary_le_one (ha s (List.mem_reverse.mp hs)))
    (fun s hs => l2_norm_unitary_le_one (hi s (List.mem_reverse.mp hs)))
  have hm : ‖word hw O W-mixedWordMatrix hw O W‖ ≤ budget W := by
    apply (show ‖word hw O W-mixedWordMatrix hw O W‖ ≤
      (W.map (fun s => ‖step hw O s-mixedStepMatrix hw O s‖)).sum from by
        simpa only [word, mixedWordMatrix, List.map_reverse, List.sum_reverse] using h).trans
    exact defect_sum hw O W
  refine ⟨hm,?_⟩
  intro ψ hψ
  have he : ApplyGate (word hw O W) ψ-ApplyGate (mixedWordMatrix hw O W) ψ =
      ApplyGate (word hw O W-mixedWordMatrix hw O W) ψ := by
    exact (Matrix.sub_mulVec _ _ _).symm
  rw [he]
  have hn := norm_applyGate_le (word hw O W-mixedWordMatrix hw O W) ψ
  rw [(normalized_iff_norm_toEuclidean_fromVec ψ).1 hψ, mul_one] at hn
  exact hn.trans hm

/-- For a legal word with valid controls and unitary oracles, mapping the identity over the word
preserves access counts and legality. The numerical and ideal outputs have event probability
difference at most twice the dyadic budget on every normalized input; see [Kitaev, Lemma
5][Kitaev1995]. -/
theorem g3 : ∀ (n w : ℕ) (hw : w≤n) (S : Type) [DecidableEq S]
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (paid : List (AccessForm S)), ValidControls W → mixedWordLegal W paid →
    (∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) →
    (∀ φ : AccessForm S, accessCount (W.map id) φ=accessCount W φ) ∧
    mixedWordLegal (W.map id) paid ∧
    ∀ (ψ : QState (Reg n)) (E : Finset (Reg n)), Normalized ψ →
      |MeasureProb (ApplyGate (word hw O W) ψ) E-
        MeasureProb (ApplyGate (mixedWordMatrix hw O W) ψ) E| ≤ 2*budget W := by
  intro n w hw S _ O W paid hv hp hO
  refine ⟨fun _ => by simp, by simpa using hp, ?_⟩
  intro ψ E hψ
  have ha := (g1 n w hw S O W hv hO).2
  have hi := product_unitary W (mixedStepMatrix hw O) (ideal_step_unitary hw O W hv hO)
  exact (measureProb_sub_le_two_mul_l2 _ _ E
    (normalized_applyGate ha hψ) (normalized_applyGate hi hψ)).trans
      (mul_le_mul_of_nonneg_left ((g2 n w hw S O W hv hO).2 ψ hψ) (by norm_num))

end
end Qatlib.Concepts.NumericalWord.MixedWordError

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorDefs
import Qatlib.Concepts.TrotterFormula.ImaginaryTime.FiniteImaginaryProductConsumers
import Qatlib.Foundations.OperatorErrors.OperatorError
import QuantumInfo.ForMathlib.HermitianMat.LogExp
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Finite Strang synthesis and imaginary-time products

This module proves finite Strang word guarantees for unitary evolution, observable error,
compiled gate costs, adjoints, and the specified controlled embedding. It also shows that the
proposed synthesis-budget assertion `G102block4`, and hence the conjunction in `not_clause59`,
is false. The product-formula estimates are situated in the framework of
[ChildsEtAl2021Trotter].

The imaginary-time results establish selected accuracy for positive semidefinite terms and
Hermitian positive semidefinite ferromagnetic products. Supporting Pauli identities yield the
exponential representation of the on-site matchgate.

## Main statements

* `clause59_block1`: unitarity, length, tariffs, and finite Strang error.
* `clause59_block3`: compiled Strang resources and accumulated error.
* `clause59_block4_refutable`: refutation of the proposed synthesis-budget assertion.
* `clause61_block3`: Hermitian positive semidefinite ferromagnetic evolution and products.
* `clause61_block4_f`: exponential formula for the on-site matchgate.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.TrotterFormula.FiniteStrang
open Qatlib.Concepts.TrotterFormula.ImaginaryTime
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.RandCompile.ReferenceModel
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For Hermitian terms and a positive segment count, the finite Strang word is unitary, has the
stated length, label counts, and tariff, and satisfies the cubic-time error bound
[ChildsEtAl2021Trotter]. -/
theorem clause59_block1 :
    (∀ (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ) (price : ℕ → ℕ),
      (∀ j, (H j).IsHermitian) → 0 < r →
      let w := finiteStrangWord H t r
      pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ w.length = 2*m*r ∧
      (∀ j : Fin m, (w.map Prod.snd).count j.val = 2*r) ∧
      (w.map (fun x => price x.2)).sum = 2*r*(∑ j : Fin m, price j.val) ∧
      ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) t‖ ≤
        |t|^3*finiteStrangConstant H/(r : ℝ)^2) :=
  finite_strang_same_word_error_and_tariffs

/-- The selected finite Strang word has positive segment count, the prescribed length, and
operator error at most `ε`; its observable conjugation error is at most `2 * ‖O‖ * ε`. -/
theorem clause59_block2 :
    (∀ (D m : ℕ) (H : Fin m → Operator D) (t ε : ℝ) (O : Operator D),
      (∀ j, (H j).IsHermitian) → 0 < ε →
      let r := finiteStrangSegments H t ε
      let w := finiteStrangWord H t r
      0 < r ∧ w.length = 2*m*r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ‖pfInterpret w-HamiltonianEvolution (∑ j, H j) t‖ ≤ ε ∧
      ‖(pfInterpret w)ᴴ*O*pfInterpret w -
        (HamiltonianEvolution (∑ j, H j) t)ᴴ*O*HamiltonianEvolution (∑ j, H j) t‖ ≤
          2*‖O‖*ε) :=
  finite_strang_selected_accuracy_and_observable

/-- The proposed assertion that selecting Strang segments from half the tolerance also controls
the accumulated declared synthesis errors and the compiled evolution error. -/
def G102block4 : Prop :=
  (∀ (n m : ℕ) (H : Fin m → Operator (2 ^ n)) (t ε : ℝ)
      (synth : Fin m → StrangAccessSynthesis n),
    (∀ j, (H j).IsHermitian) → 0 < ε →
    (∀ (r : ℕ), 0 < r → ∀ j : Fin m,
        (synthAccessMatrix (synth j)) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
        0 ≤ (synth j).floatError ∧ 0 ≤ (synth j).gateError ∧
        ‖synthAccessMatrix (synth j) -
            HamiltonianEvolution (H j) (t/(2*(r : ℝ)))‖ ≤
          (synth j).floatError + (synth j).gateError ∧
        gateWordDataBits (synth j).word ≤ (synth j).declaredDataBits) →
    let r := finiteStrangSegments H t (ε/2)
    0 < r ∧
    2*(r : ℝ)*(∑ j : Fin m, ((synth j).floatError + (synth j).gateError)) ≤ ε/2 ∧
    ‖strangBlockMatrix (strangAccessBlocks synth r) -
        HamiltonianEvolution (∑ j, H j) t‖ ≤ ε)

/-- Relabeling a matrix identity along a finite equivalence preserves the identity. -/
private theorem relabelGate_one {S T : Type} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] (e : S ≃ T) : relabelGate e (1 : Matrix S S ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.one_apply]

/-- Evolution under a zero Hamiltonian is the identity matrix. -/
private theorem hamiltonianEvolution_of_zero {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) (hH : H = 0) : HamiltonianEvolution H t = 1 := by
  subst hH
  simp [HamiltonianEvolution]

/-- A one-label synthesis record with empty gate words and declared floating error one, used to
test the proposed synthesis-budget assertion. -/
private def badSynth : Fin 1 → StrangAccessSynthesis 0 :=
  fun _ => { word := [], controlledWord := [], declaredControlledGates := 0,
             declaredDataBits := 0, declaredFloatBits := 0,
             floatError := 1, gateError := 0, classicalCost := 0 }

/-- The access matrix of `badSynth` is the identity. -/
private theorem badSynth_access (j : Fin 1) : synthAccessMatrix (badSynth j) = 1 := by
  simp [synthAccessMatrix, badSynth, gateWordMatrix, relabelGate_one]

/-- The synthesis-budget assertion `G102block4` is false. -/
theorem clause59_block4_refutable : ¬ G102block4 := by
  intro h
  let H : Fin 1 → Operator (2 ^ 0) := fun _ => 0
  have hH : ∀ j, (H j).IsHermitian := by
    intro j; simp [H]
  have hsyn : ∀ (r : ℕ), 0 < r → ∀ j : Fin 1,
      (synthAccessMatrix (badSynth j)) ∈ Matrix.unitaryGroup (Fin (2 ^ 0)) ℂ ∧
      0 ≤ (badSynth j).floatError ∧ 0 ≤ (badSynth j).gateError ∧
      ‖synthAccessMatrix (badSynth j) -
          HamiltonianEvolution (H j) (0/(2*(r : ℝ)))‖ ≤
        (badSynth j).floatError + (badSynth j).gateError ∧
      gateWordDataBits (badSynth j).word ≤ (badSynth j).declaredDataBits := by
    intro r hr j
    rw [badSynth_access]
    have hE : HamiltonianEvolution (H j) (0/(2*(r : ℝ))) = 1 := by
      apply hamiltonianEvolution_of_zero
      simp [H]
    rw [hE]
    constructor
    · exact (Matrix.unitaryGroup _ _).one_mem
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [badSynth]
      · simp [badSynth]
      · simp [badSynth]
      · simp [badSynth, gateWordDataBits]
  obtain ⟨_, hbudget, _⟩ := h 0 1 H 0 1 badSynth hH (by norm_num) hsyn
  have hsum : (∑ j : Fin 1, ((badSynth j).floatError + (badSynth j).gateError)) = 1 := by
    simp [badSynth]
  have hr1 : (1 : ℝ) ≤ finiteStrangSegments H 0 (1/2) := by
    exact_mod_cast Nat.le_max_left _ _
  have hne : ¬ (2 * ((finiteStrangSegments H 0 (1/2) : ℝ)) *
      (∑ j : Fin 1, ((badSynth j).floatError + (badSynth j).gateError)) ≤ (1:ℝ)/2) := by
    rw [hsum]
    have := hr1
    nlinarith
  exact hne hbudget

/-- The label sequence obtained by repeating the forward and reverse traversal of `Fin m` for
`r` segments. -/
private def visitLabels (m r : ℕ) : List (Fin m) :=
  (List.replicate r (List.finRange m ++ (List.finRange m).reverse)).flatten

/-- Successive left multiplication along a list equals the reverse ordered product of the mapped
factors multiplied by the initial value. -/
private theorem foldl_mul_eq {M : Type} [Monoid M] {α : Type} (f : α → M) (xs : List α) (U : M) :
    xs.foldl (fun W V => f V * W) U = ((xs.map f).reverse.prod) * U := by
  induction xs generalizing U with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih (f x * U)]
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one]
    exact (mul_assoc ((xs.map f).reverse.prod) (f x) U).symm

/-- Successive left multiplication starting at one equals the reverse ordered product of the
mapped factors. -/
private theorem foldl_one_eq {M : Type} [Monoid M] {α : Type} (f : α → M) (xs : List α) :
    xs.foldl (fun W V => f V * W) 1 = (xs.map f).reverse.prod := by
  rw [foldl_mul_eq, mul_one]

/-- Relabeling a matrix product along a finite equivalence preserves multiplication. -/
private theorem relabelGate_mul {S T : Type} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] (e : S ≃ T) (A B : Matrix S S ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp e.symm (fun k => A (e.symm i) k * B k (e.symm j))).symm

/-- Relabeling a finite list product equals the product of the relabeled matrices. -/
private theorem relabelGate_list_prod {S T : Type} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] (e : S ≃ T) (xs : List (Matrix S S ℂ)) :
    relabelGate e xs.prod = (xs.map (relabelGate e)).prod := by
  induction xs with
  | nil => simp [relabelGate_one]
  | cons x xs ih => rw [List.prod_cons, relabelGate_mul, ih, List.map_cons, List.prod_cons]

/-- Summing a function over the Strang visit sequence gives `2 * r` copies of its sum over all
labels. -/
private theorem visitLabels_sum {m r : ℕ} {M : Type} [AddCommMonoid M] (f : Fin m → M) :
    ((visitLabels m r).map f).sum = (2 * r) • (∑ j : Fin m, f j) := by
  have hstep : ((List.finRange m ++ (List.finRange m).reverse).map f).sum =
      2 • (∑ j : Fin m, f j) := by
    rw [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
      ← List.ofFn_eq_map, List.sum_ofFn]
    rw [two_nsmul]
  unfold visitLabels
  simp only [List.map_flatten, List.sum_flatten, List.map_replicate, List.sum_replicate]
  rw [hstep, ← mul_nsmul]

/-- The Strang access blocks are the visit-label sequence mapped to the corresponding synthesis
words and labels. -/
private theorem strangAccessBlocks_eq {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : strangAccessBlocks synth r =
      (visitLabels m r).map (fun j => ((synth j).word, j)) := by
  simp [strangAccessBlocks, visitLabels, List.map_flatten, List.map_replicate]

/-- The labels of the Strang access blocks form `visitLabels m r`. -/
private theorem strangAccessBlocks_map_snd {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : (strangAccessBlocks synth r).map Prod.snd = visitLabels m r := by
  rw [strangAccessBlocks_eq]
  simp [List.map_map, Function.comp_def]

/-- The finite Strang word maps each visit label to its Hamiltonian evolution for time `t/(2*r)`
and its natural-number label. -/
private theorem finiteStrangWord_eq {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) (r : ℕ) :
    finiteStrangWord H t r = (visitLabels m r).map
      (fun j => (HamiltonianEvolution (H j) (t/(2*r)), j.val)) := by
  simp [finiteStrangWord, visitLabels, List.map_flatten, List.map_replicate]

/-- The interpretation of a labeled product-formula word is the product of its matrices in
reverse list order. -/
private theorem pfInterpret_eq_prod {D : ℕ} (xs : List (Operator D × ℕ)) :
    pfInterpret xs = (xs.reverse.map Prod.fst).prod := by
  unfold pfInterpret
  rw [foldl_one_eq, List.map_reverse]

/-- The register matrix of a block word is the product of its gate-word matrices in reverse
block order. -/
private theorem strangRegBlockMatrix_eq_prod {n m : ℕ}
    (w : List (List (LocalQFTGate n) × Fin m)) :
    strangRegBlockMatrix w = (w.reverse.map (fun b => gateWordMatrix b.1)).prod := by
  unfold strangRegBlockMatrix
  rw [foldl_one_eq, List.map_id', List.map_reverse]

/-- The matrix of the Strang access blocks is the reverse visit-order product of their synthesis
access matrices. -/
private theorem strangBlockMatrix_eq_prod {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : strangBlockMatrix (strangAccessBlocks synth r) =
      ((visitLabels m r).reverse.map (fun j : Fin m => synthAccessMatrix (synth j))).prod := by
  unfold strangBlockMatrix
  rw [strangRegBlockMatrix_eq_prod, strangAccessBlocks_eq]
  simp only [List.map_reverse, List.map_map, Function.comp_def]
  rw [relabelGate_list_prod]
  simp only [List.map_reverse, List.map_map, Function.comp_def, synthAccessMatrix]

/-- Each label occurs exactly `2 * r` times in the Strang visit sequence. -/
private theorem visitLabels_count {m r : ℕ} (j : Fin m) :
    (visitLabels m r).count j = 2 * r := by
  simp only [visitLabels, List.count_flatten, List.map_replicate, List.sum_replicate,
    List.count_append, List.count_reverse, List.count_finRange]
  rw [Nat.nsmul_eq_mul]
  all_goals omega

/-- The Strang visit sequence has length `2 * m * r`. -/
private theorem visitLabels_length {m r : ℕ} : (visitLabels m r).length = 2 * m * r := by
  simp only [visitLabels, List.length_flatten, List.map_replicate, List.sum_replicate,
    List.length_append, List.length_reverse, List.length_finRange]
  rw [Nat.nsmul_eq_mul]
  ring

/-- Under the stated unitary synthesis, error, and data-size assumptions, the compiled Strang
blocks have the prescribed visit counts and resource totals. Their evolution error is
bounded by `strangCompileBudget`. -/
theorem clause59_block3 :
    (∀ (n m r : ℕ) (H : Fin m → Operator (2 ^ n)) (t : ℝ)
      (price : Fin m → ℕ) (synth : Fin m → StrangAccessSynthesis n),
    (∀ j, (H j).IsHermitian) → 0 < r →
    (∀ j : Fin m,
        (synthAccessMatrix (synth j)) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
        0 ≤ (synth j).floatError ∧ 0 ≤ (synth j).gateError ∧
        ‖synthAccessMatrix (synth j) -
            HamiltonianEvolution (H j) (t/(2*(r : ℝ)))‖ ≤
          (synth j).floatError + (synth j).gateError ∧
        gateWordDataBits (synth j).word ≤ (synth j).declaredDataBits) →
    let blocks := strangAccessBlocks synth r
    (blocks.map Prod.snd).length = 2*m*r ∧
    (∀ j : Fin m, (blocks.map Prod.snd).count j = 2*r) ∧
    strangBlockMatrix blocks ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
    blockTariffTotal price blocks = 2*r*(∑ j : Fin m, price j) ∧
    blockGateTotal blocks = 2*r*(∑ j : Fin m, (synth j).word.length) ∧
    blockDataBitsTotal blocks ≤ 2*r*(∑ j : Fin m, (synth j).declaredDataBits) ∧
    blockClassicalCostTotal synth r = 2*r*(∑ j : Fin m, (synth j).classicalCost) ∧
    forwardSpaceQubits n = n ∧
    ‖strangBlockMatrix blocks - HamiltonianEvolution (∑ j, H j) t‖ ≤
      strangCompileBudget H synth t r) := by
  intro n m r H t price synth hH hr hsyn
  (try dsimp only)
  have herr (j : Fin m) :
      ‖synthAccessMatrix (synth j) - HamiltonianEvolution (H j) (t/(2*(r : ℝ)))‖ ≤
        (synth j).floatError + (synth j).gateError := (hsyn j).2.2.2.1
  have hunit (j : Fin m) : synthAccessMatrix (synth j) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
    (hsyn j).1
  have hbits (j : Fin m) : gateWordDataBits (synth j).word ≤ (synth j).declaredDataBits :=
    (hsyn j).2.2.2.2
  have hlen : ((strangAccessBlocks synth r).map Prod.snd).length = 2*m*r := by
    rw [strangAccessBlocks_map_snd, visitLabels_length]
  have hcount : ∀ j : Fin m, ((strangAccessBlocks synth r).map Prod.snd).count j = 2*r := by
    intro j
    rw [strangAccessBlocks_map_snd, visitLabels_count]
  have hunitBlock : strangBlockMatrix (strangAccessBlocks synth r) ∈
      Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    rw [strangBlockMatrix_eq_prod]
    refine Submonoid.list_prod_mem _ ?_
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hunit j
  have htariff : blockTariffTotal price (strangAccessBlocks synth r) = 2*r*(∑ j : Fin m, price j) := by
    unfold blockTariffTotal
    rw [strangAccessBlocks_eq, List.map_map]
    simp only [Function.comp_def]
    rw [visitLabels_sum, Nat.nsmul_eq_mul]
  have hgate : blockGateTotal (strangAccessBlocks synth r) =
      2*r*(∑ j : Fin m, (synth j).word.length) := by
    unfold blockGateTotal
    rw [strangAccessBlocks_eq, List.map_map]
    simp only [Function.comp_def]
    rw [visitLabels_sum, Nat.nsmul_eq_mul]
  have hdata : blockDataBitsTotal (strangAccessBlocks synth r) ≤
      2*r*(∑ j : Fin m, (synth j).declaredDataBits) := by
    unfold blockDataBitsTotal
    rw [strangAccessBlocks_eq, List.map_map]
    simp only [Function.comp_def]
    have hle : ((visitLabels m r).map
        (fun j => gateWordDataBits (synth j).word)).sum ≤
        ((visitLabels m r).map (fun j => (synth j).declaredDataBits)).sum := by
      induction visitLabels m r with
      | nil => simp
      | cons j js ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (hbits j) ih
    refine hle.trans ?_
    rw [visitLabels_sum, Nat.nsmul_eq_mul]
  have hclass : blockClassicalCostTotal synth r = 2*r*(∑ j : Fin m, (synth j).classicalCost) := by
    unfold blockClassicalCostTotal
    rw [strangAccessBlocks_eq, List.map_map]
    simp only [Function.comp_def]
    rw [visitLabels_sum, Nat.nsmul_eq_mul]
  have hspace : forwardSpaceQubits n = n := rfl
  refine ⟨hlen, hcount, hunitBlock, htariff, hgate, hdata, hclass, hspace, ?_⟩
  have htelesc : ‖strangBlockMatrix (strangAccessBlocks synth r) -
      pfInterpret (finiteStrangWord H t r)‖ ≤
      ((visitLabels m r).map (fun j => (synth j).floatError + (synth j).gateError)).sum := by
    have hrew : ((finiteStrangWord H t r).reverse.map Prod.fst).prod =
        ((visitLabels m r).reverse.map
          (fun j : Fin m => HamiltonianEvolution (H j) (t/(2*(r : ℝ))))).prod := by
      rw [finiteStrangWord_eq]
      simp only [List.map_reverse, List.map_map, Function.comp_def]
    rw [strangBlockMatrix_eq_prod, pfInterpret_eq_prod, hrew]
    have h := l2_norm_list_map_prod_sub_prod_le ((visitLabels m r).reverse)
      (fun j : Fin m => synthAccessMatrix (synth j))
      (fun j : Fin m => HamiltonianEvolution (H j) (t/(2*(r : ℝ))))
      (fun j _ => l2_norm_unitary_le_one (hunit j))
      (fun j _ => l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hH j) _))
    refine h.trans ?_
    rw [List.map_reverse, List.sum_reverse]
    induction (visitLabels m r) with
    | nil => simp
    | cons j js ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (herr j) ih
  have hstrang : ‖pfInterpret (finiteStrangWord H t r) -
      HamiltonianEvolution (∑ j, H j) t‖ ≤ |t|^3*finiteStrangConstant H/(r : ℝ)^2 := by
    obtain ⟨_, _, _, _, hs⟩ := clause59_block1 (2 ^ n) m r H t (fun _ => 0) hH hr
    exact hs
  have hsum : ((visitLabels m r).map (fun j => (synth j).floatError + (synth j).gateError)).sum
      = 2 * (r : ℝ) * ∑ j : Fin m, ((synth j).floatError + (synth j).gateError) := by
    rw [visitLabels_sum, nsmul_eq_mul]
    push_cast
    ring
  have hfinal : ‖strangBlockMatrix (strangAccessBlocks synth r) -
      HamiltonianEvolution (∑ j, H j) t‖ ≤
      ‖strangBlockMatrix (strangAccessBlocks synth r) - pfInterpret (finiteStrangWord H t r)‖ +
      ‖pfInterpret (finiteStrangWord H t r) - HamiltonianEvolution (∑ j, H j) t‖ := by
    have hkey : strangBlockMatrix (strangAccessBlocks synth r) -
        pfInterpret (finiteStrangWord H t r) +
        (pfInterpret (finiteStrangWord H t r) - HamiltonianEvolution (∑ j, H j) t) =
        strangBlockMatrix (strangAccessBlocks synth r) - HamiltonianEvolution (∑ j, H j) t := by
      abel
    have h := norm_add_le (strangBlockMatrix (strangAccessBlocks synth r) -
        pfInterpret (finiteStrangWord H t r))
      (pfInterpret (finiteStrangWord H t r) - HamiltonianEvolution (∑ j, H j) t)
    rw [← hkey]
    exact h
  refine hfinal.trans ?_
  unfold strangCompileBudget
  rw [← hsum]
  have hadd : ‖strangBlockMatrix (strangAccessBlocks synth r) -
      pfInterpret (finiteStrangWord H t r)‖ +
      ‖pfInterpret (finiteStrangWord H t r) - HamiltonianEvolution (∑ j, H j) t‖ =
      ‖pfInterpret (finiteStrangWord H t r) - HamiltonianEvolution (∑ j, H j) t‖ +
      ‖strangBlockMatrix (strangAccessBlocks synth r) -
        pfInterpret (finiteStrangWord H t r)‖ := add_comm _ _
  rw [hadd]
  exact add_le_add hstrang htelesc

/-- The matrix of the adjoint local program is the conjugate transpose of the original program
matrix. -/
private theorem localProgramMatrix_adjoint {n : ℕ} (gs : List (LocalQFTGate n)) :
    localProgramMatrix (localProgramAdjoint gs) = (localProgramMatrix gs)ᴴ :=
  (localDyadicProgram_run_adjoint_cost n gs (fun _ => 0)).2.1

/-- Taking the adjoint of a local program preserves its length. -/
private theorem localProgramAdjoint_length {n : ℕ} (gs : List (LocalQFTGate n)) :
    (localProgramAdjoint gs).length = gs.length := by
  simp [localProgramAdjoint]

/-- The gate-word matrix of the adjoint program is the conjugate transpose of the original
gate-word matrix. -/
private theorem gateWordMatrix_adjoint {n : ℕ} (gs : List (LocalQFTGate n)) :
    gateWordMatrix (localProgramAdjoint gs) = (gateWordMatrix gs)ᴴ := by
  unfold gateWordMatrix
  have h : (localProgramAdjoint gs).reverse = localProgramAdjoint gs.reverse := by
    simp [localProgramAdjoint, List.map_reverse]
  rw [h, localProgramMatrix_adjoint]

/-- The conjugate transpose of a matrix-list product is the reverse ordered product of the
conjugate transposes. -/
private theorem conjTranspose_list_prod {n : ℕ} (xs : List (Matrix (Reg n) (Reg n) ℂ)) :
    xs.prodᴴ = (xs.reverse.map (fun x => xᴴ)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons, Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

/-- The conjugate transpose of a register block matrix is the forward list product of the
conjugate transposes of its gate-word matrices. -/
private theorem strangRegBlockMatrix_conjTranspose {n m : ℕ}
    (w : List (List (LocalQFTGate n) × Fin m)) :
    (strangRegBlockMatrix w)ᴴ = (w.map (fun b => (gateWordMatrix b.1)ᴴ)).prod := by
  rw [strangRegBlockMatrix_eq_prod, List.map_reverse]
  have h := conjTranspose_list_prod (w.reverse.map (fun b => gateWordMatrix b.1))
  rw [List.map_reverse, List.reverse_reverse, List.map_map] at h
  simp only [Function.comp_def] at h
  exact h

/-- Reversing a flattened list equals flattening the reversed outer list with each inner list
reversed. -/
private theorem flatten_reverse {α : Type} (L : List (List α)) :
    (List.flatten L).reverse = (L.reverse.map List.reverse).flatten := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.flatten_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.reverse_append, ih]

/-- The Strang visit sequence is invariant under reversal. -/
private theorem visitLabels_reverse {m r : ℕ} : (visitLabels m r).reverse = visitLabels m r := by
  unfold visitLabels
  rw [flatten_reverse, List.reverse_replicate, List.map_replicate]
  congr 1
  apply congrArg (List.replicate r)
  rw [List.reverse_append, List.reverse_reverse]

/-- The adjoint Strang blocks represent the conjugate transpose of the forward register matrix
and preserve gate totals, tariffs, and the label sequence. -/
theorem clause59_block5 :
    (∀ (n m r : ℕ) (synth : Fin m → StrangAccessSynthesis n)
      (price : Fin m → ℕ),
    let blocks := strangAccessBlocks synth r
    strangRegBlockMatrix (strangAdjointBlocks synth r) =
      (strangRegBlockMatrix blocks)ᴴ ∧
    blockGateTotal (strangAdjointBlocks synth r) = blockGateTotal blocks ∧
    blockTariffTotal price (strangAdjointBlocks synth r) =
      blockTariffTotal price blocks ∧
    (strangAdjointBlocks synth r).map Prod.snd =
      (strangAccessBlocks synth r).map Prod.snd) := by
  intro n m r synth price
  (try dsimp only)
  have hblocks : strangAdjointBlocks synth r = (strangAccessBlocks synth r).reverse.map
      (fun b => (localProgramAdjoint b.1, b.2)) := rfl
  have hmat : strangRegBlockMatrix (strangAdjointBlocks synth r) =
      (strangRegBlockMatrix (strangAccessBlocks synth r))ᴴ := by
    rw [hblocks, strangRegBlockMatrix_eq_prod, strangRegBlockMatrix_conjTranspose]
    have hrev : ((strangAccessBlocks synth r).reverse.map
        (fun b => (localProgramAdjoint b.1, b.2))).reverse =
        (strangAccessBlocks synth r).map (fun b => (localProgramAdjoint b.1, b.2)) := by
      rw [List.map_reverse, List.reverse_reverse]
    rw [hrev, List.map_map]
    simp only [Function.comp_def, gateWordMatrix_adjoint]
  have hgate : blockGateTotal (strangAdjointBlocks synth r) =
      blockGateTotal (strangAccessBlocks synth r) := by
    unfold blockGateTotal
    rw [hblocks, List.map_map]
    simp only [Function.comp_def, localProgramAdjoint_length]
    rw [List.map_reverse, List.sum_reverse]
  have htariff : blockTariffTotal price (strangAdjointBlocks synth r) =
      blockTariffTotal price (strangAccessBlocks synth r) := by
    unfold blockTariffTotal
    rw [hblocks, List.map_map]
    simp only [Function.comp_def]
    rw [List.map_reverse, List.sum_reverse]
  have hsnd : (strangAdjointBlocks synth r).map Prod.snd =
      (strangAccessBlocks synth r).map Prod.snd := by
    have h : (strangAdjointBlocks synth r).map Prod.snd
        = ((strangAccessBlocks synth r).map Prod.snd).reverse := by
      rw [hblocks, List.map_map, List.map_reverse]
      simp only [Function.comp_def]
    rw [h, strangAccessBlocks_map_snd]
    exact visitLabels_reverse
  exact ⟨hmat, hgate, htariff, hsnd⟩

/-- The embedding is diagonal: on equal indices it uses the diagonal entry of `U` when the last
bit is true and one otherwise. -/
private theorem regControlEmbed_apply {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) (x y : Reg (n + 1)) :
    regControlEmbed U x y = if x = y then
      (if x (Fin.last n) = true then
        U (fun i => x i.castSucc) (fun i => x i.castSucc) else 1) else 0 := by
  unfold regControlEmbed
  simp only [Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x (Fin.last n) = true
    · simp [hx]
    · simp [hx]
  · have hfirst : ¬ (x (Fin.last n) = true ∧ y (Fin.last n) = true ∧
        ∀ i : Fin n, x i.castSucc = y i.castSucc) := by
      intro hc
      apply hxy
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact hc.2.2 j
      · exact hc.1.trans hc.2.1.symm
    simp [hxy, hfirst]

/-- Applying `regControlEmbed` to the identity matrix gives the identity matrix on the enlarged
register. -/
private theorem regControlEmbed_one {n : ℕ} :
    regControlEmbed (n := n) (1 : Matrix (Reg n) (Reg n) ℂ) = 1 := by
  ext x y
  rw [regControlEmbed_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · simp [hxy]

/-- The matrix of every local gate word is unitary. -/
private theorem gateWordMatrix_unitary {n : ℕ} (gs : List (LocalQFTGate n)) :
    gateWordMatrix gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  unfold gateWordMatrix
  exact (localDyadicProgram_run_adjoint_cost n gs.reverse (fun _ => 0)).2.2.2.2.1

/-- Extends an `n`-bit register value by setting its final bit to true. -/
private def extendTrue {n : ℕ} (k : Reg n) : Reg (n + 1) :=
  fun i => if h : i.val < n then k ⟨i.val, h⟩ else true

/-- The final bit of `extendTrue k` is true. -/
private theorem extendTrue_last {n : ℕ} (k : Reg n) :
    extendTrue k (Fin.last n) = true := by
  simp [extendTrue]

/-- The original register bits are unchanged by `extendTrue`. -/
private theorem extendTrue_castSucc {n : ℕ} (k : Reg n) (i : Fin n) :
    extendTrue k i.castSucc = k i := by
  simp [extendTrue]

/-- Restricting `extendTrue k` to the original bit positions recovers `k`. -/
private theorem extendTrue_castSucc_fun {n : ℕ} (k : Reg n) :
    (fun i : Fin n => extendTrue k i.castSucc) = k :=
  funext fun i => extendTrue_castSucc k i

/-- A unitary matrix whose diagonal entries all have squared norm one has zero off-diagonal
entries. -/
private theorem eq_zero_of_unitary_diag {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Reg n) ℂ) (hd : ∀ x : Reg n, Complex.normSq (M x x) = 1) :
    ∀ x y : Reg n, x ≠ y → M x y = 0 := by
  have hMM : M * Mᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hM
  intro x y hxy
  have hrow : (∑ z : Reg n, (Complex.normSq (M x z) : ℂ)) = 1 := by
    have h := congrArg (fun A : Matrix (Reg n) (Reg n) ℂ => A x x) hMM
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    convert! h using 1
    apply Finset.sum_congr rfl
    intro z _
    rw [Complex.star_def, Complex.mul_conj]
  have hre : (∑ z : Reg n, Complex.normSq (M x z)) = 1 := by
    have h2 : ((∑ z : Reg n, Complex.normSq (M x z) : ℝ) : ℂ) = 1 := by
      push_cast
      exact hrow
    refine Complex.ofReal_injective ?_
    simpa [Complex.ofReal_one] using! h2
  have hrest : (∑ z ∈ (Finset.univ : Finset (Reg n)).erase x,
      Complex.normSq (M x z)) = 0 := by
    have hsplit := Finset.sum_erase_add (f := fun z : Reg n => Complex.normSq (M x z))
      (Finset.univ) (Finset.mem_univ x)
    nlinarith [hd x]
  have hle : Complex.normSq (M x y) ≤
      ∑ z ∈ (Finset.univ : Finset (Reg n)).erase x, Complex.normSq (M x z) := by
    refine Finset.single_le_sum (fun z _ => Complex.normSq_nonneg _) ?_
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Ne.symm hxy
  have hy : Complex.normSq (M x y) = 0 := by nlinarith [Complex.normSq_nonneg (M x y)]
  exact Complex.normSq_eq_zero.mp hy

/-- Each diagonal entry of a diagonal unitary matrix has squared norm one. -/
private theorem normSq_diag_of_unitary_diagonal {n : ℕ} (D : Matrix (Reg n) (Reg n) ℂ)
    (hD : D ∈ Matrix.unitaryGroup (Reg n) ℂ)
    (hdiag : ∀ x y : Reg n, x ≠ y → D x y = 0) (x : Reg n) :
    Complex.normSq (D x x) = 1 := by
  have hMM : D * Dᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hD
  have h := congrArg (fun A : Matrix (Reg n) (Reg n) ℂ => A x x) hMM
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  have hsplit : (∑ z : Reg n, D x z * star (D x z))
      = ∑ z ∈ (Finset.univ : Finset (Reg n)).erase x, D x z * star (D x z)
          + D x x * star (D x x) :=
    (Finset.sum_erase_add (Finset.univ) (fun z : Reg n => D x z * star (D x z))
      (Finset.mem_univ x)).symm
  have hzero : (∑ z ∈ (Finset.univ : Finset (Reg n)).erase x, D x z * star (D x z)) = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hzx : x ≠ z := by
      intro h
      simp [h] at hz
    rw [hdiag x z hzx, zero_mul]
  rw [hsplit, hzero, zero_add, Complex.star_def, Complex.mul_conj] at h
  refine Complex.ofReal_injective ?_
  simpa [Complex.ofReal_one] using! h

/-- If the left factor is diagonal, a diagonal entry of its product with any matrix is the
product of the corresponding diagonal entries. -/
private theorem diagonal_mul_diag {n : ℕ} (A B : Matrix (Reg n) (Reg n) ℂ)
    (hA : ∀ x y : Reg n, x ≠ y → A x y = 0) (x : Reg n) :
    (A * B) x x = A x x * B x x := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single x ?_ ?_
  · intro z _ hz
    rw [hA x z hz.symm, zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The product of two diagonal matrices has zero off-diagonal entries. -/
private theorem diagonal_mul_off {n : ℕ} (A B : Matrix (Reg n) (Reg n) ℂ)
    (hA : ∀ x y : Reg n, x ≠ y → A x y = 0) (hB : ∀ x y : Reg n, x ≠ y → B x y = 0)
    (x y : Reg n) (hxy : x ≠ y) : (A * B) x y = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hxz : x = z
  · subst hxz
    rw [hB x y hxy, mul_zero]
  · rw [hA x z hxz, zero_mul]

/-- A list product of diagonal matrices is diagonal, and each diagonal entry is the product of
the corresponding entries of the factors. -/
private theorem diagonal_prod {n : ℕ} (cs : List (Matrix (Reg n) (Reg n) ℂ))
    (h : ∀ A ∈ cs, ∀ x y : Reg n, x ≠ y → A x y = 0) :
    (∀ x y : Reg n, x ≠ y → cs.prod x y = 0) ∧
      (∀ x : Reg n, cs.prod x x = (cs.map (fun A => A x x)).prod) := by
  induction cs with
  | nil =>
    constructor
    · intro x y hxy
      simp [hxy]
    · intro x
      simp
  | cons A cs ih =>
    have hA : ∀ x y : Reg n, x ≠ y → A x y = 0 :=
      fun x y hxy => h A List.mem_cons_self x y hxy
    have hcs : ∀ B ∈ cs, ∀ x y : Reg n, x ≠ y → B x y = 0 :=
      fun B hb x y hxy => h B (List.mem_cons_of_mem A hb) x y hxy
    obtain ⟨ih1, ih2⟩ := ih hcs
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact diagonal_mul_off A cs.prod hA ih1 x y hxy
    · intro x
      rw [List.prod_cons, diagonal_mul_diag A cs.prod hA x, ih2, List.map_cons,
        List.prod_cons]

/-- The matrix produced by `regControlEmbed` has zero off-diagonal entries. -/
private theorem regControlEmbed_diagonal {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) :
    ∀ u v : Reg (n + 1), u ≠ v → regControlEmbed U u v = 0 := by
  intro u v huv
  rw [regControlEmbed_apply, if_neg huv]

/-- When the left factor is diagonal, `regControlEmbed` preserves its product with an arbitrary
right factor. -/
private theorem regControlEmbed_mul {n : ℕ} (A B : Matrix (Reg n) (Reg n) ℂ)
    (hA : ∀ x y : Reg n, x ≠ y → A x y = 0) :
    regControlEmbed (A * B) = regControlEmbed A * regControlEmbed B := by
  have hEB1 : ∀ x y : Reg (n + 1), x ≠ y →
      (regControlEmbed A * regControlEmbed B) x y = 0 :=
    diagonal_mul_off (regControlEmbed A) (regControlEmbed B)
      (regControlEmbed_diagonal A) (regControlEmbed_diagonal B)
  have hEB2 : ∀ x : Reg (n + 1),
      (regControlEmbed A * regControlEmbed B) x x
        = regControlEmbed A x x * regControlEmbed B x x :=
    diagonal_mul_diag (regControlEmbed A) (regControlEmbed B)
      (regControlEmbed_diagonal A)
  ext x y
  by_cases hxy : x = y
  · subst hxy
    show regControlEmbed (A * B) x x = (regControlEmbed A * regControlEmbed B) x x
    rw [regControlEmbed_apply, hEB2, regControlEmbed_apply, regControlEmbed_apply]
    split_ifs with hcond
    · exact diagonal_mul_diag A B hA _
    · rw [one_mul]
    · rw [zero_mul]
  · rw [regControlEmbed_apply, if_neg hxy, hEB1 x y hxy]

/-- For a family of diagonal matrices, the product of their embeddings equals the embedding of
their product. -/
private theorem prod_regControlEmbed {n m : ℕ} (cs : List (Fin m))
    (M : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (hdiag : ∀ j, ∀ x y : Reg n, x ≠ y → M j x y = 0) :
    (cs.map (fun j => regControlEmbed (M j))).prod =
      regControlEmbed ((cs.map M).prod) := by
  induction cs with
  | nil => exact regControlEmbed_one.symm
  | cons j js ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih]
    exact (regControlEmbed_mul (M j) ((js.map M).prod) (hdiag j)).symm

/-- Under the specified controlled-word matrix identities and length bounds, the controlled
Strang blocks represent the embedded forward matrix. They satisfy the declared gate bound,
visit each label `2 * r` times, and use the stated `n+1` qubit space count. -/
theorem clause59_block6 :
    (∀ (n m r : ℕ) (synth : Fin m → StrangAccessSynthesis n),
    (∀ j : Fin m,
        (synth j).controlledWord.length ≤ (synth j).declaredControlledGates ∧
        gateWordMatrix (synth j).controlledWord =
          regControlEmbed (n := n) (gateWordMatrix (synth j).word)) →
    let cblocks := strangControlledBlocks synth r
    strangRegBlockMatrix (n := n + 1) cblocks =
      regControlEmbed (n := n)
        (strangRegBlockMatrix (strangAccessBlocks synth r)) ∧
    blockGateTotal (n := n + 1) cblocks ≤
      2*r*(∑ j : Fin m, (synth j).declaredControlledGates) ∧
    (∀ j : Fin m, (cblocks.map Prod.snd).count j = 2*r) ∧
    controlledSpaceQubits n = n + 1) := by
  intro n m r synth hsyn
  (try dsimp only)
  have hblocks : strangControlledBlocks synth r =
      (visitLabels m r).map (fun j => ((synth j).controlledWord, j)) := by
    simp [strangControlledBlocks, visitLabels, List.map_flatten, List.map_replicate]
  have hlength (j : Fin m) : (synth j).controlledWord.length ≤ (synth j).declaredControlledGates :=
    (hsyn j).1
  have hemb (j : Fin m) : gateWordMatrix (synth j).controlledWord =
      regControlEmbed (gateWordMatrix (synth j).word) := (hsyn j).2
  have hdiag (j : Fin m) : ∀ x y : Reg n, x ≠ y → gateWordMatrix ((synth j).word) x y = 0 := by
    have hunit : regControlEmbed (gateWordMatrix ((synth j).word)) ∈
        Matrix.unitaryGroup (Reg (n + 1)) ℂ := by
      rw [← hemb j]
      exact gateWordMatrix_unitary _
    have hdiagEB : ∀ u v : Reg (n + 1), u ≠ v →
        regControlEmbed (gateWordMatrix ((synth j).word)) u v = 0 :=
      regControlEmbed_diagonal _
    have hent : ∀ k : Reg n, Complex.normSq (gateWordMatrix ((synth j).word) k k) = 1 := by
      intro k
      have hxd := normSq_diag_of_unitary_diagonal _ hunit hdiagEB (extendTrue k)
      rw [regControlEmbed_apply, if_pos rfl, extendTrue_last, if_pos rfl,
        extendTrue_castSucc_fun] at hxd
      exact hxd
    intro x y hxy
    exact eq_zero_of_unitary_diag (gateWordMatrix ((synth j).word))
      (gateWordMatrix_unitary _) hent x y hxy
  have hmat : strangRegBlockMatrix (strangControlledBlocks synth r) =
      regControlEmbed (strangRegBlockMatrix (strangAccessBlocks synth r)) := by
    rw [hblocks, strangRegBlockMatrix_eq_prod]
    have hrev : ((visitLabels m r).map (fun j => ((synth j).controlledWord, j))).reverse =
        (visitLabels m r).reverse.map (fun j => ((synth j).controlledWord, j)) := by
      rw [List.map_reverse]
    rw [hrev, List.map_map]
    simp only [Function.comp_def]
    have hrew : (fun j : Fin m => gateWordMatrix ((synth j).controlledWord))
        = (fun j : Fin m => regControlEmbed (gateWordMatrix ((synth j).word))) := by
      funext j
      exact hemb j
    rw [hrew, prod_regControlEmbed (visitLabels m r).reverse
      (fun j => gateWordMatrix ((synth j).word)) hdiag]
    congr 1
    rw [strangRegBlockMatrix_eq_prod]
    have hrev2 : ((visitLabels m r).map (fun j => ((synth j).word, j))).reverse =
        (visitLabels m r).reverse.map (fun j => ((synth j).word, j)) := by
      rw [List.map_reverse]
    rw [strangAccessBlocks_eq, hrev2, List.map_map]
    simp only [Function.comp_def]
  have hgate : blockGateTotal (strangControlledBlocks synth r) ≤
      2*r*(∑ j : Fin m, (synth j).declaredControlledGates) := by
    unfold blockGateTotal
    rw [hblocks, List.map_map]
    simp only [Function.comp_def]
    have hle : ((visitLabels m r).map
        (fun j => (synth j).controlledWord.length)).sum ≤
        ((visitLabels m r).map (fun j => (synth j).declaredControlledGates)).sum := by
      induction visitLabels m r with
      | nil => simp
      | cons j js ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (hlength j) ih
    refine hle.trans ?_
    rw [visitLabels_sum, Nat.nsmul_eq_mul]
  have hcount : ∀ j : Fin m, ((strangControlledBlocks synth r).map Prod.snd).count j = 2*r := by
    intro j
    have hsnd : (strangControlledBlocks synth r).map Prod.snd = visitLabels m r := by
      rw [hblocks, List.map_map]
      simp only [Function.comp_def, List.map_id']
    rw [hsnd, visitLabels_count]
  have hspace : controlledSpaceQubits n = n + 1 := rfl
  exact ⟨hmat, hgate, hcount, hspace⟩

/-- For positive semidefinite terms, nonnegative time, and positive tolerance, the selected
imaginary-time product has positive segment count, length `m*r`, norm at most one, and error
at most `ε`. -/
theorem clause61_block1 :
    (∀ {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
      (H : Fin m → Matrix I I ℂ) (t ε : ℝ),
    (∀ j : Fin m, (H j).PosSemidef) → 0 ≤ t → 0 < ε →
    let r := finiteImaginarySegments H t ε
    0 < r ∧ (imaginaryFamilyWord H t r).length = m * r ∧
    ‖imaginaryFamilyRun H t r‖ ≤ 1 ∧
    ‖imaginaryFamilyRun H t r - NormedSpace.exp (-t • ∑ j : Fin m, H j)‖ ≤ ε) :=
  imaginary_family_selected_accuracy

/-- Every Pauli-string matrix is Hermitian. -/
private theorem pauliString_isHermitian {q : ℕ} (v : Fin q → Fin 4) :
    (pauliStringMatrix q v).IsHermitian :=
  (local_pauli_string_contract_and_support q v).1

/-- Every matrix defined by `twoWirePauli` is Hermitian. -/
private theorem twoWirePauli_isHermitian (n : ℕ) (u v : Fin n) (a b : Fin 4) :
    (twoWirePauli n u v a b).IsHermitian :=
  pauliString_isHermitian _

/-- The Pauli `Z` matrix on a specified wire is Hermitian. -/
private theorem wireZ_isHermitian (n : ℕ) (u : Fin n) :
    (wireZ n u).IsHermitian :=
  pauliString_isHermitian _

/-- A real scalar multiple of a Hermitian operator is Hermitian. -/
private theorem isHermitian_real_smul {d : ℕ} (c : ℝ) (A : Operator d)
    (hA : A.IsHermitian) : (c • A).IsHermitian :=
  hA.smul (by simp [IsSelfAdjoint])

/-- A finite list sum of Hermitian operators is Hermitian. -/
private theorem isHermitian_list_sum {d : ℕ} (xs : List (Operator d))
    (h : ∀ A ∈ xs, A.IsHermitian) : xs.sum.IsHermitian := by
  induction xs with
  | nil => exact Matrix.isHermitian_zero
  | cons A As ih =>
    rw [List.sum_cons]
    exact (h A List.mem_cons_self).add (ih fun B hb => h B (List.mem_cons_of_mem _ hb))

/-- The conjugate transpose of an operator-list product is the reverse ordered product of the
conjugate transposes. -/
private theorem conjTranspose_list_prod_gen {d : ℕ} (xs : List (Operator d)) :
    xs.prodᴴ = (xs.reverse.map (fun x => xᴴ)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons, Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

/-- For a list of Hermitian factors, the reversed product is the conjugate transpose of the
original product. -/
private theorem isHermitian_list_prod_reverse {d : ℕ} (xs : List (Operator d))
    (h : ∀ A ∈ xs, A.IsHermitian) : xs.reverse.prod = (xs.prod)ᴴ := by
  rw [conjTranspose_list_prod_gen]
  have hmap : (xs.reverse.map (fun x => xᴴ)) = xs.reverse := by
    have h1 : (xs.reverse.map (fun x => xᴴ)) = (xs.reverse.map (fun x => x)) :=
      List.map_congr_left fun x hx => h x (List.mem_reverse.mp hx)
    rw [h1, List.map_id']
  rw [hmap]

/-- For Hermitian factors, the product of a list followed by its reverse equals the original
product times its conjugate transpose. -/
private theorem list_prod_palindrome {d : ℕ} (xs : List (Operator d))
    (h : ∀ A ∈ xs, A.IsHermitian) :
    (xs ++ xs.reverse).prod = xs.prod * (xs.prod)ᴴ := by
  rw [List.prod_append, isHermitian_list_prod_reverse xs h]

/-- The product of a list of Hermitian operators followed by its reverse is Hermitian. -/
private theorem isHermitian_list_prod_palindrome {d : ℕ} (xs : List (Operator d))
    (h : ∀ A ∈ xs, A.IsHermitian) : ((xs ++ xs.reverse).prod).IsHermitian := by
  rw [list_prod_palindrome xs h]
  have := Matrix.isHermitian_conjTranspose_mul_self (xs.prod)ᴴ
  simpa using! this

/-- The product of a list of Hermitian operators followed by its reverse is positive
semidefinite. -/
private theorem posSemidef_list_prod_palindrome {d : ℕ} (xs : List (Operator d))
    (h : ∀ A ∈ xs, A.IsHermitian) : ((xs ++ xs.reverse).prod).PosSemidef := by
  rw [list_prod_palindrome xs h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

set_option backward.isDefEq.respectTransparency false in

/-- The exponential of a Hermitian operator is positive semidefinite. -/
private theorem exp_hermitian_posSemidef {d : ℕ} (A : Operator d) (hA : A.IsHermitian) :
    (NormedSpace.exp A).PosSemidef := by
  let H : HermitianMat (Fin d) ℂ := ⟨A, hA⟩
  have he : H.exp.mat = NormedSpace.exp A := by
    rw [HermitianMat.exp, HermitianMat.mat_cfc]
    letI : ContinuousFunctionalCalculus ℝ (Operator d) IsSelfAdjoint :=
      Matrix.IsHermitian.instContinuousFunctionalCalculus
    exact CFC.real_exp_eq_normedSpace_exp hA
  have hp : H.exp.mat.PosSemidef := HermitianMat.zero_le_iff.mp H.exp_nonneg
  rwa [he] at hp

/-- The exponential of a Hermitian operator is Hermitian. -/
private theorem exp_hermitian_isHermitian {d : ℕ} (A : Operator d) (hA : A.IsHermitian) :
    (NormedSpace.exp A).IsHermitian :=
  Matrix.IsHermitian.exp hA

/-- Each on-site ferromagnetic term `ferroTermD` is Hermitian. -/
private theorem ferroTermD_isHermitian (n : ℕ) (u : Fin n) : (ferroTermD n u).IsHermitian :=
  Matrix.isHermitian_one.add (wireZ_isHermitian n u)

/-- Each pair term `ferroTermP` is Hermitian. -/
private theorem ferroTermP_isHermitian (n : ℕ) (u v : Fin n) : (ferroTermP n u v).IsHermitian :=
  (twoWirePauli_isHermitian n u v 1 1).neg.sub (twoWirePauli_isHermitian n u v 2 2)

/-- Each pair term `ferroTermQ` is Hermitian. -/
private theorem ferroTermQ_isHermitian (n : ℕ) (u v : Fin n) : (ferroTermQ n u v).IsHermitian :=
  (twoWirePauli_isHermitian n u v 1 1).neg.add (twoWirePauli_isHermitian n u v 2 2)

/-- The ferromagnetic Hamiltonian associated with any `FerroData` is Hermitian. -/
private theorem ferroHamiltonian_isHermitian {n : ℕ} (F : FerroData n) :
    (ferroHamiltonian F).IsHermitian := by
  unfold ferroHamiltonian
  refine IsHermitian.add (isHermitian_list_sum _ ?_) (isHermitian_list_sum _ ?_)
  · intro A hA
    obtain ⟨uv, _, rfl⟩ := List.mem_map.mp hA
    exact (isHermitian_real_smul _ _ (ferroTermP_isHermitian n uv.1 uv.2)).add
      (isHermitian_real_smul _ _ (ferroTermQ_isHermitian n uv.1 uv.2))
  · intro A hA
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hA
    exact isHermitian_real_smul _ _ (ferroTermD_isHermitian n u)

/-- Mapping a list through a function with Hermitian values produces a list whose members are
Hermitian. -/
private theorem isHermitian_of_map {d : ℕ} {α : Type} (l : List α) (f : α → Operator d)
    (hf : ∀ a, (f a).IsHermitian) : ∀ A ∈ l.map f, A.IsHermitian := by
  intro A hA
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hA
  exact hf a

/-- Appending two lists of Hermitian operators produces a list whose members are Hermitian. -/
private theorem isHermitian_of_mem_append {d : ℕ} {l1 l2 : List (Operator d)}
    (h1 : ∀ A ∈ l1, A.IsHermitian) (h2 : ∀ A ∈ l2, A.IsHermitian) :
    ∀ A ∈ l1 ++ l2, A.IsHermitian := by
  intro A hA
  exact (List.mem_append.mp hA).elim (h1 A) (h2 A)

/-- Every operator in the exponential half-step of the ferromagnetic product is Hermitian. -/
private theorem ferroStepHalf_isHermitian {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    ∀ A ∈ ferroStepHalf F β r, A.IsHermitian := by
  unfold ferroStepHalf
  refine isHermitian_of_mem_append (isHermitian_of_mem_append ?_ ?_) ?_
  · exact isHermitian_of_map _ _ fun u => Matrix.IsHermitian.exp (isHermitian_real_smul _ _
      (isHermitian_real_smul _ _ (ferroTermD_isHermitian n u)))
  · exact isHermitian_of_map _ _ fun uv => Matrix.IsHermitian.exp (isHermitian_real_smul _ _
      (isHermitian_real_smul _ _ (ferroTermQ_isHermitian n uv.1 uv.2)))
  · exact isHermitian_of_map _ _ fun uv => Matrix.IsHermitian.exp (isHermitian_real_smul _ _
      (isHermitian_real_smul _ _ (ferroTermP_isHermitian n uv.1 uv.2)))

/-- The matrix of every `FerroMatchgate` is Hermitian. -/
private theorem ferroGateMatrix_isHermitian {n : ℕ} (g : FerroMatchgate n) :
    (ferroGateMatrix g).IsHermitian := by
  cases g with
  | f u s =>
    exact (isHermitian_real_smul _ _ Matrix.isHermitian_one).add
      (isHermitian_real_smul _ _ (wireZ_isHermitian n u))
  | g u v t =>
    refine ((isHermitian_real_smul _ _ Matrix.isHermitian_one).add
      (isHermitian_real_smul _ _
        ((twoWirePauli_isHermitian n u v 1 1).sub (twoWirePauli_isHermitian n u v 2 2)))).add ?_
    exact isHermitian_real_smul _ _ (twoWirePauli_isHermitian n u v 3 3)
  | h u v t =>
    refine (((isHermitian_real_smul _ _ Matrix.isHermitian_one).add
      (isHermitian_real_smul _ _
        ((twoWirePauli_isHermitian n u v 1 1).add (twoWirePauli_isHermitian n u v 2 2)))).sub ?_)
    exact isHermitian_real_smul _ _ (twoWirePauli_isHermitian n u v 3 3)

/-- Every matrix in the ferromagnetic matchgate half-step is Hermitian. -/
private theorem ferroGateHalf_isHermitian {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    ∀ A ∈ (ferroGateHalf F β r).map ferroGateMatrix, A.IsHermitian :=
  isHermitian_of_map _ _ fun g => ferroGateMatrix_isHermitian g

/-- For legal ferromagnetic data, the Hamiltonian is Hermitian, and the ideal imaginary-time
evolution, exponential step, matchgate step, and repeated matchgate step are Hermitian and
positive semidefinite for positive inverse temperature and segment count. -/
theorem clause61_block3 :
    (∀ (n : ℕ) (F : FerroData n), FerroLegal F →
        (ferroHamiltonian F).IsHermitian ∧
        ∀ (β : ℝ) (r : ℕ), 0 < β → 0 < r →
          (ferroIdealEvolution F β).IsHermitian ∧
          (ferroIdealEvolution F β).PosSemidef ∧
          (ferroRun F β r).IsHermitian ∧ (ferroRun F β r).PosSemidef ∧
          (ferroGateRun F β r).IsHermitian ∧ (ferroGateRun F β r).PosSemidef ∧
          (ferroGatePower F β r).IsHermitian ∧
          (ferroGatePower F β r).PosSemidef) := by
  intro n F hF
  refine ⟨ferroHamiltonian_isHermitian F, ?_⟩
  intro β r hβ hr
  have hH : (ferroHamiltonian F).IsHermitian := ferroHamiltonian_isHermitian F
  have hideal : (ferroIdealEvolution F β).IsHermitian ∧ (ferroIdealEvolution F β).PosSemidef := by
    unfold ferroIdealEvolution
    exact ⟨Matrix.IsHermitian.exp (isHermitian_real_smul _ _ hH),
      exp_hermitian_posSemidef _ (isHermitian_real_smul _ _ hH)⟩
  have hrun : (ferroRun F β r).IsHermitian ∧ (ferroRun F β r).PosSemidef := by
    unfold ferroRun ferroStepWord
    exact ⟨isHermitian_list_prod_palindrome _ (ferroStepHalf_isHermitian F β r),
      posSemidef_list_prod_palindrome _ (ferroStepHalf_isHermitian F β r)⟩
  have hgrun : (ferroGateRun F β r).IsHermitian ∧ (ferroGateRun F β r).PosSemidef := by
    unfold ferroGateRun
    have hrew : (ferroGateWord F β r).map ferroGateMatrix =
        (ferroGateHalf F β r).map ferroGateMatrix ++
          ((ferroGateHalf F β r).map ferroGateMatrix).reverse := by
      unfold ferroGateWord
      rw [List.map_append, List.map_reverse]
    rw [hrew]
    exact ⟨isHermitian_list_prod_palindrome _ (ferroGateHalf_isHermitian F β r),
      posSemidef_list_prod_palindrome _ (ferroGateHalf_isHermitian F β r)⟩
  have hpow : (ferroGatePower F β r).IsHermitian ∧ (ferroGatePower F β r).PosSemidef := by
    unfold ferroGatePower
    exact ⟨hgrun.1.pow r, hgrun.2.pow r⟩
  exact ⟨hideal.1, hideal.2, hrun.1, hrun.2, hgrun.1, hgrun.2, hpow.1, hpow.2⟩

/-- The local Pauli matrix with label zero is the identity. -/
private theorem localPauliMatrix_zero : localPauliMatrix 0 = 1 := by
  simp [localPauliMatrix]

/-- The local Pauli matrix with label one is `pauliX`. -/
private theorem localPauliMatrix_one : localPauliMatrix 1 = pauliX := by
  simp [localPauliMatrix]

/-- The local Pauli matrix with label two is `pauliY`. -/
private theorem localPauliMatrix_two : localPauliMatrix 2 = pauliY := by
  simp [localPauliMatrix]

/-- The local Pauli matrix with label three is `pauliZ`. -/
private theorem localPauliMatrix_three : localPauliMatrix 3 = pauliZ := by
  simp [localPauliMatrix]

/-- Every local Pauli matrix squares to the identity. -/
private theorem localPauliMatrix_sq (a : Fin 4) :
    localPauliMatrix a * localPauliMatrix a = 1 := by
  fin_cases a <;> simp [localPauliMatrix, pauliX, pauliY, pauliZ, Matrix.one_fin_two]

/-- Left multiplication by the label-zero local Pauli matrix preserves every local Pauli matrix. -/
private theorem localPauliMatrix_mul_one (a : Fin 4) :
    localPauliMatrix 0 * localPauliMatrix a = localPauliMatrix a := by
  fin_cases a <;> simp [localPauliMatrix, pauliX, pauliY, pauliZ, Matrix.one_fin_two]

/-- Right multiplication by the label-zero local Pauli matrix preserves every local Pauli
matrix. -/
private theorem localPauliMatrix_one_mul (a : Fin 4) :
    localPauliMatrix a * localPauliMatrix 0 = localPauliMatrix a := by
  fin_cases a <;> simp [localPauliMatrix, pauliX, pauliY, pauliZ, Matrix.one_fin_two]

/-- The product of local Pauli matrices with labels one and two equals `i` times the matrix with
label three. -/
private theorem localPauliMatrix_12 :
    localPauliMatrix 1 * localPauliMatrix 2 = Complex.I • localPauliMatrix 3 := by
  simp [localPauliMatrix, pauliX, pauliY, pauliZ]

/-- The product of local Pauli matrices with labels two and one equals `-i` times the matrix
with label three. -/
private theorem localPauliMatrix_21 :
    localPauliMatrix 2 * localPauliMatrix 1 = (-Complex.I) • localPauliMatrix 3 := by
  simp [localPauliMatrix, pauliX, pauliY, pauliZ]

/-- Every Pauli-string matrix squares to the identity. -/
private theorem pauliString_sq {q : ℕ} (v : Fin q → Fin 4) :
    pauliStringMatrix q v * pauliStringMatrix q v = 1 := by
  have h := local_pauli_string_contract_and_support q v
  have hu : pauliStringMatrix q v * (pauliStringMatrix q v)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp h.2.1
  rw [h.1.eq] at hu
  exact hu

/-- Every matrix defined by `twoWirePauli` squares to the identity. -/
private theorem twoWirePauli_sq (n : ℕ) (u v : Fin n) (a b : Fin 4) :
    twoWirePauli n u v a b * twoWirePauli n u v a b = 1 :=
  pauliString_sq _

/-- Pointwise multiplication identities for the local Pauli factors yield the corresponding
two-wire matrix identity, with phase equal to the product of the local phases. -/
private theorem twoWirePauli_mul (n : ℕ) (u v : Fin n) (a b c d e f : Fin 4)
    (φ : Fin n → ℂ)
    (h : ∀ i : Fin n,
      localPauliMatrix ((fun j => if j = u then a else if j = v then b else 0) i) *
        localPauliMatrix ((fun j => if j = u then c else if j = v then d else 0) i) =
      φ i • localPauliMatrix ((fun j => if j = u then e else if j = v then f else 0) i)) :
    twoWirePauli n u v a b * twoWirePauli n u v c d =
      (∏ i : Fin n, φ i) • twoWirePauli n u v e f := by
  unfold twoWirePauli pauliStringMatrix
  rw [tensorPauliProduct_mul, ← tensorPauliProduct_smul]
  congr 1
  funext i
  exact h i

/-- A product with distinguished phases at indices `a` and `b` equals the first phase when the
indices coincide and the product of both phases otherwise. -/
private theorem prod_ite_phase {n : ℕ} (a b : Fin n) (x y : ℂ) :
    (∏ i : Fin n, (if i = a then x else if i = b then y else 1)) =
      if a = b then x else x * y := by
  by_cases hab : a = b
  · subst hab
    have hpt : ∀ i : Fin n, (if i = a then x else if i = a then y else 1) =
        if i = a then x else (1 : ℂ) := by
      intro i
      by_cases hi : i = a <;> simp [hi]
    conv_lhs => simp only [hpt]
    simp [Finset.prod_ite_eq']
  · have hpt : ∀ i : Fin n, (if i = a then x else if i = b then y else 1) =
        (if i = a then x else (1:ℂ)) * (if i = b then y else 1) := by
      intro i
      by_cases hi : i = a
      · simp [hi, hab]
      · by_cases hj : i = b
        · simp [hj, Ne.symm hab]
        · simp [hi, hj]
    conv_lhs => simp only [hpt, Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq', hab]

/-- Real scalar multiplication of a complex operator agrees with scalar multiplication by the
corresponding complex number. -/
private theorem real_smul_eq {d : ℕ} (r : ℝ) (M : Operator d) :
    (r : ℝ) • M = ((r : ℂ)) • M :=
  (IsScalarTower.algebraMap_smul ℂ r M).symm

/-- If `A * A = 2 • A`, every positive power `A^k` equals `2^(k-1) • A`. -/
private theorem pow_two_smul {d : ℕ} (A : Operator d) (hA : A * A = (2:ℂ) • A) :
    ∀ k : ℕ, 0 < k → A ^ k = (2:ℂ) ^ (k - 1) • A := by
  intro k hk
  induction k with
  | zero => exact absurd hk (by norm_num)
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have hkp : 0 < k := Nat.pos_of_ne_zero hk0
      have hscal : (2:ℂ) ^ (k - 1) * 2 = (2:ℂ) ^ (k + 1 - 1) := by
        rw [← pow_succ, Nat.sub_add_cancel hkp, Nat.add_sub_cancel]
      rw [pow_succ, ih hkp, smul_mul_assoc, hA, smul_smul, hscal]

/-- If `A * A = 2 • A`, then `exp (z • A)` equals `1 + ((exp (2*z) - 1)/2) • A`. -/
private theorem exp_smul_two {d : ℕ} (A : Operator d) (hA : A * A = (2:ℂ) • A) (z : ℂ) :
    NormedSpace.exp (z • A) = 1 + ((Complex.exp (2 * z) - 1) / 2) • A := by
  have hg : Summable fun k : ℕ => ((2 * z) ^ k / (Nat.factorial k : ℂ)) := by
    have h := NormedSpace.expSeries_summable' (𝕂 := ℂ) (2 * z)
    have hform : (fun k : ℕ => (2 * z) ^ k / (Nat.factorial k : ℂ))
        = fun k => ((Nat.factorial k : ℂ)⁻¹) • (2 * z) ^ k := by
      funext k
      rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [hform]
    exact h
  have hp : ∀ k : ℕ, ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k) =
      ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) / 2 := by
    intro k
    have hfact : ((Nat.factorial (k + 1) : ℕ) : ℂ) ≠ 0 :=
      by exact_mod_cast (Nat.factorial_ne_zero (k + 1))
    have hpow : (2 * z) ^ (k + 1) = (2:ℂ) ^ (k + 1) * z ^ (k + 1) := mul_pow 2 z (k + 1)
    have hpow2 : (2:ℂ) ^ (k + 1) = (2:ℂ) ^ k * 2 := pow_succ 2 k
    rw [hpow, hpow2]
    field_simp [hfact]
  have hbase : NormedSpace.exp (z • A)
      = ∑' k : ℕ, (((Nat.factorial k : ℕ) : ℂ)⁻¹) • (z • A) ^ k := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  have hsplit0 : (∑' k : ℕ, (((Nat.factorial k : ℕ) : ℂ)⁻¹) • (z • A) ^ k)
      = (((Nat.factorial 0 : ℕ) : ℂ)⁻¹) • (z • A) ^ 0 +
        ∑' k : ℕ, (((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) • (z • A) ^ (k + 1) :=
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • A)).tsum_eq_zero_add
  rw [hbase, hsplit0]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero]
  have hterm : ∀ k : ℕ, (((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) • (z • A) ^ (k + 1) =
      (((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k)) • A := by
    intro k
    have hpowA : A ^ (k + 1) = (2:ℂ) ^ k • A := by
      rw [pow_two_smul A hA (k + 1) (Nat.succ_pos k), Nat.add_sub_cancel]
    rw [smul_pow, hpowA, smul_smul, smul_smul]
  conv_lhs => simp only [hterm]
  have hscalar : (∑' k : ℕ, ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k)) =
      (Complex.exp (2 * z) - 1) / 2 := by
    conv_lhs => simp only [hp]
    have hsplit : (∑' k : ℕ, ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) / 2) =
        (∑' k : ℕ, ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ))) / 2 := by
      have hform : (fun k : ℕ => ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) / 2)
          = fun k => ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) * (2:ℂ)⁻¹ := by
        funext k
        rw [div_eq_mul_inv]
      rw [hform, tsum_mul_right, div_eq_mul_inv]
    rw [hsplit]
    have hge : Complex.exp (2 * z) = 1 +
        ∑' k : ℕ, ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) := by
      have hbase2 : Complex.exp (2 * z) = ∑' k : ℕ, ((2 * z) ^ k / (Nat.factorial k : ℂ)) := by
        rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)]
      have hsplit1 : (∑' k : ℕ, ((2 * z) ^ k / (Nat.factorial k : ℂ)))
          = ((2 * z) ^ 0 / (Nat.factorial 0 : ℂ)) +
            ∑' k : ℕ, ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) :=
        hg.tsum_eq_zero_add
      rw [hbase2, hsplit1]
      simp
    have hge' : Complex.exp (2 * z) - 1 =
        ∑' k : ℕ, ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) := by
      rw [hge]
      ring
    rw [hge']
  have hc : Summable fun k : ℕ =>
      ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k) := by
    have hshift : Summable fun k : ℕ => ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) :=
      (summable_nat_add_iff 1).2 hg
    have hdiv : (fun k : ℕ => ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) / 2)
        = fun k => (2:ℂ)⁻¹ • ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) := by
      funext k
      rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
    have h2 : (fun k : ℕ => ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k))
        = fun k => ((2 * z) ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) / 2 :=
      funext fun k => hp k
    rw [h2, hdiv]
    exact hshift.const_smul _
  have hpull : (∑' k : ℕ, ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k)) • A
      = ∑' k : ℕ, (((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹) * z ^ (k + 1) * (2:ℂ) ^ k)) • A :=
    (Summable.tsum_smul_const hc A).symm
  rw [← hpull, hscalar]

/-- The Pauli `Z` operator on any wire squares to the identity. -/
private theorem wireZ_sq (n : ℕ) (u : Fin n) : wireZ n u * wireZ n u = 1 :=
  pauliString_sq _

/-- The on-site ferromagnetic term satisfies `ferroTermD * ferroTermD = 2 • ferroTermD`. -/
private theorem ferroTermD_sq (n : ℕ) (u : Fin n) :
    ferroTermD n u * ferroTermD n u = (2:ℂ) • ferroTermD n u := by
  unfold ferroTermD
  simp only [mul_add, add_mul, one_mul, mul_one, wireZ_sq, two_smul]
  abel

/-- The on-site matchgate `FerroMatchgate.f u s` equals the exponential of `(s/2) • ferroTermD n
u`. -/
theorem clause61_block4_f :
    (∀ (n : ℕ) (u : Fin n) (s : ℝ),
      ferroGateMatrix (FerroMatchgate.f u s) =
        NormedSpace.exp ((s / 2) • (ferroTermD n u))) := by
  intro n u s
  have hsmul : ((s / 2 : ℝ) • ferroTermD n u) = (((s / 2 : ℝ) : ℂ)) • ferroTermD n u :=
    real_smul_eq (s / 2) _
  rw [hsmul, exp_smul_two _ (ferroTermD_sq n u) (((s / 2 : ℝ) : ℂ))]
  have hs : (Complex.exp (2 * ((s / 2 : ℝ) : ℂ)) - 1) / 2 = (((Real.exp s - 1) / 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) * ((s / 2 : ℝ) : ℂ) = ((s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    push_cast
    ring
  rw [hs, ← real_smul_eq ((Real.exp s - 1) / 2) (ferroTermD n u)]
  have hd : ferroTermD n u = (1 : Operator (2 ^ n)) + wireZ n u := rfl
  have key : (1 : Operator (2 ^ n)) + ((Real.exp s - 1) / 2 : ℝ) • (ferroTermD n u)
      = ((Real.exp s + 1) / 2) • (1 : Operator (2 ^ n)) +
        ((Real.exp s - 1) / 2) • wireZ n u := by
    rw [hd, smul_add]
    have hs1 : ((Real.exp s + 1) / 2 : ℝ) = 1 + (Real.exp s - 1) / 2 := by ring
    conv_rhs => rw [hs1, add_smul, one_smul]
    abel
  rw [key]
  rfl

/-- The conjunction of the six stated Strang simulation and synthesis assertions is false, since
its fourth assertion implies `G102block4`. -/
theorem not_clause59 : ¬ (

  (∀ (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ) (price : ℕ → ℕ),
      (∀ j, (H j).IsHermitian) → 0 < r →
      let w := finiteStrangWord H t r
      pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ w.length = 2*m*r ∧
      (∀ j : Fin m, (w.map Prod.snd).count j.val = 2*r) ∧
      (w.map (fun x => price x.2)).sum = 2*r*(∑ j : Fin m, price j.val) ∧
      ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) t‖ ≤
        |t|^3*finiteStrangConstant H/(r : ℝ)^2) ∧

  (∀ (D m : ℕ) (H : Fin m → Operator D) (t ε : ℝ) (O : Operator D),
      (∀ j, (H j).IsHermitian) → 0 < ε →
      let r := finiteStrangSegments H t ε
      let w := finiteStrangWord H t r
      0 < r ∧ w.length = 2*m*r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ‖pfInterpret w-HamiltonianEvolution (∑ j, H j) t‖ ≤ ε ∧
      ‖(pfInterpret w)ᴴ*O*pfInterpret w -
        (HamiltonianEvolution (∑ j, H j) t)ᴴ*O*HamiltonianEvolution (∑ j, H j) t‖ ≤
          2*‖O‖*ε) ∧

  (∀ (n m r : ℕ) (H : Fin m → Operator (2 ^ n)) (t : ℝ)
      (price : Fin m → ℕ) (synth : Fin m → StrangAccessSynthesis n),
    (∀ j, (H j).IsHermitian) → 0 < r →
    (∀ j : Fin m,
        (synthAccessMatrix (synth j)) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
        0 ≤ (synth j).floatError ∧ 0 ≤ (synth j).gateError ∧
        ‖synthAccessMatrix (synth j) -
            HamiltonianEvolution (H j) (t/(2*(r : ℝ)))‖ ≤
          (synth j).floatError + (synth j).gateError ∧
        gateWordDataBits (synth j).word ≤ (synth j).declaredDataBits) →
    let blocks := strangAccessBlocks synth r
    (blocks.map Prod.snd).length = 2*m*r ∧
    (∀ j : Fin m, (blocks.map Prod.snd).count j = 2*r) ∧
    strangBlockMatrix blocks ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
    blockTariffTotal price blocks = 2*r*(∑ j : Fin m, price j) ∧
    blockGateTotal blocks = 2*r*(∑ j : Fin m, (synth j).word.length) ∧
    blockDataBitsTotal blocks ≤ 2*r*(∑ j : Fin m, (synth j).declaredDataBits) ∧
    blockClassicalCostTotal synth r = 2*r*(∑ j : Fin m, (synth j).classicalCost) ∧
    forwardSpaceQubits n = n ∧
    ‖strangBlockMatrix blocks - HamiltonianEvolution (∑ j, H j) t‖ ≤
      strangCompileBudget H synth t r) ∧

  (∀ (n m : ℕ) (H : Fin m → Operator (2 ^ n)) (t ε : ℝ)
      (synth : Fin m → StrangAccessSynthesis n),
    (∀ j, (H j).IsHermitian) → 0 < ε →
    (∀ (r : ℕ), 0 < r → ∀ j : Fin m,
        (synthAccessMatrix (synth j)) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
        0 ≤ (synth j).floatError ∧ 0 ≤ (synth j).gateError ∧
        ‖synthAccessMatrix (synth j) -
            HamiltonianEvolution (H j) (t/(2*(r : ℝ)))‖ ≤
          (synth j).floatError + (synth j).gateError ∧
        gateWordDataBits (synth j).word ≤ (synth j).declaredDataBits) →
    let r := finiteStrangSegments H t (ε/2)
    0 < r ∧
    2*(r : ℝ)*(∑ j : Fin m, ((synth j).floatError + (synth j).gateError)) ≤ ε/2 ∧
    ‖strangBlockMatrix (strangAccessBlocks synth r) -
        HamiltonianEvolution (∑ j, H j) t‖ ≤ ε) ∧

  (∀ (n m r : ℕ) (synth : Fin m → StrangAccessSynthesis n)
      (price : Fin m → ℕ),
    let blocks := strangAccessBlocks synth r
    strangRegBlockMatrix (strangAdjointBlocks synth r) =
      (strangRegBlockMatrix blocks)ᴴ ∧
    blockGateTotal (strangAdjointBlocks synth r) = blockGateTotal blocks ∧
    blockTariffTotal price (strangAdjointBlocks synth r) =
      blockTariffTotal price blocks ∧
    (strangAdjointBlocks synth r).map Prod.snd =
      (strangAccessBlocks synth r).map Prod.snd) ∧

  (∀ (n m r : ℕ) (synth : Fin m → StrangAccessSynthesis n),
    (∀ j : Fin m,
        (synth j).controlledWord.length ≤ (synth j).declaredControlledGates ∧
        gateWordMatrix (synth j).controlledWord =
          regControlEmbed (n := n) (gateWordMatrix (synth j).word)) →
    let cblocks := strangControlledBlocks synth r
    strangRegBlockMatrix (n := n + 1) cblocks =
      regControlEmbed (n := n)
        (strangRegBlockMatrix (strangAccessBlocks synth r)) ∧
    blockGateTotal (n := n + 1) cblocks ≤
      2*r*(∑ j : Fin m, (synth j).declaredControlledGates) ∧
    (∀ j : Fin m, (cblocks.map Prod.snd).count j = 2*r) ∧
    controlledSpaceQubits n = n + 1)
) := by
  intro h
  exact clause59_block4_refutable h.2.2.2.1

end Qatlib.Concepts.TrotterFormula.GeneralOrder

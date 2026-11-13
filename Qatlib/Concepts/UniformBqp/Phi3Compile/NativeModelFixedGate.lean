/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGateDefs
import Qatlib.Foundations.ClockedOracle.StackProgram.ClockedOracleStack

/-!
# Fixed address-gate routing for native machines

`fixedGateWord` replaces basis swaps by address-controlled bit-flip words with exact permutation
and matrix semantics. The resulting window routing and head-flip matrices preserve spectators
and invalid head encodings, and satisfy explicit word-length estimates.

The module also relates native rules to local-machine conditions, verifies deterministic
oracle-answer rows, analyzes a query-free stack-copy program, and classifies common successors
of finite-window transitions. The background is described in [Yao1993].

## Main statements

* `fixedGateWord_matrix`: the address compilation preserves swap-word matrices.
* `binaryCellGateMatrix_eq_gateWord`: cell gates are routed canonical gates.
* `copyProgram_run`: exact copying behavior, termination time, and cost.
* `CommonSucc_classify`: head and tape constraints for a common successor.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.ClockedOracle.StackProgram
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.UniformBqp.Phi3Compile

open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeMachineCompletion
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile
open scoped BigOperators Classical Matrix ComplexConjugate

variable {n : ℕ}

/-- The address-gate word obtained by concatenating a transposition word for each pair in a swap
list. -/
def fixedGateWord (l : List (Qatlib.Foundations.PureStateMath.Reg n × Qatlib.Foundations.PureStateMath.Reg n)) : AddrWord n :=
  l.flatMap (fun p => transpositionWord p.1 p.2)

/-- Evaluating the compiled fixed-gate word agrees with evaluating the original swap word. -/
theorem fixedGateWord_eval : ∀ (l : List (Qatlib.Foundations.PureStateMath.Reg n × Qatlib.Foundations.PureStateMath.Reg n))
    (x : Qatlib.Foundations.PureStateMath.Reg n),
    AddrWord.eval (fixedGateWord l) x = swapWordEval l x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons p l ih =>
    intro x
    have h1 : fixedGateWord (p :: l) = transpositionWord p.1 p.2 ++ fixedGateWord l := rfl
    rw [h1, AddrWord.eval_append, ih (AddrWord.eval (transpositionWord p.1 p.2) x),
      transpositionWord_eval]
    rfl

/-- The address-word matrix of the compiled fixed-gate word equals the original swap-word
matrix. -/
theorem fixedGateWord_matrix (l : List (Qatlib.Foundations.PureStateMath.Reg n × Qatlib.Foundations.PureStateMath.Reg n)) :
    AddrWord.matrix (fixedGateWord l) = swapWordMatrix l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have h1 : fixedGateWord (p :: l) = transpositionWord p.1 p.2 ++ fixedGateWord l := rfl
    rw [h1, AddrWord.matrix_append, ih, transpositionWord_matrix]
    have h2 : swapWordMatrix [p] = injectionFrame (Equiv.swap p.1 p.2) := by
      simp [swapWordMatrix]
    rw [h2, swapWordMatrix]

/-- The register permutation of the compiled fixed-gate word equals the swap-word permutation. -/
theorem fixedGateWord_perm (l : List (Qatlib.Foundations.PureStateMath.Reg n × Qatlib.Foundations.PureStateMath.Reg n)) :
    AddrWord.perm (fixedGateWord l) = swapWordEval l := by
  apply Equiv.ext
  intro x
  rw [AddrWord.perm_apply, fixedGateWord_eval]

/-- The address word transposing any two width-`n` registers has length at most `2*n`. -/
theorem transpositionWord_length_bound (u v : Qatlib.Foundations.PureStateMath.Reg n) :
    (transpositionWord u v).length ≤ 2 * n := by
  by_cases hne : u = v
  · have hz : transpositionWord u v = [] := by
      have hd : diffQubits u v = [] := diffQubits_eq_nil_iff.mpr hne
      rw [transpositionWord, hd]
      rfl
    rw [hz]
    simp
  · have := transpositionWord_length_le u v hne
    omega

/-- Compiling a swap list to address gates produces a word of length at most `l.length * (2*n)`. -/
theorem fixedGateWord_length_bound (l : List (Qatlib.Foundations.PureStateMath.Reg n × Qatlib.Foundations.PureStateMath.Reg n)) :
    (fixedGateWord l).length ≤ l.length * (2 * n) := by
  induction l with
  | nil => simp [fixedGateWord]
  | cons p l ih =>
    have h1 : fixedGateWord (p :: l) = transpositionWord p.1 p.2 ++ fixedGateWord l := rfl
    rw [h1, List.length_append]
    have h2 := transpositionWord_length_bound p.1 p.2
    calc
      (transpositionWord p.1 p.2).length + (fixedGateWord l).length
          ≤ 2 * n + l.length * (2 * n) := Nat.add_le_add h2 ih
      _ = (p :: l).length * (2 * n) := by
        rw [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

/-- The address-gate compilation of the head-bit routing word for window center `i`. -/
def routeGateWord (B : ℕ) (i : WindowCenter B) : AddrWord (headQubits B) :=
  fixedGateWord (cellHeadBitRouteWord i)

/-- The address-gate compilation of the head-flip bit word for a window of radius `B`. -/
def flipGateWord (B : ℕ) : AddrWord (headQubits B) :=
  fixedGateWord (headFlipBitWord B)

/-- The address-gate routing word has length at most `4 * (2 * headQubits B)`. -/
theorem routeGateWord_length_bound (B : ℕ) (i : WindowCenter B) :
    (routeGateWord B i).length ≤ 4 * (2 * headQubits B) := by
  have h1 := fixedGateWord_length_bound (cellHeadBitRouteWord i)
  have h2 : (cellHeadBitRouteWord i).length = 4 := cellHeadBitRouteWord_length i
  rw [show routeGateWord B i = fixedGateWord (cellHeadBitRouteWord i) from rfl]
  rw [h2] at h1
  omega

/-- The address-gate head-flip word has length at most `(2*B + 1) * (2 * headQubits B)`. -/
theorem flipGateWord_length_bound (B : ℕ) :
    (flipGateWord B).length ≤ (2 * B + 1) * (2 * headQubits B) := by
  have h1 := fixedGateWord_length_bound (headFlipBitWord B)
  have h2 : (headFlipBitWord B).length = 2 * B + 1 := headFlipBitWord_length B
  rw [show flipGateWord B = fixedGateWord (headFlipBitWord B) from rfl]
  rw [h2] at h1
  omega

/-- The routing word fixes any head-bit register that does not decode to a valid head value. -/
theorem routeGateWord_illegal (B : ℕ) (i : WindowCenter B) (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B))
    (hx : headFromBits B x = none) :
    AddrWord.eval (routeGateWord B i) x = x := by
  rw [show routeGateWord B i = fixedGateWord (cellHeadBitRouteWord i) from rfl,
    fixedGateWord_eval]
  exact cellHeadBitRoute_illegal i x hx

/-- The head-flip word fixes any head-bit register that does not decode to a valid head value. -/
theorem flipGateWord_illegal (B : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B))
    (hx : headFromBits B x = none) :
    AddrWord.eval (flipGateWord B) x = x := by
  rw [show flipGateWord B = fixedGateWord (headFlipBitWord B) from rfl, fixedGateWord_eval,
    headFlipBitWord_eval, headFlipBits, hx]

/-- The binary-window permutation matrix applying the routing word to the head register and the
identity to all spectator registers. -/
noncomputable def binaryRouteGateMatrix (q a B : ℕ) (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  injectionFrame (Equiv.prodCongr (AddrWord.perm (routeGateWord B i))
    (Equiv.refl (WindowSpectators q a B)))

/-- The binary-window permutation matrix applying the head-flip word to the head register and
the identity to all spectator registers. -/
noncomputable def binaryFlipGateMatrix (q a B : ℕ) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  injectionFrame (Equiv.prodCongr (AddrWord.perm (flipGateWord B))
    (Equiv.refl (WindowSpectators q a B)))

/-- The address-gate routing matrix equals the binary head-routing swap-word matrix. -/
theorem binaryRouteGateMatrix_eq (q a B : ℕ) (i : WindowCenter B) :
    binaryRouteGateMatrix q a B i = binaryHeadRouteWordMatrix q a B i := by
  unfold binaryRouteGateMatrix binaryHeadRouteWordMatrix
  rw [show routeGateWord B i = fixedGateWord (cellHeadBitRouteWord i) from rfl,
    fixedGateWord_perm]

/-- The address-gate head-flip matrix equals the binary window-flip swap-word matrix. -/
theorem binaryFlipGateMatrix_eq (q a B : ℕ) :
    binaryFlipGateMatrix q a B = binaryWindowFlipWordMatrix q a B := by
  unfold binaryFlipGateMatrix binaryWindowFlipWordMatrix
  rw [show flipGateWord B = fixedGateWord (headFlipBitWord B) from rfl, fixedGateWord_perm]

/-- The routing permutation applies the address word to the head bits and preserves the
spectator value. -/
theorem routeGateWindow_spectators (q a B : ℕ) (i : WindowCenter B)
    (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (s : WindowSpectators q a B) :
    (Equiv.prodCongr (AddrWord.perm (routeGateWord B i))
      (Equiv.refl (WindowSpectators q a B))) (x, s)
      = (AddrWord.eval (routeGateWord B i) x, s) := by
  show Prod.map (AddrWord.perm (routeGateWord B i)) (Equiv.refl (WindowSpectators q a B)) (x, s)
      = (AddrWord.eval (routeGateWord B i) x, s)
  rw [Prod.map_apply]
  rfl

/-- The binary routing matrix sends a basis vector to the routed head basis vector with the same
spectator value. -/
theorem binaryRouteGateMatrix_spectators (q a B : ℕ) (i : WindowCenter B)
    (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (s : WindowSpectators q a B) :
    binaryRouteGateMatrix q a B i *ᵥ Pi.single (x, s) 1
      = Pi.single (AddrWord.eval (routeGateWord B i) x, s) 1 := by
  have h1 : (Equiv.prodCongr (AddrWord.perm (routeGateWord B i))
      (Equiv.refl (WindowSpectators q a B))) (x, s)
      = (AddrWord.eval (routeGateWord B i) x, s) :=
    routeGateWindow_spectators q a B i x s
  rw [binaryRouteGateMatrix]
  ext y
  rw [injectionFrame_equiv_mulVec]
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  rw [h1]

/-- The binary routing matrix fixes every basis vector with an invalid head encoding. -/
theorem binaryRouteGateMatrix_illegal (q a B : ℕ) (i : WindowCenter B)
    (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (s : WindowSpectators q a B)
    (hx : headFromBits B x = none) :
    binaryRouteGateMatrix q a B i *ᵥ Pi.single (x, s) 1 = Pi.single (x, s) 1 := by
  have h2 : (Equiv.prodCongr (AddrWord.perm (routeGateWord B i))
      (Equiv.refl (WindowSpectators q a B))) (x, s)
      = (AddrWord.eval (routeGateWord B i) x, s) :=
    routeGateWindow_spectators q a B i x s
  rw [binaryRouteGateMatrix]
  ext y
  rw [injectionFrame_equiv_mulVec]
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  rw [h2, routeGateWord_illegal B i x hx]

/-- The binary head-flip matrix fixes every basis vector with an invalid head encoding. -/
theorem binaryFlipGateMatrix_illegal (q a B : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B))
    (s : WindowSpectators q a B) (hx : headFromBits B x = none) :
    binaryFlipGateMatrix q a B *ᵥ Pi.single (x, s) 1 = Pi.single (x, s) 1 := by
  have h2 : (Equiv.prodCongr (AddrWord.perm (flipGateWord B))
      (Equiv.refl (WindowSpectators q a B))) (x, s)
      = (AddrWord.eval (flipGateWord B) x, s) := by
    show Prod.map (AddrWord.perm (flipGateWord B)) (Equiv.refl (WindowSpectators q a B)) (x, s)
      = (AddrWord.eval (flipGateWord B) x, s)
    rw [Prod.map_apply]
    rfl
  rw [binaryFlipGateMatrix]
  ext y
  rw [injectionFrame_equiv_mulVec]
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  rw [h2, flipGateWord_illegal B x hx]

/-- A binary cell gate is the canonical cell gate conjugated by the address-gate routing matrix. -/
theorem binaryCellGateMatrix_eq_gateWord {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (i : WindowCenter B) :
    R.binaryCellGate i
      = (binaryRouteGateMatrix q a B i).conjTranspose * R.binaryCanonicalGate i
        * binaryRouteGateMatrix q a B i := by
  show (binaryHeadRouteWindowMatrix q a i).conjTranspose * R.binaryCanonicalGate i
      * (binaryHeadRouteWindowMatrix q a i)
    = (binaryRouteGateMatrix q a B i).conjTranspose * R.binaryCanonicalGate i
      * binaryRouteGateMatrix q a B i
  rw [← binaryHeadRouteWordMatrix_eq, binaryRouteGateMatrix_eq]

/-- The binary step-word matrix factors as the head-flip matrix times the product of
cell-operation matrices. -/
theorem binaryStepWordMatrix_eq_gateWord {q a B : ℕ} (R : Rule (Fin q) (Fin a)) :
    R.binaryWordMatrix (windowStepOps B)
      = binaryFlipGateMatrix q a B
        * R.binaryWordMatrix ((windowCenters B).map WindowOp.cell) := by
  rw [binaryStepWordMatrix_eq, binaryFlipGateMatrix_eq]

namespace MatrixList

/-- The product of a matrix list in execution order, with the last listed matrix acting on the
left. -/
noncomputable def prod {ι : Type*} [Fintype ι] [DecidableEq ι] :
    List (Matrix ι ι ℂ) → Matrix ι ι ℂ
  | [] => 1
  | m :: l => prod l * m

end MatrixList

/-- The binary matrix for a list of cell operations is the execution-order product of the routed
canonical cell gates. -/
theorem binaryCellList_eq_gateWord {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (l : List (WindowCenter B)) :
    R.binaryWordMatrix (l.map WindowOp.cell)
      = MatrixList.prod (l.map (fun i =>
          (binaryRouteGateMatrix q a B i).conjTranspose * R.binaryCanonicalGate i
            * binaryRouteGateMatrix q a B i)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons]
    have h1 : R.binaryWordMatrix (WindowOp.cell i :: l.map WindowOp.cell)
        = R.binaryWordMatrix (l.map WindowOp.cell) * (WindowOp.cell i).binaryMatrix R := rfl
    rw [h1]
    have h3 : (WindowOp.cell i).binaryMatrix R = R.binaryCellGate i := rfl
    rw [h3, binaryCellGateMatrix_eq_gateWord]
    simp only [MatrixList.prod]
    rw [ih]

/-- The binary matrix for all step-cell operations is the execution-order product of their
routed canonical gates. -/
theorem binaryStepCells_eq_gateWord {q a B : ℕ} (R : Rule (Fin q) (Fin a)) :
    R.binaryWordMatrix ((windowCenters B).map WindowOp.cell)
      = MatrixList.prod ((windowCenters B).map (fun i =>
          (binaryRouteGateMatrix q a B i).conjTranspose * R.binaryCanonicalGate i
            * binaryRouteGateMatrix q a B i)) :=
  binaryCellList_eq_gateWord R (windowCenters B)

/-- Converting a globally well-formed native rule with zero stay amplitudes yields a local
quantum Turing machine satisfying `LocalQTMFiveConditions`. -/
theorem toLocalQTM_fiveConditions {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (R : Rule Q A) (q0 : Q) (hs : stayFree R)
    (hw : R.GloballyWellformed) :
    LocalQTMFiveConditions (toLocalQTM R q0 hs hw) := by
  unfold LocalQTMFiveConditions
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q a
    exact qtm_norm_of_global R hw q a
  · intro q₁ a₁ q₂ a₂ hne
    exact qtm_sameCell_of_global R hw q₁ q₂ a₁ a₂ hne
  · intro q₁ a₁ q₂ a₂ c d
    apply Finset.sum_eq_zero
    intro q' _
    simp only [toLocalQTM, qtmStep, qtmMoveToMove]
    rw [hs q₂ a₂ q' d]
    simp only [star_zero, mul_zero, eq_self]
  · intro q₁ a₁ q₂ a₂ c d
    apply Finset.sum_eq_zero
    intro q' _
    simp only [toLocalQTM, qtmStep, qtmMoveToMove]
    rw [hs q₁ a₁ q' c]
    simp only [zero_mul, eq_self]
  · intro q₁ a₁ q₂ a₂ c d
    exact qtm_rightLeft_of_global R hw q₁ q₂ a₁ a₂ c d

/-- Global well-formedness implies that the combined right-stay and stay-left cross-amplitude
sum vanishes. -/
theorem qtm_adjacent_combined_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ : A) (c d : A) :
    ∑ q' : Q, (star (qtmStep R q₁ a₁ QtmMove.right q' c) * qtmStep R q₂ a₂ QtmMove.stay q' d
      + star (qtmStep R q₁ a₁ QtmMove.stay q' c) * qtmStep R q₂ a₂ QtmMove.left q' d) = 0 := by
  have hnat := R.local_adjacent_gram_of_global h q₁ q₂ a₁ a₂ c d
  simpa only [qtmStep, qtmMoveToMove] using! hnat

/-- The oracle-slot charge equal to accumulated oracle-query mass times the total access tariff. -/
noncomputable def oracleSlotBill {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {w : ℕ} (O : OracleQTM Q A) (m steps : ℕ) (x : Fin m → A)
    (t : OracleTariff) : ℝ :=
  oracleQueryMass (w := w) O m steps x * t.total

/-- Away from the designated query state, the oracle machine's transition amplitude equals the
underlying machine's transition amplitude. -/
theorem toOracleQTM_nonQuery_eq {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A) (q : Q) (a : A)
    (hq : q ≠ q0) (d : QtmMove) (q' : Q) (b : A) :
    oracleDelta (toOracleQTM M q0 ans) q a d q' b = M.step q a d q' b := by
  simp [oracleDelta, toOracleQTM, hq]

/-- At the designated query state, the oracle answer transition stays in place and writes `ans
a` with amplitude one. -/
theorem toOracleQTM_oracleRow {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A) (a : A) :
    oracleDelta (toOracleQTM M q0 ans) q0 a QtmMove.stay q0 (ans a) = 1 := by
  simp [oracleDelta, toOracleQTM]

/-- The squared norm of a complex zero-one indicator equals the corresponding real zero-one
indicator. -/
private theorem normSq_ite {c : Prop} [Decidable c] :
    ‖(if c then (1 : ℂ) else 0)‖ ^ 2 = (if c then 1 else 0 : ℝ) := by
  by_cases h : c <;> simp [h]

/-- A finite sum supported only at `a` evaluates to the summand at `a`. -/
private theorem sum_delta {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (f : ι → ℝ) : ∑ x, (if x = a then f x else 0) = f a :=
  Fintype.sum_ite_eq' a f

/-- The designated query row is the indicator of staying in the same query state and writing the
oracle answer, and its squared-norm sum is one. -/
theorem toOracleQTM_queryRow {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A) (a : A) :
    (∀ d q' b, oracleDelta (toOracleQTM M q0 ans) q0 a d q' b
        = if d = QtmMove.stay ∧ q' = q0 ∧ b = ans a then 1 else 0) ∧
    (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
        ‖oracleDelta (toOracleQTM M q0 ans) q0 a d q' b‖ ^ 2 = 1) := by
  constructor
  · intro d q' b
    simp [oracleDelta, toOracleQTM]
  · have h1 : (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
        ‖oracleDelta (toOracleQTM M q0 ans) q0 a d q' b‖ ^ 2)
      = ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
        (if d = QtmMove.stay ∧ q' = q0 ∧ b = ans a then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro q' _
      apply Finset.sum_congr rfl
      intro b _
      simp only [oracleDelta, toOracleQTM, Finset.mem_singleton, if_true]
      exact normSq_ite
    rw [h1]
    calc
      (∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
          (if d = QtmMove.stay ∧ q' = q0 ∧ b = ans a then (1 : ℝ) else 0))
          = ∑ q' : Q, ∑ b : A, (if q' = q0 ∧ b = ans a then (1 : ℝ) else 0) := by
            rw [Finset.sum_eq_single QtmMove.stay]
            · simp only [true_and]
            · intro d _ hd
              simp [hd]
            · intro h
              exact (h (Finset.mem_univ _)).elim
      _ = ∑ b : A, (if b = ans a then (1 : ℝ) else 0) := by
            rw [Finset.sum_eq_single q0]
            · simp only [true_and]
            · intro q' _ hq'
              simp [hq']
            · intro h
              exact (h (Finset.mem_univ _)).elim
      _ = 1 := by
            rw [Finset.sum_eq_single (ans a)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro h
              exact (h (Finset.mem_univ _)).elim

/-- The oracle machine constructed by `toOracleQTM` satisfies `OracleExecutionCorrect`. -/
theorem toOracleQTM_oracleExecutionCorrect {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A) :
    OracleExecutionCorrect (toOracleQTM M q0 ans) := by
  refine ⟨?_, ?_⟩
  · intro q a hq d q' b
    have hq' : q ≠ q0 := by
      intro h
      exact hq (by simp [toOracleQTM, h])
    exact toOracleQTM_nonQuery_eq M q0 ans q a hq' d q' b
  · intro q a hq
    have hq' : q = q0 := by
      have hmem : q ∈ ({q0} : Finset Q) := by simpa [toOracleQTM] using! hq
      exact Finset.mem_singleton.mp hmem
    subst q
    obtain ⟨hrow, hmass⟩ := toOracleQTM_queryRow M q0 ans a
    refine ⟨hmass, ?_⟩
    simp [oracleDelta, toOracleQTM]

/-- For an oracle request, the designated query row stays in the query state and writes the
answer determined by the request's record. -/
theorem toOracleQTM_row_of_request {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A)
    (r : OracleRequest Q A) :
    ∀ d q' b, oracleDelta (toOracleQTM M q0 ans) q0 r.record d q' b
      = if d = QtmMove.stay ∧ q' = q0 ∧ b = ans r.record then 1 else 0 := by
  intro d q' b
  simp [oracleDelta, toOracleQTM]

/-- Two requests with equal records produce identical designated-query transition rows. -/
theorem toOracleQTM_record_only {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A)
    (r₁ r₂ : OracleRequest Q A) (hrec : r₁.record = r₂.record) :
    ∀ d q' b, oracleDelta (toOracleQTM M q0 ans) q0 r₁.record d q' b
      = oracleDelta (toOracleQTM M q0 ans) q0 r₂.record d q' b := by
  intro d q' b
  rw [hrec]

/-- Two window configurations with equal scanned symbols produce identical designated-query
answer rows. -/
theorem toOracleQTM_answer_row_of_record {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (q0 : Q) (ans : A → A)
    {t : ℕ} (c₁ c₂ : WindowCfg t Q A) (hrec : c₁.tape c₁.head = c₂.tape c₂.head) :
    ∀ d q' b, oracleDelta (toOracleQTM M q0 ans) q0 (c₁.tape c₁.head) d q' b
      = oracleDelta (toOracleQTM M q0 ans) q0 (c₂.tape c₂.head) d q' b := by
  intro d q' b
  rw [hrec]

/-- The binary-window map applying the routing word to the head bits while preserving both
spectator components. -/
def binaryRouteEval (q a B : ℕ) (i : WindowCenter B) (x : BinaryWindow q a B) :
    BinaryWindow q a B :=
  (AddrWord.eval (routeGateWord B i) x.1, x.2.1, x.2.2)

/-- The binary-window map applying the head-flip word to the head bits while preserving both
spectator components. -/
def binaryFlipEval (q a B : ℕ) (x : BinaryWindow q a B) : BinaryWindow q a B :=
  (AddrWord.eval (flipGateWord B) x.1, x.2.1, x.2.2)

/-- Each routing-matrix entry is one exactly at the output of `binaryRouteEval` and zero
elsewhere. -/
theorem binaryRouteGateMatrix_amp (q a B : ℕ) (i : WindowCenter B)
    (x y : BinaryWindow q a B) :
    binaryRouteGateMatrix q a B i y x = if binaryRouteEval q a B i x = y then 1 else 0 := by
  unfold binaryRouteGateMatrix binaryRouteEval
  rw [injectionFrame]
  have hf : Equiv.prodCongr (AddrWord.perm (routeGateWord B i))
      (Equiv.refl (WindowSpectators q a B)) x
      = (AddrWord.eval (routeGateWord B i) x.1, x.2.1, x.2.2) := by
    show (AddrWord.perm (routeGateWord B i) x.1, x.2) = _
    rw [AddrWord.perm_apply]
  rw [hf]
  by_cases hc : (AddrWord.eval (routeGateWord B i) x.1, x.2.1, x.2.2) = y
  · rw [if_pos hc, if_pos hc.symm]
  · rw [if_neg hc, if_neg (Ne.symm hc)]

/-- Each head-flip matrix entry is one exactly at the output of `binaryFlipEval` and zero
elsewhere. -/
theorem binaryFlipGateMatrix_amp (q a B : ℕ) (x y : BinaryWindow q a B) :
    binaryFlipGateMatrix q a B y x = if binaryFlipEval q a B x = y then 1 else 0 := by
  unfold binaryFlipGateMatrix binaryFlipEval
  rw [injectionFrame]
  have hf : Equiv.prodCongr (AddrWord.perm (flipGateWord B))
      (Equiv.refl (WindowSpectators q a B)) x
      = (AddrWord.eval (flipGateWord B) x.1, x.2.1, x.2.2) := by
    show (AddrWord.perm (flipGateWord B) x.1, x.2) = _
    rw [AddrWord.perm_apply]
  rw [hf]
  by_cases hc : (AddrWord.eval (flipGateWord B) x.1, x.2.1, x.2.2) = y
  · rw [if_pos hc, if_pos hc.symm]
  · rw [if_neg hc, if_neg (Ne.symm hc)]

/-- On a basis input, the routing matrix has Born probability one at the routed output and zero
at every other output. -/
theorem binaryRouteGateMatrix_bornProb (q a B : ℕ) (i : WindowCenter B)
    (x y : BinaryWindow q a B) :
    BornProb (binaryRouteGateMatrix q a B i *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y
      = if binaryRouteEval q a B i x = y then 1 else 0 := by
  have hmul : (binaryRouteGateMatrix q a B i *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y
      = binaryRouteGateMatrix q a B i y x := by
    rw [Matrix.mulVec]
    simp only [dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' x (fun j => binaryRouteGateMatrix q a B i y j)
  unfold BornProb
  rw [hmul, binaryRouteGateMatrix_amp, normSq_ite]

/-- The Born probabilities of the routed image of a basis state sum to one. -/
theorem binaryRouteGateMatrix_mass (q a B : ℕ) (i : WindowCenter B)
    (x : BinaryWindow q a B) :
    ∑ y : BinaryWindow q a B,
      BornProb (binaryRouteGateMatrix q a B i *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y = 1 := by
  have h : ∀ y : BinaryWindow q a B,
      BornProb (binaryRouteGateMatrix q a B i *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y
        = if binaryRouteEval q a B i x = y then 1 else 0 :=
    binaryRouteGateMatrix_bornProb q a B i x
  rw [Finset.sum_eq_single (binaryRouteEval q a B i x)]
  · simp [h]
  · intro y _ hy
    rw [h]
    rw [if_neg (Ne.symm hy)]
  · intro hc
    exact (hc (Finset.mem_univ _)).elim

/-- The binary-window qubit count, regarded as native space usage independently of the step
parameter. -/
def nativeSpace (q a B _t : ℕ) : ℕ := binaryWindowQubits q a B

/-- The defined native space usage is independent of the number of steps. -/
theorem nativeSpace_step_independent (q a B t₁ t₂ : ℕ) :
    nativeSpace q a B t₁ = nativeSpace q a B t₂ := rfl

/-- The length of the head-flip word plus the sum of the routing-word lengths over all window
centers. -/
def binaryStepGateCount (B : ℕ) : ℕ :=
  (flipGateWord B).length + ∑ i ∈ (windowCenters B).toFinset, (routeGateWord B i).length

/-- The defined routing-and-flip count for one step is at most `(2*B + 1) * 10 * headQubits B`. -/
theorem binaryStepGateCount_bound (B : ℕ) :
    binaryStepGateCount B ≤ (2 * B + 1) * 10 * headQubits B := by
  unfold binaryStepGateCount
  have h1 := flipGateWord_length_bound B
  have h2 : ∑ i ∈ (windowCenters B).toFinset, (routeGateWord B i).length
      ≤ (windowCenters B).toFinset.card * (4 * (2 * headQubits B)) := by
    calc
      ∑ i ∈ (windowCenters B).toFinset, (routeGateWord B i).length
          ≤ ∑ _i ∈ (windowCenters B).toFinset, (4 * (2 * headQubits B)) :=
            Finset.sum_le_sum fun i _ => routeGateWord_length_bound B i
      _ = (windowCenters B).toFinset.card * (4 * (2 * headQubits B)) := by
            rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have h3 : (windowCenters B).toFinset.card ≤ 2 * B + 1 := by
    have hcard : (windowCenters B).toFinset.card ≤ (windowCenters B).length :=
      List.toFinset_card_le _
    rw [windowCenters_length] at hcard
    omega
  have h4 : (windowCenters B).toFinset.card * (4 * (2 * headQubits B))
      ≤ (2 * B + 1) * (4 * (2 * headQubits B)) :=
    Nat.mul_le_mul_right (4 * (2 * headQubits B)) h3
  calc
    (flipGateWord B).length + ∑ i ∈ (windowCenters B).toFinset, (routeGateWord B i).length
        ≤ (2 * B + 1) * (2 * headQubits B) + (2 * B + 1) * (4 * (2 * headQubits B)) :=
          Nat.add_le_add h1 (h2.trans h4)
    _ = (2 * B + 1) * 10 * headQubits B := by ring

/-- For `t` repetitions, the defined routing-and-flip count is at most `t * ((2*B + 1) * 10 *
headQubits B)`. -/
theorem binaryPathGateCount_bound (B t : ℕ) :
    t * binaryStepGateCount B ≤ t * ((2 * B + 1) * 10 * headQubits B) :=
  Nat.mul_le_mul_left t (binaryStepGateCount_bound B)

/-- The `t`-step basis amplitude vanishes if the final tape differs from the initial tape at a
position farther than `t` from the initial head. -/
theorem rule_path_tape_lightcone {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (t : ℕ) (c d : Config Q A R.blank) (i : ℤ)
    (hfar : i < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < i)
    (hchange : d.tape i ≠ c.tape i) :
    R.runBasis t c d = 0 :=
  R.runBasis_tape_zero t c d i hfar hchange

/-- The `t`-step basis amplitude vanishes if the final head is farther than `t` from the initial
head. -/
theorem rule_path_head_lightcone {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (t : ℕ) (c d : Config Q A R.blank)
    (hfar : d.head < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < d.head) :
    R.runBasis t c d = 0 :=
  R.runBasis_head_zero t c d hfar

/-- The minimum of the window size `2*B + 1` and the path size `2*t + 1` is bounded by the
window size. -/
theorem pathSpaceCells_bound (B t : ℕ) :
    min (2 * B + 1) (2 * t + 1) ≤ 2 * B + 1 :=
  Nat.min_le_left _ _

/-- If total Born mass is at most one before each of the specified steps, the accumulated
oracle-query mass is at most the number of steps. -/
theorem oracleQueryMass_le_steps_of_unitMass {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {w : ℕ} (O : OracleQTM Q A) (m steps : ℕ)
    (x : Fin m → A)
    (hmass : ∀ j : ℕ, j < steps →
      ∑ c : WindowCfg w Q A,
        BornProb ((oracleWindowStep (t := w) O) ^ j *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := w) O.machine m x)) c ≤ 1) :
    oracleQueryMass (w := w) O m steps x ≤ steps := by
  unfold oracleQueryMass
  calc
    (∑ j ∈ Finset.range steps,
        ∑ c ∈ Finset.univ.filter (fun c => c.state ∈ O.queryStates),
          BornProb ((oracleWindowStep (t := w) O) ^ j *ᵥ
            Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := w) O.machine m x)) c)
        ≤ ∑ _j ∈ Finset.range steps, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' : j < steps := Finset.mem_range.mp hj
          calc
            (∑ c ∈ Finset.univ.filter (fun c => c.state ∈ O.queryStates),
                BornProb ((oracleWindowStep (t := w) O) ^ j *ᵥ
                  Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := w) O.machine m x)) c)
                ≤ ∑ c : WindowCfg w Q A,
                  BornProb ((oracleWindowStep (t := w) O) ^ j *ᵥ
                    Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := w) O.machine m x)) c := by
              rw [Finset.sum_filter]
              exact Finset.sum_le_sum fun c _ => by
                split
                · exact le_rfl
                · exact le_trans (bornProb_nonneg _ _) le_rfl
            _ ≤ 1 := hmass j hj'
    _ = steps := by
          rw [Finset.sum_const, Finset.card_range]
          simp

/-- The stack program that repeatedly reads an input bit, pushes it onto the address stack,
removes it from the input, and halts when the input is empty. -/
def copyProgram : List Qatlib.Foundations.ClockedOracle.StackProgram.Instr :=
  [.peek 3 1 2, .address false 4, .address true 4, .halt, .pop 0]

/-- No instruction of `copyProgram` is an oracle-query instruction. -/
private theorem copyProgram_not_query (pc : ℕ) (slot onFalse onTrue : ℕ) :
    copyProgram[pc]? ≠ some (.query slot onFalse onTrue) := by
  by_cases h : pc < 5
  · interval_cases pc <;> simp [copyProgram]
  · have hnone : copyProgram[pc]? = none := by
      rw [List.getElem?_eq_none_iff]
      simp [copyProgram]
      omega
    rw [hnone]
    simp

/-- Running `copyProgram` for any number of steps preserves the oracle-query log. -/
theorem copyProgram_log (O : ℕ → List Bool → Bool) (k : ℕ)
    (s : Qatlib.Foundations.ClockedOracle.StackProgram.State) :
    (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O k s).log = s.log := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : ∀ (s : Qatlib.Foundations.ClockedOracle.StackProgram.State),
        (Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O s).log = s.log := by
      intro s
      unfold Qatlib.Foundations.ClockedOracle.StackProgram.step
      split
      · rfl
      · cases hp : copyProgram[s.pc]? with
        | none => rfl
        | some i =>
          cases i with
          | peek e f r => rfl
          | pop next => rfl
          | emit value next => rfl
          | address value next => rfl
          | query slot onFalse onTrue =>
            exact (copyProgram_not_query s.pc slot onFalse onTrue hp).elim
          | halt => rfl
    rw [Qatlib.Foundations.ClockedOracle.StackProgram.run_succ_last, hstep, ih]

/-- At program counter zero with empty input and an active state, one copy-program step advances
to counter three and increments ticks and cost by one. -/
theorem copyProgram_step_empty (O : ℕ → List Bool → Bool)
    (s : Qatlib.Foundations.ClockedOracle.StackProgram.State)
    (hpc : s.pc = 0) (hin : s.input = []) (hrun : s.halted = false) :
    Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O s =
      { s with pc := 3, ticks := s.ticks + 1, cost := s.cost + 1 } := by
  have hp : copyProgram[0]? = some (.peek 3 1 2) := by rfl
  unfold Qatlib.Foundations.ClockedOracle.StackProgram.step
  split
  · simp_all
  · simp [hp, hpc, hin]

/-- At program counter zero with a leading input bit and an active state, one step branches to
counter two for true and counter one for false, incrementing ticks and cost by one. -/
theorem copyProgram_step_bit (O : ℕ → List Bool → Bool)
    (s : Qatlib.Foundations.ClockedOracle.StackProgram.State) (b : Bool) (rest : List Bool)
    (hpc : s.pc = 0) (hin : s.input = b :: rest) (hrun : s.halted = false) :
    Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O s =
      { s with pc := (if b then 2 else 1), ticks := s.ticks + 1, cost := s.cost + 1 } := by
  have hp : copyProgram[0]? = some (.peek 3 1 2) := by rfl
  unfold Qatlib.Foundations.ClockedOracle.StackProgram.step
  split
  · simp_all
  · simp [hp, hpc, hin]
    cases b <;> rfl

/-- One three-step copy round removes the leading input bit, pushes it onto the address stack,
returns to counter zero, and increments ticks and cost by three. -/
theorem copyProgram_round (b : Bool) (rest : List Bool) (O : ℕ → List Bool → Bool)
    (s : Qatlib.Foundations.ClockedOracle.StackProgram.State) (acc : List Bool)
    (hpc : s.pc = 0) (hin : s.input = b :: rest) (hacc : s.address = acc)
    (hrun : s.halted = false) :
    Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O 3 s
      = { s with pc := 0, input := rest, address := b :: acc, ticks := s.ticks + 3, cost := s.cost + 3 } := by
  have h1 : Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O 3 s
      = Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O
          (Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O
            (Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O s)) := by
    rw [Qatlib.Foundations.ClockedOracle.StackProgram.run_succ_last,
      Qatlib.Foundations.ClockedOracle.StackProgram.run_succ_last,
      Qatlib.Foundations.ClockedOracle.StackProgram.run_succ_last]
    rfl
  rw [h1]
  cases b with
  | false =>
      simp [Qatlib.Foundations.ClockedOracle.StackProgram.step, copyProgram, hpc, hin, hacc, hrun]
  | true =>
      simp [Qatlib.Foundations.ClockedOracle.StackProgram.step, copyProgram, hpc, hin, hacc, hrun]

/-- Starting at counter zero in an active state, the copy program halts after `3 * xs.length +
2` steps with empty input and address `xs.reverse ++ acc`, increasing ticks and cost by that
amount. -/
theorem copyProgram_run (xs : List Bool) (O : ℕ → List Bool → Bool)
    (s : Qatlib.Foundations.ClockedOracle.StackProgram.State) (acc : List Bool)
    (hpc : s.pc = 0) (hin : s.input = xs) (hacc : s.address = acc)
    (hrun : s.halted = false) :
    Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O (3 * xs.length + 2) s
      = { s with pc := 3, input := ([] : List Bool), address := xs.reverse ++ acc, halted := true, ticks := s.ticks + 3 * xs.length + 2, cost := s.cost + 3 * xs.length + 2 } := by
  induction xs generalizing s acc with
  | nil =>
      simp only [List.length_nil]
      have hsplit : Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O 2 s
          = Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O
              (Qatlib.Foundations.ClockedOracle.StackProgram.step copyProgram O s) := by
        rw [Qatlib.Foundations.ClockedOracle.StackProgram.run_succ_last,
          Qatlib.Foundations.ClockedOracle.StackProgram.run_succ_last]
        rfl
      rw [hsplit]
      simp [Qatlib.Foundations.ClockedOracle.StackProgram.step, copyProgram, hpc, hin, hacc, hrun]
  | cons b xs ih =>
      have hrun3 : (3 * (b :: xs).length + 2) = 3 + (3 * xs.length + 2) := by
        simp [List.length_cons]
        omega
      have hsplit : Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O
            (3 * (b :: xs).length + 2) s
          = Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O (3 * xs.length + 2)
              (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O 3 s) := by
        rw [hrun3, Qatlib.Foundations.ClockedOracle.StackProgram.run_add]
      rw [hsplit]
      have hround := copyProgram_round b xs O s acc hpc (by rw [hin]) (by rw [hacc]) hrun
      rw [hround]
      have hih :=
          ih { s with pc := 0, input := xs, address := b :: acc, ticks := s.ticks + 3, cost := s.cost + 3 } (b :: acc) rfl rfl rfl (by simp [hrun])
      rw [hih]
      simp only [Qatlib.Foundations.ClockedOracle.StackProgram.State.mk.injEq]
      simp [List.reverse_cons, List.append_assoc]
      omega

/-- The condition that a finite-window successor has the moved head, the specified new state,
and the original tape with the scanned cell overwritten by `b`. -/
abbrev StepPred {t : ℕ} {Q A : Type*} (c c' : WindowCfg t Q A)
    (d : QtmMove) (q' : Q) (b : A) : Prop :=
  moveCell d c.head = some c'.head ∧ c'.state = q' ∧
    (∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j)

/-- A raw finite-window transition entry is the sum of local transition amplitudes over move,
state, and symbol choices satisfying `StepPred`. -/
theorem rawWindowStep_expand {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {t : ℕ} (δ : Q → A → QtmMove → Q → A → ℂ)
    (c c' : WindowCfg t Q A) :
    rawWindowStep δ c' c =
      ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
        if StepPred c c' d q' b then δ c.state (c.tape c.head) d q' b else 0 := by
  simp only [rawWindowStep, Matrix.of_apply, StepPred]

/-- For fixed source, move, new state, and written symbol, a successor satisfying `StepPred` is
unique. -/
theorem StepPred_unique {t : ℕ} {Q A : Type*} {c c₁ c₂ : WindowCfg t Q A}
    {d : QtmMove} {q' : Q} {b : A}
    (h₁ : StepPred c c₁ d q' b) (h₂ : StepPred c c₂ d q' b) : c₁ = c₂ := by
  obtain ⟨hm₁, hs₁, ht₁⟩ := h₁
  obtain ⟨hm₂, hs₂, ht₂⟩ := h₂
  have hh : c₁.head = c₂.head := Option.some.inj (hm₁.symm.trans hm₂)
  have hst : c₁.state = c₂.state := hs₁.trans hs₂.symm
  have htp : ∀ j : Fin (2 * t + 1), c₁.tape j = c₂.tape j := by
    intro j
    have h1 := ht₁ j
    have h2 := ht₂ j
    by_cases hj : j = c.head
    · subst hj
      simp at h1 h2
      exact h1.trans h2.symm
    · have h1' : c₁.tape j = c.tape j := by simpa [hj] using! h1
      have h2' : c₂.tape j = c.tape j := by simpa [hj] using! h2
      exact h1'.trans h2'.symm
  obtain ⟨h₁, s₁, t₁⟩ := c₁
  obtain ⟨h₂, s₂, t₂⟩ := c₂
  simp only [WindowCfg.mk.injEq]
  exact ⟨hh, hst, funext htp⟩

/-- The moved head position when the move remains in the window, with the original head as the
fallback for an invalid move. -/
def headOf {t : ℕ} {Q A : Type*} (c : WindowCfg t Q A) (d : QtmMove) : Fin (2 * t + 1) :=
  (moveCell d c.head).getD c.head

/-- The candidate successor with head `headOf c d`, state `q'`, and symbol `b` written at the
original head. -/
def succOf {t : ℕ} {Q A : Type*} (c : WindowCfg t Q A) (d : QtmMove) (q' : Q) (b : A) :
    WindowCfg t Q A :=
  ⟨headOf c d, q', fun j => if j = c.head then b else c.tape j⟩

/-- When the head move remains in the window, `succOf` satisfies the corresponding step
predicate. -/
theorem StepPred_succOf {t : ℕ} {Q A : Type*} (c : WindowCfg t Q A) (d : QtmMove) (q' : Q) (b : A)
    (hne : moveCell d c.head ≠ none) : StepPred c (succOf c d q' b) d q' b := by
  refine ⟨?_, rfl, ?_⟩
  · cases hm : moveCell d c.head with
    | none => exact absurd hm hne
    | some h => simp [succOf, headOf, hm]
  · intro j
    rfl

/-- A successor satisfying `StepPred` has head `headOf c d`. -/
theorem succOf_head {t : ℕ} {Q A : Type*} {c c' : WindowCfg t Q A} {d : QtmMove} {q' : Q} {b : A}
    (h : StepPred c c' d q' b) : c'.head = headOf c d := by
  obtain ⟨hm, hst, ht⟩ := h
  have hne : moveCell d c.head ≠ none := by
    intro hn
    rw [hn] at hm
    simp at hm
  cases hm1 : moveCell d c.head with
  | none => exact absurd hm1 hne
  | some hh =>
    have hch : c'.head = hh := Option.some.inj (hm.symm.trans hm1)
    have heq : headOf c d = hh := by simp [headOf, hm1]
    simpa [heq] using! hch

/-- A successor satisfying `StepPred` has the specified new state. -/
theorem succOf_state {t : ℕ} {Q A : Type*} {c c' : WindowCfg t Q A} {d : QtmMove} {q' : Q} {b : A}
    (h : StepPred c c' d q' b) : c'.state = q' := h.2.1

/-- A successor satisfying `StepPred` has symbol `b` at the original head and the original tape
at every other cell. -/
theorem succOf_tape {t : ℕ} {Q A : Type*} {c c' : WindowCfg t Q A} {d : QtmMove} {q' : Q} {b : A}
    (h : StepPred c c' d q' b) (j : Fin (2 * t + 1)) :
    c'.tape j = if j = c.head then b else c.tape j := h.2.2 j

/-- If `P` has at most one satisfying element and that element also satisfies `Q`, the sum of
products of the two constant-weight indicators is `A * B`. -/
private lemma sum_prod_indicator_of_mem {α : Type*} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (A B : ℂ)
    (huniq : ∀ x y, P x → P y → x = y) (x₀ : α) (hx₀ : P x₀ ∧ Q x₀) :
    (∑ x, (if P x then A else 0) * (if Q x then B else 0)) = A * B := by
  have hsub : (∑ x, (if P x then A else 0) * (if Q x then B else 0))
      = ∑ x ∈ (Finset.univ.filter (fun x => P x ∧ Q x)),
          (if P x then A else 0) * (if Q x then B else 0) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun x hx hxnot => ?_)
    by_cases hP : P x
    · have hQ : ¬ Q x := by
        intro hQ
        exact hxnot (Finset.mem_filter.mpr ⟨hx, ⟨hP, hQ⟩⟩)
      simp [hP, hQ]
    · simp [hP]
  have hs : Finset.univ.filter (fun x => P x ∧ Q x) = {x₀} := by
    ext y
    simp only [Finset.mem_singleton, Finset.mem_filter]
    constructor
    · intro hy
      exact (huniq x₀ y hx₀.1 hy.2.1).symm
    · intro hy
      subst hy
      exact ⟨Finset.mem_univ _, hx₀⟩
  rw [hsub, hs, Finset.sum_singleton]
  simp [hx₀.1, hx₀.2]

/-- If no element satisfies both predicates, the sum of the products of their weighted
indicators is zero. -/
private lemma sum_prod_indicator_of_not {α : Type*} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (A B : ℂ)
    (hne : ¬ ∃ x, P x ∧ Q x) :
    (∑ x, (if P x then A else 0) * (if Q x then B else 0)) = 0 := by
  have hsub : (∑ x, (if P x then A else 0) * (if Q x then B else 0))
      = ∑ x ∈ (Finset.univ.filter (fun x => P x ∧ Q x)),
          (if P x then A else 0) * (if Q x then B else 0) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun x hx hxnot => ?_)
    by_cases hP : P x
    · have hQ : ¬ Q x := by
        intro hQ
        exact hxnot (Finset.mem_filter.mpr ⟨hx, ⟨hP, hQ⟩⟩)
      simp [hP, hQ]
    · simp [hP]
  have hs : Finset.univ.filter (fun x => P x ∧ Q x) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro y hy
    exact hne ⟨y, (Finset.mem_filter.mp hy).2⟩
  rw [hsub, hs, Finset.sum_empty]

/-- A sum over common finite-window successors reduces to the candidate `succOf`, provided the
first move is valid and that candidate satisfies the second step predicate. -/
theorem sum_over_common {t : ℕ} {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (c c'' : WindowCfg t Q A)
    (d : QtmMove) (q : Q) (b : A) (d' : QtmMove) (q' : Q) (b' : A) (K : ℂ) :
    (∑ c' : WindowCfg t Q A,
      (if StepPred c c' d q b then K else 0) *
      (if StepPred c'' c' d' q' b' then 1 else 0))
    = (if (moveCell d c.head ≠ none) ∧ StepPred c'' (succOf c d q b) d' q' b' then K else 0) := by
  by_cases hcond : (moveCell d c.head ≠ none) ∧ StepPred c'' (succOf c d q b) d' q' b'
  · have hmain := sum_prod_indicator_of_mem (P := fun c' => StepPred c c' d q b)
      (Q := fun c' => StepPred c'' c' d' q' b') K 1
      (fun x y hx hy => StepPred_unique hx hy) (succOf c d q b)
      ⟨StepPred_succOf c d q b hcond.1, hcond.2⟩
    rw [hmain]
    simp [hcond]
  · have hne' : ¬ ∃ c' : WindowCfg t Q A, StepPred c c' d q b ∧ StepPred c'' c' d' q' b' := by
      rintro ⟨c', hc'⟩
      have hne0 : moveCell d c.head ≠ none := by
        intro hn
        obtain ⟨hm, _, _⟩ := hc'.1
        rw [hn] at hm
        simp at hm
      have hq : q = q' := (succOf_state hc'.1).symm.trans hc'.2.2.1
      have hh : (succOf c d q b).head = c'.head := (succOf_head hc'.1).symm
      refine hcond ⟨hne0, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hh]
        exact hc'.2.1
      · have hst : (succOf c d q b).state = q := rfl
        rw [hst]
        exact hq
      · intro j
        have ht : (succOf c d q b).tape j = c'.tape j := (succOf_tape hc'.1 j).symm
        rw [ht]
        exact hc'.2.2.2 j
    have hmain := sum_prod_indicator_of_not (P := fun c' => StepPred c c' d q b)
      (Q := fun c' => StepPred c'' c' d' q' b') K 1 hne'
    rw [hmain]
    simp [hcond]

/-- The inner product of the two raw finite-window transition columns indexed by `c` and `c''`. -/
noncomputable def colGram {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    {t : ℕ} (δ : Q → A → QtmMove → Q → A → ℂ) (c c'' : WindowCfg t Q A) : ℂ :=
  ∑ c' : WindowCfg t Q A, star (rawWindowStep δ c' c) * (rawWindowStep δ c' c'')

/-- A valid finite-window head move is either a stay, a one-cell left move from a positive
position, or a one-cell right move within the window bound. -/
theorem moveCell_cases {t : ℕ} (d : QtmMove) (h h' : Fin (2 * t + 1))
    (hm : moveCell d h = some h') :
    (d = QtmMove.stay ∧ h' = h) ∨
    (d = QtmMove.left ∧ 0 < h.val ∧ h'.val + 1 = h.val) ∨
    (d = QtmMove.right ∧ h.val + 1 = h'.val ∧ h'.val ≤ 2 * t) := by
  cases d with
  | left =>
    by_cases h0 : h.val = 0
    · have hmv : moveCell QtmMove.left h = none := by simp [moveCell, h0]
      rw [hmv] at hm
      exact absurd hm (by simp)
    · have hmv : moveCell QtmMove.left h =
          some ⟨h.val - 1, by have := h.isLt; omega⟩ := by simp [moveCell, h0]
      rw [hmv] at hm
      simp only [Option.some.injEq] at hm
      have hv : h'.val = h.val - 1 := by
        have hc := congrArg (fun f : Fin (2 * t + 1) => (f : ℕ)) hm
        simpa using! hc.symm
      exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
  | stay =>
    have hmv : moveCell QtmMove.stay h = some h := by simp [moveCell]
    rw [hmv] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact Or.inl ⟨rfl, rfl⟩
  | right =>
    by_cases h0 : h.val = 2 * t
    · have hmv : moveCell QtmMove.right h = none := by simp [moveCell, h0]
      rw [hmv] at hm
      exact absurd hm (by simp)
    · have hmv : moveCell QtmMove.right h =
          some ⟨h.val + 1, by have := h.isLt; omega⟩ := by simp [moveCell, h0]
      rw [hmv] at hm
      simp only [Option.some.injEq] at hm
      have hv : h'.val = h.val + 1 := by
        have hc := congrArg (fun f : Fin (2 * t + 1) => (f : ℕ)) hm
        simpa using! hc.symm
      exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)

/-- A valid finite-window head move changes the numeric head position by zero, minus one, or
plus one according to its direction. -/
theorem moveCell_val_of_some {t : ℕ} (d : QtmMove) (h h' : Fin (2 * t + 1))
    (hm : moveCell d h = some h') :
    (d = QtmMove.stay ∧ h'.val = h.val) ∨
    (d = QtmMove.left ∧ h'.val + 1 = h.val) ∨
    (d = QtmMove.right ∧ h.val + 1 = h'.val) := by
  rcases moveCell_cases d h h' hm with hstay | hleft | hright
  · exact Or.inl ⟨hstay.1, by rw [hstay.2]⟩
  · exact Or.inr (Or.inl ⟨hleft.1, hleft.2.2⟩)
  · exact Or.inr (Or.inr ⟨hright.1, hright.2.1⟩)

/-- The integer displacement of a head move: minus one for left, zero for stay, and one for
right. -/
def qtmOffset : QtmMove → ℤ
  | QtmMove.left => -1
  | QtmMove.stay => 0
  | QtmMove.right => 1

/-- If two valid head moves have a common destination, the second source head equals the first
source head plus the first displacement minus the second. -/
theorem head_offset {t : ℕ} {Q A : Type} (c c'' : WindowCfg t Q A)
    (d : QtmMove) (d' : QtmMove)
    (hne : moveCell d c.head ≠ none)
    (hhead : moveCell d' c''.head = some (headOf c d)) :
    (c''.head.val : ℤ) = (c.head.val : ℤ) + qtmOffset d - qtmOffset d' := by
  have hm1 : moveCell d c.head = some (headOf c d) := by
    cases hh : moveCell d c.head with
    | none => exact absurd hh hne
    | some x =>
      have : headOf c d = x := by simp [headOf, hh]
      rw [this]
  rcases moveCell_val_of_some d c.head (headOf c d) hm1 with hA | hA | hA
  · rcases moveCell_val_of_some d' c''.head (headOf c d) hhead with hB | hB | hB
    · have hAi : ((headOf c d).val : ℤ) = (c.head.val : ℤ) := by exact_mod_cast hA.2
      have hBi : ((headOf c d).val : ℤ) = (c''.head.val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
    · have hAi : ((headOf c d).val : ℤ) = (c.head.val : ℤ) := by exact_mod_cast hA.2
      have hBi : ((headOf c d).val : ℤ) + 1 = (c''.head.val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
    · have hAi : ((headOf c d).val : ℤ) = (c.head.val : ℤ) := by exact_mod_cast hA.2
      have hBi : (c''.head.val : ℤ) + 1 = ((headOf c d).val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
  · rcases moveCell_val_of_some d' c''.head (headOf c d) hhead with hB | hB | hB
    · have hAi : ((headOf c d).val : ℤ) + 1 = (c.head.val : ℤ) := by exact_mod_cast hA.2
      have hBi : ((headOf c d).val : ℤ) = (c''.head.val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
    · have hAi : ((headOf c d).val : ℤ) + 1 = (c.head.val : ℤ) := by exact_mod_cast hA.2
      have hBi : ((headOf c d).val : ℤ) + 1 = (c''.head.val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
    · have hAi : ((headOf c d).val : ℤ) + 1 = (c.head.val : ℤ) := by exact_mod_cast hA.2
      have hBi : (c''.head.val : ℤ) + 1 = ((headOf c d).val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
  · rcases moveCell_val_of_some d' c''.head (headOf c d) hhead with hB | hB | hB
    · have hAi : (c.head.val : ℤ) + 1 = ((headOf c d).val : ℤ) := by exact_mod_cast hA.2
      have hBi : ((headOf c d).val : ℤ) = (c''.head.val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
    · have hAi : (c.head.val : ℤ) + 1 = ((headOf c d).val : ℤ) := by exact_mod_cast hA.2
      have hBi : ((headOf c d).val : ℤ) + 1 = (c''.head.val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega
    · have hAi : (c.head.val : ℤ) + 1 = ((headOf c d).val : ℤ) := by exact_mod_cast hA.2
      have hBi : (c''.head.val : ℤ) + 1 = ((headOf c d).val : ℤ) := by exact_mod_cast hB.2
      simp [qtmOffset, hA.1, hB.1]
      omega

/-- Equality of two tapes after single-cell writes splits into equal-head and distinct-head
cases, specifying the written symbols and agreement at all untouched cells. -/
theorem tape_eq_cases {t : ℕ} {Q A : Type*} (c c'' : WindowCfg t Q A) (b : A) (b' : A)
    (h : ∀ j : Fin (2 * t + 1),
      (if j = c.head then b else c.tape j) = if j = c''.head then b' else c''.tape j) :
    (c.head = c''.head ∧ b = b' ∧ (∀ j, j ≠ c.head → c.tape j = c''.tape j)) ∨
    (c.head ≠ c''.head ∧ b = c''.tape c.head ∧ b' = c.tape c''.head ∧
      (∀ j, j ≠ c.head → j ≠ c''.head → c.tape j = c''.tape j)) := by
  by_cases hh : c.head = c''.head
  · refine Or.inl ⟨hh, ?_, ?_⟩
    · have h1 := h c.head
      simpa [hh] using! h1
    · intro j hj
      have hj2 : j ≠ c''.head := by rw [← hh]; exact hj
      have h1 := h j
      simpa [hh, hj, hj2] using! h1
  · refine Or.inr ⟨hh, ?_, ?_, ?_⟩
    · have h1 := h c.head
      simpa [hh] using! h1
    · have h1 := h c''.head
      have h2 : c.tape c''.head = b' := by
        have h3 := h1
        simp only [if_neg (Ne.symm hh)] at h3
        exact h3
      exact h2.symm
    · intro j hj hj2
      have h1 := h j
      simpa [hj, hj2] using! h1

/-- The condition that two local move-state-symbol choices give a common valid successor, with
equal destination heads, equal new states, and equal written tapes. -/
def CommonSucc {t : ℕ} {Q A : Type} (c c'' : WindowCfg t Q A)
    (d : QtmMove) (q : Q) (b : A) (d' : QtmMove) (q' : Q) (b' : A) : Prop :=
  (moveCell d c.head ≠ none) ∧
  (moveCell d' c''.head = some (headOf c d)) ∧
  q' = q ∧
  (∀ j : Fin (2 * t + 1),
    (if j = c.head then b else c.tape j) = if j = c''.head then b' else c''.tape j)

/-- Two choices satisfying `CommonSucc` have the same new state, satisfy the equal-head or
distinct-head tape compatibility conditions, and have source-head difference determined by
their move displacements. -/
theorem CommonSucc_classify {t : ℕ} {Q A : Type} (c c'' : WindowCfg t Q A)
    (d : QtmMove) (q : Q) (b : A) (d' : QtmMove) (q' : Q) (b' : A)
    (h : CommonSucc c c'' d q b d' q' b') :
    q' = q ∧
    ((c.head = c''.head ∧ b = b' ∧ (∀ j, j ≠ c.head → c.tape j = c''.tape j)) ∨
     (c.head ≠ c''.head ∧ b = c''.tape c.head ∧ b' = c.tape c''.head ∧
       (∀ j, j ≠ c.head → j ≠ c''.head → c.tape j = c''.tape j))) ∧
    (c''.head.val : ℤ) = (c.head.val : ℤ) + qtmOffset d - qtmOffset d' := by
  obtain ⟨hne, hhead, hq, htp⟩ := h
  refine ⟨hq, tape_eq_cases c c'' b b' htp, head_offset c c'' d d' hne hhead⟩

end Qatlib.Concepts.UniformBqp.Phi3Compile

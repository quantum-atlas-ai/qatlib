/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.PrepareSelectCount
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-!
# Binary register realization of the Taylor PREPARE/SELECT words

This module transports the composed words of `PrepareSelectCount` from abstract
`Fin L` index digits to physical Boolean registers. A digit is embedded in a
`w`-wire register by `binaryDigit`, using the certified register/`Fin (2 ^ w)`
bridge `bitVecEquiv`. The embedding is injective for every `L ≤ 2 ^ w`, and is
an equivalence when `L = 2 ^ w`. The index registers therefore have a concrete
binary encoding, with `K * w` wires, and at `w = ⌈log₂ L⌉` the total ancilla
ledger is exactly `ancillaBits K L`.

For an arbitrary `L ≤ 2 ^ w`, a matrix on the abstract basis is extended to the
larger binary basis by the identity on basis states outside the image of the
encoding. The extension is block diagonal after the canonical range/complement
split, preserves multiplication, identity, conjugate transpose, and unitarity,
and is applied instruction by instruction to the abstract composed words. Hence
all gate and query counts below are counts of the transported words themselves.
The denotation theorem records that the binary word is the same serial product,
padded by the identity; it is not a new resource formula.

The extension also gives the first semantic ring needed for the later
`B† · SELECT · B` construction: the transported PREPARE and SELECT denotations
are exactly the padded abstract denotations. Spectral compression, rotation-angle
amplitudes, elementary-gate synthesis, and oracle billing of the term unitaries
remain outside this module.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CostModels.CountBridge
open Qatlib.Concepts.CostModels.UnitAlgebra
open Qatlib.Papers.TruncTaylor14.ResourceCount
open Qatlib.Papers.TruncTaylor14.PrepareSelectCount

open scoped Matrix
open scoped Classical

namespace Qatlib.Papers.TruncTaylor14.PrepareSelectBinary

noncomputable section

/-! ### Identity-on-padding matrix extension -/

section Padding

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The canonical split of a finite basis into the range of an injection and its
complement. The first summand is identified with the domain of the injection. -/
def extensionEquiv (e : I → J) (he : Function.Injective e) :
    I ⊕ {x : J // x ∉ Set.range e} ≃ J :=
  (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

/-- Extend a matrix along an injection, acting by the identity on basis states
outside its range. This is the physical padding of an abstract register. -/
def extendMatrix (e : I → J) (he : Function.Injective e) (U : Matrix I I ℂ) :
    Matrix J J ℂ :=
  Matrix.reindex (extensionEquiv e he) (extensionEquiv e he)
    (Matrix.fromBlocks U 0 0 1)

omit [DecidableEq I] [Fintype J] in

/-- On the encoded basis, the padded matrix has exactly the original entries. -/
theorem extendMatrix_image (e : I → J) (he : Function.Injective e)
    (U : Matrix I I ℂ) (i j : I) :
    extendMatrix e he U (e i) (e j) = U i j := by
  classical
  have hi : (Equiv.Set.sumCompl (Set.range e)).symm (e i) =
      Sum.inl (⟨e i, ⟨i, rfl⟩⟩ : Set.range e) :=
    Equiv.Set.sumCompl_symm_apply_of_mem (s := Set.range e)
      (show e i ∈ Set.range e from ⟨i, rfl⟩)
  have hj : (Equiv.Set.sumCompl (Set.range e)).symm (e j) =
      Sum.inl (⟨e j, ⟨j, rfl⟩⟩ : Set.range e) :=
    Equiv.Set.sumCompl_symm_apply_of_mem (s := Set.range e)
      (show e j ∈ Set.range e from ⟨j, rfl⟩)
  simp [extendMatrix, extensionEquiv, reidx_apply, hi, hj]

omit [DecidableEq I] in

/-- Padding preserves matrix products. -/
theorem extendMatrix_mul (e : I → J) (he : Function.Injective e)
    (U V : Matrix I I ℂ) :
    extendMatrix e he (U * V) = extendMatrix e he U * extendMatrix e he V := by
  classical
  simp only [extendMatrix]
  rw [← reidxMul, Matrix.fromBlocks_multiply]
  simp

omit [Fintype J] in

/-- Padding preserves the identity matrix. -/
theorem extendMatrix_one (e : I → J) (he : Function.Injective e) :
    extendMatrix e he (1 : Matrix I I ℂ) = 1 := by
  classical
  simp [extendMatrix]

omit [DecidableEq I] [Fintype J] in

/-- Padding commutes with conjugate transposition. -/
theorem extendMatrix_conjTranspose (e : I → J) (he : Function.Injective e)
    (U : Matrix I I ℂ) :
    extendMatrix e he Uᴴ = (extendMatrix e he U)ᴴ := by
  classical
  simp [extendMatrix, Matrix.fromBlocks_conjTranspose]

/-- A padded unitary is unitary on the full binary basis. -/
theorem extendMatrix_unitary (e : I → J) (he : Function.Injective e)
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    extendMatrix e he U ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU ⊢
  rw [← extendMatrix_conjTranspose, ← extendMatrix_mul, hU, extendMatrix_one]

/-- Pad every explicit gate of a query word; oracle queries remain queries. -/
def extendStep (e : I → J) (he : Function.Injective e) : Step I → Step J
  | Step.gate U => Step.gate (extendMatrix e he U)
  | Step.query => Step.query

/-- The instruction-wise binary transport of a composed query word. -/
def extendWord (e : I → J) (he : Function.Injective e) (C : Circuit I) : Circuit J :=
  C.map (extendStep e he)

omit [DecidableEq I] [Fintype J] in

/-- Transport preserves the measured explicit-gate count. -/
theorem extendWord_gateCount (e : I → J) (he : Function.Injective e) (C : Circuit I) :
    GateCount (extendWord e he C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U =>
          change GateCount (Step.gate (extendMatrix e he U) :: extendWord e he C) =
            GateCount (Step.gate U :: C)
          rw [gateCount_gate, gateCount_gate, ih]
      | query =>
          change GateCount (Step.query :: extendWord e he C) = GateCount (Step.query :: C)
          rw [gateCount_query, gateCount_query, ih]

omit [DecidableEq I] [Fintype J] in

/-- Transport preserves the measured oracle-query count. -/
theorem extendWord_queryCount (e : I → J) (he : Function.Injective e) (C : Circuit I) :
    QueryCount (extendWord e he C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U =>
          change QueryCount (Step.gate (extendMatrix e he U) :: extendWord e he C) =
            QueryCount (Step.gate U :: C)
          rw [queryCount_gate, queryCount_gate, ih]
      | query =>
          change QueryCount (Step.query :: extendWord e he C) = QueryCount (Step.query :: C)
          rw [queryCount_query, queryCount_query, ih]

/-- Transport preserves unitarity of every composed word. -/
theorem extendWord_unitary (e : I → J) (he : Function.Injective e) (C : Circuit I)
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (extendWord e he C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
      cases s with
      | gate U =>
          rw [extendWord, List.map_cons]
          exact (isUnitaryCircuit_gate _ _).mpr
            ⟨extendMatrix_unitary e he ((isUnitaryCircuit_gate _ _).mp hC).1,
              ih ((isUnitaryCircuit_gate _ _).mp hC).2⟩
      | query =>
          rw [extendWord, List.map_cons]
          exact (isUnitaryCircuit_query _).mpr
            (ih ((isUnitaryCircuit_query _).mp hC))

/-- The denotation of the transported word is the padded denotation of the
original word, including the same right-to-left serial product order. -/
theorem extendWord_denote (e : I → J) (he : Function.Injective e)
    (oracle : Matrix I I ℂ) (C : Circuit I) :
    Denote (extendMatrix e he oracle) (extendWord e he C) =
      extendMatrix e he (Denote oracle C) := by
  induction C with
  | nil =>
      rw [extendWord, List.map_nil, denote_nil, denote_nil, extendMatrix_one]
  | cons s C ih =>
      cases s with
      | gate U =>
          change Denote (extendMatrix e he oracle)
              (Step.gate (extendMatrix e he U) :: extendWord e he C) =
            extendMatrix e he (Denote oracle (Step.gate U :: C))
          rw [denote_gate, denote_gate, ih, extendMatrix_mul]
      | query =>
          change Denote (extendMatrix e he oracle)
              (Step.query :: extendWord e he C) =
            extendMatrix e he (Denote oracle (Step.query :: C))
          rw [denote_query, denote_query, ih, extendMatrix_mul]

end Padding

/-! ### Binary index digits and the width ledger -/

section Encoding

/-- Encode an abstract index digit in a `w`-wire Boolean register. The
hypothesis `L ≤ 2 ^ w` makes the `Fin.castLE` embedding total and injective. -/
def binaryDigit (w L : ℕ) (h : L ≤ 2 ^ w) (ℓ : Fin L) : Reg w :=
  (bitVecEquiv w).symm (Fin.castLE h ℓ)

/-- Binary digit encoding is injective for every register width that can hold
all `L` digits. -/
theorem binaryDigit_inj (w L : ℕ) (h : L ≤ 2 ^ w) :
    Function.Injective (binaryDigit w L h) := by
  intro a b hab
  apply Fin.castLE_injective h
  have hc := congrArg (bitVecEquiv w) hab
  simpa [binaryDigit] using hc

/-- In the exact power-of-two case, binary digits are a full register
equivalence, not merely an embedding. -/
def binaryDigitEquiv (w L : ℕ) (hL : L = 2 ^ w) : Fin L ≃ Reg w :=
  (finCongr hL).trans (bitVecEquiv w).symm

/-- The exact-width encoding agrees with the canonical binary digit map. -/
theorem binaryDigitEquiv_eq (w L : ℕ) (hL : L = 2 ^ w) (ℓ : Fin L) :
    binaryDigitEquiv w L hL ℓ = binaryDigit w L (le_of_eq hL) ℓ := by
  apply (bitVecEquiv w).injective
  simp [binaryDigitEquiv, binaryDigit, Fin.castLE]
  apply Fin.ext
  rfl

/-- The exact-width binary encoding is bijective. -/
theorem binaryDigit_bijective (w L : ℕ) (hL : L = 2 ^ w) :
    Function.Bijective (binaryDigit w L (le_of_eq hL)) := by
  have heq : binaryDigit w L (le_of_eq hL) = binaryDigitEquiv w L hL := by
    funext ℓ
    exact (binaryDigitEquiv_eq w L hL ℓ).symm
  rw [heq]
  exact (binaryDigitEquiv w L hL).bijective

/-- Encode all `K` index digits independently in binary registers. -/
def binaryIndex (K L w : ℕ) (h : L ≤ 2 ^ w) (μ : TTIdx K L) : Fin K → Reg w :=
  fun i => binaryDigit w L h (μ i)

/-- The simultaneous encoding of all index digits is injective. -/
theorem binaryIndex_inj (K L w : ℕ) (h : L ≤ 2 ^ w) :
    Function.Injective (binaryIndex K L w h) := by
  intro μ ν hμν
  funext i
  apply binaryDigit_inj w L h
  exact congrFun hμν i

/-- The binary Taylor workspace: the system and unary order registers are
unchanged, while every abstract index digit is replaced by `w` Boolean wires. -/
abbrev BinaryWs (K w : ℕ) (Sys : Type*) := Sys × ((Fin K → Bool) × (Fin K → Reg w))

/-- Encode a complete Taylor workspace in the binary layout. -/
def encodeWs (K L w : ℕ) (Sys : Type*) (h : L ≤ 2 ^ w) :
    TTWs K L Sys → BinaryWs K w Sys :=
  fun x => (x.1, (x.2.1, binaryIndex K L w h x.2.2))

/-- The workspace encoding is injective; no abstract index information is lost
when moving to the physical binary layout. -/
theorem encodeWs_inj (K L w : ℕ) (Sys : Type*) (h : L ≤ 2 ^ w) :
    Function.Injective (encodeWs K L w Sys h) := by
  intro x y hxy
  have hs : x.1 = y.1 := congrArg (fun z : BinaryWs K w Sys => z.1) hxy
  have ho : x.2.1 = y.2.1 := congrArg (fun z : BinaryWs K w Sys => z.2.1) hxy
  have hi : x.2.2 = y.2.2 := binaryIndex_inj K L w h
    (congrArg (fun z : BinaryWs K w Sys => z.2.2) hxy)
  exact Prod.ext hs (Prod.ext ho hi)

/-- Flatten the `K` independent `w`-wire index registers into one `K * w`-wire
register. This is a basis equivalence, not an assertion about a subspace. -/
def binaryIndexRegEquiv (K w : ℕ) : (Fin K → Reg w) ≃ Reg (K * w) :=
  (Equiv.curry (Fin K) (Fin w) Bool).symm.trans
    (finProdFinEquiv.arrowCongr (Equiv.refl Bool))

/-- The number of Boolean basis states of the flattened index register is
`2 ^ (K * w)`, witnessing its physical width. -/
theorem binaryIndex_card (K w : ℕ) :
    Fintype.card (Fin K → Reg w) = 2 ^ (K * w) := by
  rw [Fintype.card_fun, card_reg, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- The binary index-register width is `K * w` wires. -/
def binaryIndexWidth (K w : ℕ) : ℕ := K * w

/-- At the ceiling-log width, the binary index register uses exactly the width
appearing in the Eq. (22) ancilla ledger. -/
theorem binaryWidthLedger (K L : ℕ) :
    K + binaryIndexWidth K (Nat.clog 2 L) = ancillaBits K L := by
  rfl

/-- The flattened binary index basis has the cardinality expected from its
physical width at `w = ⌈log₂ L⌉`. -/
theorem binaryIndex_card_ledger (K L : ℕ) :
    Fintype.card (Fin K → Reg (Nat.clog 2 L)) = 2 ^ (K * Nat.clog 2 L) :=
  binaryIndex_card K (Nat.clog 2 L)

end Encoding

/-! ### Transport of the abstract composed words -/

section Transport

variable {K L w : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- PREPARE transported instruction by instruction to the binary workspace. -/
def binaryPrepareWord (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    Circuit (BinaryWs K w Sys) :=
  extendWord (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
    (prepareWord K L Sys θ bL)

/-- SELECT transported instruction by instruction to the binary workspace. -/
def binarySelectWord (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ) :
    Circuit (BinaryWs K w Sys) :=
  extendWord (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
    (selectWord K L Sys V)

/-- The binary PREPARE word has exactly the measured `K + K` macro gates of the
composed abstract word. -/
theorem binaryPrepareCnt (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    GateCount (binaryPrepareWord K L w Sys h θ bL) = K + K := by
  rw [binaryPrepareWord, extendWord_gateCount, prepareCnt]

/-- The binary PREPARE word makes no oracle queries. -/
theorem binaryPrepareQC (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    QueryCount (binaryPrepareWord K L w Sys h θ bL) = 0 := by
  rw [binaryPrepareWord, extendWord_queryCount, prepareQC]

/-- The binary SELECT word has exactly the measured `K` macro gates. -/
theorem binarySelectCnt (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ) :
    GateCount (binarySelectWord K L w Sys h V) = K := by
  rw [binarySelectWord, extendWord_gateCount, selectCnt]

/-- The binary SELECT word makes no oracle queries at the macro-word layer. -/
theorem binarySelectQC (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ) :
    QueryCount (binarySelectWord K L w Sys h V) = 0 := by
  rw [binarySelectWord, extendWord_queryCount, selectQC]

/-- Binary PREPARE is unitary whenever the abstract load matrix is unitary. -/
theorem binaryPrepareUni (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) {bL : Matrix (Fin L) (Fin L) ℂ}
    (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    IsUnitaryCircuit (binaryPrepareWord K L w Sys h θ bL) := by
  exact extendWord_unitary _ _ _ (prepareUni K L Sys θ hL)

/-- Binary SELECT is unitary over a unitary term family. -/
theorem binarySelectUni (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ)
    (hV : ∀ ℓ, V ℓ ∈ Matrix.unitaryGroup Sys ℂ) :
    IsUnitaryCircuit (binarySelectWord K L w Sys h V) := by
  exact extendWord_unitary _ _ _ (selectUni K L Sys V hV)

/-- The binary PREPARE denotation is the identity-padded abstract denotation. -/
theorem binaryPrepareDenote (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    Denote (1 : Matrix (BinaryWs K w Sys) (BinaryWs K w Sys) ℂ)
        (binaryPrepareWord K L w Sys h θ bL) =
      extendMatrix (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
        (Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
          (prepareWord K L Sys θ bL)) := by
  rw [binaryPrepareWord, ← extendMatrix_one (encodeWs K L w Sys h)
    (encodeWs_inj K L w Sys h)]
  exact extendWord_denote (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
    (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (prepareWord K L Sys θ bL)

/-- The binary SELECT denotation is the identity-padded abstract denotation. -/
theorem binarySelectDenote (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ) :
    Denote (1 : Matrix (BinaryWs K w Sys) (BinaryWs K w Sys) ℂ)
        (binarySelectWord K L w Sys h V) =
      extendMatrix (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
        (Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
          (selectWord K L Sys V)) := by
  rw [binarySelectWord, ← extendMatrix_one (encodeWs K L w Sys h)
    (encodeWs_inj K L w Sys h)]
  exact extendWord_denote (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
    (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (selectWord K L Sys V)

/-- The binary PREPARE profile exposes the measured composed macro-gate count. -/
theorem binaryPrepareMacro (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    (wordProfile (binaryPrepareWord K L w Sys h θ bL)).macroGates = some (K + K) := by
  rw [wordProfileG, binaryPrepareCnt]

/-- The binary SELECT profile exposes the measured composed macro-gate count. -/
theorem binarySelectMacro (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ) :
    (wordProfile (binarySelectWord K L w Sys h V)).macroGates = some K := by
  rw [wordProfileG, binarySelectCnt]

/-- Macro-unit expansion of the measured binary PREPARE count. -/
theorem binaryPrepUnit (u : MacroUnit) (K L w : ℕ) (Sys : Type*)
    [Fintype Sys] [DecidableEq Sys] (h : L ≤ 2 ^ w) (θ : Fin K → ℝ)
    (bL : Matrix (Fin L) (Fin L) ℂ) :
    macroCounts u (GateCount (binaryPrepareWord K L w Sys h θ bL)) =
      (K + K) * u.basic := by
  rw [binaryPrepareCnt]
  rfl

/-- Macro-unit expansion of the measured binary SELECT count. -/
theorem binarySelUnit (u : MacroUnit) (K L w : ℕ) (Sys : Type*)
    [Fintype Sys] [DecidableEq Sys] (h : L ≤ 2 ^ w) (V : Fin L → Matrix Sys Sys ℂ) :
    macroCounts u (GateCount (binarySelectWord K L w Sys h V)) = K * u.basic := by
  rw [binarySelectCnt]
  rfl

end Transport

/-! ### First ring of the `B† · SELECT · B` block operator -/

section BlockRing

variable {K L w : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- The abstract composed block operator `B† · SELECT · B`, with `B` and SELECT
 denotations taken from the actual abstract words. -/
def abstractBlock (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ)
    (V : Fin L → Matrix Sys Sys ℂ) : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  (Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
      (prepareWord K L Sys θ bL))ᴴ *
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (selectWord K L Sys V) *
      Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
        (prepareWord K L Sys θ bL)

/-- The binary composed block operator, built from the transported PREPARE and
SELECT words in the same order as `abstractBlock`. -/
def binaryBlock (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ)
    (V : Fin L → Matrix Sys Sys ℂ) : Matrix (BinaryWs K w Sys) (BinaryWs K w Sys) ℂ :=
  (Denote (1 : Matrix (BinaryWs K w Sys) (BinaryWs K w Sys) ℂ)
      (binaryPrepareWord K L w Sys h θ bL))ᴴ *
    Denote (1 : Matrix (BinaryWs K w Sys) (BinaryWs K w Sys) ℂ)
      (binarySelectWord K L w Sys h V) *
      Denote (1 : Matrix (BinaryWs K w Sys) (BinaryWs K w Sys) ℂ)
        (binaryPrepareWord K L w Sys h θ bL)

/-- First semantic ring: the binary composed block operator is exactly the
identity-padded abstract composed block operator. -/
theorem binaryBlock_eq_extend (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ)
    (V : Fin L → Matrix Sys Sys ℂ) :
    binaryBlock K L w Sys h θ bL V =
      extendMatrix (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
        (abstractBlock K L Sys θ bL V) := by
  rw [binaryBlock, abstractBlock, binaryPrepareDenote, binarySelectDenote,
    ← extendMatrix_conjTranspose, ← extendMatrix_mul, ← extendMatrix_mul]

/-- On encoded workspace basis states, the composed binary block operator has
exactly the abstract block-operator entries. This is the prepared-state-space
restriction of the first ring; no spectral compression is asserted here. -/
theorem binaryBlock_image (K L w : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (h : L ≤ 2 ^ w) (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ)
    (V : Fin L → Matrix Sys Sys ℂ) (x y : TTWs K L Sys) :
    binaryBlock K L w Sys h θ bL V (encodeWs K L w Sys h x) (encodeWs K L w Sys h y) =
      abstractBlock K L Sys θ bL V x y := by
  rw [binaryBlock_eq_extend]
  exact extendMatrix_image (encodeWs K L w Sys h) (encodeWs_inj K L w Sys h)
    (abstractBlock K L Sys θ bL V) x y

end BlockRing

end

end Qatlib.Papers.TruncTaylor14.PrepareSelectBinary

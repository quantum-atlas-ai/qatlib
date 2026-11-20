/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Concepts.CircuitLang.LocGates
public import Qatlib.Concepts.GateKit.GateContract
public import Qatlib.Concepts.CostModels.UnitAlgebra
public import Qatlib.Concepts.CostModels.CountBridge
public import Qatlib.Papers.TruncTaylor14.ResourceCount.ResourceCount
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-!
# PREPARE and SELECT as composed words, with counts from the composition

Fixed source: Berry, Childs, Cleve, Kothari and Somma, arXiv:1412.4687v1, pp. 3–4,
Eqs. (22)–(24). For the truncated-Taylor resource ledger, the block encoding's PREPARE
and SELECT are defined as actual composed query words over exact matrix-gate contracts,
and their gate counts are derived from the defined products through the UnitAlgebra
cost algebra (`GateCount` / `QueryCount` / `wordProfile` / `MacroUnit`), never
prescribed (DESIGN.md §12, criterion 5: macro-gate counting is the existence layer;
literal or synthesized T-counts stay unknown).

Concretely, the workspace is `TTWs = Sys × (order × index digits)`: a `K`-wire unary
order register (`Reg K`), `K` index digits (`Fin K → Fin L`, one per Taylor position),
and an abstract system register carrying the term-unitary family `V`. PREPARE is the
Eq. (23) composition — the unary rotation cascade (a leading one-wire rotation lifted
from the exact-gate contract `ExGate`/`exWord`, then one controlled rotation per
further wire, placed by `PlacedFirst`) followed by one load macro per index register.
SELECT is the per-position controlled selection `selStep`, a block-diagonal word step;
its denotation is proved to be exactly the LCU select operator `taylorSelect` (the
product of the term unitaries on the active unary positions). All counts
(`cascCnt = K`, `loadsCnt = K`, `prepareCnt = K + K`, `selectCnt = K`, queries `0`)
are measured off these words by list induction, then closed into `CostProfile` fields
by `wordProfileQ`/`wordProfileG`/`profAppend`/`serialMacroAdd`. Elementary accounting
goes through the `MacroUnit` expansion bridge under explicit unit hypotheses, and the
resulting totals are proved equal to the prescribed ledgers `prepGates`/`selectVGates`
of `ResourceCount` (Eq. (23)/(24) closure, composition side primary). The Eq. (22)
register-width ledger is stated as explicit hypotheses (`ancLedger`, `wsLedger`)
tying the workspace's ancilla budget to `ancillaBits`; the binary realization of the
`Fin L` digits and the physical width transport are hypotheses, not constructions.

Not claimed here: the SPAI preconditioner and the PrecondQLSA13 complexity statement
(card-level dependency note only); physical register-width transport; error–resource
joint statements (rotation-angle/amplitude semantics, OAA, block-encoding spectral
side); elementary-gate or T-count synthesis of any macro (the `ApproxGate` regime);
oracle-query billing of the `V` realization; and the full `B† · SELECT · B` block
encoding semantics.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.GateKit.GateContract
open Qatlib.Concepts.CostModels.CountBridge
open Qatlib.Concepts.CostModels.UnitAlgebra
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Papers.TruncTaylor14.ResourceCount

open scoped Matrix

namespace Qatlib.Papers.TruncTaylor14.PrepareSelectCount

/-- The index digits of the Taylor workspace: one `Fin L` term index per unary
position. The binary width of each digit register is a ledger hypothesis, not a
construction (see `wsLedger`). -/
abbrev TTIdx (K L : ℕ) := Fin K → Fin L

/-- The truncated-Taylor PREPARE/SELECT workspace: system register, unary order
register, and index digits. -/
abbrev TTWs (K L : ℕ) (Sys : Type*) := Sys × ((Fin K → Bool) × TTIdx K L)

noncomputable section

/-! ### Word skeleton: serial composition of macro-gate steps -/

section Skeleton

variable {I ι : Type*} [Fintype I] [DecidableEq I]

/-- The serial macro-gate word over an index list: one
`Step.gate` per list entry,
in list order. This is the composition skeleton all words below are instances of. -/
def gateWord (M : ι → Matrix I I ℂ) (l : List ι) : Circuit I :=
  l.map (fun i => Step.gate (M i))

omit [Fintype I] [DecidableEq I] in

/-- The skeleton word grows by one gate step at the front. -/
theorem gateWordCons (M : ι → Matrix I I ℂ) (i : ι) (l : List ι) :
    gateWord M (i :: l) = Step.gate (M i) :: gateWord M l :=
  rfl

omit [Fintype I] [DecidableEq I] in

/-- The macro-gate count of a skeleton word is its list length: measured off the
actual composition, not prescribed. -/
theorem gateWordGC (M : ι → Matrix I I ℂ) (l : List ι) :
    GateCount (gateWord M l) = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [gateWordCons, gateCount_gate, ih, List.length_cons]

omit [Fintype I] [DecidableEq I] in

/-- A skeleton word makes no oracle queries: the query count is measured, and it is
zero because no `Step.query` occurs in the
composition. -/
theorem gateWordQC (M : ι → Matrix I I ℂ) (l : List ι) :
    QueryCount (gateWord M l) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [gateWordCons, queryCount_gate, ih]

/-- A skeleton word is a unitary circuit whenever every composed macro step is
unitary. -/
theorem gateWordUni (M : ι → Matrix I I ℂ) (l : List ι)
    (hM : ∀ i, M i ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (gateWord M l) := by
  induction l with
  | nil => exact isUnitaryCircuit_nil
  | cons i l ih =>
      rw [gateWordCons]
      exact (isUnitaryCircuit_gate _ _).mpr ⟨hM i, ih⟩

/-- The denotation of a skeleton word is the right fold of its macro matrices:
the composed product, first step acting rightmost. -/
theorem gateWordDen (oracle : Matrix I I ℂ) (M : ι → Matrix I I ℂ) (l : List ι) :
    Denote oracle (gateWord M l) = l.foldr (fun i P => P * M i) 1 := by
  induction l with
  | nil => rw [gateWord, List.map_nil, denote_nil]; rfl
  | cons i l ih =>
      rw [gateWordCons, denote_gate, ih, List.foldr_cons]

end Skeleton

/-! ### Eq. (23) primitives: the one-wire rotation and its controlled lift -/

/-- The real one-wire rotation matrix of the Eq. (23) cascade, parametrized by its
cosine/sine entries. -/
def rot2C (c s : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if a then if b then (Complex.ofReal c) else (-(Complex.ofReal s))
    else if b then (Complex.ofReal s) else (Complex.ofReal c)

/-- Entry form of the parametrized rotation matrix on raw Boolean reads. -/
theorem rot2CE (c s : ℝ) (a b : Bool) :
    rot2C c s a b =
      if a then if b then (Complex.ofReal c) else (-(Complex.ofReal s))
      else if b then (Complex.ofReal s) else (Complex.ofReal c) :=
  rfl

private theorem starC (r : ℝ) :
    (starRingEnd ℂ) (Complex.ofReal r) = Complex.ofReal r :=
  Complex.conj_ofReal r

private theorem starN (r : ℝ) :
    (starRingEnd ℂ) (-(Complex.ofReal r)) = -(Complex.ofReal r) := by
  rw [map_neg]
  exact congrArg Neg.neg (starC r)

private theorem rot2PairC (c s : ℝ) (h1 : c * c + s * s = (1 : ℝ))
    (h2 : s * s + c * c = (1 : ℝ)) (x y : Bool) :
    ∑ z : Bool, star (rot2C c s z x) * rot2C c s z y = if x = y then (1 : ℂ) else 0 := by
  cases x <;> cases y <;>
    norm_num [rot2CE, Fintype.sum_bool]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    exact congrArg Complex.ofReal h2
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_add]
    exact congrArg Complex.ofReal (by ring)
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_add]
    exact congrArg Complex.ofReal (by ring)
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    exact congrArg Complex.ofReal h1

/-- The real one-wire rotation matrix of the Eq. (23) cascade. -/
def rot2 (θ : ℝ) : Matrix Bool Bool ℂ := rot2C (Real.cos θ) (Real.sin θ)

/-- The one-wire rotation is unitary: columns orthonormal by `sin² + cos² = 1`. -/
theorem rot2Uni (θ : ℝ) : rot2 θ ∈ Matrix.unitaryGroup Bool ℂ := by
  have h1 : (Real.cos θ) * (Real.cos θ) + (Real.sin θ) * (Real.sin θ) = (1 : ℝ) := by
    have h0 := Real.sin_sq_add_cos_sq θ
    rw [sq, sq] at h0
    linarith
  have h2 : (Real.sin θ) * (Real.sin θ) + (Real.cos θ) * (Real.cos θ) = (1 : ℝ) := by
    linarith
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  exact rot2PairC (Real.cos θ) (Real.sin θ) h1 h2 a b

/-- The Eq. (23) leading rotation wrapped in the exact-gate contract: the
contract carries the matrix and its unitarity proof. The wrap is at macro level —
elementary (finite-bit) synthesis of the rotation angle is not claimed and belongs
to the `ApproxGate` regime. -/
def rotEx (θ : ℝ) : ExGate := ⟨rot2 θ, rot2Uni θ⟩

/-- The two-wire controlled rotation on a control/target Boolean pair:
`rot2 θ` on the target when the control reads `true`, identity otherwise. -/
def crot2 (θ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  relabelGate (Equiv.prodComm Bool Bool)
    (Matrix.blockDiagonal fun b : Bool => if b then rot2 θ else 1)

/-- The controlled rotation is unitary: block-diagonal with unitary blocks, after
swapping the block-indexed target/control pair into control/target order. -/
theorem crot2Uni (θ : ℝ) : crot2 θ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  apply (relabelGate_mem_unitaryGroup _ _).2
  have hR : (rot2 θ)ᴴ * rot2 θ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff' (A := rot2 θ)).mp (rot2Uni θ)
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hblock : ∀ b : Bool,
      ((if b then rot2 θ else (1 : Matrix Bool Bool ℂ))ᴴ *
        (if b then rot2 θ else 1)) = 1 := by
    intro b
    cases b
    · simp
    · exact hR
  rw [funext hblock]
  exact Matrix.blockDiagonal_one

/-- The controlled-rotation block on a one-wire register and a target bit,
transported from `crot2` along `regOneBool`. -/
def crotB (θ : ℝ) : Matrix (Reg 1 × Bool) (Reg 1 × Bool) ℂ :=
  relabelGate (regOneBool.symm.prodCongr (Equiv.refl Bool)) (crot2 θ)

/-- The transported controlled-rotation block is unitary. -/
theorem crotBUni (θ : ℝ) : crotB θ ∈ Matrix.unitaryGroup (Reg 1 × Bool) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).2 (crot2Uni θ)

/-- The wire split of an `(n+1+1)`-wire register into spectators, the last prefix
wire (control), and the new last wire (target). -/
def lastE (n : ℕ) : Reg (n + 1 + 1) ≃ (Reg n × (Reg 1 × Bool)) :=
  (regAppendEquiv n 2).trans
    ((Equiv.refl (Reg n)).prodCongr
      ((regAppendEquiv 1 1).trans ((Equiv.refl (Reg 1)).prodCongr regOneBool)))

/-- The Eq. (23) controlled rotation on the last wire of an `(n+1+1)`-wire order
register, controlled by its predecessor: identity on the `n` spectator wires. -/
def lastCrot (n : ℕ) (θ : ℝ) : Matrix (Reg (n + 1 + 1)) (Reg (n + 1 + 1)) ℂ :=
  relabelGate (lastE n).symm
    (TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) (crotB θ))

/-- The last-wire controlled rotation is unitary: a tensor-placed unitary block. -/
theorem lastCrotUni (n : ℕ) (θ : ℝ) :
    lastCrot n θ ∈ Matrix.unitaryGroup (Reg (n + 1 + 1)) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).2
    (tensorGate_unitary (Submonoid.one_mem _) (crotBUni θ))

/-! ### The unary rotation cascade word of Eq. (23) -/

section Cascade

variable {K : ℕ}

/-- Step lift from an `n`-wire order register to one more wire: gates are placed on
the prefix wires by `PlacedFirst`, queries pass through. -/
def liftFirst (n : ℕ) : Step (Reg n) → Step (Reg (n + 1))
  | Step.gate U => Step.gate (PlacedFirst n 1 U)
  | Step.query => Step.query

/-- Prefix lifting preserves the gate and query counts exactly. -/
theorem liftFirstCnt (n : ℕ) (C : Circuit (Reg n)) :
    GateCount (C.map (liftFirst n)) = GateCount C ∧
      QueryCount (C.map (liftFirst n)) = QueryCount C := by
  induction C with
  | nil => exact ⟨rfl, rfl⟩
  | cons s C ih =>
      cases s with
      | gate U => simp [liftFirst, ih.1, ih.2]
      | query => simp [liftFirst, ih.1, ih.2]

/-- Prefix lifting preserves circuit unitarity. -/
theorem liftFirstUni (n : ℕ) (C : Circuit (Reg n)) :
    IsUnitaryCircuit C → IsUnitaryCircuit (C.map (liftFirst n)) := by
  induction C with
  | nil => exact fun _ => isUnitaryCircuit_nil
  | cons s C ih =>
      intro hC
      cases s with
      | gate U =>
          rw [List.map_cons]
          exact (isUnitaryCircuit_gate _ _).mpr
            ⟨placedFirst_uni ((isUnitaryCircuit_gate _ _).mp hC).1,
              ih ((isUnitaryCircuit_gate _ _).mp hC).2⟩
      | query =>
          rw [List.map_cons]
          exact (isUnitaryCircuit_query _).mpr (ih ((isUnitaryCircuit_query _).mp hC))

/-- The unary rotation cascade of Eq. (23) as an actual composed word on the `n`-wire
order register: the empty word on zero wires; the exact-gate contract word
`exWord (rotEx …)` of the leading one-wire rotation on one wire; and on `n + 2` wires,
the prefix cascade lifted by `PlacedFirst`, followed by the last-wire controlled
rotation. Every step matrix is an explicitly defined unitary; no count is prescribed. -/
def cascWord : (n : ℕ) → (Fin n → ℝ) → Circuit (Reg n)
  | 0, _ => []
  | 1, θ => exWord (rotEx (θ ⟨0, by omega⟩))
  | n + 2, θ =>
      (cascWord (n + 1) (fun i => θ i.castSucc)).map (liftFirst (n + 1))
        ++ [Step.gate (lastCrot n (θ ⟨n + 1, by omega⟩))]

/-- The exact contract word of the leading rotation is exactly the one-wire cascade
base: the contract lifting is consumed literally by the composition. -/
theorem rotExWord (θ : Fin 1 → ℝ) : exWord (rotEx (θ ⟨0, by omega⟩)) = cascWord 1 θ :=
  rfl

private theorem cascPair (n : ℕ) :
    (∀ θ : Fin n → ℝ, GateCount (cascWord n θ) = n ∧ QueryCount (cascWord n θ) = 0 ∧
      IsUnitaryCircuit (cascWord n θ)) ∧
    (∀ θ : Fin (n + 1) → ℝ, GateCount (cascWord (n + 1) θ) = n + 1 ∧
      QueryCount (cascWord (n + 1) θ) = 0 ∧ IsUnitaryCircuit (cascWord (n + 1) θ)) := by
  induction n with
  | zero =>
      refine ⟨fun _ => ⟨rfl, rfl, isUnitaryCircuit_nil⟩, fun θ => ?_⟩
      have hstep : cascWord 1 θ =
          [Step.gate (relabelGate regOneBool.symm (rot2 (θ ⟨0, by omega⟩)))] :=
        rfl
      rw [hstep]
      exact ⟨rfl, rfl, (isUnitaryCircuit_gate _ _).mpr
        ⟨(relabelGate_mem_unitaryGroup _ _).2 (rot2Uni _), isUnitaryCircuit_nil⟩⟩
  | succ n ih =>
      obtain ⟨_, ih1⟩ := ih
      refine ⟨ih1, fun θ => ?_⟩
      have hstep : cascWord (n + 2) θ =
          (cascWord (n + 1) (fun i => θ i.castSucc)).map (liftFirst (n + 1))
            ++ [Step.gate (lastCrot n (θ ⟨n + 1, by omega⟩))] :=
        rfl
      rw [hstep]
      obtain ⟨hc1, hq1, hu1⟩ := ih1 (fun i => θ i.castSucc)
      have hmap := liftFirstCnt (n + 1) (cascWord (n + 1) (fun i => θ i.castSucc))
      refine ⟨?_, ?_, ?_⟩
      · rw [gateCount_append, hmap.1, hc1]
        rfl
      · rw [queryCount_append, hmap.2, hq1]
        rfl
      · exact (isUnitaryCircuit_append _ _).mpr
          ⟨liftFirstUni (n + 1) _ hu1,
            (isUnitaryCircuit_gate _ _).mpr ⟨lastCrotUni n _, isUnitaryCircuit_nil⟩⟩

/-- Eq. (23), cascade side, measured: the composed cascade word on `n` wires carries
exactly `n` macro gates — one rotation step per unary wire. -/
theorem cascCnt (n : ℕ) (θ : Fin n → ℝ) : GateCount (cascWord n θ) = n :=
  ((cascPair n).1 θ).1

/-- The composed cascade word makes no oracle queries. -/
theorem cascQC (n : ℕ) (θ : Fin n → ℝ) : QueryCount (cascWord n θ) = 0 :=
  ((cascPair n).1 θ).2.1

/-- The composed cascade word is a unitary circuit: every step matrix is one of the
explicitly proved unitaries above. -/
theorem cascUni (n : ℕ) (θ : Fin n → ℝ) : IsUnitaryCircuit (cascWord n θ) :=
  ((cascPair n).1 θ).2.2

end Cascade

/-! ### Workspace lifts for the order and index registers -/

section Workspace

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- Workspace split at the order register: `TTWs ≃ order × (system × index)`. -/
def wsOrdE (K L : ℕ) (Sys : Type*) :
    TTWs K L Sys ≃ ((Fin K → Bool) × (Sys × TTIdx K L)) :=
  (Equiv.prodComm Sys ((Fin K → Bool) × TTIdx K L)).trans
    ((Equiv.prodAssoc (Fin K → Bool) (TTIdx K L) Sys).trans
      ((Equiv.refl (Fin K → Bool)).prodCongr (Equiv.prodComm (TTIdx K L) Sys)))

/-- Workspace split at the index digits: `TTWs ≃ index × (order × system)`. -/
def wsIdxE (K L : ℕ) (Sys : Type*) :
    TTWs K L Sys ≃ (TTIdx K L × ((Fin K → Bool) × Sys)) :=
  (Equiv.prodComm Sys ((Fin K → Bool) × TTIdx K L)).trans
    (((Equiv.prodComm (Fin K → Bool) (TTIdx K L)).prodCongr (Equiv.refl Sys)).trans
      (Equiv.prodAssoc (TTIdx K L) (Fin K → Bool) Sys))

/-- Lift an order-register gate to the workspace, identity on system and indices. -/
def liftOrd (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (U : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) :
    Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  Matrix.reindex (wsOrdE K L Sys).symm (wsOrdE K L Sys).symm
    (TensorGate U (1 : Matrix (Sys × TTIdx K L) (Sys × TTIdx K L) ℂ))

/-- Lift an index-digit gate to the workspace, identity on system and order. -/
def liftIdx (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (U : Matrix (TTIdx K L) (TTIdx K L) ℂ) :
    Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  Matrix.reindex (wsIdxE K L Sys).symm (wsIdxE K L Sys).symm
    (TensorGate U (1 : Matrix ((Fin K → Bool) × Sys) ((Fin K → Bool) × Sys) ℂ))

/-- Order lifts are multiplicative. -/
theorem liftOrdMul (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (U V : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) :
    liftOrd K L Sys (U * V) = liftOrd K L Sys U * liftOrd K L Sys V := by
  simp only [liftOrd]
  rw [← reidxMul, tensorGate_mul, Matrix.one_mul]

/-- Order lifts preserve the identity. -/
theorem liftOrdOne (K L : ℕ) (Sys : Type*) [DecidableEq Sys] :
    liftOrd K L Sys (1 : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) = 1 := by
  simp only [liftOrd, reidxOne, tensorGate_one]

/-- Lifting a unitary order gate preserves unitarity. -/
theorem liftOrdUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    {U : Matrix (Fin K → Bool) (Fin K → Bool) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin K → Bool) ℂ) :
    liftOrd K L Sys U ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ :=
  reidxUnitary _ (tensorGate_unitary hU (Submonoid.one_mem _))

/-- Lifting a unitary index-digit gate preserves unitarity. -/
theorem liftIdxUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    {U : Matrix (TTIdx K L) (TTIdx K L) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (TTIdx K L) ℂ) :
    liftIdx K L Sys U ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ :=
  reidxUnitary _ (tensorGate_unitary hU (Submonoid.one_mem _))

/-- Step lift of the order register into the workspace. -/
def liftOrdStep (K L : ℕ) (Sys : Type*) [DecidableEq Sys] :
    Step (Fin K → Bool) → Step (TTWs K L Sys)
  | Step.gate U => Step.gate (liftOrd K L Sys U)
  | Step.query => Step.query

/-- Workspace lifting preserves the gate and query counts exactly. -/
theorem liftOrdStepCnt (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (C : Circuit (Fin K → Bool)) :
    GateCount (C.map (liftOrdStep K L Sys)) = GateCount C ∧
      QueryCount (C.map (liftOrdStep K L Sys)) = QueryCount C := by
  induction C with
  | nil => exact ⟨rfl, rfl⟩
  | cons s C ih =>
      cases s with
      | gate U => simp [liftOrdStep, ih.1, ih.2]
      | query => simp [liftOrdStep, ih.1, ih.2]

/-- Workspace lifting preserves circuit unitarity. -/
theorem liftOrdStepUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (C : Circuit (Fin K → Bool)) :
    IsUnitaryCircuit C → IsUnitaryCircuit (C.map (liftOrdStep K L Sys)) := by
  induction C with
  | nil => exact fun _ => isUnitaryCircuit_nil
  | cons s C ih =>
      intro hC
      cases s with
      | gate U =>
          rw [List.map_cons]
          exact (isUnitaryCircuit_gate _ _).mpr
            ⟨liftOrdUni K L Sys ((isUnitaryCircuit_gate _ _).mp hC).1,
              ih ((isUnitaryCircuit_gate _ _).mp hC).2⟩
      | query =>
          rw [List.map_cons]
          exact (isUnitaryCircuit_query _).mpr (ih ((isUnitaryCircuit_query _).mp hC))

/-- The lifted denotation of a cascade-shaped word: lifting commutes with the
composed product. -/
private theorem denoteMapLift (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (C : Circuit (Fin K → Bool)) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (C.map (liftOrdStep K L Sys))
      = liftOrd K L Sys (Denote (1 : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) C) := by
  induction C with
  | nil => rw [List.map_nil, denote_nil, denote_nil, liftOrdOne]
  | cons s C ih =>
      cases s with
      | gate U =>
          rw [List.map_cons]
          simp only [liftOrdStep]
          rw [denote_gate, denote_gate, ih, liftOrdMul]
      | query =>
          rw [List.map_cons]
          simp only [liftOrdStep]
          rw [denote_query, denote_query, ih, liftOrdMul, liftOrdOne]

end Workspace

/-! ### Eq. (23) index loads: one macro per register -/

section Loads

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- One index-register load placed on digit `i`: the load matrix `U` on the `i`-th
digit, identity on all other digits. Entrywise on digit reads. -/
def onDigit (i : Fin K) (U : Matrix (Fin L) (Fin L) ℂ) :
    Matrix (TTIdx K L) (TTIdx K L) ℂ :=
  Matrix.of fun μ ν => if ∀ j : Fin K, j ≠ i → μ j = ν j then U (μ i) (ν i) else 0

/-- Entry form of the digit placement. -/
theorem onDigitE (i : Fin K) (U : Matrix (Fin L) (Fin L) ℂ) (μ ν : TTIdx K L) :
    onDigit i U μ ν =
      if ∀ j : Fin K, j ≠ i → μ j = ν j then U (μ i) (ν i) else 0 :=
  rfl

/-- Conjugate-transposed entry form of the digit placement. -/
theorem onDigitH (i : Fin K) (U : Matrix (Fin L) (Fin L) ℂ) (μ κ : TTIdx K L) :
    (onDigit i U)ᴴ μ κ = star (onDigit i U κ μ) :=
  rfl

/-- Fiber-sum lemma on digit registers: a function that vanishes off the `i`-fiber
of `μ` sums over the digit values. -/
private theorem sumFiber (i : Fin K) (μ : TTIdx K L) (g : TTIdx K L → ℂ)
    (hg : ∀ ν, (∀ j : Fin K, j ≠ i → ν j = μ j) ∨ g ν = 0) :
    ∑ ν, g ν = ∑ ℓ : Fin L, g (Function.update μ i ℓ) := by
  classical
  have hinj : ∀ ℓ ℓ' : Fin L,
      Function.update μ i ℓ = Function.update μ i ℓ' → ℓ = ℓ' := by
    intro ℓ ℓ' h
    have h2 := congrFun h i
    simpa using h2
  have hvan : ∀ ν ∈ (Finset.univ : Finset (TTIdx K L)),
      ν ∉ Finset.univ.image (fun ℓ => Function.update μ i ℓ) → g ν = 0 := by
    intro ν _ hν
    rcases hg ν with h | h
    · exfalso
      apply hν
      refine Finset.mem_image.mpr ⟨ν i, Finset.mem_univ _, ?_⟩
      funext j
      rcases eq_or_ne j i with rfl | hji
      · simp
      · rw [Function.update_of_ne hji]
        exact (h j hji).symm
    · exact h
  calc ∑ ν, g ν
      = ∑ ν ∈ Finset.univ.image (fun ℓ => Function.update μ i ℓ), g ν :=
        (Finset.sum_subset (Finset.subset_univ _) hvan).symm
    _ = ∑ ℓ : Fin L, g (Function.update μ i ℓ) :=
        Finset.sum_image (fun a _ b _ h => hinj a b h)

/-- The digit placement of a unitary load is unitary: entrywise orthonormality via
the fiber sum and the load's own unitarity. -/
theorem onDigitUni (i : Fin K) {U : Matrix (Fin L) (Fin L) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    onDigit i U ∈ Matrix.unitaryGroup (TTIdx K L) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hUU : (U)ᴴ * U = 1 := by
    have hU' := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rw [Matrix.star_eq_conjTranspose] at hU'
    exact hU'
  ext μ ν
  have hsum : ((onDigit i U)ᴴ * onDigit i U) μ ν =
      ∑ κ : TTIdx K L, star (onDigit i U κ μ) * onDigit i U κ ν := by
    rw [Matrix.mul_apply]
    rfl
  have hE1 : ∀ κ : TTIdx K L, onDigit i U κ μ =
      (if ∀ j : Fin K, j ≠ i → κ j = μ j then U (κ i) (μ i) else 0) := fun _ => rfl
  have hE2 : ∀ κ : TTIdx K L, onDigit i U κ ν =
      (if ∀ j : Fin K, j ≠ i → κ j = ν j then U (κ i) (ν i) else 0) := fun _ => rfl
  rw [hsum, Matrix.one_apply]
  simp only [hE1, hE2]
  by_cases hagree : ∀ j : Fin K, j ≠ i → μ j = ν j
  · rw [sumFiber i μ
      (fun κ => (star (if ∀ j : Fin K, j ≠ i → κ j = μ j then U (κ i) (μ i) else 0)) *
        (if ∀ j : Fin K, j ≠ i → κ j = ν j then U (κ i) (ν i) else 0))
      (fun κ => by
        by_cases hc : ∀ j : Fin K, j ≠ i → κ j = μ j
        · exact Or.inl hc
        · refine Or.inr ?_
          simp [hc])]
    have hval : ∀ ℓ : Fin L,
        ((fun κ => (star (if ∀ j : Fin K, j ≠ i → κ j = μ j then U (κ i) (μ i) else 0)) *
          (if ∀ j : Fin K, j ≠ i → κ j = ν j then U (κ i) (ν i) else 0))
          (Function.update μ i ℓ)) = star (U ℓ (μ i)) * U ℓ (ν i) := by
      intro ℓ
      have _h1 : ∀ j : Fin K, j ≠ i → Function.update μ i ℓ j = μ j :=
        fun j hj => by rw [Function.update_of_ne hj]
      have _h2 : ∀ j : Fin K, j ≠ i → Function.update μ i ℓ j = ν j :=
        fun j hj => (_h1 j hj).trans (hagree j hj)
      simp only [Function.update_self]
      split_ifs
      rfl
    rw [Finset.sum_congr rfl (fun ℓ _ => hval ℓ)]
    have hct : ∀ ℓ : Fin L, star (U ℓ (μ i)) = (U)ᴴ (μ i) ℓ := fun _ => rfl
    have hprod : ∑ ℓ : Fin L, (U)ᴴ (μ i) ℓ * U ℓ (ν i) = ((U)ᴴ * U) (μ i) (ν i) := by
      rw [Matrix.mul_apply]
    calc ∑ ℓ : Fin L, star (U ℓ (μ i)) * U ℓ (ν i)
        = ∑ ℓ : Fin L, (U)ᴴ (μ i) ℓ * U ℓ (ν i) :=
          Finset.sum_congr rfl (fun ℓ _ => by rw [hct ℓ])
      _ = ((U)ᴴ * U) (μ i) (ν i) := hprod
      _ = ((1 : Matrix (Fin L) (Fin L) ℂ) (μ i) (ν i)) := by rw [hUU]
      _ = (if μ i = ν i then (1 : ℂ) else 0) := Matrix.one_apply
      _ = (if μ = ν then (1 : ℂ) else 0) := by
          by_cases hμν : μ = ν
          · subst hμν
            simp
          · have hne : μ i ≠ ν i := by
              intro hc
              apply hμν
              funext j
              rcases eq_or_ne j i with rfl | hj
              · exact hc
              · exact hagree j hj
            simp [hne, hμν]
  · have hμν : μ ≠ ν := fun h => hagree (fun j _ => congrFun h j)
    rw [Finset.sum_eq_zero]
    · simp [hμν]
    · intro κ _
      by_cases h1 : ∀ j : Fin K, j ≠ i → κ j = μ j
      · have h2 : ¬(∀ j : Fin K, j ≠ i → κ j = ν j) := fun h =>
          hagree (fun j hj => ((h1 j hj).symm.trans (h j hj)))
        simp [h2]
      · have hz0 : (if ∀ j : Fin K, j ≠ i → κ j = μ j then U (κ i) (μ i) else 0) = 0 :=
          ite_eq_right h1
        rw [hz0]
        simp

/-- One index-register load step in the workspace: the digit placement of the load
unitary, lifted to the full Taylor workspace. -/
def loadStep (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (bL : Matrix (Fin L) (Fin L) ℂ) (i : Fin K) :
    Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  liftIdx K L Sys (onDigit i bL)

/-- A load step with a unitary load matrix is unitary. -/
theorem loadStepUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    {bL : Matrix (Fin L) (Fin L) ℂ}
    (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) (i : Fin K) :
    loadStep K L Sys bL i ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ :=
  liftIdxUni K L Sys (onDigitUni i hL)

/-- The Eq. (23) load stage as a composed word: one load macro per index register,
in register order. -/
def loadsWord (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (bL : Matrix (Fin L) (Fin L) ℂ) :
    Circuit (TTWs K L Sys) :=
  gateWord (fun i => loadStep K L Sys bL i) (List.finRange K)

/-- Eq. (23), load side, measured: the load stage carries exactly `K` macro gates,
one per index register. -/
theorem loadsCnt (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (bL : Matrix (Fin L) (Fin L) ℂ) :
    GateCount (loadsWord K L Sys bL) = K := by
  rw [loadsWord, gateWordGC, List.length_finRange]

/-- The load stage makes no oracle queries. -/
theorem loadsQC (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (bL : Matrix (Fin L) (Fin L) ℂ) :
    QueryCount (loadsWord K L Sys bL) = 0 :=
  gateWordQC _ _

/-- The load stage is a unitary circuit whenever the load matrix is unitary. -/
theorem loadsUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    {bL : Matrix (Fin L) (Fin L) ℂ} (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    IsUnitaryCircuit (loadsWord K L Sys bL) :=
  gateWordUni _ _ (fun i => loadStepUni K L Sys hL i)

end Loads

/-! ### The PREPARE word of the truncated-Taylor block encoding -/

section Prepare

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- The Eq. (23) cascade lifted to the full Taylor workspace. -/
def cascLift (K L : ℕ) (Sys : Type*) [DecidableEq Sys] (θ : Fin K → ℝ) :
    Circuit (TTWs K L Sys) :=
  (cascWord K θ).map (liftOrdStep K L Sys)

/-- The lifted cascade carries exactly `K` macro gates. -/
theorem cascLiftCnt (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) :
    GateCount (cascLift K L Sys θ) = K := by
  rw [cascLift, (liftOrdStepCnt K L Sys (cascWord K θ)).1, cascCnt]

/-- The lifted cascade makes no oracle queries. -/
theorem cascLiftQC (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) :
    QueryCount (cascLift K L Sys θ) = 0 := by
  rw [cascLift, (liftOrdStepCnt K L Sys (cascWord K θ)).2, cascQC]

/-- The lifted cascade is a unitary circuit. -/
theorem cascLiftUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) : IsUnitaryCircuit (cascLift K L Sys θ) :=
  liftOrdStepUni K L Sys _ (cascUni K θ)

/-- The PREPARE word `B` of Eq. (23) as an actual serial composition: the unary
rotation cascade on the order register, then one load macro per index register, both
lifted to the full workspace. -/
def prepareWord (K L : ℕ) (Sys : Type*) [DecidableEq Sys] (θ : Fin K → ℝ)
    (bL : Matrix (Fin L) (Fin L) ℂ) : Circuit (TTWs K L Sys) :=
  cascLift K L Sys θ ++ loadsWord K L Sys bL

/-- Eq. (23), PREPARE side, measured: the composed PREPARE word carries exactly
`K + K` macro gates — `K` cascade rotations plus `K` index loads — derived from the
serial composition, not prescribed. -/
theorem prepareCnt (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    GateCount (prepareWord K L Sys θ bL) = K + K := by
  rw [prepareWord, gateCount_append, cascLiftCnt, loadsCnt]

/-- The composed PREPARE word makes no oracle queries. -/
theorem prepareQC (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    QueryCount (prepareWord K L Sys θ bL) = 0 := by
  rw [prepareWord, queryCount_append, cascLiftQC, loadsQC]

/-- The composed PREPARE word is a unitary circuit. -/
theorem prepareUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) {bL : Matrix (Fin L) (Fin L) ℂ}
    (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    IsUnitaryCircuit (prepareWord K L Sys θ bL) :=
  (isUnitaryCircuit_append _ _).mpr ⟨cascLiftUni K L Sys θ, loadsUni K L Sys hL⟩

/-- The composed PREPARE denotation factors exactly as the serial composition
promises: the load stage matrix times the lifted cascade matrix. -/
theorem prepareDen (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (prepareWord K L Sys θ bL)
      = Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (loadsWord K L Sys bL)
        * liftOrd K L Sys
            (Denote (1 : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) (cascWord K θ)) := by
  rw [prepareWord, denote_append, cascLift, denoteMapLift]

/-- The PREPARE denotation is unitary: operational unitarity from the composition
and the contract-carried step proofs. -/
theorem prepareUniDen (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) {bL : Matrix (Fin L) (Fin L) ℂ}
    (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (prepareWord K L Sys θ bL)
      ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ :=
  denote_unitary _ (Submonoid.one_mem _) (prepareUni K L Sys θ hL)

end Prepare

/-! ### The SELECT word and its LCU denotation -/

section Select

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- One per-position select step: controlled on order wire `i` reading `true`, apply
the term unitary `V (μ i)` selected by the `i`-th index digit on the system;
identity everywhere else. Block-diagonal in the order-and-index read. -/
def selStep (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) (i : Fin K) :
    Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  Matrix.blockDiagonal fun om : ((Fin K → Bool) × TTIdx K L) =>
    if om.1 i then V (om.2 i) else 1

/-- A select step over a unitary term family is unitary: block-diagonal with
unitary blocks. -/
theorem selStepUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) (hV : ∀ ℓ, V ℓ ∈ Matrix.unitaryGroup Sys ℂ)
    (i : Fin K) :
    selStep K L Sys V i ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ := by
  have hblock : ∀ om : ((Fin K → Bool) × TTIdx K L),
      ((if om.1 i then V (om.2 i) else (1 : Matrix Sys Sys ℂ))ᴴ *
        (if om.1 i then V (om.2 i) else 1)) = 1 := by
    intro om
    rcases hbi : om.1 i with _ | _
    · simp
    · have hU := (Matrix.mem_unitaryGroup_iff' (A := V (om.2 i))).mp (hV (om.2 i))
      rw [Matrix.star_eq_conjTranspose] at hU
      simpa [hbi] using hU
  rw [Matrix.mem_unitaryGroup_iff',
    show selStep K L Sys V i = Matrix.blockDiagonal
      (fun om : ((Fin K → Bool) × TTIdx K L) =>
        if om.1 i then V (om.2 i) else 1) from rfl,
    Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul, funext hblock]
  exact Matrix.blockDiagonal_one

/-- The SELECT word: one select step per unary position, in position order. -/
def selectWord (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    Circuit (TTWs K L Sys) :=
  gateWord (fun i => selStep K L Sys V i) (List.finRange K)

/-- Eq. (24) structure, measured: the composed SELECT word carries exactly `K`
macro gates, one per unary position. -/
theorem selectCnt (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    GateCount (selectWord K L Sys V) = K := by
  rw [selectWord, gateWordGC, List.length_finRange]

/-- The composed SELECT word makes no oracle queries at this layer: the term
unitaries enter as macro blocks, and the oracle billing of their realization is a
separate regime (see `selBillDual` for the one-query counterpart). -/
theorem selectQC (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    QueryCount (selectWord K L Sys V) = 0 :=
  gateWordQC _ _

/-- The SELECT word is a unitary circuit over a unitary term family. -/
theorem selectUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) (hV : ∀ ℓ, V ℓ ∈ Matrix.unitaryGroup Sys ℂ) :
    IsUnitaryCircuit (selectWord K L Sys V) :=
  gateWordUni _ _ (fun i => selStepUni K L Sys V hV i)

/-- The Taylor LCU select operator: on each order-and-index read, the product of
the term unitaries over the active unary positions. -/
def taylorSelect (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  Matrix.blockDiagonal fun om : ((Fin K → Bool) × TTIdx K L) =>
    (List.finRange K).foldr
      (fun i P => P * (if om.1 i then V (om.2 i) else (1 : Matrix Sys Sys ℂ))) 1

/-- Serial products of block-diagonal steps stay block-diagonal, with the block
products folded in word order. -/
private theorem foldrBlocks (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (f : ((Fin K → Bool) × TTIdx K L) → Fin K → Matrix Sys Sys ℂ) (l : List (Fin K)) :
    l.foldr (fun i P => P * Matrix.blockDiagonal (fun om => f om i)) 1
      = Matrix.blockDiagonal (fun om => l.foldr (fun i P => P * f om i) 1) := by
  induction l with
  | nil =>
      rw [show (fun om : ((Fin K → Bool) × TTIdx K L) =>
             List.foldr (fun i P => P * f om i) 1 []) =
             (fun _ => (1 : Matrix Sys Sys ℂ)) from rfl,
        show Matrix.blockDiagonal
             (fun _ : ((Fin K → Bool) × TTIdx K L) => (1 : Matrix Sys Sys ℂ)) = 1 from
          Matrix.blockDiagonal_one]
      rfl
  | cons i l ih =>
      simp only [List.foldr_cons, ih, Matrix.blockDiagonal_mul]

/-- The composed SELECT word denotes exactly the LCU select operator: the SELECT
semantics is a theorem about the composition, not a hypothesis. -/
theorem selectDenote (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (selectWord K L Sys V)
      = taylorSelect K L Sys V := by
  rw [selectWord, gateWordDen]
  simp only [selStep]
  rw [foldrBlocks K L Sys (fun om i => if om.1 i then V (om.2 i) else 1)
    (List.finRange K)]
  rfl

/-- The SELECT denotation is unitary over a unitary term family. -/
theorem selectUniDen (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) (hV : ∀ ℓ, V ℓ ∈ Matrix.unitaryGroup Sys ℂ) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (selectWord K L Sys V)
      ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ :=
  denote_unitary _ (Submonoid.one_mem _) (selectUni K L Sys V hV)

/-- Billing duality of the same select operator: the `K`-macro composition denotes
the same matrix as a single query of the select oracle, which bills one query. The
two billings never mix: the macro word counts `K` gates and `0` queries, the query
realization counts `1` query. -/
theorem selBillDual (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    Denote (taylorSelect K L Sys V) [Step.query] = taylorSelect K L Sys V ∧
      QueryCount ([Step.query] : Circuit (TTWs K L Sys)) = 1 := by
  refine ⟨?_, rfl⟩
  rw [denote_query, denote_nil, Matrix.one_mul]

end Select

/-! ### UnitAlgebra closure: profiles from the composed words -/

section Counts

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- The PREPARE profile is the serial composition of the cascade and load profiles:
same-artifact counting through `profAppend`. -/
theorem prepareProf (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    wordProfile (prepareWord K L Sys θ bL)
      = serial (wordProfile (cascLift K L Sys θ)) (wordProfile (loadsWord K L Sys bL)) :=
  Qatlib.Concepts.CostModels.CountBridge.profAppend _ _

/-- The PREPARE macro-gate field is the serial sum of the two stage counts. -/
theorem prepareMacroAdd (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    (wordProfile (prepareWord K L Sys θ bL)).macroGates
      = some (GateCount (cascLift K L Sys θ) + GateCount (loadsWord K L Sys bL)) := by
  rw [prepareProf, serialMacroAdd (wordProfileG _) (wordProfileG _)]

/-- The PREPARE macro-gate field is the measured composed count `K + K`. -/
theorem prepareMacro (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    (wordProfile (prepareWord K L Sys θ bL)).macroGates = some (K + K) := by
  rw [wordProfileG, prepareCnt]

/-- The SELECT macro-gate field is the measured composed count `K`. -/
theorem selectMacro (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    (wordProfile (selectWord K L Sys V)).macroGates = some K := by
  rw [wordProfileG, selectCnt]

/-- The PREPARE query field is the measured composed zero. -/
theorem prepareQ (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    (wordProfile (prepareWord K L Sys θ bL)).queries = some 0 := by
  rw [wordProfileQ, prepareQC]

/-- The SELECT query field is the measured composed zero. -/
theorem selectQ (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    (wordProfile (selectWord K L Sys V)).queries = some 0 := by
  rw [wordProfileQ, selectQC]

end Counts

/-! ### MacroUnit expansion and the Eq. (23)/(24) ledger closure -/

section Units

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- Under any expansion unit, the elementary count of PREPARE is the unit price of
the measured `K + K` macro composition. -/
theorem prepUnit (u : MacroUnit) (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) :
    macroCounts u (GateCount (prepareWord K L Sys θ bL))
      = (K + K) * u.basic := by
  rw [prepareCnt]
  rfl

/-- Under any expansion unit, the elementary count of SELECT is the unit price of
the measured `K` macro composition. -/
theorem selUnit (u : MacroUnit) (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) :
    macroCounts u (GateCount (selectWord K L Sys V)) = K * u.basic := by
  rw [selectCnt]
  rfl

/-- Eq. (23) closure: with the cascade rotations priced at one elementary gate and
each index-register load priced at `L` gates (the per-load cost cited from the
source's reference [22], carried here as an explicit unit hypothesis), the
composition-measured counts expand exactly to the prescribed ledger `prepGates`. -/
theorem prepEq23 (uR uL : MacroUnit) (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ)
    (hR : uR.basic = 1) (hL : uL.basic = L) :
    macroCounts uR (GateCount (cascLift K L Sys θ))
      + macroCounts uL (GateCount (loadsWord K L Sys bL))
        = prepGates K L := by
  rw [cascLiftCnt, loadsCnt]
  show K * uR.basic + K * uL.basic = prepGates K L
  rw [hR, hL, prepGates]
  simp

/-- Eq. (24) closure: with one select macro priced at `L * (n + ⌈log₂ L⌉)`
elementary gates (the controlled `select(H)` realization for Pauli-product terms,
carried as an explicit unit hypothesis), the composition-measured count expands
exactly to the prescribed ledger `selectVGates`. -/
theorem selEq24 (u : MacroUnit) (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (V : Fin L → Matrix Sys Sys ℂ) (n : ℕ) (hL1 : 1 ≤ L)
    (hu : u.basic = L * (n + Nat.clog 2 L)) :
    macroCounts u (GateCount (selectWord K L Sys V))
      = selectVGates K L n := by
  rw [selectCnt]
  show K * u.basic = selectVGates K L n
  rw [hu, selectVGates, Nat.max_eq_right hL1]

end Units

/-! ### Eq. (22): the register-width ledger as explicit hypotheses -/

section Ledger

/-- The workspace ancilla budget — `K` unary order wires plus `K` index registers at
width `⌈log₂ L⌉` — is exactly the Eq. (22) exact ledger `ancillaBits`. -/
theorem ancLedger (K L : ℕ) : K + K * Nat.clog 2 L = ancillaBits K L :=
  rfl

/-- The Eq. (22) register-width ledger as explicit hypotheses: each `Fin L` index
digit is realizable in `w` binary wires with `L ≤ 2 ^ w`, and under that hypothesis
the workspace ancilla budget equals the exact ledger `ancillaBits`. The binary
realization and physical width transport are hypotheses of the ledger, not
constructions of this slice. -/
theorem wsLedger (K L : ℕ) :
    ∃ w : ℕ, L ≤ 2 ^ w ∧ K + K * w = ancillaBits K L :=
  ⟨Nat.clog 2 L, Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) L, rfl⟩

end Ledger

end

end Qatlib.Papers.TruncTaylor14.PrepareSelectCount

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.PrepareSelectCount
public import Qatlib.Concepts.CircuitLang.XorOracle
public import Qatlib.Concepts.CircuitLang.WordOps
public import Qatlib.Foundations.OperatorErrors.OperatorError

@[expose] public section

/-!
# Oracle realization of the SELECT unitaries and the per-segment resource ledger

Fixed source: Berry, Childs, Cleve, Kothari and Somma, arXiv:1412.4687v1, pp. 3-4,
Eqs. (22)-(25). For the truncated-Taylor resource ledger, the term unitaries `V` of the SELECT
composition, carried abstractly by `PrepareSelectCount`, are now realized over
the involutive oracle interface: a `TermOracle` is a family of concrete involutions of
the system register, one per term index, exactly as the standard XOR oracle is
`permMatrix (xorInto f)`; `xorOracle_is_termV` records that the XOR oracle is
literally the one-term instance of this contract. The select-step oracle
`selOra` is the controlled select step over the realized family, and one query to it
acts on a workspace basis state by the concrete term permutation selected by the
address read (`selOra_ket`).

The SELECT unitaries' oracle access is an actual query word: per position, a
one-query word denotes exactly the select-step oracle (`selQueryRealize`,
`selOraDual`); the composed oracle SELECT word `selectOraWord` bills `K`
term-oracle queries and zero gates, all measured from the composition. The
per-ℓ bills `qPerL` partition those queries at every index read
(`qPerL_total`, `qBillSum`), and under the Eq. (25) per-query synthesis price
the measured query count expands exactly to `sparseSegGates`
(`selectOraEq25`).

The end-to-end per-segment ledger assembles PREPARE, the SELECT oracle word,
the unprepare word `B†` (the word-level adjoint of the PREPARE composition), and
a compiled reflection word lifted to the workspace: `segmentWord` (SELECT as
one coarse query, whose denotation is the composed segment operator
`R · B† · SELECT · B`) and `segmentOraWord` (SELECT as the fine `K`-query word,
whose independent oracle-query billing is measured off the composition). All
counts close into the `CostProfile` algebra through `wordProfile`,
`profAppend`, and `serialMacroAdd`/`serialQueryAdd`, and into elementary
ledgers through the `MacroUnit` expansion (`segLedgerEq`).

The first ring of finite-bit synthesis is included at the cascade base: an
`ApproxGate` contract targeting the leading rotation yields a unitary word
billing exactly like the exact contract word, with an entrywise synthesis bound
(`approxWordEntry`). As ever, `ApproxGate` is an existence statement; no
compiler is constructed.

Not claimed here: compilation of the term permutations into elementary gates or
T-counts (the per-`ℓ` synthesis prices stay explicit unit hypotheses);
oblivious amplitude amplification correctness, spectral compression, or error
bounds of the segment operator; multi-segment composition; and any claim that a
single static oracle composes the fine select word (a static oracle yields a
power, `selectOraPow`; the exact select semantics is per position).
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.WordRelabel
open Qatlib.Concepts.CircuitLang.WordOps
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Concepts.GateKit.GateContract
open Qatlib.Concepts.GateKit
open Qatlib.Concepts.CostModels.CountBridge
open Qatlib.Concepts.CostModels.UnitAlgebra
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Papers.TruncTaylor14.ResourceCount
open Qatlib.Papers.TruncTaylor14.PrepareSelectCount

open scoped Matrix

namespace Qatlib.Papers.TruncTaylor14.PrepareSelectOracle

noncomputable section

/-! ### The involutive term-oracle contract -/

section Terms

variable {L : ℕ} {Sys : Type*}

/-- The sparse term-oracle contract: a family of concrete
involutions of the system register, one per term index. The involutive action
plays the role of `xorInto` in the standard XOR oracle: each term unitary is the
associated permutation matrix, exactly as `xorOracle f` is `permMatrix (xorInto f)`.
No compilation of these permutations into elementary gates is claimed; they are
the oracle-access primitives of this module. -/
structure TermOracle (L : ℕ) (Sys : Type*) where
  /-- The concrete involutive action of term `ℓ` on the system register. -/
  σ : Fin L → Sys → Sys
  /-- Every term action is an involution, so every term unitary is a
  permutation matrix. -/
  invol : ∀ ℓ : Fin L, Function.Involutive (σ ℓ)

variable [Fintype Sys] [DecidableEq Sys]

/-- The term unitary family realized concretely as permutation matrices over
the term contract. -/
def termV (O : TermOracle L Sys) (ℓ : Fin L) : Matrix Sys Sys ℂ :=
  permMatrix (O.σ ℓ)

/-- One realized term unitary sends a basis ket to the ket of the term action. -/
theorem termV_ket (O : TermOracle L Sys) (ℓ : Fin L) (j : Sys) :
    termV O ℓ *ᵥ Ket j = Ket (O.σ ℓ j) :=
  applyGate_permMatrix_ket (O.invol ℓ) j

/-- Every realized term unitary is a permutation matrix, hence unitary. -/
theorem termV_uni (O : TermOracle L Sys) (ℓ : Fin L) :
    termV O ℓ ∈ Matrix.unitaryGroup Sys ℂ :=
  permMatrix_unitary (O.invol ℓ)

/-- The whole realized term family is unitary. -/
theorem termV_family (O : TermOracle L Sys) :
    ∀ ℓ : Fin L, termV O ℓ ∈ Matrix.unitaryGroup Sys ℂ :=
  fun ℓ => termV_uni O ℓ

/-- Consistency with the XOR contract: the standard XOR oracle is exactly the
`ℓ = 0` term unitary of a one-term oracle on its own register. The oracle
realization of SELECT below therefore extends the very interface fixed by
`XorOracle`, not a new oracle model. -/
theorem xorOracle_is_termV {a w : ℕ} (f : Addr a → Bool) :
    termV (⟨fun _ => xorInto f, fun _ => xorInto_inv f⟩ : TermOracle 1 (OReg a w))
        ⟨0, by omega⟩ = xorOracle f :=
  rfl

end Terms

/-! ### The SELECT-step oracle and its query words -/

section SelectOracle

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- The workspace select-step oracle over the term contract: the controlled select
step matrix with the term family realized concretely as permutation matrices. -/
def selOra (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (O : TermOracle L Sys) (i : Fin K) :
    Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ :=
  selStep K L Sys (termV O) i

/-- The select-step oracle is unitary: block-diagonal over the realized term
family. -/
theorem selOra_uni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (i : Fin K) :
    selOra K L Sys O i ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ :=
  selStepUni K L Sys (termV O) (termV_family O) i

/-- The per-read action of the select-step oracle: the term involution selected
by the address read (order wire `i` hot, digit `μ i`), the identity on cold
reads. -/
def selOraPerm (K L : ℕ) (Sys : Type*)
    (O : TermOracle L Sys) (i : Fin K)
    (om : (Fin K → Bool) × TTIdx K L) : Sys → Sys :=
  if om.1 i then O.σ (om.2 i) else id

/-- Every per-read action is an involution. -/
theorem selOraPerm_invol (K L : ℕ) (Sys : Type*)
    (O : TermOracle L Sys) (i : Fin K)
    (om : (Fin K → Bool) × TTIdx K L) :
    Function.Involutive (selOraPerm K L Sys O i om) := by
  unfold selOraPerm
  split
  · exact O.invol (om.2 i)
  · exact fun x => rfl

private theorem permMatrix_id' {I : Type*} [DecidableEq I] :
    permMatrix (id : I → I) = (1 : Matrix I I ℂ) := by
  ext a b
  simp [permMatrix, Matrix.one_apply]

omit [Fintype Sys] in
/-- An identity-vs-permutation conditional is the permutation matrix of the
conditional action. -/
theorem if_termV_permMatrix (O : TermOracle L Sys) (c : Bool) (ℓ : Fin L) :
    (if c then termV O ℓ else (1 : Matrix Sys Sys ℂ))
      = permMatrix (if c then O.σ ℓ else id) := by
  by_cases h : c
  · simp [h, termV]
  · simp [h, permMatrix_id']

/-- The select-step oracle is the block-diagonal matrix of the per-read term
permutations: one query applies exactly one concrete term action. -/
theorem selOra_eq (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (O : TermOracle L Sys) (i : Fin K) :
    selOra K L Sys O i
      = Matrix.blockDiagonal fun om : ((Fin K → Bool) × TTIdx K L) =>
          permMatrix (selOraPerm K L Sys O i om) := by
  have hfun : (fun om : ((Fin K → Bool) × TTIdx K L) =>
        if om.1 i then termV O (om.2 i) else (1 : Matrix Sys Sys ℂ))
      = fun om : ((Fin K → Bool) × TTIdx K L) =>
          permMatrix (selOraPerm K L Sys O i om) := by
    funext om
    exact if_termV_permMatrix O (om.1 i) (om.2 i)
  show Matrix.blockDiagonal (fun om : ((Fin K → Bool) × TTIdx K L) =>
        if om.1 i then termV O (om.2 i) else (1 : Matrix Sys Sys ℂ))
      = Matrix.blockDiagonal (fun om : ((Fin K → Bool) × TTIdx K L) =>
          permMatrix (selOraPerm K L Sys O i om))
  rw [hfun]

private theorem blockDiagKetPerm {A : Type*} [Fintype A] [DecidableEq A]
    (τ : A → Sys → Sys) (s : Sys) (a : A) :
    (Matrix.blockDiagonal fun a' => permMatrix (τ a')) *ᵥ Ket (s, a)
      = Ket (τ a s, a) := by
  funext x
  obtain ⟨x1, x2⟩ := x
  show ∑ y : Sys × A, (Matrix.blockDiagonal (fun a' => permMatrix (τ a')) (x1, x2) y)
      * (Ket (s, a) y) = Ket (τ a s, a) (x1, x2)
  rw [Finset.sum_eq_single (s, a)]
  · by_cases h2 : x2 = a
    · subst x2
      simp only [Matrix.blockDiagonal_apply, Qatlib.Foundations.PureStateMath.Ket,
        permMatrix]
      by_cases h1 : x1 = τ a s <;> simp_all
    · simp only [Matrix.blockDiagonal_apply, Qatlib.Foundations.PureStateMath.Ket,
        permMatrix]
      simp_all
  · intro y _ hy
    simp [Qatlib.Foundations.PureStateMath.Ket, hy]
  · intro h
    exact absurd (Finset.mem_univ (s, a)) h

/-- The concrete oracle action on a workspace basis state: apply the selected
term permutation, keep the order and index read. -/
def selOraAct (K L : ℕ) (Sys : Type*)
    (O : TermOracle L Sys) (i : Fin K) (x : TTWs K L Sys) : TTWs K L Sys :=
  (selOraPerm K L Sys O i x.2 x.1, x.2)

/-- Entry form of the concrete oracle action. -/
theorem selOraAct_eq (K L : ℕ) (Sys : Type*)
    (O : TermOracle L Sys) (i : Fin K) (x : TTWs K L Sys) :
    selOraAct K L Sys O i x
      = (if x.2.1 i then O.σ (x.2.2 i) x.1 else x.1, x.2) := by
  rw [selOraAct]
  by_cases h : x.2.1 i <;> simp [h, selOraPerm]

/-- The concrete oracle semantics of one select query: on a workspace basis
state with order read `om`, one query applies exactly the term permutation
selected by the address block — wire `i` hot and digit `μ i = ℓ` — and fixes
cold reads. This is the `V_ℓ` oracle realization; the SELECT semantics under
oracle access is a theorem about the matrix, not a hypothesis. -/
theorem selOra_ket (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (i : Fin K) (x : TTWs K L Sys) :
    selOra K L Sys O i *ᵥ Ket x = Ket (selOraAct K L Sys O i x) := by
  rw [selOra_eq]
  exact blockDiagKetPerm (selOraPerm K L Sys O i) x.1 x.2

/-! #### Serial query words -/

variable {ι : Type*} {I : Type*} [Fintype I] [DecidableEq I]

/-- The serial oracle-query word over an index list: one query step per entry. -/
def queryWord (l : List ι) : Circuit I :=
  l.map (fun _ => Step.query)

omit [Fintype I] [DecidableEq I] in
/-- Prepending an index prepends exactly one oracle query instruction. -/
theorem queryWordCons (i : ι) (l : List ι) :
    queryWord (I := I) (i :: l) = Step.query :: queryWord (I := I) l :=
  rfl

omit [Fintype I] [DecidableEq I] in
/-- Measured: a serial query word carries no explicit gate steps. -/
theorem queryWordGC (l : List ι) : GateCount (queryWord (I := I) l) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [queryWordCons, gateCount_query]
      exact ih

omit [Fintype I] [DecidableEq I] in
/-- Measured: a serial query word bills one query per list entry. -/
theorem queryWordQC (l : List ι) : QueryCount (queryWord (I := I) l) = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [queryWordCons, queryCount_query, ih, List.length_cons]

/-- A query word is a unitary circuit: it has no explicit gate steps. -/
theorem queryWordUni (l : List ι) : IsUnitaryCircuit (queryWord (I := I) l) := by
  induction l with
  | nil => exact isUnitaryCircuit_nil
  | cons i l ih =>
      rw [queryWordCons]
      exact (isUnitaryCircuit_query _).mpr ih

/-- Under any single static oracle, a serial query word denotes a power of that
oracle. A static oracle cannot realize the position-dependent select; the exact
select semantics is per position (`selQueryRealize`). -/
theorem queryWordDen (oracle : Matrix I I ℂ) (l : List ι) :
    Denote oracle (queryWord (I := I) l) = oracle ^ l.length := by
  induction l with
  | nil =>
      rw [show queryWord (I := I) [] = [] from rfl, denote_nil, List.length_nil, pow_zero]
  | cons i l ih => rw [queryWordCons, denote_query, ih, List.length_cons, pow_succ]

/-! #### Per-position realization and the composed oracle SELECT word -/

/-- The per-position oracle realization: the select-step unitary is the
denotation of an actual one-query word, billing one oracle query and no gates. -/
theorem selQueryRealize (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (i : Fin K) :
    Denote (selOra K L Sys O i) [Step.query] = selOra K L Sys O i ∧
      QueryCount ([Step.query] : Circuit (TTWs K L Sys)) = 1 ∧
      GateCount ([Step.query] : Circuit (TTWs K L Sys)) = 0 :=
  ⟨denoteQOne _, rfl, rfl⟩

/-- Billing duality at one unary position: the same select-step operator is the
denotation of a one-gate macro word and of a one-query oracle word. The two
billings never mix. -/
theorem selOraDual (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (i : Fin K) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
        [Step.gate (selOra K L Sys O i)] = selOra K L Sys O i ∧
      GateCount ([Step.gate (selOra K L Sys O i)] : Circuit (TTWs K L Sys)) = 1 ∧
      Denote (selOra K L Sys O i) [Step.query] = selOra K L Sys O i ∧
      QueryCount ([Step.query] : Circuit (TTWs K L Sys)) = 1 := by
  refine ⟨?_, rfl, denoteQOne _, rfl⟩
  rw [denote_gate, denote_nil, Matrix.one_mul]

/-- The composed oracle SELECT word: one term-oracle query per unary position,
in position order. The word is a pure query skeleton — the term oracle enters
at denotation time — and all of its counts are measured off this composition. -/
def selectOraWord (K L : ℕ) (Sys : Type*) :
    Circuit (TTWs K L Sys) :=
  queryWord (List.finRange K)

/-- Measured: the composed oracle SELECT word bills exactly `K` term-oracle
queries, one per unary position. -/
theorem selectOraQC (K L : ℕ) (Sys : Type*) :
    QueryCount (selectOraWord K L Sys) = K := by
  rw [selectOraWord, queryWordQC, List.length_finRange]

/-- Measured: the composed oracle SELECT word carries no explicit gate steps. -/
theorem selectOraGC (K L : ℕ) (Sys : Type*) :
    GateCount (selectOraWord K L Sys) = 0 :=
  queryWordGC _

/-- The composed oracle SELECT word is a unitary circuit. -/
theorem selectOraUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys] :
    IsUnitaryCircuit (selectOraWord K L Sys) :=
  queryWordUni _

/-- Under any single static oracle the composed word denotes a `K`-th power;
the select semantics is realized per position (`selQueryRealize`), which is the
independent per-position billing. -/
theorem selectOraPow (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (oracle : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) :
    Denote oracle (selectOraWord K L Sys) = oracle ^ K := by
  rw [selectOraWord, queryWordDen, List.length_finRange]

/-! #### Per-ℓ oracle-query billing -/

/-- The per-ℓ query bill at index read `μ`: the number of unary positions whose
digit equals `ℓ`. -/
def qPerL (K L : ℕ) (μ : TTIdx K L) (ℓ : Fin L) : ℕ :=
  ((List.finRange K).filter (fun i => decide (μ i = ℓ))).length

private theorem filterLenSum (K L : ℕ) (μ : TTIdx K L) (l : List (Fin K)) :
    ∑ ℓ : Fin L, ((l.filter (fun i => decide (μ i = ℓ))).length) = l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have hstep : ∀ ℓ : Fin L,
          (((i :: l).filter (fun j => decide (μ j = ℓ))).length)
            = (if μ i = ℓ then 1 else 0)
              + ((l.filter (fun j => decide (μ j = ℓ))).length) := by
        intro ℓ
        by_cases h : μ i = ℓ <;> simp [h, Nat.add_comm]
      rw [Finset.sum_congr rfl (fun ℓ _ => hstep ℓ), Finset.sum_add_distrib]
      have hone : ∑ ℓ : Fin L, (if μ i = ℓ then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single (μ i)]
        · simp
        · intro ℓ _ hne
          have hne' : ¬(μ i = ℓ) := fun h => hne h.symm
          simp [hne']
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hone, ih, List.length_cons]
      omega

/-- The per-ℓ bills partition the composed word's queries: summing over the
term indices counts every unary position exactly once. -/
theorem qPerL_total (K L : ℕ) (μ : TTIdx K L) : ∑ ℓ : Fin L, qPerL K L μ ℓ = K := by
  simp only [qPerL]
  rw [filterLenSum K L μ (List.finRange K), List.length_finRange]

/-- The per-ℓ sub-word of the composed oracle SELECT word at index read `μ`:
the serial query word over exactly the positions billed to `ℓ`. -/
def qBillWord (K L : ℕ) (Sys : Type*)
    (μ : TTIdx K L) (ℓ : Fin L) : Circuit (TTWs K L Sys) :=
  queryWord ((List.finRange K).filter (fun i => decide (μ i = ℓ)))

/-- The measured query count of the per-ℓ sub-word is the per-ℓ bill. -/
theorem qBillQC (K L : ℕ) (Sys : Type*)
    (μ : TTIdx K L) (ℓ : Fin L) :
    QueryCount (qBillWord K L Sys μ ℓ) = qPerL K L μ ℓ :=
  queryWordQC _

/-- The per-ℓ sub-words together bill exactly the composed word's `K`
term-oracle queries. -/
theorem qBillSum (K L : ℕ) (Sys : Type*)
    (μ : TTIdx K L) :
    ∑ ℓ : Fin L, QueryCount (qBillWord K L Sys μ ℓ) = K := by
  rw [Finset.sum_congr rfl (fun ℓ _ => qBillQC K L Sys μ ℓ), qPerL_total]

end SelectOracle

/-! ### The unprepare word: word-level adjoint of PREPARE -/

section Adjoints

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- The adjoint word counts every original instruction as one explicit gate
step, queries included (a daggered query is the oracle adjoint, a gate step). -/
theorem wordAdjGC {I : Type*} (oadj : Matrix I I ℂ) (C : Circuit I) :
    GateCount (wordAdj oadj C) = GateCount C + QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U =>
          rw [wordAdjCons, gateCount_append, ih, gateCount_gate, queryCount_gate]
          have h1 : GateCount [stepAdj oadj (Step.gate U)] = 1 := rfl
          rw [h1]
          omega
      | query =>
          rw [wordAdjCons, gateCount_append, ih, gateCount_query, queryCount_query]
          have h1 : GateCount [stepAdj oadj (Step.query)] = 1 := rfl
          rw [h1]
          omega

/-- A daggered word makes no oracle queries: every step became an explicit
gate step. -/
theorem wordAdjQC {I : Type*} (oadj : Matrix I I ℂ) (C : Circuit I) :
    QueryCount (wordAdj oadj C) = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      rw [wordAdjCons, queryCount_append, ih]
      cases s <;> rfl

/-- The word-level adjoint of a query-free unitary word is a unitary circuit:
adjoints of unitary gates are unitary, and there are no queries to dagger. -/
theorem wordAdjUniFree {I : Type*} [Fintype I] [DecidableEq I] (oadj : Matrix I I ℂ)
    (C : Circuit I) (hC : IsUnitaryCircuit C) (hq : QueryCount C = 0) :
    IsUnitaryCircuit (wordAdj oadj C) := by
  revert hC hq
  induction C with
  | nil => intro _ _; exact isUnitaryCircuit_nil
  | cons s C ih =>
      intro hC hq
      cases s with
      | gate U =>
          obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
          rw [wordAdjCons, isUnitaryCircuit_append]
          exact ⟨ih hC' hq, (isUnitaryCircuit_gate _ _).mpr
            ⟨conjTranspose_mem_unitaryGroup hU, isUnitaryCircuit_nil⟩⟩
      | query =>
          have hq' : QueryCount (Step.query :: C) = QueryCount C + 1 := rfl
          rw [hq'] at hq
          omega

/-- The word-level adjoint of a concatenation is the reversed concatenation of
the adjoints. -/
theorem wordAdjAppend {I : Type*} (oadj : Matrix I I ℂ) (C D : Circuit I) :
    wordAdj oadj (C ++ D) = wordAdj oadj D ++ wordAdj oadj C := by
  simp [wordAdj, List.map_append, List.reverse_append]

/-- The cascade-stage adjoint at the select-oracle denotation. -/
def cascAdj (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (θ : Fin K → ℝ) : Circuit (TTWs K L Sys) :=
  wordAdj (taylorSelect K L Sys (termV O)).conjTranspose (cascLift K L Sys θ)

/-- The load-stage adjoint at the select-oracle denotation. -/
def loadsAdj (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (bL : Matrix (Fin L) (Fin L) ℂ) : Circuit (TTWs K L Sys) :=
  wordAdj (taylorSelect K L Sys (termV O)).conjTranspose (loadsWord K L Sys bL)

/-- The unprepare word `B†`: the word-level adjoint of the PREPARE
composition, split so that the load and cascade stages bill separately. -/
def prepareAdj (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys) :
    Circuit (TTWs K L Sys) :=
  loadsAdj K L Sys O bL ++ cascAdj K L Sys O θ

/-- The split unprepare word is exactly the word-level adjoint of the composed
PREPARE word. -/
theorem prepareAdj_eq (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys) :
    prepareAdj K L Sys θ bL O
      = wordAdj (taylorSelect K L Sys (termV O)).conjTranspose
          (prepareWord K L Sys θ bL) := by
  rw [prepareAdj, loadsAdj, cascAdj, ← wordAdjAppend, prepareWord]

/-- Measured: the cascade adjoint bills exactly the `K` cascade rotations. -/
theorem cascAdjGC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (θ : Fin K → ℝ) :
    GateCount (cascAdj K L Sys O θ) = K := by
  rw [cascAdj, wordAdjGC, cascLiftCnt, cascLiftQC]
  rfl

/-- The cascade adjoint makes no oracle queries. -/
theorem cascAdjQC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (θ : Fin K → ℝ) :
    QueryCount (cascAdj K L Sys O θ) = 0 :=
  wordAdjQC _ _

/-- The cascade adjoint is a unitary circuit. -/
theorem cascAdjUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (θ : Fin K → ℝ) :
    IsUnitaryCircuit (cascAdj K L Sys O θ) :=
  wordAdjUniFree _ _ (cascLiftUni K L Sys θ) (cascLiftQC K L Sys θ)

/-- Measured: the load adjoint bills exactly the `K` index loads. -/
theorem loadsAdjGC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (bL : Matrix (Fin L) (Fin L) ℂ) :
    GateCount (loadsAdj K L Sys O bL) = K := by
  rw [loadsAdj, wordAdjGC, loadsCnt, loadsQC]
  rfl

/-- The load adjoint makes no oracle queries. -/
theorem loadsAdjQC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) (bL : Matrix (Fin L) (Fin L) ℂ) :
    QueryCount (loadsAdj K L Sys O bL) = 0 :=
  wordAdjQC _ _

/-- The load adjoint is a unitary circuit whenever the load matrix is. -/
theorem loadsAdjUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (O : TermOracle L Sys) {bL : Matrix (Fin L) (Fin L) ℂ}
    (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    IsUnitaryCircuit (loadsAdj K L Sys O bL) :=
  wordAdjUniFree _ _ (loadsUni K L Sys hL) (loadsQC K L Sys bL)

/-- Measured: the unprepare word bills exactly the `K + K` macro gates of the
PREPARE composition, daggered. -/
theorem prepareAdjGC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys) :
    GateCount (prepareAdj K L Sys θ bL O) = K + K := by
  rw [prepareAdj, gateCount_append, loadsAdjGC, cascAdjGC]

/-- The unprepare word makes no oracle queries. -/
theorem prepareAdjQC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys) :
    QueryCount (prepareAdj K L Sys θ bL O) = 0 := by
  rw [prepareAdj, queryCount_append, loadsAdjQC, cascAdjQC]

/-- The unprepare word is a unitary circuit whenever the load matrix is. -/
theorem prepareAdjUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ) :
    IsUnitaryCircuit (prepareAdj K L Sys θ bL O) :=
  (isUnitaryCircuit_append _ _).mpr
    ⟨loadsAdjUni K L Sys O hL, cascAdjUni K L Sys O θ⟩

/-- The unprepare denotation is the conjugate transpose of the PREPARE
denotation: the word-level adjoint is exact, and PREPARE being query-free, the
statement is oracle-independent. -/
theorem prepareAdjDen (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys) :
    Denote (taylorSelect K L Sys (termV O)) (prepareAdj K L Sys θ bL O)
      = (Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
          (prepareWord K L Sys θ bL)).conjTranspose := by
  have hfree : Denote (taylorSelect K L Sys (termV O)) (prepareWord K L Sys θ bL)
      = Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
          (prepareWord K L Sys θ bL) :=
    denoteFree (prepareQC K L Sys θ bL) _ _
  rw [prepareAdj_eq, denoteAdj, congrArg Matrix.conjTranspose hfree]

end Adjoints

/-! ### The reflection segment lifted to the workspace -/

section Reflection

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- Denotation commutes with the workspace lift of order-register words. -/
theorem denoteLiftOrd (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (C : Circuit (Fin K → Bool)) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
        (C.map (liftOrdStep K L Sys))
      = liftOrd K L Sys
          (Denote (1 : Matrix (Fin K → Bool) (Fin K → Bool) ℂ) C) := by
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

/-- The reflection segment: a compiled reflection word on the unary order
register, lifted instruction by instruction to the full Taylor workspace. -/
def reflLift (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (gs : List (ReflectionGate K)) : Circuit (TTWs K L Sys) :=
  (reflectionCompile gs).map (liftOrdStep K L Sys)

/-- Measured: the reflection segment bills one gate per reflection instruction. -/
theorem reflLiftGC (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (gs : List (ReflectionGate K)) :
    GateCount (reflLift K L Sys gs) = gs.length := by
  rw [reflLift, (liftOrdStepCnt K L Sys (reflectionCompile gs)).1,
    gateCount_reflectionCompile]

/-- Measured: the reflection segment makes no oracle queries. -/
theorem reflLiftQC (K L : ℕ) (Sys : Type*) [DecidableEq Sys]
    (gs : List (ReflectionGate K)) :
    QueryCount (reflLift K L Sys gs) = 0 := by
  rw [reflLift, (liftOrdStepCnt K L Sys (reflectionCompile gs)).2,
    queryCount_reflectionCompile]

/-- A legal reflection word lifts to a unitary workspace circuit. -/
theorem reflLiftUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    {gs : List (ReflectionGate K)} (hgs : reflectionLegal gs) :
    IsUnitaryCircuit (reflLift K L Sys gs) :=
  liftOrdStepUni K L Sys _ (reflUniCirc gs hgs)

/-- The lifted reflection denotation is the workspace lift of the public
reflection program matrix. -/
theorem reflLiftDen (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (gs : List (ReflectionGate K)) :
    Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) (reflLift K L Sys gs)
      = liftOrd K L Sys (reflectionProgramMatrix gs) := by
  rw [reflLift, denoteLiftOrd, denoteRefl]

/-- The lifted reflection word is query-free, hence its denotation is
oracle-independent. -/
theorem reflLiftFree (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (gs : List (ReflectionGate K))
    (oracle : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ) :
    Denote oracle (reflLift K L Sys gs)
      = Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
          (reflLift K L Sys gs) :=
  denoteFree (reflLiftQC K L Sys gs) _ _

end Reflection

/-! ### The end-to-end per-segment words and their ledgers -/

section Segment

variable {K L : ℕ} {Sys : Type*} [Fintype Sys] [DecidableEq Sys]

/-- The per-segment word with the coarse select oracle: PREPARE, one coarse
SELECT query (the whole select operator as one oracle call, the coarse side of
`selBillDual`), the unprepare word `B†`, and the lifted reflection, in
execution order. -/
def segmentWord (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) : Circuit (TTWs K L Sys) :=
  prepareWord K L Sys θ bL ++ [Step.query]
    ++ prepareAdj K L Sys θ bL O ++ reflLift K L Sys gs

/-- The per-segment word with the fine oracle SELECT: the same composition with
SELECT realized as the composed term-oracle query word. Its query count is the
independent per-ℓ billing measured off the composition. -/
def segmentOraWord (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) : Circuit (TTWs K L Sys) :=
  prepareWord K L Sys θ bL ++ selectOraWord K L Sys
    ++ prepareAdj K L Sys θ bL O ++ reflLift K L Sys gs

/-- Measured: the coarse per-segment word bills the four composed stages —
`K + K` PREPARE macros, no gate for the single coarse query, `K + K` unprepare
macros, one gate per reflection instruction. -/
theorem segmentGC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    GateCount (segmentWord K L Sys θ bL O gs)
      = K + K + ((K + K) + gs.length) := by
  rw [segmentWord]
  simp only [gateCount_append, gateCount_query, gateCount_nil, prepareCnt,
    prepareAdjGC, reflLiftGC]
  omega

/-- Measured: the coarse per-segment word makes exactly one oracle query — the
coarse select call; every other stage is query-free. -/
theorem segmentQC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    QueryCount (segmentWord K L Sys θ bL O gs) = 1 := by
  rw [segmentWord]
  simp only [queryCount_append, queryCount_query, queryCount_nil, prepareQC,
    prepareAdjQC, reflLiftQC]

/-- The coarse per-segment word is a unitary circuit over a unitary load
matrix and a legal reflection word. -/
theorem segmentUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ)
    (hgs : reflectionLegal gs) :
    IsUnitaryCircuit (segmentWord K L Sys θ bL O gs) := by
  rw [segmentWord]
  exact (isUnitaryCircuit_append _ _).mpr ⟨(isUnitaryCircuit_append _ _).mpr
    ⟨(isUnitaryCircuit_append _ _).mpr ⟨prepareUni K L Sys θ hL,
      (isUnitaryCircuit_query _).mpr isUnitaryCircuit_nil⟩,
      prepareAdjUni K L Sys θ bL O hL⟩, reflLiftUni K L Sys hgs⟩

/-- The per-segment semantics: the coarse word denotes the composed segment
operator `R · B† · SELECT · B`, with the SELECT factor the concrete-oracle
`taylorSelect` and `R` the lifted reflection program matrix. -/
theorem segmentDen (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    Denote (taylorSelect K L Sys (termV O)) (segmentWord K L Sys θ bL O gs)
      = liftOrd K L Sys (reflectionProgramMatrix gs)
        * (Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
            (prepareWord K L Sys θ bL)).conjTranspose
        * taylorSelect K L Sys (termV O)
        * Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
            (prepareWord K L Sys θ bL) := by
  have hP : Denote (taylorSelect K L Sys (termV O)) (prepareWord K L Sys θ bL)
      = Denote (1 : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
          (prepareWord K L Sys θ bL) :=
    denoteFree (prepareQC K L Sys θ bL) _ _
  have hQ : Denote (taylorSelect K L Sys (termV O))
        ([Step.query] : Circuit (TTWs K L Sys))
      = taylorSelect K L Sys (termV O) := by
    rw [denote_query, denote_nil, Matrix.one_mul]
  have hR := prepareAdjDen K L Sys θ bL O
  have hS : Denote (taylorSelect K L Sys (termV O)) (reflLift K L Sys gs)
      = liftOrd K L Sys (reflectionProgramMatrix gs) := by
    rw [reflLiftFree K L Sys gs _, reflLiftDen]
  rw [segmentWord, denote_append, denote_append, denote_append, hP, hQ, hR, hS]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- Measured: the fine per-segment word bills the same macro gates as the
coarse word — the select stage enters as queries, not gates. -/
theorem segmentOraGC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    GateCount (segmentOraWord K L Sys θ bL O gs)
      = K + K + ((K + K) + gs.length) := by
  rw [segmentOraWord, gateCount_append, gateCount_append, gateCount_append,
    prepareCnt, selectOraGC, prepareAdjGC, reflLiftGC]
  omega

/-- Measured: the fine per-segment word bills exactly the `K` term-oracle
queries of the oracle SELECT realization; every other stage is query-free. -/
theorem segmentOraQC (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    QueryCount (segmentOraWord K L Sys θ bL O gs) = K := by
  rw [segmentOraWord, queryCount_append, queryCount_append, queryCount_append,
    prepareQC, selectOraQC, prepareAdjQC, reflLiftQC]
  omega

/-- The fine per-segment word is a unitary circuit over a unitary load matrix
and a legal reflection word. -/
theorem segmentOraUni (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ)
    (hgs : reflectionLegal gs) :
    IsUnitaryCircuit (segmentOraWord K L Sys θ bL O gs) :=
  (isUnitaryCircuit_append _ _).mpr ⟨(isUnitaryCircuit_append _ _).mpr
    ⟨(isUnitaryCircuit_append _ _).mpr ⟨prepareUni K L Sys θ hL,
      selectOraUni K L Sys⟩,
      prepareAdjUni K L Sys θ bL O hL⟩, reflLiftUni K L Sys hgs⟩

/-- The coarse per-segment profile is the four-fold serial composition of the
stage profiles, through `profAppend`. -/
theorem segmentProf (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    wordProfile (segmentWord K L Sys θ bL O gs)
      = serial (wordProfile (prepareWord K L Sys θ bL))
          (serial (wordProfile ([Step.query] : Circuit (TTWs K L Sys)))
            (serial (wordProfile (prepareAdj K L Sys θ bL O))
              (wordProfile (reflLift K L Sys gs)))) := by
  rw [segmentWord, Qatlib.Concepts.CostModels.CountBridge.profAppend,
    Qatlib.Concepts.CostModels.CountBridge.profAppend,
    Qatlib.Concepts.CostModels.CountBridge.profAppend, serialAssoc, serialAssoc]

/-- The coarse per-segment macro-gate field is the measured four-stage total. -/
theorem segmentMacro (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    (wordProfile (segmentWord K L Sys θ bL O gs)).macroGates
      = some (K + K + ((K + K) + gs.length)) := by
  rw [wordProfileG, segmentGC]

/-- The coarse per-segment query field is the measured single coarse select
query. -/
theorem segmentQueries (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    (wordProfile (segmentWord K L Sys θ bL O gs)).queries = some 1 := by
  rw [wordProfileQ, segmentQC]

/-- The fine per-segment macro-gate field is the measured four-stage total. -/
theorem segmentOraMacro (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    (wordProfile (segmentOraWord K L Sys θ bL O gs)).macroGates
      = some (K + K + ((K + K) + gs.length)) := by
  rw [wordProfileG, segmentOraGC]

/-- The fine per-segment query field is the measured `K` term-oracle queries:
the independent oracle-query billing of the segment. -/
theorem segmentOraQueries (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    (wordProfile (segmentOraWord K L Sys θ bL O gs)).queries = some K := by
  rw [wordProfileQ, segmentOraQC]

/-- The per-segment billing summary: the coarse word bills one select query;
its fine realization bills `K` term-oracle queries, which the per-ℓ bills
partition at every index read. -/
theorem segmentRefine (K L : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    QueryCount (segmentWord K L Sys θ bL O gs) = 1 ∧
      QueryCount (segmentOraWord K L Sys θ bL O gs) = K ∧
      ∀ μ : TTIdx K L, ∑ ℓ : Fin L, qPerL K L μ ℓ = K :=
  ⟨segmentQC K L Sys θ bL O gs, segmentOraQC K L Sys θ bL O gs,
    fun μ => qPerL_total K L μ⟩

/-- The select-oracle ledger against the Eq. (25) sparse-segment prescription:
with one term-oracle query priced at `n + m` elementary gates (the qubit-wide
oracle work plus synthesis gates of the source's sparse-segment model, carried
as an explicit unit hypothesis), the measured `K` queries of the composed word
expand exactly to `sparseSegGates`. -/
theorem selectOraEq25 (u : MacroUnit) (K L : ℕ) (Sys : Type*)
    (n m : ℕ)
    (hu : u.basic = n + m) :
    macroCounts u (QueryCount (selectOraWord K L Sys)) = sparseSegGates K n m := by
  rw [selectOraQC, show macroCounts u K = K * u.basic from rfl, hu, sparseSegGates]

/-- The end-to-end per-segment elementary ledger: with the Eq. (23) unit prices
(rotations one gate, each load `L` gates) applied to PREPARE and to the
unprepare word stage by stage, and the reflection billed one gate per
instruction, the measured macro composition expands exactly to twice the Eq.
(23) ledger plus the reflection length. -/
theorem segLedgerEq (uR uL uF : MacroUnit) (K L : ℕ) (Sys : Type*)
    [Fintype Sys] [DecidableEq Sys] (θ : Fin K → ℝ)
    (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K))
    (hR : uR.basic = 1) (hL : uL.basic = L) (hF : uF.basic = 1) :
    macroCounts uR (GateCount (cascLift K L Sys θ))
      + macroCounts uL (GateCount (loadsWord K L Sys bL))
      + macroCounts uR (GateCount (cascAdj K L Sys O θ))
      + macroCounts uL (GateCount (loadsAdj K L Sys O bL))
      + macroCounts uF (GateCount (reflLift K L Sys gs))
      = 2 * prepGates K L + gs.length := by
  have h1 : GateCount (cascAdj K L Sys O θ) = K := cascAdjGC K L Sys O θ
  have h2 : GateCount (loadsAdj K L Sys O bL) = K := loadsAdjGC K L Sys O bL
  have h3 : GateCount (reflLift K L Sys gs) = gs.length := reflLiftGC K L Sys gs
  show macroCounts uR (GateCount (cascLift K L Sys θ))
      + macroCounts uL (GateCount (loadsWord K L Sys bL))
      + macroCounts uR (GateCount (cascAdj K L Sys O θ))
      + macroCounts uL (GateCount (loadsAdj K L Sys O bL))
      + macroCounts uF (GateCount (reflLift K L Sys gs))
      = 2 * prepGates K L + gs.length
  rw [cascLiftCnt, loadsCnt, h1, h2, h3,
    show macroCounts uR K = K * uR.basic from rfl,
    show macroCounts uL K = K * uL.basic from rfl,
    show macroCounts uF gs.length = gs.length * uF.basic from rfl,
    hR, hL, hF, prepGates]
  ring

end Segment

/-! ### Repeated segments: measured resources and stable error propagation -/

section RepeatedSegments

open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.OperatorErrors.OperatorError

/-- Repetition of a physical word denotes the corresponding matrix power. -/
theorem denote_repeat_word {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (s : ℕ) :
    Denote O (RepeatCircuit C s) = Denote O C ^ s := by
  induction s with
  | zero => simp [RepeatCircuit, denote_nil]
  | succ s ih => rw [RepeatCircuit, denote_append, ih, pow_succ]

/-- Measured fine-query cost over `s` copies of the complete PREPARE/SELECT/
unprepare/reflection word. The oracle count is `s*K`; macro gates count separately.
This does not identify the position-dependent fine oracles with a single static oracle. -/
theorem repeated_fine_segment_cost (K L s : ℕ) (Sys : Type*)
    [Fintype Sys] [DecidableEq Sys] (θ : Fin K → ℝ)
    (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) :
    QueryCount (RepeatCircuit (segmentOraWord K L Sys θ bL O gs) s) = s * K ∧
      GateCount (RepeatCircuit (segmentOraWord K L Sys θ bL O gs) s) =
        s * (K + K + ((K + K) + gs.length)) := by
  constructor
  · rw [queryCount_repeatCircuit, segmentOraQC]
  · rw [gateCount_repeatCircuit, segmentOraGC]

/-- The multi-segment elementary ledger under the source's explicit unit prices:
one rotation unit, `L` units per load, one per reflection instruction, and `n+m`
per term-oracle query. These price premises specify the access/synthesis model;
the underlying counts are measured from the actual word components. -/
theorem repeated_priced_segment_cost (uR uL uF uQ : MacroUnit)
    (K L s n m : ℕ) (Sys : Type*) [Fintype Sys] [DecidableEq Sys]
    (θ : Fin K → ℝ) (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) (hR : uR.basic = 1) (hL : uL.basic = L)
    (hF : uF.basic = 1) (hQ : uQ.basic = n + m) :
    s * (macroCounts uR (GateCount (cascLift K L Sys θ))
      + macroCounts uL (GateCount (loadsWord K L Sys bL))
      + macroCounts uR (GateCount (cascAdj K L Sys O θ))
      + macroCounts uL (GateCount (loadsAdj K L Sys O bL))
      + macroCounts uF (GateCount (reflLift K L Sys gs)))
      + macroCounts uQ (QueryCount (RepeatCircuit (segmentOraWord K L Sys θ bL O gs) s))
      = s * (2 * prepGates K L + gs.length + sparseSegGates K n m) := by
  rw [segLedgerEq uR uL uF K L Sys θ bL O gs hR hL hF,
    queryCount_repeatCircuit, segmentOraQC]
  change s * (2 * prepGates K L + gs.length) + (s * K) * uQ.basic = _
  rw [hQ, sparseSegGates]
  ring

/-- Repeated coarse SELECT segments have their measured query/gate costs and a
linear operator-error bound against any unitary target segment. The single-segment
accuracy premise is explicit: this theorem propagates accuracy, and does not assert
OAA or block-encoding correctness for the reflection word. All norms are Euclidean
operator norms, including on an empty workspace. -/
theorem repeated_segment_error_cost (K L s : ℕ) (Sys : Type*)
    [Fintype Sys] [DecidableEq Sys] (θ : Fin K → ℝ)
    (bL : Matrix (Fin L) (Fin L) ℂ) (O : TermOracle L Sys)
    (gs : List (ReflectionGate K)) (hL : bL ∈ Matrix.unitaryGroup (Fin L) ℂ)
    (hgs : reflectionLegal gs) (V : Matrix (TTWs K L Sys) (TTWs K L Sys) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (TTWs K L Sys) ℂ) (δ : ℝ)
    (hstep : ‖Denote (taylorSelect K L Sys (termV O))
      (segmentWord K L Sys θ bL O gs) - V‖ ≤ δ) :
    QueryCount (RepeatCircuit (segmentWord K L Sys θ bL O gs) s) = s ∧
      GateCount (RepeatCircuit (segmentWord K L Sys θ bL O gs) s) =
        s * (K + K + ((K + K) + gs.length)) ∧
      ‖Denote (taylorSelect K L Sys (termV O))
        (RepeatCircuit (segmentWord K L Sys θ bL O gs) s) - V ^ s‖ ≤ (s : ℝ) * δ := by
  have hselect : taylorSelect K L Sys (termV O) ∈
      Matrix.unitaryGroup (TTWs K L Sys) ℂ := by
    rw [← selectDenote]
    exact selectUniDen K L Sys (termV O) (termV_family O)
  have hbody := denote_unitary _ hselect (segmentUni K L Sys θ bL O gs hL hgs)
  refine ⟨?_, ?_, ?_⟩
  · rw [queryCount_repeatCircuit, segmentQC, Nat.mul_one]
  · rw [gateCount_repeatCircuit, segmentGC]
  · rw [denote_repeat_word]
    exact (l2_norm_pow_sub_pow_le _ _ (l2_norm_unitary_le_one hbody)
      (l2_norm_unitary_le_one hV) s).trans
      (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg s))

end RepeatedSegments

/-! ### First ring: finite-bit synthesis of the leading rotation -/

section ApproxRing

/-- The ApproxGate realization of the cascade's leading rotation: the
approximating one-qubit unitary placed on the one-wire register, billing
exactly like the exact contract word `exWord (rotEx θ)`. -/
def approxWord (A : ApproxGate) : Circuit (Reg 1) :=
  [Step.gate (relabelGate regOneBool.symm A.approx)]

/-- The approximate word is unitary: the placed synthesis is unitary because
the contract says so. -/
theorem approxWordUni (A : ApproxGate) : IsUnitaryCircuit (approxWord A) :=
  (isUnitaryCircuit_gate _ _).mpr ⟨(relabelGate_mem_unitaryGroup _ _).2 A.uni,
    isUnitaryCircuit_nil⟩

/-- Measured: the approximate word bills one gate, identically to the exact
base word. -/
theorem approxWordGC (A : ApproxGate) : GateCount (approxWord A) = 1 :=
  rfl

/-- Measured: the approximate word makes no oracle queries. -/
theorem approxWordQC (A : ApproxGate) : QueryCount (approxWord A) = 0 :=
  rfl

/-- The synthesis bound of the first ring: if the approximate contract targets
the leading rotation `rot2 θ`, the approximated word's denotation is entrywise
within the tolerance stored in
`Qatlib.Concepts.GateKit.GateContract.ApproxGate.eps` of the exact contract
word's denotation.
An existence-level synthesis statement; no compiler is constructed. -/
theorem approxWordEntry (A : ApproxGate) (θ : ℝ) (hT : A.target = rot2 θ)
    (x y : Reg 1) :
    ‖Denote (1 : Matrix (Reg 1) (Reg 1) ℂ) (approxWord A) x y
      - Denote (1 : Matrix (Reg 1) (Reg 1) ℂ) (exWord (rotEx θ)) x y‖ ≤ A.eps := by
  have hA : Denote (1 : Matrix (Reg 1) (Reg 1) ℂ) (approxWord A)
      = relabelGate regOneBool.symm A.approx := by
    rw [approxWord, denote_gate, denote_nil, Matrix.one_mul]
  have hE : Denote (1 : Matrix (Reg 1) (Reg 1) ℂ) (exWord (rotEx θ))
      = relabelGate regOneBool.symm (rot2 θ) :=
    exWord_denote (rotEx θ)
  have hentry := A.entry (regOneBool x) (regOneBool y)
  rw [hT] at hentry
  rw [hA, hE]
  show ‖A.approx (regOneBool.symm.symm x) (regOneBool.symm.symm y)
      - rot2 θ (regOneBool.symm.symm x) (regOneBool.symm.symm y)‖ ≤ A.eps
  simpa only [Equiv.symm_symm] using hentry

end ApproxRing

end

end Qatlib.Papers.TruncTaylor14.PrepareSelectOracle

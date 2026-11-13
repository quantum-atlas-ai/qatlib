/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessDefs
import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs

/-!
# Quantum Merlin–Arthur and interactive proof models

This module defines verifier models and acceptance probabilities for quantum Merlin–Arthur,
Arthur–Merlin, and three-message interactive protocols. The classes `QMA`, `QAM`, `QIP`, and
`QMAM` encode completeness and soundness conditions.

The numbered declarations ending in `_statement` define propositions expressing amplification,
counting-class containments, and fidelity characterizations. The module also proves the finite
threshold estimate `prop43_qam_threshold_probability`. See [MarriottWatrous2005].

## Main statements

* `QMA`: quantum witnesses with polynomially bounded size.
* `QAM`: public random coins followed by a quantum witness.
* `QIP`: the two-verifier-gate interactive model.
* `prop43_qam_threshold_probability`: threshold fractions from average error bounds.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ArxivCs0506068.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators ComplexOrder

/-- A language of finite Boolean strings, represented as a predicate. -/
abbrev Language : Type := List Bool → Prop

/-- The function `f` is bounded by `c * n ^ k + c` for some natural constants `c` and `k`. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * n ^ k + c

/-- Languages recognized by a quantum verifier with exactly `m n` witness qubits, polynomially
bounded auxiliary space, and completeness and soundness bounds `a` and `b`. -/
def QMAm (m : ℕ → ℕ) (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ V : QmaVerifier,
      (∀ n, V.witnessQubits n = m n) ∧
      PolyBounded V.auxQubits ∧
      (∀ x, L x →
        ∃ ψ : QState (Reg (V.witnessQubits x.length)),
          Normalized ψ ∧ a x.length ≤ qmaAcceptProb V x ψ) ∧
      (∀ x, ¬ L x →
        ∀ ψ : QState (Reg (V.witnessQubits x.length)),
          Normalized ψ → qmaAcceptProb V x ψ ≤ b x.length) }

/-- Languages in `QMAm` for some polynomially bounded witness-size function. -/
def QMA (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ m : ℕ → ℕ, PolyBounded m ∧ L ∈ QMAm m a b }

/-- A public-coin quantum verifier with input-dependent register sizes and legal gate words of
polynomially bounded length. -/
structure QamProcedure where

  witnessQubits : ℕ → ℕ

  auxQubits : ℕ → ℕ

  coinBits : ℕ → ℕ

  program : List Bool → List Bool → List FiniteGateCode

  legal : ∀ x y, finiteWordLegal
    (witnessQubits x.length + auxQubits x.length + 1) (program x y) = true

  sizeBound : ∃ c k : ℕ, ∀ x y, y.length = coinBits x.length →
    (program x y).length ≤ c * x.length ^ k + c

/-- The acceptance measurement weight obtained by running the QAM verifier on input `x`, coin
string `y`, and witness `ψ`. -/
noncomputable def qamAcceptProb (A : QamProcedure) (x y : List Bool)
    (ψ : QState (Reg (A.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (A.witnessQubits x.length + A.auxQubits x.length + 1))
        (Reg (A.witnessQubits x.length + A.auxQubits x.length + 1)) ℂ)
      (finiteCodeCircuit (A.witnessQubits x.length + A.auxQubits x.length + 1)
        (A.program x y))
      (qmaInitialState (A.witnessQubits x.length) (A.auxQubits x.length) ψ))
    (qmaAcceptEvent (A.witnessQubits x.length) (A.auxQubits x.length))

/-- Convert a Boolean register to a list in coordinate order. -/
def regToList {s : ℕ} (y : Reg s) : List Bool := List.ofFn y

/-- The uniform average of QAM acceptance weights over public coins, allowing the witness to
depend on the coin outcome. -/
noncomputable def qamAvgAccept (A : QamProcedure) (x : List Bool)
    (ψ : Reg (A.coinBits x.length) → QState (Reg (A.witnessQubits x.length))) : ℝ :=
  (∑ y : Reg (A.coinBits x.length),
      qamAcceptProb A x (regToList y) (ψ y)) /
    (Fintype.card (Reg (A.coinBits x.length)) : ℝ)

/-- Languages with a QAM procedure whose witness, auxiliary, and coin sizes are polynomially
bounded and whose averaged acceptance satisfies bounds `a` and `b`. -/
def QAM (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ A : QamProcedure,
      PolyBounded A.witnessQubits ∧
      PolyBounded A.auxQubits ∧
      PolyBounded A.coinBits ∧
      (∀ x, L x →
        ∃ ψ : Reg (A.coinBits x.length) → QState (Reg (A.witnessQubits x.length)),
          (∀ y, Normalized (ψ y)) ∧ a x.length ≤ qamAvgAccept A x ψ) ∧
      (∀ x, ¬ L x →
        ∀ ψ : Reg (A.coinBits x.length) → QState (Reg (A.witnessQubits x.length)),
          (∀ y, Normalized (ψ y)) → qamAvgAccept A x ψ ≤ b x.length) }

/-- The language `L` is decided by a polynomial-time probabilistic program with oracle `K`, with
completeness at least two thirds and soundness at most one third. -/
def InBPPWithOracle (L K : Language) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      let t := c * x.length ^ k + c
      (L x → 3 * (ccAcceptCount M (ccOracleOf K) x t : ℝ) ≥ 2 * (2 : ℝ) ^ t) ∧
      (¬ L x → 3 * (ccAcceptCount M (ccOracleOf K) x t : ℝ) ≤ (2 : ℝ) ^ t)

/-- The set of languages satisfying the imported predicate `InPP`. -/
def PP : Set Language := { L | InPP L }

/-- Languages decided with bounded probabilistic error using an oracle for some language in
`PP`. -/
def BPdotPP : Set Language :=
  { L | ∃ K : Language, K ∈ PP ∧ InBPPWithOracle L K }

/-- Languages recognized by a quantum verifier with no witness qubits, polynomially bounded
auxiliary space, and acceptance thresholds two thirds and one third. -/
def BQP : Set Language :=
  { L | ∃ V : QmaVerifier,
      (∀ n, V.witnessQubits n = 0) ∧
      PolyBounded V.auxQubits ∧
      (∀ x, L x →
        2 / 3 ≤ qmaAcceptProb V x (fun _ => (1 : ℂ))) ∧
      (∀ x, ¬ L x →
        qmaAcceptProb V x (fun _ => (1 : ℂ)) ≤ 1 / 3) }

/-- The function `m` is bounded by a constant multiple of `Nat.log2 (n + 2) + 1`. -/
def LogBounded (m : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, m n ≤ c * (Nat.log2 (n + 2) + 1)

/-- Languages in `QMAm` for some logarithmically bounded witness-size function. -/
def QMAlog (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ m : ℕ → ℕ, LogBounded m ∧ L ∈ QMAm m a b }

/-- A three-message quantum interactive verifier specified by two legal, polynomial-length gate
words and a nonempty verifier register. -/
structure QipProcedure where

  verifierQubits : ℕ → ℕ

  messageQubits : ℕ → ℕ

  firstGate : List Bool → List FiniteGateCode

  secondGate : List Bool → List FiniteGateCode

  outputWire : ∀ n, 0 < verifierQubits n

  legalFirst : ∀ x, finiteWordLegal
    (verifierQubits x.length + messageQubits x.length) (firstGate x) = true

  legalSecond : ∀ x, finiteWordLegal
    (verifierQubits x.length + messageQubits x.length) (secondGate x) = true

  sizeBound : ∃ c k : ℕ, ∀ x,
    (firstGate x).length ≤ c * x.length ^ k + c ∧
    (secondGate x).length ≤ c * x.length ^ k + c

/-- A prover strategy consisting of a private register, a normalized initial message-private
state, and a unitary response. -/
structure QipStrategy (P : QipProcedure) (x : List Bool) where

  l : ℕ

  ψ : QState (Reg (P.messageQubits x.length + l))

  U : Matrix (Reg (P.messageQubits x.length + l))
      (Reg (P.messageQubits x.length + l)) ℂ

  hunitary : U ∈ Matrix.unitaryGroup
    (Reg (P.messageQubits x.length + l)) ℂ

  hnormalized : Normalized ψ

/-- Initialize the verifier register to zero and embed the supplied message-private state into
the split register space. -/
noncomputable def qipInit {k m l : ℕ} (ψ : QState (Reg (m + l))) :
    QState ((Reg k × Reg m) × Reg l) :=
  fun p => (if p.1.1 = ZeroStr k then (1 : ℂ) else 0) *
    ψ ((regAppendEquiv m l).symm (p.1.2, p.2))

/-- Apply `U` to the verifier and message registers while leaving the private register
unchanged. -/
noncomputable def qipApplyLeft {k m l : ℕ}
    (U : Matrix (Reg (k + m)) (Reg (k + m)) ℂ)
    (σ : QState ((Reg k × Reg m) × Reg l)) :
    QState ((Reg k × Reg m) × Reg l) :=
  fun p => ∑ q : Reg (k + m),
    U ((regAppendEquiv k m).symm p.1) q *
      σ ((regAppendEquiv k m) q, p.2)

/-- Apply `U` to the message and private registers while leaving the verifier register
unchanged. -/
noncomputable def qipApplyRight {k m l : ℕ}
    (U : Matrix (Reg (m + l)) (Reg (m + l)) ℂ)
    (σ : QState ((Reg k × Reg m) × Reg l)) :
    QState ((Reg k × Reg m) × Reg l) :=
  fun p => ∑ q : Reg (m + l),
    U ((regAppendEquiv m l).symm (p.1.2, p.2)) q *
      σ ((p.1.1, (regAppendEquiv m l q).1), (regAppendEquiv m l q).2)

/-- The computational-basis outcomes whose first verifier bit is true. -/
def qipAcceptEvent (k m l : ℕ) (hk : 0 < k) :
    Finset ((Reg k × Reg m) × Reg l) :=
  Finset.univ.filter fun p => (p.1.1 ⟨0, hk⟩) = true

/-- The acceptance probability after the first verifier operation, the prover response, and the
second verifier operation. -/
noncomputable def qipAcceptProb (P : QipProcedure) (x : List Bool)
    (S : QipStrategy P x) : ℝ :=
  MeasureProb
    (qipApplyLeft
      (finiteWordMatrix (P.verifierQubits x.length + P.messageQubits x.length)
        (P.secondGate x))
      (qipApplyRight S.U
        (qipApplyLeft
          (finiteWordMatrix (P.verifierQubits x.length + P.messageQubits x.length)
            (P.firstGate x))
          (qipInit S.ψ))))
    (qipAcceptEvent (P.verifierQubits x.length) (P.messageQubits x.length) S.l
      (P.outputWire x.length))

/-- The supremum of acceptance probabilities over all prover strategies for input `x`. -/
noncomputable def qipMaxAccept (P : QipProcedure) (x : List Bool) : ℝ :=
  sSup { p : ℝ | ∃ S : QipStrategy P x, qipAcceptProb P x S = p }

/-- Languages with a quantum interactive procedure of polynomially bounded verifier and message
size satisfying completeness `a` and soundness `b`. -/
def QIP (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ P : QipProcedure,
      PolyBounded P.verifierQubits ∧
      PolyBounded P.messageQubits ∧
      (∀ x, L x → ∃ S : QipStrategy P x, a x.length ≤ qipAcceptProb P x S) ∧
      (∀ x, ¬ L x → ∀ S : QipStrategy P x, qipAcceptProb P x S ≤ b x.length) }

/-- Reindex an operator on Boolean registers as an operator indexed by `Fin (2 ^ n)`. -/
noncomputable def regOperator (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) :
    Operator (2 ^ n) :=
  Matrix.reindex (bitVecEquiv n) (bitVecEquiv n) M

/-- Reindex a bipartite Boolean-register matrix by the corresponding pair of finite index types. -/
noncomputable def regPairOperator (k m : ℕ)
    (M : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ) :
    Matrix (Fin (2 ^ k) × Fin (2 ^ m)) (Fin (2 ^ k) × Fin (2 ^ m)) ℂ :=
  Matrix.reindex (Equiv.prodCongr (bitVecEquiv k) (bitVecEquiv m))
    (Equiv.prodCongr (bitVecEquiv k) (bitVecEquiv m)) M

/-- The matrix `ρ` is positive semidefinite with trace one after reindexing and satisfies `ρ = Λ
* ρ * Λ`. -/
def InStateSet (k m : ℕ) (Λ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ)
    (ρ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ) : Prop :=
  (regPairOperator k m ρ).PosSemidef ∧
  Matrix.trace (regPairOperator k m ρ) = 1 ∧
  ρ = Λ * ρ * Λ

/-- The operator `σ` is the partial trace of a state satisfying `InStateSet k m Λ`. -/
def InReducedStateSet (k m : ℕ) (Λ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ)
    (σ : Operator (2 ^ k)) : Prop :=
  ∃ ρ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ,
    InStateSet k m Λ ρ ∧ σ = PartialTrace (regPairOperator k m ρ)

/-- The diagonal projector onto outcomes whose first verifier bit is true. -/
def projOutputOne (k m : ℕ) (hk : 0 < k) :
    Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = q.2 ∧ p.1 ⟨0, hk⟩ = true then 1 else 0

/-- The projector onto the all-zero verifier register, tensored with the identity on the message
register. -/
def projZeroRegister (k m : ℕ) :
    Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ :=
  fun p q => if p.1 = ZeroStr k ∧ q.1 = ZeroStr k ∧ p.2 = q.2 then 1 else 0

/-- Reindex a gate on a concatenated register as a matrix on a pair of registers. -/
noncomputable def toPairGate (k m : ℕ) (U : Matrix (Reg (k + m)) (Reg (k + m)) ℂ) :
    Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ :=
  Matrix.reindex (regAppendEquiv k m) (regAppendEquiv k m) U

/-- The proposition identifying optimal interactive acceptance with the supremum of squared root
fidelities between the two specified reduced-state sets, as in Proposition 2.1 of
[MarriottWatrous2005]. -/
def prop21_max_accept_eq_fidelity_max_statement {k m : ℕ} (hk : 0 < k)
    (P : QipProcedure) (x : List Bool)
    (hkV : P.verifierQubits x.length = k)
    (hmV : P.messageQubits x.length = m) : Prop :=
    qipMaxAccept P x =
      sSup { v : ℝ | ∃ ρ ξ : Operator (2 ^ k),
        InReducedStateSet k m
          (toPairGate k m (finiteWordMatrix (k + m) (P.firstGate x)) *
            projZeroRegister k m *
            Matrix.conjTranspose
              (toPairGate k m (finiteWordMatrix (k + m) (P.firstGate x)))) ρ ∧
        InReducedStateSet k m
          (Matrix.conjTranspose
            (toPairGate k m (finiteWordMatrix (k + m) (P.secondGate x))) *
            projOutputOne k m hk *
            toPairGate k m (finiteWordMatrix (k + m) (P.secondGate x))) ξ ∧
        v = Froot ρ ξ ^ 2 }

/-- The witness-size-preserving QMA amplification proposition with completeness `1 - 2 ^ (-r n)`
and soundness `2 ^ (-r n)`, corresponding to Theorem 3.3 of [MarriottWatrous2005]. -/
def thm33_qma_amplification_statement {a b : ℕ → ℝ} {q : ℕ → ℕ}
    (hq : PolyBounded q)
    (hgap : ∀ n, 1 / (q n : ℝ) ≤ a n - b n)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hb0 : ∀ n, 0 ≤ b n) (hb1 : ∀ n, b n ≤ 1)
    {m r : ℕ → ℕ} (hm : PolyBounded m) (hr : PolyBounded r) : Prop :=
    QMAm m a b ⊆ QMAm m
      (fun n => 1 - (2 : ℝ) ^ (-(r n) : ℤ))
      (fun n => (2 : ℝ) ^ (-(r n) : ℤ))

/-- **Statement only — not proved in Qatlib.** The proposition that QMA with thresholds two thirds and one third is contained in `PP`,
corresponding to Theorem 3.4 of [MarriottWatrous2005]. -/
def thm34_qma_subset_pp_statement : Prop :=
    QMA (fun _ => 2 / 3) (fun _ => 1 / 3) ⊆ PP

/-- **Statement only — not proved in Qatlib.** The proposition that logarithmic-witness QMA with standard thresholds equals `BQP`,
corresponding to Theorem 3.6 of [MarriottWatrous2005]. -/
def thm36_qma_log_eq_bqp_statement : Prop :=
    QMAlog (fun _ => 2 / 3) (fun _ => 1 / 3) = BQP

/-- The QAM amplification proposition with exponentially small error under the supplied gap and
polynomial bounds, corresponding to Theorem 4.2 of [MarriottWatrous2005]. -/
def thm42_qam_amplification_statement {a b : ℕ → ℝ} {q : ℕ → ℕ}
    (hq : PolyBounded q)
    (hgap : ∀ n, 1 / (q n : ℝ) ≤ a n - b n)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hb0 : ∀ n, 0 ≤ b n) (hb1 : ∀ n, b n ≤ 1)
    {r : ℕ → ℕ} (hr : PolyBounded r) : Prop :=
    QAM a b ⊆ QAM
      (fun n => 1 - (2 : ℝ) ^ (-(r n) : ℤ))
      (fun n => (2 : ℝ) ^ (-(r n) : ℤ))

/-- If nonnegative values have average at most one ninth, at least two thirds of the indices
have value at most one third. -/
private lemma markov_card_complement {ι : Type*} [Fintype ι] [Nonempty ι]
    (ν : ι → ℝ) (h0 : ∀ i, 0 ≤ ν i)
    (hsum : (∑ i, ν i) ≤ (Fintype.card ι : ℝ) / 9) :
    (2 / 3 : ℝ) ≤
      ((Finset.univ.filter fun i => ν i ≤ 1 / 3).card : ℝ) /
        (Fintype.card ι : ℝ) := by
  classical
  set T := Finset.univ.filter (fun i => (1 / 3 : ℝ) < ν i) with hT
  set C := Finset.univ.filter (fun i => ¬ (1 / 3 : ℝ) < ν i) with hC
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => (1 / 3 : ℝ) < ν i)
  rw [Finset.card_univ] at hsplit
  have hcard : C.card = Fintype.card ι - T.card := by
    have htot : T.card + C.card = Fintype.card ι := hsplit
    omega
  have hTsum : (∑ i ∈ T, ν i) ≤ (Fintype.card ι : ℝ) / 9 :=
    le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => h0 i)) hsum
  have hTlower : (T.card : ℝ) * (1 / 3) ≤ ∑ i ∈ T, ν i := by
    calc (T.card : ℝ) * (1 / 3) = ∑ i ∈ T, (1 / 3 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ T, ν i :=
          Finset.sum_le_sum (fun i hi =>
            le_of_lt (Finset.mem_filter.mp hi).2)
  have hTcard : (T.card : ℝ) ≤ (Fintype.card ι : ℝ) / 3 := by
    nlinarith [hTlower, hTsum]
  have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hCcast : (C.card : ℝ) = (Fintype.card ι : ℝ) - (T.card : ℝ) := by
    rw [hcard]
    exact Nat.cast_sub (Finset.card_le_univ T)
  have hCge : (2 / 3 : ℝ) * (Fintype.card ι : ℝ) ≤ (C.card : ℝ) := by
    rw [hCcast]
    nlinarith [hTcard]
  have hCf : C = Finset.univ.filter (fun i => ν i ≤ 1 / 3) := by
    apply Finset.filter_congr
    intro i _
    simp [not_lt]
  rw [le_div_iff₀ hNpos, ← hCf]
  exact hCge

/-- Under the two stated average error bounds, at least two thirds of coin outcomes meet each of
the completeness and soundness thresholds. This is the finite threshold estimate associated
with Proposition 4.3 of [MarriottWatrous2005]. -/
theorem prop43_qam_threshold_probability {s : ℕ} (μ : Reg s → ℝ)
    (h0 : ∀ y, 0 ≤ μ y) (h1 : ∀ y, μ y ≤ 1)
    (hcomp : (∑ y : Reg s, (1 - μ y)) ≤ (Fintype.card (Reg s) : ℝ) / 9)
    (hsound : (∑ y : Reg s, μ y) ≤ (Fintype.card (Reg s) : ℝ) / 9) :
    (2 / 3 : ℝ) ≤
        ((Finset.univ.filter fun y : Reg s => 2 / 3 ≤ μ y).card : ℝ) /
          (Fintype.card (Reg s) : ℝ) ∧
      (2 / 3 : ℝ) ≤
        ((Finset.univ.filter fun y : Reg s => μ y ≤ 1 / 3).card : ℝ) /
          (Fintype.card (Reg s) : ℝ) := by
  refine ⟨?_, ?_⟩
  · have hν0 : ∀ y : Reg s, 0 ≤ 1 - μ y := fun y => by linarith [h1 y]
    have h := markov_card_complement (fun y : Reg s => 1 - μ y) hν0 hcomp
    have hfilter : (Finset.univ.filter fun y : Reg s => 1 - μ y ≤ 1 / 3)
        = (Finset.univ.filter fun y : Reg s => 2 / 3 ≤ μ y) := by
      apply Finset.filter_congr
      intro y _
      constructor <;> intro hy <;> linarith
    rwa [hfilter] at h
  · exact markov_card_complement μ h0 hsound

/-- **Statement only — not proved in Qatlib.** The proposition that QAM with standard thresholds is contained in `BPdotPP`, corresponding
to Theorem 4.4 of [MarriottWatrous2005]. -/
def thm44_qam_subset_bp_pp_statement : Prop :=
    QAM (fun _ => 2 / 3) (fun _ => 1 / 3) ⊆ BPdotPP

/-- A quantum Merlin–Arthur–Merlin verifier with two message registers, auxiliary qubits, public
coins, and polynomially bounded legal gate words. -/
structure QmamProcedure where

  m1 : ℕ → ℕ

  m2 : ℕ → ℕ

  aux : ℕ → ℕ

  coinBits : ℕ → ℕ

  program : List Bool → List Bool → List FiniteGateCode

  legal : ∀ x y, finiteWordLegal (m1 x.length + m2 x.length + aux x.length + 1)
    (program x y) = true

  sizeBound : ∃ c k : ℕ, ∀ x y, y.length = coinBits x.length →
    (program x y).length ≤ c * x.length ^ k + c

/-- A QMAM prover strategy with a normalized initial state and a unitary response for each
public coin outcome. -/
structure QmamStrategy (A : QmamProcedure) (x : List Bool) where

  l : ℕ

  ψ : QState ((Reg (A.m1 x.length) × Reg (A.m2 x.length)) × Reg l)

  U : Reg (A.coinBits x.length) →
    Matrix (Reg (A.m2 x.length) × Reg l) (Reg (A.m2 x.length) × Reg l) ℂ

  hunitary : ∀ y, U y ∈ Matrix.unitaryGroup
    (Reg (A.m2 x.length) × Reg l) ℂ

  hnormalized : Normalized ψ

/-- Split the verifier register into the first message, second message, auxiliary, and output
registers. -/
def qmamVerifierSplit (m1 m2 a : ℕ) :
    Reg (m1 + m2 + a + 1) ≃ ((Reg m1 × Reg m2) × Reg a) × Reg 1 :=
  (regAppendEquiv (m1 + m2 + a) 1).trans
    (Equiv.prodCongr
      ((regAppendEquiv (m1 + m2) a).trans
        (Equiv.prodCongr (regAppendEquiv m1 m2) (Equiv.refl (Reg a))))
      (Equiv.refl (Reg 1)))

/-- Apply a prover operation to the second message and private registers, leaving the first
message register unchanged. -/
noncomputable def qmamApplyProver {m1 m2 l : ℕ}
    (U : Matrix (Reg m2 × Reg l) (Reg m2 × Reg l) ℂ)
    (ψ : QState ((Reg m1 × Reg m2) × Reg l)) :
    QState ((Reg m1 × Reg m2) × Reg l) :=
  fun p => ∑ q : Reg m2 × Reg l,
    U (p.1.2, p.2) q * ψ ((p.1.1, q.1), q.2)

/-- Append zero auxiliary qubits and a zero output qubit to the message-private state. -/
noncomputable def qmamWithAncilla {m1 m2 a l : ℕ}
    (ψ : QState ((Reg m1 × Reg m2) × Reg l)) :
    QState ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l) :=
  fun p => ψ (p.1.1.1, p.2) *
    (if p.1.1.2 = ZeroStr a then (1 : ℂ) else 0) *
    (if p.1.2 = ZeroStr 1 then (1 : ℂ) else 0)

/-- Apply the verifier matrix to the message, auxiliary, and output registers, leaving the
private register unchanged. -/
noncomputable def qmamApplyVerifier {m1 m2 a l : ℕ}
    (U : Matrix (Reg (m1 + m2 + a + 1)) (Reg (m1 + m2 + a + 1)) ℂ)
    (τ : QState ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l)) :
    QState ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l) :=
  fun p => ∑ q : Reg (m1 + m2 + a + 1),
    U ((qmamVerifierSplit m1 m2 a).symm p.1) q *
      τ ((qmamVerifierSplit m1 m2 a) q, p.2)

/-- The computational-basis outcomes with the QMAM output qubit equal to true. -/
def qmamAcceptEvent (m1 m2 a l : ℕ) :
    Finset ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l) :=
  Finset.univ.filter fun p => p.1.2 0 = true

/-- The QMAM acceptance probability for a fixed input, public coin outcome, and prover strategy. -/
noncomputable def qmamAcceptProb (A : QmamProcedure) (x : List Bool)
    (y : Reg (A.coinBits x.length)) (S : QmamStrategy A x) : ℝ :=
  MeasureProb
    (qmamApplyVerifier
      (finiteWordMatrix (A.m1 x.length + A.m2 x.length + A.aux x.length + 1)
        (A.program x (regToList y)))
      (qmamWithAncilla (qmamApplyProver (S.U y) S.ψ)))
    (qmamAcceptEvent (A.m1 x.length) (A.m2 x.length) (A.aux x.length) S.l)

/-- The uniform average of QMAM acceptance probabilities over the public coin register. -/
noncomputable def qmamAvgAccept (A : QmamProcedure) (x : List Bool)
    (S : QmamStrategy A x) : ℝ :=
  (∑ y : Reg (A.coinBits x.length), qmamAcceptProb A x y S) /
    (Fintype.card (Reg (A.coinBits x.length)) : ℝ)

/-- Languages satisfying completeness `a` and soundness `b` for the fixed QMAM procedure `A`. -/
def QMAMBy (A : QmamProcedure) (a b : ℕ → ℝ) : Set Language :=
  { L |
      (∀ x, L x → ∃ S : QmamStrategy A x, a x.length ≤ qmamAvgAccept A x S) ∧
      (∀ x, ¬ L x → ∀ S : QmamStrategy A x, qmamAvgAccept A x S ≤ b x.length) }

/-- Languages recognized by some QMAM procedure with polynomially bounded message, auxiliary,
and coin sizes. -/
def QMAM (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ A : QmamProcedure,
      PolyBounded A.m1 ∧
      PolyBounded A.m2 ∧
      PolyBounded A.aux ∧
      PolyBounded A.coinBits ∧
      L ∈ QMAMBy A a b }

/-- Languages recognized by a QMAM procedure using exactly one public coin bit and satisfying
bounds `a` and `b`. -/
def SingleCoinQMAM (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ A : QmamProcedure,
      (∀ n, A.coinBits n = 1) ∧ L ∈ QMAMBy A a b }

/-- The proposition that the specified projective measurement weight is bounded by squared root
fidelity with a reduced state supported in the outcome-one subspace, as in Lemma 5.2 of
[MarriottWatrous2005]. -/
def lemma52_measurement_fidelity_bound_statement {k m : ℕ}
    (ρfull : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ)
    (hρ : (regPairOperator k m ρfull).PosSemidef)
    (htr : Matrix.trace (regPairOperator k m ρfull) = 1)
    (Λ0 Λ1 : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ)
    (hΛ1proj : Λ1 * Λ1 = Λ1) (hΛ1herm : Matrix.conjTranspose Λ1 = Λ1)
    (hΛ0proj : Λ0 * Λ0 = Λ0) (hΛ0herm : Matrix.conjTranspose Λ0 = Λ0)
    (horth1 : Λ1 * Λ0 = 0) (horth0 : Λ0 * Λ1 = 0)
    (hcomplete : Λ0 + Λ1 = 1)
    (σ : Operator (2 ^ k))
    (hσ : σ = PartialTrace (regPairOperator k m ρfull)) : Prop :=
    ∃ ρ : Operator (2 ^ k), InReducedStateSet k m Λ1 ρ ∧
      (Matrix.trace (Λ1 * ρfull)).re ≤ Froot σ ρ ^ 2

/-- The proposition giving the specified QIP language a single-coin QMAM procedure with perfect
completeness and soundness at most `1 / 2 + 2 ^ (-r n)`, as in Theorem 5.4 of
[MarriottWatrous2005]. -/
def thm54_qip_to_single_coin_qmam_statement {r : ℕ → ℕ} (hr : PolyBounded r)
    {L : Language} (hL : L ∈ QIP (fun _ => 2 / 3) (fun _ => 1 / 3)) : Prop :=
    ∃ A : QmamProcedure,
      (∀ n, A.coinBits n = 1) ∧
      PolyBounded A.m1 ∧ PolyBounded A.m2 ∧ PolyBounded A.aux ∧
      PolyBounded A.coinBits ∧
      (∀ x, L x → ∃ S : QmamStrategy A x, qmamAvgAccept A x S = 1) ∧
      (∀ x, ¬ L x → ∀ S : QmamStrategy A x,
        qmamAvgAccept A x S ≤ 1 / 2 + (2 : ℝ) ^ (-(r x.length) : ℤ))

/-- The proposition embedding standard-threshold QIP into QMAM with perfect completeness and
soundness `1 / 2 + 2 ^ (-r n)`, corresponding to Corollary 5.5 of [MarriottWatrous2005]. -/
def cor55_qip_subset_qmam_statement {r : ℕ → ℕ} (hr : PolyBounded r) : Prop :=
    QIP (fun _ => 2 / 3) (fun _ => 1 / 3) ⊆
      QMAM (fun _ => 1) (fun n => 1 / 2 + (2 : ℝ) ^ (-(r n) : ℤ))

/-- The proposition equating standard-threshold QIP with QMAM having perfect completeness and
soundness `2 ^ (-r n)`, corresponding to Corollary 5.6 of [MarriottWatrous2005]. -/
def cor56_qip_eq_qmam_statement {r : ℕ → ℕ} (hr : PolyBounded r) : Prop :=
    QIP (fun _ => 2 / 3) (fun _ => 1 / 3) =
      QMAM (fun _ => 1) (fun n => (2 : ℝ) ^ (-(r n) : ℤ))

end Qatlib.Papers.ArxivCs0506068.MainResults

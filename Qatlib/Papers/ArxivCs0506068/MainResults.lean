/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessDefs
import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Papers.ArxivCs0506068.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators ComplexOrder

abbrev Language : Type := List Bool → Prop

def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * n ^ k + c

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

def QMA (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ m : ℕ → ℕ, PolyBounded m ∧ L ∈ QMAm m a b }

structure QamProcedure where

  witnessQubits : ℕ → ℕ

  auxQubits : ℕ → ℕ

  coinBits : ℕ → ℕ

  program : List Bool → List Bool → List FiniteGateCode

  legal : ∀ x y, finiteWordLegal
    (witnessQubits x.length + auxQubits x.length + 1) (program x y) = true

  sizeBound : ∃ c k : ℕ, ∀ x y, y.length = coinBits x.length →
    (program x y).length ≤ c * x.length ^ k + c

noncomputable def qamAcceptProb (A : QamProcedure) (x y : List Bool)
    (ψ : QState (Reg (A.witnessQubits x.length))) : ℝ :=
  MeasureProb
    (Run (1 : Matrix (Reg (A.witnessQubits x.length + A.auxQubits x.length + 1))
        (Reg (A.witnessQubits x.length + A.auxQubits x.length + 1)) ℂ)
      (finiteCodeCircuit (A.witnessQubits x.length + A.auxQubits x.length + 1)
        (A.program x y))
      (qmaInitialState (A.witnessQubits x.length) (A.auxQubits x.length) ψ))
    (qmaAcceptEvent (A.witnessQubits x.length) (A.auxQubits x.length))

def regToList {s : ℕ} (y : Reg s) : List Bool := List.ofFn y

noncomputable def qamAvgAccept (A : QamProcedure) (x : List Bool)
    (ψ : Reg (A.coinBits x.length) → QState (Reg (A.witnessQubits x.length))) : ℝ :=
  (∑ y : Reg (A.coinBits x.length),
      qamAcceptProb A x (regToList y) (ψ y)) /
    (Fintype.card (Reg (A.coinBits x.length)) : ℝ)

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

def InBPPWithOracle (L K : Language) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      let t := c * x.length ^ k + c
      (L x → 3 * (ccAcceptCount M (ccOracleOf K) x t : ℝ) ≥ 2 * (2 : ℝ) ^ t) ∧
      (¬ L x → 3 * (ccAcceptCount M (ccOracleOf K) x t : ℝ) ≤ (2 : ℝ) ^ t)

def PP : Set Language := { L | InPP L }

def BPdotPP : Set Language :=
  { L | ∃ K : Language, K ∈ PP ∧ InBPPWithOracle L K }

def BQP : Set Language :=
  { L | ∃ V : QmaVerifier,
      (∀ n, V.witnessQubits n = 0) ∧
      PolyBounded V.auxQubits ∧
      (∀ x, L x →
        2 / 3 ≤ qmaAcceptProb V x (fun _ => (1 : ℂ))) ∧
      (∀ x, ¬ L x →
        qmaAcceptProb V x (fun _ => (1 : ℂ)) ≤ 1 / 3) }

def LogBounded (m : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, m n ≤ c * (Nat.log2 (n + 2) + 1)

def QMAlog (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ m : ℕ → ℕ, LogBounded m ∧ L ∈ QMAm m a b }

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

structure QipStrategy (P : QipProcedure) (x : List Bool) where

  l : ℕ

  ψ : QState (Reg (P.messageQubits x.length + l))

  U : Matrix (Reg (P.messageQubits x.length + l))
      (Reg (P.messageQubits x.length + l)) ℂ

  hunitary : U ∈ Matrix.unitaryGroup
    (Reg (P.messageQubits x.length + l)) ℂ

  hnormalized : Normalized ψ

noncomputable def qipInit {k m l : ℕ} (ψ : QState (Reg (m + l))) :
    QState ((Reg k × Reg m) × Reg l) :=
  fun p => (if p.1.1 = ZeroStr k then (1 : ℂ) else 0) *
    ψ ((regAppendEquiv m l).symm (p.1.2, p.2))

noncomputable def qipApplyLeft {k m l : ℕ}
    (U : Matrix (Reg (k + m)) (Reg (k + m)) ℂ)
    (σ : QState ((Reg k × Reg m) × Reg l)) :
    QState ((Reg k × Reg m) × Reg l) :=
  fun p => ∑ q : Reg (k + m),
    U ((regAppendEquiv k m).symm p.1) q *
      σ ((regAppendEquiv k m) q, p.2)

noncomputable def qipApplyRight {k m l : ℕ}
    (U : Matrix (Reg (m + l)) (Reg (m + l)) ℂ)
    (σ : QState ((Reg k × Reg m) × Reg l)) :
    QState ((Reg k × Reg m) × Reg l) :=
  fun p => ∑ q : Reg (m + l),
    U ((regAppendEquiv m l).symm (p.1.2, p.2)) q *
      σ ((p.1.1, (regAppendEquiv m l q).1), (regAppendEquiv m l q).2)

def qipAcceptEvent (k m l : ℕ) (hk : 0 < k) :
    Finset ((Reg k × Reg m) × Reg l) :=
  Finset.univ.filter fun p => (p.1.1 ⟨0, hk⟩) = true

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

noncomputable def qipMaxAccept (P : QipProcedure) (x : List Bool) : ℝ :=
  sSup { p : ℝ | ∃ S : QipStrategy P x, qipAcceptProb P x S = p }

def QIP (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ P : QipProcedure,
      PolyBounded P.verifierQubits ∧
      PolyBounded P.messageQubits ∧
      (∀ x, L x → ∃ S : QipStrategy P x, a x.length ≤ qipAcceptProb P x S) ∧
      (∀ x, ¬ L x → ∀ S : QipStrategy P x, qipAcceptProb P x S ≤ b x.length) }

noncomputable def regOperator (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) :
    Operator (2 ^ n) :=
  Matrix.reindex (bitVecEquiv n) (bitVecEquiv n) M

noncomputable def regPairOperator (k m : ℕ)
    (M : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ) :
    Matrix (Fin (2 ^ k) × Fin (2 ^ m)) (Fin (2 ^ k) × Fin (2 ^ m)) ℂ :=
  Matrix.reindex (Equiv.prodCongr (bitVecEquiv k) (bitVecEquiv m))
    (Equiv.prodCongr (bitVecEquiv k) (bitVecEquiv m)) M

def InStateSet (k m : ℕ) (Λ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ)
    (ρ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ) : Prop :=
  (regPairOperator k m ρ).PosSemidef ∧
  Matrix.trace (regPairOperator k m ρ) = 1 ∧
  ρ = Λ * ρ * Λ

def InReducedStateSet (k m : ℕ) (Λ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ)
    (σ : Operator (2 ^ k)) : Prop :=
  ∃ ρ : Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ,
    InStateSet k m Λ ρ ∧ σ = PartialTrace (regPairOperator k m ρ)

def projOutputOne (k m : ℕ) (hk : 0 < k) :
    Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = q.2 ∧ p.1 ⟨0, hk⟩ = true then 1 else 0

def projZeroRegister (k m : ℕ) :
    Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ :=
  fun p q => if p.1 = ZeroStr k ∧ q.1 = ZeroStr k ∧ p.2 = q.2 then 1 else 0

noncomputable def toPairGate (k m : ℕ) (U : Matrix (Reg (k + m)) (Reg (k + m)) ℂ) :
    Matrix (Reg k × Reg m) (Reg k × Reg m) ℂ :=
  Matrix.reindex (regAppendEquiv k m) (regAppendEquiv k m) U

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

def thm33_qma_amplification_statement {a b : ℕ → ℝ} {q : ℕ → ℕ}
    (hq : PolyBounded q)
    (hgap : ∀ n, 1 / (q n : ℝ) ≤ a n - b n)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hb0 : ∀ n, 0 ≤ b n) (hb1 : ∀ n, b n ≤ 1)
    {m r : ℕ → ℕ} (hm : PolyBounded m) (hr : PolyBounded r) : Prop :=
    QMAm m a b ⊆ QMAm m
      (fun n => 1 - (2 : ℝ) ^ (-(r n) : ℤ))
      (fun n => (2 : ℝ) ^ (-(r n) : ℤ))

def thm34_qma_subset_pp_statement : Prop :=
    QMA (fun _ => 2 / 3) (fun _ => 1 / 3) ⊆ PP

def thm36_qma_log_eq_bqp_statement : Prop :=
    QMAlog (fun _ => 2 / 3) (fun _ => 1 / 3) = BQP

def thm42_qam_amplification_statement {a b : ℕ → ℝ} {q : ℕ → ℕ}
    (hq : PolyBounded q)
    (hgap : ∀ n, 1 / (q n : ℝ) ≤ a n - b n)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hb0 : ∀ n, 0 ≤ b n) (hb1 : ∀ n, b n ≤ 1)
    {r : ℕ → ℕ} (hr : PolyBounded r) : Prop :=
    QAM a b ⊆ QAM
      (fun n => 1 - (2 : ℝ) ^ (-(r n) : ℤ))
      (fun n => (2 : ℝ) ^ (-(r n) : ℤ))

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

def thm44_qam_subset_bp_pp_statement : Prop :=
    QAM (fun _ => 2 / 3) (fun _ => 1 / 3) ⊆ BPdotPP

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

structure QmamStrategy (A : QmamProcedure) (x : List Bool) where

  l : ℕ

  ψ : QState ((Reg (A.m1 x.length) × Reg (A.m2 x.length)) × Reg l)

  U : Reg (A.coinBits x.length) →
    Matrix (Reg (A.m2 x.length) × Reg l) (Reg (A.m2 x.length) × Reg l) ℂ

  hunitary : ∀ y, U y ∈ Matrix.unitaryGroup
    (Reg (A.m2 x.length) × Reg l) ℂ

  hnormalized : Normalized ψ

def qmamVerifierSplit (m1 m2 a : ℕ) :
    Reg (m1 + m2 + a + 1) ≃ ((Reg m1 × Reg m2) × Reg a) × Reg 1 :=
  (regAppendEquiv (m1 + m2 + a) 1).trans
    (Equiv.prodCongr
      ((regAppendEquiv (m1 + m2) a).trans
        (Equiv.prodCongr (regAppendEquiv m1 m2) (Equiv.refl (Reg a))))
      (Equiv.refl (Reg 1)))

noncomputable def qmamApplyProver {m1 m2 l : ℕ}
    (U : Matrix (Reg m2 × Reg l) (Reg m2 × Reg l) ℂ)
    (ψ : QState ((Reg m1 × Reg m2) × Reg l)) :
    QState ((Reg m1 × Reg m2) × Reg l) :=
  fun p => ∑ q : Reg m2 × Reg l,
    U (p.1.2, p.2) q * ψ ((p.1.1, q.1), q.2)

noncomputable def qmamWithAncilla {m1 m2 a l : ℕ}
    (ψ : QState ((Reg m1 × Reg m2) × Reg l)) :
    QState ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l) :=
  fun p => ψ (p.1.1.1, p.2) *
    (if p.1.1.2 = ZeroStr a then (1 : ℂ) else 0) *
    (if p.1.2 = ZeroStr 1 then (1 : ℂ) else 0)

noncomputable def qmamApplyVerifier {m1 m2 a l : ℕ}
    (U : Matrix (Reg (m1 + m2 + a + 1)) (Reg (m1 + m2 + a + 1)) ℂ)
    (τ : QState ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l)) :
    QState ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l) :=
  fun p => ∑ q : Reg (m1 + m2 + a + 1),
    U ((qmamVerifierSplit m1 m2 a).symm p.1) q *
      τ ((qmamVerifierSplit m1 m2 a) q, p.2)

def qmamAcceptEvent (m1 m2 a l : ℕ) :
    Finset ((((Reg m1 × Reg m2) × Reg a) × Reg 1) × Reg l) :=
  Finset.univ.filter fun p => p.1.2 0 = true

noncomputable def qmamAcceptProb (A : QmamProcedure) (x : List Bool)
    (y : Reg (A.coinBits x.length)) (S : QmamStrategy A x) : ℝ :=
  MeasureProb
    (qmamApplyVerifier
      (finiteWordMatrix (A.m1 x.length + A.m2 x.length + A.aux x.length + 1)
        (A.program x (regToList y)))
      (qmamWithAncilla (qmamApplyProver (S.U y) S.ψ)))
    (qmamAcceptEvent (A.m1 x.length) (A.m2 x.length) (A.aux x.length) S.l)

noncomputable def qmamAvgAccept (A : QmamProcedure) (x : List Bool)
    (S : QmamStrategy A x) : ℝ :=
  (∑ y : Reg (A.coinBits x.length), qmamAcceptProb A x y S) /
    (Fintype.card (Reg (A.coinBits x.length)) : ℝ)

def QMAMBy (A : QmamProcedure) (a b : ℕ → ℝ) : Set Language :=
  { L |
      (∀ x, L x → ∃ S : QmamStrategy A x, a x.length ≤ qmamAvgAccept A x S) ∧
      (∀ x, ¬ L x → ∀ S : QmamStrategy A x, qmamAvgAccept A x S ≤ b x.length) }

def QMAM (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ A : QmamProcedure,
      PolyBounded A.m1 ∧
      PolyBounded A.m2 ∧
      PolyBounded A.aux ∧
      PolyBounded A.coinBits ∧
      L ∈ QMAMBy A a b }

def SingleCoinQMAM (a b : ℕ → ℝ) : Set Language :=
  { L | ∃ A : QmamProcedure,
      (∀ n, A.coinBits n = 1) ∧ L ∈ QMAMBy A a b }

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

def thm54_qip_to_single_coin_qmam_statement {r : ℕ → ℕ} (hr : PolyBounded r)
    {L : Language} (hL : L ∈ QIP (fun _ => 2 / 3) (fun _ => 1 / 3)) : Prop :=
    ∃ A : QmamProcedure,
      (∀ n, A.coinBits n = 1) ∧
      PolyBounded A.m1 ∧ PolyBounded A.m2 ∧ PolyBounded A.aux ∧
      PolyBounded A.coinBits ∧
      (∀ x, L x → ∃ S : QmamStrategy A x, qmamAvgAccept A x S = 1) ∧
      (∀ x, ¬ L x → ∀ S : QmamStrategy A x,
        qmamAvgAccept A x S ≤ 1 / 2 + (2 : ℝ) ^ (-(r x.length) : ℤ))

def cor55_qip_subset_qmam_statement {r : ℕ → ℕ} (hr : PolyBounded r) : Prop :=
    QIP (fun _ => 2 / 3) (fun _ => 1 / 3) ⊆
      QMAM (fun _ => 1) (fun n => 1 / 2 + (2 : ℝ) ^ (-(r n) : ℤ))

def cor56_qip_eq_qmam_statement {r : ℕ → ℕ} (hr : PolyBounded r) : Prop :=
    QIP (fun _ => 2 / 3) (fun _ => 1 / 3) =
      QMAM (fun _ => 1) (fun n => (2 : ℝ) ^ (-(r n) : ℤ))

end Qatlib.Papers.ArxivCs0506068.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs

/-!
# ArthurMerlin05.StaticGames — paper-faithful game vocabulary

Fixed source: Marriott--Watrous, *Quantum Arthur--Merlin Games*,
arXiv:cs/0506068v1 (Computational Complexity 14(2), 122--152, 2005).
The paper's PDF/text are the only statement sources; every class below
transcribes a definition from that fixed version.

This file only fixes the **interface vocabulary** used by the paper-layer
theorems.  It does not prove any substantive result.

Model conventions (documented honestly, since the shared library has no
parametrised uniform-`QMA_m` class):

* A register holding `m` qubits has Hilbert dimension `Qdim m = 2 ^ m`, and
  `Operator (Qdim m)` is the matrix algebra on it.
* A `QMA` verification procedure is represented by its **acceptance operator**
  family `op : (n) → Operator (Qdim (m n))`: the paper's
  `⟨ψ|Q_x|ψ⟩ = Pr[A_x accepts ψ]` with
  `Q_x = (I_m ⊗ ⟨0^k|) A_x† Π₁ A_x (I_m ⊗ |0^k⟩)` (proof of Thm 3.3/3.4).
  The polynomial-time-generation/uniformity constraint is *factored out* of the
  interface; the theorems below state the paper's spectral/probabilistic
  content.  This is the same mathematical object the paper manipulates, and it
  only makes the hypotheses stronger (arbitrary operators, not just efficient
  ones), so no bound is faked.
* `QAM`/`QMAM`/`QIP` are represented by their acceptance functionals over the
  paper's strategy spaces (Definitions 4.1 and 5.1, and §2 for QIP).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

/-- Hilbert-space dimension of an `m`-qubit register: `2 ^ m`. -/
abbrev Qdim (m : ℕ) : ℕ := 2 ^ m

/-! ## QMA (Definition 3.1, Theorem 3.3) -/

/-- Born form of the acceptance probability `⟨ψ|Q|ψ⟩` for a (not necessarily
normalized) witness amplitude `ψ`. -/
noncomputable def acceptProb {m : ℕ} (Q : Operator (Qdim m))
    (ψ : QState (Fin (Qdim m))) : ℝ :=
  (Inner ψ (Q.mulVec ψ)).re

/-- A `QMA` verification procedure at message length `m`, represented by its
acceptance-operator family (Definition 3.1 / proof of Thm 3.3). -/
structure QmaVerifier (m : ℕ → ℕ) where
  /-- The acceptance operator `Q_x` on `m(|x|)` qubits. -/
  op : (n : ℕ) → Operator (Qdim (m n))

/-- `QMAm(a,b)` (Definition 3.1): there is an `m`-qubit QMA verification
procedure with completeness `a` and soundness `b`.  The paper indexes the
bounds by the input length `n = |x|`. -/
def InQMAm (m : ℕ → ℕ) (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ V : QmaVerifier m,
    (∀ x : List Bool, L x →
      ∃ ψ : QState (Fin (Qdim (m x.length))), Normalized ψ ∧
        a x.length ≤ acceptProb (V.op x.length) ψ) ∧
    (∀ x : List Bool, ¬ L x →
      ∀ ψ : QState (Fin (Qdim (m x.length))), Normalized ψ →
        acceptProb (V.op x.length) ψ ≤ b x.length)

/-- `QMA(a,b) = ⋃_m QMAm(a,b)` (Definition 3.1). -/
def InQMA (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ m : ℕ → ℕ, InQMAm m a b L

/-! ## QAM (Definition 4.1, Theorem 4.2, Proposition 4.3, Theorem 4.4) -/

/-- A `QAM` verification procedure at message length `m` and coin length `s`
(Definition 4.1): for each Arthur coin string `y ∈ Σ^{s}` an acceptance
operator on `m` qubits. -/
structure QamVerifier (m s : ℕ → ℕ) where
  /-- `coinOp n y = Q_{x,y}` for `y` an `s(|x|)`-bit coin string. -/
  coinOp : (n : ℕ) → Fin (Qdim (s n)) → Operator (Qdim (m n))

/-- Uniform average over Arthur's `2^{s}` coin strings. -/
noncomputable def coinAverage {s : ℕ} (μ : Fin (Qdim s) → ℝ) : ℝ :=
  (∑ y : Fin (Qdim s), μ y) / (Qdim s : ℝ)

/-- `QAM(a,b)` at fixed `m,s` (Definition 4.1): completeness holds for some
family of Merlin states `{ψ_y}`, soundness for every such family. -/
def InQam (m s : ℕ → ℕ) (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ A : QamVerifier m s,
    (∀ x : List Bool, L x →
      ∃ strat : Fin (Qdim (s x.length)) → QState (Fin (Qdim (m x.length))),
        (∀ y, Normalized (strat y)) ∧
          a x.length ≤ coinAverage (fun y => acceptProb (A.coinOp x.length y) (strat y))) ∧
    (∀ x : List Bool, ¬ L x →
      ∀ strat : Fin (Qdim (s x.length)) → QState (Fin (Qdim (m x.length))),
        (∀ y, Normalized (strat y)) →
          coinAverage (fun y => acceptProb (A.coinOp x.length y) (strat y)) ≤ b x.length)

/-- `QAM(a,b) = ⋃_{m,s ∈ poly} QAM(m,s; a,b)` (Definition 4.1). -/
def InQamPoly (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ m s : ℕ → ℕ, InQam m s a b L

/-! ## QMAM (Definition 5.1, Theorem 5.4, Corollary 5.6) -/

/-- A `QMAM` verification procedure (Definition 5.1), represented by its
acceptance functional: `accept n y l ψ U` is
`Pr[A_{x,y} accepts (I_{m₁} ⊗ U)|ψ⟩]`, where `ψ` is Merlin's joint state on
`m₁+m₂+l` qubits and `U` his unitary on `m₂+l` qubits.  This is exactly the
quantity bounded in Definition 5.1; only the polynomial-time generation of the
circuit family is factored out of the interface. -/
structure QmamVerifier (m1 m2 s : ℕ → ℕ) where
  accept : (n : ℕ) → Fin (Qdim (s n)) → (l : ℕ) →
    QState (Fin (Qdim (m1 n + m2 n + l))) →
    Matrix (Fin (Qdim (m2 n + l))) (Fin (Qdim (m2 n + l))) ℂ → ℝ
  accept_nonneg : ∀ n y l ψ U, 0 ≤ accept n y l ψ U

/-- `QMAM(a,b)` at fixed `m₁,m₂,s` (Definition 5.1). -/
def InQmam (m1 m2 s : ℕ → ℕ) (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ A : QmamVerifier m1 m2 s,
    (∀ x : List Bool, L x →
      ∃ (l : ℕ) (ψ : QState (Fin (Qdim (m1 x.length + m2 x.length + l))))
        (U : Matrix (Fin (Qdim (m2 x.length + l))) (Fin (Qdim (m2 x.length + l))) ℂ),
        Normalized ψ ∧ U ∈ Matrix.unitaryGroup _ ℂ ∧
          a x.length ≤
            coinAverage (fun y => A.accept x.length y l ψ U)) ∧
    (∀ x : List Bool, ¬ L x →
      ∀ (l : ℕ) (ψ : QState (Fin (Qdim (m1 x.length + m2 x.length + l))))
        (U : Matrix (Fin (Qdim (m2 x.length + l))) (Fin (Qdim (m2 x.length + l))) ℂ),
        Normalized ψ → U ∈ Matrix.unitaryGroup _ ℂ →
          coinAverage (fun y => A.accept x.length y l ψ U) ≤ b x.length)

/-- `QMAM(a,b) = ⋃_{m₁,m₂,s ∈ poly} QMAM(m₁,m₂,s; a,b)`. -/
def InQmamPoly (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ m1 m2 s : ℕ → ℕ, InQmam m1 m2 s a b L

/-! ## QIP (three-message normal form used by the paper) -/

/-- A three-message quantum interactive proof verifier in the normal form the
paper uses in the proof of Theorem 5.4: by [KitaevWatrous2000] one may assume perfect
completeness and soundness error `2^{-2r}`.  `maxAccept n` is
`max_{|ψ⟩,U} Pr[V accepts]` from §2. -/
structure QipVerifier (r : ℕ → ℕ) where
  maxAccept : (n : ℕ) → ℝ
  maxAccept_nonneg : ∀ n, 0 ≤ maxAccept n

/-- `InQipWith r L`: `L` has a three-message QIP with completeness `1` and
soundness `2^{-2r}` (the [KitaevWatrous2000] normal form used in the proof of Thm 5.4). -/
def InQipWith (r : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ V : QipVerifier r,
    (∀ x : List Bool, L x → 1 - (2 : ℝ) ^ (-(2 * r x.length) : ℤ) ≤ V.maxAccept x.length) ∧
    (∀ x : List Bool, ¬ L x → V.maxAccept x.length ≤ (2 : ℝ) ^ (-(2 * r x.length) : ℤ))

/-- `QIP = ⋃_r QIP(r)` in the [KitaevWatrous2000] normal form. -/
def InQip (L : List Bool → Prop) : Prop :=
  ∃ r : ℕ → ℕ, InQipWith r L

/-! ## BQP and QMAlog (Theorem 3.6) -/

/-- `BQP`, represented as `QMA` with an empty witness register.  This is the
standard characterisation and is the shape the paper's construction produces
(a polynomial-time quantum algorithm `B` with no prover). -/
def InBqp (L : List Bool → Prop) : Prop :=
  InQMAm (fun _ => 0) (fun _ => 2 / 3) (fun _ => 1 / 3) L

/-- `m(n) = O(log n)` (page 13, before Theorem 3.6).  We use
`m n ≤ c * (clog 2 (n+1) + 1)` for a constant `c`. -/
def IsLogMessageLength (m : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, m n ≤ c * (Nat.clog 2 (n + 1) + 1)

/-- `QMAlog(a,b) = ⋃_{m = O(log n)} QMAm(a,b)` (page 13). -/
def InQMAlog (a b : ℕ → ℝ) (L : List Bool → Prop) : Prop :=
  ∃ m : ℕ → ℕ, IsLogMessageLength m ∧ InQMAm m a b L

/-! ## BP · PP (Theorem 4.4) -/

open Qatlib.Concepts.CountingClasses.ClassTransport

/-- `BPP` with a fixed boolean oracle `A` on the shared counting machine
model: uniform coins, two-sided error at most `1/3`. -/
def InBPPOracle (A : List Bool → Bool) (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      let t := c * x.length ^ k + c
      (L x → 3 * ccAcceptCount M A x t ≥ 2 * 2 ^ t) ∧
      (¬ L x → 3 * ccAcceptCount M A x t ≤ 2 ^ t)

/-- `BP · PP`: a `BPP` machine with oracle access to a `PP` language
`K ⊆ Σ* × Σ*`, where the PP language is indexed by the input `x`. -/
def InBPdotPP (L : List Bool → Prop) : Prop :=
  ∃ K : List Bool → List Bool → Prop,
    (∀ x, InPP (K x)) ∧
      InBPPOracle (ccOracleOf (fun z => ∃ x y, z = x ++ y ∧ K x y)) L

end Qatlib.Papers.ArthurMerlin05.StaticGames

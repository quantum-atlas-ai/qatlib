/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QShannonWilde11.MainResults.Model.ChannelCaps

set_option backward.isDefEq.respectTransparency false

/-!
# Operational-capacity interfaces for the coding chapters

(arXiv:1106.1445v8, Ch. 7, 8, 18, 19, 20–25)

This file collects the small *interface* records used by the paper-layer
statements for the coding chapters.  As in `Model.ChannelCaps`, the operational
definitions (actual coding protocols, achievable-rate regions, distillable
entanglement, …) are not formalised.  Each record bundles the mathematical
objects a theorem talks about with the operational quantity that the paper
identifies; the paper-layer theorem then states the paper's relation among
them.  Every consumer theorem flags the operational gap in its docstring.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Model

open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open scoped BigOperators

noncomputable section

/-- A resource rate triple `(C, Q, E)`: classical, quantum and entanglement
rates, as used in the dynamic-capacity region of Ch. 25. -/
structure RateTriple where
  /-- Classical communication rate `C`. -/
  c : ℝ
  /-- Quantum communication rate `Q`. -/
  q : ℝ
  /-- Entanglement consumption rate `E`. -/
  e : ℝ

/-- The product topology on rate triples, used for the closure in the dynamic
capacity theorem (Thm 25.2.1). -/
instance : TopologicalSpace RateTriple :=
  TopologicalSpace.induced (fun v => (v.c, v.q, v.e)) inferInstance

/-- Scale a region by `1/k` (the `(1/k) C^{(1)}(N^{⊗k})` step of regularisation). -/
def scaleRegion (k : ℕ) (R : Set RateTriple) : Set RateTriple :=
  { x | ∃ y ∈ R, x = ⟨(k : ℝ)⁻¹ * y.c, (k : ℝ)⁻¹ * y.q, (k : ℝ)⁻¹ * y.e⟩ }

/-- The regularised union `⋃_{k≥1} (1/k) R_k`. -/
def regUnion (f : ℕ → Set RateTriple) : Set RateTriple :=
  ⋃ k ∈ Set.Ici 1, scaleRegion k (f k)

/-! ## Dynamic-capacity interface (Ch. 25) -/

/-- Interface for the quantum dynamic capacity region of Ch. 25.  The field
`dynRegion N` is the paper's `C_CQE(N)`; `slRegion N` is the single-letter
region `C^{(1)}_CQE(N)`; the entropic fields are the single-letter functionals
`I(AX;B)`, `I(A⟩BX)`, `I(X;B)`, `|E⟩`, and the three specialisations
`I(A;B)_φ`, `I(A⟩B)_φ`, `max_{p_X} I(X;B)` of Thm 25.4.1–25.4.3. -/
structure DynInfo where
  /-- The type of channels. -/
  Ch : Type
  /-- `k`-fold tensor power. -/
  tensorPow : Ch → ℕ → Ch
  /-- The dynamic capacity region `C_CQE(N)`. -/
  dynRegion : Ch → Set RateTriple
  /-- The single-letter region `C^{(1)}_CQE(N)`. -/
  slRegion : Ch → Set RateTriple
  /-- `I(AX;B)_σ`. -/
  IAXB : Ch → ℝ
  /-- `I(A⟩BX)_σ`. -/
  coh : Ch → ℝ
  /-- `I(X;B)_σ`. -/
  IXB : Ch → ℝ
  /-- `|E|`, the entanglement rate available from a pure environment. -/
  ent : Ch → ℝ
  /-- `max_φ I(A;B)_φ` (Thm 25.4.1). -/
  IAB : Ch → ℝ
  /-- `max_φ I(A⟩B)_φ` (Thm 25.4.2). -/
  cohPure : Ch → ℝ
  /-- `max_{p_X,ψ_x} I(X;B)` (Thm 25.4.3). -/
  IXBpure : Ch → ℝ
  /-- `N` is a Hadamard channel. -/
  Hadamard : Ch → Prop
  /-- `N` is a dephasing channel with dephasing parameter `ν`. -/
  Dephasing : Ch → ℝ → Prop
  /-- `N` is a `d`-dimensional erasure channel with erasure probability `ε`. -/
  Erasure : Ch → ℕ → ℝ → Prop

/-- The single-letter region of Thm 25.2.1, cut out by the three trade-off
inequalities `C+2Q ≤ I(AX;B)`, `Q+E ≤ I(A⟩BX)`, `C+Q+E ≤ I(X;B)`. -/
def DynInfo.slRegionOf (D : DynInfo) (N : D.Ch) : Set RateTriple :=
  { v | v.c + 2 * v.q ≤ D.IAXB N ∧ v.q + v.e ≤ D.coh N ∧
        v.c + v.q + v.e ≤ D.IXB N }

/-- HSW single-letter classical region of Thm 25.2.2: `C ≤ I(X;B)+I(A⟩BX)`. -/
def DynInfo.hswRegion (D : DynInfo) (N : D.Ch) : Set RateTriple :=
  { v | v.c ≤ D.IXB N + D.coh N }

/-- Quantum single-letter region of Thm 25.2.3: `Q ≤ I(A⟩BX)` with a degenerate
`p_X`. -/
def DynInfo.qRegion (D : DynInfo) (N : D.Ch) : Set RateTriple :=
  { v | v.q ≤ D.coh N }

/-- Entanglement-assisted quantum single-letter region of Thm 25.2.4:
`2Q ≤ I(AX;B)` and `Q ≤ I(A⟩BX)+|E|`. -/
def DynInfo.qeRegion (D : DynInfo) (N : D.Ch) : Set RateTriple :=
  { v | 2 * v.q ≤ D.IAXB N ∧ v.q ≤ D.coh N + D.ent N }

/-- Classical-enhanced quantum single-letter region of Thm 25.2.5:
`C+Q ≤ I(X;B)+I(A⟩BX)` and `Q ≤ I(A⟩BX)`. -/
def DynInfo.cqRegion (D : DynInfo) (N : D.Ch) : Set RateTriple :=
  { v | v.c + v.q ≤ D.IXB N + D.coh N ∧ v.q ≤ D.coh N }

/-- Entanglement-assisted classical single-letter region of Thm 25.2.6:
`C ≤ I(AX;B)` and `C ≤ I(X;B)+I(A⟩BX)+|E|`. -/
def DynInfo.ceRegion (D : DynInfo) (N : D.Ch) : Set RateTriple :=
  { v | v.c ≤ D.IAXB N ∧ v.c ≤ D.IXB N + D.coh N + D.ent N }

/-! ## Resource-inequality rates (Ch. 7, 8, 22) -/

/-- Resource rates of the coherent-communication identity (Eq. (7.47)):
`2[q→qq] = [qq] + [q→q]`. -/
structure CoherentRates where
  /-- Rate `[q→qq]`. -/
  q2qq : ℝ
  /-- Rate `[qq]` (ebits). -/
  qq : ℝ
  /-- Rate `[q→q]`. -/
  q2q : ℝ

/-- Unit-resource region interface of Thm 8.1.1: the capacity region `C_U` and
the achievable region `C̃_U` built from unit resources. -/
structure UnitResource where
  /-- The capacity region `C_U`. -/
  capRegion : Set RateTriple
  /-- The achievable region `C̃_U`. -/
  achRegion : Set RateTriple

/-- Resource rates of the trade-off coding inequalities of Ch. 22.  Every field
is the rate of the corresponding resource on the left/right of the paper's
resource inequality. -/
structure TradeoffRates where
  /-- `⟨N⟩`, one use of the channel. -/
  chan : ℝ
  /-- `⟨ρ_AB⟩`, one use of a shared state. -/
  stateRes : ℝ
  /-- `⟨W_{S→AB}:ρ_S⟩`. -/
  Wres : ℝ
  /-- `⟨id_{S→B̂B}:ρ_S⟩`. -/
  idRes : ℝ
  /-- `H(A)_ρ[qq]`. -/
  HA : ℝ
  /-- `H(A|X)_ρ[qq]`. -/
  HAX : ℝ
  /-- `I(A;B)_ρ[c→c]`. -/
  IABc : ℝ
  /-- `I(A;B)_ρ[q→qq]`. -/
  IABq : ℝ
  /-- `I(A;B)_ρ[q→q]`. -/
  IABq2q : ℝ
  /-- `I(A;B)_φ[qq]`. -/
  IABqq : ℝ
  /-- `I(A;E)_φ[qq]`. -/
  IAE : ℝ
  /-- `I(A;R)_φ[q→q]`. -/
  IARq : ℝ
  /-- `I(A;R)_φ[c→c]`. -/
  IARcc : ℝ
  /-- `I(A⟩B)_φ[qq]`. -/
  cohABqq : ℝ
  /-- `Q(N)[q→q]`, the coherent information as a quantum rate. -/
  coh : ℝ
  /-- `I(A;B|X)_ρ[q→qq]`. -/
  cmiABq : ℝ
  /-- `I(A;B|X)_ρ[q→q]`. -/
  cmiABq2q : ℝ
  /-- `I(A;E|X)_ρ[qq]`. -/
  cmiAE : ℝ
  /-- `I(A⟩BX)_ρ[q→q]`. -/
  cohBX : ℝ
  /-- `I(X;B)_ρ[c→c]`. -/
  IXBc : ℝ

/-! ## Source / entanglement interfaces (Ch. 18, 19, 24) -/

/-- Interface for the quantum data-compression theorem (Thm 18.2.1): the source
density `ρ` and the operational compression limit of the i.i.d. source
`ρ^{⊗n}`. -/
structure CompressionSource (A : Type) [Fintype A] [DecidableEq A] where
  /-- The source density operator. -/
  ρ : Density A
  /-- The operational data-compression limit. -/
  compLimit : ℝ

/-- Interface for the entanglement-manipulation theorem (Thm 19.4.1): a pair of
pure bipartite states and the asymptotic LOCC conversion rate `ψ → φ`. -/
structure EntManipInfo (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] where
  /-- The source state `ψ`. -/
  ψ : Density (A × B)
  /-- The target state `φ`. -/
  φ : Density (A × B)
  /-- The asymptotic LOCC conversion rate. -/
  convRate : ℝ

/-- Interface for the Devetak–Winter entanglement-distillation theorem
(Thm 24.9.1): a shared state and a distillable-ebit rate per copy under
forward classical communication. -/
structure DistillInfo (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] where
  /-- The shared state `ρ_AB`. -/
  ρ : Density (A × B)
  /-- The achievable ebit rate per copy. -/
  rate : ℝ

/-! ## Feedback and stabiliser-code interfaces (Ch. 21, 24) -/

/-- Feedback capacities of a classical/quantum channel (Thm 21.5.1–21.5.2 and
Cor. 21.5.1). -/
structure FeedbackCaps where
  /-- The channel type. -/
  Ch : Type
  /-- Capacity without feedback. -/
  capNoFb : Ch → ℝ
  /-- Capacity with classical feedback. -/
  capFb : Ch → ℝ
  /-- The single-letter mutual information `max_p I(p;W)`. -/
  maxMutualInfo : Ch → ℝ
  /-- Entanglement-assisted classical capacity. -/
  capEA : Ch → ℝ
  /-- Entanglement-assisted classical capacity with quantum feedback. -/
  capFbEA : Ch → ℝ
  /-- Capacity with unlimited entanglement and classical feedback. -/
  capFbInfEnt : Ch → ℝ

/-- Interface for the hashing-bound theorem (Thm 24.6.2): Pauli-channel error
probabilities and the best stabiliser-code rate. -/
structure HashingCode where
  /-- Probability of an `I` error. -/
  pI : ℝ
  /-- Probability of an `X` error. -/
  pX : ℝ
  /-- Probability of a `Y` error. -/
  pY : ℝ
  /-- Probability of a `Z` error. -/
  pZ : ℝ
  /-- The rate of the stabiliser code. -/
  rate : ℝ

/-! ## Secret-key-assisted and pure-loss interfaces (Ch. 23, 25) -/

/-- Interface for the secret-key-assisted private classical capacity region
(Thm 23.5.1): the region of `(P, S)` pairs and the single-letter entropies
`I(X;B)`, `I(X;E)`. -/
structure SkaInfo where
  /-- The channel type. -/
  Ch : Type
  /-- `k`-fold tensor power. -/
  tensorPow : Ch → ℕ → Ch
  /-- The capacity region, as a set of `(P, S)` rates. -/
  capRegion : Ch → Set (ℝ × ℝ)
  /-- `I(X;B)_σ`. -/
  IXB : Ch → ℝ
  /-- `I(X;E)_σ`. -/
  IXE : Ch → ℝ

/-- The single-letter secret-key-assisted region: `P ≤ I(X;B)−I(X;E)+S` and
`P ≤ I(X;B)`, for the pair `(P, S)`. -/
def SkaInfo.slRegion (S : SkaInfo) (N : S.Ch) : Set (ℝ × ℝ) :=
  { v | v.1 ≤ S.IXB N - S.IXE N + v.2 ∧ v.1 ≤ S.IXB N }

/-- Scale a `(P, S)`-region by `1/k`. -/
def scaleRegion2 (k : ℕ) (R : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  { x | ∃ y ∈ R, x = ((k : ℝ)⁻¹ * y.1, (k : ℝ)⁻¹ * y.2) }

/-- Regularised union of a `(P, S)`-region family. -/
def regUnion2 (f : ℕ → Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  ⋃ k ∈ Set.Ici 1, scaleRegion2 k (f k)

/-- Interface for the pure-loss bosonic-channel dynamic region of Thm 25.5.4
(conditional on Guha's Strong Conjecture 2).  `g` is the entropy
`g(N)=(N+1)log(N+1)−N log N` of Eq. (25.217). -/
structure PureLossInfo where
  /-- The entropy function `g`. -/
  g : ℝ → ℝ
  /-- The dynamic capacity region. -/
  dynRegion : Set RateTriple
  /-- Transmissivity `η`. -/
  η : ℝ
  /-- Mean input photon number `N_S`. -/
  NS : ℝ

end

end Qatlib.Papers.QShannonWilde11.MainResults.Model

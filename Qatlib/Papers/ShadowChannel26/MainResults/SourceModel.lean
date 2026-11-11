/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Source model for *Optimal classical shadow estimation of unitary channels at Heisenberg limit*

Fixed source: arXiv:2606.13638v2 (2026-09-29), "Optimal classical shadow estimation of
unitary channels at Heisenberg limit", He–Li–Scully–Zhou–Yang.

This file fixes the paper-layer vocabulary used by the claim statements in the sibling
directories. It deliberately defines the *objects named in the paper* (operators, unitaries,
density matrices, the observable class `Obs(B)` of Problem 2.1, Pauli transfer matrix
entries, Hamiltonian Pauli coefficients) and the *protocol interfaces* on which the paper's
query/time complexity statements are phrased. Nothing here asserts a paper result; the
theorems live in the per-claim modules.

## Modelling convention (read before judging faithfulness)

* A `d`-dimensional operator is a `d × d` complex matrix `Op d`.
* The spectral norm `‖O‖` is Mathlib's matrix ℓ²-operator norm, activated through the
  `Matrix.Norms.L2Operator` scope; the trace norm is Physlib's `Matrix.traceNorm`.
* A protocol is a *finite-randomness* algorithm: its randomness is a finite seed space `Ω`
  with a probability mass function. The success probability is the exact sum of the masses
  of the "good" seeds, so `Pr[·] ≥ 2/3` in Problem 2.1 is encoded verbatim.
* Asymptotic statements `O(g)` are encoded by a universal positive constant `C`
  (`IsBigO`), `Ω(g)` by a universal positive constant `c` (`IsBigOmega`), and `Õ(g)` /
  `Ω̃(g)` by a universal constant times an arbitrary fixed power of
  `1 + log d + log(1/ε)` (`IsSoftBigO` / `IsSoftBigOmega`), which is the standard meaning of
  soft-O with polylogarithmic suppression.
-/

namespace Qatlib.Papers.ShadowChannel26.MainResults.SourceModel

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath (Reg)
open Qatlib.Concepts.PauliClifford.PauliAlgebra (PauliWord pauliWordOp)

universe u

/-! ## Operators, unitaries, states, observables -/

/-- A `d`-dimensional complex operator `ℂ^{d×d}`. -/
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- `U ∈ U(d)`: a unitary operator (paper §2, "For a unitary operator `U`").  Stated for an
arbitrary finite index type so that it applies to both `Op d` and the `n`-qubit `NOp n`. -/
def IsUnitary {I : Type u} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- A legitimate quantum state (density operator) `ρ ∈ D(ℋ)`: positive semidefinite and
trace one (paper §2 / Appendix A.2). -/
def IsDensity {I : Type u} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Purity `tr[ρ²]` of a state, as a real number. -/
noncomputable def purity {I : Type u} [Fintype I] [DecidableEq I]
    (ρ : Matrix I I ℂ) : ℝ := (ρ * ρ).trace.re

/-- The traceless part `O₀ := O − tr(O)·I/d` appearing in the definition of `Obs(B)`
(Problem 2.1, p. 4). -/
noncomputable def tracelessPartMat {I : Type u} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) : Matrix I I ℂ :=
  O - ((O.trace / (Fintype.card I : ℂ)) • (1 : Matrix I I ℂ))

/-- The observable class `Obs(B)` of Problem 2.1 (p. 4):
`O = O†`, `‖O‖_∞ = 1`, and `tr(O₀²) ≤ B` with `O₀ = O − tr(O)·I/d`. -/
noncomputable def Obs {I : Type u} [Fintype I] [DecidableEq I]
    (B : ℝ) (O : Matrix I I ℂ) : Prop :=
  O.IsHermitian ∧ ‖O‖ = 1 ∧ ((tracelessPartMat O * tracelessPartMat O).trace).re ≤ B

/-- The Hilbert–Schmidt inner product `tr(A† B)`. -/
noncomputable def hsInner {d : ℕ} (A B : Op d) : ℂ := (Aᴴ * B).trace

/-- Frobenius norm `‖A‖_F = √(tr(A† A))`. -/
noncomputable def frobeniusNorm {d : ℕ} (A : Op d) : ℝ :=
  Real.sqrt ((Aᴴ * A).trace).re

/-! ## Asymptotic vocabulary -/

/-- One-sided `O(·)` for functions of `(d, ε)` at fixed `B`: a universal positive constant
controls the ratio throughout the parameter range `1 ≤ d`, `0 < ε < 1`. -/
def IsBigO (F G : ℕ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (ε : ℝ), 1 ≤ d → 0 < ε → ε < 1 →
    F d ε ≤ C * G d ε

/-- One-sided `Ω(·)` (lower bound) with a universal positive constant. -/
def IsBigOmega (F G : ℕ → ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ), 1 ≤ d → 0 < ε → ε < 1 →
    c * G d ε ≤ F d ε

/-- Soft-`O(·)` (`Õ`): a universal constant times `g` times an arbitrary fixed power of the
polylogarithmic weight `1 + log d + log(1/ε)`. -/
def IsSoftBigO (F G : ℕ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (d : ℕ) (ε : ℝ), 1 ≤ d → 0 < ε → ε < 1 →
    F d ε ≤ C * G d ε * (1 + Real.log (d : ℝ) + Real.log (1 / ε)) ^ k

/-- Soft-`Ω(·)` (`Ω̃`). -/
def IsSoftBigOmega (F G : ℕ → ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ (d : ℕ) (ε : ℝ), 1 ≤ d → 0 < ε → ε < 1 →
    c * G d ε * (1 + Real.log (d : ℝ) + Real.log (1 / ε)) ^ k ≤ F d ε

/-- The query bound of Theorem 2.3: `min{d/ε² + √(dB)/ε, d^{3/2}/ε}` (p. 5). -/
noncomputable def theorem23Bound (d : ℕ) (B ε : ℝ) : ℝ :=
  min ((d : ℝ) / ε ^ 2 + Real.sqrt ((d : ℝ) * B) / ε)
    (((d : ℝ) * Real.sqrt (d : ℝ)) / ε)

/-- The query lower bound of Theorem 2.4: `min{d/ε², d^{3/2}/ε}` (p. 5). -/
noncomputable def theorem24Bound (d : ℕ) (_B ε : ℝ) : ℝ :=
  min ((d : ℝ) / ε ^ 2) (((d : ℝ) * Real.sqrt (d : ℝ)) / ε)

/-! ## The CSEU problem (Problem 2.1) -/

/-- Oracle access model for CSEU protocols.  Problem 2.1 uses parallel queries to `U`;
Theorem 2.4 strengthens the model to black-box queries to `U`, `U†`, `cU`, `cU†`. -/
inductive AccessModel
  | parallel
  | coherentFull
  deriving DecidableEq, Repr

/-- A CSEU protocol: finite randomness `Ω` with weights `prob`, a classical shadow
`shadow ω U ∈ {0,1}*` (encoded as `String`), a deterministic prediction function
`predict`, and its resource usage (`queryCount` parallel oracle queries, `storageSize`
bits of classical data, `predictTime` classical operations). -/
structure CSEUProtocol (d : ℕ) where
  Ω : Type
  instFintype : Fintype Ω
  prob : Ω → ℝ
  access : AccessModel
  queryCount : ℕ
  storageSize : ℕ
  predictTime : ℕ
  shadow : Ω → Op d → String
  predict : String → Op d → Op d → ℝ

namespace CSEUProtocol

variable {d : ℕ}

/-- `prob` is a probability mass function: nonnegative and normalised. -/
noncomputable def IsProbability (P : CSEUProtocol d) : Prop := by
  classical
  letI := P.instFintype
  exact (∀ ω, 0 ≤ P.prob ω) ∧ (∑ ω, P.prob ω) = 1

/-- Success probability of a protocol on a fixed request `(ρ, O)` and unitary `U`, under the
guarantee `|f(CS(U),ρ,O) − tr[OUρU†]| ≤ ε`.  This is exactly the probability appearing in
Problem 2.1, eq. (1). -/
noncomputable def successProb (P : CSEUProtocol d) (ε : ℝ) (U ρ O : Op d) : ℝ := by
  classical
  letI := P.instFintype
  exact (Finset.univ.filter
    (fun ω => |P.predict (P.shadow ω U) ρ O - ((O * U * ρ * Uᴴ).trace).re| ≤ ε)).sum P.prob

end CSEUProtocol

/-- A protocol *solves* Problem 2.1 for observable class `Obs(B)` at accuracy `ε`: it is a
valid distribution and for every unitary `U`, state `ρ` and observable `O ∈ Obs(B)` the
prediction is within `ε` with probability at least `2/3` (eq. (1)). -/
noncomputable def SolvesCSEU {d : ℕ} (B ε : ℝ) (P : CSEUProtocol d) : Prop :=
  P.IsProbability ∧
    ∀ (U ρ O : Op d), IsUnitary U → IsDensity ρ → Obs B O →
      (2 / 3 : ℝ) ≤ P.successProb ε U ρ O

/-! ## The strengthened request class `R_{P,B}` (Theorem 4.2) -/

/-- The purity-restricted request class `R_{P,B}` of Theorem 4.2 (p. 20):
`ρ` a state with `tr[ρ²] ≤ P`, `O ∈ Obs(B)`, and `BP ≥ 1`. -/
noncomputable def InRequestClass {I : Type u} [Fintype I] [DecidableEq I]
    (Pp B : ℝ) (ρ O : Matrix I I ℂ) : Prop :=
  IsDensity ρ ∧ purity ρ ≤ Pp ∧ Obs B O ∧ 1 ≤ B * Pp

/-- A protocol *solves* Problem 4.1 on the restricted class `R_{P,B}`. -/
noncomputable def SolvesCSEURestricted {d : ℕ} (Pp B ε : ℝ) (P : CSEUProtocol d) : Prop :=
  P.IsProbability ∧
    ∀ (U ρ O : Op d), IsUnitary U → InRequestClass Pp B ρ O →
      (2 / 3 : ℝ) ≤ P.successProb ε U ρ O

/-! ## Pauli transfer matrices and n-qubit operators -/

/-- The `n`-qubit operator space, indexed by the register `Reg n = Fin n → Bool`. -/
abbrev NOp (n : ℕ) := Matrix (Reg n) (Reg n) ℂ

/-- Real dimension `d = 2^n` of the `n`-qubit Hilbert space. -/
noncomputable def qubitDim (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- A Pauli transfer matrix entry `R_U(p,p') = (1/d) tr(σ_p U σ_{p'} U†)` (Section 3.2). -/
noncomputable def ptmEntry {n : ℕ} (U : NOp n) (p q : PauliWord n) : ℝ :=
  ((pauliWordOp n p * U * pauliWordOp n q * Uᴴ).trace / (2 : ℂ) ^ n).re

/-- Normalised Pauli coefficient `μ_H(p) = (1/d) tr(σ_p H)` of an `n`-qubit operator. -/
noncomputable def pauliCoeff {n : ℕ} (H : NOp n) (p : PauliWord n) : ℝ :=
  ((pauliWordOp n p * H).trace / (2 : ℂ) ^ n).re

/-! ## Hamiltonian learning interfaces -/

/-- A Hamiltonian-learning protocol for traceless `n`-qubit Hamiltonians observed through
real-time evolution `e^{-iHt}`: finite randomness, a per-Pauli estimate, a number of
parallel evolution queries, and a total evolution time (Section 3.1 / Appendix D). -/
structure HamLearnProtocol (n : ℕ) where
  Ω : Type
  instFintype : Fintype Ω
  prob : Ω → ℝ
  queryCount : ℕ
  totalEvoTime : ℝ
  estimate : Ω → NOp n → PauliWord n → ℝ

namespace HamLearnProtocol

variable {n : ℕ}

/-- `prob` is a probability mass function. -/
noncomputable def IsProbability (P : HamLearnProtocol n) : Prop := by
  classical
  letI := P.instFintype
  exact (∀ ω, 0 ≤ P.prob ω) ∧ (∑ ω, P.prob ω) = 1

/-- Success probability that *all* Pauli coefficients are estimated to normalised error `ε`
(`|μ̂_H(p) − μ_H(p)| ≤ ε‖H‖_∞` for every `p`). -/
noncomputable def successProb (P : HamLearnProtocol n) (ε : ℝ) (H : NOp n) : ℝ := by
  classical
  letI := P.instFintype
  exact (Finset.univ.filter
    (fun ω => ∀ p, |P.estimate ω H p - pauliCoeff H p| ≤ ε * ‖H‖)).sum P.prob

end HamLearnProtocol

/-- The protocol learns all Pauli coefficients of every traceless Hermitian `H` to normalised
error `ε` with probability at least `2/3` (Theorem 3.1/Proposition D.1, eq. (43)). -/
noncomputable def SolvesHamLearning {n : ℕ} (ε : ℝ) (P : HamLearnProtocol n) : Prop :=
  P.IsProbability ∧
    ∀ H : NOp n, H.IsHermitian → H.trace = 0 →
      (2 / 3 : ℝ) ≤ P.successProb ε H

/-- Piecewise total-evolution-time profile of Theorem 3.1, eq. (2):
`d/(‖H‖ε)` for `ε ≤ d^{-3/2}`, `d^{7/4}/(‖H‖√ε)` for `d^{-3/2} < ε ≤ d^{-3/4}`, and
`d/(‖H‖ε^{3/2})` for `d^{-3/4} < ε < 1`, where `d = 2^n`. -/
noncomputable def theorem31TimeBound (n : ℕ) (ε : ℝ) : ℝ :=
  let d : ℝ := qubitDim n
  if ε ≤ d ^ (-(3 / 2 : ℝ)) then d / ε
  else if ε ≤ d ^ (-(3 / 4 : ℝ)) then d ^ (7 / 4 : ℝ) / Real.sqrt ε
  else d / ε ^ (3 / 2 : ℝ)

/-- Piecewise query profile `K_Ham` of Proposition D.1, eq. (41). -/
noncomputable def propD1QueryBound (n : ℕ) (ε : ℝ) : ℝ :=
  let d : ℝ := qubitDim n
  if ε ≤ d ^ (-(3 / 2 : ℝ)) then d / ε
  else if ε ≤ d ^ (-(3 / 4 : ℝ)) then d ^ (7 / 4 : ℝ) / Real.sqrt ε
  else d / ε ^ (3 / 2 : ℝ)

/-! ## PTM-learning interface (Theorem 3.2) -/

/-- A parallel, non-adaptive PTM-learning protocol estimating all `d⁴` entries of the Pauli
transfer matrix of an unknown `U ∈ U(d)`. -/
structure PTMLearnProtocol (n : ℕ) where
  Ω : Type
  instFintype : Fintype Ω
  prob : Ω → ℝ
  queryCount : ℕ
  estimate : Ω → NOp n → PauliWord n → PauliWord n → ℝ

namespace PTMLearnProtocol

variable {n : ℕ}

/-- `prob` is a probability mass function. -/
noncomputable def IsProbability (P : PTMLearnProtocol n) : Prop := by
  classical
  letI := P.instFintype
  exact (∀ ω, 0 ≤ P.prob ω) ∧ (∑ ω, P.prob ω) = 1

/-- Success probability that every PTM entry is estimated to additive error `ε`. -/
noncomputable def successProb (P : PTMLearnProtocol n) (ε : ℝ) (U : NOp n) : ℝ := by
  classical
  letI := P.instFintype
  exact (Finset.univ.filter
    (fun ω => ∀ p q, |P.estimate ω U p q - ptmEntry U p q| ≤ ε)).sum P.prob

end PTMLearnProtocol

/-- The protocol learns all `d⁴` PTM entries of every unitary to additive error `ε` with
probability at least `2/3` (Theorem 3.2). -/
noncomputable def SolvesPTMLearning {n : ℕ} (ε : ℝ) (P : PTMLearnProtocol n) : Prop :=
  P.IsProbability ∧
    ∀ U : NOp n, IsUnitary U → (2 / 3 : ℝ) ≤ P.successProb ε U

/-- Piecewise query profile `K_PTM` of Theorem 3.2 (p. 9). -/
noncomputable def theorem32QueryBound (n : ℕ) (ε : ℝ) : ℝ :=
  let d : ℝ := qubitDim n
  if ε ≤ d ^ (-(3 / 2 : ℝ)) then d / ε
  else if ε ≤ d ^ (-(3 / 4 : ℝ)) then d ^ (7 / 4 : ℝ) / Real.sqrt ε
  else d / ε ^ (3 / 2 : ℝ)

/-! ## Unitary channel tomography (Proposition 3.4) -/

/-- A unitary-channel tomography protocol: it outputs a classically described channel
`estimate ω U` and the claim is that `‖S_U − U‖_⋄ ≤ ε`.  The diamond norm is taken as an
abstract predicate `diamondClose` (its concrete definition lives in the topology layer). -/
structure ChannelTomographyProtocol (d : ℕ) where
  Ω : Type
  instFintype : Fintype Ω
  prob : Ω → ℝ
  queryCount : ℕ
  estimate : Ω → Op d → Op d
  diamondClose : Op d → Op d → ℝ → Prop

namespace ChannelTomographyProtocol

variable {d : ℕ}

/-- `prob` is a probability mass function. -/
noncomputable def IsProbability (P : ChannelTomographyProtocol d) : Prop := by
  classical
  letI := P.instFintype
  exact (∀ ω, 0 ≤ P.prob ω) ∧ (∑ ω, P.prob ω) = 1

/-- Success probability of tomography at diamond error `ε` on `U`. -/
noncomputable def successProb (P : ChannelTomographyProtocol d) (ε : ℝ) (U : Op d) : ℝ := by
  classical
  letI := P.instFintype
  exact (Finset.univ.filter (fun ω => P.diamondClose U (P.estimate ω U) ε)).sum P.prob

end ChannelTomographyProtocol

/-- `SolvesTomography P ε`: for every unitary `U`, the output channel is `ε`-close in diamond
norm with probability at least `2/3` (Corollary 3.5 / Proposition 3.4). -/
noncomputable def SolvesTomography {d : ℕ} (ε : ℝ) (P : ChannelTomographyProtocol d) : Prop :=
  P.IsProbability ∧ ∀ U : Op d, IsUnitary U → (2 / 3 : ℝ) ≤ P.successProb ε U

/-! ## Inverse-free amplitude estimation (Corollary 3.3) -/

/-- The projector `|0⟩⟨0|` on the computational basis vector of index `0`. -/
noncomputable def zeroProjector (d : ℕ) : Op d :=
  Matrix.of fun a b => if (a : ℕ) = 0 ∧ (b : ℕ) = 0 then (1 : ℂ) else 0

/-- The target amplitude `a(U) = tr[Π U |0^n⟩⟨0^n| U†]` of Corollary 3.3. -/
noncomputable def ampVal {d : ℕ} (U Proj : Op d) : ℝ :=
  ((Proj * U * zeroProjector d * Uᴴ).trace).re

/-- An inverse-free amplitude-estimation protocol: queries only forward `U` (never `U†`),
and estimates `a(U) = tr[Π U |0⟩⟨0| U†]` for a known projector `Π`. -/
structure AmpEstProtocol (d : ℕ) where
  Ω : Type
  instFintype : Fintype Ω
  prob : Ω → ℝ
  queryCount : ℕ
  estimate : Ω → Op d → Op d → ℝ

namespace AmpEstProtocol

variable {d : ℕ}

/-- `prob` is a probability mass function. -/
noncomputable def IsProbability (P : AmpEstProtocol d) : Prop := by
  classical
  letI := P.instFintype
  exact (∀ ω, 0 ≤ P.prob ω) ∧ (∑ ω, P.prob ω) = 1

/-- Success probability at additive error `ε` on `(U, Π)`. -/
noncomputable def successProb (P : AmpEstProtocol d) (ε : ℝ) (U Proj : Op d) : ℝ := by
  classical
  letI := P.instFintype
  exact (Finset.univ.filter
    (fun ω => |P.estimate ω U Proj - ampVal U Proj| ≤ ε)).sum P.prob

end AmpEstProtocol

/-- The amplitude-estimation protocol succeeds at error `ε` with probability `≥ 2/3`, for
every unitary `U` and every known projector `Π`. -/
noncomputable def SolvesAmpEst {d : ℕ} (ε : ℝ) (P : AmpEstProtocol d) : Prop :=
  P.IsProbability ∧
    ∀ (U Proj : Op d), IsUnitary U → Proj.IsHermitian → Proj * Proj = Proj →
      (2 / 3 : ℝ) ≤ P.successProb ε U Proj

end Qatlib.Papers.ShadowChannel26.MainResults.SourceModel

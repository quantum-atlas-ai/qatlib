/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Measurements.POVM
import QuantumInfo.States.Mixed.TraceDistance
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# A model layer for `StateTesting26` (arXiv:2604.07460v2)

This module fixes the vocabulary shared by all paper-layer statements of
Wadhwa--Chen, *Optimal Quantum State Testing Even with Limited Entanglement*
(arXiv:2604.07460v2, 2026-09-24, 49 pages).  Nothing here changes the promoted
Frozen/Dev contracts: the definitions are fresh and the existing libraries
(`QuantumInfo.MState`, `QuantumInfo.POVM`, `Matrix.traceNorm`, `MState.npow`)
are only read.

What the model fixes, and why:

* **States.** `QState d` is `MState (Fin d)`, Physlib's density matrix type.
  Trace distance is Physlib's `TrDistance` (half the trace norm of the
  difference), the Hilbert--Schmidt distance is `sqrt (tr (ρ-σ)^2)`, and
  `opNorm` is the `L2` operator norm (`‖ρ.m‖`, matching the paper's `‖ρ‖∞`).
  Purity `tr ρ²` is `MState.purity` read in the reals.

* **Measurement classes** (Section 1.1 of the paper).  A *fixed* `t`-copy
  scheme measures `k` independent blocks, each with one and the same finite
  POVM on `(Fin t → Fin d)`; a *private*-randomness scheme redraws the POVM of
  each block independently from a known distribution; a *shared*-randomness
  scheme draws one POVM once and uses it for all blocks.  Copy complexity is
  `k * t`.  The Born rule is `POVM.measure` applied to the `t`-copy state
  `MState.npow ρ t`, so the success probabilities below are actual quantum
  probabilities, not free parameters.

* **Tasks.**  `FixedCertifies`/`PrivateCertifies`/`SharedCertifies` encode
  `ε`-trace-norm certification of a known hypothesis state `σ` at confidence
  `99/100` (the paper's `.99`); `FixedCertifiesConf` is the `1-δ` version used
  in Theorem 4.2.  `MixednessTestable` is mixedness testing against the
  maximally mixed state, `PurityEstimable` is `tr ρ²` up to multiplicative
  error, `HSTestable`/`HSPairTestable` are the Hilbert--Schmidt testers of
  Theorem 4.3/4.6 and Appendix A.

* **Haar moments.**  The paper averages over uniformly random pure states.  The
  library has no Haar measure on complex projective space, so a pure state is
  modelled by its rank-one projector `P` (a matrix satisfying `IsPureProj`),
  a *uniform* pure-state law is a probability measure `μ` on matrices that is
  supported on pure projectors and invariant under conjugation by unitaries
  (`IsUnitaryInvariant`).  This is exactly the defining property of the Haar
  law pushed forward to projectors, and it makes every moment statement of
  Section 2--3 a genuine integral identity rather than a restatement of its own
  right-hand side.

* **Asymptotic vocabulary.**  The paper writes `O(·)`, `Õ(·)` and `Ω(·)`.
  Statements that suppress constants are recorded with an explicit positive
  constant `C`; `Õ` additionally carries an existential polylog exponent
  through `logFactor x k = (log (x+2))^k` (`IsPolylogFactor` records what an
  `Õ` factor may be).  The max/min structure displayed in the paper is kept
  literally in the bound functions below.

All definitions are `noncomputable`; none introduces an axiom.
-/

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator ENNReal

namespace Qatlib.Papers.StateTesting26.MainResults.Model

set_option autoImplicit false
noncomputable section

/-! ## Matrix measurable structure

Matrices are functions `m → n → ℂ`, so the product measurable structure is the
canonical one.  Registering it here makes `Measure (Matrix ...)` available to
the Haar-moment statements. -/

instance instMeasurableSpaceMatrix {m n : Type*} [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

instance instBorelSpaceMatrix {m n : Type*} [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

/-! ## States and distances -/

/-- A `d`-dimensional quantum state: a density matrix on `Fin d`. -/
abbrev QState (d : ℕ) := MState (Fin d)

/-- Trace distance between states, i.e. half the trace norm of the difference
(Paper Def. 2.2 / Eq. (4.1) context). -/
def qdist {d : ℕ} (ρ σ : QState d) : ℝ := TrDistance ρ σ

/-- Purity `tr ρ²` of a state, as a real number (used in Theorem 1.4). -/
def purityReal {d : ℕ} (ρ : QState d) : ℝ := (MState.purity ρ : ℝ)

/-- Squared Hilbert--Schmidt distance `tr ((ρ-σ)²)` (Paper Eq. (4.4)-(4.8)). -/
def hsSqDist {d : ℕ} (ρ σ : QState d) : ℝ :=
  ((ρ.m - σ.m) * (ρ.m - σ.m)).trace.re

/-- Hilbert--Schmidt distance `‖ρ-σ‖₂` (Paper Thm 4.3). -/
def hsDist {d : ℕ} (ρ σ : QState d) : ℝ := Real.sqrt (hsSqDist ρ σ)

/-- Operator norm `‖ρ‖∞` of a state (Paper Cor. 4.4; the `L2` operator norm on
matrices is the spectral norm). -/
def opNorm {d : ℕ} (ρ : QState d) : ℝ := ‖ρ.m‖

/-- The maximally mixed state `ρ_mm = I/d` (Paper Section 1.1). -/
def maximallyMixed (d : ℕ) (hd : 0 < d) : QState d :=
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  MState.uniform (d := Fin d)

/-- `tr(ρσ)`, the overlap that appears in Theorem 4.3. -/
def overlap {d : ℕ} (ρ σ : QState d) : ℝ := (ρ.m * σ.m).trace.re

/-! ## Pure states and their tensor moments -/

/-- A rank-one projector on an arbitrary finite index type: `P² = P`, `P ≥ 0`,
`tr P = 1`.  This is the model of a Haar-random pure state used by every
moment statement (Section 2.1, 3.1). -/
def IsPureProjOn {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ P * P = P ∧ Matrix.trace P = 1

/-- A rank-one projector on `ℂ^d` (specialisation of `IsPureProjOn`). -/
def IsPureProj {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) : Prop := IsPureProjOn P

/-- A measure on pure projectors is *uniform* (Haar) when it is invariant under
conjugation by every unitary.  This is the defining property of the Haar law on
complex projective space, transported to the projector picture. -/
def IsUnitaryInvariant {d : ℕ} (μ : Measure (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    Measure.map
      (fun P => (U : Matrix (Fin d) (Fin d) ℂ) * P * star (U : Matrix (Fin d) (Fin d) ℂ)) μ = μ

/-- The `k`-th tensor power of a matrix, indexed by `Fin k → Fin d`.  Its
entries are `∏ a, A (i a) (j a)`, the standard Kronecker convention. -/
def tensorPowerMat {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  fun i j => ∏ a, A (i a) (j a)

/-- A measure on `n`-register pure projectors is *uniform on the symmetric
subspace* when it is invariant under conjugation by `U^{⊗n}` for every
unitary `U` on `ℂ^d` (the symmetry group of `∨^n ℂ^d` used by Hayashi's POVM). -/
def IsTensorUnitaryInvariant {d n : ℕ}
    (μ : Measure (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    Measure.map
      (fun Q => tensorPowerMat (U : Matrix (Fin d) (Fin d) ℂ) n * Q *
        star (tensorPowerMat (U : Matrix (Fin d) (Fin d) ℂ) n)) μ = μ

/-- The permutation operator `V_d(π)` of Paper Eq. (2.4)/(2.5), acting on
`(ℂ^d)^{⊗k}` by permuting the `k` tensor factors. -/
def permMat {d k : ℕ} (π : Equiv.Perm (Fin k)) :
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  fun i j => if (fun a => i (π a)) = j then 1 else 0

/-- The symmetric projector `Π^k_sym = (1/k!) ∑_π V_d(π)` (Paper Eq. (2.5)). -/
def symProj (d k : ℕ) : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  ((Nat.factorial k : ℝ)⁻¹) • ∑ π : Equiv.Perm (Fin k), permMat (d := d) π

/-- `d^[k] = d(d+1)…(d+k-1)`, the dimension `choose (d+k-1) k` of the symmetric
subspace `∨^k ℂ^d` (Paper Def. 2.4). -/
def dPowRising (d k : ℕ) : ℕ := Finset.prod (Finset.range k) (fun i => d + i)

/-- `d^[k]` read in the reals. -/
def dPowRisingR (d k : ℕ) : ℝ := (dPowRising d k : ℝ)

/-- The dimension of the symmetric subspace, as `choose (d+k-1) k`. -/
def dimSym (d k : ℕ) : ℕ := Nat.choose (d + k - 1) k

/-- `SWAP` on the first two tensor factors of `(ℂ^d)^{⊗2}` (Paper Eq. (3.2)). -/
def swapTwo {d : ℕ} : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  fun i j => if (i 0 = j 1 ∧ i 1 = j 0) then 1 else 0

/-- `ρ ⊗ I` on `(ℂ^d)^{⊗2}`, i.e. the first factor carries `ρ` (Paper Eq. (3.2)). -/
def kronFirst {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  fun i j => ρ (i 0) (j 0) * (if i 1 = j 1 then 1 else 0)

/-- `I ⊗ ρ` on `(ℂ^d)^{⊗2}` (Paper Eq. (3.2)). -/
def kronSecond {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  fun i j => (if i 0 = j 0 then 1 else 0) * ρ (i 1) (j 1)

/-! ## Reduced states on the symmetric subspace

For a state on `(ℂ^d)^{⊗(m+1)}` we need the one-register reduction
`(ψsym)_1` and the two-register reduction `(ψsym)_{1,2}` on the first
registers, together with their amplifications by identities on the remaining
registers (Paper Lemma 3.5, Eq. (3.3)-(3.4)). -/

/-- First-register reduction `tr_{2..m+1}` of a matrix on `(ℂ^d)^{⊗(m+1)}`;
this is `(ψsym)_1` of Paper Lemma 3.5. -/
def reduceFirst {d m : ℕ} (X : Matrix (Fin (m + 1) → Fin d) (Fin (m + 1) → Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ i : Fin m → Fin d, X (Fin.cons a i) (Fin.cons b i)

/-- Two-register reduction of a matrix on `(ℂ^d)^{⊗(m+2)}` on the first two
registers; this is `(ψsym)_{1,2}` of Paper Lemma 3.5, Eq. (3.4). -/
def reduceFirstTwo {d m : ℕ}
    (X : Matrix (Fin (m + 2) → Fin d) (Fin (m + 2) → Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  fun a b => ∑ i : Fin m → Fin d,
    X (Fin.cons (a 0) (Fin.cons (a 1) i)) (Fin.cons (b 0) (Fin.cons (b 1) i))

/-! ## The uniform POVM and Hayashi's POVM moments (Paper Section 3.1-3.2)

The uniform POVM has outcome density `d · tr(Pρ) dP` over pure projectors `P`;
Hayashi's POVM on `∨^n ℂ^d` has outcome density `d^[n] · tr(P ψsym) dP` over
symmetric pure projectors `P`.  The moment operators below are the *right-hand
sides* of the paper's displays (3.1)-(3.4) and (3.23). -/

/-- RHS of Lemma 3.2, Eq. (3.1): `(ρ + I)/(d+1)`. -/
def uniformFirstMoment {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℝ) + 1)⁻¹ • (ρ + 1)

/-- RHS of Lemma 3.3, Eq. (3.2). -/
def uniformSecondMoment {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  (((d : ℝ) + 1) * ((d : ℝ) + 2))⁻¹ •
    (1 + swapTwo + (kronFirst ρ + kronSecond ρ) + (kronFirst ρ + kronSecond ρ) * swapTwo)

/-- RHS of Lemma 3.5, Eq. (3.3): `I/(d+n) + n/(d+n) (ψsym)_1`, an operator on
one register.  The ambient copy number is `n = m+1`. -/
def hayashiFirstMoment {d m : ℕ}
    (ψsym : Matrix (Fin (m + 1) → Fin d) (Fin (m + 1) → Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (((d : ℝ) + (m + 1)))⁻¹ • 1 +
    (((m + 1 : ℕ) : ℝ) / ((d : ℝ) + (m + 1))) • reduceFirst ψsym

/-- RHS of Lemma 3.5, Eq. (3.4), written with the reduced one- and two-register
states; an operator on two registers.  The ambient copy number is `n = m+2`. -/
def hayashiSecondMoment {d m : ℕ}
    (ψsym : Matrix (Fin (m + 2) → Fin d) (Fin (m + 2) → Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  let A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
    kronFirst (reduceFirst (m := m + 1) ψsym) + kronSecond (reduceFirst (m := m + 1) ψsym)
  ((((d : ℝ) + (m + 2)) * ((d : ℝ) + (m + 2) + 1)))⁻¹ •
    (1 + swapTwo
      + ((m + 2 : ℕ) : ℝ) • (A * (1 + swapTwo))
      + (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1)) • reduceFirstTwo ψsym)

/-- The AGP_S estimator of Definition 3.6: `σ̂_ψ = (d+n)/n |ψ⟩⟨ψ| − (1/n) I`. -/
def agpEstimator {d n : ℕ} (P : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  (((d : ℝ) + n) / (n : ℝ)) • P - ((n : ℝ)⁻¹) • 1

/-- RHS of Lemma 3.8, Eq. (3.23): the exact second moment of `AGP_S`, an
operator on two registers.  The ambient copy number is `n = m+2`. -/
def agpSecondMoment {d m : ℕ}
    (ψsym : Matrix (Fin (m + 2) → Fin d) (Fin (m + 2) → Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  let n : ℕ := m + 2
  let one : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ := 1
  let A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
    kronFirst (reduceFirst (m := m + 1) ψsym) + kronSecond (reduceFirst (m := m + 1) ψsym)
  let ψ12 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ := reduceFirstTwo ψsym
  (((n : ℝ) - 1) / (n : ℝ) * (((d : ℝ) + n) / ((d : ℝ) + n + 1))) • ψ12
    + ((1 / (n : ℝ)) * (((d : ℝ) + n) / ((d : ℝ) + n + 1))) • (A * swapTwo)
    - (1 / ((n : ℝ) * ((d : ℝ) + n + 1))) • A
    + ((1 / (n : ℝ) ^ 2) * (((d : ℝ) + n) / ((d : ℝ) + n + 1))) • swapTwo
    - (1 / ((n : ℝ) ^ 2 * ((d : ℝ) + n + 1))) • one

/-! ## Measurement schemes -/

/-- One round of a `t`-copy measurement gives outcome `ω` with the Born
probability of `POVM.measure` on the `t`-copy state. -/
def roundProb {d t : ℕ} {Ω : Type} [Fintype Ω] (Λ : POVM Ω (Fin t → Fin d))
    (ρ : QState d) (ω : Ω) : ℝ := ((Λ.measure (MState.npow ρ t)) ω : ℝ)

/-- A **fixed** `t`-copy scheme with `k` blocks: the same POVM is measured on
each block, and a deterministic Boolean decision is applied to the `k` outcomes
(randomised decisions are absorbed into the decision rule without loss of
generality). -/
structure FixedTCopyScheme (d t k : ℕ) (Ω : Type) [Fintype Ω] where
  /-- The POVM measured on every `t`-copy block. -/
  povm : POVM Ω (Fin t → Fin d)
  /-- Whether the scheme accepts the hypothesis `ρ = σ`. -/
  accept : (Fin k → Ω) → Bool

namespace FixedTCopyScheme

/-- Acceptance probability of a fixed `t`-copy scheme on the state `ρ`. -/
def acceptProb {d t k : ℕ} {Ω : Type} [Fintype Ω]
    (S : FixedTCopyScheme d t k Ω) (ρ : QState d) : ℝ :=
  ∑ x : Fin k → Ω, if S.accept x then ∏ r, roundProb S.povm ρ (x r) else 0

end FixedTCopyScheme

/-- A **shared-randomness** non-adaptive scheme: one POVM is drawn once from
`seedProb` and used for every block (Paper Section 1.1: "several different
measurements may be drawn from a shared source of randomness"). -/
structure SharedScheme (d t k : ℕ) (Seed Ω : Type) [Fintype Seed] [Fintype Ω] where
  seedProb : Seed → ℝ
  seedProb_nonneg : ∀ s, 0 ≤ seedProb s
  seedProb_sum : ∑ s, seedProb s = 1
  povm : Seed → POVM Ω (Fin t → Fin d)
  accept : (Fin k → Ω) → Bool

namespace SharedScheme

/-- Acceptance probability of a shared-randomness scheme. -/
def acceptProb {d t k : ℕ} {Seed Ω : Type} [Fintype Seed] [Fintype Ω]
    (S : SharedScheme d t k Seed Ω) (ρ : QState d) : ℝ :=
  ∑ s, S.seedProb s *
    (∑ x : Fin k → Ω, if S.accept x then ∏ r, roundProb (S.povm s) ρ (x r) else 0)

end SharedScheme

/-- A **private-randomness** scheme: the POVM of every block is redrawn
independently from `seedProb` (Paper Section 1.1: "when such shared randomness
is unavailable, we say that these are private measurements"). -/
structure PrivateScheme (d t k : ℕ) (Seed Ω : Type) [Fintype Seed] [Fintype Ω] where
  seedProb : Seed → ℝ
  seedProb_nonneg : ∀ s, 0 ≤ seedProb s
  seedProb_sum : ∑ s, seedProb s = 1
  povm : Seed → POVM Ω (Fin t → Fin d)
  accept : (Fin k → Ω) → Bool

namespace PrivateScheme

/-- Acceptance probability of a private-randomness scheme (the seeds of the `k`
blocks are independent). -/
def acceptProb {d t k : ℕ} {Seed Ω : Type} [Fintype Seed] [Fintype Ω]
    (S : PrivateScheme d t k Seed Ω) (ρ : QState d) : ℝ :=
  ∑ x : Fin k → Ω, if S.accept x then
    ∏ r, ∑ s, S.seedProb s * roundProb (S.povm s) ρ (x r) else 0

end PrivateScheme

/-! ## Certification tasks -/

/-- `ε`-trace-norm certification of `σ` at confidence `99/100`, measured by a
fixed `t`-copy scheme (Paper Def. 2.2 and Theorem 1.1). -/
def FixedCertifies {d t k : ℕ} {Ω : Type} [Fintype Ω]
    (S : FixedTCopyScheme d t k Ω) (σ : QState d) (ε : ℝ) : Prop :=
  (∀ ρ : QState d, qdist ρ σ ≤ ε → (99 / 100 : ℝ) ≤ S.acceptProb ρ) ∧
  (∀ ρ : QState d, ε < qdist ρ σ → S.acceptProb ρ ≤ (1 / 100 : ℝ))

/-- `ε`-trace-norm certification of `σ` at confidence `1-δ` (Paper Theorem 4.2). -/
def FixedCertifiesConf {d t k : ℕ} {Ω : Type} [Fintype Ω]
    (S : FixedTCopyScheme d t k Ω) (σ : QState d) (ε δ : ℝ) : Prop :=
  (∀ ρ : QState d, qdist ρ σ ≤ ε → 1 - δ ≤ S.acceptProb ρ) ∧
  (∀ ρ : QState d, ε < qdist ρ σ → S.acceptProb ρ ≤ δ)

/-- Certification with a shared-randomness scheme (lower-bound side, Thm 1.2). -/
def SharedCertifies {d t k : ℕ} {Seed Ω : Type} [Fintype Seed] [Fintype Ω]
    (S : SharedScheme d t k Seed Ω) (σ : QState d) (ε : ℝ) : Prop :=
  (∀ ρ : QState d, qdist ρ σ ≤ ε → (99 / 100 : ℝ) ≤ S.acceptProb ρ) ∧
  (∀ ρ : QState d, ε < qdist ρ σ → S.acceptProb ρ ≤ (1 / 100 : ℝ))

/-- Certification with a private-randomness scheme (lower-bound side, Thm 1.1/1.3). -/
def PrivateCertifies {d t k : ℕ} {Seed Ω : Type} [Fintype Seed] [Fintype Ω]
    (S : PrivateScheme d t k Seed Ω) (σ : QState d) (ε : ℝ) : Prop :=
  (∀ ρ : QState d, qdist ρ σ ≤ ε → (99 / 100 : ℝ) ≤ S.acceptProb ρ) ∧
  (∀ ρ : QState d, ε < qdist ρ σ → S.acceptProb ρ ≤ (1 / 100 : ℝ))

/-- **Fixed `t`-copy certification is achievable within `m` copies** (Thm 1.1 upper). -/
def FixedCertifiable (d t : ℕ) (ε m : ℝ) : Prop :=
  ∀ σ : QState d, ∃ (k : ℕ) (Ω : Type) (_ : Fintype Ω) (S : FixedTCopyScheme d t k Ω),
    (k : ℝ) * (t : ℝ) ≤ m ∧ FixedCertifies S σ ε

/-- **Fixed `t`-copy certification of a fixed hypothesis at confidence `1-δ`**
(Thm 4.2, instance-dependent bound). -/
def FixedCertifiableConf (d t : ℕ) (σ : QState d) (ε δ m : ℝ) : Prop :=
  ∃ (k : ℕ) (Ω : Type) (_ : Fintype Ω) (S : FixedTCopyScheme d t k Ω),
    (k : ℝ) * (t : ℝ) ≤ m ∧ FixedCertifiesConf S σ ε δ

/-- **Private `t`-copy certification is achievable within `m` copies**. -/
def PrivateCertifiable (d t : ℕ) (ε m : ℝ) : Prop :=
  ∀ σ : QState d, ∃ (k : ℕ) (Seed Ω : Type) (_ : Fintype Seed) (_ : Fintype Ω)
      (S : PrivateScheme d t k Seed Ω), (k : ℝ) * (t : ℝ) ≤ m ∧ PrivateCertifies S σ ε

/-- **Copy-complexity lower bound for private `t`-copy certification**: every
private scheme certifying every `d`-dimensional state pair within `ε` needs at
least `m` copies. -/
def PrivateCertCostAtLeast (d t : ℕ) (ε m : ℝ) : Prop :=
  ∀ (k : ℕ) (Seed Ω : Type) (_ : Fintype Seed) (_ : Fintype Ω)
      (S : PrivateScheme d t k Seed Ω) (σ : QState d),
    PrivateCertifies S σ ε → m ≤ (k : ℝ) * (t : ℝ)

/-- **Copy-complexity lower bound for non-adaptive shared-randomness schemes**
(Theorem 1.2: "even ones that use shared randomness"). -/
def SharedCertCostAtLeast (d t : ℕ) (ε m : ℝ) : Prop :=
  ∀ (k : ℕ) (Seed Ω : Type) (_ : Fintype Seed) (_ : Fintype Ω)
      (S : SharedScheme d t k Seed Ω) (σ : QState d),
    SharedCertifies S σ ε → m ≤ (k : ℝ) * (t : ℝ)

/-! ## Mixedness testing and purity estimation -/

/-- Mixedness testing against `ρ_mm = I/d`: a fixed `t`-copy scheme that
accepts the maximally mixed state and rejects every state at trace distance at
least `ε` (Paper Theorem 1.3). -/
def FixedMixednessTests {d t k : ℕ} {Ω : Type} [Fintype Ω] (hd : 0 < d)
    (S : FixedTCopyScheme d t k Ω) (ε : ℝ) : Prop :=
  (99 / 100 : ℝ) ≤ S.acceptProb (maximallyMixed d hd) ∧
  (∀ ρ : QState d, ε ≤ qdist ρ (maximallyMixed d hd) → S.acceptProb ρ ≤ (1 / 100 : ℝ))

/-- Mixedness testing is achievable within `m` copies with fixed `t`-copy
measurements. -/
def MixednessTestable (d t : ℕ) (hd : 0 < d) (ε m : ℝ) : Prop :=
  ∃ (k : ℕ) (Ω : Type) (_ : Fintype Ω) (S : FixedTCopyScheme d t k Ω),
    (k : ℝ) * (t : ℝ) ≤ m ∧ FixedMixednessTests hd S ε

/-- Private-randomness mixedness testing is achievable within `m` copies. -/
def PrivateMixednessTestable (d t : ℕ) (hd : 0 < d) (ε m : ℝ) : Prop :=
  ∃ (k : ℕ) (Seed Ω : Type) (_ : Fintype Seed) (_ : Fintype Ω)
      (S : PrivateScheme d t k Seed Ω),
    (k : ℝ) * (t : ℝ) ≤ m ∧
      (99 / 100 : ℝ) ≤ S.acceptProb (maximallyMixed d hd) ∧
      (∀ ρ : QState d, ε ≤ qdist ρ (maximallyMixed d hd) → S.acceptProb ρ ≤ (1 / 100 : ℝ))

/-- Copy-complexity lower bound for private-randomness mixedness testing. -/
def PrivateMixednessCostAtLeast (d t : ℕ) (hd : 0 < d) (ε m : ℝ) : Prop :=
  ∀ (k : ℕ) (Seed Ω : Type) (_ : Fintype Seed) (_ : Fintype Ω)
      (S : PrivateScheme d t k Seed Ω),
    ((99 / 100 : ℝ) ≤ S.acceptProb (maximallyMixed d hd) ∧
      (∀ ρ : QState d, ε ≤ qdist ρ (maximallyMixed d hd) → S.acceptProb ρ ≤ (1 / 100 : ℝ)))
    → m ≤ (k : ℝ) * (t : ℝ)

/-- A purity estimator using `k` fixed `t`-copy measurements with a numerical
estimate read off the outcomes. -/
structure PurityEstimator (d t k : ℕ) (Ω : Type) [Fintype Ω] where
  povm : POVM Ω (Fin t → Fin d)
  estimate : (Fin k → Ω) → ℝ

namespace PurityEstimator

/-- Probability that the estimate is within multiplicative error `ε` of
`tr ρ²`. -/
def successProb {d t k : ℕ} {Ω : Type} [Fintype Ω]
    (E : PurityEstimator d t k Ω) (ρ : QState d) (ε : ℝ) : ℝ :=
  ∑ x : Fin k → Ω,
    if |E.estimate x - purityReal ρ| ≤ ε * purityReal ρ then
      ∏ r, roundProb E.povm ρ (x r) else 0

end PurityEstimator

/-- **Multiplicative-error purity estimation is achievable within `m` copies**
(Theorem 1.4). -/
def PurityEstimable (d t : ℕ) (ε m : ℝ) : Prop :=
  ∃ (k : ℕ) (Ω : Type) (_ : Fintype Ω) (E : PurityEstimator d t k Ω),
    (k : ℝ) * (t : ℝ) ≤ m ∧ ∀ ρ : QState d, (99 / 100 : ℝ) ≤ E.successProb ρ ε

/-! ## Hilbert--Schmidt testing (Theorem 4.3, 4.6, Appendix A) -/

/-- A two-sample Hilbert--Schmidt test: `n` blocks of `t` copies are measured
on `ρ` and on `σ`, and a decision is applied to both outcome vectors. -/
structure HSTestScheme (d t n : ℕ) (Ω : Type) [Fintype Ω] where
  povmRho : POVM Ω (Fin t → Fin d)
  povmSigma : POVM Ω (Fin t → Fin d)
  accept : (Fin n → Ω) → (Fin n → Ω) → Bool

namespace HSTestScheme

/-- Acceptance probability of a Hilbert--Schmidt test on the pair `(ρ, σ)`. -/
def acceptProb {d t n : ℕ} {Ω : Type} [Fintype Ω]
    (S : HSTestScheme d t n Ω) (ρ σ : QState d) : ℝ :=
  ∑ x : Fin n → Ω, ∑ y : Fin n → Ω,
    if S.accept x y then
      (∏ r, roundProb S.povmRho ρ (x r)) * (∏ r, roundProb S.povmSigma σ (y r)) else 0

end HSTestScheme

/-- **Hilbert--Schmidt testing is achievable within `m` copies of each state**
(Theorem 4.3/4.6). -/
def HSTestable (d t : ℕ) (ε m : ℝ) : Prop :=
  ∃ (n : ℕ) (Ω : Type) (_ : Fintype Ω) (S : HSTestScheme d t n Ω),
    (n : ℝ) * (t : ℝ) ≤ m ∧
      (∀ ρ σ : QState d, qdist ρ σ = 0 → (99 / 100 : ℝ) ≤ S.acceptProb ρ σ) ∧
      (∀ ρ σ : QState d, ε ≤ hsDist ρ σ → S.acceptProb ρ σ ≤ (1 / 100 : ℝ))

/-- Gap version of Prop. A.1: distinguish `‖ρ-σ‖₂ ≤ ε/√2` from `‖ρ-σ‖₂ ≥ ε`
with high probability. -/
def HSGapTestable (d t : ℕ) (ε m : ℝ) : Prop :=
  ∃ (n : ℕ) (Ω : Type) (_ : Fintype Ω) (S : HSTestScheme d t n Ω),
    (n : ℝ) * (t : ℝ) ≤ m ∧
      (∀ ρ σ : QState d, hsDist ρ σ ≤ ε / Real.sqrt 2 → (99 / 100 : ℝ) ≤ S.acceptProb ρ σ) ∧
      (∀ ρ σ : QState d, ε ≤ hsDist ρ σ → S.acceptProb ρ σ ≤ (1 / 100 : ℝ))

/-- Pointwise (instance-dependent) Hilbert--Schmidt testing at confidence `1-δ`
for a fixed pair `(ρ, σ)` (Theorem 4.3). -/
def HSPairTestable (d t : ℕ) (ρ σ : QState d) (ε δ m : ℝ) : Prop :=
  ∃ (n : ℕ) (Ω : Type) (_ : Fintype Ω) (S : HSTestScheme d t n Ω),
    (n : ℝ) * (t : ℝ) ≤ m ∧
      (1 - δ ≤ S.acceptProb ρ σ) ∧
      (∀ ρ' σ' : QState d, ε ≤ hsDist ρ' σ' → S.acceptProb ρ' σ' ≤ δ)

/-! ## The σ* truncation of Theorem 4.2 -/

/-- The spectral truncation of `σ` at threshold `θ`: keep the eigenvalues
`≥ θ`, delete the rest (Paper Theorem 4.2: `σ*` is obtained by removing
smallest eigenvalues). -/
def spectralTrunc {d : ℕ} (σ : QState d) (θ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  let U : Matrix (Fin d) (Fin d) ℂ :=
    ((σ.Hermitian.eigenvectorUnitary) : Matrix.unitaryGroup (Fin d) ℂ)
  U * diagonal (fun i => if θ ≤ σ.Hermitian.eigenvalues i
      then ((σ.Hermitian.eigenvalues i : ℂ)) else 0) * star U

/-- `σ*` is the operator obtained from `σ` by deleting as many of its smallest
eigenvalues as possible while removing at most `ε²/20` mass (Theorem 4.2).
The threshold formulation records the maximality of the removal. -/
structure IsTinyEigenvalueTruncation {d : ℕ} (σ : QState d) (ε : ℝ)
    (σstar : Matrix (Fin d) (Fin d) ℂ) : Prop where
  hermitian : σstar.IsHermitian
  psd : σstar.PosSemidef
  le_sigma : (σ.m - σstar).PosSemidef
  spectral : ∃ θ : ℝ, σstar = spectralTrunc σ θ ∧
    (∀ θ' : ℝ, θ < θ' → ε ^ 2 / 20 < (σ.m - spectralTrunc σ θ').trace.re)

/-- Rank of an Hermitian matrix as a real number (`rank σ*` in Theorem 4.2). -/
def rankReal {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, if hA.eigenvalues i = 0 then 0 else 1

/-- `‖A‖_{1/2} = (tr √A)² = (∑ √λ_i)²` for an Hermitian matrix, the
quasi-norm of Theorem 4.2. -/
def schattenHalf {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) : ℝ :=
  (∑ i, Real.sqrt (hA.eigenvalues i)) ^ 2

/-- `‖A‖_{1/3} = (∑ λ_i^{1/3})³` for a Hermitian matrix. -/
def schattenThird {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) : ℝ :=
  (∑ i, (hA.eigenvalues i) ^ (1 / 3 : ℝ)) ^ 3

/-! ## Bound functions displayed in the paper -/

/-- `max{d²/(√t ε²), d/ε²}` of Theorems 1.1 and 1.3. -/
def boundCert (d t ε : ℝ) : ℝ :=
  max (d ^ 2 / (Real.sqrt t * ε ^ 2)) (d / ε ^ 2)

/-- `max{d²/(√t ε), d/(√t ε²), d/ε, √d/ε²}` of Theorem 1.4 Eq. (1.6). -/
def boundPurity (d t ε : ℝ) : ℝ :=
  max (max (d ^ 2 / (Real.sqrt t * ε)) (d / (Real.sqrt t * ε ^ 2)))
      (max (d / ε) (Real.sqrt d / ε ^ 2))

/-- `max{d/ε², d²/(t ε⁴)}` of Corollary A.2. -/
def boundCorA2 (d t ε : ℝ) : ℝ := max (d / ε ^ 2) (d ^ 2 / (t * ε ^ 4))

/-- `max{d/ε², d²/(√t ε²)}` of the folklore batching bound. -/
def boundFolk (d t ε : ℝ) : ℝ := max (d / ε ^ 2) (d ^ 2 / (Real.sqrt t * ε ^ 2))

/-- `min{d^{3/2}/(t^{1/4} ε²), 1/(t³ ε³)}` of Theorem 6.1 Eq. (6.1). -/
def bound61 (d t ε : ℝ) : ℝ :=
  min (d ^ (3 / 2 : ℝ) / (t ^ (1 / 4 : ℝ) * ε ^ 2)) (1 / (t ^ 3 * ε ^ 3))

/-- `max{d^{3/2}/(t^{1/4} ε²), d/ε²}` of Theorem 1.2 Eq. (1.4). -/
def bound12 (d t ε : ℝ) : ℝ :=
  max (d ^ (3 / 2 : ℝ) / (t ^ (1 / 4 : ℝ) * ε ^ 2)) (d / ε ^ 2)

/-- `min{d²/(√t ε²), 1/(t² ε³)}` of Theorem 6.2 Eq. (6.2). -/
def bound62 (d t ε : ℝ) : ℝ :=
  min (d ^ 2 / (Real.sqrt t * ε ^ 2)) (1 / (t ^ 2 * ε ^ 3))

/-- A polylogarithmic factor of exponent `k`; the paper's `Õ` suppresses a
factor of this form (`logFactor x k = (log (x+2))^k`). -/
def logFactor (x : ℝ) (k : ℕ) : ℝ := (Real.log (x + 2)) ^ k

/-- `g` is a polylogarithmic factor: bounded by `c (log x)^k` for large `x`. -/
def IsPolylogFactor (g : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ x : ℝ, 2 ≤ x → g x ≤ c * (Real.log x) ^ k

end
end Qatlib.Papers.StateTesting26.MainResults.Model

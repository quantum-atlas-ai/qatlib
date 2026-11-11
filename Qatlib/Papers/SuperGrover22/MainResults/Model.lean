/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SuperGrover22.MainResults.Model — shared paper model

Formal model for "Mind the gap: Achieving a super-Grover quantum speedup by jumping
to the end" (fixed arXiv:2212.01513v2, 21 Feb 2026; PDF from the qatlas asset store; PDF SHA cross-checked in the
paper-layer README). All named quantities below are the paper's own:

* assignments `z ∈ {+1,-1}^n` (Eq. before Eq.(3)),
* the ramp `gη` of Eq.(4),
* the Hamiltonian `Hb = -X/n + b·gη(H/|E*|)` of Eq.(5),
* the cumulative state function `C(E)` of Eq.(21)/(107),
* the three structural conditions (Cond. 1-3) of Sec. 2.3 and App. A.1.1.

The quantum Hamiltonian of Eq.(5) is represented, as is standard for the paper layer, by
the scalar data it contributes to every statement in the paper: its ground energy `Eb`,
its first excited energy `firstExcited`, the ground energy `Ebar` of `Π̄ Hb Π̄` (Cond. 3),
its ground state vector `psiB`, the all-plus vector, and the projector `Π∗` onto the ground
space of `H/|E*|`. This keeps the statements faithful (the numbers and vectors are exactly
those of the paper) without re-deriving finite-dimensional spectral theory from scratch.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SuperGrover22.MainResults

/-- An `n`-bit assignment `z ∈ {+1,-1}^n`, represented as a Boolean vector. -/
abbrev Assign (n : ℕ) := Fin n → Bool

/-- Numeric value of a bit, `+1` or `-1` (the paper's sign encoding). -/
def bitVal (b : Bool) : ℤ := if b then 1 else -1

/-- Flip the `j`-th bit of an assignment. -/
def flipBit {n : ℕ} (z : Assign n) (j : Fin n) : Assign n := Function.update z j (!z j)

/-- Flipping bit `j` changes the value at `j` to its negation. -/
@[simp] theorem flipBit_apply_self {n : ℕ} (z : Assign n) (j : Fin n) :
    flipBit z j j = !z j := by simp [flipBit]

/-- Flipping bit `j` leaves every other bit unchanged. -/
theorem flipBit_apply_ne {n : ℕ} (z : Assign n) {j i : Fin n} (h : i ≠ j) :
    flipBit z j i = z i := by simp [flipBit, h]

/-- A classical cost function on `n` bits. -/
abbrev CostFn (n : ℕ) := Assign n → ℝ

/-- The optimal value `E* = min_z H(z)` (as an infimum over the finite range). -/
noncomputable def optimalValue {n : ℕ} (H : CostFn n) : ℝ := sInf (Set.range H)

/-- Eq.(4): the piecewise-linear ramp `gη(x) = clip_{[-1,0]}((x+1-η)/η)`. -/
noncomputable def gEta (η x : ℝ) : ℝ := max (-1) (min 0 ((x + 1 - η) / η))

/-- Eq.(15): `F(x) = 1 - x + x ln x`. -/
noncomputable def F (x : ℝ) : ℝ := 1 - x + x * Real.log x

/-- Eq.(21)/(107): the cumulative number of assignments with cost at most `E`. -/
noncomputable def cumulative {n : ℕ} (H : CostFn n) (E : ℝ) : ℝ :=
  ((Finset.univ.filter (fun z : Assign n => H z ≤ E)).card : ℝ)

/-- Def.1 / Eq.(7): `H` is `α`-depolarizing, i.e. `∑_{y∼x} H(y) = n·(1-α)·H(x)`. -/
def Depolarizing {n : ℕ} (H : CostFn n) (α : ℝ) : Prop :=
  ∀ z : Assign n, (∑ j : Fin n, H (flipBit z j)) = (n : ℝ) * (1 - α) * H z

/-- A degree-`k` monomial term `c·∏_{i∈S} z_i` with `|S| = k`. -/
def IsMonomial {n : ℕ} (f : CostFn n) (k : ℕ) : Prop :=
  ∃ (S : Finset (Fin n)) (c : ℝ), S.card = k ∧
    ∀ z : Assign n, f z = c * ∏ i ∈ S, (bitVal (z i) : ℝ)

/-- A MAX-Ek-LIN2 instance: a finite list of degree-`k` monomial terms. -/
def IsMaxEkLin2 {n : ℕ} (H : CostFn n) (k : ℕ) : Prop :=
  ∃ (terms : List (Finset (Fin n) × ℝ)),
    (∀ t ∈ terms, t.1.card = k) ∧
    (∀ z : Assign n, H z = (terms.map (fun t => t.2 * ∏ i ∈ t.1, (bitVal (z i) : ℝ))).sum)

/-- A `k`-local constraint term: depends on at most `k` bits. -/
def IsLocalTerm {n : ℕ} (f : CostFn n) (k : ℕ) : Prop :=
  ∃ (S : Finset (Fin n)), S.card ≤ k ∧
    (∀ z w : Assign n, (∀ i ∈ S, z i = w i) → f z = f w)

/-- A MAX-k-CSP instance with `m` local terms. -/
def IsMaxKCSP {n : ℕ} (H : CostFn n) (k m : ℕ) : Prop :=
  ∃ (terms : List (CostFn n)), terms.length = m ∧
    (∀ f ∈ terms, IsLocalTerm f k) ∧
    (∀ z : Assign n, H z = (terms.map (fun f => f z)).sum)

/-- Def.2 / Eq.(8): `(H,g)` is `α`-subdepolarizing.  Writing `f(x) = -g(-x)`, the paper's
expectation inequality is stated multiplied through by `n` (the uniform distribution over the
`n` single-bit flips): `n·∏_t f(c_t(1-α)H(x)/E*) ≤ ∑_j ∏_t f(c_t H(flip_j x)/E*)`. -/
def Subdepolarizing {n : ℕ} (H : CostFn n) (Eopt : ℝ) (g : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ (T : ℕ) (c : Fin T → ℝ), (∀ t, 0 < c t) → (∀ t, c t < 1) → ∀ x : Assign n,
    (n : ℝ) * (∏ t, (- g (- (c t * (1 - α) * H x / Eopt))))
      ≤ ∑ j : Fin n, ∏ t, (- g (- (c t * H (flipBit x j) / Eopt)))

/-! ## Spectral / state data for the Hamiltonian `Hb` of Eq.(5) -/

/-- Hilbert-space dimension `2^n`. -/
abbrev HilbertDim (n : ℕ) := Fin (2 ^ n)

/-- A real-amplitude state vector on `n` qubits (the ground state of the stoquastic `Hb`
has non-negative real entries in the computational basis, Sec. 2.2). -/
abbrev State (n : ℕ) := HilbertDim n → ℝ

/-- Euclidean inner product. -/
noncomputable def ip {n : ℕ} (u v : State n) : ℝ := ∑ i, u i * v i

/-- Euclidean norm. -/
noncomputable def enorm {n : ℕ} (u : State n) : ℝ := Real.sqrt (ip u u)

/-- Scalar and vector data of the Eq.(5) Hamiltonian `Hb` that appear in the paper's
statements: ground state `psiB`, all-plus state, ground-space projector `Π∗` of `H/|E*|`,
ground energy `Eb`, first excited energy, and ground energy `Ebar` of `Π̄ Hb Π̄`. -/
structure SpectralModel (n : ℕ) where
  psiB : State n
  plusVec : State n
  projStar : State n → State n
  basis : Assign n → State n
  /-- Action of the approximate ground-state projector `P_ℓ = (Hb/Eb)^ℓ` of Eq.(11). -/
  Pt : ℕ → State n → State n
  Eb : ℝ
  firstExcited : ℝ
  Ebar : ℝ

/-- Cond.1 (large-excited-energy): the ground state is non-degenerate (carried by the model)
and all excited energies exceed `-1 + 1/n`; it suffices to record the first excited energy. -/
def LargeExcitedEnergy {n : ℕ} (M : SpectralModel n) : Prop :=
  M.firstExcited > -1 + 1 / (n : ℝ)

/-- Cond.2 (small-ground-energy-shift): `-1 - 1/n^3 ≤ Eb ≤ -1`. -/
def SmallGroundEnergyShift {n : ℕ} (M : SpectralModel n) : Prop :=
  -1 - 1 / (n : ℝ) ^ 3 ≤ M.Eb ∧ M.Eb ≤ -1

/-- Cond.3 (short-path): `Ebar ≥ -1 + 1/n`, where `Ebar` is the ground energy of `Π̄ Hb Π̄`. -/
def ShortPath {n : ℕ} (M : SpectralModel n) : Prop :=
  M.Ebar ≥ -1 + 1 / (n : ℝ)

/-- The overlap `‖Π∗|ψb⟩‖`. -/
noncomputable def normProjStar {n : ℕ} (M : SpectralModel n) : ℝ :=
  enorm (M.projStar M.psiB)

/-- `⟨+++|ψb⟩`. -/
noncomputable def overlapPlusPsi {n : ℕ} (M : SpectralModel n) : ℝ :=
  ip M.plusVec M.psiB

/-- `⟨ψb|z⟩` for a computational-basis assignment `z`. -/
noncomputable def overlapPsiBasis {n : ℕ} (M : SpectralModel n) (z : Assign n) : ℝ :=
  ip M.psiB (M.basis z)

/-- `⟨+++|P_ℓ|z⟩` for `P_ℓ = (Hb/Eb)^ℓ` (Eq.(11)). -/
noncomputable def overlapPlusPt {n : ℕ} (M : SpectralModel n) (ℓ : ℕ) (z : Assign n) : ℝ :=
  ip M.plusVec (M.Pt ℓ (M.basis z))

/-- Run characteristics of a quantum algorithm: gate count and success probability. -/
structure AlgRun where
  gates : ℝ
  success : ℝ

end Qatlib.Papers.SuperGrover22.MainResults

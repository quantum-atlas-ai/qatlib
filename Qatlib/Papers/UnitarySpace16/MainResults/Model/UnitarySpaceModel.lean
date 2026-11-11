/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Model vocabulary for "A Complete Characterization of Unitary Quantum Space"

Source: Bill Fefferman and Cedric Yen-Yu Lin, *A Complete Characterization of Unitary
Quantum Space*, arXiv:1604.01384v2 (21 Nov 2016).

This file fixes the paper-level vocabulary shared by every theorem statement of the
`UnitarySpace16.MainResults` block.  It is a *model interface*: the definitions below
transcribe the paper's definitions (Definition 4, 5, 7, 8, 9, 10, 13, 17, 24) into Lean
in a way that is faithful at the level of types and hypotheses.  Where a genuine
circuit-level implementation would require a formalised Turing machine with space
accounting, the corresponding uniformity/computation predicates are explicit `Prop`
fields of the model structures rather than hidden assumptions; the deep complexity
theorems are stated over these predicates and are proved (or flagged `sorry` with a
gap note) in the `Source/` files.

## Contents

* §1 promise problems, classes, classical reductions, completeness;
* §2 unitary quantum space machines (Definition 4) and `BQU SPACE` (Definition 5);
* §3 QMA verifier machines with a witness register (Definition 7) and the
  `(t,k)`-bounded classes, `QMA`, `PreciseQMA`, `QMA(c,s)` (Definitions 8, 9);
* §4 the polynomial-space class `PSPACE` (Watrous model);
* §5 efficient matrix encodings (Definition 10) and the concrete promise problems
  `k(n)`-Well-conditioned Matrix Inversion (Definition 13),
  `k(n)`-Minimum Eigenvalue (Definition 17) and Precise `k`-Local Hamiltonian
  (Definition 24), plus the space/time variants of Section 5.

All numerical conventions (eigenvalues of Hermitian matrices, condition numbers,
`‖H‖max ≤ const`) are expressed through Mathlib's spectral data.
-/

set_option autoImplicit false

namespace Qatlib.Papers.UnitarySpace16.MainResults.Model

open Matrix
open scoped ComplexConjugate

/-! ## §1 Promise problems, classes and reductions -/

/-- Inputs are bit strings; the input size is the string length. -/
abbrev BitString : Type := List Bool

/-- A promise problem `L = (L_yes, L_no)` (paper §2.2): the two sets of inputs are
disjoint, and inputs outside their union violate the promise. -/
structure PromiseProblem where
  yes : Set BitString
  no : Set BitString
  disjoint : ∀ x, x ∈ yes → x ∈ no → False

/-- A complexity class is a set of promise problems. -/
abbrev Class : Type := Set PromiseProblem

/-- A classical reduction, together with its time and space profiles (both functions of the
input length).  Validity on the promise sets is recorded separately in `Reduction.IsValid`. -/
structure Reduction where
  map : BitString → BitString
  time : ℕ → ℕ
  space : ℕ → ℕ

/-- `r` maps the yes-instances of `L` to yes-instances of `M` and the no-instances to
no-instances. -/
def Reduction.IsValid (r : Reduction) (L M : PromiseProblem) : Prop :=
  (∀ x, x ∈ L.yes → r.map x ∈ M.yes) ∧ (∀ x, x ∈ L.no → r.map x ∈ M.no)

/-- `L` reduces to `M` via a reduction satisfying the resource predicate `R`. -/
def ReducesTo (R : Reduction → Prop) (L M : PromiseProblem) : Prop :=
  ∃ r : Reduction, R r ∧ r.IsValid L M

/-- `L` is `R`-hard for the class `C`. -/
def HardFor (R : Reduction → Prop) (L : PromiseProblem) (C : Class) : Prop :=
  ∀ M, M ∈ C → ReducesTo R M L

/-- `L` is complete for `C` under `R`-reductions. -/
def CompleteFor (R : Reduction → Prop) (L : PromiseProblem) (C : Class) : Prop :=
  L ∈ C ∧ HardFor R L C

/-- `C` is closed under `R`-reductions. -/
def ClosedUnder (R : Reduction → Prop) (C : Class) : Prop :=
  ∀ L M, ReducesTo R L M → M ∈ C → L ∈ C

/-- Polynomial bound `f(n) ≤ n^c + c` on a length function. -/
def PolyBound (f : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, f n ≤ n ^ c + c

/-- Polynomial bound relative to a parameter function `T`. -/
def PolyBoundIn (T f : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, f n ≤ T n ^ c + c

/-- Reductions computable in polynomial time (the paper's "classical reductions"). -/
def PolyTimeReduction (r : Reduction) : Prop := PolyBound r.time

/-- Reductions computable in polynomial time and space `O(k(n))` (Theorems 14, 18, 19,
22, 26, 27, 30). -/
def PolyTimeSpaceReduction (k : ℕ → ℕ) (r : Reduction) : Prop :=
  PolyBound r.time ∧ ∀ n, r.space n ≤ k n

/-- Log-space reductions (Corollaries 1 and 2, `L`-reductions). -/
def LogSpaceReduction (r : Reduction) : Prop :=
  PolyBound r.time ∧ ∀ n, r.space n ≤ Nat.log2 (n + 2)

/-- The class of log-space reductions, used by Corollary 1 and 2. -/
def LReduction : Reduction → Prop := LogSpaceReduction

/-- Space bound `Ω(log n) ≤ k(n) ≤ poly(n)` assumed throughout the paper. -/
def AdmissibleSpace (k : ℕ → ℕ) : Prop :=
  (∀ n, Nat.log2 (n + 2) ≤ k n + k n) ∧ PolyBound k

/-- `b - a ≥ 2^{-O(k)}`: the promise gap used in Theorem 19 and Lemma 20. -/
def ExpGapAtMost (k : ℕ → ℕ) (a b : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, ∀ n, (2 : ℝ) ^ (-((c * k n + c : ℕ) : ℝ)) ≤ b n - a n

/-- `b - a ≥ 1/poly(T)`, the promise gap of Theorem 27. -/
def InvPolyGap (T : ℕ → ℕ) (a b : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, ∀ n, (1 : ℝ) / (T n ^ c + c : ℝ) ≤ b n - a n

/-! ### Elementary class-algebra lemmas -/

/-- Completeness transfers across an equality of classes. -/
theorem CompleteFor.congr {R : Reduction → Prop} {L : PromiseProblem} {C D : Class}
    (h : C = D) : CompleteFor R L C ↔ CompleteFor R L D := by
  rw [h]

/-- If `L` is complete for `C` and `C = D`, then `L` is complete for `D`. -/
theorem CompleteFor.of_eq {R : Reduction → Prop} {L : PromiseProblem} {C D : Class}
    (h : CompleteFor R L C) (hCD : C = D) : CompleteFor R L D :=
  (CompleteFor.congr hCD).mp h

/-- A hard problem for `C` stays hard for any subclass. -/
theorem HardFor.mono {R : Reduction → Prop} {L : PromiseProblem} {C D : Class}
    (h : HardFor R L C) (hDC : D ⊆ C) : HardFor R L D :=
  fun M hM => h M (hDC hM)

/-- `Set.ext`-style characterization of class inclusion. -/
theorem class_subset_iff {C D : Class} : C ⊆ D ↔ ∀ L, L ∈ C → L ∈ D := Iff.rfl

/-! ## §2 Unitary quantum space (Definitions 4 and 5) -/

/-- The `m`-qubit computational-basis register. -/
abbrev Register (m : ℕ) : Type := Fin (2 ^ m)

/-- The distinguished output qubit is the least significant bit. -/
def outBit {m : ℕ} (z : Register m) : Bool := decide (z.val % 2 = 1)

/-- Acceptance probability of a unitary `U` on the all-zero input state, measuring the
output qubit: `⟨0|U† (|1⟩⟨1|_out ⊗ I) U|0⟩` (equation (1) of Definition 4). -/
noncomputable def acceptProb {m : ℕ} (U : Matrix (Register m) (Register m) ℂ) : ℝ :=
  ∑ z : Register m, if outBit z then ‖U z 0‖ ^ 2 else 0

/-- A family of quantum circuits with classical control: for every input length `n` and
input `x` a unitary on `k n` qubits, plus a gate count and the uniformity predicate
("poly(n)-time `O(k)`-space uniformly generated", Definition 4). -/
structure UnitarySpaceMachine (k : ℕ → ℕ) where
  circuit : (n : ℕ) → BitString → Matrix (Register (k n)) (Register (k n)) ℂ
  gates : ℕ → ℕ
  uniform : Prop
  unitary : ∀ n x, (circuit n x)ᴴ * circuit n x = 1

/-- `L ∈ QU SPACE[k](c,s)` with an explicit gate bound `T` (Definition 4, equations (9) and
(10)): yes-inputs are accepted with probability at least `c`, no-inputs with probability at
most `s`, and the circuit uses at most `T n` gates on `k n` qubits. -/
noncomputable def InQUSpaceGates (T k : ℕ → ℕ) (c : ℕ → ℝ) (s : ℕ → ℝ)
    (L : PromiseProblem) : Prop :=
  ∃ M : UnitarySpaceMachine k,
    (∀ n, M.gates n ≤ T n) ∧
    (∀ x, x ∈ L.yes → c x.length ≤ acceptProb (M.circuit x.length x)) ∧
    (∀ x, x ∈ L.no → acceptProb (M.circuit x.length x) ≤ s x.length)

/-- `QU SPACE[k](c,s)`: Definition 4 with the paper's gate bound `T = 2^{O(k)}` (taken as
`2^k` by rescaling the constant). -/
noncomputable def InQUSpace (k : ℕ → ℕ) (c : ℕ → ℝ) (s : ℕ → ℝ) (L : PromiseProblem) : Prop :=
  InQUSpaceGates (fun n => 2 ^ k n) k c s L

/-- `QU SPACE[k](c,s)` as a class. -/
noncomputable def QUSpace (k : ℕ → ℕ) (c : ℕ → ℝ) (s : ℕ → ℝ) : Class :=
  { L | InQUSpace k c s L }

/-- Definition 5: `BQU SPACE[k] = QU SPACE[k](2/3, 1/3)`. -/
noncomputable def BQUSpace (k : ℕ → ℕ) : Class := QUSpace k (fun _ => 2 / 3) (fun _ => 1 / 3)

/-- `BQU L`, the unitary quantum logspace class: `BQU SPACE[O(log n)]`. -/
noncomputable def BQUL : Class := BQUSpace (fun n => Nat.log2 (n + 2))

/-- `BQU PSPACE = ⋃_{k poly} BQU SPACE[k]`, the polynomial-space case of Definition 5. -/
noncomputable def BQUPSPACE : Class :=
  { L | ∃ k : ℕ → ℕ, PolyBound k ∧ L ∈ BQUSpace k }

/-! ## §3 Quantum Merlin-Arthur verifiers (Definitions 7, 8, 9) -/

/-- An `m`-qubit witness state. -/
abbrev WitnessState (m : ℕ) : Type := Register m → ℂ

/-- A normalised witness: `∑_w ‖ψ w‖² = 1`. -/
def Normalized {m : ℕ} (ψ : WitnessState m) : Prop := ∑ w : Register m, ‖ψ w‖ ^ 2 = 1

/-- Acceptance probability of a verifier `V` on witness `ψ`, the input register being
`|0^k⟩` (equation (3) of Definition 7): `⟨ψ| ⊗ ⟨0^k| V† (|1⟩⟨1|_out ⊗ I) V |ψ⟩ ⊗ |0^k⟩`.
The register is modelled as the product `Register k × Register m`. -/
noncomputable def witnessAccept {k m : ℕ}
    (V : Matrix (Register k × Register m) (Register k × Register m) ℂ)
    (ψ : WitnessState m) : ℝ :=
  ∑ z : Register k × Register m,
    if outBit (m := k) z.1 then
      ‖∑ w : Register m, V z ((0 : Register k), w) * ψ w‖ ^ 2
    else 0

/-- A `(t,k)`-bounded `QMA_m` verifier (Definition 7): for each input a unitary on
`k n + m n` qubits with at most `t n` gates, uniformly generated, no intermediate
measurements. -/
structure QMAMachine (t k m : ℕ → ℕ) where
  circuit : (n : ℕ) → BitString →
    Matrix (Register (k n) × Register (m n)) (Register (k n) × Register (m n)) ℂ
  gates : ℕ → ℕ
  gates_le : ∀ n, gates n ≤ t n
  uniform : Prop
  unitary : ∀ n x, (circuit n x)ᴴ * circuit n x = 1

/-- `L ∈ (t,k)-bounded QMA_m(c,s)` (Definition 7): a yes-instance admits some normalised
`m`-qubit witness accepted with probability at least `c`, while every witness of a
no-instance is accepted with probability at most `s`. -/
noncomputable def InQMAbounded (t k m : ℕ → ℕ) (c : ℕ → ℝ) (s : ℕ → ℝ)
    (L : PromiseProblem) : Prop :=
  ∃ V : QMAMachine t k m,
    (∀ x, x ∈ L.yes → ∃ ψ : WitnessState (m x.length),
        Normalized ψ ∧ c x.length ≤ witnessAccept (V.circuit x.length x) ψ) ∧
    (∀ x, x ∈ L.no → ∀ ψ : WitnessState (m x.length),
        Normalized ψ → witnessAccept (V.circuit x.length x) ψ ≤ s x.length)

/-- `(t,k)`-bounded `QMA_m(c,s)` as a class. -/
noncomputable def QMAbounded (t k m : ℕ → ℕ) (c : ℕ → ℝ) (s : ℕ → ℝ) : Class :=
  { L | InQMAbounded t k m c s L }

/-- `QMA(c,s) = (poly, poly)-bounded QMA_poly(c,s)` (Proposition 23). -/
noncomputable def QMAWithGap (c : ℕ → ℝ) (s : ℕ → ℝ) : Class :=
  { L | ∃ t k m : ℕ → ℕ, PolyBound t ∧ PolyBound k ∧ PolyBound m ∧
        InQMAbounded t k m c s L }

/-- Definition 8: `QMA = (poly,poly)-bounded QMA_poly(2/3, 1/3)`. -/
noncomputable def QMA : Class := QMAWithGap (fun _ => 2 / 3) (fun _ => 1 / 3)

/-- Definition 9: `PreciseQMA = ⋃_{c ∈ (0,1]} (poly,poly)-bounded QMA_poly(c, c - 2^{-poly})`. -/
noncomputable def PreciseQMA : Class :=
  { L | ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ p : ℕ → ℕ, PolyBound p ∧
        L ∈ QMAWithGap (fun _ => c) (fun n => c - (2 : ℝ) ^ (-((p n : ℝ)))) }

/-- The right-hand side of Theorem 19: `(poly, O(k))`-bounded `QMA_{O(k)}(c,s)` with a
`2^{-O(k)}` gap.  The witness register is bounded by the space bound `k`. -/
noncomputable def SpaceBoundedPreciseQMA (k : ℕ → ℕ) : Class :=
  { L | ∃ c : ℝ, ∃ s : ℕ → ℝ, ∃ gap : ℕ → ℕ,
        PolyBound gap ∧ (∀ n, (2 : ℝ) ^ (-((gap n : ℝ))) ≤ c - s n) ∧
        ∃ t m : ℕ → ℕ, PolyBound t ∧ (∀ n, m n ≤ k n) ∧
          InQMAbounded t k m (fun _ => c) s L }

/-- The class of Theorem 27: `(poly(T), O(k))`-bounded `QMA_{O(k)}(2/3, 1/3)`. -/
noncomputable def SpaceTimeQMAClass (T k : ℕ → ℕ) : Class :=
  { L | ∃ t m : ℕ → ℕ, PolyBoundIn T t ∧ (∀ n, m n ≤ k n) ∧
        InQMAbounded t k m (fun _ => 2 / 3) (fun _ => 1 / 3) L }

/-- The left-hand side of Theorem 27: `(poly(n), O(k))`-bounded `QMA_{O(k)}(c,s)` with a
`1/poly(T)` gap. -/
noncomputable def SpaceTimeQMAUnion (T k : ℕ → ℕ) : Class :=
  { L | ∃ c : ℝ, ∃ s : ℕ → ℝ, ∃ g : ℕ → ℕ,
        PolyBound g ∧ (∀ n, (1 : ℝ) / (g n : ℝ) ≤ c - s n) ∧
        ∃ t m : ℕ → ℕ, PolyBound t ∧ (∀ n, m n ≤ k n) ∧
          InQMAbounded t k m (fun _ => c) s L }

/-- The class of problems solvable by a unitary quantum algorithm with `poly(T)` gates and
`O(k)` space (Theorem 26). -/
noncomputable def SpaceTimeClass (T k : ℕ → ℕ) : Class :=
  { L | ∃ c : ℕ, InQUSpaceGates (fun n => T n ^ c + c) k (fun _ => 2 / 3) (fun _ => 1 / 3) L }

/-! ## §4 Polynomial space (Watrous model) -/

/-- A deterministic polynomial-space machine, abstracted to its halting configuration,
acceptance predicate and space usage (the paper only uses `PSPACE` through Theorems 6
and 19, so the model fixes exactly the interface needed). -/
structure PolySpaceMachine where
  Config : Type
  run : BitString → Config
  accept : Config → Bool
  spaceUsed : BitString → ℕ
  poly_space : ∃ c : ℕ, ∀ x, spaceUsed x ≤ x.length ^ c + c

/-- `L ∈ PSPACE`. -/
def InPSPACE (L : PromiseProblem) : Prop :=
  ∃ M : PolySpaceMachine,
    (∀ x, x ∈ L.yes → M.accept (M.run x) = true) ∧
    (∀ x, x ∈ L.no → M.accept (M.run x) = false)

/-- The class `PSPACE`. -/
noncomputable def PSPACE : Class := { L | InPSPACE L }

/-! ## §5 Efficient matrix encodings and the complete problems -/

/-- A matrix is positive semidefinite when it is Hermitian with nonnegative eigenvalues. -/
def MatrixPSD {n : ℕ} (H : Matrix (Register n) (Register n) ℂ) : Prop :=
  ∃ h : H.IsHermitian, ∀ i, 0 ≤ h.eigenvalues i

/-- The Hermitian matrix `H` satisfies `lo · I ⪯ H ⪯ hi · I` on its spectrum. -/
def HermitianBetween {n : ℕ} (H : Matrix (Register n) (Register n) ℂ) (lo hi : ℝ) : Prop :=
  ∃ h : H.IsHermitian, (∀ i, lo ≤ h.eigenvalues i) ∧ (∀ i, h.eigenvalues i ≤ hi)

/-- The minimum eigenvalue of a Hermitian matrix. -/
noncomputable def minEigenvalue {n : ℕ} (H : Matrix (Register n) (Register n) ℂ)
    (h : H.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty h.eigenvalues

/-- The maximum eigenvalue of a Hermitian matrix. -/
noncomputable def maxEigenvalue {n : ℕ} (H : Matrix (Register n) (Register n) ℂ)
    (h : H.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty h.eigenvalues

/-- Definition 10: a size-`n` efficient encoding of a `2^{k(n)} × 2^{k(n)}` matrix.  The
decoding function is part of the data, so every bit string encodes at most one matrix
at each length; `efficient` records the poly-time `O(k)`-space computability of the
row queries. -/
structure MatrixEncoding (k : ℕ → ℕ) where
  decode : (n : ℕ) → BitString → Option (Matrix (Register (k n)) (Register (k n)) ℂ)
  efficient : BitString → Prop
  inputSize : BitString → ℕ

/-- Definition 10 with the extra queried indices `s, t ∈ {0,1}^{k(n)}` of the Matrix
Inversion problem. -/
structure MatrixQueryEncoding (k : ℕ → ℕ) where
  decode : (n : ℕ) → BitString →
    Option (Matrix (Register (k n)) (Register (k n)) ℂ × Register (k n) × Register (k n))
  efficient : BitString → Prop
  inputSize : BitString → ℕ

/-- Definition 13: `k(n)`-Well-conditioned Matrix Inversion.  The input is an efficient
encoding of a PSD `2^{k(n)} × 2^{k(n)}` matrix `H` with `κ⁻¹ I ⪯ H ⪯ I` together with
`s, t ∈ {0,1}^{k(n)}`; the promise is `|H⁻¹(s,t)| ≥ b` (yes) or `≤ a` (no), for constants
`0 ≤ a < b ≤ 1`. -/
noncomputable def WellConditionedMatrixInversion (k : ℕ → ℕ) (a b : ℝ) (hab : a < b)
    (E : MatrixQueryEncoding k) : PromiseProblem where
  yes := { x | ∃ H s t,
    E.decode x.length x = some (H, s, t) ∧ MatrixPSD H ∧
    ∃ κ : ℝ, 0 < κ ∧ HermitianBetween H κ⁻¹ 1 ∧ b ≤ ‖H⁻¹ s t‖ }
  no := { x | ∃ H s t,
    E.decode x.length x = some (H, s, t) ∧ MatrixPSD H ∧
    ∃ κ : ℝ, 0 < κ ∧ HermitianBetween H κ⁻¹ 1 ∧ ‖H⁻¹ s t‖ ≤ a }
  disjoint := by
    intro x hy hn
    obtain ⟨H, s, t, h1, _, K, hK, _, hb⟩ := hy
    obtain ⟨H', s', t', h2, _, K', hK', _, ha⟩ := hn
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    linarith

/-- Definition 17: `k(n)`-Minimum Eigenvalue.  The input is an efficient encoding of a PSD
`2^{k(n)} × 2^{k(n)}` matrix with `‖H‖max` bounded by a constant; the promise is that the
minimum eigenvalue is at most `a` (yes) or at least `b` (no), with `b - a > 2^{-O(k)}`. -/
noncomputable def MinimumEigenvalue (k : ℕ → ℕ) (a b : ℝ) (hab : a < b)
    (E : MatrixEncoding k) : PromiseProblem where
  yes := { x | ∃ H, E.decode x.length x = some H ∧ MatrixPSD H ∧
    ∃ h : H.IsHermitian, minEigenvalue H h ≤ a }
  no := { x | ∃ H, E.decode x.length x = some H ∧ MatrixPSD H ∧
    ∃ h : H.IsHermitian, b ≤ minEigenvalue H h }
  disjoint := by
    intro x hy hn
    obtain ⟨H, h1, _, hh, hle⟩ := hy
    obtain ⟨H', h2, _, hh', hge⟩ := hn
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    have hEq : hh = hh' := Subsingleton.elim _ _
    rw [hEq] at hle
    linarith

/-- Definition 13 with instance-dependent thresholds `a(n) < b(n)`; used for the
`1/poly(n)` precision promise of Corollary 1 and the parameterised promise of Theorem 27. -/
noncomputable def WellConditionedMatrixInversionGap (k : ℕ → ℕ) (a b : ℕ → ℝ)
    (hab : ∀ n, a n < b n) (E : MatrixQueryEncoding k) : PromiseProblem where
  yes := { x | ∃ H s t,
    E.decode x.length x = some (H, s, t) ∧ MatrixPSD H ∧
    ∃ κ : ℝ, 0 < κ ∧ HermitianBetween H κ⁻¹ 1 ∧ b x.length ≤ ‖H⁻¹ s t‖ }
  no := { x | ∃ H s t,
    E.decode x.length x = some (H, s, t) ∧ MatrixPSD H ∧
    ∃ κ : ℝ, 0 < κ ∧ HermitianBetween H κ⁻¹ 1 ∧ ‖H⁻¹ s t‖ ≤ a x.length }
  disjoint := by
    intro x hy hn
    obtain ⟨H, s, t, h1, _, K, hK, _, hb⟩ := hy
    obtain ⟨H', s', t', h2, _, K', hK', _, ha⟩ := hn
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    linarith [hab x.length]

/-- Definition 17 with instance-dependent thresholds `a(n) < b(n)`. -/
noncomputable def MinimumEigenvalueGap (k : ℕ → ℕ) (a b : ℕ → ℝ)
    (hab : ∀ n, a n < b n) (E : MatrixEncoding k) : PromiseProblem where
  yes := { x | ∃ H, E.decode x.length x = some H ∧ MatrixPSD H ∧
    ∃ h : H.IsHermitian, minEigenvalue H h ≤ a x.length }
  no := { x | ∃ H, E.decode x.length x = some H ∧ MatrixPSD H ∧
    ∃ h : H.IsHermitian, b x.length ≤ minEigenvalue H h }
  disjoint := by
    intro x hy hn
    obtain ⟨H, h1, _, hh, hle⟩ := hy
    obtain ⟨H', h2, _, hh', hge⟩ := hn
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    have hEq : hh = hh' := Subsingleton.elim _ _
    rw [hEq] at hle
    linarith [hab x.length]

/-- The Minimum Eigenvalue problem of Theorem 27 with gap `1/poly(T)`. -/
noncomputable def MinimumEigenvalueGapT (T k : ℕ → ℕ) (a b : ℕ → ℝ)
    (hab : ∀ n, a n < b n) (E : MatrixEncoding k) : PromiseProblem :=
  MinimumEigenvalueGap k a b hab E

/-- A concrete local-Hamiltonian instance: qubit count, Hamiltonian matrix, and the two
eigenvalue thresholds `a < b`. -/
structure HamiltonianInstance where
  n : ℕ
  H : Matrix (Register n) (Register n) ℂ
  a : ℝ
  b : ℝ

/-- An encoding of a `k`-local Hamiltonian instance together with the predicates recording
the size-`n` efficient encoding, the poly-many terms with polynomially bounded norms, and
`k`-locality. -/
structure LocalHamiltonianEncoding (k : ℕ) where
  decode : BitString → Option HamiltonianInstance
  efficient : BitString → Prop
  isLocal : BitString → Prop
  frustrationFree : BitString → Prop

/-- Definition 24: Precise `k`-Local Hamiltonian.  The promise is that the smallest
eigenvalue is either at most `a` or at least `b`, with `a < b` and (recorded in
`efficient`) `b - a > 2^{-poly(n)}`; yes means `λ_min ≤ a`, no means `λ_min ≥ b`. -/
noncomputable def PreciseLocalHamiltonian (k : ℕ) (E : LocalHamiltonianEncoding k) :
    PromiseProblem where
  yes := { x | ∃ (I : HamiltonianInstance),
    E.decode x = some I ∧ I.a < I.b ∧ MatrixPSD I.H ∧
    ∃ h : I.H.IsHermitian, minEigenvalue I.H h ≤ I.a }
  no := { x | ∃ (I : HamiltonianInstance),
    E.decode x = some I ∧ I.a < I.b ∧ MatrixPSD I.H ∧
    ∃ h : I.H.IsHermitian, I.b ≤ minEigenvalue I.H h }
  disjoint := by
    intro x hy hn
    obtain ⟨I, h1, hab, -, hh, hle⟩ := hy
    obtain ⟨I', h2, hab', -, hh', hge⟩ := hn
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    have hEq : hh = hh' := Subsingleton.elim _ _
    rw [hEq] at hle
    linarith

/-- Frustration-Free `k`-Local Hamiltonian: the restriction of the Precise `k`-Local
Hamiltonian problem to frustration-free Hamiltonians (both promise sets carry the extra
`frustrationFree` condition).  Theorem 39 proves this problem `PSPACE`-complete. -/
noncomputable def FrustrationFreeLocalHamiltonian (k : ℕ) (E : LocalHamiltonianEncoding k) :
    PromiseProblem where
  yes := { x | E.frustrationFree x ∧ ∃ (I : HamiltonianInstance),
    E.decode x = some I ∧ I.a < I.b ∧ MatrixPSD I.H ∧
    ∃ h : I.H.IsHermitian, minEigenvalue I.H h ≤ I.a }
  no := { x | E.frustrationFree x ∧ ∃ (I : HamiltonianInstance),
    E.decode x = some I ∧ I.a < I.b ∧ MatrixPSD I.H ∧
    ∃ h : I.H.IsHermitian, I.b ≤ minEigenvalue I.H h }
  disjoint := by
    intro x hy hn
    obtain ⟨-, I, h1, hab, -, hh, hle⟩ := hy
    obtain ⟨-, I', h2, hab', -, hh', hge⟩ := hn
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    have hEq : hh = hh' := Subsingleton.elim _ _
    rw [hEq] at hle
    linarith

end Qatlib.Papers.UnitarySpace16.MainResults.Model

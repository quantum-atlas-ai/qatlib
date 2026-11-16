/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.MainResults.SourceModel
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
public import Mathlib.Order.Lattice.Nat

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Complexity measures of arXiv:1511.01937

This file assembles the query-complexity measures that appear in the statements of
Aaronson–Ben-David–Kothari (ABK16), arXiv:1511.01937v2, from frozen primitives:

* `D`, `R`, `R0`, `R1` — deterministic, bounded-error randomised, zero-error and
  one-sided-error randomised decision-tree complexity, using the frozen
  `BoolQueryTree` and its `Run`, `MaxQueries`, `SuccessProb`, `BoundedQueries`.
* `Q`, `Q0`, `Q1`, `QE` — quantum query complexity with bounded error, zero error,
  one-sided error and exact (zero-error with success probability one) semantics,
  using the frozen `Circuit`, `QueryCount`, `Run`, `WorkspaceBitOracle` and
  `MeasureProb` on the `(I × Bool) × W` workspace model.
* `C`, `C0`, `C1`, `bs` — certificate complexity (all inputs, `0`-inputs, `1`-inputs)
  and block sensitivity, with certificates as subcubes through `Finset I`.
* `deg`, `degTilde` — exact and approximate polynomial degree, using the frozen
  `boolEval`, restricted to the promise `dom f`.

All measures are `ℕ`-valued infima over the respective resource sets, so the
statements below compare natural numbers (cast to `ℝ` in the asymptotic claims).
-/

set_option autoImplicit false

open scoped Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Papers.CheatSheet15.MainResults.SourceModel

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## Randomised decision trees: `R`, `R0`, `R1` -/

/-- Success probability, as a real number, of a randomised decision-tree program on
the input `x` for the answer `b`. -/
noncomputable def bitSuccessProb (prog : PMF (BoolQueryTree I Bool)) (x : I → Bool)
    (b : Bool) : ℝ :=
  (BoolQueryTree.SuccessProb prog x (fun out => out = b)).toReal

/-- Bounded-error randomised decision-tree complexity `R(f)` (ABK16 §2). -/
noncomputable def R (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ prog : PMF (BoolQueryTree I Bool),
    BoolQueryTree.BoundedQueries prog t ∧
      ∀ x (hx : x ∈ f.dom), (2 / 3 : ℝ) ≤ bitSuccessProb prog x (f.val x hx)}

/-- Zero-error randomised decision-tree complexity `R0(f)`; the program may answer
`none` but must never err. -/
noncomputable def R0 (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ prog : PMF (BoolQueryTree I (Option Bool)),
    BoolQueryTree.BoundedQueries prog t ∧
      ∀ x (hx : x ∈ f.dom),
        (1 / 2 : ℝ) ≤
          (BoolQueryTree.SuccessProb prog x (fun out => out = some (f.val x hx))).toReal}

/-- One-sided-error randomised decision-tree complexity `R1(f)`: always correct on
`0`-inputs, correct with probability at least `2/3` on `1`-inputs. -/
noncomputable def R1 (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ prog : PMF (BoolQueryTree I Bool),
    BoolQueryTree.BoundedQueries prog t ∧
      (∀ x (hx : x ∈ f.dom), f.val x hx = false →
        (BoolQueryTree.SuccessProb prog x (fun out => out = false)).toReal = 1) ∧
      (∀ x (hx : x ∈ f.dom), f.val x hx = true →
        (2 / 3 : ℝ) ≤ (BoolQueryTree.SuccessProb prog x (fun out => out = true)).toReal)}

/-- Deterministic decision-tree complexity `D(f)`. -/
noncomputable def D (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ T : BoolQueryTree I Bool,
    T.MaxQueries ≤ t ∧ ∀ x (hx : x ∈ f.dom), (T.Run x).1 = f.val x hx}

/-! ## Quantum query complexity: `Q`, `Q0`, `Q1`, `QE` -/

/-- Query register plus target qubit with trivial workspace (bounded-error `Q`). -/
abbrev QSpace (I : Type) : Type := (I × Bool) × Unit

/-- Query register plus target qubit with a one-bit "abort" workspace (`Q0`). -/
abbrev Q0Space (I : Type) : Type := (I × Bool) × Option Bool

/-- Accepting measurement fibre for the answer `b`. -/
def QAccept (b : Bool) : Finset (QSpace I) :=
  Finset.univ.filter fun p => p.1.2 = b

/-- Accepting measurement fibre for the answer `b` in the zero-error workspace model. -/
def Q0Accept (b : Bool) : Finset (Q0Space I) :=
  Finset.univ.filter fun p => p.2 = some b

omit [DecidableEq I] in
/-- The `mem_QAccept` result for the CheatSheet15 paper model. -/
theorem mem_QAccept {b : Bool} {p : QSpace I} : p ∈ QAccept b ↔ p.1.2 = b := by
  simp [QAccept]

omit [DecidableEq I] in
/-- The `mem_Q0Accept` result for the CheatSheet15 paper model. -/
theorem mem_Q0Accept {b : Bool} {p : Q0Space I} : p ∈ Q0Accept b ↔ p.2 = some b := by
  simp [Q0Accept]

/-- Bounded-error quantum query complexity `Q(f)`. -/
noncomputable def Q (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ (C : Circuit (QSpace I)) (ψ : QState (QSpace I)),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x (hx : x ∈ f.dom),
        (2 / 3 : ℝ) ≤
          MeasureProb (Run (workspaceBitOracle x) C ψ) (QAccept (f.val x hx))}

/-- Zero-error quantum query complexity `Q0(f)`: probability at least `1/2` of the
correct answer, no probability of a wrong answer (encoded by the `Option Bool`
workspace). -/
noncomputable def Q0 (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ (C : Circuit (Q0Space I)) (ψ : QState (Q0Space I)),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x (hx : x ∈ f.dom),
        (1 / 2 : ℝ) ≤
          MeasureProb (Run (workspaceBitOracle x) C ψ) (Q0Accept (f.val x hx))}

/-- One-sided-error quantum query complexity `Q1(f)`: never accepts `0`-inputs,
accepts `1`-inputs with probability at least `2/3`. -/
noncomputable def Q1 (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ (C : Circuit (QSpace I)) (ψ : QState (QSpace I)),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      (∀ x (hx : x ∈ f.dom), f.val x hx = false →
        MeasureProb (Run (workspaceBitOracle x) C ψ) (QAccept true) = 0) ∧
      (∀ x (hx : x ∈ f.dom), f.val x hx = true →
        (2 / 3 : ℝ) ≤ MeasureProb (Run (workspaceBitOracle x) C ψ) (QAccept true))}

/-- Exact quantum query complexity `QE(f)`: correct with probability one. -/
noncomputable def QE (f : PartialBitFun I) : ℕ :=
  sInf {t : ℕ | ∃ (C : Circuit (QSpace I)) (ψ : QState (QSpace I)),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x (hx : x ∈ f.dom),
        MeasureProb (Run (workspaceBitOracle x) C ψ) (QAccept (f.val x hx)) = 1}

/-! ## Certificate complexity: `C`, `C0`, `C1`, `bs` -/

/-- `S ⊆ I` is a certificate for `f` at `x ∈ dom f` when every `y ∈ dom f`
agreeing with `x` on `S` has the same value. -/
def IsCertFor (f : PartialBitFun I) (x : I → Bool) (hx : x ∈ f.dom) (S : Finset I) : Prop :=
  ∀ (y : I → Bool) (hy : y ∈ f.dom), (∀ i ∈ S, y i = x i) → f.val y hy = f.val x hx

/-- Certificate size at `x`: the minimum cardinality of a certificate; `0` outside
the promise. -/
noncomputable def certSizeAt (f : PartialBitFun I) (x : I → Bool) : ℕ :=
  if hx : x ∈ f.dom then
    sInf ((Finset.univ.filter fun S : Finset I => IsCertFor f x hx S).image Finset.card :
      Set ℕ)
  else 0

omit [DecidableEq I] in
/-- The `certSizeAt_of_mem` result for the CheatSheet15 paper model. -/
theorem certSizeAt_of_mem (f : PartialBitFun I) {x : I → Bool} (hx : x ∈ f.dom) :
    certSizeAt f x =
      sInf ((Finset.univ.filter fun S : Finset I => IsCertFor f x hx S).image Finset.card :
        Set ℕ) := by
  rw [certSizeAt, dite_eq_left hx]

omit [DecidableEq I] in
/-- The `certSizeAt_of_not_mem` result for the CheatSheet15 paper model. -/
theorem certSizeAt_of_not_mem (f : PartialBitFun I) {x : I → Bool} (hx : x ∉ f.dom) :
    certSizeAt f x = 0 := by
  rw [certSizeAt, dite_eq_right hx]

/-- Certificate complexity `C(f)`: worst-case certificate size over the promise. -/
noncomputable def C (f : PartialBitFun I) : ℕ :=
  (Finset.univ.image fun x : I → Bool => certSizeAt f x).sup id

/-- `1`-certificate complexity `C1(f)`. -/
noncomputable def C1 (f : PartialBitFun I) : ℕ :=
  ((Finset.univ.filter fun x : I → Bool => f.valueOf x = some true).image
    fun x => certSizeAt f x).sup id

/-- `0`-certificate complexity `C0(f)`. -/
noncomputable def C0 (f : PartialBitFun I) : ℕ :=
  ((Finset.univ.filter fun x : I → Bool => f.valueOf x = some false).image
    fun x => certSizeAt f x).sup id

/-- Flip every bit in the block `B`. -/
def flipBlock (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- The block `B` is sensitive at `x` when flipping it changes the (defined) value. -/
def blockSensitive (f : PartialBitFun I) (x : I → Bool) (B : Finset I) : Prop :=
  ∃ b, f.valueOf x = some b ∧ f.valueOf (flipBlock x B) = some (!b)

/-- Block sensitivity at `x`: the largest number of pairwise disjoint sensitive blocks. -/
noncomputable def bsAt (f : PartialBitFun I) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun 𝔅 : Finset (Finset I) =>
    (∀ B ∈ 𝔅, blockSensitive f x B) ∧
      (∀ B₁ ∈ 𝔅, ∀ B₂ ∈ 𝔅, B₁ ≠ B₂ → Disjoint B₁ B₂)).sup Finset.card

/-- Block sensitivity `bs(f)` (worst case over the promise). -/
noncomputable def bs (f : PartialBitFun I) : ℕ :=
  (Finset.univ.image fun x => bsAt f x).sup id

omit [Fintype I] in
/-- The `flipBlock_empty` result for the CheatSheet15 paper model. -/
theorem flipBlock_empty (x : I → Bool) : flipBlock x ∅ = x := by
  funext i
  simp [flipBlock]

omit [Fintype I] in
/-- The `not_blockSensitive_empty` result for the CheatSheet15 paper model. -/
theorem not_blockSensitive_empty (f : PartialBitFun I) (x : I → Bool) :
    ¬ blockSensitive f x ∅ := by
  rintro ⟨b, hx, hflip⟩
  rw [flipBlock_empty] at hflip
  rw [hx] at hflip
  simp at hflip

/-! ## Polynomial degree: `deg`, `deg~` -/

/-- Exact polynomial degree `deg(f)` over the reals, restricted to the promise. -/
noncomputable def deg (f : PartialBitFun I) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ x (hx : x ∈ f.dom), boolEval p x = if f.val x hx then (1 : ℝ) else 0})

/-- Approximate polynomial degree `deg~(f)` over the reals, with approximation
parameter `1/3` and restricted to the promise. -/
noncomputable def degTilde (f : PartialBitFun I) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ x (hx : x ∈ f.dom),
      |boolEval p x - (if f.val x hx then (1 : ℝ) else 0)| ≤ 1 / 3})

end Qatlib.Papers.CheatSheet15.MainResults.SourceModel

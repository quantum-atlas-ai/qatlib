/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetFramework
public import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source model for arXiv:1511.01937 ("Separations in query complexity using cheat sheets")

This file fixes the paper-layer vocabulary of Aaronson–Ben-David–Kothari (ABK16),
arXiv:1511.01937v2.  The paper works with partial Boolean functions
`f : D → {0,1}` with `D ⊆ {0,1}^n`, their totalisations, block compositions
`f ∘ OR_m`, `f ∘ AND_m ∘ OR_m`, the `k`-sum function of Theorem 25, and the
cheat-sheet construction of Definitions 14 and 15.

The cheat-sheet construction itself is **reused** from the frozen library:
`RQSeparation.BornBaseline.cheatSheetFun`
already implements ABK16 Definition 15 on `CheatSheetIndex c M κ`, and
`IsCertifying` implements the certifying-function promise of Definition 14.
Those definitions are not duplicated here; the aliases below only specialise
them to the paper's partial-function notation `D = dom f`, `g = f` on `D`.

Oracle/measure vocabulary (`BoolQueryTree`, `Circuit`, `QueryCount`,
`workspaceBitOracle`, `MeasureProb`, `exactDegree`, `approxDegree`,
`sourceFunctionQ`) is likewise taken from the frozen library; `Measures.lean`
assembles it into the paper's measures `D, R, R0, R1, Q, Q0, Q1, QE, C, C0,
C1, bs, deg, deg~`.
-/

set_option autoImplicit false

open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Papers.CheatSheet15.BornBaseline

namespace Qatlib.Papers.CheatSheet15.MainResults.SourceModel

/-! ## Partial and total Boolean functions -/

/-- A total Boolean function on the finite input set `{0,1}^I`. -/
abbrev BitFun (I : Type*) := (I → Bool) → Bool

/-- A partial Boolean function: a promise `dom` and a value on the promise. -/
structure PartialBitFun (I : Type*) where
  /-- The promise `D` of the paper. -/
  dom : Set (I → Bool)
  /-- The value `f(x)` for `x ∈ D`. -/
  val : (x : I → Bool) → x ∈ dom → Bool

namespace PartialBitFun

variable {I : Type*}

/-- A total Boolean function as a partial function with full domain (used when the
paper's construction hands a total function to a statement about partial ones). -/
def total (g : BitFun I) : PartialBitFun I := ⟨Set.univ, fun x _ => g x⟩

/-- The `total_dom` result for the CheatSheet15 paper model. -/
@[simp] theorem total_dom (g : BitFun I) : (total g).dom = Set.univ := rfl

/-- The `total_val` result for the CheatSheet15 paper model. -/
@[simp] theorem total_val (g : BitFun I) (x : I → Bool) (h : x ∈ (total g).dom) :
    (total g).val x h = g x := rfl

/-- The canonical total extension used by `cheatSheetFun`: outside the promise it
returns `false`.  Definitions 14/15 only inspect `φ` on `dom`, so the extension is
immaterial there; it is needed because `cheatSheetFun` is a total Boolean function. -/
noncomputable def totalize (f : PartialBitFun I) : BitFun I :=
  fun x => if h : x ∈ f.dom then f.val x h else false

/-- The `totalize_of_mem` result for the CheatSheet15 paper model. -/
theorem totalize_of_mem (f : PartialBitFun I) {x : I → Bool} (h : x ∈ f.dom) :
    f.totalize x = f.val x h := by
  rw [totalize, dite_eq_left h]

/-- The `totalize_of_not_mem` result for the CheatSheet15 paper model. -/
theorem totalize_of_not_mem (f : PartialBitFun I) {x : I → Bool} (h : x ∉ f.dom) :
    f.totalize x = false := by
  rw [totalize, dite_eq_right h]

/-- Value of `f` as an `Option`, `none` outside the promise.  One-sided measures
(`R0`, `Q0`, `C0`, `C1`) read the output type `Option Bool`. -/
noncomputable def valueOf (f : PartialBitFun I) (x : I → Bool) : Option Bool :=
  if h : x ∈ f.dom then some (f.val x h) else none

/-- The `valueOf_eq_some` result for the CheatSheet15 paper model. -/
theorem valueOf_eq_some {f : PartialBitFun I} {x : I → Bool} (h : x ∈ f.dom) :
    f.valueOf x = some (f.val x h) := by
  rw [valueOf, dite_eq_left h]

/-- The `valueOf_eq_none` result for the CheatSheet15 paper model. -/
theorem valueOf_eq_none {f : PartialBitFun I} {x : I → Bool} (h : x ∉ f.dom) :
    f.valueOf x = none := by
  rw [valueOf, dite_eq_right h]

/-- The `valueOf_total` result for the CheatSheet15 paper model. -/
theorem valueOf_total (g : BitFun I) (x : I → Bool) : (total g).valueOf x = some (g x) := by
  rw [valueOf_eq_some (x := x) (h := Set.mem_univ x)]
  rfl

/-- Block composition (the paper's `f ∘ h`): query a block `i` of `m` bits through
`h`, then evaluate `f`.  Here `f` lives on `{0,1}^I` and the composed function on
`{0,1}^{I × [m]}`. -/
def compose (f : PartialBitFun I) (m : ℕ) (h : BitFun (Fin m)) : PartialBitFun (I × Fin m) where
  dom := {z | (fun i : I => h (fun j : Fin m => z (i, j))) ∈ f.dom}
  val := fun z hz => f.val (fun i => h (fun j => z (i, j))) hz

/-- The `compose_dom` result for the CheatSheet15 paper model. -/
@[simp] theorem compose_dom (f : PartialBitFun I) (m : ℕ) (h : BitFun (Fin m)) :
    (f.compose m h).dom = {z | (fun i => h (fun j => z (i, j))) ∈ f.dom} := rfl

/-- The `compose_val` result for the CheatSheet15 paper model. -/
@[simp] theorem compose_val (f : PartialBitFun I) (m : ℕ) (h : BitFun (Fin m))
    (z : I × Fin m → Bool) (hz : z ∈ (f.compose m h).dom) :
    (f.compose m h).val z hz = f.val (fun i => h (fun j => z (i, j))) hz := rfl

end PartialBitFun

/-! ## `OR`, `AND`, `AND`–`OR` and `k`-sum -/

/-- `OR_m` (the paper's `Or_m`). -/
def orFun (m : ℕ) : BitFun (Fin m) := fun x => decide (∃ i : Fin m, x i = true)

/-- `AND_m` (the paper's `And_m`). -/
def andFun (m : ℕ) : BitFun (Fin m) := fun x => decide (∀ i : Fin m, x i = true)

/-- `AND_m ∘ OR_m` on `m²` bits, read through `Fin m × Fin m ≃ Fin (m * m)`. -/
def andOrFun (m : ℕ) : BitFun (Fin (m * m)) :=
  fun z => andFun m (fun i => orFun m (fun j => z (finProdFinEquiv (i, j))))

/-- The `k`-sum function of Theorem 25: on an input `x ∈ [q+1]^n`, accept iff some
`k` of the entries sum to `0` modulo `q + 1`.  The paper's alphabet `[q]` is
represented as `Fin (q+1)` so that it has `q+1` elements; the modulus is the
alphabet size `q + 1`. -/
def kSumFun (n q k : ℕ) : (Fin n → Fin (q + 1)) → Bool :=
  fun x => decide (∃ S : Finset (Fin n), S.card = k ∧ (∑ i ∈ S, (x i).val) % (q + 1) = 0)

/-- The `orFun_eq_true_iff` result for the CheatSheet15 paper model. -/
theorem orFun_eq_true_iff (m : ℕ) (x : Fin m → Bool) :
    orFun m x = true ↔ ∃ i, x i = true := by
  simp [orFun]

/-- The `andFun_eq_true_iff` result for the CheatSheet15 paper model. -/
theorem andFun_eq_true_iff (m : ℕ) (x : Fin m → Bool) :
    andFun m x = true ↔ ∀ i, x i = true := by
  simp [andFun]

/-- The `andOrFun_eq_true_iff` result for the CheatSheet15 paper model. -/
theorem andOrFun_eq_true_iff (m : ℕ) (z : Fin (m * m) → Bool) :
    andOrFun m z = true ↔ ∀ i : Fin m, ∃ j : Fin m, z (finProdFinEquiv (i, j)) = true := by
  simp [andOrFun, andFun_eq_true_iff, orFun_eq_true_iff]

/-! ## Cheat sheets (Definitions 14 and 15, reused from the frozen library) -/

/-- The certifying-function promise of ABK16 Definition 14 for the partial function
`f`, stated through the frozen `IsCertifying`. -/
def IsCertifyingFun (M κ : ℕ) (hκ : 0 < κ) (f : PartialBitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) : Prop :=
  IsCertifying M κ hκ f.dom f.totalize φ

/-- The cheat-sheet function `f_CS` of Definition 15, i.e. the frozen
`cheatSheetFun` applied to `f`'s totalisation and the certifying function `φ`. -/
noncomputable def cheatSheet {c M κ : ℕ} (_hκ : 0 < κ) (f : PartialBitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) : BitFun (CheatSheetIndex c M κ) :=
  cheatSheetFun (c := c) f.totalize φ

/-- The certifying function `φ` packed as a partial Boolean function on its own
input space `{0,1}^{M × κ}` (used by the measures `D(φ)`, `R(φ)`, `deg(φ)`). -/
def phiBit {M κ : ℕ} (hM : 0 < M) (hκ : 0 < κ)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) : BitFun (Fin M × Fin κ) :=
  fun w => φ (fun i => w (i, ⟨0, hκ⟩)) (fun j => w (⟨0, hM⟩, j))

/-- The set of cheat-sheet inputs whose blocks are copies of `x` and whose selected
sheet holds valid certificates: this is the paper's domain `dom(f_CS)`, recovered
from the frozen construction (Definition 15 accepts exactly when every block check
`φ` passes on the sheet indexed by the `g`-values of the blocks). -/
noncomputable def cheatSheetDomain {c M κ : ℕ} (hκ : 0 < κ) (f : PartialBitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) : Set (CheatSheetIndex c M κ → Bool) :=
  {z | cheatSheet hκ f φ z = true}

/-- `f_CS` as a partial Boolean function whose promise is the set of accepting
cheat-sheet inputs (Definition 15). -/
noncomputable def cheatSheetPartial {c M κ : ℕ} (hκ : 0 < κ) (f : PartialBitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) : PartialBitFun (CheatSheetIndex c M κ) :=
  ⟨cheatSheetDomain hκ f φ, fun _ _ => true⟩

/-! ## Alphabet quantum query complexity of `k`-sum (Theorem 25)

Frozen `sourceFunctionQ` is a general-alphabet bounded-error quantum query complexity
(`input : X → Fin n → Fin (q+1)`), i.e. the paper's `Q_α` for alphabet size `q + 1`.
It returns an `ℝ≥0∞`; statements compare `.toReal` against real lower bounds. -/

/-- The paper's `Q_α(k-sum)` for alphabet `[q]` (represented as `Fin (q+1)`),
through the frozen `sourceFunctionQ`. -/
noncomputable def alphaQuantum {n q : ℕ} (f : (Fin n → Fin (q + 1)) → Bool) : ℝ≥0∞ :=
  sourceFunctionQ (X := Fin n → Fin (q + 1)) (E := Bool)
    (fun (x : Fin n → Fin (q + 1)) (j : Fin n) => x j) f

/-- `Q_α(k-sum)` as a real number. -/
noncomputable def alphaQuantumReal {n q : ℕ} (f : (Fin n → Fin (q + 1)) → Bool) : ℝ :=
  (alphaQuantum f).toReal

/-! ## Unfolding lemmas for the frozen cheat-sheet function (Definition 15) -/

/-- The `cheatSheetFun_eq_true_iff` result for the CheatSheet15 paper model. -/
theorem cheatSheetFun_eq_true_iff {c M κ : ℕ} (g : BitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) (z : CheatSheetIndex c M κ → Bool) :
    cheatSheetFun (c := c) g φ z = true ↔
      ∀ i : Fin c, φ (cheatBlock z i) (cheatCert z (sheetIndex fun i' => g (cheatBlock z i')) i) = true := by
  simp [cheatSheetFun]

/-- Definition 15 unfolded for `f_CS`: on an accepting cheat-sheet input every block
passes its certificate check on the sheet selected by the block values of `f`. -/
theorem cheatSheet_eq_true_iff {c M κ : ℕ} (hκ : 0 < κ) (f : PartialBitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) (z : CheatSheetIndex c M κ → Bool) :
    cheatSheet hκ f φ z = true ↔
      ∀ i : Fin c,
        φ (cheatBlock z i)
          (cheatCert z (sheetIndex fun i' => f.totalize (cheatBlock z i')) i) = true := by
  rw [cheatSheet, cheatSheetFun_eq_true_iff]

/-- Definition 15 at a cheat-sheet input whose blocks are all equal to `x` and whose
selected sheet holds the certificates `y i`.  This is the form in which the paper
uses the construction in its upper bounds. -/
theorem cheatSheet_true_of_certificates {c M κ : ℕ} (hκ : 0 < κ) (f : PartialBitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) (x : Fin M → Bool) (y : Fin c → Fin κ → Bool) :
    (∀ i, φ x (y i) = true) →
      ∃ z : CheatSheetIndex c M κ → Bool, cheatSheet hκ f φ z = true := by
  intro hy
  classical
  let z : CheatSheetIndex c M κ → Bool := fun p =>
    match p with
    | Sum.inl (i, j) => x j
    | Sum.inr (ℓ, i, j) =>
        if ℓ = sheetIndex (fun i' => f.totalize x) then y i j else false
  refine ⟨z, ?_⟩
  rw [cheatSheet_eq_true_iff]
  intro i
  have hblock : ∀ i : Fin c, cheatBlock z i = x := by
    intro i
    funext j
    simp [cheatBlock, z]
  have hcert : cheatCert z (sheetIndex fun i' => f.totalize (cheatBlock z i')) i = y i := by
    funext j
    have hfun : (fun i' => f.totalize (cheatBlock z i')) = fun i' => f.totalize x := by
      funext i'
      rw [hblock i']
    rw [hfun]
    simp [cheatCert, z]
  rw [hblock i, hcert]
  exact hy i

/-! ## Projections of the certifying promise -/

/-- The `isCertifying_sound` result for the CheatSheet15 paper model. -/
theorem isCertifying_sound {M κ : ℕ} {hκ : 0 < κ} {f : PartialBitFun (Fin M)}
    {φ : (Fin M → Bool) → (Fin κ → Bool) → Bool} (h : IsCertifyingFun M κ hκ f φ)
    {x : Fin M → Bool} {y : Fin κ → Bool} (hy : φ x y = true) :
    x ∈ f.dom ∧ y ⟨0, hκ⟩ = f.totalize x :=
  h.1 x y hy

/-- The `isCertifying_sound_val` result for the CheatSheet15 paper model. -/
theorem isCertifying_sound_val {M κ : ℕ} {hκ : 0 < κ} {f : PartialBitFun (Fin M)}
    {φ : (Fin M → Bool) → (Fin κ → Bool) → Bool} (h : IsCertifyingFun M κ hκ f φ)
    {x : Fin M → Bool} {y : Fin κ → Bool} (hy : φ x y = true) :
    y ⟨0, hκ⟩ = f.val x (h.1 x y hy).1 := by
  have h1 := h.1 x y hy
  have h2 : f.totalize x = f.val x h1.1 := f.totalize_of_mem h1.1
  exact h1.2.trans h2

/-- The `isCertifying_complete` result for the CheatSheet15 paper model. -/
theorem isCertifying_complete {M κ : ℕ} {hκ : 0 < κ} {f : PartialBitFun (Fin M)}
    {φ : (Fin M → Bool) → (Fin κ → Bool) → Bool} (h : IsCertifyingFun M κ hκ f φ)
    {x : Fin M → Bool} (hx : x ∈ f.dom) : ∃ y, φ x y = true :=
  h.2.1 x hx

/-- The `isCertifying_zero` result for the CheatSheet15 paper model. -/
theorem isCertifying_zero {M κ : ℕ} {hκ : 0 < κ} {f : PartialBitFun (Fin M)}
    {φ : (Fin M → Bool) → (Fin κ → Bool) → Bool} (h : IsCertifyingFun M κ hκ f φ)
    (x : Fin M → Bool) : φ x (fun _ => false) = false :=
  h.2.2 x

end Qatlib.Papers.CheatSheet15.MainResults.SourceModel

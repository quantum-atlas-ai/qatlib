/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

set_option backward.isDefEq.respectTransparency false

/-!
# Paper vocabulary for SymQueryComm20

Source: S. Chakraborty, A. Chattopadhyay, P. Høyer, N. S. Mande, M. Paraashar,
R. de Wolf, *The Role of Symmetry in Quantum Query-to-Communication
Simulation*, arXiv:2012.05233v2 (fixed version used throughout this
development; v3 renumbers the old Lemma 6.5 as Lemma 6.4).

This module only fixes the paper's objects; no theorem of the paper is assumed
here.  The encoding is the one of §2: a sign string `x ∈ {−1,1}^n` is a Boolean
word `Cube n` with `true ↦ +1` and `false ↦ −1` (`signVal`).  Consequently a
two-party function `G : {−1,1}^j × {−1,1}^k → {−1,1}` is a function
`Cube j → Cube k → Bool`, and a Boolean function is `Cube n → Bool`.

Definitions implemented, with paper locations:

* `compose` — Definition 2.13 (`f ∘ G`, p. 11).
* `partialCompose` — Definition 2.3 (composition with a partial function, p. 9).
* `hadamardWord` — Definition 2.20 (Hadamard codewords, p. 12).
* `hadamardization` — Definition 2.21 (`h_G`, p. 13).
* `hadamardCompose` — `r ∘̃ h_G` (§5.1, p. 24).
* `IsSymmetric` / `IsTransitive` — Definitions 2.1 / 2.2 (p. 9).
* `IsBalanced`, `disc`, `bdisc` — Definitions 2.16–2.18 (p. 11–12).
* `approxDegreeEps`, `spectralNorm`, `approxSpectralNorm` — Definitions 2.4,
  2.9, 2.10 (p. 10).
* `and2`, `xor2` — the two-bit gadgets `AND₂`, `XOR₂` (§1).

The Hadamard codeword `H(s)` is represented as a word indexed by `Cube m`
itself (`Fin m → Bool`, of cardinality `2^m`), which is exactly the paper's
indexing of `{−1,1}^{2^m}` by `t ∈ {−1,1}^m`.
-/

namespace Qatlib.Papers.SymQueryComm20.MainResults.SourceModel

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

/-! ## Sign strings, cubes and weights -/

/-- Sign encoding used throughout: `true ↦ +1`, `false ↦ −1`. -/
def signVal : Bool → ℝ := fun b => if b then 1 else -1

/-- A Boolean word over a finite index type. -/
abbrev Word (ι : Type) := ι → Bool

/-- The Boolean cube `{−1,1}^n`, encoded as `Fin n → Bool`. -/
abbrev Cube (n : ℕ) := Word (Fin n)

/-- Hamming weight (number of `true` entries, i.e. of `+1`s). -/
def hweight {n : ℕ} (x : Cube n) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-! ## Symmetry and transitivity (Definitions 2.1 and 2.2, p. 9) -/

/-- Definition 2.1: `f` is symmetric if `f x = f (x ∘ σ)` for every permutation
`σ ∈ S_n`. -/
def IsSymmetric {n : ℕ} (f : Cube n → Bool) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Cube n), f (fun i => x (σ i)) = f x

/-- Definition 2.2: `f` is transitive if for all coordinates `i, j` there is a
permutation moving `i` to `j` and preserving `f`. -/
def IsTransitive {n : ℕ} (f : Cube n → Bool) : Prop :=
  ∀ i j : Fin n, ∃ σ : Equiv.Perm (Fin n),
    σ i = j ∧ ∀ x : Cube n, f (fun k => x (σ k)) = f x

/-! ## Composition (Definitions 2.3 and 2.13) -/

/-- Definition 2.13: `f ∘ G` for `f : {−1,1}^n → {−1,1}` and
`G : {−1,1}^j × {−1,1}^k → {−1,1}`.  Alice holds `X = (X₁,…,Xₙ)` and Bob
holds `Y = (Y₁,…,Yₙ)`; the output is `f (G (X₁,Y₁),…,G (Xₙ,Yₙ))`. -/
def compose {n j k : ℕ} (f : Cube n → Bool) (G : Cube j → Cube k → Bool) :
    (Fin n → Cube j) → (Fin n → Cube k) → Bool :=
  fun X Y => f (fun i => G (X i) (Y i))

/-- The same composition, with the two party inputs encoded as words over
`Fin n × Fin j` and `Fin n × Fin k` (the form consumed by the complexity
measures, which take `Word ι`). -/
def composeWord {n j k : ℕ} (f : Cube n → Bool) (G : Cube j → Cube k → Bool) :
    Word (Fin n × Fin j) → Word (Fin n × Fin k) → Bool :=
  fun X Y => f (fun i => G (fun a => X (i, a)) (fun b => Y (i, b)))

/-- Definition 2.3: composition with a partial function `g : {−1,1}^m →
{−1,1,⋆}`.  If every copy of `g` returns a definite sign, apply `f`; otherwise
return `−1` (`false`). -/
def partialCompose {n : ℕ} {ι : Type} (f : Cube n → Bool) (g : ι → Option Bool)
    (x : Fin n → ι) : Bool :=
  if h : ∀ i, ∃ b, g (x i) = some b then f (fun i => Classical.choose (h i)) else false

/-! ## Hadamard codewords and `h_G` (Definitions 2.20 and 2.21) -/

/-- The exponent `#{i : s_i = −1 and t_i = −1}` of the Hadamard evaluation
`H(s)_t = ∏_{i: s_i = −1} t_i`. -/
def hadamardExponent {m : ℕ} (s t : Cube m) : ℕ :=
  (Finset.univ.filter (fun i => s i = false ∧ t i = false)).card

/-- Definition 2.20: the Hadamard codeword of `s ∈ {−1,1}^{log n}`, represented
as the word `t ↦ ∏_{i: s_i = −1} t_i` over the index cube `Cube m`. -/
def hadamardWord {m : ℕ} (s : Cube m) : Word (Cube m) :=
  fun t => decide (Even (hadamardExponent s t))

/-- `x` is a Hadamard codeword up to sign, i.e. `x = ±H(s)` for some `s`. -/
def IsSignedHadamard {m : ℕ} (x : Word (Cube m)) : Prop :=
  ∃ s : Cube m, (∀ t, x t = hadamardWord s t) ∨ (∀ t, x t = !(hadamardWord s t))

/-- Decode a signed Hadamard codeword, when it is one.  Well-definedness on the
codewords used below is `decodeHadamard_hadamardWord` and
`decodeHadamard_neg`. -/
def decodeHadamard {m : ℕ} (x : Word (Cube m)) : Option (Cube m) :=
  if h : IsSignedHadamard x then some (Classical.choose h) else none

/-- Definition 2.21: the Hadamardisation of a two-party function `G`.  On a
block `(x,y)` that is a pair of signed Hadamard codewords the value is
`G(s,t)` for the decoded `s,t`; otherwise the function is undefined (`none`,
written `⋆` in the paper). -/
def hadamardization {l m : ℕ} (G : Cube l → Cube m → Bool) :
    (Word (Cube l) × Word (Cube m)) → Option Bool :=
  fun p =>
    match decodeHadamard p.1, decodeHadamard p.2 with
    | some s, some t => some (G s t)
    | _, _ => none

/-- `r ∘̃ h_G` (§5.1, p. 24): the total function on `n` blocks of `j + k` bits
obtained by applying Definition 2.3 to `h_G`.  The input type is
`Word (Fin n × (Cube l ⊕ Cube m))`, corresponding to `n·(j+k)` bits with
`j = 2^l`, `k = 2^m`. -/
def hadamardCompose {n l m : ℕ} (r : Cube n → Bool) (G : Cube l → Cube m → Bool) :
    Word (Fin n × (Cube l ⊕ Cube m)) → Bool :=
  fun z =>
    partialCompose r (hadamardization G)
      (fun i => (fun a => z (i, Sum.inl a), fun b => z (i, Sum.inr b)))

/-! ## The two-bit gadgets -/

/-- `AND₂` in sign encoding: returns `−1` exactly when both inputs are `−1`. -/
def and2 : Bool → Bool → Bool := fun a b => a || b

/-- `XOR₂` in sign encoding: the product of the two signs, i.e. `true` (sign
`+1`) exactly when the inputs agree.  This is the gadget for which
`EQ_n = NOR_n ∘ XOR₂` (§1, p. 3). -/
def xor2 : Bool → Bool → Bool := fun a b => (a == b)

/-- Compose a single-input function with a two-bit inner gadget
`□ ∈ {AND₂, XOR₂}`. -/
def composeWithInner {ι : Type} (f : Word ι → Bool) (inner : Bool → Bool → Bool) :
    Word ι → Word ι → Bool :=
  fun a b => f (fun t => inner (a t) (b t))

/-- Alice's preprocessing for the `AND₂` reduction of Lemma 5.4 (p. 25): the
`i`-th block becomes `(H(xᵢ), (−1)^k)`. -/
def prepAliceAnd {n l m : ℕ} (X : Word (Fin n × Fin l)) :
    Word (Fin n × (Cube l ⊕ Cube m)) :=
  fun p =>
    match p.2 with
    | Sum.inl a => hadamardWord (fun j => X (p.1, j)) a
    | Sum.inr _ => false

/-- Bob's preprocessing for the `AND₂` reduction of Lemma 5.4: the `i`-th block
becomes `((−1)^j, H(yᵢ))`. -/
def prepBobAnd {n l m : ℕ} (Y : Word (Fin n × Fin m)) :
    Word (Fin n × (Cube l ⊕ Cube m)) :=
  fun p =>
    match p.2 with
    | Sum.inl _ => false
    | Sum.inr b => hadamardWord (fun j => Y (p.1, j)) b

/-- Alice's preprocessing for the `XOR₂` reduction of Lemma 5.4: the `i`-th
block becomes `(H(xᵢ), 1^k)`. -/
def prepAliceXor {n l m : ℕ} (X : Word (Fin n × Fin l)) :
    Word (Fin n × (Cube l ⊕ Cube m)) :=
  fun p =>
    match p.2 with
    | Sum.inl a => hadamardWord (fun j => X (p.1, j)) a
    | Sum.inr _ => true

/-- Bob's preprocessing for the `XOR₂` reduction of Lemma 5.4: the `i`-th block
becomes `(1^j, H(yᵢ))`. -/
def prepBobXor {n l m : ℕ} (Y : Word (Fin n × Fin m)) :
    Word (Fin n × (Cube l ⊕ Cube m)) :=
  fun p =>
    match p.2 with
    | Sum.inl _ => true
    | Sum.inr b => hadamardWord (fun j => Y (p.1, j)) b

/-! ## Distributions and discrepancy (Definitions 2.16–2.18) -/

/-- A probability distribution on `{−1,1}^j × {−1,1}^k`, as a nonnegative real
matrix with total mass one. -/
def IsProbability {j k : ℕ} (lam : Cube j → Cube k → ℝ) : Prop :=
  (∀ x y, 0 ≤ lam x y) ∧ (∑ x, ∑ y, lam x y) = 1

/-- Definition 2.16: `μ` is balanced with respect to `G` if the expected sign of
`G` vanishes. -/
def IsBalanced {j k : ℕ} (lam : Cube j → Cube k → ℝ) (G : Cube j → Cube k → Bool) : Prop :=
  (∑ x, ∑ y, signVal (G x y) * lam x y) = 0

/-- The signed rectangle sum `disc_λ(S × T, G)` of Definition 2.17 (p. 11). -/
def discRect {j k : ℕ} (lam : Cube j → Cube k → ℝ) (G : Cube j → Cube k → Bool)
    (S : Finset (Cube j)) (T : Finset (Cube k)) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ T, signVal (G x y) * lam x y

/-- Definition 2.17: `disc_λ(G)` is the maximum over rectangles. -/
def disc {j k : ℕ} (lam : Cube j → Cube k → ℝ) (G : Cube j → Cube k → Bool) : ℝ :=
  sSup (Set.range fun ST : Finset (Cube j) × Finset (Cube k) =>
    discRect lam G ST.1 ST.2)

/-- Definition 2.18: the balanced discrepancy is the minimum of `disc_λ(G)` over
balanced distributions `λ` (with respect to `G`). -/
def bdisc {j k : ℕ} (G : Cube j → Cube k → Bool) : ℝ :=
  sInf ((fun lam => disc lam G) '' {lam : Cube j → Cube k → ℝ | IsBalanced lam G})

/-! ## Polynomial measures (Definitions 2.4, 2.9 and 2.10) -/

/-- Evaluate a real polynomial at the sign point `x ∈ {−1,1}^n`. -/
def evalSign {ι : Type} (p : MvPolynomial ι ℝ) (x : Word ι) : ℝ :=
  MvPolynomial.eval (fun i => if x i then 1 else -1) p

/-- A polynomial is multilinear if every monomial in its support is squarefree. -/
def IsMultilinear {ι : Type} (p : MvPolynomial ι ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i, m i ≤ 1

/-- Definition 2.4: the `ε`-approximate degree of a Boolean function, over the
sign cube `{−1,1}^n`. -/
def approxDegreeEps {ι : Type} [Fintype ι] (eps : ℝ) (f : Word ι → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial ι ℝ => p.totalDegree) ''
    {p | ∀ x, |evalSign p x - signVal (f x)| ≤ eps})

/-- The paper's default `deg̃(f) = deg̃_{1/3}(f)` (Definition 2.4, p. 10). -/
def approxDeg {ι : Type} [Fintype ι] (f : Word ι → Bool) : ℕ :=
  approxDegreeEps (1 / 3) f

/-- Definition 2.9: the spectral norm `‖p‖₁` of a multilinear polynomial is the
sum of the absolute values of its coefficients. -/
def spectralNorm {ι : Type} (p : MvPolynomial ι ℝ) : ℝ :=
  p.support.sum (fun m => |p.coeff m|)

/-- Definition 2.10: the approximate spectral norm `‖f̂‖_{1,ε}`. -/
def approxSpectralNorm {ι : Type} [Fintype ι] (eps : ℝ) (f : Word ι → Bool) : ℝ :=
  sInf ((fun p : MvPolynomial ι ℝ => spectralNorm p) ''
    {p | IsMultilinear p ∧ ∀ x, |evalSign p x - signVal (f x)| ≤ eps})

/-! ## Base-2 logarithm -/

/-- Base-2 logarithm, the convention used in the paper (§2, p. 9). -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-! ## Basic unit lemmas for the Hadamard code -/

/-- The all-`+1` index string. -/
def allTrue (m : ℕ) : Cube m := fun _ => true

/-- Every Hadamard codeword evaluates to `+1` at the all-`+1` point. -/
@[simp] theorem hadamardWord_allTrue {m : ℕ} (s : Cube m) :
    hadamardWord s (allTrue m) = true := by
  unfold hadamardWord hadamardExponent allTrue
  have h : (Finset.univ.filter (fun i => s i = false ∧ true = false)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact absurd hi.2 (by decide)
  rw [h]
  simp

/-- A Hadamard codeword is never the pointwise negation of another one: at the
all-`+1` point every codeword is `+1` but every negation is `−1`. -/
theorem hadamardWord_ne_neg {m : ℕ} (s s' : Cube m) :
    ¬ (∀ t, hadamardWord s t = !(hadamardWord s' t)) := by
  intro h
  have h' := h (allTrue m)
  rw [hadamardWord_allTrue, hadamardWord_allTrue] at h'
  exact absurd h' (by decide)

/-- The cardinality of a filtered singleton condition:
`#{j : p j and j = i} = if p i then 1 else 0`. -/
theorem card_filter_and_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (i : ι) :
    (Finset.univ.filter (fun j => p j ∧ j = i)).card = if p i then 1 else 0 := by
  by_cases hi : p i
  · have hset : Finset.univ.filter (fun j => p j ∧ j = i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · intro hji; subst hji; exact ⟨hi, rfl⟩
    rw [hset, Finset.card_singleton, if_pos hi]
  · have hset : Finset.univ.filter (fun j => p j ∧ j = i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ hj
      exact hi (hj.2 ▸ hj.1)
    rw [hset, Finset.card_empty, if_neg hi]

/-- Hadamard codewords are injective: `H(s) = H(s')` implies `s = s'`.  Proof:
at the index `t` that is `−1` exactly at a coordinate where `s` and `s'` differ,
the two codewords differ. -/
theorem hadamardWord_injective {m : ℕ} {s s' : Cube m}
    (h : ∀ t, hadamardWord s t = hadamardWord s' t) : s = s' := by
  funext i
  by_contra hne
  -- use the index string that is `−1` exactly at `i`
  let t : Cube m := fun j => decide (j ≠ i)
  have ht : ∀ j, (t j = false) ↔ (j = i) := by
    intro j
    dsimp [t]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have hval := h t
  unfold hadamardWord at hval
  -- reduce both exponent counts to `if s i = false then 1 else 0`
  have e1 : hadamardExponent s t = if s i = false then 1 else 0 := by
    unfold hadamardExponent
    have hf : (Finset.univ.filter (fun j => s j = false ∧ t j = false)) =
        (Finset.univ.filter (fun j => s j = false ∧ j = i)) := by
      apply Finset.filter_congr
      intro j _
      rw [ht j]
    rw [hf, card_filter_and_eq]
  have e2 : hadamardExponent s' t = if s' i = false then 1 else 0 := by
    unfold hadamardExponent
    have hf : (Finset.univ.filter (fun j => s' j = false ∧ t j = false)) =
        (Finset.univ.filter (fun j => s' j = false ∧ j = i)) := by
      apply Finset.filter_congr
      intro j _
      rw [ht j]
    rw [hf, card_filter_and_eq]
  rw [e1, e2] at hval
  -- the only possible values are 0 and 1, and these differ iff the bits differ
  cases hs : s i <;> cases hs' : s' i
  · exact hne (by rw [hs, hs'])
  · simp [hs, hs'] at hval
  · simp [hs, hs'] at hval
  · exact hne (by rw [hs, hs'])

/-- Decoding returns the source of a Hadamard codeword. -/
theorem decodeHadamard_hadamardWord {m : ℕ} (s : Cube m) :
    decodeHadamard (hadamardWord s) = some s := by
  have his : IsSignedHadamard (hadamardWord s) := ⟨s, Or.inl fun _ => rfl⟩
  unfold decodeHadamard
  rw [dif_pos his]
  congr 1
  rcases Classical.choose_spec his with hpos | hneg
  · exact hadamardWord_injective (fun t => (hpos t).symm)
  · exact absurd hneg (hadamardWord_ne_neg s (Classical.choose his))

/-- Decoding returns the source of a negated Hadamard codeword. -/
theorem decodeHadamard_neg {m : ℕ} (s : Cube m) :
    decodeHadamard (fun t => !(hadamardWord s t)) = some s := by
  have his : IsSignedHadamard (fun t => !(hadamardWord s t)) :=
    ⟨s, Or.inr fun _ => rfl⟩
  unfold decodeHadamard
  rw [dif_pos his]
  congr 1
  rcases Classical.choose_spec his with hpos | hneg
  · exact absurd (fun t => (hpos t).symm) (hadamardWord_ne_neg (Classical.choose his) s)
  · refine hadamardWord_injective (s := Classical.choose his) (s' := s) (fun t => ?_)
    have h := congrArg (fun b => !b) (hneg t)
    simpa using h.symm

end

end Qatlib.Papers.SymQueryComm20.MainResults.SourceModel

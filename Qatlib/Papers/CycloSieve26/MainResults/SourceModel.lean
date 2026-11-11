/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option backward.isDefEq.respectTransparency false

/-!
# CycloSieve26 — source model

Vocabulary for the paper *Cyclotomic Cosets: Hidden Subgroup and Quantum Sieving
Algorithm for Prime-Power Moduli* (Boucher–Fouque–Shen, arXiv:2609.34996v1,
28 September 2026), block `MainResults`.

This module is **definitions only**.  All mathematical content lives in the
sibling modules under this directory.

## Modelling conventions

The paper works over the cyclotomic ring `R_L = R/π^L R` with `R = ℤ[ζ_p]`,
`L = t(p-1)` and `|R_L| = p^L`.  Its additive group is an elementary abelian
`p`-group of rank `L` (`R_L ≅ (ℤ/pℤ)^L` as an additive group), so throughout
this development the **additive group of `R_L` is modelled as
`RL p L := Fin L → ZMod p`**.  The trace pairing `B_L` of Lemma 4 is modelled by
the coordinate pairing `coordPair` (the paper's non-degenerate form after the
trace-dual basis of Lemma 4), and the characters `χ_y` of Proposition 1 are the
explicit coordinate characters `chiCoord` of `CharacterDuality`.

`RLn n p L := Fin n → RL p L` is the `n`-fold product `R_L^n` on which the
`n`-dimensional problems (`CCP`, `PSP`, `DCP`) live.

## Main definitions

* `levelOf` — the level `L = t(p-1)`;
* `RL`, `RLn` — the additive group of `R_L` and its `n`-th power;
* `coordPair`, `coordSmul` — the coordinate pairing and the coordinate scalar
  action used to state the character properties;
* `levelReduce`, `levelSection` — the projection `R_{L+1} → R_L` and its
  zero-padding section, used to state the `R_L → R_{L-1}` character descent;
* `LambdaSystem` — the data `(ζ, π, λ_j)` of the cyclotomic group with
  `π · λ_j = ζ^j − 1` (the identity `λ_j = (ζ^j−1)/π` of §1.1);
* `CCPSample`, `PhaseState`, `DCPSample` — the sample shapes of Definitions 5, 6
  and 9;
* `IsPolyIn`, `IsQuasiPolyIn`, `IsQuasiPolyLowerIn`, `IsPolySpaceIn` — the
  asymptotic vocabularies of §2 (“quasi-polynomial” means `2^{O(log² ·)}`);
* `Algorithm` — the costed algorithm record carrying sample, time and space
  profiles together with the semantic correctness promise of the paper.

Nothing here is axiomatic: every structure field is data or a hypothesis
supplied by the consumer.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CycloSieve26.MainResults

open Finset
open scoped BigOperators

/-! ## Levels and the additive group of `R_L` -/

/-- The level `L = t(p-1)` attached to a prime `p` and exponent `t ≥ 1`
(§2.1: `q = p^t` and `q = u₀ π^L`). -/
def levelOf (p t : ℕ) : ℕ := t * (p - 1)

/-- The **additive group of `R_L = R/π^L R`**, modelled as `(ℤ/pℤ)^L`.
The paper's `R_L` has `p^L` elements (Section 2.1) and exponent `p`, since
`p = u₀ π^{p-1}` and `L = t(p-1) ≥ p-1`; hence its additive group is the
elementary abelian `p`-group of rank `L` modelled here. -/
abbrev RL (p L : ℕ) : Type := Fin L → ZMod p

/-- The `n`-fold power `R_L^n` of the additive group of `R_L`. -/
abbrev RLn (n p L : ℕ) : Type := Fin n → RL p L

/-! ## Pairing, scalar action and the level projection -/

/-- The **coordinate pairing** on `R_L`: `coordPair x y = ∑ i, x i * y i`.
This is the coordinate model of the trace form
`B_L(x,y) = Tr(xy/(p π^{L-1})) mod ℤ` of Lemma 4 (written in the trace-dual
basis of the proof of Lemma 4, where the form becomes the standard dot
product). -/
def coordPair (p L : ℕ) (x y : RL p L) : ZMod p := ∑ i, x i * y i

/-- The coordinate scalar action used in Proposition 2(2): an element `λ` acts
coordinatewise, `(λ ⊙ x) i = λ i * x i`.  In the trace-dual coordinate model
this is multiplication by an element of `R_L`; the identity
`B_L(λ x, y) = B_L(x, λ y)` is exactly the symmetry of `coordPair`. -/
def coordSmul (p L : ℕ) (lam x : RL p L) : RL p L := fun i => lam i * x i

/-- The projection `R_{L+1} → R_L` dropping the last coordinate.  This models
the quotient map `R/π^{L+1}R → R/π^L R` in the `π`-adic tower. -/
def levelReduce (p L : ℕ) (x : RL p (L + 1)) : RL p L := fun i => x i.castSucc

/-- The zero-padding section `R_L → R_{L+1}` used to witness the descent of a
character of `R_{L+1}` to `R_L` (Proposition 2(5)). -/
def levelSection (p L : ℕ) (x : RL p L) : RL p (L + 1) := fun i =>
  if h : (i : ℕ) < L then x ⟨i, h⟩ else 0

/-! ## The `λ`-system of the cyclotomic group -/

/-- The **`λ`-system** of §1.1: an element `ζ` (a primitive `p`-th root of
unity in the paper), an element `π` (the uniformiser `ζ - 1`) and the family
`λ_j = (ζ^j − 1)/π`, recorded by the relation that defines it,
`π * λ_j = ζ^j − 1`.  The cocycle identity `λ_{a+b} = λ_a + ζ^a λ_b` of the
proof of Lemma 6 is proved from this relation in `SieveStep`. -/
structure LambdaSystem (A : Type*) [CommRing A] where
  /-- `ζ`, a primitive `p`-th root of unity in the source paper -/
  ζ : A
  /-- `π = ζ − 1`, the uniformiser -/
  π : A
  /-- the family `λ_j` -/
  lam : ℕ → A
  /-- defining relation `π * λ_j = ζ^j − 1` -/
  hlam : ∀ j : ℕ, π * lam j = ζ ^ j - 1

/-! ## Sample shapes of the coset problems -/

/-- A **CCP sample** (Definition 6): the state
`(1/√p) ∑_{j∈F_p} |j⟩ |x + λ_j s⟩`; the record keeps the offset `x`. -/
structure CCPSample (n p L : ℕ) where
  /-- the random offset `x ∈ R_q^n` -/
  offset : RLn n p L

/-- A **phase-state sample** of Definition 9: a label `y ∈ R_L^n` together with
the phase state `(1/√p) ∑_j χ_y(λ_j s) |j⟩` for the secret `s`. -/
structure PhaseState (n p L : ℕ) where
  /-- the measured label `y ∈ R_L^n` -/
  label : RLn n p L
  /-- the secret `s ∈ R_L^n` encoded in the phases -/
  secret : RLn n p L
  /-- the amplitudes `j ↦ χ_y(λ_j s)` -/
  amplitude : ZMod p → ℂ

/-- A **DCP sample** (Definition 5) over `ℤ_q^n`. -/
structure DCPSample (n q : ℕ) where
  /-- the random offset `x ∈ ℤ_q^n` -/
  offset : Fin n → ZMod q

/-! ## Asymptotic vocabulary -/

/-- `f` is **polynomially bounded** in the two parameters `n` and `q`. -/
def IsPolyIn (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n q : ℕ, f n q ≤ C * ((n + 1) * (q + 1)) ^ d

/-- `f` is **quasi-polynomially bounded**: `f = 2^{O(log n log q)}`. -/
def IsQuasiPolyIn (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ c C : ℕ, ∀ n q : ℕ,
    f n q ≤ C * 2 ^ (c * (Nat.log2 (n + 1) + 1) * (Nat.log2 (q + 1) + 1))

/-- `f` grows **at least quasi-polynomially**: `f = 2^{Ω(log n log q)}`, i.e.
`2^{c log n log q} ≤ C · f` for positive constants `c,C`. -/
def IsQuasiPolyLowerIn (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ c C : ℕ, 0 < c ∧ ∀ n q : ℕ,
    2 ^ (c * (Nat.log2 (n + 1) + 1) * (Nat.log2 (q + 1) + 1)) ≤ C * f n q

/-- `f` is **polynomial quantum space**: `f = poly(n)`. -/
def IsPolySpaceIn (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n q : ℕ, f n q ≤ C * (n + 1) ^ d

/-- The sample threshold `2^{Ω(log n log q)}`; this is
`IsQuasiPolyLowerIn` read as a requirement on the number of samples. -/
def MeetsQuasiPolySampleThreshold (ℓ : ℕ → ℕ → ℕ) : Prop := IsQuasiPolyLowerIn ℓ

/-! ## Costed algorithms -/

/-- An **abstract costed algorithm**: its sample, time and space profiles
together with the semantic correctness promise of the paper (the promise is
left as a `Prop` because the paper's algorithmic results are stated relative to
the problem definitions of Section 2.4 and the sample models above). -/
structure Algorithm where
  /-- number of input samples consumed as a function of `(n, q)` -/
  samples : ℕ → ℕ → ℕ
  /-- running time in elementary gates as a function of `(n, q)` -/
  time : ℕ → ℕ → ℕ
  /-- peak quantum space (qubits) as a function of `(n, q)` -/
  space : ℕ → ℕ → ℕ
  /-- constant success probability of the algorithm -/
  successProbability : ℚ
  /-- semantic correctness promise of the paper -/
  solves : Prop

end Qatlib.Papers.CycloSieve26.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# QAOABoolSAT22 — shared definitions

This file collects the concrete mathematical objects used in the paper
"Solving boolean satisfiability problems with the quantum approximate
optimization algorithm" (arXiv:2208.06909).

Everything here is stated at the level of the paper's own definitions:
* the random k-SAT ensemble (Definition 1) and the level-p QAOA state
  (Definition 2, equation (11));
* the multinomial coefficient and the generalized multinomial sum
  `S_q(A,b,c;n)` (Definition 15, equation (48));
* the function `F` of equation (76) and the single-variable `Φ` of
  equation (54);
* the toy Hamming-weight-squared model `Φ_{β,rγ}` of Section 5.2;
* the coordinate change `Y^C_j` and the function `ζ`, `ζ̃_C`
  (Definitions 28, 34 and 35);
* the combinatorial weights `B_{β,s}` (equation (25)) and `c_J`
  (equation (29)) together with the data of Example 16.

The statements of the individual claims live in the sibling directories
and only depend on these definitions.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Complex

noncomputable section

set_option autoImplicit false

namespace Qatlib.Papers.QAOABoolSAT22.MainResults

/-! ### Elementary complex analysis helpers -/

/-- The partial derivative of `f : (ι → ℂ) → ℂ` with respect to the coordinate `i`,
evaluated at `x`, i.e. the directional derivative along the `i`-th basis vector.

This is the formal counterpart of the paper's notation `∂_α F` for the
multivariate functions `F` of Section 5.3. -/
def pderiv {ι : Type*} [DecidableEq ι] (f : (ι → ℂ) → ℂ) (x : ι → ℂ) (i : ι) : ℂ :=
  fderiv ℂ f x (Pi.single i 1)

/-- Second partial derivative, defined as the first partial derivative of `∂_i f`. -/
def pderiv2 {ι : Type*} [DecidableEq ι] (f : (ι → ℂ) → ℂ) (x : ι → ℂ) (i j : ι) : ℂ :=
  pderiv (fun y => pderiv f y i) x j

/-- The `2^q`-th root used in equation (76): the principal determination of
`(-c)^{1/2^q}`, written with the complex power.  The paper fixes a branch of this
root in Definition 20 via a rephasing trick; the principal branch is a valid
choice and the paper's estimates are insensitive to the branch (they only use the
modulus `|c|^{1/2^q}`). -/
def qroot (q : ℕ) (c : ℂ) : ℂ :=
  (-c) ^ (((2 ^ q : ℕ) : ℂ)⁻¹)

/-! ### Multinomial sums (Definition 15, equation (48)) -/

/-- The multinomial coefficient `n! / ∏_s n_s!` appearing in equation (26),
as a complex number. -/
def multinomialCoeff {S : Type*} [Fintype S] (n : ℕ) (ns : S → ℕ) : ℂ :=
  (n.factorial : ℂ) / ∏ s : S, ((ns s).factorial : ℂ)

/-- The generalized multinomial sum `S_q(A,b,c;n)` of Definition 15, equation (48):

`S_q(A,b,c;n) = ∑_{(n_s), ∑_s n_s = n} (n; (n_s)) ∏_s b_s^{n_s}
   exp(n ∑_α c_α (n⁻¹ ∑_s A_{αs} n_s)^{2^q})`.

The paper keeps `A, b, c` as arbitrary complex families indexed by arbitrary
finite sets `A` and `S`; here they are `Am : A → S → ℂ`, `b : S → ℂ`, `c : A → ℂ`.
-/
def genMultinomialSum (q : ℕ) {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (Am : A → S → ℂ) (b : S → ℂ) (c : A → ℂ) (n : ℕ) : ℂ :=
  ∑ ns ∈ (Finset.univ.filter (fun ns : S → Fin (n + 1) => ∑ s : S, (ns s).val = n)),
    multinomialCoeff n (fun s => (ns s).val) * ∏ s : S, (b s) ^ ((ns s).val) *
      Complex.exp ((n : ℂ) * ∑ a : A,
        c a * (((n : ℂ)⁻¹ * ∑ s : S, Am a s * ((ns s).val : ℂ)) ^ (2 ^ q)))

/-! ### The functions `F` and `Φ` -/

/-- The function `F(z) = log ∑_s b_s exp(∑_α A_{αs} ρ_α z_α)` with an explicit
family of roots `ρ_α`.  This is the common core of equation (76) (with
`ρ_α = (-c_α)^{1/2^q}`) and equation (54) (with `ρ_α = √c_α`). -/
def Fgen {S A : Type*} [Fintype S] [Fintype A] (Am : A → S → ℂ) (b : S → ℂ)
    (ρ : A → ℂ) (z : A → ℂ) : ℂ :=
  Complex.log (∑ s : S, b s * Complex.exp (∑ a : A, Am a s * ρ a * z a))

/-- Equation (76): `F(z_α) = log ∑_s b_s exp(∑_α A_{αs} (-c_α)^{1/2^q} z_α)`. -/
def Ffun (q : ℕ) {S A : Type*} [Fintype S] [Fintype A] (Am : A → S → ℂ) (b : S → ℂ)
    (c : A → ℂ) (z : A → ℂ) : ℂ :=
  Fgen Am b (fun a => qroot q (c a)) z

/-- Equation (54): `Φ(y) = -1/4 ∑_α y_α^2 + log ∑_s b_s exp(∑_α √c_α A_{αs} y_α)`. -/
def PhiOne {A S : Type*} [Fintype A] [Fintype S] (Am : A → S → ℂ) (b : S → ℂ)
    (c : A → ℂ) (y : A → ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ∑ a : A, (y a) ^ 2 + Fgen Am b (fun a => Complex.sqrt (c a)) y

/-- The scalar part `-1/4 ∑_α y_α² + F(y)` of the function `Φ` of equation (75),
for a general `F`. -/
def PhiOf {A : Type*} [Fintype A] (F : (A → ℂ) → ℂ) (y : A → ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ∑ a : A, (y a) ^ 2 + F y

/-- The fixed-point equation of Proposition 24, equations (78)–(79):
`z_α = -(2^q) (∂_α F(z))^{2^q-1}`.  For `q = 1` this is the critical point
condition `y_α = 2 ∂_α F(y)` of the function `Φ` (up to the sign convention
absorbed in the definition of `F`). -/
def SaddlePoint {A : Type*} [Fintype A] [DecidableEq A] (q : ℕ) (F : (A → ℂ) → ℂ)
    (z : A → ℂ) : Prop :=
  ∀ a : A, z a = -(2 : ℂ) ^ q * (pderiv F z a) ^ (2 ^ q - 1)

/-! ### The toy Hamming-weight-squared model (Section 5.2) -/

/-- The one-variable function `Φ_{β,rγ}` of Section 5.2, obtained from the
Gaussian representation of the amplitude of equation (34):

`Φ_{β,rγ}(θ) = -log 2/2 - iβ/2 - θ²/4
   + log(e^{iβ/2} cos(β/2) - i sin(β/2) e^{θ √(-i rγ/2)})`.

The square root is the principal one; the exponent `θ √(-i rγ/2)` is the one
appearing in the derivation of Section 5.2 (it is `√(θ² - 2 i rγ)` after the
scaling `θ ↦ θ/√n`, written in the linearised form used in the fixed-point
analysis of equations (36)–(37)). -/
def PhiToy (β rγ θ : ℂ) : ℂ :=
  -((Real.log 2 : ℂ)) / 2 - Complex.I * β / 2 - θ ^ 2 / 4 +
    Complex.log (Complex.exp (Complex.I * β / 2) * Complex.cos (β / 2) -
      Complex.I * Complex.sin (β / 2) *
        Complex.exp (θ * Complex.sqrt (-(Complex.I * rγ) / 2)))

/-- The contraction map `F` of Lemma 9:
`F(θ) = -i √(-2 i rγ) sin(β/2) e^{θ √(-i rγ/2)}
          / (cos(β/2) - i sin(β/2) e^{θ √(-i rγ/2)})`. -/
def Fmap (β rγ θ : ℂ) : ℂ :=
  -Complex.I * Complex.sqrt (-2 * Complex.I * rγ) * Complex.sin (β / 2) *
      Complex.exp (θ * Complex.sqrt (-(Complex.I * rγ) / 2)) /
    (Complex.cos (β / 2) - Complex.I * Complex.sin (β / 2) *
      Complex.exp (θ * Complex.sqrt (-(Complex.I * rγ) / 2)))

/-- The toy amplitude of equation (34): the Hamming-weight-squared QAOA
amplitude `⟨0| e^{-iβ H_B/2} e^{-iγ H_C/2} |+⟩` written as a binomial sum. -/
def toyAmplitude (n : ℕ) (β γ : ℂ) : ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) *
      Complex.cos (β / 2) ^ (n - k) * (-Complex.I * Complex.sin (β / 2)) ^ k *
        Complex.exp (-(Complex.I * γ / 2) * (k : ℂ) ^ 2)

/-! ### The function `ζ`, the coordinate change `Y^C`, and `ζ̃_C`
(Definitions 28, 34 and 35) -/

/-- The function `ζ` of Definition 28 on `m` arguments:
`ζ(y^{(0)},…,y^{(m-1)}) = ∏_{j<m} (-i y^{(j)})^{1/2^{m-1-j}}`,
with the convention `ζ(∅) = 1` (equation (91)). -/
def zetaN (m : ℕ) (y : Fin m → ℂ) : ℂ :=
  ∏ j : Fin m, (-Complex.I * y j) ^ ((((1 : ℝ) / 2 ^ (m - 1 - j.val)) : ℝ) : ℂ)

/-- Definition 28 for a `q`-tuple: `ζ(y^{(0)},…,y^{(q-1)})`. -/
def zeta (q : ℕ) (y : Fin q → ℂ) : ℂ := zetaN q y

/-- The recursive coordinate change `Y^C` of Definition 34, extended to all
indices `j : ℕ` (with `ỹ^{(j)} = 0` beyond `q`):

`Y^{(j)} = ỹ^{(j)} + 2 i C^{1/2^{j+1}} √(ζ(Y^{(0)},…,Y^{(j-1)}))`,
which specialises to `Y^{(0)} = ỹ^{(0)} + 2 i C^{1/2}` (equation (104)) and to
equation (105) for `j ≥ 1`. -/
def YCseq (C : ℂ) (yt : ℕ → ℂ) : ℕ → ℂ
  | 0 => yt 0 + 2 * Complex.I * C ^ ((1 / 2 : ℝ) : ℂ) * Complex.sqrt (zetaN 0 finZeroElim)
  | (j + 1) =>
      yt (j + 1) + 2 * Complex.I * C ^ ((((1 : ℝ) / 2 ^ (j + 2)) : ℝ) : ℂ) *
        Complex.sqrt (zetaN (j + 1) (fun i : Fin (j + 1) => YCseq C yt i.val))

/-- The finite-`q` coordinate change `Y^C_j(ỹ)` of Definition 34. -/
def YC (q : ℕ) (C : ℂ) (yt : Fin q → ℂ) : Fin q → ℂ :=
  fun j => YCseq C (fun m => if h : m < q then yt ⟨m, h⟩ else 0) j.val

/-- Definition 35: `ζ̃_C(ỹ) = ζ(Y^C(ỹ))`. -/
def zetaTilde (q : ℕ) (C : ℂ) (yt : Fin q → ℂ) : ℂ :=
  zeta q (YC q C yt)

/-- The function `Φ` in the `ỹ` coordinates, equation (75):
`Φ(ỹ) = -1/4 ∑_{α,j} (Y^{(j)}_α(ỹ))² + F(ζ̃_α(ỹ))`. -/
def PhiTilde {A : Type*} [Fintype A] (q : ℕ) (C : A → ℂ) (F : (A → ℂ) → ℂ)
    (yt : A → Fin q → ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ∑ a : A, ∑ j : Fin q, (YC q (C a) (yt a) j) ^ 2 +
    F (fun a => zetaTilde q (C a) (yt a))

/-- The un-tilded version of `Φ` with `Y^{(j)}_α = y^{(j)}_α` and `ζ` applied to
the `y`-variables, used in the statement of Proposition 33 and Corollary 39. -/
def PhiRaw {A : Type*} [Fintype A] (q : ℕ) (F : (A → ℂ) → ℂ) (y : A → Fin q → ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ∑ a : A, ∑ j : Fin q, (y a j) ^ 2 +
    F (fun a => zeta q (y a))

/-! ### Random k-SAT and the level-p QAOA state
(Definitions 1 and 2, equation (11)) -/

/-- A literal on `n` boolean variables: a variable index together with the
polarity (`true` means the literal is `x_i`, `false` means `¬x_i`). -/
abbrev Lit (n : ℕ) : Type := Fin n × Bool

/-- A boolean assignment of `n` variables. -/
abbrev Assignment (n : ℕ) : Type := Fin n → Bool

/-- A `k`-clause is a `k`-tuple of literals (Definition 1: the clause is the OR
of its literals). -/
abbrev Clause (n k : ℕ) : Type := Fin k → Lit n

instance (n k : ℕ) : Fintype (Clause n k) := inferInstance
instance (n k : ℕ) : DecidableEq (Clause n k) := inferInstance

/-- A literal is satisfied by an assignment when the variable's value matches
the polarity. -/
def literalSat {n : ℕ} (y : Assignment n) (l : Lit n) : Bool :=
  y l.1 == l.2

/-- A clause is satisfied when at least one of its literals is. -/
def clauseSat {n k : ℕ} (σ : Clause n k) (y : Assignment n) : Bool :=
  decide (∃ j : Fin k, literalSat y (σ j) = true)

/-- The number of clauses of a formula `σ` (a finite family of clauses)
unsatisfied by `y`.  This is the diagonal Hamiltonian `H[σ]` of Definition 2,
which only enters through this count. -/
def unsatCount {m k n : ℕ} (σ : Fin m → Clause n k) (y : Assignment n) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => clauseSat (σ c) y = false)).card

/-- The uniform amplitude of `|+⟩^{⊗n}`. -/
def initAmp (n : ℕ) : Assignment n → ℂ :=
  fun _ => ((Real.sqrt 2 : ℂ)⁻¹) ^ n

/-- The diagonal phase `e^{-iγH/2}` applied to an amplitude: the Hamiltonian
`H[σ]` counts unsatisfied clauses. -/
def phaseAmp {m k n : ℕ} (σ : Fin m → Clause n k) (γ : ℝ) (f : Assignment n → ℂ) :
    Assignment n → ℂ :=
  fun y => Complex.exp (-Complex.I * (γ / 2 : ℝ) * (unsatCount σ y : ℂ)) * f y

/-- The mixer `e^{-iβ H_B/2}` with `H_B = ∑_j X_j`, acting on an amplitude.
The matrix element between assignments differing in the `j`-th coordinate is
`-i sin(β/2)`; matching coordinates contribute `cos(β/2)`. -/
def mixAmp (n : ℕ) (β : ℝ) (f : Assignment n → ℂ) : Assignment n → ℂ :=
  fun y => ∑ z : Assignment n,
    (∏ j : Fin n, if y j = z j then Complex.cos (β / 2 : ℝ) else
      -Complex.I * Complex.sin (β / 2 : ℝ)) * f z

/-- The level-`p` QAOA state of Definition 2, equation (11), applied to `|+⟩^{⊗n}`:
the operators are folded in the order `e^{-iβ_{p-1} H_B/2} … e^{-iγ_0 H/2}`,
i.e. the rightmost factor `e^{-iγ_0 H/2}` acts first. -/
def qaoaPsi (p : ℕ) {m k n : ℕ} (σ : Fin m → Clause n k) (β γ : Fin p → ℝ) :
    Assignment n → ℂ :=
  (List.finRange p).foldl
    (fun f i => mixAmp n (β i) (phaseAmp σ (γ i) f)) (initAmp n)

/-- The success probability `⟨Ψ| P_{H=0} |Ψ⟩` for a fixed formula: the total
weight of satisfying assignments. -/
def successOn (p : ℕ) {m k n : ℕ} (σ : Fin m → Clause n k) (β γ : Fin p → ℝ) : ℝ :=
  ∑ y : Assignment n, if unsatCount σ y = 0 then Complex.normSq (qaoaPsi p σ β γ y) else 0

/-- The Poisson weight of `m` clauses at clauses-to-variables ratio `r`
(Definition 1). -/
def poissonWeight (r : ℝ) (n m : ℕ) : ℝ :=
  Real.exp (-(r * n)) * (r * n) ^ m / (m.factorial : ℝ)

/-- The expected success probability over the random k-SAT ensemble
`CNF(n,k,r)`: average over the Poisson-distributed number of clauses and over
uniformly chosen clauses. -/
def ensembleSuccess (p k : ℕ) (r : ℝ) (β γ : Fin p → ℝ) (n : ℕ) : ℝ :=
  ∑' m : ℕ, poissonWeight r n m * ((1 / (2 * (n : ℝ))) ^ (k * m)) *
    ∑ σ : Fin m → Clause n k, successOn p σ β γ

/-- The matrix element of equation (21): the dephased average over the random
ensemble of `∏_j e^{iγ_j H/2} P_{H=0} ∏_j e^{-iγ_{p-1-j} H/2}` between the
assignment tuple `ys`.  Since `H` is diagonal this is a scalar per assignment:
the indicator of simultaneous satisfaction times the phase
`exp(i(∑_j γ_j - ∑_j γ_{p-1-j}) m / 2)`. -/
def dephasedAmp (p m k n : ℕ) (σ : Fin m → Clause n k) (γ : Fin p → ℝ)
    (y : Assignment n) : ℂ :=
  if unsatCount σ y = 0 then
    Complex.exp (Complex.I *
      (((∑ j : Fin p, (γ j : ℂ)) - (∑ j : Fin p, (γ ⟨p - 1 - j.val, by omega⟩ : ℂ))) / 2) *
        (unsatCount σ y : ℂ))
  else 0

/-- The ensemble average of the matrix element of equation (21), which is the
quantity `E((n_s))` of equation (23) when it only depends on the counts. -/
def dephasedValue (p k n : ℕ) (r : ℝ) (γ : Fin p → ℝ)
    (ys : Fin (2 * p + 1) → Assignment n) : ℂ :=
  ∑' m : ℕ, (poissonWeight r n m : ℂ) * ((1 / (2 * (n : ℝ))) ^ (k * m) : ℂ) *
    ∑ σ : Fin m → Clause n k, ∏ j : Fin (2 * p + 1), dephasedAmp p m k n σ γ (ys j)

/-- The counts `n_s` of equation (22): the number of variables `i` on which all
the assignments `y^{(j)}` take the common value `s_j`. -/
def countVector {n : ℕ} (p : ℕ) (ys : Fin (2 * p + 1) → Assignment n)
    (s : Fin (2 * p + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => ∀ j : Fin (2 * p + 1), ys j i = s j)).card

/-! ### The combinatorial weights `B_{β,s}` and `c_J`, and Example 16 -/

/-- The weight `B_{β,s}` of equation (25):

`B_{β,s} = (-1)^{1[s_0 ≠ s_p]} ∏_{j∈[p]}
   cos(β_j/2)^{1[s_j=s_{j+1}] + 1[s_{2p-j}=s_{2p-j-1}]}
   (i sin(β_j/2))^{1[s_j≠s_{j+1}] + 1[s_{2p-j}≠s_{2p-j-1}]}`. -/
def Bbeta (p : ℕ) (β : Fin p → ℝ) (s : Fin (2 * p + 1) → Bool) : ℂ :=
  (-1 : ℂ) ^ (if s ⟨0, by omega⟩ = s ⟨p, by omega⟩ then 0 else 1) *
    ∏ j : Fin p,
      (Complex.cos (((β j) / 2 : ℝ) : ℂ)) ^
        ((if s ⟨j.val, by omega⟩ = s ⟨j.val + 1, by omega⟩ then 1 else 0) +
         (if s ⟨2 * p - j.val, by omega⟩ = s ⟨2 * p - j.val - 1, by omega⟩ then 1 else 0)) *
      (Complex.I * Complex.sin (((β j) / 2 : ℝ) : ℂ)) ^
        ((if s ⟨j.val, by omega⟩ = s ⟨j.val + 1, by omega⟩ then 0 else 1) +
         (if s ⟨2 * p - j.val, by omega⟩ = s ⟨2 * p - j.val - 1, by omega⟩ then 0 else 1))

/-- The weight `c_J` of equation (29), for `J ⊆ [2p+1]`:

`c_J = (-1)^{1[p∈J]} ∏_{j∈J, j<p} (e^{-iγ_j/2}-1) ∏_{j∈J, j>p} (e^{iγ_{2p-j}/2}-1)`. -/
def cJ (p : ℕ) (γ : Fin p → ℝ) (J : Finset (Fin (2 * p + 1))) : ℂ :=
  (-1 : ℂ) ^ (if (⟨p, by omega⟩ : Fin (2 * p + 1)) ∈ J then 1 else 0) *
    ∏ j ∈ J,
      (if h : j.val < p then
        (Complex.exp (-(Complex.I * ((γ ⟨j.val, h⟩ : ℝ) : ℂ)) / 2) - 1) else 1) *
      (if h : p < j.val then
        (Complex.exp (Complex.I * ((γ ⟨2 * p - j.val, by omega⟩ : ℝ) : ℂ) / 2) - 1) else 1)

/-- The matrix `A_{αs}` of equation (53): `1` when all the bits `s_j`, `j ∈ α`,
coincide and `0` otherwise. -/
def AExample16 (p : ℕ) (J : Finset (Fin (2 * p + 1))) (s : Fin (2 * p + 1) → Bool) : ℂ :=
  if ∀ j ∈ J, ∀ j' ∈ J, s j = s j' then 1 else 0

/-- The parameter family `c_α = r c_J` of equation (52). -/
def cExample16 (p : ℕ) (r : ℝ) (γ : Fin p → ℝ) (J : Finset (Fin (2 * p + 1))) : ℂ :=
  (r : ℂ) * cJ p γ J

/-- The index set `A = {J ⊆ [2p+1] : |J| ≥ 2}` of equation (50). -/
abbrev IndexA (p : ℕ) : Type := {J : Finset (Fin (2 * p + 1)) // 2 ≤ J.card}

instance (p : ℕ) : Fintype (IndexA p) := inferInstance
instance (p : ℕ) : DecidableEq (IndexA p) := inferInstance

/-- The function `F` of Proposition 3, equations (13)–(14), built from the data
of Example 16: `b_s = B_{β,s}/2`, `c_J = r c_J`, `A_{Js} = 1[all bits of J agree]`,
and the `1/2` prefactor multiplying the exponent in equation (14). -/
def Fcnf (p : ℕ) (r : ℝ) (β γ : Fin p → ℝ) (z : IndexA p → ℂ) : ℂ :=
  Complex.log (∑ s : Fin (2 * p + 1) → Bool,
    (Bbeta p β s / 2) * Complex.exp ((1 / 2 : ℂ) * ∑ J : IndexA p,
      (r : ℂ) * Complex.sqrt (-(cJ p γ J.val)) * AExample16 p J.val s * z J))

/-- The fixed-point predicate of equation (14): `z_α = ∂_α F(z)` for all `α`,
where `∂_α F` denotes the partial derivative of the scalar function `Fcnf`
(the paper denotes by `F` the map `z ↦ (∂_α F(z))_α`). -/
def FcnfFixedPoint (p : ℕ) (r : ℝ) (β γ : Fin p → ℝ) (z : IndexA p → ℂ) : Prop :=
  ∀ J : IndexA p, z J = pderiv (Fcnf p r β γ) z J

end Qatlib.Papers.QAOABoolSAT22.MainResults

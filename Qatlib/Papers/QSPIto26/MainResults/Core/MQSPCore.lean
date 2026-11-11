/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Core definitions for multivariable quantum signal processing (M-QSP)

Ito, Mori, Sakamoto, Fujii, "Polynomial time constructive decision algorithm for
multivariable quantum signal processing", fixed arXiv:2410.02332v3 (Quantum 10, 2102 (2026)).

This file models the objects needed to state Theorem 1 and Lemmas 1--8:

* `MLaurent m`: the m-variable Laurent polynomial ring over `ℂ`, realised as the
  additive-monoid algebra `ℂ[Fin m → ℤ]` of the exponent lattice (Eq. (1)).
* `var j`, `varInv j`: the variables `a_j` and `a_j^{-1}` (Sec. 2).
* `signalOp j`: the signal operator `A(a_j)` of Eq. (7).
* `phaseOp φ`: the signal-processing operator `e^{iφσ_z}` of Eq. (6).
* `wordMatrix n φ s`: the M-QSP word `e^{iφ_0σ_z} ∏_{k=1}^n A(a_{s_k})e^{iφ_kσ_z}` (Eq. (6)).
* `Constructible n P Q`: `(P,Q)` is constructible by m-variable M-QSP in `n` steps (Eq. (6)/(8)).
* `degVar j P`, `degTotal P`: the per-variable and total degree (Sec. 2, Eqs. (2)).
* `substInv`: substitution `a_j ↦ a_j^{-1}`.
* `starL`: coefficientwise complex conjugation.
* `mqspCDA`: the M-QSP constructivity decision algorithm of Algorithm 1.

The matrix entry `-(Q(a))^*` of Eq. (6) is `-starL Q` and `(P(a))^*` is `starL P`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.QSPIto26.MainResults.Core

open Complex

/-- Exponent lattice of m-variable Laurent monomials. -/
abbrev ExpVec (m : ℕ) := Fin m → ℤ

/-- m-variable Laurent polynomials over `ℂ`, modelled as `ℂ[Fin m → ℤ]` (Eq. (1)). -/
abbrev MLaurent (m : ℕ) := AddMonoidAlgebra ℂ (ExpVec m)

/-- The monomial `a_1^{k 0} ⋯ a_m^{k (m-1)}` with exponent vector `k`. -/
def mono {m : ℕ} (k : ExpVec m) : MLaurent m := AddMonoidAlgebra.single k 1

/-- The constant Laurent polynomial with value `c`. -/
def C' {m : ℕ} (c : ℂ) : MLaurent m := AddMonoidAlgebra.single 0 c

/-- The variable `a_j`. -/
def var {m : ℕ} (j : Fin m) : MLaurent m := mono (Pi.single j (1 : ℤ))

/-- The inverse variable `a_j^{-1}`. -/
def varInv {m : ℕ} (j : Fin m) : MLaurent m := mono (Pi.single j (-1 : ℤ))

/-- Coefficientwise complex conjugation of a Laurent polynomial. -/
def starL {m : ℕ} (P : MLaurent m) : MLaurent m :=
  AddMonoidAlgebra.ofCoeff (P.coeff.mapRange (starRingEnd ℂ) (by simp))

/-- Substitution `a_j ↦ a_j^{-1}` for all `j`, as a ring endomorphism. -/
def substInv (m : ℕ) : MLaurent m →+* MLaurent m :=
  AddMonoidAlgebra.mapDomainRingHom ℂ ((AddEquiv.neg (ExpVec m) : ExpVec m →+ ExpVec m))

/-- The polynomial `P^*` appearing in the lower row of Eq. (6). On the torus `a ∈ T^m`
this is the coefficientwise-conjugate evaluated at `a^{-1}`, i.e. the complex conjugate of
`P(a)`. It combines coefficient conjugation (`starL`) with the exponent inversion `a_j ↦ a_j^{-1}`. -/
def starOp {m : ℕ} (P : MLaurent m) : MLaurent m := substInv m (starL P)

/-- The signal operator `A(a_j)` of Eq. (7). -/
def signalOp {m : ℕ} (j : Fin m) : Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  let half : MLaurent m := C' (1 / 2)
  let s := var j + varInv j
  let d := var j - varInv j
  !![half * s, half * d; half * d, half * s]

/-- The signal-processing operator `e^{iφσ_z}` of Eq. (6). -/
def phaseOp {m : ℕ} (φ : ℝ) : Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  !![C' (Complex.exp (Complex.I * (φ : ℂ))),
     0;
     0,
     C' (Complex.exp (-(Complex.I * (φ : ℂ))))]

/-- The M-QSP word of Eq. (6): `e^{iφ_0σ_z} ∏_{k=1}^n A(a_{s_k})e^{iφ_kσ_z}`. -/
def wordMatrix {m : ℕ} (n : ℕ) (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) :
    Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  phaseOp (φ 0) *
    (List.ofFn fun k : Fin n => signalOp (s k) * phaseOp (φ k.succ)).prod

/-- `(P,Q)` is constructible by m-variable M-QSP in `n` steps (Eq. (6), with Eq. (8) for `n = 0`).
The entry `-(Q(a))^*` is `-starOp Q` and `(P(a))^*` is `starOp P`. -/
def Constructible {m : ℕ} (n : ℕ) (P Q : MLaurent m) : Prop :=
  ∃ (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m),
    wordMatrix n φ s = !![P, Q; -starOp Q, starOp P]

/-- Prefix word of Eq. (64): `e^{iφ_0σ_z} ∏_{k=1}^{l} A(a_{s_k})e^{iφ_kσ_z}` obtained from
an `n`-step word by truncation to its first `l` steps (`l ≤ n`). -/
def wordMatrixPrefix {m : ℕ} (n l : ℕ) (hn : l ≤ n)
    (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) : Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  wordMatrix l (fun k => φ (Fin.castLE (by omega) k)) (fun k => s (Fin.castLE hn k))

/-- The partial product of Eq. (18): `∏_{k=1}^{l'} A(a_{s_k})e^{iφ_kσ_z}`, with the full
sequence of length `l` given by `s : Fin l → Fin m` and `φ : Fin l → ℝ` (zero-based indexing,
so `φ k` is the paper's `φ_{k+1}`). -/
def prefixMatrix {m : ℕ} (l : ℕ) (φ : Fin l → ℝ) (s : Fin l → Fin m)
    (l' : ℕ) (h : l' ≤ l) : Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  (List.ofFn fun k : Fin l' => signalOp (s (Fin.castLE h k)) *
    phaseOp (φ (Fin.castLE h k))).prod

/-- Upper-left entry `P^{(l')}` of `prefixMatrix`. -/
def prefixP {m : ℕ} (l : ℕ) (φ : Fin l → ℝ) (s : Fin l → Fin m)
    (l' : ℕ) (h : l' ≤ l) : MLaurent m := prefixMatrix l φ s l' h 0 0

/-- Upper-right entry `Q^{(l')}` of `prefixMatrix`. -/
def prefixQ {m : ℕ} (l : ℕ) (φ : Fin l → ℝ) (s : Fin l → Fin m)
    (l' : ℕ) (h : l' ≤ l) : MLaurent m := prefixMatrix l φ s l' h 0 1

/-- Degree of `P` with respect to the variable `a_j` (Eq. (2)); `deg 0 = 0`. -/
def degVar {m : ℕ} (j : Fin m) (P : MLaurent m) : ℕ :=
  P.coeff.support.sup (fun k => Int.natAbs (k j))

/-- Total degree `deg P = deg_{a_1} P + ⋯ + deg_{a_m} P`. -/
def degTotal {m : ℕ} (P : MLaurent m) : ℕ := ∑ j, degVar j P

/-- Evaluation of a Laurent polynomial at a tuple `a ∈ (ℂ^*)^m`. -/
def evalAt {m : ℕ} (a : Fin m → ℂ) (P : MLaurent m) : ℂ :=
  P.coeff.sum fun k c => c * ∏ j, a j ^ (k j)

/-- The slice of `P` of terms whose `a_j`-exponent equals `d`; this is the coefficient
of `a_j^d` regarded as a Laurent polynomial in the remaining variables (Algorithm 1, line 17). -/
def sliceVar {m : ℕ} (j : Fin m) (d : ℤ) (P : MLaurent m) : MLaurent m :=
  AddMonoidAlgebra.ofCoeff (P.coeff.filter (fun k => k j = d))

/-- The `n = 0` base case of Eq. (8): `P ∈ T` and `Q = 0`, i.e. `P = e^{iφ_0}`. -/
def ZeroStep {m : ℕ} (P Q : MLaurent m) : Prop :=
  ∃ φ : ℝ, P = C' (Complex.exp (Complex.I * (φ : ℂ))) ∧ Q = 0

/-- The reduced `P_j` of Algorithm 1, lines 18--19. -/
def reduceP {m : ℕ} (j : Fin m) (φ : ℝ) (P Q : MLaurent m) : MLaurent m :=
  let half : MLaurent m := C' (1 / 2)
  C' (Complex.exp (-(Complex.I * (φ : ℂ)))) * (half * (var j + varInv j)) * P -
    C' (Complex.exp (Complex.I * (φ : ℂ))) * (half * (var j - varInv j)) * Q

/-- The reduced `Q_j` of Algorithm 1, lines 18--19. -/
def reduceQ {m : ℕ} (j : Fin m) (φ : ℝ) (P Q : MLaurent m) : MLaurent m :=
  let half : MLaurent m := C' (1 / 2)
  C' (Complex.exp (Complex.I * (φ : ℂ))) * (half * (var j + varInv j)) * Q -
    C' (Complex.exp (-(Complex.I * (φ : ℂ)))) * (half * (var j - varInv j)) * P

attribute [local instance] Classical.propDecidable

/-- The M-QSP constructivity decision algorithm (Algorithm 1).
For `n = 0` it checks `ZeroStep`. For `n = k+1` it either strips two steps when
`deg P + 2 ≤ k+1`, or — when `deg P = k+1` — finds an index `j` and angle `φ`
satisfying the slice constraint `P_{a_j^{d_j}} = e^{2iφ} Q_{a_j^{d_j}}` (`d_j = deg_{a_j} P`)
and recurses on `(reduceP j φ P Q, reduceQ j φ P Q)` at `k`. Otherwise it returns `false`. -/
def mqspCDA {m : ℕ} : MLaurent m → MLaurent m → ℕ → Bool
  | P, Q, 0 => if ZeroStep P Q then true else false
  | P, Q, k + 1 =>
      if degTotal P + 2 ≤ k + 1 then
        mqspCDA P Q (k + 1 - 2)
      else if degTotal P = k + 1 then
        if h : ∃ j : Fin m, ∃ φ : ℝ,
            sliceVar j (degVar j P) P = C' (Complex.exp (2 * Complex.I * (φ : ℂ))) *
              sliceVar j (degVar j P) Q then
          let j : Fin m := Classical.choose h
          let φ : ℝ := Classical.choose (Classical.choose_spec h)
          mqspCDA (reduceP j φ P Q) (reduceQ j φ P Q) k
        else false
      else false
termination_by P Q n => n

end Qatlib.Papers.QSPIto26.MainResults.Core

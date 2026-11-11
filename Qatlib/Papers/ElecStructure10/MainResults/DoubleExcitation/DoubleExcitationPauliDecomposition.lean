/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra.PauliOperators

set_option backward.isDefEq.respectTransparency false

/-!
# ElecStructure10.MainResults.DoubleExcitation — Eq. (21): Pauli decomposition of
the double-excitation operator

Source: Whitfield, Biamonte, Aspuru-Guzik, fixed arXiv:1001.3855v3, Eqs. (18)–(21)
(p. 13–14, `assets/1001.3855.txt` lines 860–905).  For four distinct spin orbitals
`p < q < r < s` the paper defines

```
h^(1) = h_pqrs δ_{σp σs} δ_{σq σr} − h_qprs δ_{σp σr} δ_{σq σs}    (18)
h^(2) = h_psqr δ_{σp σr} δ_{σq σs} − h_spqr δ_{σp σq} δ_{σr σs}    (19)
h^(3) = h_prsq δ_{σp σq} δ_{σr σs} − h_prqs δ_{σp σs} δ_{σq σr}    (20)
```

and states

```
(1/2) ∑_{pqrs} h_pqrs (a†p a†q a_r a_s + a†s a†r a_q a_p)
  = (1/8) (⊗_{k=p+1}^{q-1} ⊗_{k=r+1}^{s-1} σ_k^z) ·
      [ (σx_p σx_q σx_r σx_s + σy_p σy_q σy_r σy_s)(−h^(1) − h^(2) + h^(3))
      + (σx_p σx_q σy_r σy_s + σy_p σy_q σx_r σx_s)(+h^(1) − h^(2) + h^(3))
      + (σy_p σx_q σy_r σx_s + σx_p σy_q σx_r σy_s)(−h^(1) − h^(2) − h^(3))
      + (σy_p σx_q σx_r σy_s + σx_p σy_q σy_r σx_s)(−h^(1) + h^(2) + h^(3)) ]   (21)
```

The left sum runs over the orderings of the four distinct orbitals `{p,q,r,s}`
(“all sets of operators corresponding to a set of four distinct spin-orbitals
are simulated using the same circuit”); we formalize it as the sum over all
`π : Equiv.Perm (Fin 4)` of the ordered quadruple `π • (p,q,r,s)`.  The middle
`Z`-string is `zString` over `{p+1,…,q−1} ∪ {r+1,…,s−1}` and the four-body Pauli
strings are products of the per-site `xOp`/`yOp` from `PauliAlgebra`.

* This file fixes the paper's objects for Eq. (21) (spin delta, coefficient
  family `h^(1..3)`, `orbitSum`, `pauliBracket`).  The coefficient identity
  itself is the open formalization gap documented below; it is deliberately
  **not** introduced as a theorem, and the file contains no unproved
  declaration.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra
open scoped BigOperators

namespace Qatlib.Papers.ElecStructure10.MainResults.DoubleExcitation

variable {n : ℕ}

/-- Spin delta `δ_{σ_a σ_b}` of Eqs. (18)–(20): `1` if orbitals `a,b` have the
same spin label, `0` otherwise. -/
def spinDelta (σ : Fin n → Bool) (a b : Fin n) : ℂ :=
  if σ a = σ b then 1 else 0

/-- Coefficient `h^(1)` of Eq. (18). -/
def hOne (h : Fin n → Fin n → Fin n → Fin n → ℂ) (σ : Fin n → Bool) (p q r s : Fin n) : ℂ :=
  h p q r s * spinDelta σ p s * spinDelta σ q r
    - h q p r s * spinDelta σ p r * spinDelta σ q s

/-- Coefficient `h^(2)` of Eq. (19). -/
def hTwo (h : Fin n → Fin n → Fin n → Fin n → ℂ) (σ : Fin n → Bool) (p q r s : Fin n) : ℂ :=
  h p s q r * spinDelta σ p r * spinDelta σ q s
    - h s p q r * spinDelta σ p q * spinDelta σ r s

/-- Coefficient `h^(3)` of Eq. (20). -/
def hThree (h : Fin n → Fin n → Fin n → Fin n → ℂ) (σ : Fin n → Bool) (p q r s : Fin n) : ℂ :=
  h p r s q * spinDelta σ p q * spinDelta σ r s
    - h p r q s * spinDelta σ p s * spinDelta σ q r

/-- Middle `Z`-string index set of Eq. (21): `{p+1,…,q−1} ∪ {r+1,…,s−1}`. -/
def midIndex {n : ℕ} (p q r s : Fin n) : Finset (Fin n) :=
  Finset.Ioo p q ∪ Finset.Ioo r s

/-- The ordered quadruple `(p,q,r,s)` as a `Fin 4`-indexed family. -/
def quartet {n : ℕ} (p q r s : Fin n) : Fin 4 → Fin n := ![p, q, r, s]

/-- Left-hand side of Eq. (21): `(1/2) ∑_{orderings π} h_{π•(pqrs)}
(a†_{π0} a†_{π1} a_{π2} a_{π3})`, i.e. the paper's `(1/2)∑_{pqrs} h_pqrs (… + h.c.)`
restricted to the orbit of `{p,q,r,s}` (the `+ h.c.` is one of the permuted
terms). -/
def orbitSum (h : Fin n → Fin n → Fin n → Fin n → ℂ) (p q r s : Fin n) :
    Matrix (Reg n) (Reg n) ℂ :=
  let v := quartet p q r s
  (1 / 2 : ℂ) • ∑ π : Equiv.Perm (Fin 4),
    (h (v (π 0)) (v (π 1)) (v (π 2)) (v (π 3))) •
      (creation (v (π 0)) * creation (v (π 1)) *
        annihilation (v (π 2)) * annihilation (v (π 3)))

/-- The eight-term `σx/σy` four-body bracket of Eq. (21). -/
def pauliBracket (p q r s : Fin n) (h1 h2 h3 : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  ((-h1 - h2 + h3) •
      (xOp p * xOp q * xOp r * xOp s + yOp p * yOp q * yOp r * yOp s))
  + ((h1 - h2 + h3) •
      (xOp p * xOp q * yOp r * yOp s + yOp p * yOp q * xOp r * xOp s))
  + ((-h1 - h2 - h3) •
      (yOp p * xOp q * yOp r * xOp s + xOp p * yOp q * xOp r * yOp s))
  + ((-h1 + h2 + h3) •
      (yOp p * xOp q * xOp r * yOp s + xOp p * yOp q * yOp r * xOp s))

/-!
### Open gap for Eq. (21)

**Fixed source version:** arXiv:1001.3855v3 (2010-12-19), Eq. (21) on p. 14
(text lines 895–905 of `assets/1001.3855.txt`), coefficients Eqs. (18)–(20) on
p. 13 (lines 865–870).

**Paper proof steps.** (i) Jordan–Wigner `a_i = (∏_{j<i} σ^z_j) σ^-_i`,
`a†_i = (∏_{j<i} σ^z_j) σ^+_i` (Eqs. (5a)/(5b)).  (ii) Multiply
`a†_p a†_q a_r a_s` and commute the `σ^z` prefix strings past the `σ^±` at the
four sites; the surviving `Z`-string is only over the “inside” gaps
`p+1..q−1` and `r+1..s−1`, and the four sites carry `σ^±, σ^±, σ^∓, σ^∓`.
(iii) Add the Hermitian conjugate `a†_s a†_r a_q a_p` and use
`σ^± = (σ^x ± i σ^y)/2` to expand the product of four `σ^±` into the eight
`σ^x/σ^y` four-body strings, with the relative signs fixed by the
`σ^+`/`σ^-` choices and collected into `h^(1), h^(2), h^(3)` via Eqs. (18)–(20).
(iv) The `1/8` comes from `(1/2)^3` in the four `σ^±` expansions times the `1/2`
of the Hamiltonian term.

**Current Lean gap.**  The objects above are formalized faithfully (frozen
`creation`/`annihilation`, the `24`-ordering sum, the middle `zString`, the
exact eight-term `pauliBracket`, and `h^(1..3)` from Eqs. (18)–(20)).  What is
missing is the proof of the coefficient identity; it is documented in the
`Status of Eq. (21)` section below and is **not** declared as a Lean theorem.
Doing it requires
(1) the frozen Jordan–Wigner isomorphism `(g1 n).2.2.2.2.1 : annihilation i = jwPauliWord i`
and its conjugate-transpose form for `creation`, (2) a normal form for products
of `σ^z`/`σ^±` at a site (`σ^z σ^+ = σ^+`, `σ^+ σ^z = -σ^+`, `σ^z σ^- = -σ^-`,
`σ^- σ^z = σ^-`), and (3) a case analysis on the four bits `x_p x_q x_r x_s`,
where both sides are non-zero only for the two patterns `0011 ↦ 1100` and
`1100 ↦ 0011` with the middle `Z`-string contributing the sign.

**Candidate reusable dependencies.** `Fermion.Fermion.g1` (JW isomorphism,
adjoint, CAR); `PauliAlgebra.xOp`/`yOp`/`zOp`/`zString` (this paper);
`GateVocabulary.GateVocab` (`pauli_multiplication`, `tensorPauliProduct`) for the
Pauli-word algebra.

**Suggested tactics.** Reduce to `Matrix.ext y x`; split with
`by_cases y = Function.update (Function.update (Function.update (Function.update x p _) q _) r _) s _`;
in the non-vanishing case unfold `creation`/`annihilation` and `jwSign`, use
`simp [xOp_apply, yOp_apply, zString_apply]` plus `Complex.I_mul_I`, and finish
with `field_simp; ring`.  A cleaner route is to build 4-site Pauli-product lemmas
over `Fin 4` first (as in `GateVocab`) and transport along `quartet`.
-/

/-! ## Status of Eq. (21)

The target identity (fixed arXiv:1001.3855v3,
p. 14) would state, for four distinct spin orbitals `p < q < r < s`,
`orbitSum h p q r s = (1/8) • (zString (midIndex p q r s) *
pauliBracket p q r s (hOne h σ p q r s) (hTwo h σ p q r s) (hThree h σ p q r s))`.
This equality is an open formalization gap and is therefore **not** declared as
a Lean theorem here: the available arguments cover only the entry-wise
Jordan–Wigner structure, not the full `24`-term coefficient identity.  Note in
particular that the unrestricted form is *false* for an arbitrary integral
family `h`; it is true only under the molecular-integral symmetries of the
paper's Eq. (4) (electron exchange `h a b c d = h b a d c`, reversal
`h a b c d = h d c b a`, and the spin-selection rule `σ a = σ d`,
`σ b = σ c`).  Asserting it without those hypotheses would be unsound, so no
such declaration appears in this file. -/

end Qatlib.Papers.ElecStructure10.MainResults.DoubleExcitation

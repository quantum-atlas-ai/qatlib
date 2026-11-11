/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# QAOADepthCut22 -- the `B`-message objects of Appendix A

This module fixes, faithfully to *The Quantum Approximate Optimization Algorithm
at High Depth for MaxCut on Large-Girth Regular Graphs and the Sherrington-Kirkpatrick
Model* (Basso, Farhi, Marwaha, Villalonga, Zhou; arXiv:2110.14206v3, TQC 2022),
the (2p+1)-bit string model and the message function `f` used throughout the paper.

Source anchors (arXiv:2110.14206v3):

* Eq. (A.1) -- the set `B` of `(2p+1)`-bit strings `(a_1,…,a_p,a_0,a_{-p},…,a_{-1})`.
* Eq. (A.2) -- the subset `B_0 = {a ∈ B : a_{-r}=a_r}`.
* Eq. (A.3) -- the level index `T(a)`.
* Eq. (A.4) -- the prime operation `a ↦ a'`.
* Eq. (A.5) -- the reversal `a ↦ ä`, `ä_j = a_{-j}`.
* Eqs. (3.3)-(3.5), (A.6)-(A.8) -- the message `f(a)` and the single-qubit matrix
  element `⟨s|e^{iθX}|t⟩`.

## Representation

We index a string `a` by *position* `0,…,2p`:

* position `r-1` for `1 ≤ r ≤ p` is `a_r`,
* position `p` is `a_0`,
* position `2p+1-r` for `1 ≤ r ≤ p` is `a_{-r}`.

With this convention the compare-pair of Eq. (A.2) for index `r` is the pair of
positions `(r-1, 2p+1-r)`, i.e. `(r.val, 2p - r.val)` for `r : Fin p`. The prime
operation flips precisely the positions whose magnitude-index is `≤ T(a)`; that
condition is stated by `flips` below (equivalent to Eq. (A.4) because `T(a) ≤ p`).
-/

namespace Qatlib.Papers.QAOADepthCut22.MainResults.Definitions

open scoped BigOperators

set_option autoImplicit false

/-- The `(2p+1)`-bit strings `B` of Eq. (A.1), indexed by position `0,…,2p`
(see the module docstring for the position/index dictionary). -/
abbrev Bits (p : ℕ) := Fin (2 * p + 1) → Bool

/-- The subset `B_0` of Eq. (A.2): `a_{-r} = a_r` for every `1 ≤ r ≤ p`.  In
position coordinates the pair for `r : Fin p` is `(r.val, 2*p - r.val)`. -/
abbrev InB0 {p : ℕ} (a : Bits p) : Prop :=
  ∀ r : Fin p, a ⟨r.val, by omega⟩ = a ⟨2 * p - r.val, by omega⟩

/-- The level index `T(a)` of Eq. (A.3): the largest index `r` at which
`a_r ≠ a_{-r}`, or `0` when `a ∈ B_0`.  It is written as a supremum over the
(default-`0`) contributions `r.val + 1` at mismatched pairs. -/
noncomputable def T {p : ℕ} (a : Bits p) : ℕ :=
  (Finset.univ : Finset (Fin p)).sup
    (fun r => if a ⟨r.val, by omega⟩ ≠ a ⟨2 * p - r.val, by omega⟩ then r.val + 1 else 0)

/-- The predicate "position `i` is flipped by the prime operation".  Position `i`
carries magnitude-index `i.val + 1` when `i.val < p` and `2*p+1 - i.val` when
`i.val > p`; the center `i.val = p` is never flipped.  This is exactly the
condition of Eq. (A.4) (the two clauses below already exclude the wrong side
because `T ≤ p`). -/
def flips {p : ℕ} (T : ℕ) (i : Fin (2 * p + 1)) : Bool :=
  decide (i.val < T) || decide (2 * p + 1 - T ≤ i.val)

/-- The prime operation `a ↦ a'` of Eq. (A.4): flip every `a_{±r}` with
`1 ≤ r ≤ T(a)`, leave `a_0` fixed. -/
noncomputable def prime {p : ℕ} (a : Bits p) : Bits p :=
  fun i => if (flips (T a) i) = true then (a i == false) else a i

/-- The reversal `a ↦ ä` of Eq. (A.5), `ä_j = a_{-j}`.  In position coordinates
this is the reflection `i ↦ 2p - i`. -/
def rev {p : ℕ} (a : Bits p) : Bits p :=
  fun i => a ⟨2 * p - i.val, by omega⟩

/-- The `(2p+1)`-component vector `Γ` of Eq. (3.3): `Γ_r = γ_r`, `Γ_0 = 0`,
`Γ_{-r} = -γ_r`, indexed by position. -/
noncomputable def Gamma {p : ℕ} (γ : Fin p → ℝ) (i : Fin (2 * p + 1)) : ℝ :=
  if h : i.val < p then γ ⟨i.val, h⟩
  else if h2 : i.val = p then 0
  else -γ ⟨2 * p - i.val, by omega⟩

/-- The edge angle `θ_i` of the message product.  Edge `i : Fin (2p)` joins
positions `i` and `i+1`.  Positive edges (`i < p`, i.e. `a_{i+1}→a_{i+2}` and
`a_p→a_0`) carry `β_{i+1}`; negative edges (`i ≥ p`) carry `-β_{2p-i}` -- this
is the sign pattern of Eq. (A.6)/(3.4). -/
noncomputable def edgeAngle {p : ℕ} (β : Fin p → ℝ) (i : Fin (2 * p)) : ℝ :=
  if h : i.val < p then β ⟨i.val, h⟩
  else -β ⟨2 * p - 1 - i.val, by omega⟩

/-- The single-qubit matrix element `⟨s|e^{iθX}|t⟩` of Eq. (A.8): `cos θ` when the
two bits agree and `i sin θ` when they differ.  (Equivalently `q θ s t` is the
`(s,t)` entry of `e^{iθX}` in the `X`-eigenbasis.) -/
noncomputable def q (θ : ℝ) (s t : Bool) : ℂ :=
  if s = t then (Real.cos θ : ℂ) else Complex.I * (Real.sin θ : ℂ)

/-- The message `f(a)` of Eq. (A.6)/(3.4): half the product of the `2p` edge
matrix elements along the path `a_1,…,a_p,a_0,a_{-p},…,a_{-1}`. -/
noncomputable def f {p : ℕ} (β : Fin p → ℝ) (a : Bits p) : ℂ :=
  (1 / 2 : ℂ) * ∏ i : Fin (2 * p), q (edgeAngle β i) (a i.castSucc) (a i.succ)

/-- The sign product `a_j b_j` of two bits (both in `{+1,-1}`), as a real number:
`+1` when equal, `-1` when different. -/
def sgn (s t : Bool) : ℝ := if s = t then 1 else -1

/-- The spin-spin form `Γ · (ab) = ∑_j Γ_j a_j b_j` appearing in Eqs. (3.7),(3.8). -/
noncomputable def dot {p : ℕ} (Γ : Fin (2 * p + 1) → ℝ) (a b : Bits p) : ℝ :=
  ∑ i, Γ i * sgn (a i) (b i)

/-- The finite-`D` message `H_D^{(m)}(a)` of Eqs. (3.6)-(3.7):
`H_D^{(0)} = 1` and
`H_D^{(m)}(a) = (∑_b f(b) H_D^{(m-1)}(b) cos(Γ·(ab)/√D))^D`. -/
noncomputable def HD {p : ℕ} (β γ : Fin p → ℝ) (D : ℕ) (m : ℕ) : Bits p → ℂ :=
  Nat.rec (motive := fun _ => Bits p → ℂ)
    (fun _ => 1)
    (fun _ IH => fun a =>
      (∑ b : Bits p,
          f β b * IH b * (Real.cos (dot (Gamma γ) a b / Real.sqrt (D : ℝ)) : ℂ)) ^ D)
    m

/-- The matrix `G^{(m)}` of the `D → ∞` iteration, Eqs. (3.9)-(3.10). -/
noncomputable def G {p : ℕ} (β γ : Fin p → ℝ) (m : ℕ) :
    Fin (2 * p + 1) → Fin (2 * p + 1) → ℂ :=
  Nat.rec (motive := fun _ => Fin (2 * p + 1) → Fin (2 * p + 1) → ℂ)
    (fun j k => ∑ a : Bits p, f β a * (sgn (a j) (a k) : ℂ))
    (fun _ IH => fun j k =>
      ∑ a : Bits p, f β a * (sgn (a j) (a k) : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) *
          ∑ j' : Fin (2 * p + 1), ∑ k' : Fin (2 * p + 1),
            IH j' k' * (Gamma γ j' : ℂ) * (Gamma γ k' : ℂ) * (sgn (a j') (a k') : ℂ)))
    m

/-- The `D → ∞` iteration value `ν_p(γ,β)` of Eq. (3.11). -/
noncomputable def nuPInf {p : ℕ} (β γ : Fin p → ℝ) : ℂ :=
  (Complex.I / 2) *
    ∑ j : Fin (2 * p + 1), (Gamma γ j : ℂ) * (G β γ p ⟨p, by omega⟩ j) ^ 2

/-- The finite-`D` value `ν_p(D,γ,β)` of Eq. (3.8). -/
noncomputable def nuPF {p : ℕ} (β γ : Fin p → ℝ) (D : ℕ) : ℂ :=
  Complex.I * (Real.sqrt (2 * D) : ℂ) *
    ∑ a : Bits p, ∑ b : Bits p,
      (sgn (a ⟨p, by omega⟩) (b ⟨p, by omega⟩) : ℂ) * f β a * f β b *
        HD β γ D p a * HD β γ D p b *
        (Real.sin (dot (Gamma γ) a b / Real.sqrt (D : ℝ)) : ℂ)

end Qatlib.Papers.QAOADepthCut22.MainResults.Definitions

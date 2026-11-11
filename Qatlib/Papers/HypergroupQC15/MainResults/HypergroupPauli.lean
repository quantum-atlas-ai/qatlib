/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypergroupQC15.MainResults.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# HypergroupQC15 — Lemma 1 (Commutativity of hypergroup Pauli operators)

Fixed source: arXiv:1509.05806, §5.1, eq. (18) and Lemma 1, p.18.

The hypergroup Pauli operators over a finite abelian hypergroup `T` with weights
`w`, structure constants `n` and normalized characters `χ` act on the basis `B_T` by

```
Z_T(χ) |x⟩ = χ(x) |x⟩ ,
X_T(a) |y⟩ = Σ_z √(w_y / w_z) n^z_{a,y} |z⟩ .
```

Lemma 1: for `a ∈ T` and a character `χ_μ`, the operators `X_T(a)` and `Z_T(χ_μ)`
commute if and only if `χ_μ(a) = 1`.

The Lean statement below uses exactly the coefficient from (18) and the hypergroup
character identity on the support of the hyperoperation (`c ∈ a·b ⇒ χ(c) = χ(a)χ(b)`,
the property quoted from [82, Prop. 2.4.15] in the paper's proof).  The proof is the
paper's: compare both actions on a basis vector, use multiplicativity of `χ` on `a·b`
for the "if" direction, and evaluate on the identity basis vector in the "only if"
direction (the paper lets `b = e`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HypergroupQC15.MainResults

open scoped BigOperators

/-- Data underlying the hypergroup Pauli operators (18): weights, structure constants,
and normalized characters satisfying the hypergroup multiplicativity identity on the
support of the hyperoperation. -/
structure HypergroupPauliData (T : Type) [Fintype T] [DecidableEq T] where
  /-- identity element of the hypergroup -/
  e : T
  /-- weights `w_x` of the basis elements -/
  w : T → ℝ
  wpos : ∀ x, 0 < w x
  /-- normalized structure constants `n^c_{a,b}` -/
  n : T → T → T → ℝ
  /-- normalized characters -/
  chi : T → ℂˣ
  chi_e : (chi e : ℂ) = 1
  /-- Characters are multiplicative on the hyperoperation support: if `c ∈ a·b`
      (i.e. `n^c_{a,b} ≠ 0`) then `χ(c) = χ(a) χ(b)` (https://arxiv.org/abs/1509.05806,
      proof of Lemma 1 citing [82, Prop. 2.4.15]). -/
  chi_mul_support : ∀ a b c, n a b c ≠ 0 → (chi c : ℂ) = (chi a : ℂ) * (chi b : ℂ)
  /-- The hypergroup identity returns the element: `a ∈ a·e`, so `n^a_{a,e} ≠ 0`. -/
  n_e : ∀ a, n a e a ≠ 0

/-- `X_T(a)`: the `X`-type hypergroup Pauli operator, eq. (18). -/
def Xop {T : Type} [Fintype T] [DecidableEq T] (D : HypergroupPauliData T) (a : T)
    (φ : T → ℂ) : T → ℂ :=
  fun c => ∑ b, ((Real.sqrt (D.w b / D.w c) : ℂ) * (D.n a b c : ℂ)) * φ b

/-- `Z_T(χ)`: the `Z`-type hypergroup Pauli operator, eq. (18). -/
def Zop {T : Type} [Fintype T] [DecidableEq T] (D : HypergroupPauliData T)
    (φ : T → ℂ) : T → ℂ :=
  fun x => (D.chi x : ℂ) * φ x

/-- Lemma 1 (arXiv:1509.05806, Lemma 1, p.18).  The hypergroup Pauli operators
`X_T(a)` and `Z_T(χ)` commute on every state if and only if `χ(a) = 1`.

Proof (paper): on the basis vector `|b⟩`,
`Z X |b⟩ = Σ_c √(w_b/w_c) n^c_{a,b} χ(c) |c⟩` while
`X Z |b⟩ = Σ_c √(w_b/w_c) n^c_{a,b} χ(b) |c⟩`.
If `χ(a) = 1`, then `χ(c) = χ(a)χ(b) = χ(b)` for every `c ∈ a·b`; conversely taking
`b = e` forces `χ(a) = 1`. -/
theorem lemma1_pauli_commute_iff {T : Type} [Fintype T] [DecidableEq T]
    (D : HypergroupPauliData T) (a : T) :
    (∀ φ : T → ℂ, Xop D a (Zop D φ) = Zop D (Xop D a φ)) ↔ (D.chi a : ℂ) = 1 := by
  constructor
  · intro h
    let φ : T → ℂ := fun b => if b = D.e then 1 else 0
    have heq := congrFun (h φ) a
    have hL : Xop D a (Zop D φ) a
        = ((Real.sqrt (D.w D.e / D.w a) : ℂ) * (D.n a D.e a : ℂ)) := by
      unfold Xop Zop
      rw [Finset.sum_eq_single D.e]
      · simp [φ, D.chi_e]
      · intro b _ hb
        simp [φ, hb]
      · intro hmem
        exact absurd (Finset.mem_univ D.e) hmem
    have hR : Zop D (Xop D a φ) a
        = (D.chi a : ℂ) * ((Real.sqrt (D.w D.e / D.w a) : ℂ) * (D.n a D.e a : ℂ)) := by
      unfold Zop Xop
      rw [Finset.sum_eq_single D.e]
      · simp [φ]
      · intro b _ hb
        simp [φ, hb]
      · intro hmem
        exact absurd (Finset.mem_univ D.e) hmem
    rw [hL, hR] at heq
    have hcoeff : ((Real.sqrt (D.w D.e / D.w a) : ℂ) * (D.n a D.e a : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · have hpos : (0 : ℝ) < D.w D.e / D.w a := div_pos (D.wpos D.e) (D.wpos a)
        exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hpos))
      · exact_mod_cast (D.n_e a)
    have h2 : (D.chi a : ℂ) * ((Real.sqrt (D.w D.e / D.w a) : ℂ) * (D.n a D.e a : ℂ))
        = 1 * ((Real.sqrt (D.w D.e / D.w a) : ℂ) * (D.n a D.e a : ℂ)) := by
      rw [← heq]
      ring
    exact mul_right_cancel₀ hcoeff h2
  · intro hchi φ
    funext c
    unfold Xop Zop
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : D.n a b c = 0
    · simp [hb]
    · have hsupp := D.chi_mul_support a b c hb
      have hcb : (D.chi c : ℂ) = (D.chi b : ℂ) := by
        rw [hsupp, hchi]
        ring
      rw [hcb]
      ring

end Qatlib.Papers.HypergroupQC15.MainResults

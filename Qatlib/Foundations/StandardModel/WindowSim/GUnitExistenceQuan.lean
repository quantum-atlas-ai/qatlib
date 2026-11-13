/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Foundations.StandardModel.WindowSim.GUnitExistenceStat

/-!
# Existence of a unitary QTM window gate

This module proves `gUnitExistence` by constructing a unitary exchange between the orthonormal
families of head basis vectors and local transition superpositions. The construction fixes their
common orthogonal complement, and the window orthogonality lemmas show that the required fixed
families lie in that complement. This establishes the unitary existence statement for the
three-cell G gate in [Yao1993].

## Main statements

* `exists_swap`: construct a unitary exchanging two mutually orthogonal orthonormal families.
* `ip_superp_self` and `ip_superp_ne`: transition superpositions form an orthonormal family.
* `gUnitExistence`: obtain a unitary satisfying the fixed-family and local-step conditions.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.StandardDefs.WindowSim
open Matrix

/-- Replace nested sums over states and symbols by a single sum over their product type. -/
private theorem sum_pair {Q A : Type*} [Fintype Q] [Fintype A] (g : Q → A → ℂ) :
    (∑ q' : Q, ∑ a' : A, g q' a') = ∑ s : Q × A, g s.1 s.2 :=
  (Fintype.sum_prod_type (fun s : Q × A => g s.1 s.2)).symm

/-- A sum over QTM moves is the sum of the left, stay, and right contributions. -/
private theorem sum_move (F : QtmMove → ℂ) :
    ∑ d : QtmMove, F d = F QtmMove.left + F QtmMove.stay + F QtmMove.right := by
  have h : (Finset.univ : Finset QtmMove) = {QtmMove.left, QtmMove.stay, QtmMove.right} := by
    decide
  rw [h]
  simp [Finset.sum_insert]
  ring

/-- Combine three directional sums over state-symbol pairs into a nested sum over states,
symbols, and moves. -/
private theorem sum_three_dir {Q A : Type*} [Fintype Q] [Fintype A]
    (F : QtmMove → Q → A → ℂ) :
    (∑ s : Q × A, F QtmMove.left s.1 s.2) + ((∑ s : Q × A, F QtmMove.stay s.1 s.2)
        + ∑ s : Q × A, F QtmMove.right s.1 s.2)
      = ∑ q' : Q, ∑ a' : A, ∑ d : QtmMove, F d q' a' := by
  have last : ∑ q' : Q, ∑ a' : A,
      (F QtmMove.left q' a' + (F QtmMove.stay q' a' + F QtmMove.right q' a'))
      = ∑ q' : Q, ∑ a' : A, ∑ d : QtmMove, F d q' a' := by
    refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [sum_move]
    ring
  rw [← sum_pair (fun q' a' => F QtmMove.left q' a'),
    ← sum_pair (fun q' a' => F QtmMove.stay q' a'),
    ← sum_pair (fun q' a' => F QtmMove.right q' a'),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun q' _ => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib])]
  exact last

/-- For a complex number, its conjugate times itself equals its squared norm embedded in the
complex numbers. -/
private theorem star_mul_self_real (x : ℂ) : star x * x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ((Complex.normSq x : ℝ) : ℂ) = star x * x := by
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  rw [← h1, ← Complex.normSq_eq_norm_sq]

/-- If the sum of `f r * star (g r)` is zero, the sum with the conjugation on `f r` is also
zero. -/
private theorem star_sum_eq {ι : Type*} [Fintype ι] (f g : ι → ℂ)
    (h : ∑ r, f r * star (g r) = 0) : ∑ r, star (f r) * g r = 0 := by
  calc ∑ r, star (f r) * g r = ∑ r, star (f r * star (g r)) :=
        Finset.sum_congr rfl fun r _ => by rw [star_mul, star_star, mul_comm]
    _ = star (∑ r, f r * star (g r)) := (star_sum _ _).symm
    _ = 0 := by rw [h]; simp

section Windows
variable {Q A : Type*}

/-- The three-cell window with prescribed entries at positions zero, one, and two. -/
private def win3 (x₀ x₁ x₂ : CellState Q A) : GWindow Q A :=
  fun j => if j = 0 then x₀ else if j = 1 then x₁ else x₂

/-- The entry of `win3 x₀ x₁ x₂` at zero is `x₀`. -/
@[simp] private theorem win3_zero (x₀ x₁ x₂ : CellState Q A) :
    win3 x₀ x₁ x₂ 0 = x₀ := by simp [win3]

/-- The entry of `win3 x₀ x₁ x₂` at one is `x₁`. -/
@[simp] private theorem win3_one (x₀ x₁ x₂ : CellState Q A) :
    win3 x₀ x₁ x₂ 1 = x₁ := by simp [win3]

/-- The entry of `win3 x₀ x₁ x₂` at two is `x₂`. -/
@[simp] private theorem win3_two (x₀ x₁ x₂ : CellState Q A) :
    win3 x₀ x₁ x₂ 2 = x₂ := by simp [win3]

/-- A window equals a prescribed three-cell window exactly when its three entries agree. -/
private theorem win3_eq_iff (z : GWindow Q A) (x₀ x₁ x₂ : CellState Q A) :
    z = win3 x₀ x₁ x₂ ↔ (z 0 = x₀ ∧ z 1 = x₁ ∧ z 2 = x₂) := by
  constructor
  · intro h; rw [h]; simp [win3]
  · rintro ⟨h0, h1, h2⟩
    funext j
    have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases hj with hj | hj | hj
    · have hJ : j = 0 := by ext; simp [hj]
      rw [hJ]; simpa [win3] using h0
    · have hJ : j = 1 := by ext; simp [hj]
      rw [hJ]; simpa [win3] using h1
    · have hJ : j = 2 := by ext; simp [hj]
      rw [hJ]; simpa [win3] using h2

/-- Two prescribed three-cell windows are equal exactly when their corresponding cell states
agree. -/
private theorem win3_inj (x₀ x₁ x₂ y₀ y₁ y₂ : CellState Q A) :
    win3 x₀ x₁ x₂ = win3 y₀ y₁ y₂ ↔ (x₀ = y₀ ∧ x₁ = y₁ ∧ x₂ = y₂) := by
  constructor
  · intro h
    have e0 : win3 x₀ x₁ x₂ 0 = win3 y₀ y₁ y₂ 0 := by rw [h]
    have e1 : win3 x₀ x₁ x₂ 1 = win3 y₀ y₁ y₂ 1 := by rw [h]
    have e2 : win3 x₀ x₁ x₂ 2 = win3 y₀ y₁ y₂ 2 := by rw [h]
    simpa using ⟨e0, e1, e2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

end Windows

section InnerFacts
variable {X : Type*} [Fintype X]

/-- The finite complex inner product, conjugating the first amplitude vector. -/
private def ip (x y : QState X) : ℂ := ∑ i, star (x i) * y i

/-- Swapping the arguments of `ip` conjugates its value. -/
private theorem ip_star_swap (x y : QState X) : ip x y = star (ip y x) := by
  simp only [ip, star_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [star_mul, star_star]

/-- The inner product is additive in its first argument. -/
private theorem ip_add_left (x y z : QState X) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

/-- The inner product is additive in its second argument. -/
private theorem ip_add_right (x y z : QState X) : ip x (y + z) = ip x y + ip x z := by
  simp only [ip, Pi.add_apply, Finset.sum_add_distrib, mul_add]

/-- A finite sum in the second argument of `ip` can be taken outside the inner product. -/
private theorem ip_sum_right {ι : Type*} [Fintype ι] (f : ι → QState X) (x : QState X) :
    ip x (∑ i, f i) = ∑ i, ip x (f i) := by
  simp only [ip, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

end InnerFacts

section PartVec
variable {X : Type*} [Fintype X] [DecidableEq X] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The amplitude vector formed by summing coefficients `c p` at the basis indices `W p`,
including repeated indices. -/
private def partVec (W : ι → X) (c : ι → ℂ) : QState X :=
  fun z => ∑ p, c p * (if z = W p then (1 : ℂ) else 0)

omit [Fintype X] in

/-- A complex zero-one equality indicator is fixed by conjugation. -/
private theorem star_ind (z w : X) :
    star ((if z = w then (1 : ℂ) else 0)) = if z = w then 1 else 0 := by
  split_ifs <;> simp

/-- The sum of products of two basis indicators is one when their basis indices agree and zero
otherwise. -/
private theorem sum_ind_ind (w w' : X) :
    ∑ z : X, (if z = w then (1 : ℂ) else 0) * (if z = w' then 1 else 0)
      = if w = w' then 1 else 0 := by
  by_cases hw : w = w'
  · subst hw
    have e : ∀ z : X, (if z = w then (1 : ℂ) else 0) * (if z = w then 1 else 0)
        = if z = w then 1 else 0 := by
      intro z; split_ifs <;> simp
    simp only [e]
    simp
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z = w
    · rw [if_pos hz, if_neg (fun hzz => hw (hz.symm.trans hzz))]
      ring
    · rw [if_neg hz]
      ring

/-- Expand the inner product of two `partVec` vectors as a double sum of conjugated coefficients
weighted by equality of basis indices. -/
private theorem ip_bilin (W : ι → X) (g : ι → ℂ) (W' : κ → X) (h : κ → ℂ) :
    ip (partVec W g) (partVec W' h)
      = ∑ s, ∑ t, star (g s) * h t * (if W s = W' t then (1 : ℂ) else 0) := by
  have hstep : ∀ z : X,
      star (∑ s, g s * (if z = W s then (1 : ℂ) else 0))
          * (∑ t, h t * (if z = W' t then 1 else 0))
      = ∑ s, ∑ t, star (g s) * h t
          * ((if z = W s then 1 else 0) * (if z = W' t then 1 else 0)) := by
    intro z
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [star_mul, star_ind]
    ring
  show (∑ z : X, star (∑ s, g s * (if z = W s then (1 : ℂ) else 0))
      * (∑ t, h t * (if z = W' t then 1 else 0)))
    = ∑ s, ∑ t, star (g s) * h t * (if W s = W' t then (1 : ℂ) else 0)
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => by
    rw [← Finset.mul_sum, sum_ind_ind (W s) (W' t)]

/-- The inner product of a basis vector with `partVec W c` sums the coefficients whose basis
index equals that vector's index. -/
private theorem ip_ket_parts (z : X) (W : ι → X) (c : ι → ℂ) :
    ip (Qatlib.Foundations.PureStateMath.Ket z) (partVec W c) = ∑ p, c p * (if z = W p then (1 : ℂ) else 0) := by
  have hstep : ∀ p : ι, ∑ y : X,
      star ((if y = z then (1 : ℂ) else 0)) * (c p * (if y = W p then 1 else 0))
      = c p * (if z = W p then 1 else 0) := by
    intro p
    have h1 : ∑ y : X, star ((if y = z then (1 : ℂ) else 0))
        * (c p * (if y = W p then 1 else 0))
        = star ((if z = z then (1 : ℂ) else 0)) * (c p * (if z = W p then 1 else 0)) :=
      Finset.sum_eq_single z
        (fun y _ hy => by rw [if_neg hy, star_zero]; ring)
        (fun hne => absurd (Finset.mem_univ z) hne)
    rw [h1, if_pos rfl, star_one, one_mul]
  show (∑ y : X, star ((if y = z then (1 : ℂ) else 0))
      * ∑ p, c p * (if y = W p then 1 else 0)) = ∑ p, c p * (if z = W p then 1 else 0)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => hstep p

/-- The inner product of `partVec W c` with a basis vector sums the conjugated coefficients at
its index. -/
private theorem ip_parts_ket (W : ι → X) (c : ι → ℂ) (z : X) :
    ip (partVec W c) (Qatlib.Foundations.PureStateMath.Ket z) = ∑ p, star (c p) * (if z = W p then (1 : ℂ) else 0) := by
  have hstep : ∀ p : ι, ∑ y : X,
      star (c p * (if y = W p then (1 : ℂ) else 0)) * (if y = z then 1 else 0)
      = star (c p) * (if z = W p then 1 else 0) := by
    intro p
    have h1 : ∑ y : X, star (c p * (if y = W p then (1 : ℂ) else 0))
        * (if y = z then 1 else 0)
        = star (c p * (if z = W p then (1 : ℂ) else 0)) * (if z = z then 1 else 0) :=
      Finset.sum_eq_single z
        (fun y _ hy => by rw [if_neg hy, mul_zero])
        (fun hne => absurd (Finset.mem_univ z) hne)
    rw [h1, if_pos rfl, mul_one, star_mul, star_ind, mul_comm]
  show (∑ y : X, star (∑ p, c p * (if y = W p then (1 : ℂ) else 0))
      * (if y = z then 1 else 0)) = ∑ p, star (c p) * (if z = W p then 1 else 0)
  simp only [star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => hstep p

end PartVec

section InnerRight
variable {X : Type*} [Fintype X]

/-- The inner product distributes over subtraction in its second argument. -/
private theorem ip_sub_right (x y z : QState X) : ip x (y - z) = ip x y - ip x z := by
  simp only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- A complex scalar multiplying every amplitude in the second argument factors out of `ip`. -/
private theorem ip_smul_right (x : QState X) (c : ℂ) (w : QState X) :
    ip x (fun k => w k * c) = ip x w * c := by
  calc ip x (fun k => w k * c) = ∑ k : X, star (x k) * (w k * c) := by rw [ip]
    _ = ∑ k : X, (star (x k) * w k) * c :=
        Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
    _ = (∑ k : X, star (x k) * w k) * c := (Finset.sum_mul _ _ _).symm
    _ = ip x w * c := by rw [ip]

/-- Expand the inner product against a four-term linear combination of two vectors. -/
private theorem ip_four (a w1 w2 : QState X) (c1 c2 c3 c4 : ℂ) :
    ip a (fun k => w1 k * c1 + w2 k * c2 - w2 k * c3 - w1 k * c4)
      = ip a w1 * c1 + ip a w2 * c2 - ip a w2 * c3 - ip a w1 * c4 := by
  have h1 : (fun k => w1 k * c1 + w2 k * c2 - w2 k * c3 - w1 k * c4)
      = (fun k => w1 k * c1 + w2 k * c2) - (fun k => w2 k * c3 + w1 k * c4) := by
    funext k
    simp only [Pi.sub_apply]
    ring
  rw [h1, ip_sub_right]
  show ip a ((fun k => w1 k * c1) + (fun k => w2 k * c2))
      - ip a ((fun k => w2 k * c3) + (fun k => w1 k * c4))
      = ip a w1 * c1 + ip a w2 * c2 - ip a w2 * c3 - ip a w1 * c4
  rw [ip_add_right, ip_add_right, ip_smul_right, ip_smul_right, ip_smul_right, ip_smul_right]
  ring

end InnerRight

section Swap
variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]

/-- The matrix with entries `w i * star (w' j)`, representing the outer product of two amplitude
vectors. -/
private def outer (w w' : QState X) : Matrix X X ℂ := Matrix.of fun i j => w i * star (w' j)

omit [DecidableEq X] in

/-- The outer-product matrix sends `x` to `w` multiplied by the inner product of `w'` with `x`,
evaluated at a coordinate. -/
private theorem outer_mulVec (w w' x : QState X) (k : X) :
    (outer w w' *ᵥ x) k = w k * ∑ j, star (w' j) * x j := by
  calc (outer w w' *ᵥ x) k = ∑ j : X, (w k * star (w' j)) * x j := by
        simp only [Matrix.mulVec, dotProduct, outer, Matrix.of_apply]
    _ = w k * ∑ j : X, star (w' j) * x j := by
        calc ∑ j : X, (w k * star (w' j)) * x j
            = ∑ j : X, w k * (star (w' j) * x j) :=
              Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
          _ = w k * ∑ j : X, star (w' j) * x j := (Finset.mul_sum _ _ _).symm

/-- The outer-product correction `outer v u + outer u v - outer u u - outer v v` used to
exchange vectors. -/
private def eTerm (u v : QState X) : Matrix X X ℂ :=
  outer v u + outer u v - outer u u - outer v v

/-- The identity plus the sum of the pairwise outer-product corrections `eTerm (u i) (v i)`. -/
private def swapG (u v : ι → QState X) : Matrix X X ℂ := 1 + ∑ i, eTerm (u i) (v i)

omit [DecidableEq X] in

/-- Matrix-vector multiplication distributes over a finite sum of matrices. -/
private theorem sum_mulVec (Mt : ι → Matrix X X ℂ) (x : QState X) :
    (∑ i, Mt i) *ᵥ x = ∑ i, (Mt i *ᵥ x) :=
  map_sum (Matrix.mulVec.addMonoidHomLeft x) Mt Finset.univ

omit [DecidableEq X] in

/-- The action of an exchange correction is the sum of its four outer-product actions expressed
through `ip`. -/
private theorem eTerm_mulVec (u v x : QState X) (k : X) :
    (eTerm u v *ᵥ x) k
      = v k * ip u x + u k * ip v x - u k * ip u x - v k * ip v x := by
  simp only [eTerm, Matrix.sub_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.sub_apply,
    outer_mulVec, ip]

/-- Evaluate the exchange matrix on a vector as its original amplitude plus the sum of pairwise
corrections. -/
private theorem swapG_mulVec (u v : ι → QState X) (x : QState X) (k : X) :
    (swapG u v *ᵥ x) k = x k + ∑ i, (v i k * ip (u i) x + u i k * ip (v i) x
      - u i k * ip (u i) x - v i k * ip (v i) x) := by
  simp only [swapG, Matrix.add_mulVec, Matrix.one_mulVec, sum_mulVec, Pi.add_apply,
    Finset.sum_apply, eTerm_mulVec]

/-- Express the exchange matrix action as a vector identity consisting of the input plus its
finite correction sum. -/
private theorem swapG_mulVec' (u v : ι → QState X) (x : QState X) :
    swapG u v *ᵥ x = x + ∑ i, (fun k => v i k * ip (u i) x + u i k * ip (v i) x
      - u i k * ip (u i) x - v i k * ip (v i) x) := by
  funext k
  rw [Pi.add_apply, Finset.sum_apply]
  exact swapG_mulVec u v x k

/-- If `u` is orthonormal and orthogonal to every `v`, the `u j` inner product after applying
`swapG u v` equals the original `v j` inner product. -/
private theorem swapG_ip_u [DecidableEq ι] (u v : ι → QState X)
    (hun : ∀ i, ip (u i) (u i) = 1) (huu : ∀ i j, i ≠ j → ip (u i) (u j) = 0)
    (huv : ∀ i j, ip (u i) (v j) = 0)
    (j : ι) (x : QState X) : ip (u j) (swapG u v *ᵥ x) = ip (v j) x := by
  have hdelta : ∀ i, ip (u j) (u i) = if j = i then (1 : ℂ) else 0 := by
    intro i
    by_cases h : j = i
    · subst h; simp [hun]
    · rw [if_neg h, huu j i h]
  have key : ∀ i : ι, ip (u j) (fun k => v i k * ip (u i) x + u i k * ip (v i) x
      - u i k * ip (u i) x - v i k * ip (v i) x)
      = (if j = i then (1 : ℂ) else 0) * (ip (v i) x - ip (u i) x) := by
    intro i
    rw [ip_four, huv j i, hdelta i]
    by_cases h : j = i
    · subst h; simp
    · rw [if_neg h]; ring
  have hsum : ∑ i, (if j = i then (1 : ℂ) else 0) * (ip (v i) x - ip (u i) x)
      = ip (v j) x - ip (u j) x := by
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, one_mul]
    · intro i _ hi; rw [if_neg (Ne.symm hi)]; ring
    · intro hne; exact absurd (Finset.mem_univ j) hne
  rw [swapG_mulVec', ip_add_right, ip_sum_right]
  simp only [key]
  rw [hsum]
  ring

/-- If `v` is orthonormal and orthogonal to every `u`, the `v j` inner product after applying
`swapG u v` equals the original `u j` inner product. -/
private theorem swapG_ip_v [DecidableEq ι] (u v : ι → QState X)
    (hvn : ∀ i, ip (v i) (v i) = 1) (hvv : ∀ i j, i ≠ j → ip (v i) (v j) = 0)
    (huv : ∀ i j, ip (u i) (v j) = 0)
    (j : ι) (x : QState X) : ip (v j) (swapG u v *ᵥ x) = ip (u j) x := by
  have hdelta : ∀ i, ip (v j) (v i) = if j = i then (1 : ℂ) else 0 := by
    intro i
    by_cases h : j = i
    · subst h; simp [hvn]
    · rw [if_neg h, hvv j i h]
  have hconj : ∀ i, ip (v j) (u i) = 0 := by
    intro i; rw [ip_star_swap, huv i j]; simp
  have key : ∀ i : ι, ip (v j) (fun k => v i k * ip (u i) x + u i k * ip (v i) x
      - u i k * ip (u i) x - v i k * ip (v i) x)
      = (if j = i then (1 : ℂ) else 0) * (ip (u i) x - ip (v i) x) := by
    intro i
    rw [ip_four, hconj i, hdelta i]
    by_cases h : j = i
    · subst h; simp
    · rw [if_neg h]; ring
  have hsum : ∑ i, (if j = i then (1 : ℂ) else 0) * (ip (u i) x - ip (v i) x)
      = ip (u j) x - ip (v j) x := by
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, one_mul]
    · intro i _ hi; rw [if_neg (Ne.symm hi)]; ring
    · intro hne; exact absurd (Finset.mem_univ j) hne
  rw [swapG_mulVec', ip_add_right, ip_sum_right]
  simp only [key]
  rw [hsum]
  ring

/-- If `u` is orthonormal and orthogonal to every `v`, `swapG u v` sends each `u j` to `v j`. -/
private theorem swapG_mulVec_u [DecidableEq ι] (u v : ι → QState X)
    (hun : ∀ i, ip (u i) (u i) = 1) (huu : ∀ i j, i ≠ j → ip (u i) (u j) = 0)
    (huv : ∀ i j, ip (u i) (v j) = 0) (j : ι) :
    swapG u v *ᵥ u j = v j := by
  have hdelta : ∀ i, ip (u i) (u j) = if i = j then (1 : ℂ) else 0 := by
    intro i
    by_cases h : i = j
    · subst h; simp [hun]
    · rw [if_neg h, huu i j h]
  have hconj : ∀ i, ip (v i) (u j) = 0 := by
    intro i; rw [ip_star_swap, huv j i]; simp
  funext k'
  have key : ∀ i : ι, v i k' * ip (u i) (u j) + u i k' * ip (v i) (u j)
      - u i k' * ip (u i) (u j) - v i k' * ip (v i) (u j)
      = if i = j then v i k' - u i k' else 0 := by
    intro i
    rw [hdelta i, hconj i]
    by_cases h : i = j
    · subst h; simp
    · simp only [if_neg h]
      ring
  rw [swapG_mulVec u v (u j) k']
  simp only [key]
  rw [Finset.sum_ite_eq']
  simp

/-- If `v` is orthonormal and orthogonal to every `u`, `swapG u v` sends each `v j` to `u j`. -/
private theorem swapG_mulVec_v [DecidableEq ι] (u v : ι → QState X)
    (hvn : ∀ i, ip (v i) (v i) = 1) (hvv : ∀ i j, i ≠ j → ip (v i) (v j) = 0)
    (huv : ∀ i j, ip (u i) (v j) = 0) (j : ι) :
    swapG u v *ᵥ v j = u j := by
  have hdelta : ∀ i, ip (v i) (v j) = if i = j then (1 : ℂ) else 0 := by
    intro i
    by_cases h : i = j
    · subst h; simp [hvn]
    · rw [if_neg h, hvv i j h]
  have hconj : ∀ i, ip (u i) (v j) = 0 := fun i => huv i j
  have key : ∀ (k' : X) (i : ι), v i k' * ip (u i) (v j) + u i k' * ip (v i) (v j)
      - u i k' * ip (u i) (v j) - v i k' * ip (v i) (v j)
      = if i = j then u i k' - v i k' else 0 := by
    intro k' i
    rw [hconj i, hdelta i]
    by_cases h : i = j
    · subst h; simp
    · simp only [if_neg h]
      ring
  funext k'
  rw [swapG_mulVec u v (v j) k']
  simp only [key]
  rw [Finset.sum_ite_eq']
  simp

/-- The exchange matrix fixes any vector orthogonal to both indexed families. -/
private theorem swapG_mulVec_orth (u v : ι → QState X) (w : QState X)
    (h : ∀ i, ip (u i) w = 0 ∧ ip (v i) w = 0) : swapG u v *ᵥ w = w := by
  funext k'
  rw [swapG_mulVec u v w k']
  have key : ∀ i : ι, v i k' * ip (u i) w + u i k' * ip (v i) w
      - u i k' * ip (u i) w - v i k' * ip (v i) w = 0 := by
    intro i
    obtain ⟨h1, h2⟩ := h i
    rw [h1, h2]
    ring
  simp only [key, Finset.sum_const_zero]
  ring

/-- For two mutually orthogonal orthonormal families, the exchange matrix squares to the
identity. -/
private theorem swapG_sq [DecidableEq ι] (u v : ι → QState X)
    (hun : ∀ i, ip (u i) (u i) = 1) (hvn : ∀ i, ip (v i) (v i) = 1)
    (huu : ∀ i j, i ≠ j → ip (u i) (u j) = 0) (hvv : ∀ i j, i ≠ j → ip (v i) (v j) = 0)
    (huv : ∀ i j, ip (u i) (v j) = 0) : swapG u v * swapG u v = 1 := by
  have hact : ∀ x : QState X, swapG u v *ᵥ (swapG u v *ᵥ x) = x := by
    intro x
    have e1 := swapG_ip_u u v hun huu huv
    have e2 := swapG_ip_v u v hvn hvv huv
    funext k'
    rw [swapG_mulVec u v (swapG u v *ᵥ x) k']
    have hrow : ∀ i : ι, v i k' * ip (u i) (swapG u v *ᵥ x)
        + u i k' * ip (v i) (swapG u v *ᵥ x)
        - u i k' * ip (u i) (swapG u v *ᵥ x) - v i k' * ip (v i) (swapG u v *ᵥ x)
        = -(v i k' * ip (u i) x + u i k' * ip (v i) x
          - u i k' * ip (u i) x - v i k' * ip (v i) x) := by
      intro i; rw [e1 i, e2 i]; ring
    simp only [hrow]
    rw [swapG_mulVec u v x k']
    have hsum0 : ∀ g : ι → ℂ, (∑ i, g i) + ∑ i, -(g i) = 0 := by
      intro g
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by ring
    rw [add_assoc, hsum0]
    ring
  ext i j
  have h1 := congrFun (hact (Qatlib.Foundations.PureStateMath.Ket j)) i
  rw [Matrix.mulVec_mulVec] at h1
  have hL : ((swapG u v * swapG u v) *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = (swapG u v * swapG u v) i j := by
    simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; ring
    · intro k _ hk; rw [if_neg hk]; ring
    · intro hne; exact absurd (Finset.mem_univ j) hne
  rw [hL] at h1
  rw [Matrix.one_apply]
  simpa only [Qatlib.Foundations.PureStateMath.Ket] using h1

omit [Fintype X] [DecidableEq X] in

/-- The matrix adjoint of an outer product exchanges its two vector arguments. -/
private theorem star_outer (w w' : QState X) : star (outer w w') = outer w' w := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  simp only [Matrix.conjTranspose_apply, outer, Matrix.of_apply, star_mul, star_star]

omit [Fintype X] [DecidableEq X] in

/-- Each pairwise exchange correction equals its matrix adjoint. -/
private theorem star_eTerm (a b : QState X) : star (eTerm a b) = eTerm a b := by
  simp only [eTerm, star_sub, star_add, star_outer]
  rw [add_comm (outer a b) (outer b a)]

/-- The exchange matrix equals its matrix adjoint. -/
private theorem star_swapG (u v : ι → QState X) : star (swapG u v) = swapG u v := by
  simp only [swapG, star_add, star_sum, star_one, star_eTerm]

/-- Two mutually orthogonal orthonormal families possess a unitary matrix sending each vector of
the first family to its partner and fixing their common orthogonal complement. -/
private theorem exists_swap [DecidableEq ι] (u v : ι → QState X)
    (hun : ∀ i, ip (u i) (u i) = 1) (hvn : ∀ i, ip (v i) (v i) = 1)
    (huu : ∀ i j, i ≠ j → ip (u i) (u j) = 0) (hvv : ∀ i j, i ≠ j → ip (v i) (v j) = 0)
    (huv : ∀ i j, ip (u i) (v j) = 0) :
    ∃ S : Matrix X X ℂ, S ∈ Matrix.unitaryGroup X ℂ ∧ (∀ i, S *ᵥ u i = v i)
      ∧ ∀ w : QState X, (∀ i, ip (u i) w = 0 ∧ ip (v i) w = 0) → S *ᵥ w = w :=
  ⟨swapG u v, by
      rw [Matrix.mem_unitaryGroup_iff, star_swapG]
      exact swapG_sq u v hun hvn huu hvv huv,
    swapG_mulVec_u u v hun huu huv, swapG_mulVec_orth u v⟩

end Swap

section Builders
variable {Q A : Type*}

/-- The window with a flag-two head on the left carrying `s.1`, and tape symbols `b`, `s.2`, and
`c` from left to right. -/
private def wL (s : Q × A) (b c : A) : GWindow Q A :=
  win3 (2, some s.1, b) (0, none, s.2) (0, none, c)

/-- The window with a flag-two head in the middle carrying `s.1`, and tape symbols `b`, `s.2`,
and `c` from left to right. -/
private def wS (s : Q × A) (b c : A) : GWindow Q A :=
  win3 (0, none, b) (2, some s.1, s.2) (0, none, c)

/-- The window with a flag-two head on the right carrying `s.1`, and tape symbols `b`, `s.2`,
and `c` from left to right. -/
private def wR (s : Q × A) (b c : A) : GWindow Q A :=
  win3 (0, none, b) (0, none, s.2) (2, some s.1, c)

/-- The window with a flag-two head on the left carrying `s.1`, and tape symbols `s.2`, `b`, and
`c` from left to right. -/
private def wFS (s : Q × A) (b c : A) : GWindow Q A :=
  win3 (2, some s.1, s.2) (0, none, b) (0, none, c)

/-- The window with a flag-two head in the middle carrying `s.1`, and tape symbols `s.2`, `b`,
and `c` from left to right. -/
private def wFR (s : Q × A) (b c : A) : GWindow Q A :=
  win3 (0, none, s.2) (2, some s.1, b) (0, none, c)

/-- The window with a flag-two head on the left carrying state `r`, and tape symbols `b`, `c`,
and `d` from left to right. -/
private def wU (r : Q) (b c d : A) : GWindow Q A :=
  win3 (2, some r, b) (0, none, c) (0, none, d)

/-- The window with a flag-one head in the middle carrying state `q`, and tape symbols `b`, `a`,
and `c` from left to right. -/
private def wH (q : Q) (a b c : A) : GWindow Q A :=
  win3 (0, none, b) (1, some q, a) (0, none, c)

/-- Three-cell windows with different left-cell flags are distinct. -/
private theorem win3_ne_left {x₀ x₁ x₂ y₀ y₁ y₂ : CellState Q A}
    (h : x₀.1 ≠ y₀.1) : win3 x₀ x₁ x₂ ≠ win3 y₀ y₁ y₂ := by
  intro he
  exact h (congrArg (fun z => z.1) ((win3_inj x₀ x₁ x₂ y₀ y₁ y₂).mp he).1)

/-- Three-cell windows with different middle-cell flags are distinct. -/
private theorem win3_ne_mid {x₀ x₁ x₂ y₀ y₁ y₂ : CellState Q A}
    (h : x₁.1 ≠ y₁.1) : win3 x₀ x₁ x₂ ≠ win3 y₀ y₁ y₂ := by
  intro he
  exact h (congrArg (fun z => z.1) ((win3_inj x₀ x₁ x₂ y₀ y₁ y₂).mp he).2.1)

/-- Three-cell windows with different right-cell flags are distinct. -/
private theorem win3_ne_right {x₀ x₁ x₂ y₀ y₁ y₂ : CellState Q A}
    (h : x₂.1 ≠ y₂.1) : win3 x₀ x₁ x₂ ≠ win3 y₀ y₁ y₂ := by
  intro he
  exact h (congrArg (fun z => z.1) ((win3_inj x₀ x₁ x₂ y₀ y₁ y₂).mp he).2.2)

end Builders

section WinFacts
variable {Q A : Type*}

/-- For fixed neighboring symbols, equality of two `wL` windows is equivalent to equality of
their state-symbol parameters. -/
private theorem wL_inj (s t : Q × A) (b c : A) : wL s b c = wL t b c ↔ s = t := by
  simp only [wL, win3_inj, Prod.mk.injEq, Option.some.injEq]
  simp [Prod.ext_iff]

/-- For fixed neighboring symbols, equality of two `wS` windows is equivalent to equality of
their state-symbol parameters. -/
private theorem wS_inj (s t : Q × A) (b c : A) : wS s b c = wS t b c ↔ s = t := by
  simp only [wS, win3_inj, Prod.mk.injEq, Option.some.injEq]
  simp [Prod.ext_iff]

/-- For fixed neighboring symbols, equality of two `wR` windows is equivalent to equality of
their state-symbol parameters. -/
private theorem wR_inj (s t : Q × A) (b c : A) : wR s b c = wR t b c ↔ s = t := by
  simp only [wR, win3_inj, Prod.mk.injEq, Option.some.injEq]
  rw [Prod.ext_iff]
  tauto

/-- A window `wFS s b c` equals `wL t b' c'` exactly when `t = (s.1, b)`, `s.2 = b'`, and `c =
c'`. -/
private theorem wFS_wL (s t : Q × A) (b c b' c' : A) :
    wFS s b c = wL t b' c' ↔ (t = (s.1, b) ∧ (s.2 = b' ∧ c = c')) := by
  simp only [wFS, wL, win3_inj, Prod.mk.injEq, Option.some.injEq, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨Prod.ext (by simp [h1]) (by simp [h3]), h2, h4⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- A window `wFR s b c` equals `wS t b' c'` exactly when `t = (s.1, b)`, `s.2 = b'`, and `c =
c'`. -/
private theorem wFR_wS (s t : Q × A) (b c b' c' : A) :
    wFR s b c = wS t b' c' ↔ (t = (s.1, b) ∧ (s.2 = b' ∧ c = c')) := by
  simp only [wFR, wS, win3_inj, Prod.mk.injEq, Option.some.injEq, true_and]
  constructor
  · rintro ⟨h0, ⟨h1, h2⟩, h4⟩
    exact ⟨Prod.ext (by simp [h1]) (by simp [h2]), h0, h4⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- A window `wU r b c d` equals `wL t b' c'` exactly when `t = (r, c)`, `b = b'`, and `d = c'`. -/
private theorem wU_wL (r : Q) (t : Q × A) (b c d b' c' : A) :
    wU r b c d = wL t b' c' ↔ (t = (r, c) ∧ (b = b' ∧ d = c')) := by
  simp only [wU, wL, win3_inj, Prod.mk.injEq, Option.some.injEq, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨Prod.ext (by simp [h1]) (by simp [h3]), h2, h4⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- Equality of two `wH` windows forces equality of their machine states and all three tape
symbols. -/
private theorem wH_inj {q q' : Q} {a a' b b' c c' : A}
    (h : wH q a b c = wH q' a' b' c') : q = q' ∧ a = a' ∧ b = b' ∧ c = c' := by
  simp only [wH, win3_inj, Prod.mk.injEq, Option.some.injEq] at h
  tauto

/-- A window of form `wL` is distinct from every window of form `wS`. -/
private theorem wL_ne_wS (s t : Q × A) (b c b' c' : A) : wL s b c ≠ wS t b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wL` is distinct from every window of form `wR`. -/
private theorem wL_ne_wR (s t : Q × A) (b c b' c' : A) : wL s b c ≠ wR t b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wS` is distinct from every window of form `wL`. -/
private theorem wS_ne_wL (s t : Q × A) (b c b' c' : A) : wS s b c ≠ wL t b' c' :=
  fun he => win3_ne_mid (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wS` is distinct from every window of form `wR`. -/
private theorem wS_ne_wR (s t : Q × A) (b c b' c' : A) : wS s b c ≠ wR t b' c' :=
  fun he => win3_ne_mid (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wR` is distinct from every window of form `wL`. -/
private theorem wR_ne_wL (s t : Q × A) (b c b' c' : A) : wR s b c ≠ wL t b' c' :=
  fun he => win3_ne_right (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wR` is distinct from every window of form `wS`. -/
private theorem wR_ne_wS (s t : Q × A) (b c b' c' : A) : wR s b c ≠ wS t b' c' :=
  fun he => win3_ne_mid (by decide : (0 : Fin 3) ≠ 2) he

/-- A window of form `wFS` is distinct from every window of form `wS`. -/
private theorem wFS_ne_wS (s t : Q × A) (b c b' c' : A) : wFS s b c ≠ wS t b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wFS` is distinct from every window of form `wR`. -/
private theorem wFS_ne_wR (s t : Q × A) (b c b' c' : A) : wFS s b c ≠ wR t b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wFR` is distinct from every window of form `wL`. -/
private theorem wFR_ne_wL (s t : Q × A) (b c b' c' : A) : wFR s b c ≠ wL t b' c' :=
  fun he => win3_ne_mid (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wFR` is distinct from every window of form `wR`. -/
private theorem wFR_ne_wR (s t : Q × A) (b c b' c' : A) : wFR s b c ≠ wR t b' c' :=
  fun he => win3_ne_mid (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wH` is distinct from every window of form `wL`. -/
private theorem wH_ne_wL (q : Q) (a b c : A) (s : Q × A) (b' c' : A) :
    wH q a b c ≠ wL s b' c' :=
  fun he => win3_ne_mid (by decide : (1 : Fin 3) ≠ 0) he

/-- A window of form `wH` is distinct from every window of form `wS`. -/
private theorem wH_ne_wS (q : Q) (a b c : A) (s : Q × A) (b' c' : A) :
    wH q a b c ≠ wS s b' c' :=
  fun he => win3_ne_mid (by decide : (1 : Fin 3) ≠ 2) he

/-- A window of form `wH` is distinct from every window of form `wR`. -/
private theorem wH_ne_wR (q : Q) (a b c : A) (s : Q × A) (b' c' : A) :
    wH q a b c ≠ wR s b' c' :=
  fun he => win3_ne_mid (by decide : (1 : Fin 3) ≠ 0) he

/-- A window of form `wFS` is distinct from every window of form `wH`. -/
private theorem wFS_ne_wH (s : Q × A) (b c : A) (q : Q) (a b' c' : A) :
    wFS s b c ≠ wH q a b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wFR` is distinct from every window of form `wH`. -/
private theorem wFR_ne_wH (s : Q × A) (b c : A) (q : Q) (a b' c' : A) :
    wFR s b c ≠ wH q a b' c' :=
  fun he => win3_ne_mid (by decide : (2 : Fin 3) ≠ 1) he

/-- A window of form `wU` is distinct from every window of form `wH`. -/
private theorem wU_ne_wH (r : Q) (b c d : A) (q : Q) (a b' c' : A) :
    wU r b c d ≠ wH q a b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wU` is distinct from every window of form `wS`. -/
private theorem wU_ne_wS (r : Q) (b c d : A) (s : Q × A) (b' c' : A) :
    wU r b c d ≠ wS s b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- A window of form `wU` is distinct from every window of form `wR`. -/
private theorem wU_ne_wR (r : Q) (b c d : A) (s : Q × A) (b' c' : A) :
    wU r b c d ≠ wR s b' c' :=
  fun he => win3_ne_left (by decide : (2 : Fin 3) ≠ 0) he

/-- Componentwise equality of a state and three symbols gives equality of the corresponding
quadruples. -/
private theorem quad_eq {q q' : Q} {a a' b b' c c' : A}
    (h1 : q = q') (h2 : a = a') (h3 : b = b') (h4 : c = c') :
    (q, a, b, c) = (q', a', b', c') := by
  rw [h1, h2, h3, h4]

end WinFacts

section Ortho
variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

omit [DecidableEq Q] [DecidableEq A] in

/-- A sum over state-symbol pairs equals the corresponding nested sum over states and symbols. -/
private theorem sum_prod_split (F : Q × A → ℂ) :
    ∑ s : Q × A, F s = ∑ r : Q, ∑ a2 : A, F (r, a2) := by
  rw [Fintype.sum_prod_type]

omit [Fintype Q] [Fintype A] in

/-- The indicator of three specified cell values equals the indicator of equality with the
corresponding `win3` window. -/
private theorem ind_win3 (z : GWindow Q A) (x y w : CellState Q A) :
    (if z 0 = x ∧ z 1 = y ∧ z 2 = w then (1 : ℂ) else 0)
      = if z = win3 x y w then 1 else 0 := by
  by_cases h : z 0 = x ∧ z 1 = y ∧ z 2 = w
  · rw [if_pos h, if_pos]
    exact (win3_eq_iff z x y w).2 h
  · rw [if_neg h, if_neg]
    intro hh
    exact h ((win3_eq_iff z x y w).1 hh)

omit [Fintype Q] [Fintype A] in

/-- The vector `headBasis q a b c` is the computational basis vector at `wH q a b c`. -/
private theorem headBasis_eq (q : Q) (a b c : A) :
    headBasis q a b c = Qatlib.Foundations.PureStateMath.Ket (wH q a b c) := by
  funext z
  have hz : z = wH q a b c ↔ (z 1 = (1, some q, a) ∧ z 0 = (0, none, b) ∧ z 2 = (0, none, c)) := by
    rw [wH, win3_eq_iff]
    tauto
  simp only [headBasis, Qatlib.Foundations.PureStateMath.Ket]
  by_cases h : z 1 = (1, some q, a) ∧ z 0 = (0, none, b) ∧ z 2 = (0, none, c)
  · rw [if_pos h, if_pos (hz.2 h)]
  · rw [if_neg h, if_neg (fun hh => h (hz.1 hh))]

/-- The local transition superposition decomposes into left, stay, and right `partVec`
components weighted by machine transition amplitudes. -/
private theorem stepSuperposition_eq (M : LocalQTM Q A) (q : Q) (a b c : A) :
    stepSuperposition M q a b c =
      partVec (fun s : Q × A => wL s b c) (fun s => M.step q a QtmMove.left s.1 s.2)
      + partVec (fun s : Q × A => wS s b c) (fun s => M.step q a QtmMove.stay s.1 s.2)
      + partVec (fun s : Q × A => wR s b c) (fun s => M.step q a QtmMove.right s.1 s.2) := by
  funext z
  have h1 : (∑ q' : Q, ∑ a' : A, M.step q a QtmMove.left q' a'
        * (if z 0 = (2, some q', b) ∧ z 1 = (0, none, a') ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0))
      = ∑ s : Q × A, M.step q a QtmMove.left s.1 s.2
        * (if z = wL s b c then (1 : ℂ) else 0) := by
    rw [sum_pair (fun q' a' => M.step q a QtmMove.left q' a'
      * (if z 0 = (2, some q', b) ∧ z 1 = (0, none, a') ∧ z 2 = (0, none, c)
        then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [wL, ind_win3 z _ _ _]
  have h2 : (∑ q' : Q, ∑ a' : A, M.step q a QtmMove.stay q' a'
        * (if z 0 = (0, none, b) ∧ z 1 = (2, some q', a') ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0))
      = ∑ s : Q × A, M.step q a QtmMove.stay s.1 s.2
        * (if z = wS s b c then (1 : ℂ) else 0) := by
    rw [sum_pair (fun q' a' => M.step q a QtmMove.stay q' a'
      * (if z 0 = (0, none, b) ∧ z 1 = (2, some q', a') ∧ z 2 = (0, none, c)
        then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [wS, ind_win3 z _ _ _]
  have h3 : (∑ q' : Q, ∑ a' : A, M.step q a QtmMove.right q' a'
        * (if z 0 = (0, none, b) ∧ z 1 = (0, none, a') ∧ z 2 = (2, some q', c)
          then (1 : ℂ) else 0))
      = ∑ s : Q × A, M.step q a QtmMove.right s.1 s.2
        * (if z = wR s b c then (1 : ℂ) else 0) := by
    rw [sum_pair (fun q' a' => M.step q a QtmMove.right q' a'
      * (if z 0 = (0, none, b) ∧ z 1 = (0, none, a') ∧ z 2 = (2, some q', c)
        then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [wR, ind_win3 z _ _ _]
  simp only [stepSuperposition, partVec, Pi.add_apply]
  rw [h1, h2, h3]

/-- The vector `vFamily` decomposes into its `wFS` stay component and `wFR` right-move component
with the corresponding transition amplitudes. -/
private theorem vFamily_eq (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) :
    vFamily M q₀ a₀ b c =
      partVec (fun s : Q × A => wFS s b c) (fun s => M.step q₀ a₀ QtmMove.stay s.1 s.2)
      + partVec (fun s : Q × A => wFR s b c) (fun s => M.step q₀ a₀ QtmMove.right s.1 s.2) := by
  funext z
  have h1 : (∑ q' : Q, ∑ a' : A, M.step q₀ a₀ QtmMove.stay q' a'
        * (if z 0 = (2, some q', a') ∧ z 1 = (0, none, b) ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0))
      = ∑ s : Q × A, M.step q₀ a₀ QtmMove.stay s.1 s.2
        * (if z = wFS s b c then (1 : ℂ) else 0) := by
    rw [sum_pair (fun q' a' => M.step q₀ a₀ QtmMove.stay q' a'
      * (if z 0 = (2, some q', a') ∧ z 1 = (0, none, b) ∧ z 2 = (0, none, c)
        then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [wFS, ind_win3 z _ _ _]
  have h2 : (∑ q' : Q, ∑ a' : A, M.step q₀ a₀ QtmMove.right q' a'
        * (if z 0 = (0, none, a') ∧ z 1 = (2, some q', b) ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0))
      = ∑ s : Q × A, M.step q₀ a₀ QtmMove.right s.1 s.2
        * (if z = wFR s b c then (1 : ℂ) else 0) := by
    rw [sum_pair (fun q' a' => M.step q₀ a₀ QtmMove.right q' a'
      * (if z 0 = (0, none, a') ∧ z 1 = (2, some q', b) ∧ z 2 = (0, none, c)
        then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [wFR, ind_win3 z _ _ _]
  simp only [vFamily, partVec, Pi.add_apply]
  rw [h1, h2]

/-- The vector `uFamily` is a `partVec` over machine states on `wU` windows, weighted by
right-move transition amplitudes with fixed output symbol. -/
private theorem uFamily_eq (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A) :
    uFamily M q₀ a₀ a'' b c d
      = partVec (fun r : Q => wU r b c d) (fun r => M.step q₀ a₀ QtmMove.right r a'') := by
  funext z
  have h1 : (∑ q' : Q, M.step q₀ a₀ QtmMove.right q' a''
        * (if z 0 = (2, some q', b) ∧ z 1 = (0, none, c) ∧ z 2 = (0, none, d)
          then (1 : ℂ) else 0))
      = ∑ r : Q, M.step q₀ a₀ QtmMove.right r a''
        * (if z = wU r b c d then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [wU, ind_win3 z _ _ _]
  simp only [uFamily, partVec]
  rw [h1]

/-- The inner product of two window basis vectors is one when their indices agree and zero
otherwise. -/
private theorem ip_ket_ket (w z : GWindow Q A) :
    ip (Qatlib.Foundations.PureStateMath.Ket w) (Qatlib.Foundations.PureStateMath.Ket z) = if w = z then (1 : ℂ) else 0 := by
  show (∑ i : GWindow Q A, star ((if i = w then (1 : ℂ) else 0))
      * (if i = z then 1 else 0)) = if w = z then (1 : ℂ) else 0
  rw [Finset.sum_congr rfl (fun i _ => by rw [star_ind])]
  exact sum_ind_ind w z

/-- For an injective basis-index map `W`, the inner product of two `partVec W` vectors is the
inner product of their coefficient functions. -/
private theorem ip_diag {X : Type*} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → X) (hW : ∀ s t, W s = W t ↔ s = t) (g h : ι → ℂ) :
    ip (partVec W g) (partVec W h) = ∑ s, star (g s) * h s := by
  rw [ip_bilin W g W h]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc ∑ t, star (g s) * h t * (if W s = W t then (1 : ℂ) else 0)
      = ∑ t, star (g s) * h t * (if s = t then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun t _ => by rw [if_congr (hW s t) rfl rfl]
    _ = star (g s) * h s := by
        calc ∑ t, star (g s) * h t * (if s = t then (1 : ℂ) else 0)
            = star (g s) * ∑ t, (if s = t then h t else 0) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
          _ = star (g s) * h s := by rw [Finset.sum_ite_eq]; simp

/-- Two `partVec` vectors have zero inner product when their basis-index maps have disjoint
images. -/
private theorem ip_zero_disj {X : Type*} [Fintype X] [DecidableEq X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : ι → X) (g : ι → ℂ) (W' : κ → X) (h : κ → ℂ)
    (hdis : ∀ s t, W s ≠ W' t) : ip (partVec W g) (partVec W' h) = 0 := by
  rw [ip_bilin W g W' h]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg (hdis s t)]
  ring

/-- Two window superpositions are orthogonal when their distinct side-symbol pairs could be
recovered from any equality of their basis windows. -/
private theorem ip_zero_of_side {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : ι → GWindow Q A) (g : ι → ℂ) (W' : κ → GWindow Q A) (h : κ → ℂ)
    (b c b' c' : A) (hbc : (b, c) ≠ (b', c'))
    (hextr : ∀ s t, W s = W' t → (b, c) = (b', c')) :
    ip (partVec W g) (partVec W' h) = 0 := by
  rw [ip_bilin W g W' h]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg (fun heq => hbc (hextr s t heq))]
  ring

/-- Collapse the double sum constrained by `t = (s.1, b)`, `s.2 = b'`, and `c = c'` to the state
sum `∑ r, g (r, b') * h (r, b)`, or zero if `c ≠ c'`. -/
private theorem sum_pair_collapse (g h : Q × A → ℂ) (b b' c c' : A) :
    ∑ s : Q × A, ∑ t : Q × A, g s * h t
        * (if t = (s.1, b) ∧ (s.2 = b' ∧ c = c') then (1 : ℂ) else 0)
      = (if c = c' then ∑ r : Q, g (r, b') * h (r, b) else 0) := by
  by_cases hcc : c = c'
  · rw [if_pos hcc]
    have key : ∀ s : Q × A, ∑ t : Q × A, g s * h t
        * (if t = (s.1, b) ∧ (s.2 = b' ∧ c = c') then (1 : ℂ) else 0)
        = (if s.2 = b' then g s * h (s.1, b) else 0) := by
      intro s
      by_cases hb : s.2 = b'
      · rw [if_pos hb]
        have hc : ∀ t : Q × A,
            (t = (s.1, b) ∧ (s.2 = b' ∧ c = c')) ↔ (t = (s.1, b)) := by
          intro t; rw [hb, hcc]; simp
        simp only [hc]
        rw [Finset.sum_eq_single (s.1, b)
          (fun t _ ht => by rw [if_neg ht]; ring)
          (fun hne => absurd (Finset.mem_univ _) hne)]
        rw [if_pos rfl, mul_one]
      · rw [if_neg hb]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [if_neg (fun hk => hb hk.2.1)]
        ring
    simp only [key]
    rw [sum_prod_split]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single b'
      (fun a2 _ ha2 => by rw [if_neg ha2])
      (fun hne => absurd (Finset.mem_univ _) hne)]
    rw [if_pos rfl]
  · rw [if_neg hcc]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun hk => hcc hk.2.2)]
    ring

/-- Collapse the state and state-symbol sum constrained by `t = (r, c)`, `b = b'`, and `d = c'`
to `∑ r, g r * h (r, c)`, or zero when the fixed-symbol constraints fail. -/
private theorem sum_single_collapse (g : Q → ℂ) (h : Q × A → ℂ) (c b b' d c' : A) :
    ∑ r : Q, ∑ t : Q × A, g r * h t
        * (if t = (r, c) ∧ (b = b' ∧ d = c') then (1 : ℂ) else 0)
      = (if b = b' ∧ d = c' then ∑ r : Q, g r * h (r, c) else 0) := by
  by_cases hK : b = b' ∧ d = c'
  · rw [if_pos hK]
    have hc : ∀ (r : Q) (t : Q × A), (t = (r, c) ∧ (b = b' ∧ d = c')) ↔ (t = (r, c)) := by
      intro r t; rw [hK.1, hK.2]; simp
    simp only [hc]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single (r, c)
      (fun t _ ht => by rw [if_neg ht]; ring)
      (fun hne => absurd (Finset.mem_univ _) hne)]
    rw [if_pos rfl, mul_one]
  · rw [if_neg hK]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun hk => hK hk.2)]
    ring

end Ortho

section Pairs
variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

/-- For fixed side symbols, the inner product of two left-move window superpositions is the
inner product of their left-transition coefficient functions. -/
private theorem ip_LL (M : LocalQTM Q A) (q q' : Q) (a a' b c : A) :
    ip (partVec (fun s : Q × A => wL s b c) (fun s => M.step q a QtmMove.left s.1 s.2))
        (partVec (fun t : Q × A => wL t b c) (fun t => M.step q' a' QtmMove.left t.1 t.2))
      = ∑ s : Q × A, star (M.step q a QtmMove.left s.1 s.2)
        * M.step q' a' QtmMove.left s.1 s.2 :=
  ip_diag _ (fun s t => wL_inj s t b c) _ _

/-- For fixed side symbols, the inner product of two stay-move window superpositions is the
inner product of their stay-transition coefficient functions. -/
private theorem ip_SS (M : LocalQTM Q A) (q q' : Q) (a a' b c : A) :
    ip (partVec (fun s : Q × A => wS s b c) (fun s => M.step q a QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wS t b c) (fun t => M.step q' a' QtmMove.stay t.1 t.2))
      = ∑ s : Q × A, star (M.step q a QtmMove.stay s.1 s.2)
        * M.step q' a' QtmMove.stay s.1 s.2 :=
  ip_diag _ (fun s t => wS_inj s t b c) _ _

/-- For fixed side symbols, the inner product of two right-move window superpositions is the
inner product of their right-transition coefficient functions. -/
private theorem ip_RR (M : LocalQTM Q A) (q q' : Q) (a a' b c : A) :
    ip (partVec (fun s : Q × A => wR s b c) (fun s => M.step q a QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wR t b c) (fun t => M.step q' a' QtmMove.right t.1 t.2))
      = ∑ s : Q × A, star (M.step q a QtmMove.right s.1 s.2)
        * M.step q' a' QtmMove.right s.1 s.2 :=
  ip_diag _ (fun s t => wR_inj s t b c) _ _

/-- The left-move window superposition is orthogonal to the stay-move window superposition. -/
private theorem ip_LS (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (partVec (fun s : Q × A => wL s b c) (fun s => M.step q a QtmMove.left s.1 s.2))
        (partVec (fun t : Q × A => wS t b' c') (fun t => M.step q' a' QtmMove.stay t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wL_ne_wS s t b c b' c')

/-- The left-move window superposition is orthogonal to the right-move window superposition. -/
private theorem ip_LR (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (partVec (fun s : Q × A => wL s b c) (fun s => M.step q a QtmMove.left s.1 s.2))
        (partVec (fun t : Q × A => wR t b' c') (fun t => M.step q' a' QtmMove.right t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wL_ne_wR s t b c b' c')

/-- The stay-move window superposition is orthogonal to the left-move window superposition. -/
private theorem ip_SL (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (partVec (fun s : Q × A => wS s b c) (fun s => M.step q a QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wL t b' c') (fun t => M.step q' a' QtmMove.left t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wS_ne_wL s t b c b' c')

/-- The stay-move window superposition is orthogonal to the right-move window superposition. -/
private theorem ip_SR (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (partVec (fun s : Q × A => wS s b c) (fun s => M.step q a QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wR t b' c') (fun t => M.step q' a' QtmMove.right t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wS_ne_wR s t b c b' c')

/-- The right-move window superposition is orthogonal to the left-move window superposition. -/
private theorem ip_RL (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (partVec (fun s : Q × A => wR s b c) (fun s => M.step q a QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wL t b' c') (fun t => M.step q' a' QtmMove.left t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wR_ne_wL s t b c b' c')

/-- The right-move window superposition is orthogonal to the stay-move window superposition. -/
private theorem ip_RS (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (partVec (fun s : Q × A => wR s b c) (fun s => M.step q a QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wS t b' c') (fun t => M.step q' a' QtmMove.stay t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wR_ne_wS s t b c b' c')

/-- Left-move window superpositions with different side-symbol pairs are orthogonal. -/
private theorem ip_LL_side (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A)
    (hbc : (b, c) ≠ (b', c')) :
    ip (partVec (fun s : Q × A => wL s b c) (fun s => M.step q a QtmMove.left s.1 s.2))
        (partVec (fun t : Q × A => wL t b' c') (fun t => M.step q' a' QtmMove.left t.1 t.2))
      = 0 :=
  ip_zero_of_side _ _ _ _ b c b' c' hbc (fun s t heq => by
    simp only [wL, win3_inj, Prod.mk.injEq, Option.some.injEq] at heq
    exact Prod.ext_iff.mpr ⟨heq.1.2.2, heq.2.2.2.2⟩)

/-- Stay-move window superpositions with different side-symbol pairs are orthogonal. -/
private theorem ip_SS_side (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A)
    (hbc : (b, c) ≠ (b', c')) :
    ip (partVec (fun s : Q × A => wS s b c) (fun s => M.step q a QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wS t b' c') (fun t => M.step q' a' QtmMove.stay t.1 t.2))
      = 0 :=
  ip_zero_of_side _ _ _ _ b c b' c' hbc (fun s t heq => by
    simp only [wS, win3_inj, Prod.mk.injEq, Option.some.injEq] at heq
    exact Prod.ext_iff.mpr ⟨heq.1.2.2, heq.2.2.2.2⟩)

/-- Right-move window superpositions with different side-symbol pairs are orthogonal. -/
private theorem ip_RR_side (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A)
    (hbc : (b, c) ≠ (b', c')) :
    ip (partVec (fun s : Q × A => wR s b c) (fun s => M.step q a QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wR t b' c') (fun t => M.step q' a' QtmMove.right t.1 t.2))
      = 0 :=
  ip_zero_of_side _ _ _ _ b c b' c' hbc (fun s t heq => by
    simp only [wR, win3_inj, Prod.mk.injEq, Option.some.injEq] at heq
    exact Prod.ext_iff.mpr ⟨heq.1.2.2, heq.2.2.2.2⟩)

/-- Each local transition superposition has inner product one with itself, as in [Yao, Lemma
1][Yao1993]. -/
private theorem ip_superp_self (M : LocalQTM Q A) (q : Q) (a b c : A) :
    ip (stepSuperposition M q a b c) (stepSuperposition M q a b c) = 1 := by
  nth_rewrite 1 [stepSuperposition_eq M q a b c]
  rw [stepSuperposition_eq M q a b c]
  simp only [ip_add_left, ip_add_right]
  rw [ip_LL M q q a a b c, ip_LS M q q a a b c b c, ip_LR M q q a a b c b c,
    ip_SL M q q a a b c b c, ip_SS M q q a a b c, ip_SR M q q a a b c b c,
    ip_RL M q q a a b c b c, ip_RS M q q a a b c b c, ip_RR M q q a a b c]
  simp only [add_zero, zero_add]
  rw [add_assoc]
  rw [sum_three_dir (fun d r x => star (M.step q a d r x) * M.step q a d r x)]
  simp only [star_mul_self_real]
  simp only [← Complex.ofReal_sum]
  rw [M.wf_norm q a]
  simp

/-- Local transition superpositions indexed by distinct state-and-symbol quadruples are
orthogonal, as in [Yao, Lemma 1][Yao1993]. -/
private theorem ip_superp_ne (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A)
    (h : (q, a, b, c) ≠ (q', a', b', c')) :
    ip (stepSuperposition M q a b c) (stepSuperposition M q' a' b' c') = 0 := by
  by_cases hbc : (b, c) = (b', c')
  · obtain ⟨hb, hc⟩ := Prod.ext_iff.mp hbc
    subst hb
    subst hc
    rw [stepSuperposition_eq M q a b c, stepSuperposition_eq M q' a' b c]
    simp only [ip_add_left, ip_add_right]
    rw [ip_LS M q q' a a' b c b c, ip_LR M q q' a a' b c b c,
      ip_SL M q q' a a' b c b c, ip_SR M q q' a a' b c b c,
      ip_RL M q q' a a' b c b c, ip_RS M q q' a a' b c b c,
      ip_LL M q q' a a' b c, ip_SS M q q' a a' b c, ip_RR M q q' a a' b c]
    simp only [add_zero, zero_add]
    rw [add_assoc]
    rw [sum_three_dir (fun d r x => star (M.step q a d r x) * M.step q' a' d r x)]
    exact M.wf_sameCell q a q' a' (fun hqa => h (by
      obtain ⟨hq, ha⟩ := Prod.ext_iff.mp hqa
      exact quad_eq hq ha rfl rfl))
  · rw [stepSuperposition_eq M q a b c, stepSuperposition_eq M q' a' b' c']
    simp only [ip_add_left, ip_add_right]
    rw [ip_LS M q q' a a' b c b' c', ip_LR M q q' a a' b c b' c',
      ip_SL M q q' a a' b c b' c', ip_SR M q q' a a' b c b' c',
      ip_RL M q q' a a' b c b' c', ip_RS M q q' a a' b c b' c',
      ip_LL_side M q q' a a' b c b' c' hbc, ip_SS_side M q q' a a' b c b' c' hbc,
      ip_RR_side M q q' a a' b c b' c' hbc]
    simp

/-- Every head basis vector is orthogonal to every local transition superposition. -/
private theorem ip_head_superp (M : LocalQTM Q A) (q q' : Q) (a a' b c b' c' : A) :
    ip (headBasis q a b c) (stepSuperposition M q' a' b' c') = 0 := by
  rw [headBasis_eq q a b c, stepSuperposition_eq M q' a' b' c']
  simp only [ip_add_right]
  rw [ip_ket_parts, ip_ket_parts, ip_ket_parts,
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (wH_ne_wL q a b c s b' c')]; ring),
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (wH_ne_wS q a b c s b' c')]; ring),
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (wH_ne_wR q a b c s b' c')]; ring)]
  ring

/-- Every head basis vector is orthogonal to each computational basis vector of a type-I window. -/
private theorem ip_head_ket_typeI (z : GWindow Q A) (hI : IsTypeI z) (q : Q) (a b c : A) :
    ip (headBasis q a b c) (Qatlib.Foundations.PureStateMath.Ket z) = 0 := by
  rw [headBasis_eq q a b c, ip_ket_ket, if_neg]
  intro heq
  exact hI.1 (by rw [← heq]; simp [wH, win3])

/-- Every local transition superposition is orthogonal to each computational basis vector of a
type-I window. -/
private theorem ip_superp_ket_typeI (z : GWindow Q A) (hI : IsTypeI z) (M : LocalQTM Q A)
    (q : Q) (a b c : A) :
    ip (stepSuperposition M q a b c) (Qatlib.Foundations.PureStateMath.Ket z) = 0 := by
  rw [stepSuperposition_eq M q a b c]
  simp only [ip_add_left]
  rw [ip_parts_ket, ip_parts_ket, ip_parts_ket,
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (fun hk : z = wL s b c => hI.2 0 (by rw [hk]; simp [wL, win3]))]; ring),
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (fun hk : z = wS s b c => hI.2 1 (by rw [hk]; simp [wS, win3]))]; ring),
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (fun hk : z = wR s b c => hI.2 2 (by rw [hk]; simp [wR, win3]))]; ring)]
  ring

end Pairs

section FixFam
variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

/-- The `wFS` superposition weighted by stay transitions is orthogonal to the `wL` superposition
weighted by left transitions. -/
private theorem ip_wFS_wL (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun s : Q × A => wFS s b c) (fun s => M.step q₀ a₀ QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wL t b' c') (fun t => M.step q a QtmMove.left t.1 t.2))
      = 0 := by
  rw [ip_bilin _ _ _ _]
  simp only [wFS_wL]
  rw [sum_pair_collapse _ _ _ _ _ _]
  by_cases hcc : c = c'
  · rw [if_pos hcc]
    exact star_sum_eq _ _ (M.wf_stayLeft q₀ a₀ q a b' b)
  · rw [if_neg hcc]

/-- The `wFR` superposition weighted by right transitions is orthogonal to the `wS`
superposition weighted by stay transitions. -/
private theorem ip_wFR_wS (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun s : Q × A => wFR s b c) (fun s => M.step q₀ a₀ QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wS t b' c') (fun t => M.step q a QtmMove.stay t.1 t.2))
      = 0 := by
  rw [ip_bilin _ _ _ _]
  simp only [wFR_wS]
  rw [sum_pair_collapse _ _ _ _ _ _]
  by_cases hcc : c = c'
  · rw [if_pos hcc]
    exact star_sum_eq _ _ (M.wf_rightStay q₀ a₀ q a b' b)
  · rw [if_neg hcc]

/-- The `wFS` superposition weighted by stay transitions is orthogonal to the `wS` superposition
weighted by stay transitions. -/
private theorem ip_wFS_wS (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun s : Q × A => wFS s b c) (fun s => M.step q₀ a₀ QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wS t b' c') (fun t => M.step q a QtmMove.stay t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wFS_ne_wS s t b c b' c')

/-- The `wFS` superposition weighted by stay transitions is orthogonal to the `wR` superposition
weighted by right transitions. -/
private theorem ip_wFS_wR (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun s : Q × A => wFS s b c) (fun s => M.step q₀ a₀ QtmMove.stay s.1 s.2))
        (partVec (fun t : Q × A => wR t b' c') (fun t => M.step q a QtmMove.right t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wFS_ne_wR s t b c b' c')

/-- The `wFR` superposition weighted by right transitions is orthogonal to the `wL`
superposition weighted by left transitions. -/
private theorem ip_wFR_wL (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun s : Q × A => wFR s b c) (fun s => M.step q₀ a₀ QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wL t b' c') (fun t => M.step q a QtmMove.left t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wFR_ne_wL s t b c b' c')

/-- The `wFR` superposition weighted by right transitions is orthogonal to the `wR`
superposition weighted by right transitions. -/
private theorem ip_wFR_wR (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun s : Q × A => wFR s b c) (fun s => M.step q₀ a₀ QtmMove.right s.1 s.2))
        (partVec (fun t : Q × A => wR t b' c') (fun t => M.step q a QtmMove.right t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun s t => wFR_ne_wR s t b c b' c')

/-- Every `vFamily` vector is orthogonal to every local transition superposition. -/
private theorem ip_vFamily_superp (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A)
    (q : Q) (a b' c' : A) :
    ip (vFamily M q₀ a₀ b c) (stepSuperposition M q a b' c') = 0 := by
  rw [vFamily_eq M q₀ a₀ b c, stepSuperposition_eq M q a b' c']
  simp only [ip_add_left, ip_add_right]
  rw [ip_wFS_wL M q₀ a₀ b c q a b' c', ip_wFS_wS M q₀ a₀ b c q a b' c',
    ip_wFS_wR M q₀ a₀ b c q a b' c', ip_wFR_wL M q₀ a₀ b c q a b' c',
    ip_wFR_wS M q₀ a₀ b c q a b' c', ip_wFR_wR M q₀ a₀ b c q a b' c']
  ring

/-- The `wU` superposition over states weighted by fixed-output-symbol right transitions is
orthogonal to the `wL` left-transition superposition. -/
private theorem ip_wU_wL (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun r : Q => wU r b c d) (fun r => M.step q₀ a₀ QtmMove.right r a''))
        (partVec (fun t : Q × A => wL t b' c') (fun t => M.step q a QtmMove.left t.1 t.2))
      = 0 := by
  rw [ip_bilin _ _ _ _]
  simp only [wU_wL]
  rw [sum_single_collapse _ _ _ _ _ _]
  by_cases hK : b = b' ∧ d = c'
  · rw [if_pos hK]
    exact star_sum_eq _ _ (M.wf_rightLeft q₀ a₀ q a a'' c)
  · rw [if_neg hK]

/-- The `wU` superposition over states weighted by fixed-output-symbol right transitions is
orthogonal to the `wS` stay-transition superposition. -/
private theorem ip_wU_wS (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun r : Q => wU r b c d) (fun r => M.step q₀ a₀ QtmMove.right r a''))
        (partVec (fun t : Q × A => wS t b' c') (fun t => M.step q a QtmMove.stay t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun r t => wU_ne_wS r b c d t b' c')

/-- The `wU` superposition over states weighted by fixed-output-symbol right transitions is
orthogonal to the `wR` right-transition superposition. -/
private theorem ip_wU_wR (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A) (q : Q) (a b' c' : A) :
    ip (partVec (fun r : Q => wU r b c d) (fun r => M.step q₀ a₀ QtmMove.right r a''))
        (partVec (fun t : Q × A => wR t b' c') (fun t => M.step q a QtmMove.right t.1 t.2))
      = 0 :=
  ip_zero_disj _ _ _ _ (fun r t => wU_ne_wR r b c d t b' c')

/-- Every `uFamily` vector is orthogonal to every local transition superposition. -/
private theorem ip_uFamily_superp (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A)
    (q : Q) (a b' c' : A) :
    ip (uFamily M q₀ a₀ a'' b c d) (stepSuperposition M q a b' c') = 0 := by
  rw [uFamily_eq M q₀ a₀ a'' b c d, stepSuperposition_eq M q a b' c']
  simp only [ip_add_right]
  rw [ip_wU_wL M q₀ a₀ a'' b c d q a b' c', ip_wU_wS M q₀ a₀ a'' b c d q a b' c',
    ip_wU_wR M q₀ a₀ a'' b c d q a b' c']
  ring

/-- Every head basis vector is orthogonal to every `vFamily` vector. -/
private theorem ip_head_vFamily (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A)
    (q : Q) (a b' c' : A) :
    ip (headBasis q a b' c') (vFamily M q₀ a₀ b c) = 0 := by
  rw [headBasis_eq q a b' c', vFamily_eq M q₀ a₀ b c]
  simp only [ip_add_right]
  rw [ip_ket_parts, ip_ket_parts,
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (Ne.symm (wFS_ne_wH s b c q a b' c'))]; ring),
    Finset.sum_eq_zero (fun s _ => by
      rw [if_neg (Ne.symm (wFR_ne_wH s b c q a b' c'))]; ring)]
  ring

/-- Every head basis vector is orthogonal to every `uFamily` vector. -/
private theorem ip_head_uFamily (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A)
    (q : Q) (a b' c' : A) :
    ip (headBasis q a b' c') (uFamily M q₀ a₀ a'' b c d) = 0 := by
  rw [headBasis_eq q a b' c', uFamily_eq M q₀ a₀ a'' b c d, ip_ket_parts,
    Finset.sum_eq_zero (fun r _ => by
      rw [if_neg (Ne.symm (wU_ne_wH r b c d q a b' c'))]; ring)]

/-- Every local transition superposition is orthogonal to every `vFamily` vector. -/
private theorem ip_superp_vFamily (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A)
    (q : Q) (a b' c' : A) :
    ip (stepSuperposition M q a b' c') (vFamily M q₀ a₀ b c) = 0 := by
  rw [ip_star_swap, ip_vFamily_superp]
  simp

/-- Every local transition superposition is orthogonal to every `uFamily` vector. -/
private theorem ip_superp_uFamily (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A)
    (q : Q) (a b' c' : A) :
    ip (stepSuperposition M q a b' c') (uFamily M q₀ a₀ a'' b c d) = 0 := by
  rw [ip_star_swap, ip_uFamily_superp]
  simp

/-- Each head basis vector has inner product one with itself. -/
private theorem ip_head_head_self (q : Q) (a b c : A) :
    ip (headBasis q a b c) (headBasis q a b c) = 1 := by
  rw [headBasis_eq q a b c, ip_ket_ket, if_pos rfl]

/-- Head basis vectors indexed by distinct state-and-symbol quadruples are orthogonal. -/
private theorem ip_head_head_ne (q q' : Q) (a a' b b' c c' : A)
    (h : (q, a, b, c) ≠ (q', a', b', c')) :
    ip (headBasis q a b c) (headBasis q' a' b' c') = 0 := by
  rw [headBasis_eq q a b c, headBasis_eq q' a' b' c', ip_ket_ket, if_neg]
  intro heq
  obtain ⟨hq, ha, hb, hc⟩ := wH_inj heq
  exact h (quad_eq hq ha hb hc)

end FixFam

/-- For every finite local QTM, there exists a unitary three-cell window matrix satisfying
`GUnitFixesH` and `GUnitSteps`, giving the G-unit existence conclusion of [Yao, Lemma
2][Yao1993]. -/
theorem gUnitExistence : GUnitExistence := by
  intro Q _ _ A _ _ M
  obtain ⟨S, hSunit, hSu, hSorth⟩ :=
    exists_swap (X := GWindow Q A) (ι := Q × A × A × A)
      (fun p => headBasis p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => stepSuperposition M p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => ip_head_head_self p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => ip_superp_self M p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p p' hp => ip_head_head_ne p.1 p'.1 p.2.1 p'.2.1 p.2.2.1 p'.2.2.1 p.2.2.2 p'.2.2.2
        (fun hq => hp (by
          obtain ⟨q, a, b, c⟩ := p
          obtain ⟨q', a', b', c'⟩ := p'
          exact hq)))
      (fun p p' hp => ip_superp_ne M p.1 p'.1 p.2.1 p'.2.1 p.2.2.1 p.2.2.2 p'.2.2.1 p'.2.2.2
        (fun hq => hp (by
          obtain ⟨q, a, b, c⟩ := p
          obtain ⟨q', a', b', c'⟩ := p'
          exact hq)))
      (fun p p' => ip_head_superp M p.1 p'.1 p.2.1 p'.2.1 p.2.2.1 p.2.2.2 p'.2.2.1 p'.2.2.2)
  refine ⟨S, hSunit, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hI
    exact hSorth (Qatlib.Foundations.PureStateMath.Ket z) fun p => ⟨ip_head_ket_typeI z hI p.1 p.2.1 p.2.2.1 p.2.2.2,
      ip_superp_ket_typeI z hI M p.1 p.2.1 p.2.2.1 p.2.2.2⟩
  · intro q₀ a₀ b c
    exact hSorth _ fun p => ⟨ip_head_vFamily M q₀ a₀ b c p.1 p.2.1 p.2.2.1 p.2.2.2,
      ip_superp_vFamily M q₀ a₀ b c p.1 p.2.1 p.2.2.1 p.2.2.2⟩
  · intro q₀ a₀ a'' b c d
    exact hSorth _ fun p => ⟨ip_head_uFamily M q₀ a₀ a'' b c d p.1 p.2.1 p.2.2.1 p.2.2.2,
      ip_superp_uFamily M q₀ a₀ a'' b c d p.1 p.2.1 p.2.2.1 p.2.2.2⟩
  · intro q a b c
    exact hSu (q, a, b, c)

end Qatlib.Foundations.StandardDefs.WindowSim

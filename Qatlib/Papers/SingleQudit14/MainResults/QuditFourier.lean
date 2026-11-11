/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Qudit Fourier core (SingleQudit14)

Gedik--Silva--Çakmak--Karpat--Vidoto--Soares-Pinto--deAzevedo--Fanchini,
*Computational speed-up with a single qudit*, fixed arXiv:1403.5861v3.

This file provides the finite `d`-level qudit Fourier machinery used by the paper's
algorithm (Eq. (7)): the DFT column `qftVec k`, the permutation (oracle) operator
`applyPerm σ`, the inverse DFT `qftInvVec`, and the two structural lemmas that drive
the whole paper:

* a positive cyclic permutation (rotation `j ↦ j + s`) scales the column `qftVec k`
  by the phase `stdAddChar (s * k)` (so it keeps the column, up to a phase);
* a negative cyclic permutation (reflection `j ↦ c - j`) sends `qftVec k` to
  `stdAddChar (c * k)` times the column `qftVec (-k)`.

With `k = 1` these say rotations fix `|ψ_2⟩` up to a global phase while reflections
give `|ψ_d⟩ = qftVec (-1)` up to a global phase — exactly Eq. (7) and the sentence
following it. `qftInvVec` is the adjoint (`U_FT†`) and is computed on basis columns by
character orthogonality, giving back the basis state.

Boundary: this is the ideal, noiseless algebraic layer. States are written without the
common normalisation `1/√d`; every statement below (`... = c • qftVec k`) is invariant
under that common scalar, and the physical measurement outcome is a basis state up to
the same scalar, so the normalisation cancels everywhere and is only noted, not tracked.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.SingleQudit14.MainResults

variable {d : ℕ} [NeZero d]

/-- Paper Eq. (7): the `k`-th (zero-based) column of the qudit Fourier transform,
`(|ψ_{k+1}⟩` up to the normalisation `1/√d`), evaluated on the basis state `|i⟩`.
Concretely `qftVec k i = exp(2πi·(i·k)/d)` via the primitive additive character. -/
def qftVec (k : ZMod d) : ZMod d → ℂ := fun i => ZMod.stdAddChar (i * k)

/-- Every value of the primitive additive character is a nonzero complex number
(a root of unity on the unit circle). -/
lemma stdAddChar_ne_zero (x : ZMod d) : ZMod.stdAddChar (N := d) x ≠ 0 := by
  have hx : ((x.val : ℤ) : ZMod d) = x := by
    push_cast
    exact ZMod.natCast_zmod_val x
  rw [← hx, ZMod.stdAddChar_coe (N := d) (x.val : ℤ)]
  exact Complex.exp_ne_zero _

/-- The computational basis vector `|k⟩` in the single-qudit register `ℂ^d`. -/
def basisVec (k : ZMod d) : ZMod d → ℂ := Pi.single k 1

/-- The oracle operator `U_f` attached to a permutation `f` of the `d` values: it sends
the state vector `v` to `v ∘ f⁻¹`. We parametrise it by `σ = f⁻¹` (the inverse is again
a rotation/reflection in the positive/negative cyclic families), so `applyPerm σ v = v ∘ σ`. -/
def applyPerm (σ : Equiv.Perm (ZMod d)) (v : ZMod d → ℂ) : ZMod d → ℂ := v ∘ σ

/-- The positive cyclic (rotation) permutation `j ↦ j + s` of the `d` values. -/
def rotPerm (s : ZMod d) : Equiv.Perm (ZMod d) where
  toFun j := j + s
  invFun j := j - s
  left_inv j := by simp
  right_inv j := by simp

/-- The negative cyclic (reflection) permutation `j ↦ c - j` of the `d` values. -/
def reflPerm (c : ZMod d) : Equiv.Perm (ZMod d) where
  toFun j := c - j
  invFun j := c - j
  left_inv j := by simp
  right_inv j := by simp

/-- `σ` is a positive cyclic permutation (a rotation of the `d`-cycle). -/
def IsPositiveCyclic (σ : Equiv.Perm (ZMod d)) : Prop := ∃ s : ZMod d, σ = rotPerm s

/-- `σ` is a negative cyclic permutation (a reflection of the `d`-cycle). -/
def IsNegativeCyclic (σ : Equiv.Perm (ZMod d)) : Prop := ∃ c : ZMod d, σ = reflPerm c

/-- The permutation action evaluates by composition with the permutation. -/
@[simp]
lemma applyPerm_apply (σ : Equiv.Perm (ZMod d)) (v : ZMod d → ℂ) (i : ZMod d) :
    applyPerm σ v i = v (σ i) := rfl

/-- A cyclic rotation acts by addition of its shift. -/
@[simp]
lemma rotPerm_apply (s j : ZMod d) : rotPerm s j = j + s := rfl

/-- A reflection subtracts the input from its center. -/
@[simp]
lemma reflPerm_apply (c j : ZMod d) : reflPerm c j = c - j := rfl

/-- Fixed arXiv:1403.5861v3, Eq. (7) + following sentence. A positive cyclic permutation
`j ↦ j + s` scales the Fourier column `|ψ_{k+1}⟩` by the phase `stdAddChar (s * k)`;
in particular (taking `k = 1`) it maps `|ψ_2⟩` onto itself up to a global phase. -/
lemma applyPerm_rot (s k : ZMod d) :
    applyPerm (rotPerm s) (qftVec k) = ZMod.stdAddChar (s * k) • qftVec k := by
  funext i
  simp only [applyPerm, Function.comp_apply, rotPerm_apply, qftVec, Pi.smul_apply, smul_eq_mul]
  rw [add_mul, ZMod.stdAddChar.map_add_eq_mul]
  ring

/-- Fixed arXiv:1403.5861v3, Eq. (7) + following sentence. A negative cyclic permutation
`j ↦ c - j` sends the Fourier column `|ψ_{k+1}⟩` to `stdAddChar (c * k)` times the column
`|ψ_{d-k+1}⟩ = qftVec (-k)`; with `k = 1` and `-1 ≡ d - 1` this is `|ψ_d⟩`. -/
lemma applyPerm_refl (c k : ZMod d) :
    applyPerm (reflPerm c) (qftVec k) = ZMod.stdAddChar (c * k) • qftVec (-k) := by
  funext i
  simp only [applyPerm, Function.comp_apply, reflPerm_apply, qftVec, Pi.smul_apply, smul_eq_mul]
  rw [show (c - i) * k = c * k + i * (-k) by ring, ZMod.stdAddChar.map_add_eq_mul]

/-- The inverse Fourier transform `U_FT†` applied to a state vector: it pairs `v` with the
conjugate character, `(U_FT† v) i = ∑_j exp(-2πi·i·j/d) · v j`. -/
def qftInvVec (v : ZMod d → ℂ) : ZMod d → ℂ :=
  fun i => ∑ j : ZMod d, ZMod.stdAddChar (-(i * j)) * v j

/-- Character orthogonality: the sum of the nontrivial additive character `j ↦ ω^{t·j}`
over all `j` is `0`, while the trivial character (`t = 0`) sums to `d`. -/
lemma sum_stdAddChar_mul (t : ZMod d) :
    (∑ j : ZMod d, ZMod.stdAddChar (t * j)) = if t = 0 then (d : ℂ) else 0 := by
  classical
  have hshift : (∑ j : ZMod d, ZMod.stdAddChar (t * j))
      = ∑ j : ZMod d, AddChar.mulShift (ZMod.stdAddChar (N := d)) t j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [AddChar.mulShift_apply]
  have hiff : AddChar.mulShift (ZMod.stdAddChar (N := d)) t = 0 ↔ t = 0 := by
    constructor
    · intro h
      have h1 : ZMod.stdAddChar (N := d) t = 1 := by
        have := congrFun (congrArg DFunLike.coe h) 1
        simpa [AddChar.mulShift_apply] using this
      have h0 : ZMod.stdAddChar (N := d) (0 : ZMod d) = 1 :=
        (ZMod.stdAddChar (N := d)).map_zero_eq_one
      exact ZMod.injective_stdAddChar (h1.trans h0.symm)
    · rintro rfl
      ext x
      simp
  rw [hshift, AddChar.sum_eq_ite, ZMod.card]
  by_cases ht : t = 0
  · have hm : AddChar.mulShift (ZMod.stdAddChar (N := d)) t = 0 := hiff.mpr ht
    rw [if_pos hm, if_pos ht]
  · have hm : ¬ (AddChar.mulShift (ZMod.stdAddChar (N := d)) t = 0) := fun h => ht (hiff.mp h)
    rw [if_neg hm, if_neg ht]

/-- `U_FT† ∘ U_FT` on a basis column returns `d` times the basis state: the inverse Fourier
transform of `|ψ_{k+1}⟩ = U_FT |k⟩` is (up to the common normalisation) the basis vector
`|k⟩`, by character orthogonality. This is the last gate `U_FT†` of the paper's circuit. -/
lemma qftInvVec_qftVec (k : ZMod d) :
    qftInvVec (qftVec k) = (d : ℂ) • basisVec k := by
  classical
  funext i
  simp only [qftInvVec, qftVec, basisVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have hprod : ∀ j : ZMod d,
      ZMod.stdAddChar (-(i * j)) * ZMod.stdAddChar (j * k) = ZMod.stdAddChar ((k - i) * j) := by
    intro j
    rw [← ZMod.stdAddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hprod]
  rw [sum_stdAddChar_mul]
  by_cases h : k = i
  · subst h
    simp
  · have hki : k - i ≠ 0 := sub_ne_zero.mpr h
    have hik : i ≠ k := fun hc => h hc.symm
    rw [if_neg hki, if_neg hik, mul_zero]

/-- The inverse Fourier transform commutes with scalar multiplication. -/
@[simp]
lemma qftInvVec_smul (c : ℂ) (v : ZMod d → ℂ) :
    qftInvVec (c • v) = c • qftInvVec v := by
  funext i
  simp only [qftInvVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Helper: the dimension `d`, seen in `ℂ`, is nonzero. Used to see that the inverse-DFT
output scalar `d · phase` (the unnormalised inverse transform of a Fourier column) is
nonzero, i.e. the final pointer state is a genuine state, not the zero vector. -/
lemma natCast_ne_zero_complex (n : ℕ) [NeZero n] : (n : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NeZero.ne n)

/-- Helper: distinct basis indices give distinct computational basis vectors `|k⟩`. -/
lemma basisVec_ne_of_ne {a b : ZMod d} (h : a ≠ b) : basisVec a ≠ basisVec b := by
  intro he
  have hb : basisVec b b = 1 := by simp [basisVec, Pi.single_apply]
  have ha : basisVec a b = 0 := by simp [basisVec, Pi.single_apply, h, Ne.symm h]
  rw [he] at ha
  rw [hb] at ha
  exact one_ne_zero ha

/-- Helper: the `0`-component of a computational basis vector `|k⟩` is `0` whenever `k ≠ 0`;
equivalently, measuring `|k⟩` in the `|0⟩` outcome never fires for `k ≠ 0`. -/
lemma basisVec_apply_zero_of_ne {k : ZMod d} (h : k ≠ 0) : basisVec k (0 : ZMod d) = 0 := by
  simp [basisVec, Pi.single_apply, h, Ne.symm h]

/-- For `d ≥ 3` the two outcome labels `1` and `-1` of the algorithm are distinct residues
(so the final pointer states `|1⟩` and `|d-1⟩` are genuinely different, and the algorithm
distinguishes the two parities). Proved by `2 ≡ 0 (mod d) ⟹ d ∣ 2` against `d ≥ 3`. -/
lemma one_ne_neg_one (hd : 3 ≤ d) : (1 : ZMod d) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod d) = 0 := by
    have hthis : (1 : ZMod d) + 1 = (-1 : ZMod d) + 1 := congrArg (fun x => x + 1) h
    have hz : (-1 : ZMod d) + 1 = 0 := by ring
    have hc : (2 : ZMod d) = (1 : ZMod d) + 1 := by ring
    rw [hc, hthis, hz]
  have hdvd : d ∣ 2 := (ZMod.natCast_eq_zero_iff 2 d).mp h2
  have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- The rotation family `s ↦ rotPerm s` is injective: distinct shifts give distinct
permutations of the `d`-cycle. -/
lemma rotPerm_injective : Function.Injective (rotPerm : ZMod d → Equiv.Perm (ZMod d)) := by
  intro s t h
  have hh := congrFun (congrArg (fun e : Equiv.Perm (ZMod d) => (e : ZMod d → ZMod d)) h) 0
  simpa using hh

/-- The reflection family `c ↦ reflPerm c` is injective: distinct reflections of the
`d`-cycle are distinct permutations. -/
lemma reflPerm_injective : Function.Injective (reflPerm : ZMod d → Equiv.Perm (ZMod d)) := by
  intro s t h
  have hh := congrFun (congrArg (fun e : Equiv.Perm (ZMod d) => (e : ZMod d → ZMod d)) h) 0
  simpa using hh

/-- For `d ≥ 3` no permutation of the `d`-cycle is simultaneously a rotation `j ↦ j + s`
(positive cyclic) and a reflection `j ↦ c - j` (negative cyclic); so the two families of
cyclic permutations are disjoint. -/
lemma rotPerm_ne_reflPerm (hd : 3 ≤ d) (s c : ZMod d) : rotPerm s ≠ reflPerm c := by
  intro h
  have h0 : s = c := by
    have hh := congrFun (congrArg (fun e : Equiv.Perm (ZMod d) => (e : ZMod d → ZMod d)) h) 0
    simpa using hh
  have h1 : (1 : ZMod d) + s = c - 1 := by
    have hh := congrFun (congrArg (fun e : Equiv.Perm (ZMod d) => (e : ZMod d → ZMod d)) h) 1
    simpa using hh
  rw [h0] at h1
  have hc : (1 : ZMod d) = -1 := by linear_combination h1
  exact one_ne_neg_one hd hc

end Qatlib.Papers.SingleQudit14.MainResults

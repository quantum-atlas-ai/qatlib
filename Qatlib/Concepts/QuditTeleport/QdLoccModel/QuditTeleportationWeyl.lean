/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationBranchMarginal

/-!
# Weyl orthogonality and teleportation branch geometry

`clause4Aux_weyl` and `clause4Aux_hs` provide finite Weyl operators and their Hilbert–Schmidt
pairing. Character sums prove orthogonality, and the teleportation branch Kraus family has Gram
matrix `1 / n` times the identity.

The remaining results establish normalization and counting consequences for maximally entangled
resources, together with positive semidefinite spectral decompositions and square roots. These
results develop resource and communication properties of teleportation
[BennettEtAl1993Teleportation]. Matrix positivity and finite-dimensional operator methods are
treated in [Watrous2018].

## Main statements

* `clause4Aux_weyl_hs`: The Hilbert–Schmidt pairing of two Weyl operators is `n` when both
  labels agree and zero otherwise.
* `clause4Aux_branchKraus_gramMatrix`: The Hilbert–Schmidt Gram matrix of the qudit branch Kraus
  family equals `(1 / n) • 1`.
* `clause4Aux_me_counting`: For orthonormal-family resources in nonzero dimension, perfect
  teleportation with unitary corrections gives the outcome, alphabet-bit, and injective-code
  communication bounds.
* `clause4Aux_psd_spectral_sqrt`: A positive semidefinite matrix possesses a positive
  semidefinite Hermitian square root.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel
open Matrix
open scoped BigOperators ComplexOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

/-- The Weyl operator `quditX n b * quditZ n a` with shift `b` and phase parameter `a`. -/
noncomputable def clause4Aux_weyl (n : ℕ) [NeZero n] (a b : ZMod n) : Operator n :=
  quditX n b * quditZ n a

/-- A Weyl matrix entry is its additive-character phase when the row index is the column index
shifted by `b`, and zero otherwise. -/
theorem clause4Aux_weyl_apply (n : ℕ) [NeZero n] (a b : ZMod n) (k j : Fin n) :
    clause4Aux_weyl n a b k j =
      if (ZMod.finEquiv n) k = (ZMod.finEquiv n) j + b
        then ZMod.stdAddChar (a * (ZMod.finEquiv n) j) else 0 :=
  quditXZ_entry n b a k j

/-- The Hilbert–Schmidt pairing obtained by summing `star (A i j) * B i j` over all matrix
entries. -/
noncomputable def clause4Aux_hs {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, star (A i j) * B i j

/-- Complex conjugation by `star` agrees with `starRingEnd ℂ`. -/
theorem clause4Aux_star_eq_starRingEnd (z : ℂ) : star z = (starRingEnd ℂ) z := rfl

/-- Conjugating the standard additive character at `t` gives its value at `-t`. -/
theorem clause4Aux_star_stdAddChar {n : ℕ} [NeZero n] (t : ZMod n) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) :=
  conj_stdAddChar t

/-- Summing a constant over the unique preimage of `c` under a finite equivalence yields that
constant. -/
private theorem clause4Aux_sum_ite_const {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (c : β) (s : ℂ) :
    ∑ i : α, (if e i = c then s else 0) = s := by
  have h : ∑ i : α, (if e i = c then s else 0) = ∑ t : β, (if t = c then s else 0) :=
    e.sum_comp (fun t : β => if t = c then s else 0)
  rw [h, Finset.sum_ite_eq']
  simp

/-- The inner product of two Weyl columns vanishes unless their shifts agree, and otherwise
equals the product of their conjugate and ordinary phase factors. -/
theorem clause4Aux_weyl_col_sum (n : ℕ) [NeZero n] (a a' b b' : ZMod n) (j : Fin n) :
    ∑ i : Fin n, star (clause4Aux_weyl n a b i j) * clause4Aux_weyl n a' b' i j =
      if (ZMod.finEquiv n) j + b = (ZMod.finEquiv n) j + b'
        then star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
          * ZMod.stdAddChar (a' * (ZMod.finEquiv n) j)
      else 0 := by
  classical
  have hA : ∀ i : Fin n, star (clause4Aux_weyl n a b i j) =
      if (ZMod.finEquiv n) i = (ZMod.finEquiv n) j + b
        then star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j)) else 0 := by
    intro i
    rw [clause4Aux_weyl_apply]
    split_ifs <;> simp
  have hB : ∀ i : Fin n, clause4Aux_weyl n a' b' i j =
      if (ZMod.finEquiv n) i = (ZMod.finEquiv n) j + b'
        then ZMod.stdAddChar (a' * (ZMod.finEquiv n) j) else 0 := by
    intro i
    exact clause4Aux_weyl_apply n a' b' i j
  simp only [hA, hB]
  set c1 : ZMod n := (ZMod.finEquiv n) j + b
  set c2 : ZMod n := (ZMod.finEquiv n) j + b'
  set s1 : ℂ := star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
  set s2 : ℂ := ZMod.stdAddChar (a' * (ZMod.finEquiv n) j)
  by_cases hb : c1 = c2
  · rw [if_pos hb]
    have hbb : ∀ i : Fin n,
        (if (ZMod.finEquiv n) i = c1 then s1 else 0) *
          (if (ZMod.finEquiv n) i = c2 then s2 else 0)
        = if (ZMod.finEquiv n) i = c1 then s1 * s2 else 0 := by
      intro i
      by_cases hi : (ZMod.finEquiv n) i = c1
      · rw [if_pos hi, if_pos (hi.trans hb), if_pos hi]
      · rw [if_neg hi, if_neg (fun he => hi (he.trans hb.symm)), if_neg hi, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => hbb i)]
    exact clause4Aux_sum_ite_const (ZMod.finEquiv n).toEquiv c1 (s1 * s2)
  · rw [if_neg hb]
    have hz : ∀ i : Fin n,
        (if (ZMod.finEquiv n) i = c1 then s1 else 0) *
          (if (ZMod.finEquiv n) i = c2 then s2 else 0) = 0 := by
      intro i
      by_cases hi : (ZMod.finEquiv n) i = c1
      · by_cases hi' : (ZMod.finEquiv n) i = c2
        · exact (hb (hi.symm.trans hi')).elim
        · rw [if_pos hi, if_neg hi', mul_zero]
      · rw [if_neg hi, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero]

/-- The inner product of two phase-character columns is `n` when their phase parameters agree
and zero otherwise. -/
theorem clause4Aux_weyl_char_sum (n : ℕ) [NeZero n] (a a' : ZMod n) :
    ∑ j : Fin n, star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
        * ZMod.stdAddChar (a' * (ZMod.finEquiv n) j)
      = if a = a' then (n : ℂ) else 0 := by
  classical
  have hconj : ∀ j : Fin n,
      star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
        * ZMod.stdAddChar (a' * (ZMod.finEquiv n) j)
      = ZMod.stdAddChar ((a' - a) * (ZMod.finEquiv n) j) := by
    intro j
    rw [clause4Aux_star_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => hconj j)]
  have htr : ∑ j : Fin n, ZMod.stdAddChar ((a' - a) * (ZMod.finEquiv n) j)
      = ∑ t : ZMod n, ZMod.stdAddChar ((a' - a) * t) :=
    (ZMod.finEquiv n).toEquiv.sum_comp
      (fun t : ZMod n => ZMod.stdAddChar ((a' - a) * t))
  rw [htr, sum_stdAddChar_mul]
  by_cases ha : a = a'
  · subst ha
    rw [if_pos (sub_self a), if_pos rfl]
  · rw [if_neg (fun he => ha (sub_eq_zero.mp he).symm), if_neg ha]

/-- The Hilbert–Schmidt pairing of two Weyl operators is `n` when both labels agree and zero
otherwise. -/
theorem clause4Aux_weyl_hs (n : ℕ) [NeZero n] (a a' b b' : ZMod n) :
    clause4Aux_hs (clause4Aux_weyl n a b) (clause4Aux_weyl n a' b') =
      if a = a' ∧ b = b' then (n : ℂ) else 0 := by
  classical
  unfold clause4Aux_hs
  rw [Finset.sum_comm]
  simp only [clause4Aux_weyl_col_sum]
  by_cases hb : b = b'
  · subst hb
    have hsum : ∑ j : Fin n,
        (if (ZMod.finEquiv n) j + b = (ZMod.finEquiv n) j + b
          then star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
            * ZMod.stdAddChar (a' * (ZMod.finEquiv n) j) else 0)
        = ∑ j : Fin n, star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
            * ZMod.stdAddChar (a' * (ZMod.finEquiv n) j) :=
      Finset.sum_congr rfl (fun j _ => if_pos rfl)
    rw [hsum, clause4Aux_weyl_char_sum]
    by_cases ha : a = a' <;> simp [ha]
  · have hz : ∀ j : Fin n,
        (if (ZMod.finEquiv n) j + b = (ZMod.finEquiv n) j + b'
          then star (ZMod.stdAddChar (a * (ZMod.finEquiv n) j))
            * ZMod.stdAddChar (a' * (ZMod.finEquiv n) j) else 0) = 0 := by
      intro j
      rw [if_neg (fun he => hb (add_left_cancel he))]
    rw [Finset.sum_congr rfl (fun j _ => hz j), Finset.sum_const_zero]
    rw [if_neg (fun h : a = a' ∧ b = b' => hb h.2)]

/-- The Hilbert–Schmidt pairing of a Weyl operator with itself is `n`. -/
theorem clause4Aux_weyl_hs_self (n : ℕ) [NeZero n] (a b : ZMod n) :
    clause4Aux_hs (clause4Aux_weyl n a b) (clause4Aux_weyl n a b) = (n : ℂ) := by
  rw [clause4Aux_weyl_hs]
  simp

/-- Weyl operators with distinct phase-shift labels are orthogonal for the Hilbert–Schmidt
pairing. -/
theorem clause4Aux_weyl_hs_cross (n : ℕ) [NeZero n] (a a' b b' : ZMod n)
    (h : a ≠ a' ∨ b ≠ b') :
    clause4Aux_hs (clause4Aux_weyl n a b) (clause4Aux_weyl n a' b') = 0 := by
  rw [clause4Aux_weyl_hs]
  apply if_neg
  rintro ⟨ha, hb⟩
  rcases h with h | h
  · exact h ha
  · exact h hb

/-- The entrywise Hilbert–Schmidt pairing equals `trace (Aᴴ * B)`. -/
theorem clause4Aux_hs_eq_trace {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) :
    clause4Aux_hs A B = Matrix.trace (A.conjTranspose * B) := by
  classical
  unfold clause4Aux_hs Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- Every Weyl operator `clause4Aux_weyl n a b` is unitary. -/
theorem clause4Aux_weyl_unitary (n : ℕ) [NeZero n] (a b : ZMod n) :
    clause4Aux_weyl n a b ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  (Matrix.unitaryGroup (Fin n) ℂ).mul_mem (quditX_unitary n b) (quditZ_unitary n a)

/-- Scaling the first argument of the Hilbert–Schmidt pairing by `c` scales the result by `star
c`. -/
theorem clause4Aux_hs_smul_left {ι : Type} [Fintype ι] (c : ℂ) (A B : Matrix ι ι ℂ) :
    clause4Aux_hs (c • A) B = star c * clause4Aux_hs A B := by
  classical
  unfold clause4Aux_hs
  have h : ∀ i j : ι,
      star ((c • A) i j) * B i j = star c * (star (A i j) * B i j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, star_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))]
  have e1 : (∑ i : ι, ∑ j : ι, star c * (star (A i j) * B i j))
      = (∑ i : ι, star c * ∑ j : ι, star (A i j) * B i j) :=
    Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ (fun j => star (A i j) * B i j) _).symm)
  have e2 : (∑ i : ι, star c * ∑ j : ι, star (A i j) * B i j)
      = star c * ∑ i : ι, ∑ j : ι, star (A i j) * B i j :=
    (Finset.mul_sum _ (fun i => ∑ j : ι, star (A i j) * B i j) _).symm
  rw [e1, e2]

/-- Scaling the second argument of the Hilbert–Schmidt pairing by `c` scales the result by `c`. -/
theorem clause4Aux_hs_smul_right {ι : Type} [Fintype ι] (c : ℂ) (A B : Matrix ι ι ℂ) :
    clause4Aux_hs A (c • B) = c * clause4Aux_hs A B := by
  classical
  unfold clause4Aux_hs
  have h : ∀ i j : ι,
      star (A i j) * (c • B) i j = c * (star (A i j) * B i j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))]
  have e1 : (∑ i : ι, ∑ j : ι, c * (star (A i j) * B i j))
      = (∑ i : ι, c * ∑ j : ι, star (A i j) * B i j) :=
    Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ (fun j => star (A i j) * B i j) _).symm)
  have e2 : (∑ i : ι, c * ∑ j : ι, star (A i j) * B i j)
      = c * ∑ i : ι, ∑ j : ι, star (A i j) * B i j :=
    (Finset.mul_sum _ (fun i => ∑ j : ι, star (A i j) * B i j) _).symm
  rw [e1, e2]

/-- A qudit teleportation branch Kraus operator is `1 / n` times the Weyl operator with negative
first outcome coordinate as phase and second coordinate as shift. -/
theorem clause4Aux_branchKraus_weyl (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    quditBranchKraus n o = (1 / (n : ℂ)) •
      clause4Aux_weyl n (-((ZMod.finEquiv n) o.1)) ((ZMod.finEquiv n) o.2) := by
  rw [quditBranchKraus_formula]
  rfl

/-- The complex number `1 / n` is fixed by conjugation. -/
theorem clause4Aux_star_inv_natCast (n : ℕ) : star (1 / (n : ℂ)) = 1 / (n : ℂ) := by
  change (starRingEnd ℂ) (1 / (n : ℂ)) = _
  rw [map_div₀, map_one, map_natCast]

/-- The Hilbert–Schmidt pairing of two teleportation branch Kraus operators is `1 / n` for equal
outcomes and zero otherwise. -/
theorem clause4Aux_branchKraus_hs (n : ℕ) [NeZero n] (o o' : Fin n × Fin n) :
    clause4Aux_hs (quditBranchKraus n o) (quditBranchKraus n o') =
      if o = o' then 1 / (n : ℂ) else 0 := by
  classical
  rw [clause4Aux_branchKraus_weyl, clause4Aux_branchKraus_weyl]
  rw [clause4Aux_hs_smul_left, clause4Aux_hs_smul_right, clause4Aux_star_inv_natCast]
  rw [clause4Aux_weyl_hs]
  have hlab : ((-(ZMod.finEquiv n) o.1) = (-(ZMod.finEquiv n) o'.1) ∧
      (ZMod.finEquiv n) o.2 = (ZMod.finEquiv n) o'.2) ↔ o = o' := by
    constructor
    · rintro ⟨h1, h2⟩
      have ha : (ZMod.finEquiv n) o.1 = (ZMod.finEquiv n) o'.1 := neg_inj.mp h1
      exact Prod.ext ((ZMod.finEquiv n).injective ha) ((ZMod.finEquiv n).injective h2)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  by_cases ho : o = o'
  · subst ho
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    field_simp
  · rw [if_neg (fun h => ho (hlab.mp h)), if_neg ho]
    rw [mul_zero, mul_zero]

/-- The Hilbert–Schmidt Gram matrix of the qudit branch Kraus family equals `(1 / n) • 1`. -/
theorem clause4Aux_branchKraus_gramMatrix (n : ℕ) [NeZero n] :
    (fun o o' : Fin n × Fin n => clause4Aux_hs (quditBranchKraus n o) (quditBranchKraus n o'))
      = (1 / (n : ℂ)) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := by
  funext o o'
  show clause4Aux_hs (quditBranchKraus n o) (quditBranchKraus n o')
    = (1 / (n : ℂ)) * (if o = o' then 1 else 0)
  rw [clause4Aux_branchKraus_hs]
  by_cases h : o = o'
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]
open Matrix
open scoped BigOperators ComplexOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff

/-- The product of a complex number with its conjugate equals its squared norm, coerced to `ℂ`. -/
private theorem clause4Aux_normSq_coe (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h := Complex.normSq_eq_conj_mul_self (z := z)
  rw [Complex.normSq_eq_norm_sq] at h
  refine Eq.trans ?_ h.symm
  exact (mul_comm _ _).symm

/-- A maximally entangled resource built from two orthonormal families in nonzero dimension is
normalized. -/
theorem clause4Aux_me_normalized (n : ℕ) [NeZero n] (u v : Fin n → QState (Fin n))
    (hu : QuditOrthonormalFamily n u) (hv : QuditOrthonormalFamily n v) :
    Normalized (quditMaxEntResource n u v) := by
  classical
  set Ψ : QState (Fin n × Fin n) := quditMaxEntResource n u v
  have hm : PartialTrace (outerProduct Ψ) = (1 / (n : ℂ)) • (1 : Operator n) :=
    qudit_maxEnt_first_marginal hu hv
  have htrMarg : Matrix.trace (PartialTrace (outerProduct Ψ)) = 1 := by
    rw [hm, Matrix.trace_smul, Matrix.trace_one]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Fintype.card_fin, smul_eq_mul]
    field_simp
  have hterm : ∀ p : Fin n × Fin n,
      outerProduct Ψ p p = ((‖Ψ p‖ ^ 2 : ℝ) : ℂ) := by
    intro p
    rw [outerProduct_apply]
    exact clause4Aux_normSq_coe (Ψ p)
  have htrOuter : Matrix.trace (outerProduct Ψ)
      = ((∑ p : Fin n × Fin n, ‖Ψ p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    show (∑ p : Fin n × Fin n, outerProduct Ψ p p)
      = ((∑ p : Fin n × Fin n, ‖Ψ p‖ ^ 2 : ℝ) : ℂ)
    rw [Finset.sum_congr rfl (fun p _ => hterm p)]
    exact (Complex.ofReal_sum _ (fun p : Fin n × Fin n => ‖Ψ p‖ ^ 2)).symm
  have key : ((∑ p : Fin n × Fin n, ‖Ψ p‖ ^ 2 : ℝ) : ℂ) = 1 :=
    htrOuter.symm.trans ((trace_partialTrace (outerProduct Ψ)).symm.trans htrMarg)
  show ∑ i, ‖Ψ i‖ ^ 2 = 1
  exact_mod_cast key

/-- Perfect teleportation with unitary corrections and a resource of the form
`quditMaxEntResource` in nonzero dimension requires at least `n²` outcomes. -/
theorem clause4Aux_me_card_le {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n)
    (u v : Fin n → QState (Fin n))
    (hU : QdLoccUnitaryCorr P U)
    (hperf : QdLoccPerfect P (outerProduct (quditMaxEntResource n u v))) :
    n * n ≤ Fintype.card κ :=
  qdCard_le_of_perfect P U hU (quditMaxEntResource n u v) hperf

/-- For orthonormal-family resources in nonzero dimension, perfect teleportation with unitary
corrections gives the outcome, alphabet-bit, and injective-code communication bounds. -/
theorem clause4Aux_me_counting {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n)
    (u v : Fin n → QState (Fin n))
    (hu : QuditOrthonormalFamily n u) (hv : QuditOrthonormalFamily n v)
    (hU : QdLoccUnitaryCorr P U)
    (hperf : QdLoccPerfect P (outerProduct (quditMaxEntResource n u v))) :
    n * n ≤ Fintype.card κ ∧ n * n ≤ 2 ^ qdMessageBits κ ∧
      (Function.Injective P.msgCode → n * n ≤ 2 ^ (qdCommCost P + 1)) := by
  have hnorm : Normalized (quditMaxEntResource n u v) := clause4Aux_me_normalized n u v hu hv
  have h := clause4_clause2 n κ _ P U (quditMaxEntResource n u v) hnorm hU hperf
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- A positive semidefinite matrix has a unitary spectral decomposition with nonnegative real
diagonal entries. -/
theorem clause4Aux_psd_spectral_decomp {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : Matrix ι ι ℂ) (hω : ω.PosSemidef) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ),
      (∀ i, 0 ≤ d i) ∧
        ω = (U : Matrix ι ι ℂ) * (diagonal fun i => (d i : ℂ)) * (U : Matrix ι ι ℂ)ᴴ := by
  refine ⟨hω.1.eigenvectorUnitary, hω.1.eigenvalues, fun i => hω.eigenvalues_nonneg i, ?_⟩
  have hdecomp : ω = Unitary.conjStarAlgAut ℂ _ hω.1.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hω.1.eigenvalues)) := hω.1.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hdecomp
  exact hdecomp

/-- A positive semidefinite matrix possesses a positive semidefinite Hermitian square root. -/
theorem clause4Aux_psd_spectral_sqrt {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : Matrix ι ι ℂ) (hω : ω.PosSemidef) :
    ∃ S : Matrix ι ι ℂ, S * S = ω ∧ S.conjTranspose = S ∧ S.PosSemidef := by
  classical
  obtain ⟨U, d, hd, hωeq⟩ := clause4Aux_psd_spectral_decomp ω hω
  set W : Matrix ι ι ℂ := (U : Matrix ι ι ℂ) * (diagonal fun i => (Real.sqrt (d i) : ℂ))
  set S : Matrix ι ι ℂ := W * (U : Matrix ι ι ℂ)ᴴ
  have hW : W = (U : Matrix ι ι ℂ) * (diagonal fun i => (Real.sqrt (d i) : ℂ)) := rfl
  refine ⟨S, ?_, ?_, ?_⟩
  · have hUU : (U : Matrix ι ι ℂ)ᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff'.mp U.property)
    have hdiag : (diagonal fun i => (Real.sqrt (d i) : ℂ))
        * (diagonal fun i => (Real.sqrt (d i) : ℂ))
        = (diagonal fun i => (d i : ℂ)) := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd i)]
    have hWU : (U : Matrix ι ι ℂ)ᴴ * W = (diagonal fun i => (Real.sqrt (d i) : ℂ)) := by
      rw [hW, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    have h1 : S * S = W * ((U : Matrix ι ι ℂ)ᴴ * W) * (U : Matrix ι ι ℂ)ᴴ := by
      show (W * (U : Matrix ι ι ℂ)ᴴ) * (W * (U : Matrix ι ι ℂ)ᴴ) = _
      rw [Matrix.mul_assoc W ((U : Matrix ι ι ℂ)ᴴ) (W * (U : Matrix ι ι ℂ)ᴴ)]
      rw [← Matrix.mul_assoc ((U : Matrix ι ι ℂ)ᴴ) W ((U : Matrix ι ι ℂ)ᴴ)]
      rw [← Matrix.mul_assoc W (((U : Matrix ι ι ℂ)ᴴ) * W) ((U : Matrix ι ι ℂ)ᴴ)]
    rw [h1, hWU]
    calc W * (diagonal fun i => (Real.sqrt (d i) : ℂ)) * (U : Matrix ι ι ℂ)ᴴ
        = (U : Matrix ι ι ℂ) * (diagonal fun i => (d i : ℂ)) * (U : Matrix ι ι ℂ)ᴴ := by
          rw [hW, Matrix.mul_assoc (U : Matrix ι ι ℂ)
            (diagonal fun i => (Real.sqrt (d i) : ℂ)) (diagonal fun i => (Real.sqrt (d i) : ℂ)),
            hdiag]
      _ = ω := hωeq.symm
  · have hdiagStar : (diagonal fun i => (Real.sqrt (d i) : ℂ))ᴴ
        = (diagonal fun i => (Real.sqrt (d i) : ℂ)) := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    show (W * (U : Matrix ι ι ℂ)ᴴ).conjTranspose = W * (U : Matrix ι ι ℂ)ᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hW,
      Matrix.conjTranspose_mul, hdiagStar, Matrix.mul_assoc]
  · have hdiag : ((diagonal fun i => (Real.sqrt (d i) : ℂ)) : Matrix ι ι ℂ).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i
      exact Complex.zero_le_real.mpr (Real.sqrt_nonneg (d i))
    have hunit : IsUnit (U : Matrix ι ι ℂ) := Unitary.isUnit_coe
    have hS : S = (U : Matrix ι ι ℂ)
        * (diagonal fun i => (Real.sqrt (d i) : ℂ)) * (U : Matrix ι ι ℂ)ᴴ := by
      show W * (U : Matrix ι ι ℂ)ᴴ = _
      rw [hW]
    rw [hS, ← Matrix.star_eq_conjTranspose]
    exact hunit.posSemidef_star_right_conjugate_iff.mpr hdiag
end Qatlib.Concepts.QuditTeleport.QdLoccModel

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedStat
import Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundOriginalContracts

/-!
# Proofs of restricted teleportation communication bounds

The results prove `CommBoundRestricted` by showing that distinct teleportation outcomes cannot
share a correction in an exact protocol with unitary corrections. Scalar Kraus decompositions
and projective distinctions between Weyl operators provide the qudit argument.

Explicit two-label recovery examples disprove the legacy injectivity contracts for unrestricted
correction matrices. The contracts address the classical communication requirement of
teleportation [BennettEtAl1993Teleportation].

## Main statements

* `comm_kraus_scalar_of_identity`: If a finite sum of Kraus conjugations is a scalar multiple of
  the identity map, each Kraus operator is a scalar multiple of the identity matrix.
* `commBoundMessageInjectiveQudit`: Exact qudit recovery with unitary corrections forces an
  injective message assignment and at least `n²` message labels.
* `commBoundRestricted`: The qudit and Bell merged-branch impossibility and unitary
  message-injectivity contracts hold. These formalize restricted communication bounds for
  teleportation [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.AbelianDecoders.FourierSupport
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.CommLowerBound

open Matrix

/-- There exist a noninjective two-label message map and correction matrices whose summed Bell
branches recover every input operator. -/
theorem comm_bound_bell_two_label_recovery :
    ∃ (m : Bool × Bool → Bool) (Cm : Bool → Operator 2),
      (∀ ρ : Operator 2, (∑ o : Bool × Bool,
        conjBranch (Cm (m o) * teleportBranchKraus o) ρ) = ρ) ∧
      ¬Function.Injective m := by
  classical
  let m (o : Bool × Bool) := if o = (false, false) then true else false
  let Cm (b : Bool) : Operator 2 := if b then (2 : ℂ) • teleportCorrection (false, false) else 0
  have hselected : Cm (m (false, false)) * teleportBranchKraus (false, false) = 1 := by
    dsimp [Cm, m]
    rw [Matrix.smul_mul, (bell_pauli_corrections (false, false)).2, smul_smul]
    norm_num
  refine ⟨m, Cm, ?_, ?_⟩
  · intro ρ
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    rw [hselected]
    simp [m, Cm]
  · intro h
    have he := h (show m (false, true) = m (true, false) by decide)
    have := congrArg Prod.fst he
    contradiction

/-- The legacy Bell message-injectivity contract fails for unrestricted correction matrices. -/
theorem not_commBoundMessageInjectiveBell : ¬CommBoundMessageInjectiveBellLegacy := by
  intro h
  obtain ⟨m, Cm, hr, hm⟩ := comm_bound_bell_two_label_recovery
  exact hm (h Bool m Cm hr).1

/-- For dimension two, there exist a noninjective two-label map and correction matrices whose
summed qudit branches recover every input operator. -/
theorem comm_bound_qudit_two_label_recovery :
    ∃ (m : Fin 2 × Fin 2 → Bool) (Cm : Bool → Operator 2),
      (∀ ρ : Operator 2, (∑ o : Fin 2 × Fin 2,
        conjBranch (Cm (m o) * quditBranchKraus 2 o) ρ) = ρ) ∧
      ¬Function.Injective m := by
  classical
  let m (o : Fin 2 × Fin 2) := if o = (0, 0) then true else false
  let Cm (b : Bool) : Operator 2 := if b then (2 : ℂ) • quditCorrection 2 (0, 0) else 0
  have hselected : Cm (m (0, 0)) * quditBranchKraus 2 (0, 0) = 1 := by
    dsimp [Cm, m]
    rw [Matrix.smul_mul, quditCorrection_cancel, smul_smul]
    norm_num
  refine ⟨m, Cm, ?_, ?_⟩
  · intro ρ
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hselected]
    simp [m, Cm]
  · intro h
    have he := h (show m (0, 1) = m (1, 0) by decide)
    have := congrArg Prod.fst he
    norm_num at this

/-- The legacy qudit message-injectivity contract fails for unrestricted correction matrices. -/
theorem not_commBoundMessageInjectiveQudit : ¬CommBoundMessageInjectiveQuditLegacy := by
  intro h
  obtain ⟨m, Cm, hr, hm⟩ := comm_bound_qudit_two_label_recovery
  exact hm (h 2 Bool m Cm hr).1

/-- The two-dimensional matrix with zero diagonal and unit off-diagonal entries. -/
private def commBellX : Operator 2 := fun i j => if i = j then 0 else 1

/-- The two-dimensional diagonal matrix with diagonal entries `1` and `-1`. -/
private def commBellZ : Operator 2 := fun i j => if i = j then (if i = 0 then 1 else -1) else 0

/-- A Bell branch sends `commBellX` to one quarter of itself, with sign determined by the first
outcome bit. -/
private theorem comm_bell_conj_x (o : Bool × Bool) :
    conjBranch (teleportBranchKraus o) commBellX =
      (if o.1 then (-1 / 4 : ℂ) else 1 / 4) • commBellX := by
  rw [bell_decoded_branch_operators.2]
  ext i j
  rcases o with ⟨a, b⟩
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [conjBranch_apply, commBellX, relabelGate, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_bool,
      Matrix.conjTranspose_apply, Matrix.smul_apply, PauliX, PauliZ, permMatrix,
      Matrix.one_apply, Matrix.diagonal_apply, boolEquivFin2, RCLike.star_def]

/-- A Bell branch sends `commBellZ` to one quarter of itself, with sign determined by the second
outcome bit. -/
private theorem comm_bell_conj_z (o : Bool × Bool) :
    conjBranch (teleportBranchKraus o) commBellZ =
      (if o.2 then (-1 / 4 : ℂ) else 1 / 4) • commBellZ := by
  rw [bell_decoded_branch_operators.2]
  ext i j
  rcases o with ⟨a, b⟩
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [conjBranch_apply, commBellZ, relabelGate, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_bool,
      Matrix.conjTranspose_apply, Matrix.smul_apply, PauliX, PauliZ, permMatrix,
      Matrix.one_apply, Matrix.diagonal_apply, boolEquivFin2, RCLike.star_def]

/-- If two uncorrected Bell branches cancel on `P`, their sum still vanishes after applying any
common correction `C`. -/
private theorem comm_merged_bell_zero (o o' : Bool × Bool) (C : Operator 2) (P : Operator 2)
    (hP : conjBranch (teleportBranchKraus o) P + conjBranch (teleportBranchKraus o') P = 0) :
    mergedBellBranch o o' C P = 0 := by
  have he : mergedBellBranch o o' C P = C *
      (conjBranch (teleportBranchKraus o) P + conjBranch (teleportBranchKraus o') P) * Cᴴ := by
    simp only [mergedBellBranch, LinearMap.add_apply, conjBranch_apply,
      Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [he, hP, Matrix.mul_zero, Matrix.zero_mul]

/-- Distinct Bell outcomes cannot be merged under one correction to obtain half the identity map
on every finite extension. -/
theorem commBoundMergeNoGoBell : CommBoundMergeNoGoBell := by
  intro o o' hoo C
  by_cases ha : o.1 = o'.1
  · have hP : conjBranch (teleportBranchKraus o) commBellZ +
        conjBranch (teleportBranchKraus o') commBellZ = 0 := by
      rw [comm_bell_conj_z, comm_bell_conj_z, ← add_smul]
      rcases o with ⟨a, b⟩
      rcases o' with ⟨a', b'⟩
      cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all <;> norm_num
    have hm := comm_merged_bell_zero o o' C commBellZ hP
    let X : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ := fun i j => commBellZ i.1 j.1
    have ht : tensorLeft (mergedBellBranch o o' C) X = 0 := by
      ext i j
      change mergedBellBranch o o' C commBellZ i.1 j.1 = 0
      rw [hm]
      rfl
    refine ⟨1, X, ?_⟩
    rw [ht]
    intro h
    have he := congrArg (fun M => M (0, 0) (0, 0)) h
    norm_num [X, commBellZ, Matrix.smul_apply] at he
  · have hP : conjBranch (teleportBranchKraus o) commBellX +
        conjBranch (teleportBranchKraus o') commBellX = 0 := by
      rw [comm_bell_conj_x, comm_bell_conj_x, ← add_smul]
      cases he : o.1 <;> cases he' : o'.1 <;> simp_all <;> norm_num
    have hm := comm_merged_bell_zero o o' C commBellX hP
    let X : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ := fun i j => commBellX i.1 j.1
    have ht : tensorLeft (mergedBellBranch o o' C) X = 0 := by
      ext i j
      change mergedBellBranch o o' C commBellX i.1 j.1 = 0
      rw [hm]
      rfl
    refine ⟨1, X, ?_⟩
    rw [ht]
    intro h
    have he := congrArg (fun M => M (0, 0) (1, 0)) h
    norm_num [X, commBellX, Matrix.smul_apply] at he

/-- The matrix unit with its only nonzero entry equal to one at row `p` and column `q`. -/
private def commMatrixUnit {n : ℕ} (p q : Fin n) : Operator n :=
  fun a b => if a = p ∧ b = q then 1 else 0

/-- Conjugation of the matrix unit at `(p, q)` by `A` has entry `A a p * star (A b q)` at `(a,
b)`. -/
private theorem comm_conj_matrix_unit {n : ℕ} (A : Operator n) (p q a b : Fin n) :
    conjBranch A (commMatrixUnit p q) a b = A a p * star (A b q) := by
  simp [commMatrixUnit, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ite_and, mul_ite, ite_mul]

/-- If a finite sum of Kraus conjugations is a scalar multiple of the identity map, each Kraus
operator is a scalar multiple of the identity matrix. -/
theorem comm_kraus_scalar_of_identity {n : ℕ} [NeZero n] {ι : Type} [Fintype ι]
    (A : ι → Operator n) (c : ℂ)
    (h : ∀ ρ : Operator n, (∑ w, conjBranch (A w) ρ) = c • ρ) :
    ∀ w, ∃ z : ℂ, A w = z • (1 : Operator n) := by
  classical
  have hcoeff (p q a b : Fin n) :
      (∑ w, A w a p * star (A w b q)) = if a = p ∧ b = q then c else 0 := by
    have he := congrArg (fun M => M a b) (h (commMatrixUnit p q))
    simp only [Matrix.sum_apply, comm_conj_matrix_unit, Matrix.smul_apply,
      smul_eq_mul, commMatrixUnit] at he
    split_ifs at he ⊢ <;> simpa using he
  have hdiag (p : Fin n) : (∑ w, Complex.normSq (A w p p)) = c.re := by
    have he := congrArg Complex.re (hcoeff p p p p)
    simpa [RCLike.star_def, Complex.mul_conj] using he
  have hoff (a p : Fin n) (hap : a ≠ p) (w : ι) : A w a p = 0 := by
    have he : (∑ v, Complex.normSq (A v a p)) = 0 := by
      have hs := congrArg Complex.re (hcoeff p p a a)
      simpa [RCLike.star_def, Complex.mul_conj, hap] using hs
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v (_ : v ∈ Finset.univ) => Complex.normSq_nonneg (A v a p))).mp he
    exact Complex.normSq_eq_zero.mp (hz w (Finset.mem_univ w))
  have hequal (p q : Fin n) (w : ι) : A w p p = A w q q := by
    have hcross : (∑ v, (A v p p * (starRingEnd ℂ) (A v q q)).re) = c.re := by
      simpa [RCLike.star_def] using congrArg Complex.re (hcoeff p q p q)
    have hs : (∑ v, Complex.normSq (A v p p - A v q q)) = 0 := by
      simp_rw [Complex.normSq_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      linarith [hdiag p, hdiag q]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v (_ : v ∈ Finset.univ) => Complex.normSq_nonneg (A v p p - A v q q))).mp hs
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (hz w (Finset.mem_univ w)))
  intro w
  refine ⟨A w 0 0, ?_⟩
  ext p q
  by_cases hpq : p = q
  · subst q
    simpa using hequal p 0 w
  · simp [hpq, hoff p q hpq w]

/-- The Weyl operator with shift given by the second outcome coordinate and negative phase given
by the first. -/
private noncomputable def commWeyl (n : ℕ) [NeZero n] (o : Fin n × Fin n) : Operator n :=
  quditX n ((ZMod.finEquiv n) o.2) * quditZ n (-((ZMod.finEquiv n) o.1))

/-- Every operator `commWeyl n o` is unitary. -/
private theorem commWeyl_unitary (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    commWeyl n o ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  (Matrix.unitaryGroup (Fin n) ℂ).mul_mem (quditX_unitary _ _) (quditZ_unitary _ _)

/-- If a nonzero scalar multiple of one outcome Weyl operator equals a scalar multiple of
another, the outcomes coincide. -/
private theorem comm_weyl_projective (n : ℕ) [NeZero n] (o o' : Fin n × Fin n)
    (z z' : ℂ) (hz : z ≠ 0) (he : z • commWeyl n o = z' • commWeyl n o') : o = o' := by
  have hsupport : o.2 = o'.2 := by
    by_contra hs
    have hentry := congrArg (fun M => M o.2 0) he
    have hf : (ZMod.finEquiv n) o.2 ≠ (ZMod.finEquiv n) o'.2 :=
      fun h => hs ((ZMod.finEquiv n).injective h)
    simp [commWeyl, Matrix.smul_apply, smul_eq_mul, quditXZ_entry, hf] at hentry
    exact hz hentry
  have hscalar : z = z' := by
    have hentry := congrArg (fun M => M o.2 0) he
    simpa [commWeyl, Matrix.smul_apply, smul_eq_mul, quditXZ_entry, hsupport] using hentry
  subst z'
  have hW : commWeyl n o = commWeyl n o' := by
    ext i j
    have hentry := congrArg (fun M => M i j) he
    change z * commWeyl n o i j = z * commWeyl n o' i j at hentry
    exact mul_left_cancel₀ hz hentry
  let j := (ZMod.finEquiv n).symm (1 : ZMod n)
  let k := (ZMod.finEquiv n).symm (1 + (ZMod.finEquiv n) o.2)
  have hchar : ZMod.stdAddChar (-((ZMod.finEquiv n) o.1)) =
      ZMod.stdAddChar (-((ZMod.finEquiv n) o'.1)) := by
    have hentry := congrArg (fun M => M k j) hW
    simpa [commWeyl, quditXZ_entry, j, k, ← hsupport] using hentry
  have hfirst : o.1 = o'.1 := (ZMod.finEquiv n).injective
    (neg_inj.mp (stdAddChar_injective hchar))
  exact Prod.ext hfirst hsupport

/-- If `C * quditBranchKraus n o = z • 1`, then `(1 / n) • C` equals `z` times the adjoint
outcome Weyl operator. -/
private theorem comm_corrected_weyl_scalar (n : ℕ) [NeZero n] (o : Fin n × Fin n)
    (C : Operator n) (z : ℂ) (hz : C * quditBranchKraus n o = z • (1 : Operator n)) :
    (1 / (n : ℂ)) • C = z • (commWeyl n o)ᴴ := by
  have he := congrArg (fun M => M * (commWeyl n o)ᴴ) hz
  (try dsimp only at he)
  have hK : quditBranchKraus n o = (1 / (n : ℂ)) • commWeyl n o :=
    quditBranchKraus_formula n o
  rw [hK, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    show commWeyl n o * (commWeyl n o)ᴴ = 1 from (commWeyl_unitary n o).2,
    Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at he
  exact he

/-- Distinct qudit outcomes cannot be merged under one correction to obtain `2 / n²` times the
identity map on every finite extension. -/
theorem commBoundMergeNoGoQudit : CommBoundMergeNoGoQudit := by
  classical
  intro n _ o o' hoo C
  by_contra hbad
  push Not at hbad
  let c : ℂ := 2 / (n : ℂ) ^ 2
  have hmap (ρ : Operator n) : mergedQuditBranch n o o' C ρ = c • ρ := by
    have he := hbad 1 (fun i j => ρ i.1 j.1)
    ext p q
    exact congrArg (fun M => M (p, 0) (q, 0)) he
  let A (b : Bool) : Operator n := if b then C * quditBranchKraus n o else C * quditBranchKraus n o'
  have hA (ρ : Operator n) : (∑ b : Bool, conjBranch (A b) ρ) = c • ρ := by
    simpa [A, Fintype.sum_bool, mergedQuditBranch, LinearMap.add_apply] using hmap ρ
  obtain ⟨z, hz⟩ := comm_kraus_scalar_of_identity A c hA true
  obtain ⟨z', hz'⟩ := comm_kraus_scalar_of_identity A c hA false
  change C * quditBranchKraus n o = z • (1 : Operator n) at hz
  change C * quditBranchKraus n o' = z' • (1 : Operator n) at hz'
  have hc : c ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact pow_ne_zero _ (by exact_mod_cast NeZero.ne n)
  have hnonzero : z ≠ 0 ∨ z' ≠ 0 := by
    by_contra hn
    push Not at hn
    have he := hmap (1 : Operator n)
    simp only [mergedQuditBranch, LinearMap.add_apply, hz, hz', hn.1, hn.2,
      zero_smul, conjBranch_apply, Matrix.zero_mul, zero_add] at he
    have hentry := congrArg (fun M => M 0 0) he
    have hz0 : c = 0 := by simpa using hentry.symm
    exact hc hz0
  have hrep : z • (commWeyl n o)ᴴ = z' • (commWeyl n o')ᴴ :=
    (comm_corrected_weyl_scalar n o C z hz).symm.trans
      (comm_corrected_weyl_scalar n o' C z' hz')
  have hrep' : star z • commWeyl n o = star z' • commWeyl n o' := by
    simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hrep
  rcases hnonzero with hn | hn
  · exact hoo (comm_weyl_projective n o o' (star z) (star z') (star_ne_zero.mpr hn) hrep')
  · exact hoo (comm_weyl_projective n o' o (star z') (star z) (star_ne_zero.mpr hn) hrep'.symm).symm

/-- A unitary operator in nonzero dimension is nonzero. -/
private theorem comm_unitary_ne_zero (n : ℕ) [NeZero n] (C : Operator n)
    (hC : C∈Matrix.unitaryGroup (Fin n) ℂ) : C≠0 := by
  intro hc
  have h : C*Cᴴ=1 := hC.2
  rw [hc,Matrix.zero_mul] at h
  have he := congrArg (fun M : Operator n => M 0 0) h
  norm_num at he

/-- Exact qudit recovery with unitary corrections forces an injective message assignment and at
least `n²` message labels. -/
theorem commBoundMessageInjectiveQudit : CommBoundMessageInjectiveQudit := by
  classical
  intro n _ κ _ m Cm hCm hrec
  let A := fun w : Fin n × Fin n => Cm (m w)*quditBranchKraus n w
  have hA (ρ : Operator n) : (∑ w,conjBranch (A w) ρ)=(1 : ℂ) • ρ := by
    simpa only [one_smul] using hrec ρ
  have hsc := comm_kraus_scalar_of_identity A 1 hA
  have hinj : Function.Injective m := by
    intro o o' hm
    obtain ⟨z,hz⟩ := hsc o
    obtain ⟨z',hz'⟩ := hsc o'
    change Cm (m o)*quditBranchKraus n o=z • (1 : Operator n) at hz
    change Cm (m o')*quditBranchKraus n o'=z' • (1 : Operator n) at hz'
    rw [← hm] at hz'
    have hrep := comm_corrected_weyl_scalar n o (Cm (m o)) z hz
    have hrep' := comm_corrected_weyl_scalar n o' (Cm (m o)) z' hz'
    have hn : z≠0 := by
      intro hz0
      rw [hz0,zero_smul] at hrep
      have ha : (1/(n : ℂ))≠0 := div_ne_zero one_ne_zero (by exact_mod_cast NeZero.ne n)
      exact comm_unitary_ne_zero n (Cm (m o)) (hCm (m o))
        ((smul_eq_zero.mp hrep).resolve_left ha)
    have he : star z • commWeyl n o=star z' • commWeyl n o' := by
      simpa only [Matrix.conjTranspose_smul,Matrix.conjTranspose_conjTranspose] using
        congrArg Matrix.conjTranspose (hrep.symm.trans hrep')
    exact comm_weyl_projective n o o' (star z) (star z') (star_ne_zero.mpr hn) he
  refine ⟨hinj,?_⟩
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective m hinj

/-- The Bell outcome operator obtained by relabeling the corresponding product of Pauli `X` and
Pauli `Z`. -/
private noncomputable def commBellW (o : Bool × Bool) : Operator 2 :=
  relabelGate boolEquivFin2 ((if o.2 then PauliX else 1)*(if o.1 then PauliZ else 1))

/-- Every Bell outcome operator `commBellW o` is unitary. -/
private theorem commBellW_unitary (o : Bool × Bool) : commBellW o∈Matrix.unitaryGroup (Fin 2) ℂ := by
  apply teleportRelabelGate_mem_unitaryGroup
  apply (Matrix.unitaryGroup Bool ℂ).mul_mem
  · cases o.2 <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact Submonoid.one_mem _
    · exact pauliX_unitary
  · cases o.1 <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact Submonoid.one_mem _
    · exact pauliZ_unitary

/-- If a nonzero scalar multiple of one Bell outcome operator equals a scalar multiple of
another, the outcomes coincide. -/
private theorem comm_bell_projective (o o' : Bool × Bool) (z z' : ℂ) (hz : z≠0)
    (he : z • commBellW o=z' • commBellW o') : o=o' := by
  rcases o with ⟨a,b⟩
  rcases o' with ⟨a',b'⟩
  cases a <;> cases b <;> cases a' <;> cases b'
  all_goals try rfl
  all_goals exfalso; apply hz
  all_goals
    have h00 := congrArg (fun M : Operator 2 => M 0 0) he
    have h01 := congrArg (fun M : Operator 2 => M 0 1) he
    have h10 := congrArg (fun M : Operator 2 => M 1 0) he
    have h11 := congrArg (fun M : Operator 2 => M 1 1) he
    norm_num [commBellW,Matrix.smul_apply,smul_eq_mul,relabelGate,Matrix.reindex_apply,
      Matrix.submatrix_apply,Matrix.mul_apply,Fintype.sum_bool,PauliX,PauliZ,permMatrix,
      Matrix.one_apply,Matrix.diagonal_apply,boolEquivFin2] at h00 h01 h10 h11
    first
    | exact h00
    | exact h01
    | exact h10
    | exact h11
    | linear_combination (1/2 : ℂ)*h00+(1/2 : ℂ)*h11
    | linear_combination (1/2 : ℂ)*h00-(1/2 : ℂ)*h11
    | linear_combination (1/2 : ℂ)*h01+(1/2 : ℂ)*h10
    | linear_combination (1/2 : ℂ)*h10-(1/2 : ℂ)*h01

/-- Exact Bell recovery with unitary corrections forces an injective message assignment and at
least four message labels. -/
theorem commBoundMessageInjectiveBell : CommBoundMessageInjectiveBell := by
  classical
  intro κ _ m Cm hCm hrec
  let A := fun o : Bool × Bool => Cm (m o)*teleportBranchKraus o
  have hA (ρ : Operator 2) : (∑ o,conjBranch (A o) ρ)=(1 : ℂ) • ρ := by
    simpa only [one_smul] using hrec ρ
  have hsc := comm_kraus_scalar_of_identity A 1 hA
  have hrep (o : Bool × Bool) (C : Operator 2) (z : ℂ)
      (hz : C*teleportBranchKraus o=z • (1 : Operator 2)) :
      (1/2 : ℂ) • C=z • (commBellW o)ᴴ := by
    have he := congrArg (fun M => M*(commBellW o)ᴴ) hz
    (try dsimp only at he)
    have hK : teleportBranchKraus o=(1/2 : ℂ) • commBellW o := bell_decoded_branch_operators.2 o
    rw [hK,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc,
      show commBellW o*(commBellW o)ᴴ=1 from (commBellW_unitary o).2,
      Matrix.mul_one,Matrix.smul_mul,Matrix.one_mul] at he
    exact he
  have hinj : Function.Injective m := by
    intro o o' hm
    obtain ⟨z,hz⟩ := hsc o
    obtain ⟨z',hz'⟩ := hsc o'
    change Cm (m o)*teleportBranchKraus o=z • (1 : Operator 2) at hz
    change Cm (m o')*teleportBranchKraus o'=z' • (1 : Operator 2) at hz'
    rw [← hm] at hz'
    have hrep1 := hrep o (Cm (m o)) z hz
    have hrep2 := hrep o' (Cm (m o)) z' hz'
    have hn : z≠0 := by
      intro hz0
      rw [hz0,zero_smul] at hrep1
      exact comm_unitary_ne_zero 2 (Cm (m o)) (hCm (m o))
        ((smul_eq_zero.mp hrep1).resolve_left (by norm_num))
    have he : star z • commBellW o=star z' • commBellW o' := by
      simpa only [Matrix.conjTranspose_smul,Matrix.conjTranspose_conjTranspose] using
        congrArg Matrix.conjTranspose (hrep1.symm.trans hrep2)
    exact comm_bell_projective o o' (star z) (star z') (star_ne_zero.mpr hn) he
  exact ⟨hinj,Fintype.card_le_of_injective m hinj⟩

/-- The qudit and Bell merged-branch impossibility and unitary message-injectivity contracts
hold. These formalize restricted communication bounds for teleportation
[BennettEtAl1993Teleportation]. -/
theorem commBoundRestricted : CommBoundRestricted :=
  ⟨commBoundMergeNoGoQudit,commBoundMessageInjectiveQudit,
    commBoundMergeNoGoBell,commBoundMessageInjectiveBell⟩

end Qatlib.Concepts.QuditTeleport.CommLowerBound

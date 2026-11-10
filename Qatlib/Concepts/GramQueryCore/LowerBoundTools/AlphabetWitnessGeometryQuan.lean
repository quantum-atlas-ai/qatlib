/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetWitnessGeometryStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionGeometry
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators ComplexOrder

theorem source_hermitian_inner_mulVec {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : Pᴴ=P) (v w : QState I) :
    Qatlib.Foundations.PureStateMath.Inner v (P *ᵥ w) = Qatlib.Foundations.PureStateMath.Inner (P *ᵥ v) w := by
  change star v ⬝ᵥ (P *ᵥ w) = star (P *ᵥ v) ⬝ᵥ w
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,hP]

theorem source_forbidden_complement_projection
    (I X : Type) [Fintype I] [DecidableEq I] (forbidden : X → QState I) :
    ∃ P : Matrix I I ℂ, IsOrthogonalProjector P ∧
      (∀ ψ : QState I, P *ᵥ ψ=ψ ↔ ∀ x, Qatlib.Foundations.PureStateMath.Inner (forbidden x) ψ=0) ∧
      ∀ x, P *ᵥ forbidden x=0 := by
  let A := {ψ : QState I // ∀ x, Qatlib.Foundations.PureStateMath.Inner (forbidden x) ψ=0}
  let F : X ⊕ A → QState I := Sum.elim forbidden (fun _ => 0)
  let S : X ⊕ A → QState I := Sum.elim (fun _ => 0) Subtype.val
  have hCross : ∀ x y, Qatlib.Foundations.PureStateMath.Inner (F x) (S y)=0 := by
    rintro (x | x) (y | y)
    · simp [F,S,Qatlib.Foundations.PureStateMath.Inner]
    · exact y.prop x
    · simp [F,S,Qatlib.Foundations.PureStateMath.Inner]
    · simp [F,S,Qatlib.Foundations.PureStateMath.Inner]
  obtain ⟨P,hP,hF,hS⟩ := conversion_public_complement_projection I (X ⊕ A) F S hCross
  have hkill (x : X) : P *ᵥ forbidden x=0 := hF (.inl x)
  refine ⟨P,hP,?_,hkill⟩
  intro ψ
  constructor
  · intro hψ x
    calc
      Qatlib.Foundations.PureStateMath.Inner (forbidden x) ψ = Qatlib.Foundations.PureStateMath.Inner (forbidden x) (P *ᵥ ψ) := by rw [hψ]
      _ = Qatlib.Foundations.PureStateMath.Inner (P *ᵥ forbidden x) ψ := source_hermitian_inner_mulVec P hP.2 _ _
      _ = 0 := by rw [hkill]; simp [Qatlib.Foundations.PureStateMath.Inner]
  · intro hψ
    exact hS (.inr ⟨ψ,hψ⟩)

theorem source_complement_annihilates
    {I X : Type} [Fintype I] [DecidableEq I] (forbidden : X → QState I)
    (P : Matrix I I ℂ) (hP : IsOrthogonalProjector P)
    (hfix : ∀ ψ : QState I, P *ᵥ ψ=ψ ↔ ∀ x, Qatlib.Foundations.PureStateMath.Inner (forbidden x) ψ=0) :
    ∀ x, P *ᵥ forbidden x=0 := by
  intro x
  have hPP : P *ᵥ (P *ᵥ forbidden x)=P *ᵥ forbidden x := by
    rw [Matrix.mulVec_mulVec,hP.1]
  have horth := ((hfix (P *ᵥ forbidden x)).mp hPP) x
  have hzero : Qatlib.Foundations.PureStateMath.Inner (P *ᵥ forbidden x) (P *ᵥ forbidden x)=0 := by
    rw [← source_hermitian_inner_mulVec P hP.2,hPP]
    exact horth
  exact dotProduct_star_self_eq_zero.mp hzero

theorem sourceComplement_public {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) :
    let L := sourceComplement input ρ σ u W ε
    IsOrthogonalProjector L ∧
      (∀ ψ : QState (SourceGeometry n q m H), L *ᵥ ψ=ψ ↔
        ∀ x, Qatlib.Foundations.PureStateMath.Inner (sourceForbidden input ρ σ u W ε x) ψ=0) ∧
      ∀ x, L *ᵥ sourceForbidden input ρ σ u W ε x=0 := by
  obtain ⟨P,hP,hfix,_⟩ := source_forbidden_complement_projection
    (SourceGeometry n q m H) X (sourceForbidden input ρ σ u W ε)
  have hp : ∃ P : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ,
      IsOrthogonalProjector P ∧ ∀ ψ : QState (SourceGeometry n q m H),
      P *ᵥ ψ=ψ ↔ ∀ x, (∑ i,star (sourceForbidden input ρ σ u W ε x i)*ψ i)=0 :=
    ⟨P,hP,hfix⟩
  unfold sourceComplement
  rw [dif_pos hp]
  have hchoose := Classical.choose_spec hp
  exact ⟨hchoose.1,hchoose.2,source_complement_annihilates _ _ hchoose.1 hchoose.2⟩

theorem sourceAlpha_parameters (q : ℕ) (hq : 0 < q) :
    (sourceAlpha q)^2 = 1/2-Real.sqrt (q : ℝ)/(q+1) ∧
    0 ≤ sourceAlpha q ∧ (sourceAlpha q)^2 ≤ 1/2 ∧
    (Real.sqrt (1-(sourceAlpha q)^2))^2 = 1-(sourceAlpha q)^2 ∧
    sourceAlpha q*Real.sqrt (1-(sourceAlpha q)^2) = (q-1)/(2*(q+1)) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < q+1 := by positivity
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hr0 := Real.sqrt_nonneg (q : ℝ)
  have harg0 : 0 ≤ 1/2-Real.sqrt (q : ℝ)/(q+1) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (Real.sqrt (q : ℝ)-1)]
  have ha2 : (sourceAlpha q)^2 = 1/2-Real.sqrt (q : ℝ)/(q+1) := Real.sq_sqrt harg0
  have ha0 : 0 ≤ sourceAlpha q := Real.sqrt_nonneg _
  have haq : (sourceAlpha q)^2 ≤ 1/2 := by
    rw [ha2]
    exact sub_le_self _ (div_nonneg hr0 hden.le)
  have hb2 : (Real.sqrt (1-(sourceAlpha q)^2))^2 = 1-(sourceAlpha q)^2 :=
    Real.sq_sqrt (by linarith)
  refine ⟨ha2,ha0,haq,hb2,?_⟩
  have hab0 : 0 ≤ sourceAlpha q*Real.sqrt (1-(sourceAlpha q)^2) :=
    mul_nonneg ha0 (Real.sqrt_nonneg _)
  have hrhs0 : (0 : ℝ) ≤ ((q : ℝ)-1)/(2*(q+1)) := div_nonneg (by linarith) (by positivity)
  have hsquares : (sourceAlpha q*Real.sqrt (1-(sourceAlpha q)^2))^2 =
      (((q : ℝ)-1)/(2*(q+1)))^2 := by
    rw [mul_pow,hb2,ha2]
    field_simp
    nlinarith only [hr2]
  nlinarith only [hsquares,hab0,hrhs0]

private theorem source_sum_one_exception {K : Type} [CommRing K]
    (q : ℕ) (a : Fin (q+1)) (b c : K) :
    (∑ i : Fin (q+1), if i=a then b else c) = b+(q : K)*c := by
  classical
  calc
    _ = ∑ i : Fin (q+1), (c+(if i=a then b-c else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ = ((q+1 : ℕ) : K)*c+(b-c) := by simp [Finset.sum_add_distrib]
    _ = _ := by push_cast; ring

theorem sourceMu_normalized (q : ℕ) (hq : 0 < q) (a : Fin (q+1)) :
    Normalized (sourceMu q a) := by
  obtain ⟨ha2,_,haq,hb2,_⟩ := sourceAlpha_parameters q hq
  have hrp : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hnorm : ‖toEuclidean_fromVec (sourceMu q a)‖^2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [sourceMu,apply_ite (fun z : ℂ => ‖z‖^2),norm_neg,norm_div,Complex.norm_real,
      Real.norm_eq_abs,div_pow,sq_abs]
    rw [source_sum_one_exception]
    rw [hb2,hr2]
    field_simp
    ring
  apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
  nlinarith [norm_nonneg (toEuclidean_fromVec (sourceMu q a))]

theorem sourceNu_normalized (q : ℕ) (hq : 0 < q) (a : Fin (q+1)) :
    Normalized (sourceNu q a) := by
  obtain ⟨ha2,_,haq,hb2,_⟩ := sourceAlpha_parameters q hq
  have hrp : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hnorm : ‖toEuclidean_fromVec (sourceNu q a)‖^2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [sourceNu,apply_ite (fun z : ℂ => ‖z‖^2),norm_div,Complex.norm_real,
      Real.norm_eq_abs,div_pow,sq_abs]
    rw [source_sum_one_exception]
    rw [hb2,hr2]
    field_simp
    ring
  apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
  nlinarith [norm_nonneg (toEuclidean_fromVec (sourceNu q a))]

private theorem source_sum_pair_exceptions {K : Type} [CommRing K]
    (q : ℕ) (a b : Fin (q+1)) (A B C D : K) :
    (∑ i : Fin (q+1), (if i=a then A else B)*(if i=b then C else D)) =
      (A+(q : K)*B)*D+(if b=a then A else B)*(C-D) := by
  classical
  calc
    _ = ∑ i : Fin (q+1),
        ((if i=a then A else B)*D+if i=b then (if b=a then A else B)*(C-D) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hib : i=b
      · subst i
        split_ifs <;> ring
      · simp only [if_neg hib,add_zero]
    _ = (∑ i : Fin (q+1), if i=a then A else B)*D+(if b=a then A else B)*(C-D) := by
      simp [Finset.sum_add_distrib,Finset.sum_mul]
    _ = _ := by rw [source_sum_one_exception]

theorem sourceMu_sourceNu_pairing (q : ℕ) (hq : 0 < q) (a b : Fin (q+1)) :
    (∑ k, star (sourceMu q a k)*sourceNu q b k) =
      if a=b then 0 else ((q+1)/(2*q) : ℂ) := by
  classical
  let A := sourceAlpha q
  let B := Real.sqrt (1-A^2)
  let r := Real.sqrt (q : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hr2 : r^2=(q : ℝ) := Real.sq_sqrt hqr.le
  obtain ⟨ha2,_,_,hb2,hab⟩ := sourceAlpha_parameters q hq
  have hdiff : B^2-A^2=2*r/(q+1) := by
    dsimp only [A,B,r]
    rw [hb2,ha2]
    ring
  have hab' : A*B=((q : ℝ)-1)/(2*(q+1)) := hab
  have hreal : (∑ i : Fin (q+1),
      (if i=a then -A else B/r)*(if i=b then B else A/r)) =
      if a=b then (0 : ℝ) else ((q : ℝ)+1)/(2*q) := by
    rw [source_sum_pair_exceptions]
    by_cases heq : a=b
    · subst b
      rw [if_pos rfl,if_pos rfl]
      have hid : (-A+(q : ℝ)*(B/r))*(A/r)+(-A)*(B-A/r) =
          A*B*((q : ℝ)/r^2-1) := by field_simp; ring
      rw [hid,hr2,div_self hqr.ne',sub_self,mul_zero]
    · rw [if_neg heq,if_neg (Ne.symm heq)]
      have hid : (-A+(q : ℝ)*(B/r))*(A/r)+(B/r)*(B-A/r) =
          (B^2-A^2)/r+((q : ℝ)-1)*A*B/r^2 := by field_simp; ring
      rw [hid,hdiff,hr2,show ((q : ℝ)-1)*A*B=((q : ℝ)-1)*(A*B) by ring,hab']
      field_simp
      ring
  have hmu (i : Fin (q+1)) : sourceMu q a i =
      ((if i=a then -A else B/r : ℝ) : ℂ) := by
    dsimp [sourceMu,A,B,r]
    split_ifs <;> push_cast <;> rfl
  have hnu (i : Fin (q+1)) : sourceNu q b i =
      ((if i=b then B else A/r : ℝ) : ℂ) := by
    dsimp [sourceNu,A,B,r]
    split_ifs <;> push_cast <;> rfl
  simp_rw [hmu,hnu]
  by_cases habeq : a=b
  · rw [if_pos habeq]
    have hreal0 : (∑ i : Fin (q+1),
        (if i=a then -A else B/r)*(if i=b then B else A/r))=0 := by
      simpa only [if_pos habeq] using! hreal
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal0
    simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.star_def,Complex.conj_ofReal,
      Complex.ofReal_zero] using! hcast
  · rw [if_neg habeq]
    have hreal1 : (∑ i : Fin (q+1),
        (if i=a then -A else B/r)*(if i=b then B else A/r))=((q : ℝ)+1)/(2*q) := by
      simpa only [if_neg habeq] using! hreal
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal1
    simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_div,
      Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat] using! hcast

def sourceMuFrame {X H : Type} {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Matrix (SourceGeometry n q m H) (Fin n × Fin m) ℂ := fun p jk =>
  match p with
  | .inl _ => 0
  | .inr (j,a,k) => if j=jk.1 ∧ k=jk.2 then sourceMu q (input x j) a else 0

theorem sourceMuFrame_isometry {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X) (hq : 0 < q) :
    (sourceMuFrame (m := m) (H := H) input x)ᴴ*sourceMuFrame (m := m) (H := H) input x=1 := by
  classical
  ext i j
  rcases i with ⟨i,k⟩
  rcases j with ⟨j,h⟩
  by_cases hij : i=j
  · subst j
    by_cases hkh : k=h
    · subst h
      have hmu := (normalized_iff_inner_self (sourceMu q (input x i))).mp
        (sourceMu_normalized q hq (input x i))
      simpa [sourceMuFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type,
        Fintype.sum_prod_type,ite_and,apply_ite star,ite_mul,mul_ite,Qatlib.Foundations.PureStateMath.Inner] using! hmu
    · simp [sourceMuFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type,
        Fintype.sum_prod_type,ite_and,mul_ite,hkh,Ne.symm hkh]
  · simp [sourceMuFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type,
      Fintype.sum_prod_type,ite_and,mul_ite,hij,Ne.symm hij]

theorem sourceKeep_frame {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X) :
    sourceKeep (m := m) (H := H) input x =
      (1 : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ)-
        sourceMuFrame (m := m) (H := H) input x*(sourceMuFrame (m := m) (H := H) input x)ᴴ := by
  classical
  ext p t
  rcases p with p | ⟨j,a,k⟩ <;> rcases t with t | ⟨l,b,h⟩
  · simp [sourceKeep,sourceMuFrame,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.one_apply]
  · simp [sourceKeep,sourceMuFrame,Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  · simp [sourceKeep,sourceMuFrame,Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  · by_cases hjl : j=l
    · subst l
      by_cases hkh : k=h
      · subst h
        simp [sourceKeep,sourceMuFrame,Matrix.mul_apply,
          Matrix.conjTranspose_apply,Matrix.one_apply,Fintype.sum_prod_type,ite_and,apply_ite star,
          ite_mul]
      · simp [sourceKeep,sourceMuFrame,Matrix.mul_apply,
          Matrix.conjTranspose_apply,Fintype.sum_prod_type,ite_and,apply_ite star,
          ite_mul,hkh]
    · simp [sourceKeep,sourceMuFrame,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Fintype.sum_prod_type,ite_and,apply_ite star,
        ite_mul,hjl]

theorem sourceKeep_isOrthogonalProjector {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X) (hq : 0 < q) :
    IsOrthogonalProjector (sourceKeep (m := m) (H := H) input x) := by
  let M := sourceMuFrame (m := m) (H := H) input x
  have hM : Mᴴ*M=1 := sourceMuFrame_isometry input x hq
  have hR : (M*Mᴴ)*(M*Mᴴ)=M*Mᴴ := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc Mᴴ M Mᴴ,hM,Matrix.one_mul]
  rw [sourceKeep_frame]
  change IsOrthogonalProjector (1-M*Mᴴ)
  constructor
  · change (1-M*Mᴴ)*(1-M*Mᴴ)=1-M*Mᴴ
    rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub]
    simp only [Matrix.one_mul,Matrix.mul_one,hR]
    abel
  · change (1-M*Mᴴ)ᴴ=1-M*Mᴴ
    simp [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem sourceMuFrame_adjoint_action {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (ψ : QState (SourceGeometry n q m H)) (j : Fin n) (k : Fin m) :
    ((sourceMuFrame input x)ᴴ *ᵥ ψ) (j,k) =
      ∑ a, star (sourceMu q (input x j) a)*ψ (.inr (j,a,k)) := by
  simp [sourceMuFrame,Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,Fintype.sum_sum_type,
    Fintype.sum_prod_type,ite_and,apply_ite (starRingEnd ℂ),ite_mul]

theorem sourceMuFrame_inl_action {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (φ : QState (Fin n × Fin m)) (h : Bool × H) :
    ((sourceMuFrame (H := H) input x) *ᵥ φ) (.inl h)=0 := by simp [sourceMuFrame,Matrix.mulVec]

theorem sourceMuFrame_inr_action {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (φ : QState (Fin n × Fin m)) (j : Fin n) (a : Fin (q+1)) (k : Fin m) :
    ((sourceMuFrame (H := H) input x) *ᵥ φ) (.inr (j,a,k))=sourceMu q (input x j) a*φ (j,k) := by
  simp [sourceMuFrame,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,ite_and,ite_mul]

theorem sourceKeep_action {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (ψ : QState (SourceGeometry n q m H)) (p : SourceGeometry n q m H) :
    (sourceKeep input x *ᵥ ψ) p = match p with
      | .inl h => ψ (.inl h)
      | .inr (j,a,k) => ψ (.inr (j,a,k))-sourceMu q (input x j) a*
          ∑ b, star (sourceMu q (input x j) b)*ψ (.inr (j,b,k)) := by
  simp only [sourceKeep_frame,Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec,Pi.sub_apply]
  cases p with
  | inl h => simp [sourceMuFrame_inl_action]
  | inr z =>
    rcases z with ⟨j,a,k⟩
    rw [sourceMuFrame_inr_action,sourceMuFrame_adjoint_action]

theorem sourceKeep_fixed {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (v : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) (hq : 0 < q) :
    sourceKeep input x *ᵥ sourceFixed input ρ σ v W ε x=sourceFixed input ρ σ v W ε x := by
  ext p
  rw [sourceKeep_action]
  cases p with
  | inl h => rfl
  | inr z =>
    rcases z with ⟨j,a,k⟩
    have hp := sourceMu_sourceNu_pairing q hq (input x j) (input x j)
    simp only [if_true] at hp
    simp only [sourceFixed]
    have hz : (∑ b, star (sourceMu q (input x j) b)*
        ((ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)*sourceNu q (input x j) b*v x j k))=0 := by
      calc
        _ = ((ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)*v x j k)*
            ∑ b, star (sourceMu q (input x j) b)*sourceNu q (input x j) b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = 0 := by rw [hp,mul_zero]
    rw [hz,mul_zero,sub_zero]

theorem sourceKeep_forbidden {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) (hq : 0 < q) :
    sourceKeep input x *ᵥ sourceForbidden input ρ σ u W ε x=
      ((ε/Real.sqrt W : ℝ) : ℂ) • sourceMinus (ρ x) (σ x) := by
  ext p
  rw [sourceKeep_action]
  cases p with
  | inl h => rfl
  | inr z =>
    rcases z with ⟨j,a,k⟩
    have hp := (normalized_iff_inner_self (sourceMu q (input x j))).mp
      (sourceMu_normalized q hq (input x j))
    simp only [sourceForbidden,Pi.smul_apply,smul_eq_mul,sourceMinus,mul_zero]
    have hsum : (∑ b, star (sourceMu q (input x j) b)*(-sourceMu q (input x j) b*u x j k)) =
        -(u x j k) := by
      calc
        _ = ∑ b, -(star (sourceMu q (input x j) b)*sourceMu q (input x j) b*u x j k) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = -(∑ b, star (sourceMu q (input x j) b)*sourceMu q (input x j) b)*u x j k := by
          rw [Finset.sum_neg_distrib,← Finset.sum_mul]
          ring
        _ = _ := by rw [show (∑ b, star (sourceMu q (input x j) b)*sourceMu q (input x j) b)=1 from hp]; ring
    rw [hsum]
    ring

theorem sourcePlusMinus_norm {H : Type} [Fintype H] [DecidableEq H] {n q m : ℕ}
    (ρ σ : QState H) (hρ : Normalized ρ) (hσ : Normalized σ) :
    ‖toEuclidean_fromVec (sourcePlus (n := n) (q := q) (m := m) ρ σ)‖^2=1 ∧
    ‖toEuclidean_fromVec (sourceMinus (n := n) (q := q) (m := m) ρ σ)‖^2=1 := by
  have hρsum : (∑ h, ‖ρ h‖^2)=1 := by
    rw [← norm_toEuclidean_fromVec_sq,(normalized_iff_norm_toEuclidean_fromVec _).mp hρ]
    norm_num
  have hσsum : (∑ h, ‖σ h‖^2)=1 := by
    rw [← norm_toEuclidean_fromVec_sq,(normalized_iff_norm_toEuclidean_fromVec _).mp hσ]
    norm_num
  constructor <;>
    rw [norm_toEuclidean_fromVec_sq] <;>
    simp [sourcePlus,sourceMinus,Fintype.sum_sum_type,Fintype.sum_prod_type,
      norm_inv,Complex.norm_real,Real.norm_eq_abs,mul_pow,inv_pow,sq_abs,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),← Finset.mul_sum,hρsum,hσsum] <;> norm_num

theorem sourceMinusPlus_inner {H : Type} [Fintype H] [DecidableEq H] {n q m : ℕ}
    (ρ σ ρ' σ' : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (sourceMinus (n := n) (q := q) (m := m) ρ σ) (sourcePlus ρ' σ') =
      (1/2 : ℂ)*(Qatlib.Foundations.PureStateMath.Inner ρ ρ'-Qatlib.Foundations.PureStateMath.Inner σ σ') := by
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hc : star c*c=(1/2 : ℂ) := by
    let a : ℝ := (Real.sqrt 2)⁻¹
    have hrep : c=(a : ℂ) := (Complex.ofReal_inv (Real.sqrt 2)).symm
    have hstar : star (a : ℂ)=(a : ℂ) := Complex.conj_ofReal a
    have ha : a*a=(1/2 : ℝ) := by
      dsimp only [a]
      rw [← mul_inv,← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc
      _ = ((a*a : ℝ) : ℂ) := by rw [hrep,hstar,Complex.ofReal_mul]
      _ = _ := by rw [ha]; norm_num
  have hleft (h : H) : star (c*ρ h)*(c*ρ' h) = (star c*c)*(star (ρ h)*ρ' h) := by
    rw [star_mul]
    ring
  have hright (h : H) : star ((-c)*σ h)*(c*σ' h) = -(star c*c)*(star (σ h)*σ' h) := by
    rw [star_mul,star_neg]
    ring
  change (∑ p : SourceGeometry n q m H,
      star (sourceMinus ρ σ p)*sourcePlus ρ' σ' p) = _
  rw [Fintype.sum_sum_type]
  simp only [sourceMinus,sourcePlus,star_zero,zero_mul,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  change (∑ h, star ((-c)*σ h)*(c*σ' h))+(∑ h, star (c*ρ h)*(c*ρ' h)) = _
  simp_rw [hleft,hright,hc]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  change -(1/2 : ℂ)*Qatlib.Foundations.PureStateMath.Inner σ σ' +
      (1/2 : ℂ)*Qatlib.Foundations.PureStateMath.Inner ρ ρ' = _
  ring

theorem sourceForbiddenFixed_inner_zero {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u v : X → Fin n → QState (Fin m)) (W ε : ℝ) (hq : 0 < q) (hW : 0 < W)
    (hEq : ∀ y x, (gramStateMatrix ρ-gramStateMatrix σ) y x=
      ∑ j, sourceAlphabetDelta input j y x*∑ k, star (u y j k)*v x j k)
    (y x : X) : Qatlib.Foundations.PureStateMath.Inner (sourceForbidden input ρ σ u W ε y) (sourceFixed input ρ σ v W ε x)=0 := by
  let lam : ℂ := ((ε/Real.sqrt W : ℝ) : ℂ)
  let c : ℂ := (ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)
  let β : ℂ := ((q+1)/(2*q) : ℂ)
  have hq0 : (q : ℂ)≠0 := by exact_mod_cast hq.ne'
  have hqp : ((q : ℂ)+1)≠0 := by exact_mod_cast (Nat.succ_ne_zero q)
  have hr : (Real.sqrt W : ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hW).ne'
  have hcβ : c*β=lam/2 := by dsimp [c,β,lam]; push_cast; field_simp
  have hpair (j : Fin n) : (∑ a, star (sourceMu q (input y j) a)*sourceNu q (input x j) a)=
      sourceAlphabetDelta input j y x*β := by
    have hp := sourceMu_sourceNu_pairing q hq (input y j) (input x j)
    dsimp [sourceAlphabetDelta,β]
    split_ifs with h <;> simpa [h] using! hp
  have hleft : (∑ h : Bool × H, star (sourceForbidden input ρ σ u W ε y (.inl h))*
      sourceFixed input ρ σ v W ε x (.inl h)) =
      lam*(1/2 : ℂ)*(gramStateMatrix ρ-gramStateMatrix σ) y x := by
    have hmp := sourceMinusPlus_inner (n := n) (q := q) (m := m) (ρ y) (σ y) (ρ x) (σ x)
    have hmp' : (∑ h : Bool × H,
        star (sourceMinus (n := n) (q := q) (m := m) (ρ y) (σ y) (.inl h))*
          sourcePlus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h)) =
        (1/2 : ℂ)*(Qatlib.Foundations.PureStateMath.Inner (ρ y) (ρ x)-Qatlib.Foundations.PureStateMath.Inner (σ y) (σ x)) := by
      simpa only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_sum_type,Pi.star_apply,sourceMinus,sourcePlus,
        star_zero,mul_zero,Finset.sum_const_zero,add_zero] using! hmp
    have hlam : star lam=lam := by simp [lam]
    calc
      _ = lam*(∑ h : Bool × H, star (sourceMinus (n := n) (q := q) (m := m) (ρ y) (σ y) (.inl h))*
          sourcePlus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        change star (lam*sourceMinus (n := n) (q := q) (m := m) (ρ y) (σ y) (.inl h))*sourcePlus
            (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h) = _
        rw [star_mul,hlam]
        ring
      _ = lam*((1/2 : ℂ)*(Qatlib.Foundations.PureStateMath.Inner (ρ y) (ρ x)-Qatlib.Foundations.PureStateMath.Inner (σ y) (σ x))) := by rw [hmp']
      _ = _ := by
        change lam*((1/2 : ℂ)*(Qatlib.Foundations.PureStateMath.Inner (ρ y) (ρ x)-Qatlib.Foundations.PureStateMath.Inner (σ y) (σ x))) =
          lam*(1/2 : ℂ)*(Qatlib.Foundations.PureStateMath.Inner (ρ y) (ρ x)-Qatlib.Foundations.PureStateMath.Inner (σ y) (σ x))
        ring
  have hright : (∑ z : Fin n × (Fin (q+1) × Fin m),
      star (sourceForbidden input ρ σ u W ε y (.inr z))*sourceFixed input ρ σ v W ε x (.inr z)) =
      -c*β*(∑ j, sourceAlphabetDelta input j y x*∑ k, star (u y j k)*v x j k) := by
    simp only [sourceForbidden,sourceFixed,Fintype.sum_prod_type]
    have hterms (j : Fin n) (a : Fin (q+1)) (k : Fin m) :
        star (-sourceMu q (input y j) a*u y j k)*(c*sourceNu q (input x j) a*v x j k)=
        -c*(star (sourceMu q (input y j) a)*sourceNu q (input x j) a)*
          (star (u y j k)*v x j k) := by rw [star_mul,star_neg]; ring
    simp_rw [show (ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)=c from rfl,hterms]
    simp only [← Finset.mul_sum]
    calc
      _ = ∑ j, -c*(∑ a, star (sourceMu q (input y j) a)*sourceNu q (input x j) a)*
          (∑ k, star (u y j k)*v x j k) := by
        apply Finset.sum_congr rfl
        intro j _
        conv_rhs => rw [mul_assoc,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = ∑ j, -c*(sourceAlphabetDelta input j y x*β)*(∑ k, star (u y j k)*v x j k) := by
        simp_rw [hpair]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  change (∑ p : SourceGeometry n q m H, star (sourceForbidden input ρ σ u W ε y p)*
      sourceFixed input ρ σ v W ε x p)=0
  rw [Fintype.sum_sum_type,hleft,hright,← hEq y x,neg_mul,hcβ]
  ring

private theorem source_sum_norm_tensor {A B : Type} [Fintype A] [Fintype B]
    (c : ℂ) (f : QState A) (g : QState B) :
    (∑ a, ∑ b, ‖c*f a*g b‖^2) = ‖c‖^2*(∑ a, ‖f a‖^2)*(∑ b, ‖g b‖^2) := by
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum]

theorem sourceFixed_distance_norm {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (v : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) (hq : 0 < q) :
    ‖toEuclidean_fromVec (sourceFixed input ρ σ v W ε x-sourcePlus (ρ x) (σ x))‖^2 =
      ‖(ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)‖^2*
        (∑ j, ‖toEuclidean_fromVec (v x j)‖^2) := by
  rw [norm_toEuclidean_fromVec_sq,Fintype.sum_sum_type]
  simp only [Pi.sub_apply,sourceFixed,sourcePlus,sub_self,norm_zero,sub_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,source_sum_norm_tensor]
  have hnorm (j : Fin n) : (∑ a, ‖sourceNu q (input x j) a‖^2)=1 := by
    rw [← norm_toEuclidean_fromVec_sq,
      (normalized_iff_norm_toEuclidean_fromVec _).mp (sourceNu_normalized q hq (input x j))]
    norm_num
  simp_rw [hnorm,mul_one,← norm_toEuclidean_fromVec_sq]
  rw [Finset.mul_sum]
  simp only [zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add]

theorem sourceFixed_distance_le {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (v : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) (hq : 0 < q) (hW : 0 < W)
    (hv : (∑ j, ‖toEuclidean_fromVec (v x j)‖^2) ≤ W) :
    ‖toEuclidean_fromVec (sourceFixed input ρ σ v W ε x-sourcePlus (ρ x) (σ x))‖^2 ≤ ε^2 := by
  rw [sourceFixed_distance_norm input ρ σ v W ε x hq]
  let c : ℂ := (ε/(2*Real.sqrt W)*(2*q/(q+1)) : ℂ)
  have hc : ‖c‖^2*W ≤ ε^2 := by
    have hqr : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hqp : (0 : ℝ) < q+1 := by positivity
    have hroot : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
    have hroot2 := Real.sq_sqrt hW.le
    have hqC : ((q : ℂ)+1)≠0 := by exact_mod_cast (Nat.succ_ne_zero q)
    have hrC : (Real.sqrt W : ℂ)≠0 := by exact_mod_cast hroot.ne'
    have hrep : c=((ε/Real.sqrt W*((q : ℝ)/(q+1)) : ℝ) : ℂ) := by
      dsimp only [c]
      push_cast
      field_simp
    have hratio0 : 0 ≤ (q : ℝ)/(q+1) := div_nonneg hqr hqp.le
    have hratio1 : (q : ℝ)/(q+1) ≤ 1 := (div_le_one hqp).mpr (by linarith)
    have hsqratio := pow_le_pow_left₀ hratio0 hratio1 2
    have hid : ‖c‖^2*W=ε^2*((q : ℝ)/(q+1))^2 := by
      rw [hrep,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,div_pow,hroot2]
      field_simp
    rw [hid]
    nlinarith [sq_nonneg ε]
  exact le_trans (mul_le_mul_of_nonneg_left hv (sq_nonneg ‖c‖)) hc

theorem sourceForbidden_scaled_norm {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) (hq : 0 < q)
    (hW : 0 < W) (hε : 0 < ε) (hρ : Normalized (ρ x)) (hσ : Normalized (σ x)) :
    ‖toEuclidean_fromVec (((Real.sqrt W/ε : ℝ) : ℂ) • sourceForbidden input ρ σ u W ε x)‖^2 =
      1+(W/ε^2)*(∑ j, ‖toEuclidean_fromVec (u x j)‖^2) := by
  let s : ℂ := ((Real.sqrt W/ε : ℝ) : ℂ)
  have hroot := Real.sqrt_pos.mpr hW
  have hproduct : s*((ε/Real.sqrt W : ℝ) : ℂ)=1 := by
    dsimp only [s]
    push_cast
    field_simp
  have hs : ‖s‖^2=W/ε^2 := by
    dsimp only [s]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt hW.le]
  have hminus := (sourcePlusMinus_norm (n := n) (q := q) (m := m) (ρ x) (σ x) hρ hσ).2
  rw [norm_toEuclidean_fromVec_sq,Fintype.sum_sum_type]
  have hlogical : (∑ h : Bool × H, ‖(s • sourceForbidden input ρ σ u W ε x) (.inl h)‖^2)=1 := by
    have hvalue (h : Bool × H) : (s • sourceForbidden input ρ σ u W ε x) (.inl h)=
        sourceMinus (n := n) (q := q) (m := m) (ρ x) (σ x) (.inl h) := by
      change s*(((ε/Real.sqrt W : ℝ) : ℂ)*sourceMinus (ρ x) (σ x) (.inl h)) = _
      rw [← mul_assoc,hproduct,one_mul]
    simp_rw [hvalue]
    simpa only [norm_toEuclidean_fromVec_sq,Fintype.sum_sum_type,sourceMinus,norm_zero,zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero,add_zero] using! hminus
  change (∑ h : Bool × H, ‖(s • sourceForbidden input ρ σ u W ε x) (.inl h)‖^2)+_ = _
  rw [hlogical,Fintype.sum_prod_type]
  simp only [Pi.smul_apply,smul_eq_mul,sourceForbidden,norm_mul,norm_neg,mul_pow]
  have htensor (j : Fin n) : (∑ a, ∑ k, ‖s‖^2*‖sourceMu q (input x j) a‖^2*‖u x j k‖^2)=
      ‖s‖^2*‖toEuclidean_fromVec (u x j)‖^2 := by
    have hn : (∑ a, ‖sourceMu q (input x j) a‖^2)=1 := by
      rw [← norm_toEuclidean_fromVec_sq,
        (normalized_iff_norm_toEuclidean_fromVec _).mp (sourceMu_normalized q hq (input x j))]
      norm_num
    have h := source_sum_norm_tensor s (sourceMu q (input x j)) (u x j)
    simp only [norm_mul,mul_pow] at h
    rw [hn,mul_one,← norm_toEuclidean_fromVec_sq] at h
    exact h
  simp_rw [Fintype.sum_prod_type]
  have hwork : (∑ j, ∑ a, ∑ k, ‖s‖^2*(‖sourceMu q (input x j) a‖^2*‖u x j k‖^2)) =
      (W/ε^2)*(∑ j, ‖toEuclidean_fromVec (u x j)‖^2) := by
    simp only [← mul_assoc,htensor]
    rw [← Finset.mul_sum,hs]
  rw [hwork]

theorem sourceForbidden_scaled_norm_le {X H : Type} [Fintype H] [DecidableEq H]
    {n q m : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ) (x : X) (hq : 0 < q)
    (hW : 0 < W) (hε : 0 < ε) (hρ : Normalized (ρ x)) (hσ : Normalized (σ x))
    (hu : (∑ j, ‖toEuclidean_fromVec (u x j)‖^2) ≤ W) :
    ‖toEuclidean_fromVec (((Real.sqrt W/ε : ℝ) : ℂ) • sourceForbidden input ρ σ u W ε x)‖^2 ≤
      W^2/ε^2+1 := by
  rw [sourceForbidden_scaled_norm input ρ σ u W ε x hq hW hε hρ hσ]
  have hmul := mul_le_mul_of_nonneg_left hu (div_nonneg hW.le (sq_nonneg ε))
  calc
    _ ≤ 1+(W/ε^2)*W := add_le_add le_rfl hmul
    _ = _ := by ring

theorem sourceGeometry_of_witness {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u v : X → Fin n → QState (Fin m)) (W ε : ℝ)
    (hnorm : ∀ x, Normalized (ρ x) ∧ Normalized (σ x))
    (hq : 0 < q) (hW : 0 < W) (hε : 0 < ε)
    (hEq : ∀ y x, (gramStateMatrix ρ-gramStateMatrix σ) y x=
      ∑ j, sourceAlphabetDelta input j y x*∑ k, star (u y j k)*v x j k)
    (hbudget : ∀ x, (∑ j, ‖toEuclidean_fromVec (u x j)‖^2) ≤ W ∧
      (∑ j, ‖toEuclidean_fromVec (v x j)‖^2) ≤ W) :
    let L := sourceComplement input ρ σ u W ε
    IsOrthogonalProjector L ∧ ∀ x,
      IsOrthogonalProjector (sourceKeep (m := m) (H := H) input x) ∧
      L *ᵥ sourceForbidden input ρ σ u W ε x=0 ∧
      L *ᵥ sourceFixed input ρ σ v W ε x=sourceFixed input ρ σ v W ε x ∧
      sourceKeep input x *ᵥ sourceFixed input ρ σ v W ε x=sourceFixed input ρ σ v W ε x ∧
      sourceKeep input x *ᵥ sourceForbidden input ρ σ u W ε x=
        ((ε/Real.sqrt W : ℝ) : ℂ) • sourceMinus (ρ x) (σ x) ∧
      ‖toEuclidean_fromVec (sourceFixed input ρ σ v W ε x-sourcePlus (ρ x) (σ x))‖^2 ≤ ε^2 ∧
      ‖toEuclidean_fromVec (((Real.sqrt W/ε : ℝ) : ℂ) •
        sourceForbidden input ρ σ u W ε x)‖^2 ≤ W^2/ε^2+1 := by
  obtain ⟨hL,hcriterion,hkill⟩ := sourceComplement_public input ρ σ u W ε
  refine ⟨hL,?_⟩
  intro x
  refine ⟨sourceKeep_isOrthogonalProjector input x hq,hkill x,?_,
    sourceKeep_fixed input ρ σ v W ε x hq,sourceKeep_forbidden input ρ σ u W ε x hq,
    sourceFixed_distance_le input ρ σ v W ε x hq hW (hbudget x).2,
    sourceForbidden_scaled_norm_le input ρ σ u W ε x hq hW hε (hnorm x).1 (hnorm x).2 (hbudget x).1⟩
  exact (hcriterion _).mpr
      (fun y => sourceForbiddenFixed_inner_zero input ρ σ u v W ε hq hW hEq y x)

theorem alphabetWitnessGeometry : AlphabetWitnessGeometry := by
  intro X H _ _ _ _ n q input ρ σ W ε hnorm hq hW hε hvalue
  obtain ⟨m,u,v,hEq,hu,hv⟩ :=
    (sourceRectValue_budget_boundary (gramStateMatrix ρ-gramStateMatrix σ)
      (sourceAlphabetDelta input) W hW.le).mp hvalue
  refine ⟨m,u,v,hEq,fun x => ⟨hu x,hv x⟩,fun a =>
    ⟨sourceMu_normalized q hq a,sourceNu_normalized q hq a⟩,
    sourceMu_sourceNu_pairing q hq,?_⟩
  exact sourceGeometry_of_witness input ρ σ u v W ε hnorm hq hW hε hEq (fun x => ⟨hu x,hv x⟩)

end Qatlib.Concepts.GramQueryCore.LowerBoundTools

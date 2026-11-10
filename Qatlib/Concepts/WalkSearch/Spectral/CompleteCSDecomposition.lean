/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.Approximation
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Mathlib.Analysis.Matrix.PosDef
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator ComplexOrder

abbrev CSIndex (a b c d m : ℕ) := Fin a ⊕ (Fin b ⊕ (Fin c ⊕ (Fin d ⊕ (Fin m×Bool))))
def csPValue {a b c d m : ℕ} : CSIndex a b c d m → ℂ
  | .inl _ => 0 | .inr (.inl _) => 1 | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inl _))) => 0
  | .inr (.inr (.inr (.inr z))) => if z.2 then 0 else 1
def csQEndpoint {a b c d m : ℕ} : CSIndex a b c d m → ℂ
  | .inr (.inl _) => 1 | .inr (.inr (.inr (.inl _))) => 1 | _ => 0
noncomputable def csQPlane (t : ℝ) (b c : Bool) : ℂ :=
  if b= c then (if b then (1-t:ℝ) else t) else Real.sqrt (t*(1-t))
noncomputable def csCanonicalP (a b c d m : ℕ) : Matrix (CSIndex a b c d m) (CSIndex a b c d m) ℂ :=
  diagonal csPValue
noncomputable def csCanonicalQ (a b c d m : ℕ) (t : Fin m→ℝ) :
    Matrix (CSIndex a b c d m) (CSIndex a b c d m) ℂ := fun i j =>
  match i,j with
  | .inr (.inr (.inr (.inr z))), .inr (.inr (.inr (.inr w))) =>
      if z.1= w.1 then csQPlane (t z.1) z.2 w.2 else 0
  | _,_ => if i= j then csQEndpoint i else 0

theorem cs_plane_isOrthogonalProjector (t : ℝ) (ht : t∈Set.Icc 0 1) :
    IsOrthogonalProjector (csQPlane t : Matrix Bool Bool ℂ) := by
  have hs : 0 ≤ t*(1-t) := mul_nonneg ht.1 (by linarith [ht.2])
  have hs2 := Real.sq_sqrt hs
  let q : Matrix Bool Bool ℂ := csQPlane t
  have hH : qᴴ=q := by
    ext a b; cases a <;> cases b <;> simp [q,csQPlane,Matrix.conjTranspose_apply]
  have hid : q*q=q := by
    ext a b
    cases a <;> cases b <;> apply Complex.ext <;>
      simp [q,csQPlane,Matrix.mul_apply,Complex.mul_re,Complex.mul_im] <;> nlinarith only [hs2]
  exact ⟨hid,hH⟩

theorem cs_canonicalP_isOrthogonalProjector (a b c d m : ℕ) :
    IsOrthogonalProjector (csCanonicalP a b c d m) := by
  have hi : ∀ i : CSIndex a b c d m,csPValue i*csPValue i=csPValue i := by
    intro i
    rcases i with i | i
    · simp [csPValue]
    · rcases i with i | i
      · norm_num [csPValue]
      · rcases i with i | i
        · norm_num [csPValue]
        · rcases i with i | ⟨i,b⟩
          · simp [csPValue]
          · cases b <;> norm_num [csPValue]
  have hh : ∀ i : CSIndex a b c d m,star (csPValue i)=csPValue i := by
    intro i
    rcases i with i | i
    · simp [csPValue]
    · rcases i with i | i
      · norm_num [csPValue]
      · rcases i with i | i
        · norm_num [csPValue]
        · rcases i with i | ⟨i,b⟩
          · simp [csPValue]
          · cases b <;> norm_num [csPValue]
  constructor
  · change diagonal csPValue*diagonal csPValue=diagonal csPValue
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact hi i
  · change (diagonal csPValue)ᴴ=diagonal csPValue
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext i; exact hh i

theorem cs_projector_eigenvalues_binary {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (i : H) :
    (show P.IsHermitian from hP.2).eigenvalues i=0 ∨
      (show P.IsHermitian from hP.2).eigenvalues i=1 := by
  let hH : P.IsHermitian := hP.2
  let u : QState H := fun j=>hH.eigenvectorBasis i j
  have he : P*ᵥu=(hH.eigenvalues i : ℂ) • u := hH.mulVec_eigenvectorBasis i
  have hid : P*P=P := hP.1
  have hu : u≠0 := by
    intro hz
    have heq : hH.eigenvectorBasis i=0 := by ext j; exact congrFun hz j
    exact hH.eigenvectorBasis.orthonormal.ne_zero i heq
  have hh := congrArg (fun A : Matrix H H ℂ=>A*ᵥu) hid

  rw [← Matrix.mulVec_mulVec,he,Matrix.mulVec_smul,he,smul_smul] at hh
  have hs : (hH.eigenvalues i : ℂ)*(hH.eigenvalues i : ℂ)=(hH.eigenvalues i : ℂ) :=
    (smul_left_injective ℂ hu) hh
  have hsR : (hH.eigenvalues i)^2=hH.eigenvalues i := by rw [pow_two]; exact_mod_cast hs
  rcases (mul_eq_zero.mp (show hH.eigenvalues i*(hH.eigenvalues i-1)=0 by nlinarith only [hsR])) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

abbrev CSProjectorSupport {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) :=
  {i : H // (show P.IsHermitian from hP.2).eigenvalues i=1}

noncomputable def csProjectorFrame {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) : Matrix H (CSProjectorSupport P hP) ℂ :=
  fun h i=>(show P.IsHermitian from hP.2).eigenvectorUnitary h i.1

theorem cs_projector_frame_range {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) :
    IsIsometry (csProjectorFrame P hP) ∧ csProjectorFrame P hP*(csProjectorFrame P hP)ᴴ=P := by
  let hH : P.IsHermitian := hP.2
  let U : Matrix H H ℂ := hH.eigenvectorUnitary
  have hU : U∈unitaryGroup H ℂ := hH.eigenvectorUnitary.property
  have hUU : Uᴴ*U=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  have hspec : P=U*diagonal (fun i=>(hH.eigenvalues i : ℂ))*Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Function.comp_def] using!
        hH.spectral_theorem
  refine ⟨?_,?_⟩
  · unfold IsIsometry
    ext i j
    have he := congrFun (congrFun hUU i.1) j.1
    simpa only [csProjectorFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
      Subtype.val_inj] using! he
  · symm
    refine hspec.trans ?_
    ext h k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,csProjectorFrame,Matrix.mul_apply]
    have hsub := Finset.sum_subtype (F:=inferInstance) (p:=fun i : H=>hH.eigenvalues i=1)
      (Finset.univ.filter (fun i=>hH.eigenvalues i=1)) (by intro i; simp)
      (fun i=>U h i*star (U k i))
    rw [← hsub,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    have hd : (∑ j,U h j*diagonal (fun i=>(hH.eigenvalues i : ℂ)) j i)=U h i*(hH.eigenvalues i : ℂ) := by
      simp [Matrix.diagonal_apply,mul_ite]
    rw [hd]
    rcases cs_projector_eigenvalues_binary P hP i with h0 | h1
    · simp only [h0,zero_ne_one,if_false,Complex.ofReal_zero,mul_zero,zero_mul]
    · simp only [h1,if_true,Complex.ofReal_one,mul_one]

private noncomputable abbrev csMatMul {M N K : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

private theorem csMatMul_assoc {M N K L : Type} [Fintype N] [Fintype K]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) (C : Matrix K L ℂ) :
    csMatMul (csMatMul A B) C=csMatMul A (csMatMul B C) := Matrix.mul_assoc A B C

theorem cs_projector_compressed_eigenframe {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    ∃ (A : Matrix H (CSProjectorSupport P hP) ℂ) (t : CSProjectorSupport P hP→ℝ),
      (∀ i,0 ≤ t i ∧ t i ≤ 1) ∧ IsIsometry A ∧ A*Aᴴ=P ∧
      csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)) := by
  let F := csProjectorFrame P hP
  have hF := cs_projector_frame_range P hP
  let C := csMatMul (csMatMul Fᴴ Q) F
  have hQs : Qᴴ=Q := hQ.2
  have hQi : Q*Q=Q := hQ.1
  have hC : C.IsHermitian := by
    change Cᴴ=C
    simp only [C,csMatMul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hQs,Matrix.mul_assoc]
  let V : Matrix (CSProjectorSupport P hP) (CSProjectorSupport P hP) ℂ := hC.eigenvectorUnitary
  let A := csMatMul F V
  have hV : V∈unitaryGroup (CSProjectorSupport P hP) ℂ := hC.eigenvectorUnitary.property
  have hV1 : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hV2 : V*Vᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  have hFA : Fᴴ*F=1 := hF.1
  have hA : IsIsometry A := by
    change Aᴴ*A=1
    calc
      _ = Vᴴ*(Fᴴ*F)*V := by simp only [A,csMatMul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hFA,Matrix.mul_one,hV1]
  have hAP : A*Aᴴ=P := by
    calc
      _ = F*(V*Vᴴ)*Fᴴ := by simp only [A,csMatMul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = P := by rw [hV2,Matrix.mul_one]; exact hF.2
  have hdiag : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(hC.eigenvalues i : ℂ)) := by
    have hd := hC.conjStarAlgAut_star_eigenvectorUnitary
    have hd' : Vᴴ*C*V=diagonal (fun i=>(hC.eigenvalues i : ℂ)) := by
      simpa only [Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,Function.comp_def] using! hd
    convert! hd' using 1 <;> simp only [A,C,csMatMul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hCG : (csMatMul Q F)ᴴ*csMatMul Q F=C := by
    calc
      _ = Fᴴ*(Qᴴ*Q)*F := by simp only [csMatMul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = C := by rw [hQs,hQi]
  have hpos : C.PosSemidef := by rw [← hCG]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hQnorm : ‖Q‖ ≤ 1 := IsStarProjection.norm_le Q hQ
  have hFnorm : ‖F‖ ≤ 1 := Qatlib.Concepts.BlockEncoding.EncodingCore.isometry_norm_le hF.1
  have hFsnorm : ‖Fᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hFnorm
  have hCnorm : ‖C‖ ≤ 1 := by
    have hh := (Matrix.l2_opNorm_mul (csMatMul Fᴴ Q) F).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Fᴴ Q) (norm_nonneg F))
    have hmul := mul_le_mul (mul_le_mul hFsnorm hQnorm (norm_nonneg Q) (by norm_num)) hFnorm
      (norm_nonneg F) (by norm_num)
    exact hh.trans (by simpa only [one_mul,mul_one] using! hmul)
  refine ⟨A,hC.eigenvalues,?_,hA,hAP,hdiag⟩
  intro i
  have htnn : 0 ≤ hC.eigenvalues i := hpos.eigenvalues_nonneg i
  let u : QState (CSProjectorSupport P hP) := fun j=>hC.eigenvectorBasis i j
  have hu : ‖toEuclidean_fromVec u‖=1 := hC.eigenvectorBasis.norm_eq_one i
  have he : C*ᵥu=(hC.eigenvalues i : ℂ) • u := hC.mulVec_eigenvectorBasis i
  have hh := Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_mulVec_fromVec_le C u
  rw [he,hu,mul_one] at hh
  change ‖(hC.eigenvalues i : ℂ) • toEuclidean_fromVec u‖ ≤ ‖C‖ at hh
  rw [norm_smul,hu,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg htnn] at hh
  exact ⟨htnn,hh.trans hCnorm⟩

private theorem cs_inner_sub_left {H : Type} [Fintype H] (u v w : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (u-v) w=Qatlib.Foundations.PureStateMath.Inner u w-Qatlib.Foundations.PureStateMath.Inner v w := by simp only [Qatlib.Foundations.PureStateMath.Inner,star_sub,sub_dotProduct]

private theorem cs_inner_sub_right {H : Type} [Fintype H] (u v w : QState H) :
    Qatlib.Foundations.PureStateMath.Inner u (v-w)=Qatlib.Foundations.PureStateMath.Inner u v-Qatlib.Foundations.PureStateMath.Inner u w := by simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct_sub]

private theorem cs_inner_smul_left {H : Type} [Fintype H] (c : ℂ) (u v : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (c • u) v=star c*Qatlib.Foundations.PureStateMath.Inner u v := by simp only [Qatlib.Foundations.PureStateMath.Inner,star_smul,smul_dotProduct,smul_eq_mul]

private theorem cs_inner_smul_right {H : Type} [Fintype H] (c : ℂ) (u v : QState H) :
    Qatlib.Foundations.PureStateMath.Inner u (c • v)=c*Qatlib.Foundations.PureStateMath.Inner u v := by simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct_smul,smul_eq_mul]

private theorem cs_inner_star {H : Type} [Fintype H] (u v : QState H) :
    star (Qatlib.Foundations.PureStateMath.Inner u v)=Qatlib.Foundations.PureStateMath.Inner v u := (star_dotProduct (v:=v) (w:=u)).symm

noncomputable def csCrossRaw {H J : Type} [Fintype H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (A : Matrix H J ℂ) (t : J→ℝ) : Matrix H J ℂ :=
  csMatMul Q A-csMatMul A (diagonal (fun i=>(t i : ℂ)))

private theorem cs_cross_column {H J : Type} [Fintype H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (A : Matrix H J ℂ) (t : J→ℝ) (i : J) :
    (fun h=>csCrossRaw Q A t h i)=Q*ᵥ(fun h=>A h i)-(t i : ℂ) • (fun h=>A h i) := by
  funext h
  simp only [csCrossRaw,csMatMul,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.mul_apply,
    Matrix.mulVec,dotProduct,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  simp [Matrix.diagonal_apply,mul_ite,mul_comm]

theorem cs_cross_raw_gram {H J : Type} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (A : Matrix H J ℂ) (t : J→ℝ)
    (hA : IsIsometry A) (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ))) :
    (csCrossRaw Q A t)ᴴ*csCrossRaw Q A t=diagonal (fun i=>Complex.ofReal (t i*(1-t i))) := by
  have hQs : Qᴴ=Q := hQ.2
  have hQi : Q*Q=Q := hQ.1
  let a := fun i : J=>fun h : H=>A h i
  have horth (i j : J) : Qatlib.Foundations.PureStateMath.Inner (a i) (a j)=if i=j then (1 : ℂ) else 0 := by
    have he := congrFun (congrFun (show Aᴴ*A=1 from hA) i) j
    simpa only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply] using! he
  have hcomp (i j : J) : Qatlib.Foundations.PureStateMath.Inner (a i) (Q*ᵥa j)=if i=j then (t i : ℂ) else 0 := by
    have ht' : csMatMul Aᴴ (csMatMul Q A)=diagonal (fun i=>(t i : ℂ)) := by
      rw [← csMatMul_assoc]; exact ht
    have he := congrFun (congrFun ht' i) j
    simp only [csMatMul,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply] at he
    simpa only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,Matrix.mulVec,dotProduct] using! he
  have hqq (i j : J) : Qatlib.Foundations.PureStateMath.Inner (Q*ᵥa i) (Q*ᵥa j)=if i=j then (t i : ℂ) else 0 := by
    rw [inner_mulVec_left_rect,hQs,Matrix.mulVec_mulVec,hQi]
    exact hcomp i j
  have hqa (i j : J) : Qatlib.Foundations.PureStateMath.Inner (Q*ᵥa i) (a j)=if i=j then (t i : ℂ) else 0 := by
    rw [← cs_inner_star,hcomp j i]
    by_cases hij : i=j
    · subst j; simp only [if_true,Complex.star_def,Complex.conj_ofReal]
    · simp [hij,Ne.symm hij]
  ext i j
  change Qatlib.Foundations.PureStateMath.Inner (fun h=>csCrossRaw Q A t h i)
      (fun h=>csCrossRaw Q A t h j)=_
  rw [cs_cross_column,cs_cross_column,cs_inner_sub_left,cs_inner_sub_right,cs_inner_sub_right,
    cs_inner_smul_left,cs_inner_smul_left,cs_inner_smul_right,cs_inner_smul_right,hqq,hqa,hcomp,horth]
  by_cases hij : i=j
  · subst j
    simp only [if_true,Complex.star_def,Complex.conj_ofReal,Matrix.diagonal_apply_eq]
    push_cast
    ring
  · simp [hij,Matrix.diagonal_apply]

noncomputable def csCrossNormalized {H J : Type} [Fintype H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (A : Matrix H J ℂ) (t : J→ℝ) : Matrix H J ℂ :=
  csMatMul (csCrossRaw Q A t) (diagonal (fun i=>(Real.sqrt (t i*(1-t i)) : ℂ)⁻¹))

theorem cs_cross_normalized_grams {H J : Type} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (A : Matrix H J ℂ) (t : J→ℝ)
    (hA : IsIsometry A) (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) :
    csMatMul Aᴴ (csCrossNormalized Q A t)=0 ∧
    (csCrossNormalized Q A t)ᴴ*csCrossNormalized Q A t=
      diagonal (fun i=>if 0<t i ∧ t i<1 then (1 : ℂ) else 0) := by
  let D := diagonal (fun i=>(Real.sqrt (t i*(1-t i)) : ℂ)⁻¹)
  have ht' : Aᴴ*Q*A=diagonal (fun i=>(t i : ℂ)) := ht
  have hAR : csMatMul Aᴴ (csCrossRaw Q A t)=0 := by
    change csMatMul Aᴴ (csMatMul Q A-csMatMul A (diagonal (fun i=>(t i : ℂ))))=0
    simp only [csMatMul,Matrix.mul_sub,← Matrix.mul_assoc]
    rw [ht',show Aᴴ*A=1 from hA,Matrix.one_mul,sub_self]
  refine ⟨?_,?_⟩
  · change csMatMul Aᴴ (csMatMul (csCrossRaw Q A t) D)=0
    rw [← csMatMul_assoc,hAR]
    exact Matrix.zero_mul _
  · have hR := cs_cross_raw_gram Q hQ A t hA ht
    calc
      _ = Dᴴ*((csCrossRaw Q A t)ᴴ*csCrossRaw Q A t)*D := by
        simp only [csCrossNormalized,csMatMul,D,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by
        rw [hR]
        simp only [D,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        have hn : 0≤t i*(1-t i) := mul_nonneg (hb i).1 (by linarith [(hb i).2])
        have hs := Real.sq_sqrt hn
        by_cases hi : 0<t i ∧ t i<1
        · have hp : 0<Real.sqrt (t i*(1-t i)) := Real.sqrt_pos.mpr (mul_pos hi.1 (by linarith [hi.2]))
          simp only [if_pos hi,Pi.star_apply,Complex.star_def,map_inv₀,Complex.conj_ofReal]
          have hsC : (Real.sqrt (t i*(1-t i)) : ℂ)^2=Complex.ofReal (t i*(1-t i)) := by
            exact_mod_cast hs
          rw [← hsC]
          field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
        · by_cases hz : t i=0
          · simp [hz]
          · have hp : 0<t i := lt_of_le_of_ne (hb i).1 (Ne.symm hz)
            have he : t i=1 := le_antisymm (hb i).2 (le_of_not_gt (fun hlt=>hi ⟨hp,hlt⟩))
            simp [he]

private theorem cs_cross_normalized_column {H J : Type} [Fintype H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (A : Matrix H J ℂ) (t : J→ℝ) (i : J) :
    (fun h=>csCrossNormalized Q A t h i)=(Real.sqrt (t i*(1-t i)) : ℂ)⁻¹ •
      (fun h=>csCrossRaw Q A t h i) := by
  funext h
  simp [csCrossNormalized,csMatMul,Matrix.mul_apply,Matrix.diagonal_apply,mul_ite,mul_comm]

theorem cs_cross_scale_recovery {H J : Type} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (A : Matrix H J ℂ) (t : J→ℝ)
    (hA : IsIsometry A) (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) (i : J) :
    (fun h=>csCrossRaw Q A t h i)=(Real.sqrt (t i*(1-t i)) : ℂ) •
      (fun h=>csCrossNormalized Q A t h i) := by
  let s := Real.sqrt (t i*(1-t i))
  rw [cs_cross_normalized_column,smul_smul]
  by_cases hs : s=0
  · have hn : 0≤t i*(1-t i) := mul_nonneg (hb i).1 (by linarith [(hb i).2])
    have hprod : t i*(1-t i)=0 := by rw [← Real.sq_sqrt hn]; change s^2=0; rw [hs]; norm_num
    have hh := congrFun (congrFun (cs_cross_raw_gram Q hQ A t hA ht) i) i
    rw [Matrix.diagonal_apply_eq,hprod,Complex.ofReal_zero] at hh
    change Qatlib.Foundations.PureStateMath.Inner (fun h=>csCrossRaw Q A t h i)
        (fun h=>csCrossRaw Q A t h i)=0 at hh
    have hz := dotProduct_star_self_eq_zero.mp hh
    rw [hz]
    exact (smul_zero _).symm
  · have hsC : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs
    rw [mul_inv_cancel₀ hsC,one_smul]

theorem cs_cross_Q_actions {H J : Type} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (A : Matrix H J ℂ) (t : J→ℝ)
    (hA : IsIsometry A) (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) :
    csMatMul Q A=csMatMul A (diagonal (fun i=>(t i : ℂ)))+
      csMatMul (csCrossNormalized Q A t) (diagonal (fun i=>(Real.sqrt (t i*(1-t i)) : ℂ))) ∧
    csMatMul Q (csCrossNormalized Q A t)=
      csMatMul A (diagonal (fun i=>(Real.sqrt (t i*(1-t i)) : ℂ)))+
        csMatMul (csCrossNormalized Q A t) (diagonal (fun i=>Complex.ofReal (1-t i))) := by
  have hQi : Q*Q=Q := hQ.1
  let a := fun i : J=>fun h : H=>A h i
  let b := fun i : J=>fun h : H=>csCrossNormalized Q A t h i
  let r := fun i : J=>fun h : H=>csCrossRaw Q A t h i
  have hrec (i : J) : r i=(Real.sqrt (t i*(1-t i)) : ℂ) • b i :=
      cs_cross_scale_recovery Q hQ A t hA ht hb i
  have hqa (i : J) : Q*ᵥa i=(t i : ℂ) • a i+(Real.sqrt (t i*(1-t i)) : ℂ) • b i := by
    have he := cs_cross_column Q A t i
    change r i=Q*ᵥa i-(t i : ℂ) • a i at he
    rw [hrec] at he
    have hh := congrArg (fun v=>v+(t i : ℂ) • a i) he.symm
    simp only [sub_add_cancel] at hh
    exact hh.trans (add_comm _ _)
  have hqb (i : J) : Q*ᵥb i=(Real.sqrt (t i*(1-t i)) : ℂ) • a i+(1-(t i : ℂ)) • b i := by
    let s := Real.sqrt (t i*(1-t i))
    by_cases hs : s=0
    · have hbi : b i=0 := by
        change (fun h=>csCrossNormalized Q A t h i)=0
        rw [cs_cross_normalized_column]
        change (s : ℂ)⁻¹ • r i=0
        rw [hs]; simp
      rw [hbi,Matrix.mulVec_zero]
      simp only [smul_zero,add_zero]
      change 0=(s : ℂ) • a i
      rw [hs]; simp
    · have hsC : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs
      have hn : 0≤t i*(1-t i) := mul_nonneg (hb i).1 (by linarith [(hb i).2])
      have hs2 : (s : ℂ)^2=(t i : ℂ)*(1-(t i : ℂ)) := by
        have he := congrArg Complex.ofReal (Real.sq_sqrt hn)
        simpa only [Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one] using! he
      have hc1 : (s : ℂ)⁻¹*(1-(t i : ℂ))*(t i : ℂ)=(s : ℂ) := by
        field_simp
        all_goals rw [hs2]
        all_goals ring
      have hc2 : (s : ℂ)⁻¹*(1-(t i : ℂ))*(s : ℂ)=1-(t i : ℂ) := by field_simp
      have hbi : b i=(s : ℂ)⁻¹ • r i := cs_cross_normalized_column Q A t i
      have hqr : Q*ᵥr i=(1-(t i : ℂ)) • (Q*ᵥa i) := by
        change Q*ᵥ(fun h=>csCrossRaw Q A t h i)=_
        rw [cs_cross_column,Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_mulVec,hQi]
        module
      calc
        _ = (s : ℂ)⁻¹ • (Q*ᵥr i) := by rw [hbi,Matrix.mulVec_smul]
        _ = _ := by rw [hqr,hqa,smul_smul,smul_add,smul_smul,smul_smul,hc1,hc2]
  constructor
  · ext h i
    have he := congrFun (hqa i) h
    simpa [csMatMul,a,b,Matrix.mul_apply,Matrix.diagonal_apply,mul_ite,mul_comm] using! he
  · ext h i
    have he := congrFun (hqb i) h
    simp only [csMatMul,Matrix.mul_apply,Matrix.mul_diagonal,Matrix.add_apply,Matrix.mulVec,dotProduct,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he ⊢
    simp [Matrix.diagonal_apply,mul_ite,Complex.ofReal_sub,mul_comm] at he ⊢
    simpa only [a,b] using! he

private theorem cs_real_diagonal_adjoint {J : Type} [DecidableEq J] (f : J→ℝ) :
    (diagonal (fun i=>(f i : ℂ)))ᴴ=diagonal (fun i=>(f i : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp only [Pi.star_apply,Complex.star_def,Complex.conj_ofReal]

theorem cs_busy_sum_isProjector_and_commutes {H J : Type} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (A : Matrix H J ℂ) (t : J→ℝ)
    (hA : IsIsometry A) (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) :
    let B := csCrossNormalized Q A t;
    IsOrthogonalProjector (A*Aᴴ+B*Bᴴ) ∧ Q*(A*Aᴴ+B*Bᴴ)=(A*Aᴴ+B*Bᴴ)*Q ∧
      (A*Aᴴ)*(A*Aᴴ+B*Bᴴ)=A*Aᴴ := by
  let B := csCrossNormalized Q A t
  let D := diagonal (fun i=>if 0<t i ∧ t i<1 then (1 : ℂ) else 0)
  change IsOrthogonalProjector (A*Aᴴ+B*Bᴴ) ∧ Q*(A*Aᴴ+B*Bᴴ)=(A*Aᴴ+B*Bᴴ)*Q ∧ (A*Aᴴ)*(A*Aᴴ+B*Bᴴ)=A*Aᴴ
  have hg := cs_cross_normalized_grams Q hQ A t hA ht hb
  have hAB : Aᴴ*B=0 := hg.1
  have hBA : Bᴴ*A=0 := by
    have he := congrArg Matrix.conjTranspose hAB
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using! he
  have hGB : Bᴴ*B=D := hg.2
  have hBD : B*D=B := by
    ext h i
    rw [Matrix.mul_diagonal]
    by_cases hi : 0<t i ∧ t i<1
    · simp [D,hi]
    · have he := congrFun (congrFun hGB i) i
      simp only [D,Matrix.diagonal_apply_eq,if_neg hi] at he
      change Qatlib.Foundations.PureStateMath.Inner (fun h=>B h i) (fun h=>B h i)=0 at he
      have hz := dotProduct_star_self_eq_zero.mp he
      have hzi : B h i=0 := congrFun hz h
      simp [D,hi,hzi]
  have hBproj : IsOrthogonalProjector (B*Bᴴ) := by
    constructor
    · change (B*Bᴴ)*(B*Bᴴ)=B*Bᴴ
      calc
        _ = B*(Bᴴ*B)*Bᴴ := by simp only [Matrix.mul_assoc]
        _ = B*Bᴴ := by rw [hGB,hBD]
    · change (B*Bᴴ)ᴴ=B*Bᴴ
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have hAproj := rangeProjector_isOrthogonalProjector hA
  have hAA : (A*Aᴴ)*(A*Aᴴ)=A*Aᴴ := hAproj.1
  have hBB : (B*Bᴴ)*(B*Bᴴ)=B*Bᴴ := hBproj.1
  have hzero1 : (A*Aᴴ)*(B*Bᴴ)=0 := by
    calc
      _ = A*(Aᴴ*B)*Bᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hAB]; simp
  have hzero2 : (B*Bᴴ)*(A*Aᴴ)=0 := by
    calc
      _ = B*(Bᴴ*A)*Aᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBA]; simp
  have hsum : IsOrthogonalProjector (A*Aᴴ+B*Bᴴ) := by
    constructor
    · change (A*Aᴴ+B*Bᴴ)*(A*Aᴴ+B*Bᴴ)=A*Aᴴ+B*Bᴴ
      simp only [Matrix.add_mul,Matrix.mul_add,hAA,hBB,hzero1,hzero2,add_zero,zero_add]
    · change (A*Aᴴ+B*Bᴴ)ᴴ=A*Aᴴ+B*Bᴴ
      simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have hQA := (cs_cross_Q_actions Q hQ A t hA ht hb).1
  have hQB := (cs_cross_Q_actions Q hQ A t hA ht hb).2
  let Dt := diagonal (fun i=>(t i : ℂ))
  let Ds := diagonal (fun i=>(Real.sqrt (t i*(1-t i)) : ℂ))
  let Dc := diagonal (fun i=>Complex.ofReal (1-t i))
  have hqa : Q*A=A*Dt+B*Ds := hQA
  have hqb : Q*B=A*Ds+B*Dc := hQB
  have hQa : Aᴴ*Q=Dt*Aᴴ+Ds*Bᴴ := by
    have he := congrArg Matrix.conjTranspose hqa
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_add,show Qᴴ=Q from hQ.2,
      Dt,Ds,Dc,cs_real_diagonal_adjoint] using! he
  have hQb : Bᴴ*Q=Ds*Aᴴ+Dc*Bᴴ := by
    have he := congrArg Matrix.conjTranspose hqb
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_add,show Qᴴ=Q from hQ.2,
      Dt,Ds,Dc,cs_real_diagonal_adjoint] using! he
  refine ⟨hsum,?_,?_⟩
  · calc
      _ = (Q*A)*Aᴴ+(Q*B)*Bᴴ := by simp only [Matrix.mul_add,Matrix.mul_assoc]
      _ = A*Dt*Aᴴ+B*Ds*Aᴴ+A*Ds*Bᴴ+B*Dc*Bᴴ := by rw [hqa,hqb]; simp only [Matrix.add_mul]; abel
      _ = A*(Dt*Aᴴ+Ds*Bᴴ)+B*(Ds*Aᴴ+Dc*Bᴴ) := by simp only [Matrix.mul_add,Matrix.mul_assoc]; abel
      _ = (A*Aᴴ+B*Bᴴ)*Q := by rw [← hQa,← hQb]; simp only [Matrix.add_mul,Matrix.mul_assoc]
  · simp only [Matrix.mul_add,hAA,hzero1,add_zero]

private theorem cs_commuting_projector_product {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hc : P*Q=Q*P) : IsOrthogonalProjector (P*Q) := by
  have hPi : P*P=P := hP.1
  have hQi : Q*Q=Q := hQ.1
  have hPs : Pᴴ=P := hP.2
  have hQs : Qᴴ=Q := hQ.2
  constructor
  · change (P*Q)*(P*Q)=P*Q
    calc
      _ = P*(Q*P)*Q := by simp only [Matrix.mul_assoc]
      _ = P*Q := by rw [← hc,← Matrix.mul_assoc,hPi,Matrix.mul_assoc,hQi]
  · change (P*Q)ᴴ=P*Q
    rw [Matrix.conjTranspose_mul,hPs,hQs,← hc]

theorem cs_residual_endpoint_projectors {H : Type} [Fintype H] [DecidableEq H]
    (Q T : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hT : IsOrthogonalProjector T)
    (hc : Q*T=T*Q) :
    IsOrthogonalProjector ((1-T)*(1-Q)) ∧ IsOrthogonalProjector ((1-T)*Q) ∧
    (1-T)*(1-Q)+(1-T)*Q=1-T ∧ Q*((1-T)*(1-Q))=0 ∧ Q*((1-T)*Q)=(1-T)*Q := by
  have hC := isOrthogonalProjector_compl hT
  have hQc := isOrthogonalProjector_compl hQ
  have hQi : Q*Q=Q := hQ.1
  have hCQ : (1-T)*Q=Q*(1-T) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,← hc]
  have hCQc : (1-T)*(1-Q)=(1-Q)*(1-T) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
    rw [hc]
    abel
  refine ⟨cs_commuting_projector_product (1-T) (1-Q) hC hQc hCQc,
    cs_commuting_projector_product (1-T) Q hC hQ hCQ,?_,?_,?_⟩
  · rw [← Matrix.mul_add,sub_add_cancel,Matrix.mul_one]
  · calc
      _ = (1-T)*(Q*(1-Q)) := by rw [← Matrix.mul_assoc,← hCQ,Matrix.mul_assoc]
      _ = 0 := by rw [Matrix.mul_sub,Matrix.mul_one,hQi,sub_self,Matrix.mul_zero]
  · calc
      _ = (1-T)*(Q*Q) := by rw [← Matrix.mul_assoc,← hCQ,Matrix.mul_assoc]
      _ = _ := by rw [hQi]

theorem cs_projector_frame_fixed {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) :
    csMatMul P (csProjectorFrame P hP)=csProjectorFrame P hP := by
  have hf := cs_projector_frame_range P hP
  have hgram : (csProjectorFrame P hP)ᴴ*csProjectorFrame P hP=1 := hf.1
  calc
    _ = csMatMul (csProjectorFrame P hP*(csProjectorFrame P hP)ᴴ) (csProjectorFrame P hP) := by rw [hf.2]
    _ = csProjectorFrame P hP := by simp only [csMatMul,Matrix.mul_assoc,hgram,Matrix.mul_one]

private theorem cs_fromCols_isometry {H J K : Type} [Fintype H] [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K] (A : Matrix H J ℂ) (B : Matrix H K ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (hAB : csMatMul Aᴴ B=0) :
    IsIsometry (Matrix.fromCols A B) := by
  have hBA : csMatMul Bᴴ A=0 := by
    have hs := congrArg Matrix.conjTranspose hAB
    simpa only [csMatMul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using! hs
  unfold IsIsometry
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr,Matrix.one_apply,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,if_false]
  · exact congrFun (congrFun (show Aᴴ*A=1 from hA) _) _
  · exact congrFun (congrFun hAB _) _
  · exact congrFun (congrFun hBA _) _
  · exact congrFun (congrFun (show Bᴴ*B=1 from hB) _) _

private theorem cs_fromCols_range {H J K : Type} [Fintype J] [Fintype K]
    (A : Matrix H J ℂ) (B : Matrix H K ℂ) :
    Matrix.fromCols A B * (Matrix.fromCols A B)ᴴ=A*Aᴴ+B*Bᴴ := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,Matrix.fromCols_mul_fromRows]

private theorem cs_cross_endpoint_zero {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q)
    (A : Matrix H J ℂ) (t : J→ℝ) (hA : IsIsometry A)
    (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) (i : J) (hi : ¬(0<t i ∧ t i<1)) :
    (fun h=>csCrossNormalized Q A t h i)=0 := by
  have hg := congrFun (congrFun (cs_cross_normalized_grams Q hQ A t hA ht hb).2 i) i
  simp only [Matrix.diagonal_apply_eq,if_neg hi] at hg
  exact dotProduct_star_self_eq_zero.mp hg

theorem cs_interior_partner_isometry {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q)
    (A : Matrix H J ℂ) (t : J→ℝ) (hA : IsIsometry A)
    (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) :
    IsIsometry ((csCrossNormalized Q A t).submatrix id
      (Subtype.val : {i : J // 0<t i ∧ t i<1}→J)) ∧
    let B := csCrossNormalized Q A t;
    let Bm := B.submatrix id (Subtype.val : {i : J // 0<t i ∧ t i<1}→J);
    Bm*Bmᴴ=B*Bᴴ := by
  let B := csCrossNormalized Q A t
  have hg : Bᴴ*B=diagonal (fun i=>if 0<t i ∧ t i<1 then (1:ℂ) else 0) :=
    (cs_cross_normalized_grams Q hQ A t hA ht hb).2
  constructor
  · unfold IsIsometry
    ext i j
    have he := congrFun (congrFun hg i.1) j.1
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply,id_eq,
      Matrix.diagonal_apply,if_pos i.2,Matrix.one_apply,Subtype.val_inj] using! he
  · ext h k
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply,id_eq]
    have hs := Finset.sum_subtype (F:=inferInstance) (p:=fun i : J=>0<t i ∧ t i<1)
      (Finset.univ.filter (fun i=>0<t i ∧ t i<1)) (by intro i; simp)
      (fun i=>B h i*star (B k i))
    rw [← hs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    change (if 0<t i ∧ t i<1 then B h i*star (B k i) else 0)=B h i*star (B k i)
    by_cases hi : 0<t i ∧ t i<1
    · simp [hi]
    · have hz := cs_cross_endpoint_zero Q hQ A t hA ht hb i hi
      have hzi : B h i=0 := congrFun hz h
      simp [hi,hzi]

theorem cs_complete_reducing_frame {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q)
    (A : Matrix H J ℂ) (t : J→ℝ) (hA : IsIsometry A)
    (ht : csMatMul (csMatMul Aᴴ Q) A=diagonal (fun i=>(t i : ℂ)))
    (hb : ∀ i,t i∈Set.Icc 0 1) :
    let B := csCrossNormalized Q A t;
    let T := A*Aᴴ+B*Bᴴ;
    let hT := cs_busy_sum_isProjector_and_commutes Q hQ A t hA ht hb;
    let he := cs_residual_endpoint_projectors Q T hQ hT.1 hT.2.1;
    let C := csProjectorFrame ((1-T)*(1-Q)) he.1;
    let D := csProjectorFrame ((1-T)*Q) he.2.1;
    let Bm := B.submatrix id (Subtype.val : {i : J // 0<t i ∧ t i<1}→J);
    let V := Matrix.fromCols C (Matrix.fromCols A (Matrix.fromCols D Bm));
    IsIsometry V ∧ V*Vᴴ=1 ∧ csMatMul (A*Aᴴ) C=0 ∧ csMatMul (A*Aᴴ) D=0 ∧
      csMatMul Q C=0 ∧ csMatMul Q D=D := by
  let B := csCrossNormalized Q A t
  let T := A*Aᴴ+B*Bᴴ
  have hT := cs_busy_sum_isProjector_and_commutes Q hQ A t hA ht hb
  have he := cs_residual_endpoint_projectors Q T hQ hT.1 hT.2.1
  let C := csProjectorFrame ((1-T)*(1-Q)) he.1
  let D := csProjectorFrame ((1-T)*Q) he.2.1
  let Bm := B.submatrix id (Subtype.val : {i : J // 0<t i ∧ t i<1}→J)
  change IsIsometry (Matrix.fromCols C (Matrix.fromCols A (Matrix.fromCols D Bm))) ∧
    Matrix.fromCols C (Matrix.fromCols A (Matrix.fromCols D Bm)) *
      (Matrix.fromCols C (Matrix.fromCols A (Matrix.fromCols D Bm)))ᴴ=1 ∧
    csMatMul (A*Aᴴ) C=0 ∧ csMatMul (A*Aᴴ) D=0 ∧ csMatMul Q C=0 ∧ csMatMul Q D=D
  have hC := cs_projector_frame_range ((1-T)*(1-Q)) he.1
  have hD := cs_projector_frame_range ((1-T)*Q) he.2.1
  have hBm := cs_interior_partner_isometry Q hQ A t hA ht hb
  have hTC : csMatMul T C=0 := by
    apply (Matrix.mul_self_mul_conjTranspose_eq_zero C T).mp
    have hzero : T*(1-T)=0 := by
      rw [Matrix.mul_sub,Matrix.mul_one,show T*T=T from hT.1.1,sub_self]
    rw [hC.2,← Matrix.mul_assoc,hzero,Matrix.zero_mul]
  have hTD : csMatMul T D=0 := by
    apply (Matrix.mul_self_mul_conjTranspose_eq_zero D T).mp
    rw [hD.2,← Matrix.mul_assoc,Matrix.mul_sub,Matrix.mul_one,
      show T*T=T from hT.1.1,sub_self,Matrix.zero_mul]
  have hPT : csMatMul (A*Aᴴ) T=A*Aᴴ := hT.2.2
  have hPC : csMatMul (A*Aᴴ) C=0 := by
    calc
      _ = csMatMul (csMatMul (A*Aᴴ) T) C := by rw [hPT]
      _ = 0 := by rw [csMatMul_assoc,hTC]; exact Matrix.mul_zero _
  have hPD : csMatMul (A*Aᴴ) D=0 := by
    calc
      _ = csMatMul (csMatMul (A*Aᴴ) T) D := by rw [hPT]
      _ = 0 := by rw [csMatMul_assoc,hTD]; exact Matrix.mul_zero _
  have hBC : csMatMul (B*Bᴴ) C=0 := by
    have hs : B*Bᴴ=T-A*Aᴴ := by dsimp [T]; abel
    rw [hs,show csMatMul (T-A*Aᴴ) C=csMatMul T C-csMatMul (A*Aᴴ) C from Matrix.sub_mul _ _ _,hTC,hPC,sub_self]
  have hBD : csMatMul (B*Bᴴ) D=0 := by
    have hs : B*Bᴴ=T-A*Aᴴ := by dsimp [T]; abel
    rw [hs,show csMatMul (T-A*Aᴴ) D=csMatMul T D-csMatMul (A*Aᴴ) D from Matrix.sub_mul _ _ _,hTD,hPD,sub_self]
  have hAC : csMatMul Aᴴ C=0 := (Matrix.self_mul_conjTranspose_mul_eq_zero A C).mp hPC
  have hAD : csMatMul Aᴴ D=0 := (Matrix.self_mul_conjTranspose_mul_eq_zero A D).mp hPD
  have hBC' : csMatMul Bᴴ C=0 := (Matrix.self_mul_conjTranspose_mul_eq_zero B C).mp hBC
  have hBD' : csMatMul Bᴴ D=0 := (Matrix.self_mul_conjTranspose_mul_eq_zero B D).mp hBD
  have hQC : csMatMul Q C=0 := by
    apply (Matrix.mul_self_mul_conjTranspose_eq_zero C Q).mp
    rw [hC.2]
    exact he.2.2.2.1
  have hQD : csMatMul Q D=D := by
    have hfixed := cs_projector_frame_fixed ((1-T)*Q) he.2.1
    change csMatMul ((1-T)*Q) D=D at hfixed
    calc
      _ = csMatMul Q (csMatMul ((1-T)*Q) D) := by rw [hfixed]
      _ = D := by
        have hQQ : csMatMul Q ((1-T)*Q)=(1-T)*Q := he.2.2.2.2
        rw [← csMatMul_assoc]
        exact (congrArg (fun X : Matrix H H ℂ => csMatMul X D) hQQ).trans hfixed
  have hCD : csMatMul Cᴴ D=0 := by
    apply (Matrix.self_mul_conjTranspose_mul_eq_zero C D).mp
    rw [hC.2]
    change csMatMul ((1-T)*(1-Q)) D=0
    rw [csMatMul_assoc,show csMatMul (1-Q) D=D-csMatMul Q D from by simp [csMatMul,Matrix.sub_mul],
      hQD,sub_self]
    exact Matrix.mul_zero _
  have hCBm : csMatMul Cᴴ Bm=0 := by
    have hs := congrArg Matrix.conjTranspose hBC'
    have hh : csMatMul Cᴴ B=0 := by
      simpa only [csMatMul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using! hs
    ext i j
    exact congrFun (congrFun hh i) j.1
  have hDBm : csMatMul Dᴴ Bm=0 := by
    have hs := congrArg Matrix.conjTranspose hBD'
    have hh : csMatMul Dᴴ B=0 := by
      simpa only [csMatMul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using! hs
    ext i j
    exact congrFun (congrFun hh i) j.1
  have hABm : csMatMul Aᴴ Bm=0 := by
    have hh := (cs_cross_normalized_grams Q hQ A t hA ht hb).1
    ext i j
    exact congrFun (congrFun hh i) j.1
  have hCA : csMatMul Cᴴ A=0 := by
    have hs := congrArg Matrix.conjTranspose hAC
    simpa only [csMatMul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using! hs
  have hAX : csMatMul Aᴴ (Matrix.fromCols D Bm)=0 := by
    ext i j
    cases j <;>
      simp only [csMatMul,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.fromCols_apply_inl,
        Matrix.fromCols_apply_inr,Matrix.zero_apply]
    · exact congrFun (congrFun hAD i) _
    · exact congrFun (congrFun hABm i) _
  have hCX : csMatMul Cᴴ (Matrix.fromCols A (Matrix.fromCols D Bm))=0 := by
    ext i j
    rcases j with j | j
    · exact congrFun (congrFun hCA i) j
    · rcases j with j | j
      · exact congrFun (congrFun hCD i) j
      · exact congrFun (congrFun hCBm i) j
  refine ⟨cs_fromCols_isometry _ _ hC.1
    (cs_fromCols_isometry _ _ hA (cs_fromCols_isometry _ _ hD.1 hBm.1 hDBm) hAX) hCX,
    ?_,hPC,hPD,hQC,hQD⟩
  rw [cs_fromCols_range,cs_fromCols_range,cs_fromCols_range,hC.2,hD.2,hBm.2]
  have hs := he.2.2.1
  change (1-T)*(1-Q)+(1-T)*Q=1-T at hs
  change (1-T)*(1-Q)+(A*Aᴴ+((1-T)*Q+B*Bᴴ))=1
  calc
    _ = T+((1-T)*(1-Q)+(1-T)*Q) := by dsimp [T]; abel
    _ = 1 := by rw [hs,add_sub_cancel]

private abbrev CSInterior {J : Type} (t : J→ℝ) := {i : J // 0<t i ∧ t i<1}
private abbrev CSMixedIndex (K0 K1 J : Type) (t : J→ℝ) := K0 ⊕ (J ⊕ (K1 ⊕ CSInterior t))

private noncomputable def csCoordinateEquiv (K0 K1 J : Type)
    [Fintype K0] [Fintype K1] [Fintype J] (t : J→ℝ) (hb : ∀ i,t i∈Set.Icc 0 1) :
    CSIndex (Fintype.card K0) (Fintype.card {i : J // t i=1})
      (Fintype.card {i : J // t i=0}) (Fintype.card K1) (Fintype.card (CSInterior t)) ≃
      CSMixedIndex K0 K1 J t := by
  classical
  let eC := (Fintype.equivFin K0).symm
  let eD := (Fintype.equivFin K1).symm
  let e1 := (Fintype.equivFin {i : J // t i=1}).symm
  let e0 := (Fintype.equivFin {i : J // t i=0}).symm
  let em := (Fintype.equivFin (CSInterior t)).symm
  have hm (i : J) (h1 : t i≠1) (h0 : t i≠0) : 0<t i ∧ t i<1 :=
    ⟨lt_of_le_of_ne (hb i).1 (Ne.symm h0),lt_of_le_of_ne (hb i).2 h1⟩
  refine {
    toFun := fun z => match z with
      | .inl i => .inl (eC i)
      | .inr (.inl i) => .inr (.inl (e1 i).1)
      | .inr (.inr (.inl i)) => .inr (.inl (e0 i).1)
      | .inr (.inr (.inr (.inl i))) => .inr (.inr (.inl (eD i)))
      | .inr (.inr (.inr (.inr z))) => if z.2 then .inr (.inr (.inr (em z.1))) else .inr (.inl (em z.1).1)
    invFun := fun z => match z with
      | .inl i => .inl (eC.symm i)
      | .inr (.inl i) => if h1 : t i=1 then .inr (.inl (e1.symm ⟨i,h1⟩)) else
          if h0 : t i=0 then .inr (.inr (.inl (e0.symm ⟨i,h0⟩))) else
            .inr (.inr (.inr (.inr (em.symm ⟨i,hm i h1 h0⟩,false))))
      | .inr (.inr (.inl i)) => .inr (.inr (.inr (.inl (eD.symm i))))
      | .inr (.inr (.inr i)) => .inr (.inr (.inr (.inr (em.symm i,true))))
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    rcases z with i | i
    · simp
    · rcases i with i | i
      · simp only [(e1 i).2,dif_pos]
        change Sum.inr (Sum.inl (e1.symm (e1 i)))=Sum.inr (Sum.inl i)
        rw [e1.symm_apply_apply]
      · rcases i with i | i
        · simp only [(e0 i).2,zero_ne_one,dif_neg,dif_pos,not_false_eq_true]
          change Sum.inr (Sum.inr (Sum.inl (e0.symm (e0 i))))=Sum.inr (Sum.inr (Sum.inl i))
          rw [e0.symm_apply_apply]
        · rcases i with i | ⟨i,b⟩
          · simp
          · cases b <;>
              simp [ne_of_gt (em i).2.1,ne_of_lt (em i).2.2]
  · intro z
    rcases z with i | i
    · simp
    · rcases i with i | i
      · by_cases h1 : t i=1
        · simp [h1]
        · by_cases h0 : t i=0 <;> simp [h1,h0]
      · rcases i with i | i <;> simp

private theorem cs_canonicalQ_column {H : Type} {a b c d m : ℕ}
    (V : Matrix H (CSIndex a b c d m) ℂ) (t : Fin m→ℝ) (h : H)
    (i : CSIndex a b c d m) :
    (csMatMul V (csCanonicalQ a b c d m t)) h i = match i with
      | .inl _ => 0
      | .inr (.inl _) => V h i
      | .inr (.inr (.inl _)) => 0
      | .inr (.inr (.inr (.inl _))) => V h i
      | .inr (.inr (.inr (.inr z))) =>
          if z.2 then
            V h (.inr (.inr (.inr (.inr (z.1,false))))) * (Real.sqrt (t z.1*(1-t z.1)):ℂ) +
            V h (.inr (.inr (.inr (.inr (z.1,true))))) * (1-(t z.1:ℂ))
          else
            V h (.inr (.inr (.inr (.inr (z.1,false))))) * (t z.1:ℂ) +
            V h (.inr (.inr (.inr (.inr (z.1,true))))) * (Real.sqrt (t z.1*(1-t z.1)):ℂ) := by
  rcases i with i | i
  · simp [csMatMul,Matrix.mul_apply,Fintype.sum_sum_type,csCanonicalQ,csQEndpoint,ite_mul]
  · rcases i with i | i
    · simp [csMatMul,Matrix.mul_apply,Fintype.sum_sum_type,csCanonicalQ,csQEndpoint,ite_mul]
    · rcases i with i | i
      · simp [csMatMul,Matrix.mul_apply,Fintype.sum_sum_type,csCanonicalQ,csQEndpoint,ite_mul]
      · rcases i with i | ⟨i,b⟩
        · simp [csMatMul,Matrix.mul_apply,Fintype.sum_sum_type,csCanonicalQ,csQEndpoint,ite_mul]
        · cases b <;> simp [csMatMul,Matrix.mul_apply,Fintype.sum_sum_type,Fintype.sum_prod_type,
            csCanonicalQ,csQPlane,ite_mul,Complex.ofReal_sub,add_comm]

theorem complete_two_projector_cs_normal_form :
    ∀ (H : Type) [Fintype H] [DecidableEq H] (P Q : Matrix H H ℂ),
    IsOrthogonalProjector P → IsOrthogonalProjector Q →
    ∃ (a b c d m : ℕ) (t : Fin m→ℝ) (V : Matrix H (CSIndex a b c d m) ℂ),
      (∀ i,0<t i ∧ t i<1) ∧ IsIsometry V ∧ V*Vᴴ=1 ∧
      P=V*csCanonicalP a b c d m*Vᴴ ∧ Q=V*csCanonicalQ a b c d m t*Vᴴ := by
  intro H _ _ P Q hP hQ
  classical
  obtain ⟨A,t,hb,hA,hAP,ht⟩ := cs_projector_compressed_eigenframe P Q hP hQ
  let J := CSProjectorSupport P hP
  let B := csCrossNormalized Q A t
  let T := A*Aᴴ+B*Bᴴ
  have hT := cs_busy_sum_isProjector_and_commutes Q hQ A t hA ht hb
  have he := cs_residual_endpoint_projectors Q T hQ hT.1 hT.2.1
  let K0 := CSProjectorSupport ((1-T)*(1-Q)) he.1
  let K1 := CSProjectorSupport ((1-T)*Q) he.2.1
  let C := csProjectorFrame ((1-T)*(1-Q)) he.1
  let D := csProjectorFrame ((1-T)*Q) he.2.1
  let Bm := B.submatrix id (Subtype.val : CSInterior t→J)
  let W : Matrix H (CSMixedIndex K0 K1 J t) ℂ :=
    Matrix.fromCols C (Matrix.fromCols A (Matrix.fromCols D Bm))
  have hfull : IsIsometry W ∧ W*Wᴴ=1 ∧ csMatMul (A*Aᴴ) C=0 ∧
      csMatMul (A*Aᴴ) D=0 ∧ csMatMul Q C=0 ∧ csMatMul Q D=D :=
    cs_complete_reducing_frame Q hQ A t hA ht hb
  let a := Fintype.card K0
  let b := Fintype.card {i : J // t i=1}
  let c := Fintype.card {i : J // t i=0}
  let d := Fintype.card K1
  let m := Fintype.card (CSInterior t)
  let em := (Fintype.equivFin (CSInterior t)).symm
  let e1 := (Fintype.equivFin {i : J // t i=1}).symm
  let e0 := (Fintype.equivFin {i : J // t i=0}).symm
  let eC := (Fintype.equivFin K0).symm
  let eD := (Fintype.equivFin K1).symm
  let e := csCoordinateEquiv K0 K1 J t hb
  let V : Matrix H (CSIndex a b c d m) ℂ := W.submatrix id e
  let ti : Fin m→ℝ := fun i => t (em i).1
  have hV : IsIsometry V := by
    unfold IsIsometry
    ext i j
    have hs := congrFun (congrFun (show Wᴴ*W=1 from hfull.1) (e i)) (e j)
    simpa only [V,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply,id_eq,
      Matrix.one_apply,e.injective.eq_iff] using! hs
  have hVV : V*Vᴴ=1 := by
    have hs := Matrix.submatrix_mul W Wᴴ id e id e.bijective
    rw [hfull.2.1] at hs
    simpa only [V,Matrix.conjTranspose_submatrix,Matrix.submatrix_id_id] using! hs.symm
  have hPA : csMatMul P A=A := by
    calc
      _ = csMatMul (A*Aᴴ) A := congrArg (fun X : Matrix H H ℂ => csMatMul X A) hAP.symm
      _ = A := by simp only [csMatMul,Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.mul_one]
  have hPB : csMatMul P B=0 := by
    calc
      _ = csMatMul (A*Aᴴ) B := congrArg (fun X : Matrix H H ℂ => csMatMul X B) hAP.symm
      _ = 0 := by
        rw [csMatMul_assoc,(cs_cross_normalized_grams Q hQ A t hA ht hb).1]
        exact Matrix.mul_zero _
  have hPC : csMatMul P C=0 := by
    calc
      _ = csMatMul (A*Aᴴ) C := congrArg (fun X : Matrix H H ℂ => csMatMul X C) hAP.symm
      _ = 0 := hfull.2.2.1
  have hPD : csMatMul P D=0 := by
    calc
      _ = csMatMul (A*Aᴴ) D := congrArg (fun X : Matrix H H ℂ => csMatMul X D) hAP.symm
      _ = 0 := hfull.2.2.2.1
  have hQC : csMatMul Q C=0 := hfull.2.2.2.2.1
  have hQD : csMatMul Q D=D := hfull.2.2.2.2.2
  have hqa := (cs_cross_Q_actions Q hQ A t hA ht hb).1
  have hqb := (cs_cross_Q_actions Q hQ A t hA ht hb).2
  have hVA (h : H) (i : CSIndex a b c d m) : V h i = match i with
      | .inl i => C h (eC i)
      | .inr (.inl i) => A h (e1 i).1
      | .inr (.inr (.inl i)) => A h (e0 i).1
      | .inr (.inr (.inr (.inl i))) => D h (eD i)
      | .inr (.inr (.inr (.inr z))) => if z.2 then B h (em z.1).1 else A h (em z.1).1 := by
    rcases i with i | i
    · rfl
    · rcases i with i | i
      · rfl
      · rcases i with i | i
        · rfl
        · rcases i with i | ⟨i,b⟩
          · rfl
          · cases b <;> rfl
  have hPV : csMatMul P V=csMatMul V (csCanonicalP a b c d m) := by
    ext h i
    change (P *ᵥ (fun k => V k i)) h = _
    simp only [csMatMul,csCanonicalP,Matrix.mul_diagonal]
    rcases i with i | i
    · simp only [hVA,csPValue,mul_zero]
      exact congrFun (congrFun hPC h) (eC i)
    · rcases i with i | i
      · simp only [hVA,csPValue,mul_one]
        exact congrFun (congrFun hPA h) (e1 i).1
      · rcases i with i | i
        · simp only [hVA,csPValue,mul_one]
          exact congrFun (congrFun hPA h) (e0 i).1
        · rcases i with i | ⟨i,b⟩
          · simp only [hVA,csPValue,mul_zero]
            exact congrFun (congrFun hPD h) (eD i)
          · cases b
            · simp only [hVA,csPValue,Bool.false_eq_true,if_false,mul_one]
              exact congrFun (congrFun hPA h) (em i).1
            · simp only [hVA,csPValue,if_true,mul_zero]
              exact congrFun (congrFun hPB h) (em i).1
  have hQV : csMatMul Q V=csMatMul V (csCanonicalQ a b c d m ti) := by
    ext h i
    rw [cs_canonicalQ_column]
    change (Q *ᵥ (fun k => V k i)) h = _
    rcases i with i | i
    · simp only [hVA]
      exact congrFun (congrFun hQC h) (eC i)
    · rcases i with i | i
      · simp only [hVA]
        have hs := congrFun (congrFun hqa h) (e1 i).1
        simpa only [csMatMul,Matrix.add_apply,Matrix.mul_diagonal,(e1 i).2,
          Complex.ofReal_one,sub_self,mul_zero,Real.sqrt_zero,Complex.ofReal_zero,mul_one,add_zero] using! hs
      · rcases i with i | i
        · simp only [hVA]
          have hs := congrFun (congrFun hqa h) (e0 i).1
          simpa only [csMatMul,Matrix.add_apply,Matrix.mul_diagonal,(e0 i).2,
            Complex.ofReal_zero,zero_mul,mul_zero,Real.sqrt_zero,add_zero] using! hs
        · rcases i with i | ⟨i,b⟩
          · simp only [hVA]
            exact congrFun (congrFun hQD h) (eD i)
          · cases b
            · simp only [hVA,Bool.false_eq_true,if_false,if_true]
              have hs := congrFun (congrFun hqa h) (em i).1
              simpa only [csMatMul,Matrix.add_apply,Matrix.mul_diagonal,ti] using! hs
            · simp only [hVA,Bool.false_eq_true,if_false,if_true]
              have hs := congrFun (congrFun hqb h) (em i).1
              simpa only [csMatMul,Matrix.add_apply,Matrix.mul_diagonal,ti,Complex.ofReal_sub,
                Complex.ofReal_one] using! hs
  refine ⟨a,b,c,d,m,ti,V,fun i => (em i).2,hV,hVV,?_,?_⟩
  · calc
      P = csMatMul P (V*Vᴴ) := by rw [hVV]; exact (Matrix.mul_one P).symm
      _ = csMatMul (csMatMul P V) Vᴴ := (csMatMul_assoc _ _ _).symm
      _ = _ := congrArg (fun X : Matrix H (CSIndex a b c d m) ℂ => csMatMul X Vᴴ) hPV
  · calc
      Q = csMatMul Q (V*Vᴴ) := by rw [hVV]; exact (Matrix.mul_one Q).symm
      _ = csMatMul (csMatMul Q V) Vᴴ := (csMatMul_assoc _ _ _).symm
      _ = _ := congrArg (fun X : Matrix H (CSIndex a b c d m) ℂ => csMatMul X Vᴴ) hQV

end Qatlib.Concepts.WalkSearch.Spectral

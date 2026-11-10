/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsStat
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.IntermediateValue
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator

theorem sourceNormal_euclidean_eigenbasis (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ)
    (hu : Uᴴ*U = U*Uᴴ) :
    ∃ (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (μ : I → ℂ),
      ∀ j, U.toEuclideanLin (b j) = μ j • b j := by
  classical
  let f : Module.End ℂ (EuclideanSpace ℂ I) := U.toEuclideanLin
  have hf : star f * f = f * star f := by
    change U.toEuclideanLin.adjoint * U.toEuclideanLin =
      U.toEuclideanLin * U.toEuclideanLin.adjoint
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using!
      congrArg Matrix.toEuclideanLin hu
  let H : Module.End ℂ (EuclideanSpace ℂ I) := (1 / 2 : ℂ) • (f + star f)
  let K : Module.End ℂ (EuclideanSpace ℂ I) := (-Complex.I / 2) • (f - star f)
  have hH : H.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change star H = H
    simp [H, star_smul, add_comm]
  have hK : K.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change star K = K
    simp only [K, star_smul, star_sub, star_star]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp]
    rw [← neg_sub f (star f), smul_neg, ← neg_smul]
    rw [neg_smul, neg_div]
    exact (neg_smul _ _).symm
  have hc : Commute f (star f) := by
    show f * star f = star f * f
    exact hf.symm
  have hHK : Commute H K :=
    (((Commute.refl f).sub_right hc).add_left
      (hc.symm.sub_right (Commute.refl (star f)))).smul_left (1 / 2 : ℂ)
        |>.smul_right (-Complex.I / 2)
  let ι := {i : ℂ × ℂ // H.eigenspace i.2 ⊓ K.eigenspace i.1 ≠ ⊥}
  let embed : ι → Module.End.Eigenvalues H × Module.End.Eigenvalues K :=
    fun i => (⟨i.1.2, ne_bot_of_le_ne_bot i.2 inf_le_left⟩,
      ⟨i.1.1, ne_bot_of_le_ne_bot i.2 inf_le_right⟩)
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => p.2.val) hij) (congrArg (fun p => p.1.val) hij)
  letI : Finite ι := Finite.of_injective embed hembed
  letI : Fintype ι := Fintype.ofFinite ι
  have horth := (hH.orthogonalFamily_eigenspace_inf_eigenspace hK).comp
    (Subtype.coe_injective : Function.Injective (Subtype.val : ι → ℂ × ℂ))
  have hdecomp : DirectSum.IsInternal (fun i : ι => H.eigenspace i.1.2 ⊓ K.eigenspace i.1.1) := by
    apply horth.isInternal_iff.mpr
    rw [iSup_ne_bot_subtype]
    rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
    exact hH.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hK hHK
  have hn : Module.finrank ℂ (EuclideanSpace ℂ I) = Fintype.card I := by simp
  let b := hdecomp.subordinateOrthonormalBasis hn horth
  let χ := fun j => hdecomp.subordinateOrthonormalBasisIndex hn j horth
  let μ := fun j => (χ j).1.2 + Complex.I * (χ j).1.1
  have hparts : H + Complex.I • K = f := by
    have hIK : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
      norm_num
    simp only [H, K, smul_smul, hIK]
    module
  have heig (j : Fin (Fintype.card I)) : f (b j) = μ j • b j := by
    have hj := hdecomp.subordinateOrthonormalBasis_subordinate hn j horth
    have hHj := Module.End.mem_eigenspace_iff.mp hj.1
    have hKj := Module.End.mem_eigenspace_iff.mp hj.2
    rw [← hparts, LinearMap.add_apply]
    change H (b j) + Complex.I • K (b j) = _
    rw [hHj, hKj, smul_smul, ← add_smul]
  let e := (Fintype.equivFin I).symm
  refine ⟨b.reindex e,fun j => μ (e.symm j),?_⟩
  intro j
  simpa only [f,OrthonormalBasis.reindex_apply] using! heig (e.symm j)

theorem sourceNormal_matrix_eigenbasis (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : Aᴴ*A = A*Aᴴ) :
    ∃ (E : Matrix I I ℂ) (μ : I → ℂ),
      E ∈ Matrix.unitaryGroup I ℂ ∧ A*E = E*Matrix.diagonal μ := by
  classical
  obtain ⟨b, μ, hb⟩ := sourceNormal_euclidean_eigenbasis I A hA
  let E := (EuclideanSpace.basisFun I ℂ).toBasis.toMatrix b.toBasis
  have hE : E ∈ Matrix.unitaryGroup I ℂ :=
    (EuclideanSpace.basisFun I ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨E, μ, hE, ?_⟩
  ext i j
  have h := congrArg WithLp.ofLp (hb j)
  change A *ᵥ (fun i => E i j) = μ j • (fun i => E i j) at h
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using! congrFun h i

theorem sourceUnitary_principal_diagonalization (H : Type) [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    ∃ (V : Matrix H H ℂ) (angles : H → ℝ),
      V ∈ Matrix.unitaryGroup H ℂ ∧ (∀ j, -Real.pi<angles j ∧ angles j≤Real.pi) ∧
      U=V*Matrix.diagonal (fun j => Complex.exp (Complex.I*angles j))*Vᴴ := by
  have hUstar : Uᴴ*U=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  have hUright : U*Uᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.2
  obtain ⟨V,μ,hV,hUV⟩ := sourceNormal_matrix_eigenbasis H U (by rw [hUstar,hUright])
  have hVstar : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hVright : V*Vᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  have hD : Matrix.diagonal μ=Vᴴ*U*V := by
    calc
      Matrix.diagonal μ = (Vᴴ*V)*Matrix.diagonal μ := by rw [hVstar,Matrix.one_mul]
      _ = Vᴴ*(V*Matrix.diagonal μ) := Matrix.mul_assoc _ _ _
      _ = Vᴴ*(U*V) := by rw [hUV]
      _ = Vᴴ*U*V := (Matrix.mul_assoc _ _ _).symm
  have hVadj : Vᴴ ∈ Matrix.unitaryGroup H ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hV
  have hDu : Matrix.diagonal μ ∈ Matrix.unitaryGroup H ℂ := by
    rw [hD]
    exact (Matrix.unitaryGroup H ℂ).mul_mem
      ((Matrix.unitaryGroup H ℂ).mul_mem hVadj hU) hV
  have hμ (j : H) : ‖μ j‖=1 := by
    have hh := hDu.1
    simp only [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal] at hh
    have hj := congrFun (congrFun hh j) j
    simp only [Matrix.diagonal_apply_eq,Pi.star_apply,Matrix.one_apply_eq] at hj
    have hn := congrArg norm hj
    rw [norm_mul,norm_star,norm_one] at hn
    nlinarith [norm_nonneg (μ j)]
  have hp (j : H) : Complex.exp (Complex.I*(Complex.arg (μ j)))=μ j := by
    have hh := Complex.norm_mul_exp_arg_mul_I (μ j)
    simpa only [hμ j,Complex.ofReal_one,one_mul,mul_comm Complex.I] using! hh
  refine ⟨V,fun j => Complex.arg (μ j),hV,
    fun j => ⟨Complex.neg_pi_lt_arg _,Complex.arg_le_pi _⟩,?_⟩
  simp only [hp]
  calc
    U = U*(V*Vᴴ) := by rw [hVright,Matrix.mul_one]
    _ = (U*V)*Vᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = (V*Matrix.diagonal μ)*Vᴴ := by rw [hUV]

theorem sourceUnitary_negative_diagonalization (H : Type) [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    ∃ (V : Matrix H H ℂ) (angles : H → ℝ),
      V ∈ Matrix.unitaryGroup H ℂ ∧ (∀ j, -Real.pi<angles j ∧ angles j≤Real.pi) ∧
      U=V*Matrix.diagonal (fun j => Complex.exp (-Complex.I*angles j))*Vᴴ := by
  have hUa : Uᴴ ∈ Matrix.unitaryGroup H ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hU
  obtain ⟨V,angles,hV,ha,he⟩ := sourceUnitary_principal_diagonalization H Uᴴ hUa
  refine ⟨V,angles,hV,ha,?_⟩
  have hh := congrArg Matrix.conjTranspose he
  have hs : star (fun j => Complex.exp (Complex.I*(angles j : ℂ)))=
      (fun j => Complex.exp (-Complex.I*(angles j : ℂ))) := by
    funext j
    change (starRingEnd ℂ) (Complex.exp (Complex.I*(angles j : ℂ)))=_
    rw [← Complex.exp_conj]
    simp
  simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose,hs,Matrix.mul_assoc] using! hh

theorem sourceLog_representation (H : Type) [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    ∃ (V : Matrix H H ℂ) (angles : H → ℝ),
      V ∈ Matrix.unitaryGroup H ℂ ∧ (∀ j, -Real.pi<angles j ∧ angles j≤Real.pi) ∧
      U=V*Matrix.diagonal (fun j => Complex.exp (-Complex.I*angles j))*Vᴴ ∧
      sourceLog U=V*Matrix.diagonal (fun j => (angles j : ℂ))*Vᴴ := by
  have hs := sourceUnitary_negative_diagonalization H U hU
  let V := Classical.choose hs
  let angles := Classical.choose (Classical.choose_spec hs)
  have hv := Classical.choose_spec (Classical.choose_spec hs)
  exact ⟨V,angles,hv.1,hv.2.1,hv.2.2,by simp only [sourceLog,dif_pos hs,V,angles]⟩

theorem sourceLog_hermitian_norm (H : Type) [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    (sourceLog U).IsHermitian ∧ ‖sourceLog U‖≤Real.pi := by
  obtain ⟨V,angles,hV,ha,_,he⟩ := sourceLog_representation H U hU
  rw [he]
  constructor
  · change (V*Matrix.diagonal (fun j => (angles j : ℂ))*Vᴴ)ᴴ=_
    have hs : star (fun j => (angles j : ℂ))=(fun j => (angles j : ℂ)) := by
      funext j
      simp
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose,hs,Matrix.mul_assoc]
  · have hVa : Vᴴ ∈ Matrix.unitaryGroup H ℂ := by
      simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hV
    rw [CStarRing.norm_mul_coe_unitary _ ⟨Vᴴ,hVa⟩,
      CStarRing.norm_coe_unitary_mul ⟨V,hV⟩,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
    intro j
    simp only [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨(ha j).1.le,(ha j).2⟩

local instance sourceMatrixENormedAddCommMonoid (H : Type) [Fintype H] :
    ENormedAddCommMonoid (Matrix H H ℂ) :=
  @NormedAddCommGroup.toENormedAddCommMonoid _ Matrix.instL2OpNormedAddCommGroup

local instance sourceMatrixPseudoMetrizable (H : Type) [Fintype H] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix H H ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (H → H → ℂ)
  infer_instance

theorem sourceVolterra_matrix_integrable (H : Type) [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ)
    (hK : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T) :
    IntervalIntegrable K MeasureTheory.volume 0 T := by
  have he : K=(fun t => ∑ i : H,∑ j : H,(K t i j) • Matrix.single i j (1 : ℂ)) := by
    funext t
    simpa using! matrix_eq_sum_single (K t)
  rw [he]
  have hi : IntervalIntegrable
      (∑ i : H,∑ j : H,fun t => (K t i j) • Matrix.single i j (1 : ℂ))
      MeasureTheory.volume 0 T := by
    apply IntervalIntegrable.sum
    intro i _
    apply IntervalIntegrable.sum
    intro j _
    exact (hK i j).smul_continuousOn continuousOn_const
  have hf : (∑ i : H,∑ j : H,fun t => (K t i j) • Matrix.single i j (1 : ℂ))=
      (fun t => ∑ i : H,∑ j : H,(K t i j) • Matrix.single i j (1 : ℂ)) := by
    funext t
    simp only [Finset.sum_apply]
  rw [hf] at hi
  exact hi

def sourceHermitianPart {H : Type} (A : Matrix H H ℂ) : Matrix H H ℂ :=
  (1/2 : ℂ) • (A+Aᴴ)

theorem sourceHermitianPart_hermitian {H : Type} (A : Matrix H H ℂ) :
    (sourceHermitianPart A).IsHermitian := by
  change (sourceHermitianPart A)ᴴ=sourceHermitianPart A
  simp [sourceHermitianPart,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,add_comm]

theorem sourceHermitianPart_error {H : Type} [Fintype H] [DecidableEq H]
    (K A : Matrix H H ℂ) (hK : K.IsHermitian) :
    ‖K-sourceHermitianPart A‖≤‖K-A‖ := by
  have he : K-sourceHermitianPart A=(1/2 : ℂ) • ((K-A)+(K-A)ᴴ) := by
    simp only [sourceHermitianPart,Matrix.conjTranspose_sub,hK.eq]
    module
  rw [he,norm_smul]
  have hs : ‖(K-A)ᴴ‖=‖K-A‖ := by
    simpa only [Matrix.star_eq_conjTranspose] using! norm_star (K-A)
  have hh := norm_add_le (K-A) (K-A)ᴴ
  rw [hs] at hh
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  linarith

theorem sourceVolterra_continuous_approx (H : Type) [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T ε : ℝ) (hT : 0≤T) (hε : 0<ε)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T)
    (hh : ∀ t ∈ Set.Icc 0 T,(K t).IsHermitian) :
    ∃ G : ℝ → Matrix H H ℂ, Continuous G ∧ (∀ t,(G t).IsHermitian) ∧
      (∫ t in (0 : ℝ)..T,‖K t-G t‖)≤ε := by
  have hKm := sourceVolterra_matrix_integrable H K T hi
  have hK := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hKm
  obtain ⟨A,hA,hAi⟩ := hK.exists_boundedContinuous_integral_sub_le hε
  let G := fun t => sourceHermitianPart (A t)
  have hstar : Continuous (fun t => (A t)ᴴ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((continuous_apply i).comp ((continuous_apply j).comp A.continuous)).star
  have hc : Continuous G := by dsimp [G, sourceHermitianPart]; fun_prop
  refine ⟨G,hc,fun t => sourceHermitianPart_hermitian (A t),?_⟩
  have hdiff : IntervalIntegrable (fun t => ‖K t-A t‖) MeasureTheory.volume 0 T :=
    (hKm.sub (A.continuous.intervalIntegrable 0 T)).norm
  have hdiffG : IntervalIntegrable (fun t => ‖K t-G t‖) MeasureTheory.volume 0 T :=
    (hKm.sub (hc.intervalIntegrable 0 T)).norm
  apply (intervalIntegral.integral_mono_on hT hdiffG hdiff
    (fun t ht => sourceHermitianPart_error (K t) (A t) (hh t ht))).trans
  have he : (∫ t in (0 : ℝ)..T,‖K t-A t‖)=
      ∫ t,‖K t-A t‖ ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)) := by
    rw [intervalIntegral.integral_of_le hT]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc.symm
  rw [he]
  exact hA

theorem sourceContinuousEvolution_stability (H : Type) [Fintype H] [DecidableEq H]
    (G K : ℝ → Matrix H H ℂ) (hG : Continuous G) (hK : Continuous K)
    (hGh : ∀ t,(G t).IsHermitian) (hKh : ∀ t,(K t).IsHermitian)
    (t : ℝ) (ht : 0≤t) :
    ‖orderedEvolution (fun s => Complex.I • G s) 0 t-
      orderedEvolution (fun s => Complex.I • K s) 0 t‖≤∫ s in (0 : ℝ)..t,‖G s-K s‖ := by
  let A := fun s => Complex.I • G s
  let B := fun s => Complex.I • K s
  let F := fun s => orderedEvolution A s t*orderedEvolution B 0 s
  let D := fun s => Complex.I • (orderedEvolution A s t*(G s-K s)*orderedEvolution B 0 s)
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hEa : Continuous (fun s => orderedEvolution A s t) :=
    continuous_iff_continuousAt.mpr (fun s => (orderedEvolution_hasDerivAt_start A hAc t s).continuousAt)
  have hEb : Continuous (orderedEvolution B 0) :=
    continuous_iff_continuousAt.mpr (fun s => (orderedEvolution_hasDerivAt B hBc 0 s).continuousAt)
  have hDc : Continuous D := by dsimp [D]; fun_prop
  have hd (s : ℝ) : HasDerivAt F (D s) s := by
    convert! (orderedEvolution_hasDerivAt_start A hAc t s).mul
      (orderedEvolution_hasDerivAt B hBc 0 s) using 1
    simp only [D,A,B,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc,Matrix.mul_sub,Matrix.sub_mul,
      smul_sub,mul_neg]
    module
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s∈Set.uIcc 0 t) => hd s) (hDc.intervalIntegrable 0 t)
  have hDa (s : ℝ) : ‖D s‖=‖G s-K s‖ := by
    have hUa := ordered_evolution_hermitian_unitary H G hG hGh s t
    have hUb := ordered_evolution_hermitian_unitary H K hK hKh 0 s
    dsimp only [D]
    rw [norm_smul,Complex.norm_I,one_mul,
      CStarRing.norm_mul_coe_unitary _ ⟨_,hUb⟩,
      CStarRing.norm_coe_unitary_mul ⟨_,hUa⟩]
  have hn := intervalIntegral.norm_integral_le_of_norm_le (μ:=MeasureTheory.volume) ht
    (Filter.Eventually.of_forall (fun s (_ : s∈Set.Ioc 0 t) => (hDa s).le))
    ((hG.sub hK).norm.intervalIntegrable 0 t)
  rw [he] at hn
  have hf : F t-F 0=orderedEvolution B 0 t-orderedEvolution A 0 t := by simp [F]
  rw [hf] at hn
  rw [norm_sub_rev]
  exact hn

theorem sourceVolterra_approx_close (H : Type) [Fintype H] [DecidableEq H]
    (K G J : ℝ → Matrix H H ℂ) (T ε η : ℝ) (hT : 0≤T)
    (hKi : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T)
    (hG : Continuous G) (hJ : Continuous J)
    (hGh : ∀ t,(G t).IsHermitian) (hJh : ∀ t,(J t).IsHermitian)
    (hε : (∫ t in (0 : ℝ)..T,‖K t-G t‖)≤ε)
    (hη : (∫ t in (0 : ℝ)..T,‖K t-J t‖)≤η) :
    ∀ t ∈ Set.Icc 0 T,
    ‖orderedEvolution (fun s => Complex.I • G s) 0 t-
      orderedEvolution (fun s => Complex.I • J s) 0 t‖≤ε+η := by
  have hKm := sourceVolterra_matrix_integrable H K T hKi
  have hKg := (hKm.sub (hG.intervalIntegrable 0 T)).norm
  have hKj := (hKm.sub (hJ.intervalIntegrable 0 T)).norm
  have hGj := (hG.sub hJ).norm.intervalIntegrable (μ:=MeasureTheory.volume) 0 T
  have hbound (t : ℝ) : ‖G t-J t‖≤‖K t-G t‖+‖K t-J t‖ := by
    have hh := norm_sub_le (G t-K t) (J t-K t)
    have he : (G t-K t)-(J t-K t)=G t-J t := by abel
    rw [he,norm_sub_rev (G t) (K t),norm_sub_rev (J t) (K t)] at hh
    exact hh
  have hbig : (∫ t in (0 : ℝ)..T,‖G t-J t‖)≤ε+η := by
    apply (intervalIntegral.integral_mono_on hT hGj (hKg.add hKj)
      (fun t _ => hbound t)).trans
    rw [intervalIntegral.integral_add hKg hKj]
    exact add_le_add hε hη
  intro t ht
  have hsmall := intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) ht.1 ht.2
    (Filter.Eventually.of_forall (fun s => norm_nonneg (G s-J s))) hGj
  exact (sourceContinuousEvolution_stability H G J hG hJ hGh hJh t ht.1).trans
    (hsmall.trans hbig)

theorem sourceVolterra_unitary_limit (H : Type) [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T)
    (hh : ∀ t ∈ Set.Icc 0 T,(K t).IsHermitian) :
    ∃ (G : ℕ → ℝ → Matrix H H ℂ)
      (U : C(Set.Icc 0 T,Matrix H H ℂ))
      (V : ℕ → C(Set.Icc 0 T,Matrix H H ℂ)),
      (∀ n, Continuous (G n) ∧ (∀ t,(G n t).IsHermitian) ∧
        (∫ t in (0 : ℝ)..T,‖K t-G n t‖)≤(1/2 : ℝ)^n) ∧
      (∀ n t, V n t=orderedEvolution (fun s => Complex.I • G n s) 0 t.val) ∧
      TendstoUniformly (fun n t => V n t) U Filter.atTop ∧
      (∀ n t,‖V n t-U t‖≤(1/2 : ℝ)^n) ∧
      U ⟨0,⟨le_rfl,hT⟩⟩=1 ∧ ∀ t,U t ∈ Matrix.unitaryGroup H ℂ := by
  choose G hGc hGh hGp using fun n : ℕ =>
    sourceVolterra_continuous_approx H K T ((1/2 : ℝ)^n) hT (by positivity) hi hh
  let V (n : ℕ) : C(Set.Icc 0 T,Matrix H H ℂ) :=
    ⟨fun t => orderedEvolution (fun s => Complex.I • G n s) 0 t.val,
      (continuous_iff_continuousAt.mpr (fun t =>
        (orderedEvolution_hasDerivAt (fun s => Complex.I • G n s) (by have := hGc n; fun_prop) 0 t).continuousAt)).comp continuous_subtype_val⟩
  have hbound (n m : ℕ) (t : Set.Icc 0 T) : ‖V n t-V m t‖≤(1/2 : ℝ)^n+(1/2 : ℝ)^m :=
    sourceVolterra_approx_close H K (G n) (G m) T _ _ hT hi
      (hGc n) (hGc m) (hGh n) (hGh m) (hGp n) (hGp m) t.val t.prop
  have hpzero : Filter.Tendsto (fun n : ℕ => (1/2 : ℝ)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : Filter.Tendsto (fun n : ℕ => 2*(1/2 : ℝ)^n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using! hpzero.const_mul 2
  have hCauchy (t : Set.Icc 0 T) : CauchySeq (fun n => V n t) :=
    cauchySeq_of_le_tendsto_0 (fun n => 2*(1/2 : ℝ)^n)
      (fun n m N hn hm => by
        rw [dist_eq_norm]
        have hnp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)≤1) hn
        have hmp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)≤1) hm
        exact (hbound n m t).trans (by linarith)) hzero
  choose u hu using fun t => cauchySeq_tendsto_of_complete (hCauchy t)
  have hdist (n : ℕ) (t : Set.Icc 0 T) : ‖V n t-u t‖≤(1/2 : ℝ)^n := by
    have hl := ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => V n t)
      Filter.atTop (nhds (V n t))).sub (hu t)).norm
    have hr := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1/2 : ℝ)^n)
      Filter.atTop (nhds ((1/2 : ℝ)^n))).add hpzero
    simp only [add_zero] at hr
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall (fun m => hbound n m t))
  have hunif : TendstoUniformly (fun n t => V n t) u Filter.atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have he := hpzero.eventually (gt_mem_nhds hε)
    filter_upwards [he] with n hn
    intro t
    rw [dist_eq_norm,norm_sub_rev]
    exact (hdist n t).trans_lt hn
  let U : C(Set.Icc 0 T,Matrix H H ℂ) :=
    ⟨u,hunif.continuous (Filter.Eventually.of_forall (fun n => (V n).continuous)).frequently⟩
  refine ⟨G,U,V,fun n => ⟨hGc n,hGh n,hGp n⟩,by intros; rfl,hunif,hdist,?_,?_⟩
  · have he := hu ⟨0,⟨le_rfl,hT⟩⟩
    have hc : Filter.Tendsto (fun n => V n ⟨0,⟨le_rfl,hT⟩⟩) Filter.atTop (nhds (1 : Matrix H H ℂ)) := by
      simp [V]
    exact tendsto_nhds_unique he hc
  · intro t
    have hv (n : ℕ) : V n t ∈ Matrix.unitaryGroup H ℂ :=
      ordered_evolution_hermitian_unitary H (G n) (hGc n) (hGh n) 0 t.val
    have hp := (hu t).star.mul (hu t)
    have hc : Filter.Tendsto (fun n => star (V n t)*V n t) Filter.atTop (nhds (1 : Matrix H H ℂ)) := by
      have he : (fun n => star (V n t)*V n t)=(fun _ : ℕ => (1 : Matrix H H ℂ)) :=
        funext (fun n => (hv n).1)
      rw [he]
      exact tendsto_const_nhds
    rw [Matrix.mem_unitaryGroup_iff']
    exact tendsto_nhds_unique hp hc

def sourceIntervalPath {H : Type} [Fintype H] [DecidableEq H]
    (T : ℝ) (U : C(Set.Icc 0 T,Matrix H H ℂ)) (t : ℝ) : Matrix H H ℂ :=
  if ht : t∈Set.Icc 0 T then U ⟨t,ht⟩ else 1

theorem sourceIntervalPath_eq {H : Type} [Fintype H] [DecidableEq H]
    (T : ℝ) (U : C(Set.Icc 0 T,Matrix H H ℂ)) (t : ℝ) (ht : t∈Set.Icc 0 T) :
    sourceIntervalPath T U t=U ⟨t,ht⟩ := by simp [sourceIntervalPath,ht]

theorem sourceIntervalPath_continuousOn {H : Type} [Fintype H] [DecidableEq H]
    (T : ℝ) (U : C(Set.Icc 0 T,Matrix H H ℂ)) :
    ContinuousOn (sourceIntervalPath T U) (Set.Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  have he : (Set.Icc 0 T).domRestrict (sourceIntervalPath T U)=U := by
    funext t
    exact sourceIntervalPath_eq T U t.val t.prop
  rw [he]
  exact U.continuous

theorem sourceOrderedEvolution_volterra_integral (H : Type) [Fintype H] [DecidableEq H]
    (G : ℝ → Matrix H H ℂ) (hG : Continuous G) (t : ℝ) :
    orderedEvolution (fun s => Complex.I • G s) 0 t=1+
      ∫ s in (0 : ℝ)..t,(-Complex.I) • (G s*orderedEvolution (fun u => Complex.I • G u) 0 s) := by
  let A := fun s => Complex.I • G s
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hEc : Continuous (orderedEvolution A 0) :=
    continuous_iff_continuousAt.mpr (fun s => (orderedEvolution_hasDerivAt A hAc 0 s).continuousAt)
  have hd (s : ℝ) : HasDerivAt (orderedEvolution A 0)
      ((-Complex.I) • (G s*orderedEvolution A 0 s)) s := by
    simpa only [A,Matrix.smul_mul,neg_smul] using! orderedEvolution_hasDerivAt A hAc 0 s
  have hc :=
      (show Continuous (fun s => (-Complex.I) • (G s*orderedEvolution A 0 s)) by fun_prop).intervalIntegrable (μ:=MeasureTheory.volume) 0 t
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s∈Set.uIcc 0 t) => hd s) hc
  simp only [orderedEvolution_self] at he
  exact (eq_add_of_sub_eq he.symm).trans (add_comm _ _)

theorem sourceVolterra_integral_error (H : Type) [Fintype H] [DecidableEq H]
    (K G F V : ℝ → Matrix H H ℂ) (T e : ℝ) (hT : 0≤T) (he : 0≤e)
    (hKi : IntervalIntegrable K MeasureTheory.volume 0 T)
    (hGc : Continuous G) (hVc : Continuous V) (hFc : ContinuousOn F (Set.Icc 0 T))
    (hVu : ∀ s,V s ∈ Matrix.unitaryGroup H ℂ)
    (hclose : ∀ s∈Set.Icc 0 T,‖V s-F s‖≤e)
    (hGclose : (∫ s in (0 : ℝ)..T,‖K s-G s‖)≤e) :
    ∀ t∈Set.Icc 0 T,
      ‖(∫ s in (0 : ℝ)..t,(-Complex.I) • (G s*V s))-
        ∫ s in (0 : ℝ)..t,(-Complex.I) • (K s*F s)‖≤
        e+e*(∫ s in (0 : ℝ)..T,‖K s‖) := by
  have hFi : IntervalIntegrable (fun s => K s*F s) MeasureTheory.volume 0 T :=
    hKi.mul_continuousOn (by rwa [Set.uIcc_of_le hT])
  have hGi := (hGc.mul hVc).intervalIntegrable (μ:=MeasureTheory.volume) 0 T
  have hKn := hKi.norm
  have hdiff := (hKi.sub (hGc.intervalIntegrable 0 T)).norm
  have hbound (s : ℝ) (hs : s∈Set.Icc 0 T) :
      ‖(-Complex.I) • (G s*V s)-(-Complex.I) • (K s*F s)‖≤
        ‖K s-G s‖+e*‖K s‖ := by
    rw [← smul_sub,norm_smul,norm_neg,Complex.norm_I,one_mul]
    have hx : G s*V s-K s*F s=(G s-K s)*V s+K s*(V s-F s) := by noncomm_ring
    rw [hx]
    apply (norm_add_le _ _).trans
    have hv := l2_norm_unitary_le_one (hVu s)
    have h1 : ‖(G s-K s)*V s‖≤‖K s-G s‖ := by
      apply (norm_mul_le _ _).trans
      calc
        _ ≤ ‖G s-K s‖*1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
        _ = _ := by rw [mul_one,norm_sub_rev]
    have h2 : ‖K s*(V s-F s)‖≤e*‖K s‖ := by
      apply (norm_mul_le _ _).trans
      calc
        _ ≤ ‖K s‖*e := mul_le_mul_of_nonneg_left (hclose s hs) (norm_nonneg _)
        _ = _ := mul_comm _ _
    exact add_le_add h1 h2
  intro t ht
  have hsub : Set.uIcc 0 t⊆Set.uIcc 0 T := by
    rw [Set.uIcc_of_le ht.1,Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hFt : IntervalIntegrable (fun s => (-Complex.I) • (K s*F s)) MeasureTheory.volume 0 t :=
    (hFi.continuousOn_smul continuousOn_const).mono_set hsub
  have hGt : IntervalIntegrable (fun s => (-Complex.I) • (G s*V s)) MeasureTheory.volume 0 t :=
    (hGi.continuousOn_smul continuousOn_const).mono_set hsub
  rw [← intervalIntegral.integral_sub hGt hFt]
  have hnonneg : ∀ s,0≤‖K s-G s‖+e*‖K s‖ := by intro s; positivity
  have hbigi := hdiff.add (hKn.const_mul e)
  have htint := hbigi.mono_set hsub
  have hn := intervalIntegral.norm_integral_le_of_norm_le (μ:=MeasureTheory.volume) ht.1
    (Filter.Eventually.of_forall (fun s (hs : s∈Set.Ioc 0 t) =>
      hbound s ⟨hs.1.le,hs.2.trans ht.2⟩)) htint
  apply hn.trans
  have hmono := intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) ht.1 ht.2
    (Filter.Eventually.of_forall hnonneg) hbigi
  apply hmono.trans
  rw [intervalIntegral.integral_add hdiff (hKn.const_mul e),intervalIntegral.integral_const_mul]
  exact add_le_add hGclose le_rfl

def sourceMatrixEntryCLM (H : Type) [Fintype H] (i j : H) : Matrix H H ℂ →L[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

theorem sourceVolterra_exists (H : Type) [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T)
    (hh : ∀ t∈Set.Icc 0 T,(K t).IsHermitian) :
    ∃ F : ℝ → Matrix H H ℂ, sourceVolterra K T F ∧
      ∀ t∈Set.Icc 0 T,F t ∈ Matrix.unitaryGroup H ℂ := by
  obtain ⟨G,U,V,hG,hV,hu,hRate,hU0,hUu⟩ := sourceVolterra_unitary_limit H K T hT hi hh
  let F := sourceIntervalPath T U
  let W (n : ℕ) := orderedEvolution (fun s => Complex.I • G n s) 0
  have hFc : ContinuousOn F (Set.Icc 0 T) := sourceIntervalPath_continuousOn T U
  have hKm := sourceVolterra_matrix_integrable H K T hi
  have hKF : IntervalIntegrable (fun s => (-Complex.I) • (K s*F s)) MeasureTheory.volume 0 T :=
    (hKm.mul_continuousOn (by rwa [Set.uIcc_of_le hT])).continuousOn_smul continuousOn_const
  have hWc (n : ℕ) : Continuous (W n) := continuous_iff_continuousAt.mpr
    (fun s => (orderedEvolution_hasDerivAt (fun s => Complex.I • G n s) (by have := (hG n).1; fun_prop) 0 s).continuousAt)
  have hWu (n : ℕ) (s : ℝ) : W n s ∈ Matrix.unitaryGroup H ℂ :=
    ordered_evolution_hermitian_unitary H (G n) (hG n).1 (hG n).2.1 0 s
  have hFlow (t : ℝ) (ht : t∈Set.Icc 0 T) : F t=1+
      ∫ s in (0 : ℝ)..t,(-Complex.I) • (K s*F s) := by
    let J (n : ℕ) := ∫ s in (0 : ℝ)..t,(-Complex.I) • (G n s*W n s)
    let J0 := ∫ s in (0 : ℝ)..t,(-Complex.I) • (K s*F s)
    have hpzero : Filter.Tendsto (fun n : ℕ => (1/2 : ℝ)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have herr (n : ℕ) : ‖J n-J0‖≤(1/2 : ℝ)^n+(1/2 : ℝ)^n*(∫ s in (0 : ℝ)..T,‖K s‖) := by
      apply sourceVolterra_integral_error H K (G n) F (W n) T _ hT (by positivity)
        hKm (hG n).1 (hWc n) hFc (hWu n) ?_ (hG n).2.2 t ht
      intro s hs
      have hc := hRate n ⟨s,hs⟩
      rw [hV] at hc
      simpa only [F,W,sourceIntervalPath,dif_pos hs] using! hc
    have hR := hpzero.add (hpzero.mul_const (∫ s in (0 : ℝ)..T,‖K s‖))
    simp only [zero_mul,zero_add] at hR
    have hJnorm : Filter.Tendsto (fun n => ‖J n-J0‖) Filter.atTop (nhds 0) :=
      squeeze_zero (fun _ => norm_nonneg _) herr hR
    have hJ : Filter.Tendsto J Filter.atTop (nhds J0) :=
      (tendsto_iff_norm_sub_tendsto_zero).mpr hJnorm
    have hWt := hu.tendsto_at ⟨t,ht⟩
    have he (n : ℕ) : V n ⟨t,ht⟩=1+J n :=
      (hV n _).trans (sourceOrderedEvolution_volterra_integral H (G n) (hG n).1 t)
    simp_rw [he] at hWt
    have hf := tendsto_nhds_unique hWt (hJ.const_add (1 : Matrix H H ℂ))
    simpa only [F,sourceIntervalPath,dif_pos ht,J0] using! hf
  refine ⟨F,⟨?_,hFc,?_⟩,?_⟩
  · simpa only [F,sourceIntervalPath,dif_pos (show (0 : ℝ)∈Set.Icc 0 T from ⟨le_rfl,hT⟩)] using! hU0
  · intro t ht
    have hsub : Set.uIcc 0 t⊆Set.uIcc 0 T := by
      rw [Set.uIcc_of_le ht.1,Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc le_rfl ht.2
    have hf := hKF.mono_set hsub
    have he : (∫ s in (0 : ℝ)..t,(-Complex.I) • (K s*F s))=
        Matrix.of (fun i j => ∫ s in (0 : ℝ)..t,((-Complex.I) • (K s*F s)) i j) := by
      ext i j
      exact ((sourceMatrixEntryCLM H i j).intervalIntegral_comp_comm hf).symm
    rw [← he]
    exact hFlow t ht
  · intro t ht
    change sourceIntervalPath T U t∈Matrix.unitaryGroup H ℂ
    rw [sourceIntervalPath_eq T U t ht]
    exact hUu ⟨t,ht⟩

theorem sourceVolterra_matrix_equation (H : Type) [Fintype H] [DecidableEq H]
    (K V : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T)
    (hK : IntervalIntegrable K MeasureTheory.volume 0 T) (hV : sourceVolterra K T V) :
    (∀ t∈Set.Icc 0 T,V t=1+∫ s in (0 : ℝ)..t,(-Complex.I) • (K s*V s)) ∧
      IntervalIntegrable (fun s => (-Complex.I) • (K s*V s)) MeasureTheory.volume 0 T := by
  have hI : IntervalIntegrable (fun s => (-Complex.I) • (K s*V s)) MeasureTheory.volume 0 T :=
    (hK.mul_continuousOn (by simpa only [Set.uIcc_of_le hT] using! hV.2.1)).continuousOn_smul continuousOn_const
  refine ⟨?_,hI⟩
  intro t ht
  have hsub : Set.uIcc 0 t⊆Set.uIcc 0 T := by
    rw [Set.uIcc_of_le ht.1,Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have he : (∫ s in (0 : ℝ)..t,(-Complex.I) • (K s*V s))=
      Matrix.of (fun i j => ∫ s in (0 : ℝ)..t,((-Complex.I) • (K s*V s)) i j) := by
    ext i j
    exact ((sourceMatrixEntryCLM H i j).intervalIntegral_comp_comm (hI.mono_set hsub)).symm
  rw [he]
  exact hV.2.2 t ht

theorem sourceVolterra_short_zero (H : Type) [Fintype H] [DecidableEq H]
    (K D : ℝ → Matrix H H ℂ) (a b : ℝ) (hab : a≤b)
    (hK : IntervalIntegrable K MeasureTheory.volume a b) (hD : ContinuousOn D (Set.Icc a b))
    (hEq : ∀ s∈Set.Icc a b,D s=∫ t in a..s,(-Complex.I) • (K t*D t))
    (hmass : (∫ t in a..b,‖K t‖)<1) : ∀ s∈Set.Icc a b,D s=0 := by
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hD.norm
  let M := ‖D x‖
  have hM : 0≤M := norm_nonneg _
  have hbound (s : ℝ) (hs : s∈Set.Icc a b) : ‖D s‖≤M := hmax hs
  have hestimate (s : ℝ) (hs : s∈Set.Icc a b) : ‖D s‖≤M*(∫ t in a..b,‖K t‖) := by
    rw [hEq s hs]
    have hsub : Set.uIcc a s⊆Set.uIcc a b := by
      rw [Set.uIcc_of_le hs.1,Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl hs.2
    have hg := (hK.norm.const_mul M).mono_set hsub
    have hn := intervalIntegral.norm_integral_le_of_norm_le (μ:=MeasureTheory.volume)
      (f:=fun t => (-Complex.I) • (K t*D t)) hs.1
      (Filter.Eventually.of_forall (fun t (ht : t∈Set.Ioc a s) => by
        rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
        apply (norm_mul_le _ _).trans
        calc
          _ ≤ ‖K t‖*M := mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le,ht.2.trans hs.2⟩) (norm_nonneg _)
          _ = _ := mul_comm _ _)) hg
    rw [intervalIntegral.integral_const_mul] at hn
    have hmono := intervalIntegral.integral_mono_interval (le_refl a) hs.1 hs.2
      (Filter.Eventually.of_forall (fun t => norm_nonneg (K t))) hK.norm
    exact hn.trans (mul_le_mul_of_nonneg_left hmono hM)
  have hz : M=0 := by
    have hh := hestimate x hx
    change M≤M*(∫ t in a..b,‖K t‖) at hh
    nlinarith
  intro s hs
  apply norm_eq_zero.mp
  exact le_antisymm (by rw [← hz]; exact hbound s hs) (norm_nonneg _)

noncomputable def sourceKernelMass {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, ‖K s‖

theorem sourceKernelMass_zero {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) : sourceKernelMass K 0 = 0 := by
  simp [sourceKernelMass]

theorem sourceKernelMass_of_nonneg {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) {t : ℝ} (ht : 0≤t) :
    sourceKernelMass K t = ∫ s in Set.Icc (0:ℝ) t, ‖K s‖ := by
  simp only [sourceKernelMass, intervalIntegral.integral_of_le ht]
  exact (MeasureTheory.integral_Icc_eq_integral_Ioc (f := fun s => ‖K s‖)).symm

theorem sourceKernelMass_continuousOn {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T)
    (hK : IntervalIntegrable K MeasureTheory.volume 0 T) :
    ContinuousOn (sourceKernelMass K) (Set.Icc 0 T) := by
  have hac : AbsolutelyContinuousOnInterval (fun t => ∫ s in (0 : ℝ)..t, ‖K s‖) 0 T :=
    hK.norm.absolutelyContinuousOnInterval_intervalIntegral
      (c := (0 : ℝ)) Set.left_mem_uIcc
  have hc := hac.continuousOn
  rwa [Set.uIcc_of_le hT] at hc

theorem sourceKernelMass_nonneg {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T) :
    0 ≤ sourceKernelMass K T :=
  intervalIntegral.integral_nonneg_of_forall hT (fun _ => norm_nonneg _)

theorem sourceKernelMass_sub {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) {a b : ℝ} (ha : 0≤a) (hab : a≤b)
    (hK : IntervalIntegrable K MeasureTheory.volume 0 b) :
    ∫ s in a..b, ‖K s‖ = sourceKernelMass K b - sourceKernelMass K a := by
  have h1 : IntervalIntegrable (fun s => ‖K s‖) MeasureTheory.volume 0 b := hK.norm
  have hsub : Set.uIcc 0 a ⊆ Set.uIcc 0 b := by
    rw [Set.uIcc_of_le ha,Set.uIcc_of_le (ha.trans hab)]
    exact Set.Icc_subset_Icc le_rfl hab
  exact (intervalIntegral.integral_interval_sub_left h1 (h1.mono_set hsub)).symm

theorem sourceKernelMass_mono {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) {a b : ℝ} (ha : 0≤a) (hab : a≤b)
    (hK : IntervalIntegrable K MeasureTheory.volume 0 b) :
    sourceKernelMass K a ≤ sourceKernelMass K b := by
  rw [← sub_nonneg,← sourceKernelMass_sub K ha hab hK]
  exact intervalIntegral.integral_nonneg_of_forall hab (fun _ => norm_nonneg _)

theorem sourceVolterra_unique {H : Type} [Fintype H] [DecidableEq H]
    (K V W : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T)
    (hV : sourceVolterra K T V) (hW : sourceVolterra K T W) :
    ∀ t ∈ Set.Icc 0 T, V t=W t := by
  have hKm : IntervalIntegrable K MeasureTheory.volume 0 T :=
    sourceVolterra_matrix_integrable H K T hi
  obtain ⟨hVe,hVi⟩ := sourceVolterra_matrix_equation H K V T hT hKm hV
  obtain ⟨hWe,hWi⟩ := sourceVolterra_matrix_equation H K W T hT hKm hW
  have hsubT : ∀ s : ℝ, s∈Set.Icc 0 T → Set.uIcc 0 s ⊆ Set.uIcc 0 T := by
    intro s hs
    rw [Set.uIcc_of_le hs.1,Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc le_rfl hs.2
  have hDsub : ∀ s ∈ Set.Icc 0 T,
      V s-W s=∫ t in (0 : ℝ)..s, (-Complex.I) • (K t*(V t-W t)) := by
    intro s hs
    rw [hVe s hs,hWe s hs]
    simp only [add_sub_add_left_eq_sub]
    rw [← intervalIntegral.integral_sub
      (hVi.mono_set (hsubT s hs)) (hWi.mono_set (hsubT s hs))]
    congr 1
    funext t
    simp only [Matrix.mul_sub,smul_sub]
  have hzero0 : ∀ s ∈ Set.Icc 0 0, V s=W s := by
    intro s hs
    have h0 := hDsub 0 ⟨le_rfl,hT⟩
    simp only [intervalIntegral.integral_same] at h0
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst hs0
    exact sub_eq_zero.mp h0
  have hDD : IntervalIntegrable (fun t => (-Complex.I) • (K t*(V t-W t)))
      MeasureTheory.volume 0 T :=
    ((hKm.mul_continuousOn (by
      rw [Set.uIcc_of_le hT]
      exact hV.2.1.sub hW.2.1)).continuousOn_smul continuousOn_const)
  have hstep : ∀ (p p' : ℝ), 0≤p → p≤p' → p'≤T →
      (∀ s ∈ Set.Icc 0 p, V s=W s) → sourceKernelMass K p'-sourceKernelMass K p<1 →
      ∀ s ∈ Set.Icc 0 p', V s=W s := by
    intro p p' hp0 hp'p hp'T hz hmass s hs
    have hp'0 : 0≤p' := hp0.trans hp'p
    have hp'Tmem : p ∈ Set.Icc 0 T := ⟨hp0,hp'p.trans hp'T⟩
    have hsub : Set.uIcc p p' ⊆ Set.uIcc 0 T := by
      rw [Set.uIcc_of_le hp'p,Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc hp0 hp'T
    have hsubps : ∀ s : ℝ, s∈Set.Icc p p' → Set.uIcc p s ⊆ Set.uIcc 0 T := by
      intro s hs'
      rw [Set.uIcc_of_le hs'.1,Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc hp0 ((hs'.2.trans hp'T))
    have hrestart : ∀ s ∈ Set.Icc p p',
        V s-W s=∫ t in p..s, (-Complex.I) • (K t*(V t-W t)) := by
      intro s hs'
      have hs : s∈Set.Icc 0 T := ⟨hp0.trans hs'.1,hs'.2.trans hp'T⟩
      have hsplit : (∫ t in (0 : ℝ)..p, (-Complex.I) • (K t*(V t-W t)))+
          ∫ t in p..s, (-Complex.I) • (K t*(V t-W t))=
          ∫ t in (0 : ℝ)..s, (-Complex.I) • (K t*(V t-W t)) :=
        intervalIntegral.integral_add_adjacent_intervals
          (hDD.mono_set (hsubT p hp'Tmem))
          (hDD.mono_set (hsubps s hs'))
      rw [hDsub s hs,← hsplit,← hDsub p hp'Tmem,hz p ⟨hp0,le_refl p⟩,sub_self,zero_add]
    have hzero := sourceVolterra_short_zero H K (fun s => V s-W s) p p' hp'p
      (hKm.mono_set hsub)
      ((hV.2.1.mono (Set.Icc_subset_Icc hp0 hp'T)).sub
        (hW.2.1.mono (Set.Icc_subset_Icc hp0 hp'T)))
      hrestart (by
        have hsubbig : Set.uIcc 0 p' ⊆ Set.uIcc 0 T := hsubT p' ⟨hp'0,hp'T⟩
        rw [sourceKernelMass_sub K hp0 hp'p (hKm.mono_set hsubbig)]
        exact hmass)
    rcases le_total s p with hsp | hps
    · exact hz s ⟨hs.1,hsp⟩
    · exact sub_eq_zero.mp (hzero s ⟨hps,hs.2⟩)
  have hMnn : 0 ≤ sourceKernelMass K T := sourceKernelMass_nonneg K T hT
  have hmC : ContinuousOn (sourceKernelMass K) (Set.Icc 0 T) :=
    sourceKernelMass_continuousOn K T hT hKm
  rcases eq_or_lt_of_le hMnn with hM0 | hMpos
  · have hfin0 := hstep 0 T le_rfl hT (le_refl T) hzero0 (by
      rw [sourceKernelMass_zero,sub_zero,← hM0]; norm_num)
    intro t ht
    exact hfin0 t ht
  · have hNpos : (0 : ℝ) < (Nat.ceil (sourceKernelMass K T) + 1 : ℕ) := by positivity
    set N : ℕ := (Nat.ceil (sourceKernelMass K T) + 1 : ℕ) with hNdef
    have hMN : sourceKernelMass K T < (N : ℝ) := by
      rw [hNdef,Nat.cast_add,Nat.cast_one]
      exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    have hNn : ((N : ℝ)) ≠ 0 := by positivity
    set Δ : ℝ := sourceKernelMass K T/(N : ℝ) with hΔdef
    have hΔpos : 0<Δ := div_pos hMpos (by positivity)
    have hΔ1 : Δ<1 := (div_lt_one (by positivity)).2 hMN
    have hNΔ : (N : ℝ)*Δ = sourceKernelMass K T := by
      rw [hΔdef]
      exact mul_div_cancel₀ _ hNn
    have hpart : ∀ i : ℕ, i≤N → ∃ p : ℝ, 0≤p ∧ p≤T ∧
        (∀ s ∈ Set.Icc 0 p, V s=W s) ∧ sourceKernelMass K p=(i : ℝ)*Δ := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨0,le_rfl,hT,hzero0,?_⟩
        rw [sourceKernelMass_zero]
        simp
      | succ i ih =>
        intro hiN
        obtain ⟨p,hp0,hpT,hz,hmp⟩ := ih (Nat.le_of_succ_le hiN)
        by_cases hpTeq : p=T
        · exfalso
          have hcheq : (i : ℝ) = (N : ℝ) := by
            apply mul_right_cancel₀ (by positivity : (Δ : ℝ) ≠ 0)
            rw [hNΔ,← hpTeq,← hmp]
          have : i=N := Nat.cast_injective hcheq
          omega
        · have hpTlt : p<T := lt_of_le_of_ne hpT hpTeq
          have hgeo : (((i : ℝ))+1)*Δ ∈ Set.Icc (sourceKernelMass K p)
              (sourceKernelMass K T) := by
            refine ⟨?_,?_⟩
            · rw [hmp]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_succ i))
                (le_of_lt hΔpos)
            · rw [← hNΔ]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) (le_of_lt hΔpos)
          have hpc : ContinuousOn (sourceKernelMass K) (Set.Icc p T) :=
            hmC.mono (Set.Icc_subset_Icc hp0 (le_refl T))
          obtain ⟨p',hp'mem,hp'm⟩ :=
            (isPreconnected_Icc.intermediate_value (s := Set.Icc p T)
              ⟨le_refl p,hpT⟩ ⟨hpT,le_refl T⟩ hpc) hgeo
          have hmass : sourceKernelMass K p'-sourceKernelMass K p<1 := by
            rw [hp'm,hmp]
            have hstep1 : (((i : ℝ))+1)*Δ-(i : ℝ)*Δ=Δ := by ring
            rw [hstep1]
            exact hΔ1
          refine ⟨p',(hp0.trans hp'mem.1),hp'mem.2,hstep p p' hp0 hp'mem.1 hp'mem.2 hz hmass,?_⟩
          exact_mod_cast hp'm
    obtain ⟨p,hp0,hpT,hz,hmp⟩ := hpart N (le_refl N)
    have hfinal := hstep p T hp0 hpT (le_refl T) hz (by
      rw [← hNΔ,hmp,sub_self]; norm_num)
    intro t ht
    exact hfinal t ht

theorem sourceVolterraMatrix_eq {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0≤T)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T)
    (F : ℝ → Matrix H H ℂ) (hF : sourceVolterra K T F) :
    sourceVolterraMatrix K T=F T := by
  have hex : ∃ U, sourceVolterra K T U := ⟨F,hF⟩
  rw [sourceVolterraMatrix,dif_pos hex]
  exact sourceVolterra_unique K (Classical.choose hex) F T hT hi
    (Classical.choose_spec hex) hF T ⟨hT,le_refl T⟩

theorem sourceFrameConj_mul {H : Type} [Fintype H] [DecidableEq H]
    {V : Matrix H H ℂ} (hV : V ∈ Matrix.unitaryGroup H ℂ) (X Y : Matrix H H ℂ) :
    (V*X*Vᴴ)*(V*Y*Vᴴ)=V*(X*Y)*Vᴴ := by
  have hVstar : Vᴴ*V=1 := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff.mp (Unitary.star_mem hV)
  rw [Matrix.mul_assoc (V*X) Vᴴ (V*Y*Vᴴ),
      ← Matrix.mul_assoc Vᴴ (V*Y) Vᴴ,
      ← Matrix.mul_assoc Vᴴ V Y,
      hVstar,one_mul,
      ← Matrix.mul_assoc (V*X) Y Vᴴ,
      Matrix.mul_assoc V X Y]

theorem sourceVolterra_const_spectral {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (angles : H → ℝ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (T : ℝ) (_hT : 0≤T) :
    sourceVolterra (fun _ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) T
      (fun t => V*Matrix.diagonal (fun h => Complex.exp (-Complex.I*t*angles h))*Vᴴ) := by
  have hVstar2 : V*Vᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hV
  set W : ℝ → Matrix H H ℂ :=
    fun t => V*Matrix.diagonal (fun h => Complex.exp (-Complex.I*t*angles h))*Vᴴ with hWdef
  have hcexp (h : H) : Continuous (fun s : ℝ =>
      Complex.exp (-Complex.I*s*(angles h : ℂ))) := by
    continuity
  have hdiagentry : ∀ (g : H → ℂ) (i j : H),
      (V*Matrix.diagonal g*Vᴴ) i j=∑ h, V i h*(g h*star (V j h)) := by
    intro g i j
    simp [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply,mul_assoc]
  have hentry (t : ℝ) (i j : H) :
      W t i j=∑ h, V i h*(Complex.exp (-Complex.I*t*angles h)*star (V j h)) := by
    simp only [hWdef]
    exact hdiagentry _ i j
  have hzeroexp : (fun h => Complex.exp (-Complex.I*(0 : ℝ)*angles h))=(fun _ => (1 : ℂ)) := by
    funext h
    simp
  have hW01 : W 0=1 := by
    simp only [hWdef,hzeroexp,Matrix.diagonal_one,mul_one]
    exact hVstar2
  refine ⟨?_,?_,?_⟩
  · exact hW01
  · have hcont : Continuous W := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      simp only [hentry]
      apply continuous_finsetSum
      intro h _
      exact continuous_const.mul ((hcexp h).mul continuous_const)
    exact hcont.continuousOn
  · intro t ht
    have hderiv (i j : H) (s : ℝ) :
        HasDerivAt (fun u => W u i j)
          (∑ h, V i h*((-Complex.I*angles h)*
            Complex.exp (-Complex.I*s*angles h)*star (V j h))) s := by
      have hsum : HasDerivAt
          (fun (u : ℝ) => ∑ h, V i h*(Complex.exp (-Complex.I*u*angles h)*star (V j h)))
          (∑ h, V i h*((Complex.exp (-Complex.I*s*angles h)*(-Complex.I*angles h))*
            star (V j h))) s := by
        apply HasDerivAt.fun_sum
        intro h _
        have hcoe : HasDerivAt (fun u : ℝ => (u : ℂ)) ((1 : ℂ)) s := by
          simpa using! (Complex.ofRealCLM.hasFDerivAt).hasDerivAt
        have hinner0 := (hcoe.const_mul (-Complex.I : ℂ)).mul_const ((angles h : ℂ))
        have hinner : HasDerivAt (fun (u : ℝ) => (-Complex.I : ℂ)*u*(angles h : ℂ))
            ((-Complex.I*(angles h : ℂ))) s :=
          hinner0.congr_deriv (by ring)
        have hchain := (Complex.hasDerivAt_exp
          ((-Complex.I : ℂ)*s*(angles h : ℂ))).comp s hinner
        simpa only [Function.comp_def,mul_assoc] using!
          ((hchain).const_mul (V i h)).mul_const (star (V j h))
      simp only [hentry]
      refine hsum.congr_deriv ?_
      apply Finset.sum_congr rfl
      intro h _
      ring
    have hKmul (s : ℝ) :
        (fun _ : ℝ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) s*W s=
          V*Matrix.diagonal
            (fun h => (angles h : ℂ)*Complex.exp (-Complex.I*s*angles h))*Vᴴ := by
      have hstep := sourceFrameConj_mul hV
        (Matrix.diagonal (fun h => (angles h : ℂ)))
        (Matrix.diagonal (fun h => Complex.exp (-Complex.I*s*angles h)))
      rw [Matrix.diagonal_mul_diagonal] at hstep
      simpa [hWdef] using! hstep
    have hcontsum (i j : H) : Continuous (fun (s : ℝ) => ∑ h, V i h*((-Complex.I*angles h)*
        Complex.exp (-Complex.I*s*angles h)*star (V j h))) := by
      apply continuous_finsetSum
      intro h _
      continuity
    have hentryeq (i j : H) (s : ℝ) :
        ((-Complex.I) • ((fun _ : ℝ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) s*W s)) i j=
          ∑ h, V i h*((-Complex.I*angles h)*
            Complex.exp (-Complex.I*s*angles h)*star (V j h)) := by
      simp only [Matrix.smul_apply,hKmul,hdiagentry,smul_eq_mul,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun h _ => by ring)
    ext i j
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => W u i j)
      (fun u (_ : u∈Set.uIcc (0 : ℝ) t) => hderiv i j u)
      ((hcontsum i j).intervalIntegrable 0 t)
    have hintgr : (∫ s in (0 : ℝ)..t,((-Complex.I) •
        ((fun _ : ℝ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) s*W s)) i j)=
        ∫ s in (0 : ℝ)..t,∑ h, V i h*((-Complex.I*angles h)*
          Complex.exp (-Complex.I*s*angles h)*star (V j h)) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact hentryeq i j s
    simp only [Matrix.of_apply,Matrix.add_apply,Matrix.one_apply]
    rw [hintgr,hftc]
    (try simp only [])
    have hW0e : W 0 i j=(if i = j then (1 : ℂ) else 0) := by
      rw [hW01,Matrix.one_apply]
    rw [hW0e]
    ring

theorem sourceFrameDiag_entry {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (g : H → ℂ) (i j : H) :
    (V*Matrix.diagonal g*Vᴴ) i j=∑ h, V i h*(g h*star (V j h)) := by
  simp [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply,mul_assoc]

theorem sourceFrameDiag_hermitian_norm {H : Type} [Fintype H] [DecidableEq H]
    (E : Matrix H H ℂ) (Θ : H → ℝ) (hE : E ∈ Matrix.unitaryGroup H ℂ)
    (hΘ : ∀ i, -Real.pi<Θ i ∧ Θ i≤Real.pi) :
    (E*Matrix.diagonal (fun i => (Θ i : ℂ))*Eᴴ).IsHermitian ∧
      ‖E*Matrix.diagonal (fun i => (Θ i : ℂ))*Eᴴ‖≤Real.pi := by
  refine ⟨?_,?_⟩
  · change (E*Matrix.diagonal (fun i => (Θ i : ℂ))*Eᴴ)ᴴ=_
    have hs : star (fun i => (Θ i : ℂ))=(fun i => (Θ i : ℂ)) := by funext i; simp
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose,hs,Matrix.mul_assoc]
  · have hEa : Eᴴ ∈ Matrix.unitaryGroup H ℂ := by
      simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hE
    rw [CStarRing.norm_mul_coe_unitary _ ⟨Eᴴ,hEa⟩,
      CStarRing.norm_coe_unitary_mul ⟨E,hE⟩,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
    intro j
    simp only [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨(hΘ j).1.le,(hΘ j).2⟩

set_option maxHeartbeats 8000000 in

theorem sourceVolterraMatrix_log_value {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    sourceVolterraMatrix (fun _ => sourceLog U) 1=U := by
  obtain ⟨V,angles,hV,ha,hrep,hlog⟩ := sourceLog_representation H U hU
  have hpath : sourceVolterra (fun _ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) 1
      (fun t => V*Matrix.diagonal (fun h => Complex.exp (-Complex.I*t*angles h))*Vᴴ) :=
    sourceVolterra_const_spectral V angles hV 1 zero_le_one
  have hM : sourceVolterraMatrix (fun _ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) 1=
      V*Matrix.diagonal (fun h => Complex.exp (-Complex.I*(1 : ℝ)*angles h))*Vᴴ :=
    sourceVolterraMatrix_eq (fun _ => V*Matrix.diagonal (fun h => (angles h : ℂ))*Vᴴ) 1
      zero_le_one (fun _ _ => continuous_const.intervalIntegrable 0 1)
      (fun t => V*Matrix.diagonal (fun h => Complex.exp (-Complex.I*t*angles h))*Vᴴ) hpath
  rw [hlog,hM]
  have hone : Matrix.diagonal (fun h => Complex.exp (-Complex.I*(1 : ℝ)*angles h))=
      Matrix.diagonal (fun h => Complex.exp (-Complex.I*angles h)) := by
    ext h h'
    simp only [Matrix.diagonal_apply]
    by_cases hc : h=h'
    · rw [if_pos hc,if_pos hc]
      congr 1
      simp
    · rw [if_neg hc,if_neg hc]
  rw [hone]
  exact hrep.symm

set_option maxHeartbeats 8000000 in

theorem sourceLogOracle_frame (X S : Type) [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    ∃ (E : Matrix ((Fin (n+1) × Fin (q+1)) × S) ((Fin (n+1) × Fin (q+1)) × S) ℂ)
      (Θ : ((Fin (n+1) × Fin (q+1)) × S) → ℝ),
      E ∈ Matrix.unitaryGroup _ ℂ ∧ (∀ t, -Real.pi<Θ t ∧ Θ t≤Real.pi) ∧
      sourceLogOracle (W := S) input x=E*Matrix.diagonal (fun t => (Θ t : ℂ))*Eᴴ ∧
      E*Matrix.diagonal (fun t => Complex.exp (-Complex.I*(1 : ℝ)*Θ t))*Eᴴ=
        sourceAlphabetOracle (W := S) input x := by
  have hex : ∀ j : Fin (n+1), ∃ (V : Matrix (Fin (q+1)) (Fin (q+1)) ℂ) (θ : Fin (q+1) → ℝ),
      V ∈ Matrix.unitaryGroup _ ℂ ∧ (∀ h, -Real.pi<θ h ∧ θ h≤Real.pi) ∧
      sourceValueQuery (sourcePaddedSymbol input x j)=
        V*Matrix.diagonal (fun h => Complex.exp (-Complex.I*θ h))*Vᴴ ∧
      sourceLog (sourceValueQuery (sourcePaddedSymbol input x j))=
        V*Matrix.diagonal (fun h => (θ h : ℂ))*Vᴴ := by
    intro j
    have hinj : Function.Injective (fun t : Fin (q+1) => t+sourcePaddedSymbol input x j) := by
      intro a b hab
      exact add_right_cancel hab
    exact sourceLog_representation _ _
      (permMatrix_unitary_of_injective hinj)
  choose Vf θf hVf hθf hrepf hlogf using hex
  set E : Matrix ((Fin (n+1) × Fin (q+1)) × S) ((Fin (n+1) × Fin (q+1)) × S) ℂ :=
    Matrix.of fun p t => if p.1.1=t.1.1 ∧ p.2=t.2 then Vf t.1.1 p.1.2 t.1.2 else 0 with hEdef
  set Θ : ((Fin (n+1) × Fin (q+1)) × S) → ℝ := fun t => θf t.1.1 t.1.2 with hΘdef
  have hsumsplit : ∀ (F : ((Fin (n+1) × Fin (q+1)) × S) → ℂ),
      ∑ r, F r = ∑ j' : Fin (n+1), ∑ i' : Fin (q+1), ∑ w' : S, F ((j',i'),w') := by
    intro F
    rw [← Finset.univ_product_univ,Finset.sum_product,← Finset.univ_product_univ,
      Finset.sum_product]
  have hentry (p t : ((Fin (n+1) × Fin (q+1)) × S)) :
      E p t=if p.1.1=t.1.1 ∧ p.2=t.2 then Vf t.1.1 p.1.2 t.1.2 else 0 := hEdef ▸ rfl
  have hcollapse : ∀ (G1 G2 : Fin (n+1) → Fin (q+1) → ℂ)
      (p t : ((Fin (n+1) × Fin (q+1)) × S)),
      (∑ r : ((Fin (n+1) × Fin (q+1)) × S),
        (if r.1.1=p.1.1 ∧ r.2=p.2 then G1 p.1.1 r.1.2 else 0)*
        (if r.1.1=t.1.1 ∧ r.2=t.2 then G2 t.1.1 r.1.2 else 0))=
      (if p.1.1=t.1.1 ∧ p.2=t.2 then ∑ i', G1 p.1.1 i'*G2 p.1.1 i' else 0) := by
    intro G1 G2 p t
    rw [hsumsplit]
    by_cases hblk : p.1.1=t.1.1 ∧ p.2=t.2
    · rw [← hblk.1,← hblk.2]
      have hterm : ∀ (j' : Fin (n+1)) (i' : Fin (q+1)) (w' : S),
          ((if j'=p.1.1 ∧ w'=p.2 then G1 p.1.1 i' else 0)*
           (if j'=p.1.1 ∧ w'=p.2 then G2 p.1.1 i' else 0))=
          (if j'=p.1.1 ∧ w'=p.2 then G1 p.1.1 i'*G2 p.1.1 i' else 0) := by
        intro j' i' w'
        by_cases hc : j'=p.1.1 ∧ w'=p.2
        · rw [if_pos hc,if_pos hc,if_pos hc]
        · rw [if_neg hc,if_neg hc,if_neg hc,zero_mul]
      simp only [hterm]
      have hj0 : ∀ b : Fin (n+1), b ∈ Finset.univ → b ≠ p.1.1 →
          (∑ i' : Fin (q+1), ∑ w' : S,
            if b=p.1.1 ∧ w'=p.2 then G1 p.1.1 i'*G2 p.1.1 i' else 0)=0 := by
        intro b _ hb
        rw [Finset.sum_eq_zero]
        intro i' _
        rw [Finset.sum_eq_zero]
        intro w' _
        rw [if_neg (fun hc => hb hc.1)]
      rw [Finset.sum_eq_single p.1.1 hj0 (fun h => absurd (Finset.mem_univ p.1.1) h)]
      simp only [true_and,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    · have hterm : ∀ (j' : Fin (n+1)) (i' : Fin (q+1)) (w' : S),
          ((if j'=p.1.1 ∧ w'=p.2 then G1 p.1.1 i' else 0)*
           (if j'=t.1.1 ∧ w'=t.2 then G2 t.1.1 i' else 0))=0 := by
        intro j' i' w'
        by_cases h1 : j'=p.1.1 ∧ w'=p.2
        · rw [if_pos h1]
          have h2 : ¬(j'=t.1.1 ∧ w'=t.2) := by
            intro hc
            exact hblk ⟨h1.1.symm.trans hc.1,h1.2.symm.trans hc.2⟩
          rw [if_neg h2,mul_zero]
        · rw [if_neg h1,zero_mul]
      simp only [hterm]
      rw [if_neg hblk]
      simp
  have hcollapse2 : ∀ (G1 G2 : Fin (n+1) → Fin (q+1) → ℂ)
      (p t : ((Fin (n+1) × Fin (q+1)) × S)),
      (∑ r : ((Fin (n+1) × Fin (q+1)) × S),
        (if p.1.1=r.1.1 ∧ p.2=r.2 then G1 p.1.1 r.1.2 else 0)*
        (if r.1.1=t.1.1 ∧ r.2=t.2 then G2 t.1.1 r.1.2 else 0))=
      (if p.1.1=t.1.1 ∧ p.2=t.2 then ∑ i', G1 p.1.1 i'*G2 p.1.1 i' else 0) := by
    intro G1 G2 p t
    rw [hsumsplit]
    by_cases hblk : p.1.1=t.1.1 ∧ p.2=t.2
    · rw [← hblk.1,← hblk.2]
      have hterm : ∀ (j' : Fin (n+1)) (i' : Fin (q+1)) (w' : S),
          ((if p.1.1=j' ∧ p.2=w' then G1 p.1.1 i' else 0)*
           (if j'=p.1.1 ∧ w'=p.2 then G2 p.1.1 i' else 0))=
          (if p.1.1=j' ∧ p.2=w' then G1 p.1.1 i'*G2 p.1.1 i' else 0) := by
        intro j' i' w'
        by_cases hc : p.1.1=j' ∧ p.2=w'
        · rw [if_pos hc,if_pos ⟨hc.1.symm,hc.2.symm⟩,if_pos hc]
        · rw [if_neg hc,if_neg (fun h' => hc ⟨h'.1.symm,h'.2.symm⟩),if_neg hc,zero_mul]
      simp only [hterm]
      have hj0 : ∀ b : Fin (n+1), b ∈ Finset.univ → b ≠ p.1.1 →
          (∑ i' : Fin (q+1), ∑ w' : S,
            if p.1.1=b ∧ p.2=w' then G1 p.1.1 i'*G2 p.1.1 i' else 0)=0 := by
        intro b _ hb
        rw [Finset.sum_eq_zero]
        intro i' _
        rw [Finset.sum_eq_zero]
        intro w' _
        rw [if_neg (fun hc => hb hc.1.symm)]
      rw [Finset.sum_eq_single p.1.1 hj0 (fun h => absurd (Finset.mem_univ p.1.1) h)]
      simp only [true_and,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    · have hterm : ∀ (j' : Fin (n+1)) (i' : Fin (q+1)) (w' : S),
          ((if p.1.1=j' ∧ p.2=w' then G1 p.1.1 i' else 0)*
           (if j'=t.1.1 ∧ w'=t.2 then G2 t.1.1 i' else 0))=0 := by
        intro j' i' w'
        by_cases h1 : p.1.1=j' ∧ p.2=w'
        · rw [if_pos h1]
          have h2 : ¬(j'=t.1.1 ∧ w'=t.2) := by
            intro hc
            exact hblk ⟨h1.1.trans hc.1,h1.2.trans hc.2⟩
          rw [if_neg h2,mul_zero]
        · rw [if_neg h1,zero_mul]
      simp only [hterm]
      rw [if_neg hblk]
      simp
  have hunitL : ∀ j : Fin (n+1), (Vf j)ᴴ*(Vf j)=1 := by
    intro j
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff.mp (Unitary.star_mem (hVf j))
  have hcollapse3 : ∀ (G1 G2 : Fin (n+1) → Fin (q+1) → ℂ)
      (H : ((Fin (n+1) × Fin (q+1)) × S) → ℂ)
      (p t : ((Fin (n+1) × Fin (q+1)) × S)),
      (∑ r : ((Fin (n+1) × Fin (q+1)) × S),
        (if p.1.1=r.1.1 ∧ p.2=r.2 then G1 r.1.1 r.1.2 else 0)*
        (H r)*
        (if t.1.1=r.1.1 ∧ t.2=r.2 then G2 r.1.1 r.1.2 else 0))=
      (if p.1.1=t.1.1 ∧ p.2=t.2 then
        ∑ i', G1 p.1.1 i'*(H ((p.1.1,i'),p.2))*G2 p.1.1 i' else 0) := by
    intro G1 G2 H p t
    rw [hsumsplit]
    by_cases hblk : p.1.1=t.1.1 ∧ p.2=t.2
    · rw [← hblk.1,← hblk.2]
      have hterm : ∀ (j' : Fin (n+1)) (i' : Fin (q+1)) (w' : S),
          ((if p.1.1=j' ∧ p.2=w' then G1 j' i' else 0)*
           (H ((j',i'),w'))*
           (if p.1.1=j' ∧ p.2=w' then G2 j' i' else 0))=
          (if p.1.1=j' ∧ p.2=w' then G1 j' i'*(H ((j',i'),w'))*G2 j' i' else 0) := by
        intro j' i' w'
        by_cases hc : p.1.1=j' ∧ p.2=w'
        · rw [if_pos hc,if_pos hc,if_pos hc]
        · rw [if_neg hc,if_neg hc,if_neg hc,zero_mul,zero_mul]
      simp only [hterm]
      have hj0 : ∀ b : Fin (n+1), b ∈ Finset.univ → b ≠ p.1.1 →
          (∑ i' : Fin (q+1), ∑ w' : S,
            if p.1.1=b ∧ p.2=w' then G1 b i'*(H ((b,i'),w'))*G2 b i' else 0)=0 := by
        intro b _ hb
        rw [Finset.sum_eq_zero]
        intro i' _
        rw [Finset.sum_eq_zero]
        intro w' _
        rw [if_neg (fun hc => hb hc.1.symm)]
      rw [Finset.sum_eq_single p.1.1 hj0 (fun h => absurd (Finset.mem_univ p.1.1) h)]
      simp only [true_and,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    · have hterm : ∀ (j' : Fin (n+1)) (i' : Fin (q+1)) (w' : S),
          ((if p.1.1=j' ∧ p.2=w' then G1 j' i' else 0)*
           (H ((j',i'),w'))*
           (if t.1.1=j' ∧ t.2=w' then G2 j' i' else 0))=0 := by
        intro j' i' w'
        by_cases h1 : p.1.1=j' ∧ p.2=w'
        · rw [if_pos h1]
          have h2 : ¬(t.1.1=j' ∧ t.2=w') := by
            intro hc
            exact hblk ⟨h1.1.trans hc.1.symm,h1.2.trans hc.2.symm⟩
          rw [if_neg h2,mul_zero]
        · rw [if_neg h1,zero_mul,zero_mul]
      simp only [hterm]
      rw [if_neg hblk]
      simp
  have hentryH (p t : ((Fin (n+1) × Fin (q+1)) × S)) :
      Eᴴ p t=if t.1.1=p.1.1 ∧ t.2=p.2 then star (Vf p.1.1 t.1.2 p.1.2) else 0 := by
    show star (E t p)=_
    by_cases hc : t.1.1=p.1.1 ∧ t.2=p.2
    · rw [hentry t p,if_pos hc,if_pos hc]
    · rw [hentry t p,if_neg hc,star_zero,if_neg hc]
  have hE : E ∈ Matrix.unitaryGroup _ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    ext p t
    rw [Matrix.mul_apply]
    simp only [hentryH,hentry]
    rw [hcollapse (fun j i' => star (Vf j i' p.1.2)) (fun j i' => Vf j i' t.1.2) p t,
      Matrix.one_apply]
    by_cases hblk : p.1.1=t.1.1 ∧ p.2=t.2
    · rw [if_pos hblk]
      by_cases hdiag : p.1.2=t.1.2
      · rw [if_pos (Prod.ext (Prod.ext hblk.1 hdiag) hblk.2),← hdiag]
        have hsmall : ((Vf p.1.1)ᴴ*(Vf p.1.1)) p.1.2 p.1.2=(1 : ℂ) := by
          rw [hunitL p.1.1,Matrix.one_apply,if_pos rfl]
        simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using! hsmall
      · rw [if_neg (fun h => hdiag (congrArg (fun r => r.1.2) h))]
        have hzero : ((Vf p.1.1)ᴴ*(Vf p.1.1)) p.1.2 t.1.2=(0 : ℂ) := by
          rw [hunitL p.1.1,Matrix.one_apply,if_neg hdiag]
        simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using! hzero
    · rw [if_neg hblk]
      by_cases h1 : p.1.1=t.1.1
      · have h2 : p.2≠t.2 := fun h2 => hblk ⟨h1,h2⟩
        rw [if_neg (fun he => h2 (congrArg (fun r => r.2) he))]
      · rw [if_neg (fun he => h1 (congrArg (fun r => r.1.1) he))]
  refine ⟨E,Θ,hE,fun t => hθf t.1.1 t.1.2,?_,?_⟩
  have hER : E*Eᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hE
  have hstep2 : sourceLogOracle (W := S) input x*E=
      E*Matrix.diagonal (fun t => (Θ t : ℂ)) := by
    ext p t
    rw [Matrix.mul_apply]
    simp only [sourceLogOracle,hentry]
    have hR : (E*Matrix.diagonal (fun t => (Θ t : ℂ))) p t=E p t*(Θ t : ℂ) :=
      Matrix.mul_diagonal _ _ _ _
    rw [hR,hentry]
    rw [hcollapse2 (fun j i' => (sourceLog (sourceValueQuery (sourcePaddedSymbol input x j))) p.1.2 i')
      (fun j i' => Vf j i' t.1.2) p t]
    by_cases hblk : p.1.1=t.1.1 ∧ p.2=t.2
    · rw [if_pos hblk,if_pos hblk]
      have hlog : sourceLog (sourceValueQuery (sourcePaddedSymbol input x p.1.1))=
          (Vf p.1.1)*(Matrix.diagonal (fun i => (θf p.1.1 i : ℂ)))*(Vf p.1.1)ᴴ := hlogf p.1.1
      rw [hlog]
      show (((Vf p.1.1)*(Matrix.diagonal (fun i => (θf p.1.1 i : ℂ))))*(Vf p.1.1)ᴴ*(Vf p.1.1)) p.1.2 t.1.2=
        Vf t.1.1 p.1.2 t.1.2*(Θ t : ℂ)
      have hprod : ((Vf p.1.1)*(Matrix.diagonal (fun i => (θf p.1.1 i : ℂ)))*(Vf p.1.1)ᴴ)*(Vf p.1.1)=
          (Vf p.1.1)*(Matrix.diagonal (fun i => (θf p.1.1 i : ℂ))) := by
        rw [Matrix.mul_assoc,hunitL p.1.1,Matrix.mul_one]
      rw [hprod,Matrix.mul_diagonal _ _ _]
      show (Vf p.1.1) p.1.2 t.1.2*(θf p.1.1 t.1.2 : ℂ)=Vf t.1.1 p.1.2 t.1.2*(θf t.1.1 t.1.2 : ℂ)
      rw [hblk.1]
    · rw [if_neg hblk,if_neg hblk,zero_mul]
  · calc sourceLogOracle (W := S) input x
        = sourceLogOracle (W := S) input x*(E*Eᴴ) := by rw [hER,Matrix.mul_one]
      _ = (sourceLogOracle (W := S) input x*E)*Eᴴ := by rw [Matrix.mul_assoc]
      _ = (E*Matrix.diagonal (fun t => (Θ t : ℂ)))*Eᴴ := by rw [hstep2]
  · ext p t
    rw [Matrix.mul_apply]
    have hEd : ∀ r : ((Fin (n+1) × Fin (q+1)) × S),
        (E*Matrix.diagonal (fun s => Complex.exp (-Complex.I*(1 : ℝ)*Θ s))) p r=
        E p r*Complex.exp (-Complex.I*(1 : ℝ)*Θ r) :=
      fun r => Matrix.mul_diagonal _ _ _ _
    simp only [hEd,hentry,hentryH]
    rw [hcollapse3 (fun j i' => Vf j p.1.2 i') (fun j i' => star (Vf j t.1.2 i'))
      (fun r => Complex.exp (-Complex.I*(1 : ℝ)*Θ r)) p t]
    by_cases hblk : p.1.1=t.1.1 ∧ p.2=t.2
    · rw [if_pos hblk]
      simp only [hΘdef]
      have h1 : (Vf p.1.1)*Matrix.diagonal
            (fun i' => Complex.exp (-Complex.I*(1 : ℝ)*θf p.1.1 i'))*(Vf p.1.1)ᴴ=
          sourceValueQuery (sourcePaddedSymbol input x p.1.1) := by
        have hone : Matrix.diagonal (fun i' => Complex.exp (-Complex.I*(1 : ℝ)*θf p.1.1 i'))=
            Matrix.diagonal (fun h => Complex.exp (-Complex.I*θf p.1.1 h)) := by
          ext h h'
          simp only [Matrix.diagonal_apply]
          by_cases hc : h=h'
          · rw [if_pos hc,if_pos hc]
            congr 1
            simp
          · rw [if_neg hc,if_neg hc]
        rw [hone]
        exact (hrepf p.1.1).symm
      calc ∑ i', Vf p.1.1 p.1.2 i'*
            Complex.exp (-Complex.I*(1 : ℝ)*θf p.1.1 i')*star (Vf p.1.1 t.1.2 i')
          = ((Vf p.1.1)*Matrix.diagonal
              (fun i' => Complex.exp (-Complex.I*(1 : ℝ)*θf p.1.1 i'))*(Vf p.1.1)ᴴ) p.1.2 t.1.2 := by
              rw [Matrix.mul_apply]
              have hEd2 : ∀ i' : Fin (q+1),
                  ((Vf p.1.1)*Matrix.diagonal
                    (fun i'' => Complex.exp (-Complex.I*(1 : ℝ)*θf p.1.1 i''))) p.1.2 i'=
                  Vf p.1.1 p.1.2 i'*Complex.exp (-Complex.I*(1 : ℝ)*θf p.1.1 i') :=
                fun i' => Matrix.mul_diagonal _ _ _ _
              simp only [hEd2,Matrix.conjTranspose_apply]
        _ = sourceValueQuery (sourcePaddedSymbol input x p.1.1) p.1.2 t.1.2 := by rw [h1]
        _ = sourceAlphabetOracle (W := S) input x p t := by
              simp only [sourceAlphabetOracle,sourceValueQuery,permMatrix,Matrix.of_apply]
              by_cases hpt : p.1.2=t.1.2+sourcePaddedSymbol input x p.1.1
              · have hpt' : p.1.2=t.1.2+sourcePaddedSymbol input x t.1.1 := by
                  rw [← hblk.1]
                  exact hpt
                have hpe : p=((t.1.1, t.1.2+sourcePaddedSymbol input x t.1.1), t.2) :=
                  Prod.ext (Prod.ext hblk.1 hpt') hblk.2
                rw [if_pos hpt,if_pos hpe]
              · have hne : p≠((t.1.1, t.1.2+sourcePaddedSymbol input x t.1.1), t.2) := by
                  intro he
                  have hpt' : p.1.2=t.1.2+sourcePaddedSymbol input x t.1.1 :=
                    congrArg (fun r => r.1.2) he
                  rw [← hblk.1] at hpt'
                  exact hpt hpt'
                rw [if_neg hpt,if_neg hne]
    · rw [if_neg hblk]
      simp only [sourceAlphabetOracle,permMatrix,Matrix.of_apply]
      by_cases h1 : p.1.1=t.1.1
      · have h2 : p.2≠t.2 := fun h2 => hblk ⟨h1,h2⟩
        rw [if_neg (fun he => h2 (congrArg (fun r => r.2) he))]
      · rw [if_neg (fun he => h1 (congrArg (fun r => r.1.1) he))]

theorem sourceLogOracle_hermitian_norm (X S : Type) [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    (sourceLogOracle (W := S) input x).IsHermitian ∧
      ‖sourceLogOracle (W := S) input x‖≤Real.pi := by
  obtain ⟨E,Θ,hE,hΘ,hL,_⟩ := sourceLogOracle_frame X S input x
  rw [hL]
  exact sourceFrameDiag_hermitian_norm E Θ hE hΘ

set_option maxHeartbeats 8000000 in

theorem volterraAndOracleLogSemantics : VolterraAndOracleLogSemantics := by
  refine ⟨?_,?_,?_⟩
  · intro H _ _ K T hT hi hh
    obtain ⟨F,hFs,hFu⟩ := sourceVolterra_exists H K T hT hi hh
    have hex : ∃ U, sourceVolterra K T U := ⟨F,hFs⟩
    refine ⟨⟨F,hFs,fun V hV t ht => sourceVolterra_unique K F V T hT hi hFs hV t ht,hFu⟩,?_⟩
    rw [sourceVolterraMatrix,dif_pos hex,
      sourceVolterra_unique K (Classical.choose hex) F T hT hi
        (Classical.choose_spec hex) hFs T ⟨hT,le_refl T⟩]
    exact hFu T ⟨hT,le_refl T⟩
  · intro H _ _ U hU
    have hn := sourceLog_hermitian_norm H U hU
    exact ⟨hn.1,hn.2,sourceVolterraMatrix_log_value hU⟩
  · intro X S _ _ n q input x
    obtain ⟨E,Θ,hE,hΘ,hL,hexp⟩ := sourceLogOracle_frame X S input x
    have hhn := sourceFrameDiag_hermitian_norm E Θ hE hΘ
    rw [← hL] at hhn
    refine ⟨hhn.1,hhn.2,?_⟩
    have hbase := sourceVolterra_const_spectral E Θ hE 1 zero_le_one
    rw [← hL] at hbase
    exact (sourceVolterraMatrix_eq (fun _ => sourceLogOracle (W := S) input x) 1 zero_le_one
      (fun _ _ => continuous_const.intervalIntegrable 0 1)
      (fun t => E*Matrix.diagonal (fun s => Complex.exp (-Complex.I*t*Θ s))*Eᴴ) hbase).trans hexp

end Qatlib.Concepts.GramQueryCore.ModelSemantics

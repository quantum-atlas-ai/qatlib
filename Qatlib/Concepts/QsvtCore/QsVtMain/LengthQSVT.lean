/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler

/-!
# Length-controlled real QSVT compilation

This module constructs real phase representations of prescribed positive length for bounded real
polynomials with matching degree bound and parity. The response `sourcePhaseResponse` and the
conjugate-angle family `sourceRealFamily` connect polynomial synthesis with the real-part QSVT
construction of [GilyenSuLowWiebe2019].

The compiled word `sourceRealWord` encodes the odd or right singular transform according to
parity, using the averaged clean frames and an exact instruction count.

## Main statements

* `source_length_real_phase_existence`: Synthesize a real response with prescribed positive
  length.
* `source_cpp_real_singular_transform_of_response`: Turn a response identity into a compiled
  singular-transform encoding.
* `source_length_cpp_real_singular_transform`: Combine phase existence, encoding, and exact
  instruction counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The primary polynomial response of a real-angle list with base phase one. -/
noncomputable def sourcePhaseResponse (Φ : List ℝ) : Polynomial ℂ :=
  responseP 1 (Φ.map anglePhase)

/-- Both response polynomials are linear in the base phase through multiplication by a constant
polynomial. -/
private theorem response_base_linear (base : ℂ) (zs : List ℂ) :
    responseP base zs = C base * responseP 1 zs ∧
    responseQ base zs = C base * responseQ 1 zs := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [responseP_cons, responseQ_cons, ih.1, ih.2]
    constructor <;> ring

/-- A unit complex phase is the phase of its complex argument. -/
theorem anglePhase_arg_of_isPhase {z : ℂ} (hz : IsPhase z) :
    anglePhase z.arg = z := by
  have hn : ‖z‖ = 1 := by
    have hh := congrArg Complex.re hz
    have hs : ‖z‖ ^ 2 = 1 := by
      simpa [Complex.mul_re, Complex.normSq_apply, ← Complex.normSq_eq_norm_sq] using hh
    nlinarith [norm_nonneg z]
  have h0 : z ≠ 0 := by intro h; simp [h] at hn
  apply Complex.ext <;> simp [anglePhase, Complex.cos_arg h0, Complex.sin_arg, hn]

/-- A real polynomial bounded by one on `[-1, 1]`, with degree at most a positive `d` and parity
`d`, has a real phase representation of length `d` [GilyenSuLowWiebe2019]. -/
theorem source_length_real_phase_existence : ∀ (p : Polynomial ℝ) (d : ℕ), 0 < d →
  p.degree ≤ (d : WithBot ℕ) → HasRealParity d p →
  (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
  ∃ Φ : List ℝ, Φ.length = d ∧ ∀ x : ℝ,
    ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x := by
  intro p d hd hp hpar hb
  obtain ⟨base,zs,hbase,hzs,hlen,_,hre⟩ := exists_phases_of_bounded hp hpar hb
  cases zs with
  | nil => simp at hlen; omega
  | cons z zs =>
    have hz : IsPhase z := hzs z (by simp)
    have hbz : IsPhase (base*z) := by
      unfold IsPhase at hbase hz ⊢
      calc
        star (base*z)*(base*z) = (star base*base)*(star z*z) := by rw [star_mul]; ring
        _ = 1 := by rw [hbase,hz]; simp
    let ws := base*z :: zs
    have hw : ∀ w ∈ ws, IsPhase w := by
      intro w h
      rcases List.mem_cons.mp h with h | h
      · subst w; exact hbz
      · exact hzs w (by simp [h])
    have hmap : (ws.map Complex.arg).map anglePhase = ws := by
      rw [List.map_map]
      calc
        ws.map (anglePhase ∘ Complex.arg) = ws.map id := by
          apply List.map_congr_left
          intro w h
          exact anglePhase_arg_of_isPhase (hw w h)
        _ = ws := List.map_id ws
    refine ⟨ws.map Complex.arg, by simpa [ws] using hlen, ?_⟩
    intro x
    have he : responseP 1 ws = responseP base (z::zs) := by
      simp only [ws, responseP_cons, (response_base_linear base zs).1,
        (response_base_linear base zs).2, map_mul]
      ring
    simpa only [sourcePhaseResponse,hmap,he] using hre x

/-- The Boolean-indexed phase family pairing each angle with its negative. -/
def sourceRealFamily (Φ : List ℝ) : List (Bool→ℝ) :=
  Φ.map (fun φ b=>if b then -φ else φ)

/-- The compiled word implementing the two conjugate phase branches, with the oracle convention
chosen by list parity. -/
noncomputable def sourceRealWord {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (Φ : List ℝ) : Matrix (Bool×(Bool×H)) (Bool×(Bool×H)) ℂ :=
  if Φ.length%2=1 then cppEvaluate U P Q (cppCompile (sourceRealFamily Φ))
  else cppEvaluate U Q P ((cppCompile (sourceRealFamily Φ)).map cppSwapData)

/-- The averaged clean-ancilla frame associated to a data frame. -/
noncomputable def sourceAverageClean {H I : Type} [Fintype H] (F : Matrix H I ℂ) :
    Matrix (Bool×(Bool×H)) I ℂ := averageFrame (cppCleanFrame F)

/-- Rectangular matrix multiplication with an explicit finite intermediate index. -/
private noncomputable abbrev sourceMul {M N K : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- Associativity of the explicitly instantiated rectangular matrix product. -/
private theorem sourceMul_assoc {M N K L : Type} [Fintype N] [Fintype K]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) (C : Matrix K L ℂ) :
    sourceMul (sourceMul A B) C = sourceMul A (sourceMul B C) := Matrix.mul_assoc A B C

/-- Adjoining a clean Boolean ancilla preserves the isometry property of a frame. -/
theorem cppCleanFrame_isIsometry {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] {F : Matrix H I ℂ} (hF : IsIsometry F) : IsIsometry (cppCleanFrame F) := by
  have he : cppCleanFrame F = flagFrame F := by
    ext ⟨b,h⟩ i; cases b <;> rfl
  rw [he]
  exact flagFrame_isIsometry hF

/-- The clean embedding for an indexed family is an isometry. -/
private theorem source_family_isometry {J H : Type} [Fintype J] [DecidableEq J]
    [Fintype H] [DecidableEq H] : IsIsometry (cppFamilyClean (J:=J) (H:=H)) := by
  unfold IsIsometry
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j=k
  · subst k
    by_cases hi : h=i
    · subst i
      simp [cppFamilyClean, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, mul_ite]
    · simp [cppFamilyClean, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, mul_ite, hi, Ne.symm hi]
  · simp [cppFamilyClean, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite, hj, Ne.symm hj]

/-- The averaged clean frame factors through the family clean embedding and the averaged
original frame. -/
private theorem source_average_clean {H I : Type} [Fintype H] [DecidableEq H]
    (F : Matrix H I ℂ) :
    sourceAverageClean F = sourceMul (cppFamilyClean (J:=Bool) (H:=H)) (averageFrame F) := by
  ext ⟨j,b,h⟩ i
  cases b <;> simp [sourceAverageClean,averageFrame,cppCleanFrame,cppFamilyClean,
    sourceMul,Matrix.mul_apply,prepareLift,Fintype.sum_prod_type,
    Matrix.one_apply,ite_mul,mul_ite]

/-- A unitary intertwining the clean family embedding with an encoded operator inherits the
encoding on averaged clean frames. -/
private theorem source_clean_encoding {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {V : Matrix (Bool×(Bool×H)) (Bool×(Bool×H)) ℂ}
    {W : Matrix (Bool×H) (Bool×H) ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (hV : V ∈ unitaryGroup _ ℂ)
    (hact : sourceMul V (cppFamilyClean (J:=Bool) (H:=H)) =
      sourceMul (cppFamilyClean (J:=Bool) (H:=H)) W)
    (hW : ProjectedUnitaryEncoding A W (averageFrame L) (averageFrame R)) :
    ProjectedUnitaryEncoding A V (sourceAverageClean L) (sourceAverageClean R) := by
  have hK := source_family_isometry (J:=Bool) (H:=H)
  refine ⟨hV, ?_, ?_, ?_⟩
  · rw [source_average_clean]
    unfold IsIsometry at hK ⊢
    simp only [sourceMul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ _ (averageFrame L),hK,Matrix.one_mul]
    exact hW.left_isometry
  · rw [source_average_clean]
    unfold IsIsometry at hK ⊢
    simp only [sourceMul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ _ (averageFrame R),hK,Matrix.one_mul]
    exact hW.right_isometry
  · rw [source_average_clean,source_average_clean]
    unfold compress
    change sourceMul (sourceMul (sourceMul (cppFamilyClean (J:=Bool) (H:=H)) (averageFrame L))ᴴ V)
      (sourceMul (cppFamilyClean (J:=Bool) (H:=H)) (averageFrame R)) = A
    rw [Matrix.conjTranspose_mul]
    simp only [sourceMul_assoc]
    rw [← sourceMul_assoc V _ _,hact,sourceMul_assoc]
    rw [← sourceMul_assoc (cppFamilyClean (J:=Bool) (H:=H))ᴴ _ _]
    have hK' : sourceMul (cppFamilyClean (J:=Bool) (H:=H))ᴴ
        (cppFamilyClean (J:=Bool) (H:=H)) = 1 := hK
    rw [hK']
    simpa [sourceMul,compress,Matrix.mul_assoc] using hW.encoded

/-- The phase of a negative angle is the conjugate phase. -/
private theorem source_angle_neg (φ : ℝ) : anglePhase (-φ) = star (anglePhase φ) := by
  apply Complex.ext <;> simp [anglePhase]

/-- The Boolean branches of `sourceRealFamily` produce the original phase list and its
conjugate. -/
private theorem source_family_map (Φ : List ℝ) (b : Bool) :
    (sourceRealFamily Φ).map (fun f => anglePhase (f b)) =
      if b then (Φ.map anglePhase).map star else Φ.map anglePhase := by
  cases b <;> simp [sourceRealFamily,List.map_map,source_angle_neg,Function.comp_def]

/-- The selected family of alternating words for the two opposite-angle branches. -/
private noncomputable def sourceBranches {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (Φ : List ℝ) : Matrix (Bool×H) (Bool×H) ℂ :=
  select (fun b => phasedAlternating U P Q 1
    ((sourceRealFamily Φ).map (fun f => anglePhase (f b))))

/-- The two selected phase branches equal the average circuit of the conjugate and original
alternating words. -/
private theorem source_branches_eq {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (Φ : List ℝ) :
    sourceBranches U P Q Φ = averageCircuit
      (phasedAlternating U P Q 1 ((Φ.map anglePhase).map star))
      (phasedAlternating U P Q 1 (Φ.map anglePhase)) := by
  unfold sourceBranches averageCircuit
  congr 1; funext b
  cases b <;> simp [source_family_map]

/-- An encoding by `realPartQSVT` is also an encoding by the selected opposite-angle branches. -/
private theorem source_branches_encoding {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {U P Q : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (Φ : List ℝ)
    (hreal : ProjectedUnitaryEncoding A (realPartQSVT U P Q 1 (Φ.map anglePhase))
      (averageFrame L) (averageFrame R)) :
    ProjectedUnitaryEncoding A (sourceBranches U P Q Φ) (averageFrame L) (averageFrame R) := by
  rw [source_branches_eq]
  refine ⟨?_,hreal.left_isometry,hreal.right_isometry,?_⟩
  · have hu := hreal.unitary
    rw [realPartQSVT,averageCircuit] at hu
    rw [averageCircuit]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu ⊢
    ext ⟨b,h⟩ ⟨c,i⟩
    have he := congrFun (congrFun hu (!b,h)) (!c,i)
    cases b <;> cases c <;>
      simpa [select,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Fintype.sum_prod_type,Matrix.one_apply,mul_ite,ite_mul] using he
  · have he := hreal.encoded
    simp only [realPartQSVT,star_one,averageCircuit_compress] at he
    rw [averageCircuit_compress,add_comm]
    exact he

/-- A real response identity gives the parity-appropriate singular transform through the
compiled clean word, together with its exact instruction counts. -/
theorem source_cpp_real_singular_transform_of_response : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] (A : Matrix O I ℂ)
    (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (p : Polynomial ℝ) (Φ : List ℝ), ProjectedUnitaryEncoding A U L R →
  (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) →
    (Φ.length%2=1 → ProjectedUnitaryEncoding (oddSingularTransform A (fun x=>((p.eval x:ℝ):ℂ)))
      (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean L) (sourceAverageClean R)) ∧
    (Φ.length%2=0 → ProjectedUnitaryEncoding (rightSingularTransform A (fun x=>((p.eval x:ℝ):ℂ)))
      (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean R) (sourceAverageClean R)) ∧
    cppCounts (cppCompile (sourceRealFamily Φ))=
      (Φ.length,2*(Φ.length/2),2*((Φ.length+1)/2),Φ.length) := by
  intro H I O _ _ _ _ _ _ A U L R p Φ h hre
  have hP := rangeProjector_isOrthogonalProjector h.right_isometry
  have hQ := rangeProjector_isOrthogonalProjector h.left_isometry
  have hz : ∀ z ∈ Φ.map anglePhase, IsPhase z := by
    intro z hz; obtain ⟨φ,_,rfl⟩ := List.mem_map.mp hz; exact anglePhase_isPhase φ
  have hone : IsPhase (1 : ℂ) := by simp [IsPhase]
  have hfun : (fun x : ℝ => (((responseP 1 (Φ.map anglePhase)).eval (x : ℂ)).re : ℂ)) =
      (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) := by
    funext x; exact congrArg Complex.ofReal (hre x)
  refine ⟨?_,?_,?_⟩
  · intro hodd
    have hreal := realPartQSVT_odd_singularEncoding h hone (Φ.map anglePhase) hz
      (by simpa only [List.length_map] using hodd)
    rw [hfun] at hreal
    have hbranch := source_branches_encoding Φ hreal
    obtain ⟨hu,hact,_⟩ := cpp_family_actual_compilation_and_counts Bool H U
      (rangeProjector R) (rangeProjector L) (sourceRealFamily Φ) h.unitary hP hQ
    rw [sourceRealWord,if_pos hodd]
    exact source_clean_encoding hu hact hbranch
  · intro heven
    have hreal := realPartQSVT_even_right_singularEncoding h hone (Φ.map anglePhase) hz
      (by simpa only [List.length_map] using heven)
    rw [hfun] at hreal
    have hbranch := source_branches_encoding Φ hreal
    obtain ⟨hu,hact,_⟩ := cpp_family_actual_compilation_and_counts Bool H Uᴴ
      (rangeProjector L) (rangeProjector R) (sourceRealFamily Φ) (adjoint_unitary h.unitary) hQ hP
    rw [sourceRealWord,if_neg (by simp [heven]),cppEvaluate_swapData]
    exact source_clean_encoding hu hact hbranch
  · simpa [sourceRealFamily] using cppCompile_counts (sourceRealFamily Φ)

/-- Every bounded real polynomial with degree at most a positive `d` and parity `d` has a
length-`d` compiled singular-transform encoding with exact instruction counts
[GilyenSuLowWiebe2019]. -/
theorem source_length_cpp_real_singular_transform : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] (A : Matrix O I ℂ)
    (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (p : Polynomial ℝ) (d : ℕ),ProjectedUnitaryEncoding A U L R → 0<d →
  p.degree≤(d:WithBot ℕ) → HasRealParity d p →
  (∀ x∈Set.Icc (-1:ℝ) 1,|p.eval x|≤1) →
  ∃ Φ : List ℝ,Φ.length=d ∧
    (d%2=1 → ProjectedUnitaryEncoding (oddSingularTransform A (fun x=>((p.eval x:ℝ):ℂ)))
      (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean L) (sourceAverageClean R)) ∧
    (d%2=0 → ProjectedUnitaryEncoding (rightSingularTransform A (fun x=>((p.eval x:ℝ):ℂ)))
      (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean R) (sourceAverageClean R)) ∧
    cppCounts (cppCompile (sourceRealFamily Φ))=(d,2*(d/2),2*((d+1)/2),d) := by
  intro H I O _ _ _ _ _ _ A U L R p d h hd hp hpar hb
  obtain ⟨Φ,hlen,hre⟩ := source_length_real_phase_existence p d hd hp hpar hb
  refine ⟨Φ,hlen,?_⟩
  simpa only [hlen] using
    source_cpp_real_singular_transform_of_response H I O A U L R p Φ h hre

end Qatlib.Concepts.QsvtCore.QsVtMain

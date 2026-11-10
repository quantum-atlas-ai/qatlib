/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilationDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify
open Matrix
open Qatlib
open scoped Classical BigOperators

lemma finiteWordMatrix_eq_code (w : ℕ) (gs : List FiniteGateCode) :
    finiteWordMatrix w gs = finiteCodeWordMatrix w gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [finiteWordMatrix, finite_phase_word_cons, ih]
noncomputable def exactCoverWitness : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.diagonal (fun i : Reg 2 => if i=(fun _ => false) then finiteGaussianScalar else 1)

lemma exactCoverWitness_unitary : exactCoverWitness ∈ Matrix.unitaryGroup (Reg 2) ℂ := by
  have hc : (starRingEnd ℂ) finiteGaussianScalar * finiteGaussianScalar = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      finite_phase_gaussian_norm, one_pow]
    rfl
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [exactCoverWitness, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i=(fun _ => false) <;> simp [h, hc]

lemma exactCoverWitness_det : Matrix.det exactCoverWitness = finiteGaussianScalar := by
  simp [exactCoverWitness, Matrix.det_diagonal]

theorem no_exact_gate_cover : noCountableExactGateCover := by
  rintro ⟨words, hw⟩
  obtain ⟨k, hk, he⟩ := hw exactCoverWitness exactCoverWitness_unitary
  have hd := (finite_code_word_determinant_invariant 2 (words k) hk).2.1
  rw [← finiteWordMatrix_eq_code, he, exactCoverWitness_det] at hd
  have h16 : finiteGaussianScalar^16 = 1 := by
    calc _ = (finiteGaussianScalar^8)^2 := by rw [← pow_mul]
         _ = 1 := by rw [hd, one_pow]
  have hr := finite_phase_gaussian_sixteen
  rw [h16] at hr
  norm_num at hr

lemma not_empty_find {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (Sc Uc Cc bound : ℝ) : ¬ HasRealElementFind P ∅ Sc Uc Cc bound := by
  rintro ⟨Mq, k, t, L, w, sw, uw, cw, h⟩
  rcases h with ⟨_, hs, _, _, _, _, _, _, _, _, _, _, _, _, _, h0⟩
  rw [h0 rfl] at hs
  norm_num at hs

lemma singleton_transition : IsTransitionMatrix (fun _ _ : Fin 1 => (1:ℝ)) := by
  constructor <;> simp

lemma singleton_gap : SymmetricChainGap (fun _ _ : Fin 1 => (1:ℝ)) 1 := by
  refine ⟨singleton_transition, by simp, ?_⟩
  intro v hv
  have hv0 : v 0 = 0 := by simpa using! hv
  simp [hv0]

lemma not_empty_walk_find {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (Sc Uc Cc bound : ℝ) : ¬ HasWalkFind P ∅ Sc Uc Cc bound := by
  rintro ⟨k, t, M, _, h, _⟩
  norm_num [walkFindSuccessProb, edgeMarkedSet, MeasureProb] at h

open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
set_option maxHeartbeats 1000000

lemma two_frame_eigen_action {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A B : Matrix H I ℂ)
    (hA : Aᴴ*A=1) (hB : Bᴴ*B=1) (hGram : (Aᴴ*B)ᴴ=Aᴴ*B)
    (v : I → ℂ) (z : ℂ) (hv : (Aᴴ*B)*ᵥv=z • v) :
    (ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))*ᵥ(A*ᵥv) =
      (2*z) • (B*ᵥv)-A*ᵥv ∧
    (ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))*ᵥ(B*ᵥv) =
      (-(2*z)) • (A*ᵥv)+(4*z^2-1) • (B*ᵥv) := by
  have ha : Aᴴ*ᵥ(A*ᵥv)=v := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  have hb : Bᴴ*ᵥ(B*ᵥv)=v := by rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  have hab : Aᴴ*ᵥ(B*ᵥv)=z • v := by rw [Matrix.mulVec_mulVec]; exact hv
  have hba : Bᴴ*ᵥ(A*ᵥv)=z • v := by
    rw [Matrix.mulVec_mulVec, show Bᴴ*A=Aᴴ*B by
      rw [← hGram, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]]
    exact hv
  have haa : ReflectionAbout (A*Aᴴ)*ᵥ(A*ᵥv)=A*ᵥv := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, ha]
    module
  have hbb : ReflectionAbout (B*Bᴴ)*ᵥ(B*ᵥv)=B*ᵥv := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, hb]
    module
  have hba' : ReflectionAbout (B*Bᴴ)*ᵥ(A*ᵥv)=(2*z) • (B*ᵥv)-A*ᵥv := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, hba, Matrix.mulVec_smul, smul_smul]
  have hab' : ReflectionAbout (A*Aᴴ)*ᵥ(B*ᵥv)=(2*z) • (A*ᵥv)-B*ᵥv := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec, hab, Matrix.mulVec_smul, smul_smul]
  constructor
  · rw [← Matrix.mulVec_mulVec, haa, hba']
  · rw [← Matrix.mulVec_mulVec, hab', Matrix.mulVec_sub, Matrix.mulVec_smul, hba', hbb]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

lemma reachable_two_plane {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) : ReachableTwoPlaneLaw P := by
  intro u lam hu
  have he : ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P)*ᵥ(complexLift u) =
      (lam:ℂ) • complexLift u := by
    rw [szegedy_gram_eq_discriminant P hP]
    ext i
    have hi := congrFun hu i
    simp only [Matrix.mulVec, dotProduct, complexLift, Matrix.map_apply,
      Pi.smul_apply, smul_eq_mul] at hi ⊢
    exact_mod_cast hi
  rw [szegedyWalk_eq_twoReflections P hP]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one] using!
    two_frame_eigen_action (SzegedyIsometry P) (SzegedyIsometryB P)
      (szegedyIsometry_conjTranspose_mul P hP) (szegedyIsometryB_conjTranspose_mul P hP)
      (szegedy_gram_hermitian P hP) (complexLift u) (lam:ℂ) he

lemma frame_vector_mem {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (v : QState I) :
    SzegedyIsometry P *ᵥ v ∈ walkReachableSpan P ∧
      SzegedyIsometryB P *ᵥ v ∈ walkReachableSpan P := by
  have he (A : Matrix (I×I) I ℂ) : A*ᵥv = ∑ j, v j • (A*ᵥKet j) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_comm]
  constructor
  · rw [he]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  · rw [he]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨i, rfl⟩))

lemma reachable_span_invariant {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) : WalkPreservesReachableSpan P := by
  have hA (ψ : QState (I×I)) (hψ : ψ ∈ walkReachableSpan P) :
      ReflectionAbout (SzegedyIsometry P*(SzegedyIsometry P)ᴴ)*ᵥψ ∈ walkReachableSpan P := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec]
    exact (walkReachableSpan P).sub_mem
      ((walkReachableSpan P).smul_mem 2 (frame_vector_mem P _).1) hψ
  have hB (ψ : QState (I×I)) (hψ : ψ ∈ walkReachableSpan P) :
      ReflectionAbout (SzegedyIsometryB P*(SzegedyIsometryB P)ᴴ)*ᵥψ ∈ walkReachableSpan P := by
    rw [reflectionAbout_mulVec, ← Matrix.mulVec_mulVec]
    exact (walkReachableSpan P).sub_mem
      ((walkReachableSpan P).smul_mem 2 (frame_vector_mem P _).2) hψ
  constructor
  · intro ψ hψ
    rw [szegedyWalk_eq_twoReflections P hP, ← Matrix.mulVec_mulVec]
    exact hB _ (hA _ hψ)
  · intro ψ hψ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
    · intro x hx
      rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · change SwapGate*ᵥ(SzegedyIsometry P*ᵥKet i) ∈ walkReachableSpan P
        rw [Matrix.mulVec_mulVec]
        exact (frame_vector_mem P (Qatlib.Foundations.PureStateMath.Ket i)).2
      · change SwapGate*ᵥ((SwapGate*SzegedyIsometry P)*ᵥKet i) ∈ walkReachableSpan P
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, swapGate_mul_self, Matrix.one_mul]
        exact (frame_vector_mem P (Qatlib.Foundations.PureStateMath.Ket i)).1
    · simp
    · intro x y _hx _hy hx hy
      rw [Matrix.mulVec_add]
      exact (walkReachableSpan P).add_mem hx hy
    · intro c x _hx hx
      rw [Matrix.mulVec_smul]
      exact (walkReachableSpan P).smul_mem c hx

lemma addressed_frame_completion {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (e : I ↪ H) (F : Matrix H I ℂ) (hF : IsIsometry F) :
    ∃ U : Matrix H H ℂ, U ∈ unitaryGroup H ℂ ∧
      ∀ i, U *ᵥ Qatlib.Foundations.PureStateMath.Ket (e i) = F *ᵥ Qatlib.Foundations.PureStateMath.Ket i := by
  let v : H → EuclideanSpace ℂ H := fun x =>
    if h : ∃ j, e j = x then WithLp.toLp 2 (fun i => F i (Classical.choose h)) else 0
  have ve (j : I) : v (e j) = WithLp.toLp 2 (fun i => F i j) := by
    have hj : ∃ k, e k = e j := ⟨j, rfl⟩
    dsimp only [v]
    rw [dif_pos hj]
    have he : Classical.choose hj = j := e.injective (Classical.choose_spec hj)
    rw [he]
  have hv : Orthonormal ℂ ((Set.range e).restrict v) := by
    rw [orthonormal_iff_ite]
    intro ⟨x,hx⟩ ⟨y,hy⟩
    obtain ⟨j,rfl⟩ := hx
    obtain ⟨k,rfl⟩ := hy
    dsimp only [Set.restrict, Set.domRestrict]; rw [ve, ve, EuclideanSpace.inner_eq_star_dotProduct]
    have hh := congrArg (fun M : Matrix I I ℂ => M j k) hF
    simpa [IsIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      dotProduct, e.injective.eq_iff, Subtype.ext_iff, mul_comm, WithLp.ofLp_toLp] using! hh
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (ι := H) finrank_euclideanSpace
  let U : Matrix H H ℂ := fun x y => b y x
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext x y
    have hbxy := orthonormal_iff_ite.mp b.orthonormal x y
    simpa [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using! hbxy
  · intro i
    ext x
    simp only [mulVec_ket_column]
    have hi := hb (e i) ⟨i,rfl⟩
    rw [ve] at hi
    exact congrArg (fun w : EuclideanSpace ℂ H => w x) hi

lemma graph_setup {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (hP : IsTransitionMatrix P) : GraphSetupAccount P S := by
  intro j
  let e : I ↪ I×I := ⟨fun i => (i,j), fun i k h => congrArg Prod.fst h⟩
  obtain ⟨U, hU, hcol⟩ := addressed_frame_completion e (SzegedyIsometry P)
    (szegedyIsometry_conjTranspose_mul P hP)
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · intro i
    rw [tensorState_ket_ket]
    exact hcol i
  · have ht : TensorState chainUniform (Qatlib.Foundations.PureStateMath.Ket j) =
        ∑ i : I, (chainUniform i) • Qatlib.Foundations.PureStateMath.Ket (i,j) := by
      ext x
      simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, Prod.ext_iff, ite_and]
    rw [ht, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    have hc (i : I) : U*ᵥKet (i,j)=SzegedyIsometry P*ᵥKet i := hcol i
    simp only [hc]
    ext x
    simp [detectionInitial, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket,
        mul_comm]
  · exact (detection_marked_initial_mass P S hP).2

lemma graph_bit_access_zero_workspace (n d : ℕ) (hdn : d ≤ n)
    (adj : Fin n → Fin n → Bool) (M : Fin n → Bool) :
    HasGraphBitAccess n d hdn adj M := by
  have hpow (m : ℕ) : m < 2^m := by
    induction m with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have hn := hpow n
  let enc : Fin n → Reg n := fun i => (bitVecEquiv n).symm ⟨i.val, by omega⟩
  have henc : Function.Injective enc := by
    intro i j h
    have he := congrArg (bitVecEquiv n) h
    simp only [enc, Equiv.apply_symm_apply] at he
    exact Fin.ext (congrArg (fun x : Fin (2^n) => x.val) he)
  have hrun (r s : Reg 0) : finiteWordRun 0 [] (Qatlib.Foundations.PureStateMath.Ket r) = some (Qatlib.Foundations.PureStateMath.Ket s) := by
    have he : r=s := Subsingleton.elim _ _
    subst s
    simp [finiteWordRun, finiteWordLegal, finiteCodeCircuit]
  refine ⟨n, 0, 0, 0, 0, enc, [], [], henc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [finiteWordLegal]
  · simp [finiteWordLegal]
  · intro x k hk
    exact hrun _ _
  · intro x
    exact hrun _ _
  · simp
  · simp
  · simp

end Qatlib.Concepts.WalkSearch.MnrsAmplify

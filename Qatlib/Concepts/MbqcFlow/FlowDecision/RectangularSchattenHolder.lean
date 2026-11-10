/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.SchattenDiamond
import QuantumInfo.ForMathlib.HermitianMat.Schatten
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

noncomputable section

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder

variable {M N K D E : Type} [Fintype M] [Fintype N] [Fintype K]
  [Fintype D] [Fintype E]
  [DecidableEq M] [DecidableEq N] [DecidableEq K] [DecidableEq D] [DecidableEq E]

def embed (U : Matrix D M ℂ) (V : Matrix E N ℂ) (A : Matrix M N ℂ) : Matrix D E ℂ :=
  U * A * Vᴴ

omit [Fintype E] [DecidableEq N] [DecidableEq D] [DecidableEq E] in

theorem embed_gram (U : Matrix D M ℂ) (V : Matrix E N ℂ)
    (A : Matrix M N ℂ) (hU : Uᴴ * U = 1) :
    (embed U V A)ᴴ * embed U V A = V * (Aᴴ * A) * Vᴴ := by
  simp only [embed, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    V * (Aᴴ * Uᴴ) * (U * A * Vᴴ) = V * Aᴴ * (Uᴴ * U) * A * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [hU, Matrix.mul_assoc]

def cornerHom (V : Matrix E N ℂ) (hV : Vᴴ * V = 1) :
    Matrix N N ℂ →⋆ₙₐ[ℝ] Matrix E E ℂ where
  toFun A := V * A * Vᴴ
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' A B := by
    calc
      V * (A * B) * Vᴴ = V * A * (Vᴴ * V) * B * Vᴴ := by simp [hV, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  map_smul' c A := by simp [Matrix.smul_mul, Matrix.mul_smul]
  map_star' A := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem cfc_corner (V : Matrix E N ℂ) (hV : Vᴴ * V = 1)
    (G : Matrix N N ℂ) (hG : G.IsHermitian) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 = 0) :
    cfc f (V * G * Vᴴ) = V * cfc f G * Vᴴ := by
  let φ := cornerHom V hV
  have hφ : Continuous φ := by
    change Continuous (fun A : Matrix N N ℂ => V * A * Vᴴ)
    fun_prop
  have hself : IsSelfAdjoint G := hG
  have hself' : IsSelfAdjoint (φ G) := by
    change (V * G * Vᴴ).IsHermitian
    exact Matrix.isHermitian_mul_mul_conjTranspose V hG
  have h := φ.map_cfcₙ f G hf.continuousOn hf0 hφ hself hself'
  rw [cfcₙ_eq_cfc hf.continuousOn hf0, cfcₙ_eq_cfc hf.continuousOn hf0] at h
  exact h.symm

omit [DecidableEq E] in

theorem trace_corner (V : Matrix E N ℂ) (hV : Vᴴ * V = 1) (G : Matrix N N ℂ) :
    Matrix.trace (V * G * Vᴴ) = Matrix.trace G := by
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

theorem spectral_sum_eq_trace (G : Matrix N N ℂ) (hG : G.IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (hG.eigenvalues i) = (Matrix.trace (cfc f G)).re := by
  rw [hG.cfc_eq, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]

theorem spectral_sum_corner (V : Matrix E N ℂ) (hV : Vᴴ * V = 1)
    (G : Matrix N N ℂ) (hG : G.IsHermitian) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 = 0) :
    ∑ i, f ((Matrix.isHermitian_mul_mul_conjTranspose V hG).eigenvalues i) =
      ∑ i, f (hG.eigenvalues i) := by
  rw [spectral_sum_eq_trace, spectral_sum_eq_trace, cfc_corner V hV G hG f hf hf0,
    trace_corner V hV]

omit [DecidableEq D] in

theorem schatten_embed (p : ℝ) (hp : 0 < p)
    (U : Matrix D M ℂ) (V : Matrix E N ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (A : Matrix M N ℂ) :
    schattenPower p (embed U V A) = schattenPower p A := by
  dsimp only [schattenPower]
  apply congrArg (fun x : ℝ => x ^ p⁻¹)
  have hg := embed_gram U V A hU
  have he := spectral_sum_corner V hV (Aᴴ * A)
    (Matrix.isHermitian_conjTranspose_mul_self A)
    (fun x : ℝ => (Real.sqrt x)^p)
    ((Real.continuous_rpow_const hp.le).comp Real.continuous_sqrt)
    (by simp [Real.zero_rpow hp.ne'])
  simpa only [← hg] using! he

theorem isometry_norm_le (U : Matrix D M ℂ) (hU : Uᴴ*U=1) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [hU] at h
  have h₁ : ‖(1 : Matrix M M ℂ)‖ ≤ 1 := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le
  nlinarith [norm_nonneg U]

theorem norm_two_contractions (L : Matrix D M ℂ) (R : Matrix N E ℂ) (A : Matrix M N ℂ)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L*A*R‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖L*A‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖L‖*‖A‖)*‖R‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul L A) (norm_nonneg R)
    _ ≤ (1*‖A‖)*1 := by gcongr
    _ = _ := by ring

theorem extract_embed (U : Matrix D M ℂ) (V : Matrix E N ℂ)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) (A : Matrix M N ℂ) : Uᴴ*(embed U V A)*V=A := by
  calc
    _ = (Uᴴ*U)*A*(Vᴴ*V) := by simp only [embed, Matrix.mul_assoc]
    _ = A := by simp [hU,hV]

theorem opnorm_embed (U : Matrix D M ℂ) (V : Matrix E N ℂ)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) (A : Matrix M N ℂ) : ‖embed U V A‖=‖A‖ := by
  have hu := isometry_norm_le U hU
  have hv := isometry_norm_le V hV
  have hu' : ‖Uᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using! hu
  have hv' : ‖Vᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using! hv
  apply le_antisymm (norm_two_contractions U Vᴴ A hu hv')
  calc
    ‖A‖ = ‖Uᴴ*(embed U V A)*V‖ := by rw [extract_embed U V hU hV A]
    _ ≤ ‖embed U V A‖ := norm_two_contractions Uᴴ V (embed U V A) hu' hv

theorem square_norm_eq (A : Matrix N N ℂ) (p : ℝ) (hp : 0 < p) :
    schattenPower p A = schattenNorm A p := by
  have hn : schattenNorm A p = @schattenNorm N _ (Classical.decEq N) A p :=
    congrArg (fun d : DecidableEq N => @schattenNorm N _ d A p) (Subsingleton.elim _ _)
  rw [hn, schattenPower_eq_frozen_schatten]
  unfold Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schatten
  simpa only [one_div] using!
    (@schattenNorm_eq_sum_singularValues_rpow N _ (Classical.decEq N) A p hp).symm

def coordM : Matrix (Sum M (Sum N K)) M ℂ := Matrix.fromRows 1 0

def coordN : Matrix (Sum M (Sum N K)) N ℂ := Matrix.fromRows 0 (Matrix.fromRows 1 0)

def coordK : Matrix (Sum M (Sum N K)) K ℂ := Matrix.fromRows 0 (Matrix.fromRows 0 1)

omit [DecidableEq N] [DecidableEq K] in

theorem coordM_iso : (coordM (M:=M) (N:=N) (K:=K))ᴴ * coordM (M:=M) (N:=N) (K:=K) = 1 := by
  simp [coordM, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]

omit [DecidableEq M] [DecidableEq K] in

theorem coordN_iso : (coordN (M:=M) (N:=N) (K:=K))ᴴ * coordN (M:=M) (N:=N) (K:=K) = 1 := by
  simp [coordN, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]

omit [DecidableEq M] [DecidableEq N] in

theorem coordK_iso : (coordK (M:=M) (N:=N) (K:=K))ᴴ * coordK (M:=M) (N:=N) (K:=K) = 1 := by
  simp [coordK, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]

omit [DecidableEq M] [DecidableEq K] [DecidableEq D] in

theorem embed_mul (U : Matrix D M ℂ) (V : Matrix D N ℂ) (W : Matrix D K ℂ)
    (hV : Vᴴ * V = 1) (A : Matrix M N ℂ) (B : Matrix N K ℂ) :
    embed U W (A * B) = embed U V A * embed V W B := by
  simp only [embed]
  calc
    U * (A * B) * Wᴴ = U * A * (Vᴴ * V) * B * Wᴴ := by simp [hV, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem rectangular_holder (A : Matrix M N ℂ) (B : Matrix N K ℂ)
    (r p q : ℝ) (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hpqr : 1/r = 1/p + 1/q) :
    schattenPower r (A*B) ≤ schattenPower p A * schattenPower q B := by
  let U := coordM (M:=M) (N:=N) (K:=K)
  let V := coordN (M:=M) (N:=N) (K:=K)
  let W := coordK (M:=M) (N:=N) (K:=K)
  have hU : Uᴴ*U=1 := coordM_iso
  have hV : Vᴴ*V=1 := coordN_iso
  have hW : Wᴴ*W=1 := coordK_iso
  have h := schattenNorm_mul_le (embed U V A) (embed V W B) hr hp hq hpqr
  rw [← square_norm_eq _ r hr, ← square_norm_eq _ p hp, ← square_norm_eq _ q hq,
    ← embed_mul U V W hV A B, schatten_embed r hr U W hU hW,
    schatten_embed p hp U V hU hV, schatten_embed q hq V W hV hW] at h
  exact h

open Polynomial

theorem charpoly_corner (V : Matrix E N ℂ) (hV : Vᴴ * V = 1) (G : Matrix N N ℂ) :
    X ^ Fintype.card N * (V * G * Vᴴ).charpoly
      = X ^ Fintype.card E * G.charpoly := by
  have h := Matrix.charpoly_mul_comm' (V * G) Vᴴ
  have hm : Vᴴ * (V * G) = G := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  simpa only [hm] using! h

theorem roots_corner_nonzero (V : Matrix E N ℂ) (hV : Vᴴ * V = 1) (G : Matrix N N ℂ) :
    (V * G * Vᴴ).charpoly.roots.filter (fun z => z ≠ 0)
      = G.charpoly.roots.filter (fun z => z ≠ 0) := by
  classical
  have h := congrArg Polynomial.roots (charpoly_corner V hV G)
  have hl : (X ^ Fintype.card N * (V * G * Vᴴ).charpoly : ℂ[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  have hr : (X ^ Fintype.card E * G.charpoly : ℂ[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  rw [Polynomial.roots_mul hl, Polynomial.roots_mul hr,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at h
  have hf := congrArg (Multiset.filter (fun z : ℂ => z ≠ 0)) h
  have hz (n : ℕ) : Multiset.filter (fun z : ℂ => z ≠ 0) (n • ({0} : Multiset ℂ)) = 0 := by
    induction n with
    | zero => simp
    | succ n ih => simp [succ_nsmul, Multiset.filter_add, ih]
  simpa [hz] using! hf

def singularMultiset (A : Matrix M N ℂ) : Multiset ℝ :=
  Finset.univ.val.map (fun i => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i))

def nonzeroSingularValues (A : Matrix M N ℂ) : Multiset ℝ :=
  (singularMultiset A).filter (fun x => x ≠ 0)

theorem sqrt_ne_zero_iff (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hs hz
    exact hs (by simp [hz])
  · intro hn hs
    apply hn
    nlinarith [Real.sq_sqrt hx]

theorem nonzeroSingularValues_eq_roots (A : Matrix M N ℂ) :
    nonzeroSingularValues A =
      ((Aᴴ*A).charpoly.roots.filter (fun z => z ≠ 0)).map (fun z : ℂ => Real.sqrt z.re) := by
  classical
  rw [(Matrix.isHermitian_conjTranspose_mul_self A).roots_charpoly_eq_eigenvalues]
  simp only [nonzeroSingularValues, singularMultiset, Multiset.filter_map, Multiset.map_map,
    Function.comp_def]
  congr 1
  apply Multiset.filter_congr
  intro i _
  have hs := sqrt_ne_zero_iff _ ((Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)
  constructor
  · intro hn hz
    apply hs.mp hn
    have he := congrArg Complex.re hz
    simpa using! he
  · intro hn hz
    apply hn
    have he := hs.not.mp (not_not.mpr hz)
    simp only [not_not] at he
    simp [he]

theorem nonzero_singular_embed (U : Matrix D M ℂ) (V : Matrix E N ℂ)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) (A : Matrix M N ℂ) :
    nonzeroSingularValues (embed U V A) = nonzeroSingularValues A := by
  rw [nonzeroSingularValues_eq_roots, nonzeroSingularValues_eq_roots, embed_gram U V A hU,
    roots_corner_nonzero V hV (Aᴴ*A)]

omit [DecidableEq N] in

theorem power_conjTranspose (A : Matrix N N ℂ) (p : ℝ) :
    schattenPower p Aᴴ = schattenPower p A := by
  classical
  have he : (gram_isHermitian Aᴴ).eigenvalues = (gram_isHermitian A).eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    simp only [Matrix.conjTranspose_conjTranspose]
    exact Matrix.charpoly_mul_comm A Aᴴ
  dsimp only [schattenPower]
  rw [he]

theorem norm_conjTranspose (A : Matrix N N ℂ) (p : ℝ) (hp : 0 < p) :
    schattenNorm Aᴴ p = schattenNorm A p := by
  rw [← square_norm_eq Aᴴ p hp, ← square_norm_eq A p hp, power_conjTranspose]

theorem norm_mul_le_op_right (A B : Matrix N N ℂ) (p : ℝ) (hp : 0 < p) :
    schattenNorm (A*B) p ≤ schattenNorm A p * ‖B‖ := by
  calc
    schattenNorm (A*B) p = schattenNorm (A*B)ᴴ p := (norm_conjTranspose (A*B) p hp).symm
    _ = schattenNorm (Bᴴ*Aᴴ) p := by rw [Matrix.conjTranspose_mul]
    _ ≤ ‖Bᴴ‖ * schattenNorm Aᴴ p := Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.schatten_mul_le_op Bᴴ Aᴴ p hp
    _ = schattenNorm A p * ‖B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, norm_conjTranspose A p hp]
      exact mul_comm _ _

theorem power_mul_le_op_left (A B : Matrix N N ℂ) (p : ℝ) (hp : 0 < p) :
    schattenPower p (A*B) ≤ ‖A‖ * schattenPower p B := by
  rw [square_norm_eq _ p hp, square_norm_eq _ p hp]
  exact Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.schatten_mul_le_op A B p hp

theorem power_mul_le_op_right (A B : Matrix N N ℂ) (p : ℝ) (hp : 0 < p) :
    schattenPower p (A*B) ≤ schattenPower p A * ‖B‖ := by
  rw [square_norm_eq _ p hp, square_norm_eq _ p hp]
  exact norm_mul_le_op_right A B p hp

theorem rectangular_op_left (A : Matrix M N ℂ) (B : Matrix N K ℂ) (p : ℝ) (hp : 0 < p) :
    schattenPower p (A*B) ≤ ‖A‖ * schattenPower p B := by
  let U := coordM (M:=M) (N:=N) (K:=K)
  let V := coordN (M:=M) (N:=N) (K:=K)
  let W := coordK (M:=M) (N:=N) (K:=K)
  have hU : Uᴴ*U=1 := coordM_iso
  have hV : Vᴴ*V=1 := coordN_iso
  have hW : Wᴴ*W=1 := coordK_iso
  have h := power_mul_le_op_left (embed U V A) (embed V W B) p hp
  rw [← embed_mul U V W hV A B, schatten_embed p hp U W hU hW,
    opnorm_embed U V hU hV, schatten_embed p hp V W hV hW] at h
  exact h

theorem rectangular_op_right (A : Matrix M N ℂ) (B : Matrix N K ℂ) (p : ℝ) (hp : 0 < p) :
    schattenPower p (A*B) ≤ schattenPower p A * ‖B‖ := by
  let U := coordM (M:=M) (N:=N) (K:=K)
  let V := coordN (M:=M) (N:=N) (K:=K)
  let W := coordK (M:=M) (N:=N) (K:=K)
  have hU : Uᴴ*U=1 := coordM_iso
  have hV : Vᴴ*V=1 := coordN_iso
  have hW : Wᴴ*W=1 := coordK_iso
  have h := power_mul_le_op_right (embed U V A) (embed V W B) p hp
  rw [← embed_mul U V W hV A B, schatten_embed p hp U W hU hW,
    schatten_embed p hp U V hU hV, opnorm_embed V W hV hW] at h
  exact h

theorem unitary_transport (p : ℝ) (hp : 0 < p) (A : Matrix M N ℂ)
    (U : Matrix M M ℂ) (V : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup M ℂ) (hV : V ∈ Matrix.unitaryGroup N ℂ) :
    schattenPower p (U*A*Vᴴ) = schattenPower p A ∧ ‖U*A*Vᴴ‖=‖A‖ := by
  have hu : Uᴴ*U=1 := ((Matrix.mem_unitaryGroup_iff_isometry U).mp hU).1
  have hv : Vᴴ*V=1 := ((Matrix.mem_unitaryGroup_iff_isometry V).mp hV).1
  exact ⟨schatten_embed p hp U V hu hv A, opnorm_embed U V hu hv A⟩

theorem gram_zero_eigenvalues :
    (Matrix.isHermitian_conjTranspose_mul_self (0 : Matrix M N ℂ)).eigenvalues = 0 := by
  exact (Matrix.IsHermitian.eigenvalues_eq_zero_iff
    (Matrix.isHermitian_conjTranspose_mul_self (0 : Matrix M N ℂ))).mpr (by simp)

theorem schatten_zero (p : ℝ) (hp : 0 < p) : schattenPower p (0 : Matrix M N ℂ)=0 := by
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq N := Classical.decEq N
  dsimp only [schattenPower]
  rw [gram_zero_eigenvalues (M:=M) (N:=N)]
  simp [Real.zero_rpow hp.ne', Real.zero_rpow (inv_pos.mpr hp).ne']

theorem singular_zero : nonzeroSingularValues (0 : Matrix M N ℂ) = 0 := by
  unfold nonzeroSingularValues singularMultiset
  rw [gram_zero_eigenvalues (M:=M) (N:=N)]
  simp [Multiset.mem_replicate]

theorem zero_dimensions (p : ℝ) (hp : 0 < p) (A : Matrix M N ℂ) (h : IsEmpty M ∨ IsEmpty N) :
    schattenPower p A = 0 ∧ ‖A‖=0 ∧ nonzeroSingularValues A=0 := by
  have ha : A=0 := by
    ext i j
    rcases h with hm | hn
    · exact (hm.false i).elim
    · exact (hn.false j).elim
  rw [ha]
  exact ⟨schatten_zero p hp, norm_zero, singular_zero⟩

theorem frontier1 (A : Matrix M N ℂ) (B : Matrix N K ℂ)
    (r p q : ℝ) (hr : 0 < r) (hp : 0 < p) (hq : 0 < q) (hpqr : 1/r=1/p+1/q) :
    schattenPower r (A*B) ≤ schattenPower p A * schattenPower q B ∧
    schattenPower r (A*B) ≤ ‖A‖ * schattenPower r B ∧
    schattenPower r (A*B) ≤ schattenPower r A * ‖B‖ ∧
    ‖A*B‖ ≤ ‖A‖*‖B‖ := by
  exact ⟨rectangular_holder A B r p q hr hp hq hpqr, rectangular_op_left A B r hr,
    rectangular_op_right A B r hr, Matrix.l2_opNorm_mul A B⟩

def rowColumnSchur (u : M → ℂ) (v : N → ℂ) (A : Matrix M N ℂ) : Matrix M N ℂ :=
  fun i j => u i * v j * A i j

theorem rowColumnSchur_eq (u : M → ℂ) (v : N → ℂ) (A : Matrix M N ℂ) :
    rowColumnSchur u v A = Matrix.diagonal u * A * Matrix.diagonal v := by
  ext i j
  simp only [rowColumnSchur, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem rowColumnSchur_bound (p : ℝ) (hp : 0 < p) (u : M → ℂ) (v : N → ℂ) (A : Matrix M N ℂ) :
    schattenPower p (rowColumnSchur u v A) ≤ ‖u‖ * schattenPower p A * ‖v‖ := by
  rw [rowColumnSchur_eq]
  calc
    _ ≤ schattenPower p (Matrix.diagonal u * A) * ‖Matrix.diagonal v‖ := rectangular_op_right _ _ p hp
    _ ≤ (‖Matrix.diagonal u‖*schattenPower p A)*‖Matrix.diagonal v‖ :=
      mul_le_mul_of_nonneg_right (rectangular_op_left _ _ p hp) (norm_nonneg _)
    _ = _ := by rw [Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_diagonal]

end Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder

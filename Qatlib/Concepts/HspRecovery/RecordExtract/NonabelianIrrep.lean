/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianDefs
import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawDihe
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.LinearAlgebra.Semisimple
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian.TopBitBundle

set_option autoImplicit false

open Qatlib
open scoped BigOperators

namespace Qatlib.Concepts.HspRecovery.RecordExtract
open scoped Classical

theorem irrep_rhoY_sq {N : ℕ} {V : DihedralIrrep N} : V.rhoY * V.rhoY = 1 := by
  have h := V.orderY
  rwa [pow_two] at h

theorem irrep_rhoXt_mul {N : ℕ} {V : DihedralIrrep N} :
    V.rhoX.conjTranspose * V.rhoX = 1 := by
  have h := V.unitaryX
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using! h

theorem irrep_rhoX_mul_rhoXt {N : ℕ} {V : DihedralIrrep N} :
    V.rhoX * V.rhoX.conjTranspose = 1 := by
  have h := V.unitaryX
  rw [Matrix.mem_unitaryGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using! h

theorem irrep_rhoY_mul_rhoX {N : ℕ} {V : DihedralIrrep N} :
    V.rhoY * V.rhoX = V.rhoX.conjTranspose * V.rhoY := by
  calc V.rhoY * V.rhoX = V.rhoY * V.rhoX * 1 := (mul_one _).symm
    _ = V.rhoY * V.rhoX * (V.rhoY * V.rhoY) := by rw [irrep_rhoY_sq]
    _ = (V.rhoY * V.rhoX * V.rhoY) * V.rhoY := by noncomm_ring
    _ = V.rhoX.conjTranspose * V.rhoY := by rw [V.relation]

theorem irrep_rhoY_mul_rhoX_pow {N : ℕ} {V : DihedralIrrep N} (k : ℕ) :
    V.rhoY * V.rhoX ^ k = V.rhoX.conjTranspose ^ k * V.rhoY := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc V.rhoY * V.rhoX ^ (k + 1)
        = (V.rhoY * V.rhoX ^ k) * V.rhoX := by rw [pow_succ, mul_assoc]
      _ = (V.rhoX.conjTranspose ^ k * V.rhoY) * V.rhoX := by rw [ih]
      _ = V.rhoX.conjTranspose ^ k * (V.rhoY * V.rhoX) := by noncomm_ring
      _ = V.rhoX.conjTranspose ^ k * (V.rhoX.conjTranspose * V.rhoY) :=
        by rw [irrep_rhoY_mul_rhoX]
      _ = V.rhoX.conjTranspose ^ (k + 1) * V.rhoY := by rw [← mul_assoc, ← pow_succ]

theorem irrep_rhoXt_pow_mul {N : ℕ} {V : DihedralIrrep N} (k : ℕ) :
    V.rhoX.conjTranspose ^ k * V.rhoX ^ k = 1 := by
  have h : V.rhoX ^ k ∈ Matrix.unitaryGroup (Fin V.dim) ℂ := pow_mem V.unitaryX k
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_pow] using! h

theorem irrep_reflection_sq {N : ℕ} [NeZero N] {V : DihedralIrrep N} (s : ZMod N) :
    reflectionElem V s * reflectionElem V s = 1 := by
  simp only [reflectionElem]
  have hYXsY : V.rhoY * V.rhoX ^ s.val * V.rhoY = V.rhoX.conjTranspose ^ s.val := by
    calc V.rhoY * V.rhoX ^ s.val * V.rhoY = (V.rhoY * V.rhoX ^ s.val) * V.rhoY := rfl
      _ = (V.rhoX.conjTranspose ^ s.val * V.rhoY) * V.rhoY :=
        by rw [irrep_rhoY_mul_rhoX_pow]
      _ = V.rhoX.conjTranspose ^ s.val * (V.rhoY * V.rhoY) := by noncomm_ring
      _ = V.rhoX.conjTranspose ^ s.val * 1 := by rw [irrep_rhoY_sq]
      _ = V.rhoX.conjTranspose ^ s.val := mul_one _
  have rearr : (V.rhoY * V.rhoX ^ s.val) * (V.rhoY * V.rhoX ^ s.val)
      = (V.rhoY * V.rhoX ^ s.val * V.rhoY) * V.rhoX ^ s.val := by noncomm_ring
  calc (V.rhoY * V.rhoX ^ s.val) * (V.rhoY * V.rhoX ^ s.val)
      = (V.rhoY * V.rhoX ^ s.val * V.rhoY) * V.rhoX ^ s.val := rearr
    _ = V.rhoX.conjTranspose ^ s.val * V.rhoX ^ s.val := by rw [hYXsY]
    _ = 1 := irrep_rhoXt_pow_mul s.val

theorem irrep_rank_eq_trace_idem {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (h : P * P = P) : (P.rank : ℂ) = P.trace := by
  have hlin : IsIdempotentElem P.toLin' := by
    have := congrArg Matrix.toLin' h
    simpa [Matrix.toLin'_mul, Matrix.toLin'_one] using! this
  have hproj : LinearMap.IsProj (LinearMap.range P.toLin') P.toLin' :=
    LinearMap.IsIdempotentElem.isProj_range P.toLin' hlin
  have htr : LinearMap.trace ℂ (n → ℂ) P.toLin'
      = (Module.finrank ℂ (LinearMap.range P.toLin') : ℂ) :=
    LinearMap.IsProj.trace hproj
  have htr2 : LinearMap.trace ℂ (n → ℂ) P.toLin' = P.trace := Matrix.trace_toLin'_eq P
  have hrank0 : P.rank = Module.finrank ℂ (LinearMap.range P.mulVecLin) := rfl
  have hsame : P.mulVecLin = P.toLin' := (Matrix.toLin'_apply' P).symm
  rw [hsame] at hrank0
  rw [← hrank0] at htr
  exact htr.symm.trans htr2

theorem irrep_dimFixed_eq_trace {N : ℕ} [NeZero N] (V : DihedralIrrep N) (s : ZMod N) :
    (dimFixed V s : ℂ) = ((V.dim : ℂ) + Matrix.trace (reflectionElem V s)) / 2 := by
  have hR2 : reflectionElem V s * reflectionElem V s = 1 := irrep_reflection_sq s
  set R := reflectionElem V s
  set P : Matrix (Fin V.dim) (Fin V.dim) ℂ := (2 : ℂ)⁻¹ • (1 + R)
  have hkey : (1 + R) * (1 + R) = (2 : ℂ) • (1 + R) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw [Matrix.one_mul, Matrix.mul_one, hR2, two_smul]
    ac_rfl
  have hPP : P * P = P := by
    show ((2 : ℂ)⁻¹ • (1 + R)) * ((2 : ℂ)⁻¹ • (1 + R)) = (2 : ℂ)⁻¹ • (1 + R)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hkey, smul_smul]
    congr 1
    ring
  have htrace : Matrix.trace P = (2 : ℂ)⁻¹ * ((V.dim : ℂ) + Matrix.trace R) := by
    show Matrix.trace ((2 : ℂ)⁻¹ • (1 + R)) = _
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
    ring
  have hrank : (Matrix.rank P : ℂ) = Matrix.trace P := irrep_rank_eq_trace_idem P hPP
  rw [htrace] at hrank
  have this : (dimFixed V s : ℂ) = (Matrix.rank P : ℂ) := rfl
  rw [this, hrank]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  field_simp
open scoped Classical
open Matrix

theorem pair_self_ne_zero {n : Type} [Fintype n] {u : n → ℂ} (hu : u ≠ 0) :
    star u ⬝ᵥ u ≠ 0 := by
  intro h
  apply hu
  ext i
  have hsum : (star u ⬝ᵥ u) = ∑ j : n, star (u j) * u j := by simp [dotProduct]
  rw [hsum] at h
  have key : ∀ j : n, star (u j) * u j = (Complex.normSq (u j) : ℂ) := by
    intro j
    have h2 := Complex.mul_conj (u j)
    rw [mul_comm] at h2
    exact h2
  simp only [key] at h
  rw [← Complex.ofReal_sum] at h
  have hre : (∑ j : n, Complex.normSq (u j)) = 0 := Complex.ofReal_eq_zero.mp h
  have hterm : ∀ j : n, Complex.normSq (u j) = 0 := by
    intro j
    have hnn : ∀ j : n, 0 ≤ Complex.normSq (u j) := fun j => Complex.normSq_nonneg _
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hre
    · exact hre j (Finset.mem_univ j)
    · intro j _; exact hnn j
  exact Complex.normSq_eq_zero.mp (hterm i)

theorem star_smul_vec {n : Type} (r : ℂ) (v : n → ℂ) : star (r • v) = star r • star v := by
  ext i; simp [Pi.smul_apply, Pi.star_apply]

theorem pair_mulVec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.conjTranspose * A = 1) (u w : n → ℂ) :
    (star (A *ᵥ u)) ⬝ᵥ (A *ᵥ w) = (star u) ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hA,
    Matrix.one_mulVec]

theorem pair_smul_smul {n : Type} [Fintype n] (a b : ℂ) (x y : n → ℂ) :
    (a • x) ⬝ᵥ (b • y) = (a * b) * (x ⬝ᵥ y) := by
  simp only [dotProduct, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem star_mul_self_of_eigen {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.conjTranspose * A = 1) {μ : ℂ} {u : n → ℂ}
    (hu : u ≠ 0) (hAu : A *ᵥ u = μ • u) : star μ * μ = 1 := by
  have h1 : (star u) ⬝ᵥ u = (star u) ⬝ᵥ (A.conjTranspose *ᵥ (A *ᵥ u)) := by
    rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  rw [Matrix.dotProduct_mulVec] at h1
  have h2 : star u ᵥ* A.conjTranspose = star (A *ᵥ u) := (Matrix.star_mulVec A u).symm
  rw [h2, hAu] at h1
  have hnn : star u ⬝ᵥ u ≠ 0 := pair_self_ne_zero hu
  have h3 : star (μ • u) ⬝ᵥ (μ • u) = (star μ * μ) * (star u ⬝ᵥ u) := by
    rw [star_smul_vec]
    simp only [dotProduct, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have key : (star u ⬝ᵥ u) = (star μ * μ) * (star u ⬝ᵥ u) := h1.trans h3
  have hsub : (star μ * μ - 1) * (star u ⬝ᵥ u) = 0 := by
    rw [sub_mul, one_mul, ← key]
    exact sub_self _
  have hz := mul_eq_zero.mp hsub
  exact sub_eq_zero.mp (hz.resolve_right hnn)

theorem vecMulVec_mulVec_apply {n : Type} [Fintype n] (u v z : n → ℂ) :
    vecMulVec u v *ᵥ z = (v ⬝ᵥ z) • u := by
  ext i
  simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, mul_comm, mul_left_comm,
    Finset.mul_sum]

theorem exists_eigen_of_factor {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (μ ν : ℂ)
    (hfac : (X - μ • 1) * (X - ν • 1) = 0)
    (hnot : ∀ κ : ℂ, X ≠ κ • 1) :
    ∃ u : n → ℂ, u ≠ 0 ∧ X *ᵥ u = μ • u := by
  by_cases hinj : ∀ v : n → ℂ, (X - μ • 1) *ᵥ v = 0 → v = 0
  · have hzero : ∀ v : n → ℂ, (X - ν • 1) *ᵥ v = 0 := by
      intro v
      have h1 : ((X - μ • 1) * (X - ν • 1)) *ᵥ v = 0 := by rw [hfac]; simp
      rw [← Matrix.mulVec_mulVec] at h1
      exact hinj _ h1
    have hX : X = ν • 1 := by
      ext i j
      have hcol := congrFun (hzero (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at hcol
      have hent : X i j - (ν • 1 : Matrix n n ℂ) i j = 0 := hcol
      exact sub_eq_zero.mp hent
    exact absurd hX (hnot ν)
  · have hex : ∃ v : n → ℂ, (X - μ • 1) *ᵥ v = 0 ∧ v ≠ 0 := by
      by_contra h
      apply hinj
      intro v hv
      by_contra hne0
      exact h ⟨v, hv, hne0⟩
    obtain ⟨v, hv, hv0⟩ := hex
    refine ⟨v, hv0, ?_⟩
    have : (X - μ • 1) *ᵥ v = 0 := hv
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact sub_eq_zero.mp this

theorem adjoint_eigen {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hXtX : X.conjTranspose * X = 1) {μ : ℂ} {u : n → ℂ} (hμ : μ ≠ 0) (hXu : X *ᵥ u = μ • u) :
    X.conjTranspose *ᵥ u = μ⁻¹ • u := by
  have h1 : X.conjTranspose *ᵥ (X *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, hXtX, Matrix.one_mulVec]
  rw [hXu, Matrix.mulVec_smul] at h1
  have h2 := congrArg (fun z => μ⁻¹ • z) h1
  simp only [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h2
  exact h2

theorem star_vecMul_of_eigen {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hXtX : X.conjTranspose * X = 1) {μ : ℂ} {u : n → ℂ} (hu : u ≠ 0) (hXu : X *ᵥ u = μ • u) :
    star u ᵥ* X = μ • star u := by
  have hsm := star_mul_self_of_eigen X hXtX hu hXu
  have hμ : μ ≠ 0 := by rintro rfl; simp at hsm
  have hconj : star μ = μ⁻¹ := by
    have hμ0 : μ ≠ 0 := hμ
    calc star μ = star μ * 1 := (mul_one _).symm
      _ = star μ * (μ * μ⁻¹) := by rw [mul_inv_cancel₀ hμ0]
      _ = (star μ * μ) * μ⁻¹ := by rw [← mul_assoc]
      _ = 1 * μ⁻¹ := by rw [hsm]
      _ = μ⁻¹ := one_mul _
  have hXt : X.conjTranspose *ᵥ u = μ⁻¹ • u := adjoint_eigen X hXtX hμ hXu
  have hstar : star (X.conjTranspose *ᵥ u) = star (μ⁻¹ • u) := congrArg star hXt
  rw [Matrix.star_mulVec, star_smul_vec] at hstar
  rw [Matrix.conjTranspose_conjTranspose] at hstar
  have hinv : star (μ⁻¹ : ℂ) = (star μ)⁻¹ := by
    rw [← starRingEnd_apply, ← starRingEnd_apply, map_inv₀]
  rw [hinv, hconj, inv_inv] at hstar
  exact hstar

theorem aux_dim_two {N : ℕ} (V : DihedralIrrep N) (μ ν : ℂ)
    (hμν : μ * ν = 1) (hne : μ ≠ ν)
    (hfac : (V.rhoX - μ • 1) * (V.rhoX - ν • 1) = 0)
    (hnot : ∀ κ : ℂ, V.rhoX ≠ κ • 1) : V.dim = 2 := by
  classical
  have hXtX : V.rhoX.conjTranspose * V.rhoX = 1 := by
    have h := V.unitaryX; rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [Matrix.star_eq_conjTranspose] using! h
  have hXXt : V.rhoX * V.rhoX.conjTranspose = 1 := by
    have h := V.unitaryX; rw [Matrix.mem_unitaryGroup_iff] at h
    simpa [Matrix.star_eq_conjTranspose] using! h
  have hy2 : V.rhoY * V.rhoY = 1 := by have h := V.orderY; rwa [pow_two] at h
  have hYX : V.rhoY * V.rhoX = V.rhoX.conjTranspose * V.rhoY := by
    calc V.rhoY * V.rhoX = V.rhoY * V.rhoX * 1 := (mul_one _).symm
      _ = V.rhoY * V.rhoX * (V.rhoY * V.rhoY) := by rw [irrep_rhoY_sq]
      _ = (V.rhoY * V.rhoX * V.rhoY) * V.rhoY := by simp [mul_assoc]
      _ = V.rhoX.conjTranspose * V.rhoY := by rw [V.relation]
  have hXY : V.rhoX * V.rhoY = V.rhoY * V.rhoX.conjTranspose := by
    have hrel : V.rhoY * (V.rhoY * V.rhoX * V.rhoY) * V.rhoY
        = V.rhoY * V.rhoX.conjTranspose * V.rhoY :=
      congrArg (fun M => V.rhoY * M * V.rhoY) V.relation
    have hYXtY : V.rhoY * V.rhoX.conjTranspose * V.rhoY = V.rhoX := by
      have h1 : V.rhoY * (V.rhoY * V.rhoX * V.rhoY) * V.rhoY = V.rhoX := by
        have e : V.rhoY * (V.rhoY * V.rhoX * V.rhoY) * V.rhoY
            = (V.rhoY * V.rhoY) * V.rhoX * (V.rhoY * V.rhoY) := by simp [mul_assoc]
        rw [e, hy2, one_mul, mul_one]
      rw [h1] at hrel
      exact hrel.symm
    calc V.rhoX * V.rhoY = (V.rhoY * V.rhoX.conjTranspose * V.rhoY) * V.rhoY := by rw [hYXtY]
      _ = V.rhoY * V.rhoX.conjTranspose * (V.rhoY * V.rhoY) := by simp [mul_assoc]
      _ = V.rhoY * V.rhoX.conjTranspose * 1 := by rw [irrep_rhoY_sq]
      _ = V.rhoY * V.rhoX.conjTranspose := mul_one _
  obtain ⟨u, hu, hXu⟩ := exists_eigen_of_factor V.rhoX μ ν hfac hnot
  have hsm := star_mul_self_of_eigen V.rhoX hXtX hu hXu
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hsm
  have hconj : star μ = μ⁻¹ := by
    calc star μ = star μ * 1 := (mul_one _).symm
      _ = star μ * (μ * μ⁻¹) := by rw [mul_inv_cancel₀ hμ0]
      _ = (star μ * μ) * μ⁻¹ := by rw [← mul_assoc]
      _ = 1 * μ⁻¹ := by rw [hsm]
      _ = μ⁻¹ := one_mul _
  have hν : ν = μ⁻¹ := by
    calc ν = 1 * ν := (one_mul _).symm
      _ = (μ⁻¹ * μ) * ν := by rw [inv_mul_cancel₀ hμ0]
      _ = μ⁻¹ * (μ * ν) := by rw [← mul_assoc]
      _ = μ⁻¹ * 1 := by rw [hμν]
      _ = μ⁻¹ := mul_one _
  have hμ2 : μ ^ 2 ≠ 1 := by
    rintro h2
    apply hne
    have hme : μ = μ⁻¹ := by
      calc μ = μ * 1 := (mul_one _).symm
        _ = μ * (μ * μ⁻¹) := by rw [mul_inv_cancel₀ hμ0]
        _ = (μ * μ) * μ⁻¹ := by rw [← mul_assoc]
        _ = (μ ^ 2) * μ⁻¹ := by rw [pow_two]
        _ = 1 * μ⁻¹ := by rw [h2]
        _ = μ⁻¹ := one_mul _
    rw [hme, ← hν]
  set w : Fin V.dim → ℂ := V.rhoY *ᵥ u
  have hXt : V.rhoX.conjTranspose *ᵥ u = μ⁻¹ • u := adjoint_eigen V.rhoX hXtX hμ0 hXu
  have hXw : V.rhoX *ᵥ w = ν • w := by
    show V.rhoX *ᵥ (V.rhoY *ᵥ u) = ν • (V.rhoY *ᵥ u)
    rw [Matrix.mulVec_mulVec, hXY]
    show (V.rhoY * V.rhoX.conjTranspose) *ᵥ u = ν • (V.rhoY *ᵥ u)
    rw [← Matrix.mulVec_mulVec, hXt, Matrix.mulVec_smul, hν]
  have horth : star u ⬝ᵥ w = 0 := by
    have hpair := pair_mulVec V.rhoX hXtX u w
    rw [hXu, hXw, star_smul_vec, pair_smul_smul] at hpair
    have hpair' : star u ⬝ᵥ w = (star μ * ν) * (star u ⬝ᵥ w) := hpair.symm
    have hneq : star μ * ν ≠ 1 := by
      rw [hconj, hν]
      intro hbad
      apply hμ2
      have h3 : μ⁻¹ ^ 2 = 1 := by rw [← hbad]; ring
      have h4 : μ ^ 2 * μ⁻¹ ^ 2 = μ ^ 2 := by
        have := congrArg (fun z => μ ^ 2 * z) h3
        simp only [mul_one] at this
        exact this
      have h5 : μ ^ 2 * μ⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hμ0, one_pow]
      rw [h5] at h4
      exact h4.symm
    have hz : (star μ * ν - 1) * (star u ⬝ᵥ w) = 0 := by
      rw [sub_mul, one_mul, ← hpair']
      exact sub_self _
    exact mul_eq_zero.mp hz |>.resolve_left (sub_ne_zero_of_ne hneq)
  set A : Matrix (Fin V.dim) (Fin V.dim) ℂ := vecMulVec u (star u)
  have hAX : A * V.rhoX = V.rhoX * A := by
    have h1 : A * V.rhoX = vecMulVec u (star u ᵥ* V.rhoX) := by
      change vecMulVec u (star u) * V.rhoX = _
      rw [Matrix.vecMulVec_mul]
    have h2 : V.rhoX * A = vecMulVec (V.rhoX *ᵥ u) (star u) := by
      change V.rhoX * vecMulVec u (star u) = _
      rw [Matrix.mul_vecMulVec]
    rw [h1, h2, star_vecMul_of_eigen V.rhoX hXtX hu hXu, hXu]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply]
    ring
  have hAXt : A * V.rhoX.conjTranspose = V.rhoX.conjTranspose * A := by
    have e1 : V.rhoX.conjTranspose * (A * V.rhoX) * V.rhoX.conjTranspose
        = (V.rhoX.conjTranspose * A) * (V.rhoX * V.rhoX.conjTranspose) := by noncomm_ring
    have e2 : V.rhoX.conjTranspose * (V.rhoX * A) * V.rhoX.conjTranspose
        = (V.rhoX.conjTranspose * V.rhoX) * (A * V.rhoX.conjTranspose) := by noncomm_ring
    have e3 : V.rhoX.conjTranspose * (A * V.rhoX) * V.rhoX.conjTranspose
        = V.rhoX.conjTranspose * (V.rhoX * A) * V.rhoX.conjTranspose := by rw [hAX]
    have hmid : (V.rhoX.conjTranspose * A) * (V.rhoX * V.rhoX.conjTranspose)
        = (V.rhoX.conjTranspose * V.rhoX) * (A * V.rhoX.conjTranspose) := by
      rw [← e1, e3, e2]
    rw [hXXt, hXtX, mul_one, one_mul] at hmid
    exact hmid.symm
  set T : Matrix (Fin V.dim) (Fin V.dim) ℂ := A + V.rhoY * A * V.rhoY
  have hTX : T * V.rhoX = V.rhoX * T := by
    have hs : (V.rhoY * A * V.rhoY) * V.rhoX = V.rhoX * (V.rhoY * A * V.rhoY) := by
      calc (V.rhoY * A * V.rhoY) * V.rhoX = V.rhoY * A * (V.rhoY * V.rhoX) := by simp [mul_assoc]
        _ = V.rhoY * A * (V.rhoX.conjTranspose * V.rhoY) := by rw [hYX]
        _ = V.rhoY * (A * V.rhoX.conjTranspose) * V.rhoY := by simp [mul_assoc]
        _ = V.rhoY * (V.rhoX.conjTranspose * A) * V.rhoY := by rw [hAXt]
        _ = (V.rhoY * V.rhoX.conjTranspose) * (A * V.rhoY) := by simp [mul_assoc]
        _ = (V.rhoX * V.rhoY) * (A * V.rhoY) := by rw [← hXY]
        _ = V.rhoX * (V.rhoY * A * V.rhoY) := by
          have t1 : (V.rhoX * V.rhoY) * (A * V.rhoY) = V.rhoX * (V.rhoY * (A * V.rhoY)) := by
            rw [mul_assoc]
          have t2 : V.rhoX * (V.rhoY * A * V.rhoY) = V.rhoX * (V.rhoY * (A * V.rhoY)) := by
            rw [mul_assoc]
          rw [t1, t2]
    show (A + V.rhoY * A * V.rhoY) * V.rhoX = V.rhoX * (A + V.rhoY * A * V.rhoY)
    rw [Matrix.add_mul, Matrix.mul_add, hAX, hs]
  have hTY : T * V.rhoY = V.rhoY * T := by
    show (A + V.rhoY * A * V.rhoY) * V.rhoY = V.rhoY * (A + V.rhoY * A * V.rhoY)
    rw [Matrix.add_mul, Matrix.mul_add]
    have h1 : (V.rhoY * A * V.rhoY) * V.rhoY = V.rhoY * A := by
      calc (V.rhoY * A * V.rhoY) * V.rhoY = V.rhoY * A * (V.rhoY * V.rhoY) := by simp [mul_assoc]
        _ = V.rhoY * A * 1 := by rw [irrep_rhoY_sq]
        _ = V.rhoY * A := mul_one _
    have h2 : V.rhoY * (V.rhoY * A * V.rhoY) = A * V.rhoY := by
      calc V.rhoY * (V.rhoY * A * V.rhoY) = (V.rhoY * V.rhoY) * A * V.rhoY := by simp [mul_assoc]
        _ = 1 * A * V.rhoY := by rw [irrep_rhoY_sq]
        _ = A * V.rhoY := by simp
    rw [h1, h2, add_comm]
  obtain ⟨c, hc⟩ := V.irreducible T hTX hTY
  have hA : A *ᵥ u = (star u ⬝ᵥ u) • u := by
    change vecMulVec u (star u) *ᵥ u = _
    rw [vecMulVec_mulVec_apply]
  have hS : (V.rhoY * A * V.rhoY) *ᵥ u = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hAw : A *ᵥ (V.rhoY *ᵥ u) = (star u ⬝ᵥ (V.rhoY *ᵥ u)) • u := by
      change vecMulVec u (star u) *ᵥ (V.rhoY *ᵥ u) = _
      rw [vecMulVec_mulVec_apply]
    rw [hAw, show V.rhoY *ᵥ u = w from rfl, horth, zero_smul, Matrix.mulVec_zero]
  have hTu : T *ᵥ u = (star u ⬝ᵥ u) • u := by
    show (A + V.rhoY * A * V.rhoY) *ᵥ u = _
    rw [Matrix.add_mulVec, hA, hS, add_zero]
  have hcu : c • u = (star u ⬝ᵥ u) • u := by
    have := congrArg (fun M => M *ᵥ u) hc
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at this
    rw [hTu] at this
    exact this.symm
  have hceq : c = star u ⬝ᵥ u := by
    have hdiff : (c - (star u ⬝ᵥ u)) • u = 0 := by
      rw [sub_smul, hcu, sub_self]
    have hz := smul_eq_zero.mp hdiff
    rcases hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact absurd hz hu
  have hT1 : T = (star u ⬝ᵥ u) • 1 := by rw [hc, hceq]
  have htr1 : Matrix.trace T = 2 * (star u ⬝ᵥ u) := by
    show Matrix.trace (A + V.rhoY * A * V.rhoY) = 2 * (star u ⬝ᵥ u)
    rw [Matrix.trace_add]
    have htrA : Matrix.trace A = star u ⬝ᵥ u := by
      change Matrix.trace (vecMulVec u (star u)) = _
      rw [Matrix.trace_vecMulVec, dotProduct_comm]
    have htrS : Matrix.trace (V.rhoY * A * V.rhoY) = star u ⬝ᵥ u := by
      rw [Matrix.trace_mul_cycle V.rhoY A V.rhoY]
      have hyy : V.rhoY * V.rhoY * A = A := by rw [hy2, one_mul]
      rw [hyy, htrA]
    rw [htrA, htrS]
    ring
  have htr2 : Matrix.trace T = (star u ⬝ᵥ u) * V.dim := by
    rw [hT1, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    rw [smul_eq_mul]
  have hnn : star u ⬝ᵥ u ≠ 0 := pair_self_ne_zero hu
  have hcalc : (star u ⬝ᵥ u) * V.dim = (star u ⬝ᵥ u) * 2 := by
    have := htr2.symm.trans htr1
    rw [this]
    ring
  have hfin : (V.dim : ℂ) = 2 := (mul_left_cancel₀ hnn) hcalc
  exact_mod_cast hfin

theorem irrep_rhoY_comm_conjSum {N : ℕ} (V : DihedralIrrep N) :
    V.rhoY * (V.rhoX + V.rhoX.conjTranspose) = (V.rhoX + V.rhoX.conjTranspose) * V.rhoY := by
  have hYXtY : V.rhoY * V.rhoX.conjTranspose * V.rhoY = V.rhoX := by
    have h : V.rhoY * (V.rhoY * V.rhoX * V.rhoY) * V.rhoY
        = V.rhoY * V.rhoX.conjTranspose * V.rhoY :=
      congrArg (fun M => V.rhoY * M * V.rhoY) V.relation
    have h1 : V.rhoY * (V.rhoY * V.rhoX * V.rhoY) * V.rhoY = V.rhoX := by
      have e : V.rhoY * (V.rhoY * V.rhoX * V.rhoY) * V.rhoY
          = (V.rhoY * V.rhoY) * V.rhoX * (V.rhoY * V.rhoY) := by noncomm_ring
      rw [e, irrep_rhoY_sq, one_mul, mul_one]
    rw [h1] at h
    exact h.symm
  have h1 : V.rhoY * (V.rhoX + V.rhoX.conjTranspose) * V.rhoY = V.rhoX + V.rhoX.conjTranspose := by
    rw [Matrix.mul_add, Matrix.add_mul, V.relation, hYXtY]
    exact (add_comm _ _).symm
  calc V.rhoY * (V.rhoX + V.rhoX.conjTranspose)
      = V.rhoY * (V.rhoX + V.rhoX.conjTranspose) * (V.rhoY * V.rhoY) := by
        rw [irrep_rhoY_sq, mul_one]
    _ = (V.rhoY * (V.rhoX + V.rhoX.conjTranspose) * V.rhoY) * V.rhoY := by noncomm_ring
    _ = (V.rhoX + V.rhoX.conjTranspose) * V.rhoY := by rw [h1]

theorem irrep_sum_conjTranspose {N : ℕ} (V : DihedralIrrep N) :
    ∃ c : ℂ, V.rhoX + V.rhoX.conjTranspose = c • 1 := by
  set M := V.rhoX + V.rhoX.conjTranspose
  have hX : M * V.rhoX = V.rhoX * M := by
    show (V.rhoX + V.rhoX.conjTranspose) * V.rhoX = V.rhoX * (V.rhoX + V.rhoX.conjTranspose)
    rw [Matrix.add_mul, Matrix.mul_add, irrep_rhoXt_mul, irrep_rhoX_mul_rhoXt]
  have hY : M * V.rhoY = V.rhoY * M := by
    show (V.rhoX + V.rhoX.conjTranspose) * V.rhoY = V.rhoY * (V.rhoX + V.rhoX.conjTranspose)
    exact (irrep_rhoY_comm_conjSum V).symm
  have hex := V.irreducible M hX hY
  show ∃ c, V.rhoX + V.rhoX.conjTranspose = c • 1
  exact hex

theorem irrep_rhoX_sq {N : ℕ} (V : DihedralIrrep N) (c : ℂ)
    (hc : V.rhoX + V.rhoX.conjTranspose = c • 1) :
    V.rhoX ^ 2 = c • V.rhoX - 1 := by
  have h : V.rhoX * (V.rhoX + V.rhoX.conjTranspose) = V.rhoX * (c • 1) := by rw [hc]
  rw [Matrix.mul_add, irrep_rhoX_mul_rhoXt, Matrix.mul_smul, Matrix.mul_one] at h
  rw [pow_two, eq_sub_iff_add_eq]
  exact h

theorem irrep_dim_le_one_of_scalars {N : ℕ} (V : DihedralIrrep N) (μ δ : ℂ)
    (hX : V.rhoX = μ • 1) (hY : V.rhoY = δ • 1) : V.dim ≤ 1 := by
  by_contra h
  have hge : 2 ≤ V.dim := by omega
  letI : NeZero V.dim := ⟨by omega⟩
  have hall : ∀ M : Matrix (Fin V.dim) (Fin V.dim) ℂ, ∃ c : ℂ, M = c • 1 := by
    intro M
    refine V.irreducible M ?_ ?_
    · rw [hX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    · rw [hY, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hi : (0 : Fin V.dim) ≠ 1 := by
    intro hcon
    have hval := congrArg Fin.val hcon
    simp at hval
    omega
  obtain ⟨c, hc⟩ := hall (Matrix.single (0 : Fin V.dim) 1 (1 : ℂ))
  have hentry : (Matrix.single (0 : Fin V.dim) 1 (1 : ℂ) : Matrix (Fin V.dim) (Fin V.dim) ℂ) 0 1 = 1 := by
    simp [Matrix.single]
  have hentry2 : (c • 1 : Matrix (Fin V.dim) (Fin V.dim) ℂ) 0 1 = 0 := by
    simp [hi]
  have hcomp := congrFun (congrFun hc 0) 1
  have contra : (1 : ℂ) = 0 :=
    hentry.symm.trans (hcomp.trans hentry2)
  simp at contra

theorem quad_roots (c : ℂ) :
    ((c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2) + ((c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2) = c ∧
    ((c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2) * ((c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2) = 1 := by
  have hsq : ((c ^ 2 - 4) ^ (2⁻¹ : ℂ)) ^ 2 = c ^ 2 - 4 := Complex.cpow_ofNat_inv_pow _ 2
  constructor
  · ring
  · have h1 : (c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) * (c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) = 4 := by
      have key : (c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) * (c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ))
          = c ^ 2 - ((c ^ 2 - 4) ^ (2⁻¹ : ℂ)) ^ 2 := by ring
      rw [key, hsq]
      ring
    calc ((c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2) * ((c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2)
        = ((c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) * (c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ))) / 4 := by ring
      _ = (4 : ℂ) / 4 := by rw [h1]
      _ = 1 := by norm_num

theorem factor_quadratic {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (c μ ν : ℂ)
    (hsum : μ + ν = c) (hprod : μ * ν = 1) (hsq : X ^ 2 = c • X - 1) :
    (X - μ • 1) * (X - ν • 1) = 0 := by
  have hexp : (X - μ • 1) * (X - ν • 1)
      = X * X - (μ + ν) • X + (μ * ν) • 1 := by
    conv_lhs =>
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, smul_smul]
    module
  rw [hexp, hsum, hprod, show (X * X = X ^ 2) from (pow_two X).symm, hsq, one_smul]
  abel

theorem rhoY_scalar_of_rhoX_scalar {N : ℕ} (V : DihedralIrrep N) (μ : ℂ)
    (hX : V.rhoX = μ • 1) : ∃ δ : ℂ, V.rhoY = δ • 1 := by
  refine V.irreducible V.rhoY ?_ ?_
  · rw [hX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  · rfl

theorem eq_scalar_of_double_root {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ)
    {N : ℕ} [NeZero N] (hXN : X ^ N = 1) (hsq : (X - μ • 1) ^ 2 = 0) :
    ∃ κ : ℂ, X = κ • 1 := by
  classical
  have hsep : (Polynomial.X ^ N - 1 : Polynomial ℂ).Separable :=
    Polynomial.X_pow_sub_one_separable_iff.mpr (NeZero.natCast_ne N ℂ)
  have haeval : Polynomial.aeval (Matrix.toLin' X) (Polynomial.X ^ N - 1 : Polynomial ℂ) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero]
    have := congrArg Matrix.toLin' hXN
    simpa [Matrix.toLin'_pow, Matrix.toLin'_one] using! this
  have hss : Module.End.IsSemisimple (Matrix.toLin' X) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval
  have hform : Matrix.toLin' (X - μ • 1)
      = Matrix.toLin' X - algebraMap ℂ (Module.End ℂ ((Fin d) → ℂ)) μ := by
    rw [map_sub, map_smul, Matrix.toLin'_one, Module.algebraMap_end_eq_smul_id]
  have hnil : IsNilpotent (Matrix.toLin' X -
      algebraMap ℂ (Module.End ℂ ((Fin d) → ℂ)) μ) := by
    rw [← hform]
    refine ⟨2, ?_⟩
    have := congrArg Matrix.toLin' hsq
    simpa [Matrix.toLin'_pow, map_zero] using! this
  have hf0 : (Matrix.toLin' X -
      algebraMap ℂ (Module.End ℂ ((Fin d) → ℂ)) μ) = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hnil
      (by rwa [Module.End.isSemisimple_sub_algebraMap_iff])
  have hf0' : Matrix.toLin' X
      = algebraMap ℂ (Module.End ℂ ((Fin d) → ℂ)) μ := by rwa [sub_eq_zero] at hf0
  have hμ : Matrix.toLin' (μ • 1 : Matrix (Fin d) (Fin d) ℂ)
      = algebraMap ℂ (Module.End ℂ ((Fin d) → ℂ)) μ := by
    rw [map_smul, Matrix.toLin'_one, Module.algebraMap_end_eq_smul_id]
  refine ⟨μ, ?_⟩
  have hcongr := congrArg LinearMap.toMatrix' (hf0'.trans hμ.symm)
  simpa [LinearMap.toMatrix'_toLin'] using! hcongr

theorem irrep_rhoX_scalar_or_dim_two {N : ℕ} [NeZero N] (V : DihedralIrrep N) :
    (∃ κ : ℂ, V.rhoX = κ • 1) ∨ V.dim = 2 := by
  obtain ⟨c, hc⟩ := irrep_sum_conjTranspose V
  have hsq : V.rhoX ^ 2 = c • V.rhoX - 1 := irrep_rhoX_sq V c hc
  set μ : ℂ := (c + (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2 with hμdef
  set ν : ℂ := (c - (c ^ 2 - 4) ^ (2⁻¹ : ℂ)) / 2 with hνdef
  have hsum : μ + ν = c := by rw [hμdef, hνdef]; exact (quad_roots c).1
  have hprod : μ * ν = 1 := by rw [hμdef, hνdef]; exact (quad_roots c).2
  have hfac : (V.rhoX - μ • 1) * (V.rhoX - ν • 1) = 0 :=
    factor_quadratic V.rhoX c μ ν hsum hprod hsq
  by_cases hnot : ∀ κ : ℂ, V.rhoX ≠ κ • 1
  · by_cases hne : μ = ν
    · exfalso
      have hsq2 : (V.rhoX - μ • 1) ^ 2 = 0 := by
        rw [pow_two]
        have h2 : (V.rhoX - μ • 1) * (V.rhoX - μ • 1) = 0 := by
          rw [← hne] at hfac
          exact hfac
        exact h2
      obtain ⟨κ, hκ⟩ := eq_scalar_of_double_root V.rhoX μ V.orderX hsq2
      exact hnot κ hκ
    · exact Or.inr (aux_dim_two V μ ν hprod hne hfac hnot)
  · simp only [not_forall, not_ne_iff] at hnot
    exact Or.inl hnot

theorem irrep_dim_le_two {N : ℕ} [NeZero N] (V : DihedralIrrep N) : V.dim ≤ 2 := by
  rcases irrep_rhoX_scalar_or_dim_two V with h | h
  · obtain ⟨δ, hδ⟩ := rhoY_scalar_of_rhoX_scalar V _ h.choose_spec
    have := irrep_dim_le_one_of_scalars V _ δ h.choose_spec hδ
    omega
  · omega

theorem irrep_dim_cases {N : ℕ} [NeZero N] (V : DihedralIrrep N) :
    V.dim = 0 ∨ V.dim = 1 ∨ V.dim = 2 := by
  have h := irrep_dim_le_two V
  interval_cases V.dim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
open scoped Classical
open Matrix
open scoped ComplexConjugate

theorem matrix_eq_smul_one_of_dim_one {d : ℕ} (hd : d = 1) (M : Matrix (Fin d) (Fin d) ℂ) :
    M = (Matrix.trace M) • 1 := by
  subst hd
  ext i j
  have hi := Fin.fin_one_eq_zero i
  have hj := Fin.fin_one_eq_zero j
  subst hi
  subst hj
  rw [Matrix.trace_fin_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]

theorem smul_one_pow {d : ℕ} (a : ℂ) (k : ℕ) :
    ((a • (1 : Matrix (Fin d) (Fin d) ℂ)) ^ k) = a ^ k • 1 := by
  rw [smul_pow, one_pow]

theorem trace_smul_one {d : ℕ} (a : ℂ) :
    Matrix.trace (a • (1 : Matrix (Fin d) (Fin d) ℂ)) = a * (d : ℂ) := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]

theorem trace_smul_one_cancel {d : ℕ} (hd : d ≠ 0) {a b : ℂ}
    (h : Matrix.trace (a • (1 : Matrix (Fin d) (Fin d) ℂ))
        = Matrix.trace (b • (1 : Matrix (Fin d) (Fin d) ℂ))) : a = b := by
  rw [trace_smul_one, trace_smul_one] at h
  have hne : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  exact mul_right_cancel₀ hne h

theorem trace_smul_one_eq_one_cancel {d : ℕ} (hd : d ≠ 0) {a : ℂ}
    (h : Matrix.trace (a • (1 : Matrix (Fin d) (Fin d) ℂ))
        = Matrix.trace (1 : Matrix (Fin d) (Fin d) ℂ)) : a = 1 := by
  refine trace_smul_one_cancel hd ?_
  rw [one_smul]
  exact h

theorem normSq_pow (z : ℂ) (k : ℕ) : Complex.normSq (z ^ k) = Complex.normSq z ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Complex.normSq_mul, ih]

theorem irrep_one_dim_data {N : ℕ} [NeZero N] (V : DihedralIrrep N) (hd : V.dim = 1) :
    ∃ ε δ : ℂ, V.rhoX = ε • 1 ∧ V.rhoY = δ • 1 ∧
      Matrix.trace V.rhoX = ε ∧ Matrix.trace V.rhoY = δ ∧
      (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧ ε ^ N = 1 := by
  set ε : ℂ := Matrix.trace V.rhoX with hεdef
  set δ : ℂ := Matrix.trace V.rhoY with hδdef
  have hX : V.rhoX = ε • 1 := by rw [hεdef]; exact matrix_eq_smul_one_of_dim_one hd V.rhoX
  have hY : V.rhoY = δ • 1 := by rw [hδdef]; exact matrix_eq_smul_one_of_dim_one hd V.rhoY
  have htrX : Matrix.trace V.rhoX = ε := by rw [hεdef]
  have htrY : Matrix.trace V.rhoY = δ := by rw [hδdef]
  have hdne : V.dim ≠ 0 := by omega
  have hy2 : V.rhoY * V.rhoY = 1 := by have h := V.orderY; rwa [pow_two] at h
  have hδ2 : δ * δ = 1 := by
    have hprod : V.rhoY * V.rhoY = (δ * δ) • 1 := by
      simp only [hY, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    have htr := congrArg Matrix.trace (hprod.symm.trans hy2)
    exact trace_smul_one_eq_one_cancel hdne htr
  have hδ : δ = 1 ∨ δ = -1 := mul_self_eq_one_iff.mp hδ2
  have hεconj : ε = conj ε := by
    have e1 : V.rhoY * V.rhoX = (δ * ε) • 1 := by
      simp only [hY, hX, Matrix.mul_smul, Matrix.mul_one, smul_smul]
      rw [mul_comm]
    have e2 : (δ * ε) • 1 * V.rhoY = ((δ * ε) * δ) • 1 := by
      simp only [hY, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    have hL : V.rhoY * V.rhoX * V.rhoY = ((δ * ε) * δ) • 1 := by rw [e1, e2]
    have hR : V.rhoX.conjTranspose = conj ε • 1 := by
      rw [hX, conjTranspose_smul, conjTranspose_one, starRingEnd_apply]
    have hrel : ((δ * ε) * δ) • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)
        = conj ε • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ) := by
      have := V.relation
      rw [hL, hR] at this
      exact this
    have h3 : (δ * ε) * δ = conj ε := trace_smul_one_cancel hdne (congrArg Matrix.trace hrel)
    have h4 : δ * δ * ε = conj ε := by
      calc δ * δ * ε = (δ * ε) * δ := by ring
        _ = conj ε := h3
    rw [hδ2, one_mul] at h4
    exact h4
  have hεN : ε ^ N = 1 := by
    have hpow : V.rhoX ^ N = ε ^ N • 1 := by rw [hX, smul_one_pow]
    have h := congrArg Matrix.trace (hpow.symm.trans V.orderX)
    exact trace_smul_one_eq_one_cancel hdne h
  have hε : ε = 1 ∨ ε = -1 := by
    have h1 : Complex.normSq (ε ^ N) = 1 := by rw [hεN, Complex.normSq_one]
    have h2 : Complex.normSq ε ^ N = 1 := (normSq_pow ε N).symm.trans h1
    have h3 : Complex.normSq ε = 1 :=
      pow_left_inj₀ (Complex.normSq_nonneg ε) (by norm_num : (0:ℝ) ≤ 1)
        (NeZero.ne N) |>.mp (h2.trans (one_pow N).symm)
    have h5 : (Complex.normSq ε : ℂ) = 1 := by rw [h3]; norm_num
    have h6 : conj ε * ε = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      exact h5
    have h7 : ε * ε = 1 := by
      rw [← hεconj] at h6
      exact h6
    exact mul_self_eq_one_iff.mp h7
  exact ⟨ε, δ, hX, hY, htrX, htrY, hε, hδ, hεN⟩

theorem one_or_neg_one_pow {k : ℕ} {z : ℂ} (hz : z = 1 ∨ z = -1) :
    z ^ k = 1 ∨ z ^ k = -1 := by
  rcases hz with h | h
  · rw [h]; exact Or.inl (one_pow k)
  · rw [h]
    induction k with
    | zero => exact Or.inl (one_pow 0)
    | succ k ih =>
      rw [pow_succ]
      rcases ih with ih | ih
      · rw [ih, one_mul]; exact Or.inr rfl
      · rw [ih]; exact Or.inl (neg_mul_neg 1 1 |>.trans (one_mul 1))

theorem mul_one_or_neg_one {a b : ℂ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inl (by norm_num)

theorem irrep_one_dim_dimFixed {N : ℕ} [NeZero N] (V : DihedralIrrep N) (hd : V.dim = 1)
    (s : ZMod N) : dimFixed V s =
      if Matrix.trace V.rhoY * (Matrix.trace V.rhoX) ^ s.val = 1 then 1 else 0 := by
  classical
  obtain ⟨ε, δ, hX, hY, htrX, htrY, hε, hδ, _⟩ := irrep_one_dim_data V hd
  have hpow : V.rhoX ^ s.val = ε ^ s.val • 1 := by rw [hX, smul_one_pow]
  have hR : reflectionElem V s = (δ * ε ^ s.val) • 1 := by
    simp only [reflectionElem, hY, hpow, Matrix.mul_smul, Matrix.mul_one]
    rw [smul_smul, mul_comm]
  have hRtr : Matrix.trace (reflectionElem V s) = δ * ε ^ s.val := by
    rw [hR, trace_smul_one, show (V.dim : ℂ) = 1 by exact_mod_cast hd, mul_one]
  have hexp : (dimFixed V s : ℂ) = ((V.dim : ℂ) + Matrix.trace (reflectionElem V s)) / 2 :=
    irrep_dimFixed_eq_trace V s
  rw [hRtr] at hexp
  rw [show (V.dim : ℂ) = 1 by exact_mod_cast hd] at hexp
  have hpm : δ * ε ^ s.val = 1 ∨ δ * ε ^ s.val = -1 :=
    mul_one_or_neg_one hδ (one_or_neg_one_pow hε)
  rw [htrX, htrY]
  by_cases hcond : δ * ε ^ s.val = 1
  · rw [if_pos hcond]
    have : ((dimFixed V s : ℂ)) = 1 := by rw [hexp, hcond]; norm_num
    exact_mod_cast this
  · rw [if_neg hcond]
    have hneg : δ * ε ^ s.val = -1 := by
      rcases hpm with h | h
      · exact absurd h hcond
      · exact h
    have : ((dimFixed V s : ℂ)) = 0 := by rw [hexp, hneg]; norm_num
    exact_mod_cast this

theorem trace_zero_or_eq_pm_one {d : ℕ} (hd : d = 2) (R : Matrix (Fin d) (Fin d) ℂ)
    (h : R * R = 1) : Matrix.trace R = 0 ∨ R = 1 ∨ R = -1 := by
  classical
  subst hd
  rw [Matrix.trace_fin_two]
  by_cases htr : R 0 0 + R 1 1 = 0
  · exact Or.inl htr
  · right
    have h01 : R 0 1 * (R 0 0 + R 1 1) = 0 := by
      have hh : (R * R) 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by rw [h]
      rw [Matrix.mul_apply] at hh
      simp only [Matrix.one_apply, if_neg (by decide : (0:Fin 2) ≠ 1), Fin.sum_univ_two] at hh
      have key : R 0 0 * R 0 1 + R 0 1 * R 1 1 = R 0 1 * (R 0 0 + R 1 1) := by ring
      rw [← key, hh]
    have h10 : R 1 0 * (R 0 0 + R 1 1) = 0 := by
      have hh : (R * R) 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by rw [h]
      rw [Matrix.mul_apply] at hh
      simp only [Matrix.one_apply, if_neg (by decide : (1:Fin 2) ≠ 0), Fin.sum_univ_two] at hh
      have key : R 1 0 * R 0 0 + R 1 1 * R 1 0 = R 1 0 * (R 0 0 + R 1 1) := by ring
      rw [← key, hh]
    have hb : R 0 1 = 0 := by
      rcases mul_eq_zero.mp h01 with h | h
      · exact h
      · exact absurd h htr
    have hc : R 1 0 = 0 := by
      rcases mul_eq_zero.mp h10 with h | h
      · exact h
      · exact absurd h htr
    have h00 : R 0 0 * R 0 0 = 1 := by
      have hh : (R * R) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
      rw [Matrix.mul_apply] at hh
      simp only [Matrix.one_apply, Fin.sum_univ_two, hb, hc] at hh
      rw [mul_zero, add_zero] at hh
      exact hh
    have h11 : R 1 1 * R 1 1 = 1 := by
      have hh : (R * R) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by rw [h]
      rw [Matrix.mul_apply] at hh
      simp only [Matrix.one_apply, Fin.sum_univ_two, hb, hc] at hh
      rw [mul_zero, zero_add] at hh
      exact hh
    have hs0 : R 0 0 = 1 ∨ R 0 0 = -1 := mul_self_eq_one_iff.mp h00
    have hs1 : R 1 1 = 1 ∨ R 1 1 = -1 := mul_self_eq_one_iff.mp h11
    have hsame : R 0 0 = R 1 1 := by
      rcases hs0 with h0 | h0 <;> rcases hs1 with h1 | h1
      · rw [h0, h1]
      · exfalso; rw [h0, h1] at htr; simp at htr
      · exfalso; rw [h0, h1] at htr; simp at htr
      · rw [h0, h1]
    have hmat : R = (R 0 0) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, hb, hc, hsame]
    rcases hs0 with h0 | h0
    · rw [hmat, h0, one_smul]; exact Or.inl rfl
    · rw [hmat, h0, neg_one_smul]; exact Or.inr rfl

theorem irrep_reflection_ne_pm_one_of_dim_two {N : ℕ} [NeZero N] (V : DihedralIrrep N)
    (hd : V.dim = 2) (s : ZMod N) (ε : ℂ) (hr : reflectionElem V s = ε • 1) : False := by
  classical
  have hdne : V.dim ≠ 0 := by omega
  have hR2 : reflectionElem V s * reflectionElem V s = 1 := irrep_reflection_sq s
  have hε2 : ε * ε = 1 := by
    have hprod : reflectionElem V s * reflectionElem V s = (ε * ε) • 1 := by
      simp only [hr, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    have htr := congrArg Matrix.trace (hprod.symm.trans hR2)
    exact trace_smul_one_eq_one_cancel hdne htr
  have hε : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp hε2
  have hre : V.rhoY * V.rhoX ^ s.val = ε • 1 := hr
  have hk : V.rhoX ^ s.val = ε • V.rhoY := by
    have happly : V.rhoY * (V.rhoY * V.rhoX ^ s.val)
        = V.rhoY * (ε • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)) := by rw [hre]
    have h3 : V.rhoY * (ε • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)) = ε • V.rhoY := by
      rw [Matrix.mul_smul, Matrix.mul_one]
    have h2 : V.rhoY * (V.rhoY * V.rhoX ^ s.val) = V.rhoX ^ s.val := by
      rw [← mul_assoc, irrep_rhoY_sq, one_mul]
    rw [h3, h2] at happly
    exact happly
  have hy : V.rhoY = ε • V.rhoX ^ s.val := by
    have h := congrArg (fun M : Matrix (Fin V.dim) (Fin V.dim) ℂ => ε • M) hk
    simp only [smul_smul] at h
    rw [hε2, one_smul] at h
    exact h.symm
  have hcomm : V.rhoY * V.rhoX = V.rhoX * V.rhoY := by
    rw [hy]
    calc ε • V.rhoX ^ s.val * V.rhoX = ε • (V.rhoX ^ s.val * V.rhoX) := by
          rw [Matrix.smul_mul]
      _ = ε • (V.rhoX * V.rhoX ^ s.val) := by rw [← pow_succ, ← pow_succ']
      _ = V.rhoX * (ε • V.rhoX ^ s.val) := by rw [Matrix.mul_smul]
  have hXXt : V.rhoX = V.rhoX.conjTranspose := by
    have h := irrep_rhoY_mul_rhoX (V := V)
    rw [hcomm] at h
    have hsub : (V.rhoX - V.rhoX.conjTranspose) * V.rhoY = 0 := by
      rw [Matrix.sub_mul, h, sub_self]
    have hsub2 : (V.rhoX - V.rhoX.conjTranspose) * (V.rhoY * V.rhoY) = 0 := by
      rw [← mul_assoc, hsub, zero_mul]
    rw [irrep_rhoY_sq, mul_one] at hsub2
    exact sub_eq_zero.mp hsub2
  obtain ⟨c, hc⟩ := irrep_sum_conjTranspose V
  have hsc : V.rhoX = ((2:ℂ)⁻¹ * c) • 1 := by
    have hc2 : V.rhoX + V.rhoX = c • 1 := by
      rw [← hXXt] at hc
      exact hc
    have hc3 : (2:ℂ) • V.rhoX = c • 1 := by
      rw [two_smul]
      exact hc2
    have := congrArg (fun M : Matrix (Fin V.dim) (Fin V.dim) ℂ => (2:ℂ)⁻¹ • M) hc3
    simp only [smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_smul] at this
    exact this
  have hysc : V.rhoY = (ε * (((2:ℂ)⁻¹ * c) ^ s.val)) • 1 := by
    rw [hy, hsc, smul_one_pow, smul_smul]
  have hle := irrep_dim_le_one_of_scalars V _ _ hsc hysc
  omega

theorem irrep_two_dim_dimFixed {N : ℕ} [NeZero N] (V : DihedralIrrep N) (hd : V.dim = 2)
    (s : ZMod N) : dimFixed V s = 1 := by
  classical
  have hR2 : reflectionElem V s * reflectionElem V s = 1 := irrep_reflection_sq s
  have hcase := trace_zero_or_eq_pm_one hd (reflectionElem V s) hR2
  have htr : Matrix.trace (reflectionElem V s) = 0 := by
    rcases hcase with h | h | h
    · exact h
    · exact (irrep_reflection_ne_pm_one_of_dim_two V hd s 1 (by rw [h, one_smul])).elim
    · exact (irrep_reflection_ne_pm_one_of_dim_two V hd s (-1) (by rw [h, neg_one_smul])).elim
  have hexp : (dimFixed V s : ℂ) = ((V.dim : ℂ) + Matrix.trace (reflectionElem V s)) / 2 :=
    irrep_dimFixed_eq_trace V s
  rw [htr] at hexp
  rw [show (V.dim : ℂ) = 2 by exact_mod_cast hd] at hexp
  have : ((dimFixed V s : ℂ)) = 1 := by rw [hexp]; norm_num
  exact_mod_cast this

theorem neg_one_pow_odd_eq {n : ℕ} (h : n % 2 = 1) : (-1 : ℂ) ^ n = -1 := by
  have hk : n = 2 * ((n - 1) / 2) + 1 := by omega
  rw [hk, pow_succ, pow_mul, show ((-1 : ℂ) ^ 2) = 1 by norm_num, one_pow, one_mul]

theorem irrep_one_dim_pair_injective {N : ℕ} [NeZero N] {Label : Type} [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (l₁ l₂ : Label)
    (hd₁ : (family.irrep l₁).dim = 1) (hd₂ : (family.irrep l₂).dim = 1)
    (hε : Matrix.trace (family.irrep l₁).rhoX = Matrix.trace (family.irrep l₂).rhoX)
    (hδ : Matrix.trace (family.irrep l₁).rhoY = Matrix.trace (family.irrep l₂).rhoY) :
    l₁ = l₂ := by
  classical
  by_contra hne
  obtain ⟨ε₁, δ₁, hX₁, hY₁, htrX₁, htrY₁, _, _, _⟩ := irrep_one_dim_data (family.irrep l₁) hd₁
  obtain ⟨ε₂, δ₂, hX₂, hY₂, htrX₂, htrY₂, _, _, _⟩ := irrep_one_dim_data (family.irrep l₂) hd₂
  have hεe : ε₁ = ε₂ := htrX₁.symm.trans (hε.trans htrX₂)
  have hδe : δ₁ = δ₂ := htrY₁.symm.trans (hδ.trans htrY₂)
  set M : Matrix (Fin (family.irrep l₁).dim) (Fin (family.irrep l₂).dim) ℂ :=
    Matrix.single ⟨0, by omega⟩ ⟨0, by omega⟩ (1 : ℂ) with hMdef
  have hMeq : M ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    rw [hMdef]
    simp [Matrix.single]
  have hM : M ≠ 0 := by
    intro h0
    rw [h0] at hMeq
    simp at hMeq
  have hMX : M * (family.irrep l₂).rhoX = (family.irrep l₁).rhoX * M := by
    rw [hX₂, hX₁, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, hεe]
  have hMY : M * (family.irrep l₂).rhoY = (family.irrep l₁).rhoY * M := by
    rw [hY₂, hY₁, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, hδe]
  exact hM (family.inequivalent l₁ l₂ hne M hMX hMY)

theorem dimFixed_half_count (N : ℕ) [NeZero N] (Label : Type) [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N)
    (hdim : (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1)).card
        + 4 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 2)).card = 2 * N) :
    2 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1 ∧
        Matrix.trace (family.irrep l).rhoY * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)).card
      = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1)).card := by
  classical
  set L1 : Finset Label := Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1) with hL1def
  set G : Finset Label := Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1 ∧
    Matrix.trace (family.irrep l).rhoY * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)
    with hGdef
  have hmem : ∀ l : Label, l ∈ L1 ↔ (family.irrep l).dim = 1 := by
    intro l
    rw [hL1def]
    simp [Finset.mem_filter]
  have hmemG : ∀ l : Label, l ∈ G ↔ ((family.irrep l).dim = 1 ∧
      Matrix.trace (family.irrep l).rhoY * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1) := by
    intro l
    rw [hGdef]
    simp [Finset.mem_filter]
  have hbits : ∀ l : Label, (family.irrep l).dim = 1 →
      ((if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = true ↔
        Matrix.trace (family.irrep l).rhoX = 1) ∧
      ((if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = false ↔
        Matrix.trace (family.irrep l).rhoX = -1) ∧
      ((if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = true ↔
        Matrix.trace (family.irrep l).rhoY = 1) ∧
      ((if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = false ↔
        Matrix.trace (family.irrep l).rhoY = -1) := by
    intro l hl
    obtain ⟨ε, δ, hX, hY, htrX, htrY, hε, hδ, _⟩ := irrep_one_dim_data (family.irrep l) hl
    have hep1 : ((if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = true ↔
        Matrix.trace (family.irrep l).rhoX = 1) := by
      by_cases hc : Matrix.trace (family.irrep l).rhoX = 1
      · rw [if_pos hc]; simp [hc]
      · rw [if_neg hc]; simp [hc]
    have hep2 : ((if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = false ↔
        Matrix.trace (family.irrep l).rhoX = -1) := by
      rw [htrX]
      rcases hε with h | h
      · rw [h, if_pos (rfl : (1 : ℂ) = 1)]
        norm_num
      · rw [h, if_neg (by norm_num : ¬((-1 : ℂ) = 1))]
        norm_num
    have hdp1 : ((if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = true ↔
        Matrix.trace (family.irrep l).rhoY = 1) := by
      by_cases hc : Matrix.trace (family.irrep l).rhoY = 1
      · rw [if_pos hc]; simp [hc]
      · rw [if_neg hc]; simp [hc]
    have hdp2 : ((if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = false ↔
        Matrix.trace (family.irrep l).rhoY = -1) := by
      rw [htrY]
      rcases hδ with h | h
      · rw [h, if_pos (rfl : (1 : ℂ) = 1)]
        norm_num
      · rw [h, if_neg (by norm_num : ¬((-1 : ℂ) = 1))]
        norm_num
    exact ⟨hep1, hep2, hdp1, hdp2⟩
  have hinj : ∀ l ∈ L1, ∀ l' ∈ L1,
      (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
        if Matrix.trace (family.irrep l).rhoY = 1 then true else false)
      = (if Matrix.trace (family.irrep l').rhoX = 1 then true else false,
        if Matrix.trace (family.irrep l').rhoY = 1 then true else false) → l = l' := by
    intro l hl l' hl' hpb
    have hl1 : (family.irrep l).dim = 1 := (hmem l).mp hl
    have hl2 : (family.irrep l').dim = 1 := (hmem l').mp hl'
    obtain ⟨hep, hepf, hdp, hdpf⟩ := hbits l hl1
    obtain ⟨hep', hepf', hdp', hdpf'⟩ := hbits l' hl2
    have hb1 : (if Matrix.trace (family.irrep l).rhoX = 1 then true else false)
        = (if Matrix.trace (family.irrep l').rhoX = 1 then true else false) :=
      congrArg Prod.fst hpb
    have hb2 : (if Matrix.trace (family.irrep l).rhoY = 1 then true else false)
        = (if Matrix.trace (family.irrep l').rhoY = 1 then true else false) :=
      congrArg Prod.snd hpb
    have hε : Matrix.trace (family.irrep l).rhoX = Matrix.trace (family.irrep l').rhoX := by
      by_cases hc : (if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = true
      · rw [hep.mp hc, hep'.mp (by rw [← hb1]; exact hc)]
      · have hcf : (if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = false :=
          Bool.eq_false_of_not_eq_true hc
        rw [hepf.mp hcf, hepf'.mp (by rw [← hb1]; exact hcf)]
    have hδ : Matrix.trace (family.irrep l).rhoY = Matrix.trace (family.irrep l').rhoY := by
      by_cases hc : (if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = true
      · rw [hdp.mp hc, hdp'.mp (by rw [← hb2]; exact hc)]
      · have hcf : (if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = false :=
          Bool.eq_false_of_not_eq_true hc
        rw [hdpf.mp hcf, hdpf'.mp (by rw [← hb2]; exact hcf)]
    exact irrep_one_dim_pair_injective family l l' hl1 hl2 hε hδ
  have hL1le4 : L1.card ≤ 4 := by
    have hinj' : Set.InjOn
        (fun l : Label =>
          (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
            if Matrix.trace (family.irrep l).rhoY = 1 then true else false)) ↑L1 :=
      fun l hl l' hl' h => hinj l hl l' hl' h
    have hcard := Finset.card_image_of_injOn hinj'
    have hle := Finset.card_le_univ
      (L1.image (fun l : Label =>
        (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
          if Matrix.trace (family.irrep l).rhoY = 1 then true else false)))
    rw [Fintype.card_prod, Fintype.card_bool] at hle
    omega
  have hL1mod : L1.card % 4 = (2 * N) % 4 := by omega
  have hGB : G.card + (L1.filter (fun l : Label =>
      ¬(Matrix.trace (family.irrep l).rhoY
        * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1))).card = L1.card := by
    have h1 : G = L1.filter (fun l : Label =>
        Matrix.trace (family.irrep l).rhoY * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1) := by
      rw [hGdef, hL1def]
      exact (Finset.filter_filter (fun l : Label => (family.irrep l).dim = 1)
        (fun l : Label => Matrix.trace (family.irrep l).rhoY
          * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1) Finset.univ).symm
    rw [h1]
    exact Finset.card_filter_add_card_filter_not
      (fun l : Label => Matrix.trace (family.irrep l).rhoY
        * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)
  by_cases hNmod : N % 2 = 0
  · have hL1 : L1.card = 0 ∨ L1.card = 4 := by omega
    rcases hL1 with h0 | h4
    · have hsub : G ⊆ L1 := by
        intro x hx
        exact (hmem x).mpr ((hmemG x).mp hx |>.1)
      have hG0 : G.card = 0 := by
        have := Finset.card_le_card hsub
        omega
      rw [hG0, h0]
    · have him : L1.image (fun l : Label =>
          (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
            if Matrix.trace (family.irrep l).rhoY = 1 then true else false))
          = (Finset.univ : Finset (Bool × Bool)) := by
        refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
        have hinj' : Set.InjOn
            (fun l : Label =>
              (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
                if Matrix.trace (family.irrep l).rhoY = 1 then true else false)) ↑L1 :=
          fun l hl l' hl' h => hinj l hl l' hl' h
        rw [Finset.card_image_of_injOn hinj', h4, Finset.card_univ, Fintype.card_prod,
          Fintype.card_bool]
      have hexb : ∀ x : Bool × Bool, ∃ l ∈ L1,
          (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
            if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = x := by
        intro x
        have hx : x ∈ L1.image (fun l : Label =>
            (if Matrix.trace (family.irrep l).rhoX = 1 then true else false,
              if Matrix.trace (family.irrep l).rhoY = 1 then true else false)) := by
          rw [him]; simp
        exact Finset.mem_image.mp hx
      obtain ⟨ltt, hltt, hpbltt⟩ := hexb (true, true)
      obtain ⟨ltf, hltf, hpbltf⟩ := hexb (true, false)
      obtain ⟨lft, hlft, hpblft⟩ := hexb (false, true)
      obtain ⟨lff, hlff, hpblff⟩ := hexb (false, false)
      have hltt1 : (family.irrep ltt).dim = 1 := (hmem ltt).mp hltt
      have hltf1 : (family.irrep ltf).dim = 1 := (hmem ltf).mp hltf
      have hlft1 : (family.irrep lft).dim = 1 := (hmem lft).mp hlft
      have hlff1 : (family.irrep lff).dim = 1 := (hmem lff).mp hlff
      have htt : Matrix.trace (family.irrep ltt).rhoX = 1 ∧
          Matrix.trace (family.irrep ltt).rhoY = 1 := by
        exact ⟨(hbits ltt hltt1).1.mp (congrArg Prod.fst hpbltt),
          (hbits ltt hltt1).2.2.1.mp (congrArg Prod.snd hpbltt)⟩
      have htf : Matrix.trace (family.irrep ltf).rhoX = 1 ∧
          Matrix.trace (family.irrep ltf).rhoY = -1 := by
        exact ⟨(hbits ltf hltf1).1.mp (congrArg Prod.fst hpbltf),
          (hbits ltf hltf1).2.2.2.mp (congrArg Prod.snd hpbltf)⟩
      have hft : Matrix.trace (family.irrep lft).rhoX = -1 ∧
          Matrix.trace (family.irrep lft).rhoY = 1 := by
        exact ⟨(hbits lft hlft1).2.1.mp (congrArg Prod.fst hpblft),
          (hbits lft hlft1).2.2.1.mp (congrArg Prod.snd hpblft)⟩
      have hff : Matrix.trace (family.irrep lff).rhoX = -1 ∧
          Matrix.trace (family.irrep lff).rhoY = -1 := by
        exact ⟨(hbits lff hlff1).2.1.mp (congrArg Prod.fst hpblff),
          (hbits lff hlff1).2.2.2.mp (congrArg Prod.snd hpblff)⟩
      have hne_ttft : ltt ≠ lft := by
        intro h; subst h; rw [hpbltt] at hpblft; simp at hpblft
      have hne_ttff : ltt ≠ lff := by
        intro h; subst h; rw [hpbltt] at hpblff; simp at hpblff
      have hne_tflt : ltf ≠ lft := by
        intro h; subst h; rw [hpbltf] at hpblft; simp at hpblft
      have hne_tflf : ltf ≠ lff := by
        intro h; subst h; rw [hpbltf] at hpblff; simp at hpblff
      have hcondtt : Matrix.trace (family.irrep ltt).rhoY
          * (Matrix.trace (family.irrep ltt).rhoX) ^ s.val = 1 := by
        rw [htt.2, htt.1, one_mul, one_pow]
      have hcondtf : ¬(Matrix.trace (family.irrep ltf).rhoY
          * (Matrix.trace (family.irrep ltf).rhoX) ^ s.val = 1) := by
        rw [htf.2, htf.1, one_pow, mul_one]
        norm_num
      have hcondft_iff : (Matrix.trace (family.irrep lft).rhoY
            * (Matrix.trace (family.irrep lft).rhoX) ^ s.val = 1) ↔ (-1 : ℂ) ^ s.val = 1 := by
        rw [hft.2, hft.1, one_mul]
      have hcondff_iff : (Matrix.trace (family.irrep lff).rhoY
            * (Matrix.trace (family.irrep lff).rhoX) ^ s.val = 1) ↔ (-1 : ℂ) ^ s.val = -1 := by
        rw [hff.2, hff.1]
        constructor
        · intro h
          have key : (-1 : ℂ) * (-1) ^ s.val = (-1) * (-1) := by rw [h]; ring
          exact mul_left_cancel₀ (by norm_num : (-1 : ℂ) ≠ 0) key
        · intro h
          rw [h]
          ring
      have hpm : (-1 : ℂ) ^ s.val = 1 ∨ (-1 : ℂ) ^ s.val = -1 :=
        one_or_neg_one_pow (Or.inr rfl)
      have hG2 : 1 < G.card := by
        have hlG : ltt ∈ G := (hmemG ltt).mpr ⟨hltt1, hcondtt⟩
        rcases hpm with hp | hp
        · have hcond : Matrix.trace (family.irrep lft).rhoY
              * (Matrix.trace (family.irrep lft).rhoX) ^ s.val = 1 := hcondft_iff.mpr hp
          have hl2 : lft ∈ G := (hmemG lft).mpr ⟨hlft1, hcond⟩
          rw [Finset.one_lt_card]
          exact ⟨ltt, hlG, lft, hl2, hne_ttft⟩
        · have hcond : Matrix.trace (family.irrep lff).rhoY
              * (Matrix.trace (family.irrep lff).rhoX) ^ s.val = 1 := hcondff_iff.mpr hp
          have hl2 : lff ∈ G := (hmemG lff).mpr ⟨hlff1, hcond⟩
          rw [Finset.one_lt_card]
          exact ⟨ltt, hlG, lff, hl2, hne_ttff⟩
      have hB2 : 1 < (L1.filter (fun l : Label =>
          ¬(Matrix.trace (family.irrep l).rhoY
            * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1))).card := by
        have hlB : ltf ∈ L1.filter (fun l : Label =>
            ¬(Matrix.trace (family.irrep l).rhoY
              * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)) :=
          Finset.mem_filter.mpr ⟨hltf, hcondtf⟩
        rcases hpm with hp | hp
        · have hn : ¬(Matrix.trace (family.irrep lff).rhoY
              * (Matrix.trace (family.irrep lff).rhoX) ^ s.val = 1) := by
            intro hc
            have h1 : (-1 : ℂ) ^ s.val = -1 := hcondff_iff.mp hc
            rw [hp] at h1
            norm_num at h1
          have hl2 : lff ∈ L1.filter (fun l : Label =>
              ¬(Matrix.trace (family.irrep l).rhoY
                * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)) :=
            Finset.mem_filter.mpr ⟨hlff, hn⟩
          rw [Finset.one_lt_card]
          exact ⟨ltf, hlB, lff, hl2, hne_tflf⟩
        · have hn : ¬(Matrix.trace (family.irrep lft).rhoY
              * (Matrix.trace (family.irrep lft).rhoX) ^ s.val = 1) := by
            intro hc
            have h1 : (-1 : ℂ) ^ s.val = 1 := hcondft_iff.mp hc
            rw [hp] at h1
            norm_num at h1
          have hl2 : lft ∈ L1.filter (fun l : Label =>
              ¬(Matrix.trace (family.irrep l).rhoY
                * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)) :=
            Finset.mem_filter.mpr ⟨hlft, hn⟩
          rw [Finset.one_lt_card]
          exact ⟨ltf, hlB, lft, hl2, hne_tflt⟩
      have hGcard : G.card = 2 := by omega
      rw [hGcard, h4]
  · have hNodd : N % 2 = 1 := by omega
    have hε1 : ∀ l ∈ L1, Matrix.trace (family.irrep l).rhoX = 1 := by
      intro l hl
      have hl1 : (family.irrep l).dim = 1 := (hmem l).mp hl
      obtain ⟨ε, δ, hX, hY, htrX, htrY, hε, hδ, hεN⟩ := irrep_one_dim_data (family.irrep l) hl1
      rw [htrX]
      rcases hε with h | h
      · exact h
      · exfalso
        rw [h] at hεN
        rw [neg_one_pow_odd_eq hNodd] at hεN
        norm_num at hεN
    have hinjD : ∀ l ∈ L1, ∀ l' ∈ L1,
        (if Matrix.trace (family.irrep l).rhoY = 1 then true else false)
        = (if Matrix.trace (family.irrep l').rhoY = 1 then true else false) → l = l' := by
      intro l hl l' hl' hd
      have hl1 : (family.irrep l).dim = 1 := (hmem l).mp hl
      have hl2 : (family.irrep l').dim = 1 := (hmem l').mp hl'
      have he : (if Matrix.trace (family.irrep l).rhoX = 1 then true else false)
          = (if Matrix.trace (family.irrep l').rhoX = 1 then true else false) := by
        have h1 : (if Matrix.trace (family.irrep l).rhoX = 1 then true else false) = true :=
          (hbits l hl1).1.mpr (hε1 l hl)
        have h2 : (if Matrix.trace (family.irrep l').rhoX = 1 then true else false) = true :=
          (hbits l' hl2).1.mpr (hε1 l' hl')
        rw [h1, h2]
      exact hinj l hl l' hl' (by rw [he, hd])
    have hL1le2 : L1.card ≤ 2 := by
      have hinj' : Set.InjOn
          (fun l : Label => if Matrix.trace (family.irrep l).rhoY = 1 then true else false) ↑L1 :=
        fun l hl l' hl' h => hinjD l hl l' hl' h
      have hcard := Finset.card_image_of_injOn hinj'
      have hle := Finset.card_le_univ
        (L1.image (fun l : Label => if Matrix.trace (family.irrep l).rhoY = 1 then true else false))
      rw [Fintype.card_bool] at hle
      omega
    have hL1card : L1.card = 2 := by omega
    have him : L1.image (fun l : Label =>
        if Matrix.trace (family.irrep l).rhoY = 1 then true else false)
        = (Finset.univ : Finset Bool) := by
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
      have hinj' : Set.InjOn
          (fun l : Label => if Matrix.trace (family.irrep l).rhoY = 1 then true else false) ↑L1 :=
        fun l hl l' hl' h => hinjD l hl l' hl' h
      rw [Finset.card_image_of_injOn hinj', hL1card, Finset.card_univ, Fintype.card_bool]
    have hexT : ∃ l ∈ L1, (if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = true := by
      have hx : true ∈ L1.image
          (fun l : Label => if Matrix.trace (family.irrep l).rhoY = 1 then true else false) := by
        rw [him]; simp
      exact Finset.mem_image.mp hx
    have hexF : ∃ l ∈ L1,
        (if Matrix.trace (family.irrep l).rhoY = 1 then true else false) = false := by
      have hx : false ∈ L1.image
          (fun l : Label => if Matrix.trace (family.irrep l).rhoY = 1 then true else false) := by
        rw [him]; simp
      exact Finset.mem_image.mp hx
    obtain ⟨lg, hlg, hblg⟩ := hexT
    obtain ⟨lb, hlb, hblb⟩ := hexF
    have hlg1 : (family.irrep lg).dim = 1 := (hmem lg).mp hlg
    have hlb1 : (family.irrep lb).dim = 1 := (hmem lb).mp hlb
    have hcondg : Matrix.trace (family.irrep lg).rhoY
        * (Matrix.trace (family.irrep lg).rhoX) ^ s.val = 1 := by
      have hd : Matrix.trace (family.irrep lg).rhoY = 1 := (hbits lg hlg1).2.2.1.mp hblg
      have he : Matrix.trace (family.irrep lg).rhoX = 1 := hε1 lg hlg
      rw [hd, he, one_mul, one_pow]
    have hcondb : ¬(Matrix.trace (family.irrep lb).rhoY
        * (Matrix.trace (family.irrep lb).rhoX) ^ s.val = 1) := by
      have hd : Matrix.trace (family.irrep lb).rhoY = -1 := (hbits lb hlb1).2.2.2.mp hblb
      have he : Matrix.trace (family.irrep lb).rhoX = 1 := hε1 lb hlb
      rw [hd, he, one_pow, mul_one]
      norm_num
    have hGcard : G.card = 1 := by
      have hge : 1 ≤ G.card := by
        have : lg ∈ G := (hmemG lg).mpr ⟨hlg1, hcondg⟩
        rw [Finset.one_le_card]
        exact ⟨lg, this⟩
      have hle : G.card ≤ 1 := by
        have hGfilter : G = L1.filter (fun l : Label =>
            Matrix.trace (family.irrep l).rhoY
              * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1) := by
          rw [hGdef, hL1def]
          exact (Finset.filter_filter (fun l : Label => (family.irrep l).dim = 1)
            (fun l : Label => Matrix.trace (family.irrep l).rhoY
              * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1) Finset.univ).symm
        rw [hGfilter, Finset.card_le_one]
        intro a ha b hb
        have ha1 : (family.irrep a).dim = 1 := (hmem a).mp (Finset.mem_filter.mp ha).1
        have hb1 : (family.irrep b).dim = 1 := (hmem b).mp (Finset.mem_filter.mp hb).1
        have hca : Matrix.trace (family.irrep a).rhoY
            * (Matrix.trace (family.irrep a).rhoX) ^ s.val = 1 := (Finset.mem_filter.mp ha).2
        have hcb : Matrix.trace (family.irrep b).rhoY
            * (Matrix.trace (family.irrep b).rhoX) ^ s.val = 1 := (Finset.mem_filter.mp hb).2
        have hda : Matrix.trace (family.irrep a).rhoY = 1 := by
          rw [hε1 a (Finset.mem_filter.mp ha).1] at hca
          rw [one_pow, mul_one] at hca
          exact hca
        have hdb : Matrix.trace (family.irrep b).rhoY = 1 := by
          rw [hε1 b (Finset.mem_filter.mp hb).1] at hcb
          rw [one_pow, mul_one] at hcb
          exact hcb
        exact hinjD a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
          (by rw [hda, hdb])
      omega
    rw [hGcard, hL1card]

theorem dimFixedCount_identity (N : ℕ) [NeZero N] (Label : Type) [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N) :
    ∑ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s = N := by
  classical
  have hdf : ∀ l : Label, (family.irrep l).dim = 0 ∨ (family.irrep l).dim = 1
      ∨ (family.irrep l).dim = 2 := fun l => irrep_dim_cases (family.irrep l)
  have hw : ∀ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s
      = (if (family.irrep l).dim = 1 ∧
          Matrix.trace (family.irrep l).rhoY
            * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1 then 1 else 0)
        + (if (family.irrep l).dim = 2 then 2 else 0) := by
    intro l
    rcases hdf l with h | h | h
    · rw [if_neg (by intro hh; omega), if_neg (by intro hh; omega)]
      rw [h, zero_mul, add_zero]
    · rw [irrep_one_dim_dimFixed (family.irrep l) h s]
      by_cases hc : Matrix.trace (family.irrep l).rhoY
          * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1
      · rw [if_pos hc, if_pos (And.intro h hc), if_neg (by intro hh; omega)]
        rw [mul_one, add_zero]
        exact h
      · rw [if_neg hc, if_neg (by intro hh; cases hh with | intro h1 h2 => exact hc h2),
          if_neg (by intro hh; omega)]
        rw [mul_zero, add_zero]
    · rw [irrep_two_dim_dimFixed (family.irrep l) h s]
      rw [if_neg (by intro hh; omega), if_pos h]
      rw [mul_one, zero_add]
      exact h
  have h2s : ∀ l : Label, (family.irrep l).dim ^ 2
      = (if (family.irrep l).dim = 1 then 1 else 0) + (if (family.irrep l).dim = 2 then 4 else 0) := by
    intro l
    rcases hdf l with h | h | h <;> simp [h]
  have hsumW : (∑ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s)
      = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1 ∧
            Matrix.trace (family.irrep l).rhoY
              * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)).card
        + 2 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 2)).card := by
    calc (∑ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s)
        = ∑ l : Label, ((if (family.irrep l).dim = 1 ∧
              Matrix.trace (family.irrep l).rhoY
                * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1 then 1 else 0)
            + (if (family.irrep l).dim = 2 then 2 else 0)) :=
          Finset.sum_congr rfl (fun l _ => hw l)
      _ = (∑ l : Label, (if (family.irrep l).dim = 1 ∧
              Matrix.trace (family.irrep l).rhoY
                * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1 then 1 else 0))
          + ∑ l : Label, (if (family.irrep l).dim = 2 then 2 else 0) :=
          Finset.sum_add_distrib
      _ = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1 ∧
            Matrix.trace (family.irrep l).rhoY
              * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)).card
          + ∑ l : Label, (if (family.irrep l).dim = 2 then 2 else 0) := by
            rw [← Finset.card_filter]
      _ = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1 ∧
            Matrix.trace (family.irrep l).rhoY
              * (Matrix.trace (family.irrep l).rhoX) ^ s.val = 1)).card
          + 2 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 2)).card := by
            have hpnt : ∀ l : Label, (if (family.irrep l).dim = 2 then (2 : ℕ) else 0)
                = 2 * (if (family.irrep l).dim = 2 then 1 else 0) := by
              intro l
              by_cases h : (family.irrep l).dim = 2 <;> simp [h]
            rw [Finset.sum_congr rfl (fun l _ => hpnt l), ← Finset.mul_sum, Finset.sum_boole]
            push_cast
            rfl
  have hdim2 : (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1)).card
      + 4 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 2)).card = 2 * N := by
    have hs : (∑ l : Label, (family.irrep l).dim ^ 2)
        = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1)).card
          + 4 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 2)).card := by
      calc (∑ l : Label, (family.irrep l).dim ^ 2)
          = ∑ l : Label, ((if (family.irrep l).dim = 1 then 1 else 0)
              + (if (family.irrep l).dim = 2 then 4 else 0)) :=
            Finset.sum_congr rfl fun l _ => h2s l
        _ = (∑ l : Label, (if (family.irrep l).dim = 1 then 1 else 0))
            + ∑ l : Label, (if (family.irrep l).dim = 2 then 4 else 0) :=
            Finset.sum_add_distrib
        _ = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1)).card
            + ∑ l : Label, (if (family.irrep l).dim = 2 then 4 else 0) := by
              rw [← Finset.card_filter]
        _ = (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 1)).card
            + 4 * (Finset.univ.filter (fun l : Label => (family.irrep l).dim = 2)).card := by
              have hpnt : ∀ l : Label, (if (family.irrep l).dim = 2 then (4 : ℕ) else 0)
                  = 4 * (if (family.irrep l).dim = 2 then 1 else 0) := by
                intro l
                by_cases h : (family.irrep l).dim = 2 <;> simp [h]
              rw [Finset.sum_congr rfl (fun l _ => hpnt l), ← Finset.mul_sum, Finset.sum_boole]
              push_cast
              rfl
    rw [← hs]
    exact family.dimensionCount
  have hhalf := dimFixed_half_count N Label family s hdim2
  rw [hsumW]
  omega
end Qatlib.Concepts.HspRecovery.RecordExtract

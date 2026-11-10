/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLogicSynth04.MainResults.QubitRotations
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix
open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLogicSynth04.MainResults

theorem blockDiagonal_mulVec {N : Type*} [Fintype N] [DecidableEq N]
    (M : N → Matrix Bool Bool ℂ) (ψ : Bool × N → ℂ) :
    Matrix.blockDiagonal M *ᵥ ψ =
      fun p : Bool × N => (M p.2 *ᵥ fun i => ψ (i, p.2)) p.1 := by
  ext ⟨i, c⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply]
  conv_lhs => rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_comm, Finset.sum_eq_single c]
  · simp
  · intro b _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ c) h

lemma twoGate_block (a b : ℂ) :
    ∃ (φ θ : ℝ) (r : ℂ),
      (paperRy θ * paperRz φ) *ᵥ (fun i : Bool => if i then b else a) =
        fun i : Bool => if i then 0 else r := by
  by_cases hzero : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    refine ⟨0, 0, 0, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct]
  · have hne : Complex.normSq a + Complex.normSq b ≠ 0 := by
      intro h
      have ha : Complex.normSq a = 0 := by
        nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]
      have hb : Complex.normSq b = 0 := by
        nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]
      exact hzero ⟨Complex.normSq_eq_zero.mp ha, Complex.normSq_eq_zero.mp hb⟩
    set t : ℝ := Complex.normSq a + Complex.normSq b with htdef
    have ht : 0 < t := lt_of_le_of_ne
      (by nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]) (Ne.symm hne)
    set n : ℝ := Real.sqrt t with hndef
    have hn : 0 < n := by rw [hndef]; exact Real.sqrt_pos.mpr ht
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    set a' : ℂ := a / (n : ℂ) with ha'def
    set b' : ℂ := b / (n : ℂ) with hb'def
    have hn2 : Complex.normSq ((n : ℝ) : ℂ) = t := by
      rw [Complex.normSq_ofReal, hndef, Real.mul_self_sqrt ht.le]
    have hnorm : Complex.normSq a' + Complex.normSq b' = 1 := by
      rw [ha'def, hb'def, Complex.normSq_div, Complex.normSq_div, hn2]
      field_simp
      rw [htdef]
    obtain ⟨α, θ, β, hW⟩ := theorem2_preparation a' b' hnorm
    have hWun : (paperRz α * paperRy θ * paperRz β) ∈ Matrix.unitaryGroup Bool ℂ :=
      mul_mem_unitaryGroup (mul_mem_unitaryGroup (paperRz_unitary α) (paperRy_unitary θ))
        (paperRz_unitary β)
    have hWmul : (paperRz α * paperRy θ * paperRz β)ᴴ * (paperRz α * paperRy θ * paperRz β) = 1 := by
      have hh := (Matrix.mem_unitaryGroup_iff').mp hWun
      rwa [Matrix.star_eq_conjTranspose] at hh
    have hconj : (paperRz α * paperRy θ * paperRz β)ᴴ
        = paperRz (-β) * (paperRy (-θ) * paperRz (-α)) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        paperRz_conjTranspose, paperRy_conjTranspose, paperRz_conjTranspose]
    have hcol : (paperRz (-β) * (paperRy (-θ) * paperRz (-α))) *ᵥ
        (fun i : Bool => if i then b' else a') = ket0 := by
      rw [← hconj, ← hW, Matrix.mulVec_mulVec, hWmul, Matrix.one_mulVec]
    have hPbeta : paperRz (-β) *ᵥ ((paperRy (-θ) * paperRz (-α)) *ᵥ
        (fun i : Bool => if i then b' else a')) = ket0 := by
      rw [Matrix.mulVec_mulVec]
      exact hcol
    have hV : (paperRy (-θ) * paperRz (-α)) *ᵥ (fun i : Bool => if i then b' else a')
        = paperRz β *ᵥ ket0 := by
      have hinv : paperRz β * paperRz (-β) = 1 := by
        rw [paperRz_mul, show β + -β = 0 from by ring, paperRz_zero]
      have h := congrArg (fun w => paperRz β *ᵥ w) hPbeta
      (try dsimp only at h)
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h
      exact h
    have hvec : (fun i : Bool => if i then b else a)
        = n • (fun i : Bool => if i then b' else a') := by
      ext i
      rcases i with _ | _
      · simp only [ha'def, Pi.smul_apply, Complex.real_smul, Bool.false_eq_true, if_false]
        field_simp
      · simp only [hb'def, Pi.smul_apply, Complex.real_smul, if_true]
        field_simp
    refine ⟨-α, -θ, (n : ℂ) * Complex.exp (((-(β/2) : ℝ) : ℂ) * Complex.I), ?_⟩
    rw [hvec, Matrix.mulVec_smul, hV, paperRz_mulVec_ket0]
    ext i
    rcases i with _ | _
    · simp [Pi.smul_apply, Complex.real_smul]
    · simp [Pi.smul_apply]

theorem theorem9_disentangle {N : Type*} [Fintype N] [DecidableEq N] (ψ : Bool × N → ℂ) :
    ∃ (φ θ : N → ℝ) (r : N → ℂ),
      (Matrix.blockDiagonal (fun c => paperRy (θ c)) *
        Matrix.blockDiagonal (fun c => paperRz (φ c))) *ᵥ ψ
      = fun p : Bool × N => if p.1 then 0 else r p.2 := by
  choose φ θ r hr using fun c => twoGate_block (ψ (false, c)) (ψ (true, c))
  refine ⟨φ, θ, r, ?_⟩
  funext p
  rcases p with ⟨d, c⟩
  (try dsimp only)
  rw [← Matrix.blockDiagonal_mul, blockDiagonal_mulVec]
  exact congrArg (fun v => v d) (hr c)

theorem theorem9_disentangle_one {N : Type*} [Fintype N] [DecidableEq N]
    (ψ : Bool × N → ℂ) :
    ∃ (φ θ : N → ℝ) (r : N → ℂ),
      (Matrix.blockDiagonal (fun c => paperRy (θ c)) *
        Matrix.blockDiagonal (fun c => paperRz (φ c))) *ᵥ ψ
      = fun p : Bool × N => if p.1 then r p.2 else 0 := by
  obtain ⟨φ, θ, r, hr⟩ := theorem9_disentangle ψ
  refine ⟨φ, fun c => θ c + Real.pi, fun c => -r c, ?_⟩
  have hRy : Matrix.blockDiagonal (fun c => paperRy (θ c + Real.pi))
      = Matrix.blockDiagonal (fun _ : N => paperRy Real.pi) *
        Matrix.blockDiagonal (fun c => paperRy (θ c)) := by
    rw [← Matrix.blockDiagonal_mul]
    apply congrArg Matrix.blockDiagonal
    funext c
    rw [paperRy_mul]
    congr 1
    ring
  calc
    (Matrix.blockDiagonal (fun c => paperRy (θ c + Real.pi)) *
        Matrix.blockDiagonal (fun c => paperRz (φ c))) *ᵥ ψ
        = ((Matrix.blockDiagonal (fun _ : N => paperRy Real.pi) *
             Matrix.blockDiagonal (fun c => paperRy (θ c))) *
            Matrix.blockDiagonal (fun c => paperRz (φ c))) *ᵥ ψ := by rw [hRy]
    _ = (Matrix.blockDiagonal (fun _ : N => paperRy Real.pi) *
           Matrix.blockDiagonal (fun c => paperRy (θ c))) *ᵥ
          (Matrix.blockDiagonal (fun c => paperRz (φ c)) *ᵥ ψ) :=
        (Matrix.mulVec_mulVec ψ _ _).symm
    _ = Matrix.blockDiagonal (fun _ : N => paperRy Real.pi) *ᵥ
          (Matrix.blockDiagonal (fun c => paperRy (θ c)) *ᵥ
            (Matrix.blockDiagonal (fun c => paperRz (φ c)) *ᵥ ψ)) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = Matrix.blockDiagonal (fun _ : N => paperRy Real.pi) *ᵥ
          ((Matrix.blockDiagonal (fun c => paperRy (θ c)) *
            Matrix.blockDiagonal (fun c => paperRz (φ c))) *ᵥ ψ) :=
        congrArg _ (Matrix.mulVec_mulVec ψ _ _)
    _ = Matrix.blockDiagonal (fun _ : N => paperRy Real.pi) *ᵥ
          (fun p : Bool × N => if p.1 then 0 else r p.2) := congrArg _ hr
    _ = fun p : Bool × N =>
          ((fun _ : N => paperRy Real.pi) p.2 *ᵥ
            fun i => (fun p : Bool × N => if p.1 then 0 else r p.2) (i, p.2)) p.1 :=
        blockDiagonal_mulVec (fun _ : N => paperRy Real.pi)
          (fun p : Bool × N => if p.1 then 0 else r p.2)
    _ = fun p : Bool × N => if p.1 then (fun c => -r c) p.2 else 0 := by
        funext p
        rcases p with ⟨d, c⟩
        change (paperRy Real.pi *ᵥ (fun i : Bool => if i then (0 : ℂ) else r c)) d =
          if d then -r c else 0
        have hRyPi : paperRy Real.pi *ᵥ ket0 = fun i : Bool => if i then -1 else 0 := by
          ext i
          rcases i with _ | _ <;>
            simp [paperRy, ket0, Matrix.mulVec, dotProduct, qubitEulerRotation_apply]
        have hstep : (paperRy Real.pi *ᵥ (fun i : Bool => if i then (0 : ℂ) else r c)) =
            fun i : Bool => if i then -r c else 0 := by
          rw [show (fun i : Bool => if i then (0 : ℂ) else r c) = r c • ket0 from by
            ext i
            rcases i with _ | _ <;> simp [ket0]]
          rw [Matrix.mulVec_smul (M := paperRy Real.pi) (b := r c) (v := ket0)]
          rw [hRyPi]
          ext i
          rcases i with _ | _ <;> simp [Pi.smul_apply, mul_neg]
        exact congrFun hstep d

end Qatlib.Papers.QLogicSynth04.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.HigherMoments.FiniteTripleUStatistic
import Qatlib.Concepts.ShadowModels.ShadowVariance.QuadraticObservableShadows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ClassShadows20.HigherMoments
open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

noncomputable def cubicShadowKernel (n : ℕ) (a b c : Fin n → Fin 3 × Bool) : ℝ :=
  (Matrix.trace (tensorPauliSnapshot n a*tensorPauliSnapshot n b*tensorPauliSnapshot n c)).re
noncomputable def cubicShadowU (n m : ℕ) (ω : Fin m → Fin n → Fin 3 × Bool) : ℝ :=
  tripleUStatistic (cubicShadowKernel n) ω
noncomputable def cubicShadowMedian (n m r : ℕ)
    (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) : ℝ :=
  sortedBlockMedian r (fun b => cubicShadowU n m (ω b))

def cubicSign (b : Bool) : ℚ := if b then 1 else -1
def cubicOrientation (a b c : Fin 3) : ℚ :=
  if (a,b,c)=(0,1,2) ∨ (a,b,c)=(1,2,0) ∨ (a,b,c)=(2,0,1) then 1 else
  if (a,b,c)=(0,2,1) ∨ (a,b,c)=(2,1,0) ∨ (a,b,c)=(1,0,2) then -1 else 0

def gaussianRatMul (u v : ℚ × ℚ) : ℚ × ℚ :=
  (u.1*v.1-u.2*v.2,u.1*v.2+u.2*v.1)
def cubicLocalRat (a b c : Fin 3 × Bool) : ℚ × ℚ :=
  ((1+9*((if a.1=b.1 then cubicSign a.2*cubicSign b.2 else 0)+
         (if a.1=c.1 then cubicSign a.2*cubicSign c.2 else 0)+
         (if b.1=c.1 then cubicSign b.2*cubicSign c.2 else 0)))/4,
    27*cubicSign a.2*cubicSign b.2*cubicSign c.2*cubicOrientation a.1 b.1 c.1/4)

def cubicGaussianComplex (v : ℚ × ℚ) : ℂ := (v.1 : ℂ) + (v.2 : ℂ)*Complex.I

theorem gaussianRatMul_complex (u v : ℚ × ℚ) :
    cubicGaussianComplex (gaussianRatMul u v) = cubicGaussianComplex u*cubicGaussianComplex v := by
  simp only [cubicGaussianComplex,gaussianRatMul,Rat.cast_sub,Rat.cast_add,Rat.cast_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem cubicPauliShadow_form (a : Fin 3) (b : Bool) :
    PauliShadow b a = (1/2 : ℂ) • (1 : Operator 2) +
      ((3/2 : ℂ)*(cubicSign b : ℂ)) • pauliMatrix a := by
  cases b <;> simp only [PauliShadow,PauliProjector,cubicSign,Bool.false_eq_true,if_false,if_true]
  all_goals module

private theorem cubic_pauli_triple_trace (a b c : Fin 3) :
    Matrix.trace (pauliMatrix a*pauliMatrix b*pauliMatrix c) =
      2*(cubicOrientation a b c : ℂ)*Complex.I := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [h20,h21,Ne.symm h20,Ne.symm h21,cubicOrientation,Fin.ext_iff,Fin.val_ofNat,pauliMatrix,pauliX,pauliY,pauliZ,
      Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Complex.ext_iff,Complex.mul_re,Complex.mul_im]

theorem cubicLocalRat_trace (a b c : Fin 3 × Bool) :
    Matrix.trace (PauliShadow a.2 a.1 * PauliShadow b.2 b.1 * PauliShadow c.2 c.1) =
      cubicGaussianComplex (cubicLocalRat a b c) := by
  simp only [cubicPauliShadow_form,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,Matrix.trace_add,
    Matrix.trace_smul,trace_pauliMatrix,trace_pauliMatrix_mul,cubic_pauli_triple_trace,
    Matrix.trace_one,smul_eq_mul]
  simp only [cubicGaussianComplex,cubicLocalRat,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_one,Rat.cast_ofNat,apply_ite]
  split_ifs <;> norm_num only [Fintype.card_fin,Rat.cast_mul] <;> ring

theorem cubicPauliShadow_hermitian (a : Fin 3 × Bool) :
    (PauliShadow a.2 a.1).IsHermitian := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hp : (pauliMatrix a.1)ᴴ = pauliMatrix a.1 := by
    rcases a with ⟨a,s⟩
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      norm_num [h20,h21,Fin.ext_iff,Fin.val_ofNat,pauliMatrix,pauliX,pauliY,pauliZ,Matrix.conjTranspose_apply]
  unfold Matrix.IsHermitian
  rw [cubicPauliShadow_form,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul,hp]
  rcases a with ⟨a,s⟩
  cases s <;> norm_num [cubicSign]

theorem cubicSnapshot_hermitian (n : ℕ) (a : Fin n → Fin 3 × Bool) :
    (tensorPauliSnapshot n a).IsHermitian := by
  unfold Matrix.IsHermitian tensorPauliSnapshot
  rw [tensorPauliProduct_conjTranspose]
  congr 1
  funext i
  exact (cubicPauliShadow_hermitian (a i)).eq

private theorem cubic_trace_reverse {D : ℕ} (A B C : Operator D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (Matrix.trace (A*B*C)).re = (Matrix.trace (C*B*A)).re := by
  have he := Matrix.trace_conjTranspose (A*B*C)
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hA.eq,hB.eq,hC.eq,
    ← Matrix.mul_assoc] at he
  exact (congrArg Complex.re he).symm

theorem cubicShadowKernel_symmetric (n : ℕ) : tripleKernelSymmetric (cubicShadowKernel n) := by
  intro a b c
  have ha := cubicSnapshot_hermitian n a
  have hb := cubicSnapshot_hermitian n b
  have hc := cubicSnapshot_hermitian n c
  constructor
  · unfold cubicShadowKernel
    rw [cubic_trace_reverse (tensorPauliSnapshot n a) (tensorPauliSnapshot n b)
      (tensorPauliSnapshot n c) ha hb hc]
    rw [Matrix.mul_assoc (tensorPauliSnapshot n c) (tensorPauliSnapshot n b) (tensorPauliSnapshot n a),
      Matrix.trace_mul_comm (tensorPauliSnapshot n c)
        (tensorPauliSnapshot n b*tensorPauliSnapshot n a)]
  · unfold cubicShadowKernel
    rw [cubic_trace_reverse (tensorPauliSnapshot n a) (tensorPauliSnapshot n b)
      (tensorPauliSnapshot n c) ha hb hc]
    exact congrArg Complex.re (Matrix.trace_mul_cycle (tensorPauliSnapshot n c)
      (tensorPauliSnapshot n b) (tensorPauliSnapshot n a))

theorem cubicShadowKernel_mean (n : ℕ) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) :
    tripleKernelMean (tensorPauliLaw n ρ hρ) (cubicShadowKernel n) =
      (Matrix.trace (ρ^3)).re := by
  classical
  let p := tensorPauliLaw n ρ hρ
  have hrec : (∑ a, (p.prob a : ℂ) • tensorPauliSnapshot n a) = ρ :=
    tensor_pauli_snapshot_reconstructs_entangled_input n ρ hρ
  have he : (∑ a, ∑ b, ∑ c, (p.prob a : ℂ)*(p.prob b : ℂ)*(p.prob c : ℂ)*
      Matrix.trace (tensorPauliSnapshot n c*tensorPauliSnapshot n b*tensorPauliSnapshot n a)) =
      Matrix.trace (ρ*ρ*ρ) := by
    conv_rhs => rw [← hrec]
    simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hr := congrArg Complex.re he
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero] at hr
  have hs : ∀ a b c, (Matrix.trace
      (tensorPauliSnapshot n c*tensorPauliSnapshot n b*tensorPauliSnapshot n a)).re =
      cubicShadowKernel n a b c := by
    intro a b c
    exact cubic_trace_reverse (tensorPauliSnapshot n c) (tensorPauliSnapshot n b)
      (tensorPauliSnapshot n a) (cubicSnapshot_hermitian n c) (cubicSnapshot_hermitian n b)
        (cubicSnapshot_hermitian n a)
  simp_rw [hs] at hr
  simpa [tripleKernelMean,cubicShadowKernel,p,pow_succ,pow_two] using hr

theorem cubicLocalRat_sq_bound (a b c : Fin 3 × Bool) :
    (cubicLocalRat a b c).1^2+(cubicLocalRat a b c).2^2 ≤ (49 : ℚ) := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  rcases a with ⟨a,s⟩; rcases b with ⟨b,t⟩; rcases c with ⟨c,u⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> cases s <;> cases t <;> cases u <;>
    norm_num [h20,h21,Ne.symm h20,Ne.symm h21,cubicLocalRat,cubicSign,cubicOrientation,Fin.ext_iff,Fin.val_ofNat]

theorem cubicLocalRat_norm_bound (a b c : Fin 3 × Bool) :
    ‖cubicGaussianComplex (cubicLocalRat a b c)‖ ≤ (7 : ℝ) := by
  have hh : ((cubicLocalRat a b c).1 : ℝ)^2+((cubicLocalRat a b c).2 : ℝ)^2 ≤ (49 : ℝ) :=
    by exact_mod_cast cubicLocalRat_sq_bound a b c
  have hs := Complex.sq_norm (cubicGaussianComplex (cubicLocalRat a b c))
  have hr : Complex.normSq (cubicGaussianComplex (cubicLocalRat a b c)) =
      ((cubicLocalRat a b c).1 : ℝ)^2+((cubicLocalRat a b c).2 : ℝ)^2 := by
    simp [cubicGaussianComplex,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two]
  rw [hr] at hs
  nlinarith [norm_nonneg (cubicGaussianComplex (cubicLocalRat a b c))]

theorem cubicShadowKernel_bound (n : ℕ) (a b c : Fin n → Fin 3 × Bool) :
    |cubicShadowKernel n a b c| ≤ (7 : ℝ)^n := by
  unfold cubicShadowKernel tensorPauliSnapshot
  rw [tensorPauliProduct_mul,tensorPauliProduct_mul,tensorPauliProduct_trace]
  simp_rw [cubicLocalRat_trace]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, (7 : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => cubicLocalRat_norm_bound _ _ _)
    _ = _ := by simp

theorem cubic_shadow_actual_kernel_reconstruction_and_bound (n : ℕ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) :
    tripleKernelSymmetric (cubicShadowKernel n) ∧
    (∀ a b c, |cubicShadowKernel n a b c| ≤ (7:ℝ)^n) ∧
    tripleKernelMean (tensorPauliLaw n ρ hρ) (cubicShadowKernel n)=(Matrix.trace (ρ^3)).re := by
  exact ⟨cubicShadowKernel_symmetric n,cubicShadowKernel_bound n,cubicShadowKernel_mean n ρ hρ⟩

theorem cubic_shadow_same_record_mean_and_variance (n m : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (hm : 3 ≤ m) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool,
      (tensorPauliLaw n ρ hρ).probOf ω*cubicShadowU n m ω)=(Matrix.trace (ρ^3)).re ∧
    (∑ ω : Fin m → Fin n → Fin 3 × Bool,
      (tensorPauliLaw n ρ hρ).probOf ω*(cubicShadowU n m ω-(Matrix.trace (ρ^3)).re)^2)=
      tripleVarianceBudget (tensorPauliLaw n ρ hρ) m (cubicShadowKernel n) := by
  constructor
  · exact (triple_u_actual_unbiased _ (tensorPauliLaw n ρ hρ) m (cubicShadowKernel n) hm).trans
      (cubicShadowKernel_mean n ρ hρ)
  · rw [← cubicShadowKernel_mean n ρ hρ]
    exact triple_u_exact_overlap_variance _ _ m _ hm (cubicShadowKernel_symmetric n)

theorem cubic_shadow_explicit_sample_budget_and_median (n m r : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (ε : ℝ) (hm : 3 ≤ m) (hε : 0 < ε) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool,
      (tensorPauliLaw n ρ hρ).probOf ω*(cubicShadowU n m ω-(Matrix.trace (ρ^3)).re)^2) ≤
        (9:ℝ)/(m:ℝ)*(49:ℝ)^n ∧
    ((144:ℝ)*(49:ℝ)^n ≤ (m:ℝ)*ε^2 →
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
        ε < |cubicShadowMedian n m r ω-(Matrix.trace (ρ^3)).re|),
        ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤
        (2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1)) := by
  classical
  let p := tensorPauliLaw n ρ hρ
  let Y := Fin m → Fin n → Fin 3 × Bool
  let q : FinDist Y :=
    { prob := p.probOf
      nonneg := fun ω => Finset.prod_nonneg fun _ _ => p.nonneg _
      sum_one := p.sum_probOf m }
  let θ := (Matrix.trace (ρ^3)).re
  have hmean : q.expect (cubicShadowU n m) = θ :=
    (cubic_shadow_same_record_mean_and_variance n m ρ hρ hm).1
  have hv : q.expect (fun ω => (cubicShadowU n m ω-θ)^2) ≤ 9/(m:ℝ)*(49:ℝ)^n := by
    have he := triple_u_variance_le_bound _ p m (cubicShadowKernel n) hm
      (cubicShadowKernel_symmetric n) ((7:ℝ)^n) (by positivity) (cubicShadowKernel_bound n)
    have hpow : ((7:ℝ)^n)^2 = (49:ℝ)^n := by rw [← pow_mul,pow_mul']; norm_num
    rw [hpow,cubicShadowKernel_mean] at he
    exact he
  refine ⟨hv,?_⟩
  intro hbudget
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hvε : q.expect (fun ω => (cubicShadowU n m ω-q.expect (cubicShadowU n m))^2) ≤ ε^2/16 := by
    rw [hmean]
    apply hv.trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [hbudget]
  have hc := heterogeneous_weighted_median_concentration r 1 (fun _ _ => q)
    (fun _ _ => 1) (fun _ _ => cubicShadowU n m) θ ε hε
    (fun _ => by simpa only [Fin.sum_univ_one,one_mul] using hmean)
    (fun _ => by simpa only [Fin.sum_univ_one,one_pow,one_mul] using hvε)
  let e : (Fin (2*r+1) → Y) ≃ (Fin (2*r+1) → Fin 1 → Y) :=
    { toFun := fun ω j _ => ω j
      invFun := fun ω j => ω j 0
      left_inv := fun _ => rfl
      right_inv := by
        intro ω
        funext j b
        have hb : b = 0 := Subsingleton.elim _ _
        subst b
        rfl }
  have hblock (ω : Fin (2*r+1) → Y) :
      weightedBlock r 1 (fun _ _ => 1) (fun _ _ => cubicShadowU n m) (e ω) =
        fun j => cubicShadowU n m (ω j) := by
    funext j
    change (∑ _b : Fin 1, (1:ℝ)*cubicShadowU n m (ω j)) = _
    simp only [Fin.sum_univ_one,one_mul]
  have hprob (ω : Fin (2*r+1) → Y) :
      (blockRecordLaw r 1 (fun _ _ => q)).prob (e ω) = ∏ j, p.probOf (ω j) := by
    change (∏ j, ∏ _b : Fin 1, p.probOf (ω j)) = _
    simp only [Fin.prod_univ_one]
  rw [Finset.sum_filter] at hc ⊢
  rw [← e.sum_comp] at hc
  simp_rw [hblock,hprob] at hc
  exact hc

end Qatlib.Papers.ClassShadows20.HigherMoments

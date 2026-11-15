/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiSeparabilityDefs
public import Qatlib.Foundations.MatrixAlgebra.GramFactor.RealGramFactorization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
namespace Qatlib.Concepts.GramQueryCore.QfiCompletion

open Qatlib.Foundations.MatrixAlgebra.GramFactor
open scoped Classical BigOperators Matrix

def MqfiDilationData {p r q : ℕ} (B : Fin p → Matrix (Fin r) (Fin q) ℝ) : Prop :=
  ∃ (n : ℕ) (u : (Fin r ⊕ Fin (q+n)) → Fin r → ℝ)
    (lam : Fin p → (Fin r ⊕ Fin (q+n)) → ℝ),
    (∀ s t : Fin r,∑ j,u j s*u j t=if s=t then 1 else 0) ∧
    (∀ a : Fin p,∀ s t : Fin r,∑ j,lam a j*u j s*u j t=0) ∧
    (∀ a b : Fin p,∀ s t : Fin r,∑ j,lam a j*lam b j*u j s*u j t=mqfiBlocks B (a,s) (b,t))

/-- For positive `a`, twice the product of the two normalized scalars equals their product
divided by the square of `a`. -/
private theorem mqfi_pair_norm (a : ℝ) (ha : 0<a) (x y : ℝ) :
    2*(x/(a*Real.sqrt 2)* (y/(a*Real.sqrt 2)))=(a^2)⁻¹*(x*y) := by
  have ha0 := ha.ne'
  have h2 : Real.sqrt (2 : ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]

/-- For positive `a` and nonnegative `c`, the normalized paired covariance simplifies to `c`
times the two scalar products. -/
private theorem mqfi_pair_covariance (a : ℝ) (ha : 0<a) (c : ℝ) (hc : 0≤c)
    (x y v w : ℝ) :
    2*((a*Real.sqrt c*x)*(a*Real.sqrt c*y)*(v/(a*Real.sqrt 2))*(w/(a*Real.sqrt 2)))=
      c*(x*y)*(v*w) := by
  have ha0 := ha.ne'
  have h2 : Real.sqrt (2 : ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt hc,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  ring

/-- Real separability of the MQFI blocks provides dilation data for `B`. -/
theorem mqfiDilationData_of_realSeparable {p r q : ℕ}
    (B : Fin p → Matrix (Fin r) (Fin q) ℝ) (h : RealSeparable (mqfiBlocks B)) :
    MqfiDilationData B := by
  obtain ⟨m,c,z,w,hc,hsep⟩ := h
  let W : Matrix (Fin r) (Fin m) ℝ := fun s i => w i s
  obtain ⟨a,R,ha,hR⟩ :=
      Qatlib.Foundations.MatrixAlgebra.GramFactor.exists_scaled_real_gram_complement W
  let N := 2*m+r
  let T := ((Fin m × Bool) ⊕ Fin r) ⊕ Fin (r+q)
  let J := Fin r ⊕ Fin (q+N)
  let E : T ≃ J := Fintype.equivOfCardEq (by simp [T,J,N]; omega)
  let u0 : T → Fin r → ℝ := fun j => match j with
    | Sum.inl (Sum.inl (i,_)) => fun s => w i s/(a*Real.sqrt 2)
    | Sum.inl (Sum.inr k) => fun s => R s k
    | Sum.inr _ => fun _ => 0
  let lam0 : Fin p → T → ℝ := fun b j => match j with
    | Sum.inl (Sum.inl (i,b')) => if b' then -a*Real.sqrt (c i)*z i b else a*Real.sqrt (c i)*z i b
    | Sum.inl (Sum.inr _) => 0
    | Sum.inr _ => 0
  have hnorm (s t : Fin r) : (∑ j : T,u0 j s*u0 j t)=if s=t then 1 else 0 := by
    have h := congrFun (congrFun hR s) t
    simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply] at h
    simp only [T,u0,Fintype.sum_sum_type,Fintype.sum_prod_type,zero_mul,Finset.sum_const_zero,add_zero,
      Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat]
    simp_rw [mqfi_pair_norm a ha]
    rw [← Finset.mul_sum,add_comm]
    exact h
  have hmean (b : Fin p) (s t : Fin r) : (∑ j : T,lam0 b j*u0 j s*u0 j t)=0 := by
    simp only [T,u0,lam0,Fintype.sum_sum_type,Fintype.sum_prod_type,zero_mul,Finset.sum_const_zero,add_zero]
    apply Finset.sum_eq_zero
    intro i _
    simp only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false]
    ring
  have hcov (b d : Fin p) (s t : Fin r) :
      (∑ j : T,lam0 b j*lam0 d j*u0 j s*u0 j t)=mqfiBlocks B (b,s) (d,t) := by
    have hpair (i : Fin m) :
        (∑ b' : Bool,lam0 b (Sum.inl (Sum.inl (i,b')))*lam0 d (Sum.inl (Sum.inl (i,b')))*
          u0 (Sum.inl (Sum.inl (i,b'))) s*u0 (Sum.inl (Sum.inl (i,b'))) t)=
            c i*(z i b*z i d)*(w i s*w i t) := by
      simp only [u0,lam0,Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false]
      calc
        _ = 2*((a*Real.sqrt (c i)*z i b)*(a*Real.sqrt (c i)*z i d)*
          (w i s/(a*Real.sqrt 2))*(w i t/(a*Real.sqrt 2))) := by ring
        _ = _ := mqfi_pair_covariance a ha (c i) (hc i) (z i b) (z i d) (w i s) (w i t)
    simp only [T,Fintype.sum_sum_type,Fintype.sum_prod_type]
    have hslack : (∑ j : Fin r,lam0 b (Sum.inl (Sum.inr j))*lam0 d (Sum.inl (Sum.inr j))*
      u0 (Sum.inl (Sum.inr j)) s*u0 (Sum.inl (Sum.inr j)) t)=0 := by simp [lam0]
    have hpad :
        (∑ j : Fin (r+q),lam0 b (Sum.inr j)*lam0 d (Sum.inr j)*u0 (Sum.inr j) s*u0 (Sum.inr j) t)=0 := by simp [lam0]
    rw [hslack,hpad,add_zero,add_zero]
    simp_rw [hpair]
    exact (hsep (b,s) (d,t)).symm
  let u := fun j : J => u0 (E.symm j)
  let lam := fun b : Fin p => fun j : J => lam0 b (E.symm j)
  refine ⟨N,u,lam,?_,?_,?_⟩
  · intro s t
    rw [← Equiv.sum_comp E (fun j : J => u j s*u j t)]
    simpa only [u,Equiv.symm_apply_apply] using hnorm s t
  · intro b s t
    rw [← Equiv.sum_comp E (fun j : J => lam b j*u j s*u j t)]
    simpa only [u,lam,Equiv.symm_apply_apply] using hmean b s t
  · intro b d s t
    rw [← Equiv.sum_comp E (fun j : J => lam b j*lam d j*u j s*u j t)]
    simpa only [u,lam,Equiv.symm_apply_apply] using hcov b d s t
end Qatlib.Concepts.GramQueryCore.QfiCompletion

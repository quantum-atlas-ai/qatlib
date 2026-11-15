/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Data.List.GetD
public import Qatlib.Concepts.LaurentPolys.FiniteBitCost.FiniteQSPGates

@[expose] public section
open Qatlib.Concepts.NativeNumerics.NlfftPipeline Qatlib.Concepts.LaurentPolys.FiniteBitCost Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.FiniteBitCost
open Polynomial Matrix
open scoped Matrix.Norms.L2Operator

/-- The symmetric QSP bridge parameter list has length `2*d+1`. -/
theorem rhw_qsp_bridge_sym_length (ψ : ℕ → ℝ) (d : ℕ) : (rhwQSPBridgeGammas ψ d).length=2*d+1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [rhwQSPBridgeGammas,List.length_cons,List.length_append,List.length_nil,ih]; omega

/-- For the stated angle ranges, the symmetric QSP operator is the bridge word conjugated by
Hadamard gates. -/
theorem rhw_qsp_bridge_symmetric_qsp (ψ : ℕ → ℝ) (d : ℕ) (θ : ℝ)
    (hθ : θ∈Set.Icc (0:ℝ) (Real.pi/2))
    (hψ : ∀ k≤d, ψ k∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) :
    rhwQSPBridgeOperator ψ (Real.cos θ) d=Hadamard*rhwQSPBridgeWord (Complex.exp ((θ:ℂ)*Complex.I)) (rhwQSPBridgeGammas ψ d)*Hadamard := by
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hw : w≠0 := Complex.exp_ne_zero _
  change rhwQSPBridgeOperator ψ (Real.cos θ) d=Hadamard*rhwQSPBridgeWord w
      (rhwQSPBridgeGammas ψ d)*Hadamard
  have hsignal : Hadamard*rhwQSPBridgeDiagonal w*Hadamard=rhwQSPBridgeSignal (Real.cos θ) :=
      rhw_qsp_bridge_had_signal θ hθ
  induction d with
  | zero => simp only [rhwQSPBridgeGammas,rhw_qsp_bridge_word_singleton w hw,rhw_qsp_bridge_had_elem (ψ 0) (hψ 0 le_rfl),rhwQSPBridgeOperator]
  | succ d ih =>
    have hp := hψ (d+1) le_rfl
    have hprev := ih (fun k hk => hψ k (by omega))
    rw [rhwQSPBridgeGammas,rhwQSPBridgeWord,rhw_qsp_bridge_word_append w hw,rhw_qsp_bridge_word_singleton w hw]
    simp only [rhw_qsp_bridge_had_mul,rhw_qsp_bridge_had_elem _ hp,hsignal,← hprev]
    simp only [rhwQSPBridgeOperator,mul_assoc]

/-- For a unit modulus signal, sandwiching the centered bridge by diagonal powers gives the
bridge pair followed by the doubled diagonal power. -/
theorem rhw_qsp_bridge_centered_sandwich (d : ℕ) (gs : List ℂ) (w : ℂ) (hw : ‖w‖=1) :
    (rhwQSPBridgeDiagonal w)^d*rhwQSPBridgeCentered d gs (w^2)*(rhwQSPBridgeDiagonal w)^d=rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^(2*d) := by
  have hw0 : w≠0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have hstar := rhw_qsp_bridge_star_of_unit w hw
  have hbinv : star (((w^2)^d)⁻¹)=(w^2)^d := by
    rw [star_inv₀,star_pow,star_pow,hstar]
    simp only [← inv_pow,inv_inv]
  have hpow : (w^2)^d=(w^d)^2 := by rw [← pow_mul,← pow_mul]; congr 1; omega
  have hlast : w^(2*d)=(w^d)^2 := by rw [← pow_mul]; congr 1; omega
  simp only [rhw_qsp_bridge_diag_pow]
  simp only [rhwQSPBridgeCentered,rhwQSPBridgePair,rhwQSPBridgeDiagonal,rhw_qsp_bridge_mat_mul,star_mul,hbinv]
  simp only [hpow,hlast]
  ext i j
  cases i <;> cases j <;> simp only [rhwQSPBridgeMatrix,Bool.false_eq_true,ite_false,ite_true]
  all_goals field_simp
  all_goals ring

/-- For the stated angle ranges, the QSP operator has the centered bridge sandwich
representation of equation 27. -/
theorem rhw_qsp_bridge_eq27 (ψ : ℕ → ℝ) (d : ℕ) (θ : ℝ)
    (hθ : θ∈Set.Icc (0:ℝ) (Real.pi/2))
    (hψ : ∀ k≤d, ψ k∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) :
    let w := Complex.exp ((θ:ℂ)*Complex.I)
    rhwQSPBridgeOperator ψ (Real.cos θ) d=Hadamard*(rhwQSPBridgeDiagonal w)^d*
      rhwQSPBridgeCentered d (rhwQSPBridgeGammas ψ d) (w^2)*(rhwQSPBridgeDiagonal w)^d*Hadamard := by
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hw : ‖w‖=1 := Complex.norm_exp_ofReal_mul_I θ
  have hn : rhwQSPBridgeGammas ψ d≠[] := by
    intro he
    have h := rhw_qsp_bridge_sym_length ψ d
    rw [he,List.length_nil] at h
    omega
  (try dsimp only)
  rw [rhw_qsp_bridge_symmetric_qsp ψ d θ hθ hψ,rhw_qsp_bridge_word_pair_nonempty _ hn w hw,rhw_qsp_bridge_sym_length,Nat.add_sub_cancel]
  rw [← rhw_qsp_bridge_centered_sandwich d (rhwQSPBridgeGammas ψ d) w hw]
  simp only [mul_assoc,w]

/-- The symmetric QSP bridge operator equals its transpose. -/
theorem rhw_qsp_bridge_qsp_symmetric (ψ : ℕ → ℝ) (x : ℝ) (d : ℕ) : (rhwQSPBridgeOperator ψ x d).transpose=rhwQSPBridgeOperator ψ x d := by
  have hp (φ : ℝ) : (rhwQSPBridgePhase φ).transpose=rhwQSPBridgePhase φ := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.transpose_apply,rhwQSPBridgePhase,rhwQSPBridgeMatrix]
  have hs : (rhwQSPBridgeSignal x).transpose=rhwQSPBridgeSignal x := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.transpose_apply,rhwQSPBridgeSignal,rhwQSPBridgeMatrix]
  induction d with
  | zero => exact hp _
  | succ d ih => simp only [rhwQSPBridgeOperator,Matrix.transpose_mul,hp,hs,ih,mul_assoc]

/-- For a unit modulus signal, the bridge pair with its diagonal power has the stated matrix
form in terms of the two nonlinear Fourier polynomials. -/
theorem rhw_qsp_bridge_pair_sandwich_shape (d : ℕ) (gs : List ℂ) (w : ℂ) (hw : ‖w‖=1) :
    let A := (nlftSU2 gs).1.eval (w^2)
    let B := (nlftSU2 gs).2.eval (w^2)
    let α := w^(2*d)*star A
    let b := ((w^2)^d)⁻¹*B
    rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^(2*d)=rhwQSPBridgeMatrix α b (-star b) (star α) := by
  have hw0 : w≠0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have hstar := rhw_qsp_bridge_star_of_unit w hw
  have hbinv : star (((w^2)^d)⁻¹)=(w^2)^d := by
    rw [star_inv₀,star_pow,star_pow,hstar]
    simp only [← inv_pow,inv_inv]
  have hlast : star (w^(2*d))=(w^(2*d))⁻¹ := by
    simp only [star_pow,hstar,inv_pow]
  have hpow : (w^2)^d=w^(2*d) := (pow_mul w 2 d).symm
  (try dsimp only)
  simp only [rhw_qsp_bridge_diag_pow]
  simp only [rhwQSPBridgePair,rhwQSPBridgeDiagonal,rhw_qsp_bridge_mat_mul,star_mul,hbinv,hlast,star_star]
  simp only [hpow]
  ext i j
  cases i <;> cases j <;> simp only [rhwQSPBridgeMatrix,Bool.false_eq_true,ite_false,ite_true]
  all_goals field_simp
  all_goals ring

/-- If the Hadamard conjugated bridge matrix is symmetric, its false diagonal entry imaginary
part multiplied by `Complex.I` equals `b`. -/
theorem rhw_qsp_bridge_observable (a b : ℂ) (h : (Hadamard*rhwQSPBridgeMatrix a b (-star b) (star a)*Hadamard).transpose=
    Hadamard*rhwQSPBridgeMatrix a b (-star b) (star a)*Hadamard) :
    Complex.I*((Hadamard*rhwQSPBridgeMatrix a b (-star b) (star a)*Hadamard) false false).im=b := by
  rw [rhw_qsp_bridge_had_mat] at h ⊢
  have hc := congrArg (fun M : Matrix Bool Bool ℂ => (M false true).re) h
  simp only [Matrix.transpose_apply,rhwQSPBridgeMatrix,Bool.false_eq_true,ite_false,ite_true] at hc
  have hbr : b.re=0 := by
    simp only [Complex.div_ofNat_re,Complex.add_re,Complex.sub_re,Complex.neg_re,
      Complex.star_def,Complex.conj_re] at hc
    linarith
  apply Complex.ext
  · simp only [rhwQSPBridgeMatrix,Bool.false_eq_true,ite_false,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,hbr]
  · simp only [rhwQSPBridgeMatrix,Bool.false_eq_true,ite_false,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,
      Complex.div_ofNat_im,Complex.add_im,Complex.neg_im,Complex.star_def,Complex.conj_im]
    ring

/-- For the stated angle ranges, the QSP observable equals the second nonlinear Fourier
polynomial evaluated at the squared signal, divided by its degree power. -/
theorem rhw_qsp_bridge_eq28 (ψ : ℕ → ℝ) (d : ℕ) (θ : ℝ)
    (hθ : θ∈Set.Icc (0:ℝ) (Real.pi/2))
    (hψ : ∀ k≤d, ψ k∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) :
    let w := Complex.exp ((θ:ℂ)*Complex.I)
    Complex.I*((rhwQSPBridgeOperator ψ (Real.cos θ) d) false false).im=
      ((w^2)^d)⁻¹*(nlftSU2 (rhwQSPBridgeGammas ψ d)).2.eval (w^2) := by
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hw : ‖w‖=1 := Complex.norm_exp_ofReal_mul_I θ
  have hn : rhwQSPBridgeGammas ψ d≠[] := by
    intro he
    have h := rhw_qsp_bridge_sym_length ψ d
    rw [he,List.length_nil] at h
    omega
  have hq : rhwQSPBridgeOperator ψ (Real.cos θ) d=Hadamard*
      rhwQSPBridgeMatrix (w^(2*d)*star ((nlftSU2 (rhwQSPBridgeGammas ψ d)).1.eval (w^2)))
        (((w^2)^d)⁻¹*(nlftSU2 (rhwQSPBridgeGammas ψ d)).2.eval (w^2))
        (-star (((w^2)^d)⁻¹*(nlftSU2 (rhwQSPBridgeGammas ψ d)).2.eval (w^2)))
        (star (w^(2*d)*star ((nlftSU2 (rhwQSPBridgeGammas ψ d)).1.eval (w^2))))*Hadamard := by
    rw [rhw_qsp_bridge_symmetric_qsp ψ d θ hθ hψ,rhw_qsp_bridge_word_pair_nonempty _ hn w hw,rhw_qsp_bridge_sym_length,Nat.add_sub_cancel,
      rhw_qsp_bridge_pair_sandwich_shape d _ w hw]
  have hs := rhw_qsp_bridge_qsp_symmetric ψ (Real.cos θ) d
  rw [hq] at hs
  (try dsimp only)
  rw [hq]
  exact rhw_qsp_bridge_observable _ _ hs

/-- The symmetric bridge parameter list has the prescribed coefficient at both positions equally
distant from its center. -/
theorem rhw_qsp_bridge_sym_get_center (ψ : ℕ → ℝ) (d k : ℕ) (hk : k≤d) :
    (rhwQSPBridgeGammas ψ d).getD (d-k) 0=rhwQSPBridgeCoefficient (ψ k) ∧
    (rhwQSPBridgeGammas ψ d).getD (d+k) 0=rhwQSPBridgeCoefficient (ψ k) := by
  induction d generalizing k with
  | zero =>
    have h : k=0 := by omega
    subst k
    simp [rhwQSPBridgeGammas]
  | succ d ih =>
    by_cases hkd : k=d+1
    · subst k
      rw [rhwQSPBridgeGammas]
      constructor
      · simp only [Nat.sub_self,List.getD_cons_zero]
      · rw [show d+1+(d+1)=(2*d+1)+1 by omega,List.getD_cons_succ,
          List.getD_append_right _ _ _ _ (by rw [rhw_qsp_bridge_sym_length]),rhw_qsp_bridge_sym_length,Nat.sub_self,List.getD_cons_zero]
    · have hkle : k≤d := by omega
      have h := ih k hkle
      rw [rhwQSPBridgeGammas]
      constructor
      · rw [show d+1-k=(d-k)+1 by omega,List.getD_cons_succ,
          List.getD_append _ _ _ _ (by rw [rhw_qsp_bridge_sym_length]; omega)]
        exact h.1
      · rw [show d+1+k=(d+k)+1 by omega,List.getD_cons_succ,
          List.getD_append _ _ _ _ (by rw [rhw_qsp_bridge_sym_length]; omega)]
        exact h.2

/-- A list of length `2*d+1` with the prescribed coefficients on both sides of its center equals
the symmetric bridge parameter list. -/
theorem rhw_qsp_bridge_sym_eq_of_centers (ψ : ℕ → ℝ) (d : ℕ) (gs : List ℂ)
    (hlen : gs.length=2*d+1)
    (h : ∀ k≤d, gs.getD (d-k) 0=rhwQSPBridgeCoefficient (ψ k) ∧
      gs.getD (d+k) 0=rhwQSPBridgeCoefficient (ψ k)) : gs=rhwQSPBridgeGammas ψ d := by
  apply List.ext_getElem
  · rw [hlen,rhw_qsp_bridge_sym_length]
  · intro i hi hj
    have hg : gs[i]=gs.getD i 0 := (List.getD_eq_getElem gs 0 hi).symm
    have hs : (rhwQSPBridgeGammas ψ d)[i]=(rhwQSPBridgeGammas ψ d).getD i 0 :=
      (List.getD_eq_getElem _ 0 hj).symm
    rw [hg,hs]
    by_cases hid : i≤d
    · have hk : d-i≤d := by omega
      have he : d-(d-i)=i := by omega
      have a := (h (d-i) hk).1
      have b := (rhw_qsp_bridge_sym_get_center ψ d (d-i) hk).1
      rw [he] at a b
      exact a.trans b.symm
    · have hk : i-d≤d := by rw [hlen] at hi; omega
      have he : d+(i-d)=i := by omega
      have a := (h (i-d) hk).2
      have b := (rhw_qsp_bridge_sym_get_center ψ d (i-d) hk).2
      rw [he] at a b
      exact a.trans b.symm

end Qatlib.Concepts.LaurentPolys.FiniteBitCost

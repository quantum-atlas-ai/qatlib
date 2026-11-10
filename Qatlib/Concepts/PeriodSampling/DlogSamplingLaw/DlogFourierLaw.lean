/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms
import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicPeriodSampling
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Matrix
open scoped Classical BigOperators

private theorem applyGate_ket_entry {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (k t : I) : ApplyGate A (Ket k) t = A t k := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite]

theorem dlog_qft_column (N q : ℕ) (hNq : N ≤ q) (a : Fin N) (c : Fin q) :
    QFTMatrix q c (Fin.castLE hNq a) = offGridPhase q ((a.val : ℝ)/(q : ℝ)) c := by
  rw [qftMatrix_apply, primRoot_zpow_eq_exp, offGridPhase]
  simp only [Fin.val_castLE]
  congr 1
  congr 1
  push_cast
  ring

theorem dlog_state_normalized (p q : ℕ) [NeZero p] (g x : ZMod p)
    (hp : 1 < p) (hpq : p < q) : Normalized (dlogTwoDimState p q g x) := by
  let P := p-1
  have hP : 0 < P := by dsimp [P]; omega
  have hq : 0 < q := by omega
  have hPq : P ≤ q := by dsimp [P]; omega
  let f := fun z : Fin P × Fin P => g ^ z.1.val * x ^ (P-z.2.val)
  let index := fun z : Fin P × Fin P => (Fin.castLE hPq z.1, Fin.castLE hPq z.2, f z)
  let G := TensorGate (QFTMatrix q) (TensorGate (QFTMatrix q) (1 : Matrix (ZMod p) (ZMod p) ℂ))
  let v := fun z : Fin P × Fin P => ApplyGate G (Ket (index z))
  have hG : G ∈ Matrix.unitaryGroup (Fin q × Fin q × ZMod p) ℂ :=
    tensorGate_unitary (qftMatrix_unitary hq) (tensorGate_unitary (qftMatrix_unitary hq) (Submonoid.one_mem _))
  have hindex : Function.Injective index := by
    intro z w h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun t : Fin q × Fin q × ZMod p => t.1.val) h
    · apply Fin.ext
      exact congrArg (fun t : Fin q × Fin q × ZMod p => t.2.1.val) h
  have hv (z w : Fin P × Fin P) : Inner (v z) (v w) = if z=w then 1 else 0 := by
    rw [inner_applyGate hG, inner_ket_ket]
    simp only [hindex.eq_iff]
  have hvalue (z : Fin P × Fin P) (t : Fin q × Fin q × ZMod p) :
      v z t = if f z = t.2.2 then
        offGridPhase q ((z.1.val : ℝ)/(q : ℝ)) t.1 *
          offGridPhase q ((z.2.val : ℝ)/(q : ℝ)) t.2.1 else 0 := by
    dsimp only [v]
    rw [applyGate_ket_entry]
    change QFTMatrix q t.1 (Fin.castLE hPq z.1) *
      (QFTMatrix q t.2.1 (Fin.castLE hPq z.2) * (1 : Matrix (ZMod p) (ZMod p) ℂ) t.2.2 (f z)) = _
    rw [dlog_qft_column, dlog_qft_column]
    by_cases h : f z = t.2.2
    · have hi : (1 : Matrix (ZMod p) (ZMod p) ℂ) t.2.2 (f z) = 1 := by
        rw [h]; simp
      simp only [if_pos h, hi, mul_one]
    · have hi : (1 : Matrix (ZMod p) (ZMod p) ℂ) t.2.2 (f z) = 0 := by
        simp only [Matrix.one_apply, if_neg (Ne.symm h)]
      simp only [if_neg h, hi, mul_zero]
  have hstate : dlogTwoDimState p q g x = ∑ z : Fin P × Fin P, ((P : ℂ)⁻¹) • v z := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvalue, Fintype.sum_prod_type]
    simp only [dlogTwoDimState, P, f, Finset.mul_sum]
  rw [hstate]
  unfold Normalized
  rw [sum_norm_sq_orthonormal v (fun _ => (P : ℂ)⁻¹) (fun z w => by
    by_cases h : z = w
    · simpa only [if_pos h] using hv z w
    · simpa only [if_neg h] using hv z w)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, norm_inv, Complex.norm_natCast]
  have hPc : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  push_cast
  field_simp

theorem dlog_generator_fiber (p : ℕ) [NeZero p] (g x : ZMod p) (hp : 1 < p)
    (ho : orderOf g = p-1) (r k : ℕ) (hx : x = g ^ r) (a b : Fin (p-1)) :
    g ^ a.val * x ^ (p-1-b.val) = g ^ k ↔ a.val = (r*b.val+k) % (p-1) := by
  have hg : IsOfFinOrder g := orderOf_pos_iff.mp (by rw [ho]; omega)
  have hb : b.val ≤ p-1 := Nat.le_of_lt b.isLt
  have hm : r * (p-1-b.val) + r*b.val = r*(p-1) := by
    rw [← mul_add, Nat.sub_add_cancel hb]
  rw [hx, ← pow_mul, ← pow_add, hg.pow_eq_pow_iff_modEq, ho]
  have he : Nat.ModEq (p-1) (a.val + r*(p-1-b.val)) k ↔
      Nat.ModEq (p-1) a.val (r*b.val+k) := by
    constructor
    · intro h
      have h' := h.add_right (r*b.val)
      have he : a.val + r*(p-1-b.val) + r*b.val = a.val + r*(p-1) := by omega
      rw [he] at h'
      simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod, add_comm] using h'
    · intro h
      have h' := h.add_right (r*(p-1-b.val))
      have he : r*b.val+k+r*(p-1-b.val) = k+r*(p-1) := by omega
      rw [he] at h'
      simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod] using h'
  rw [he]
  simp only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt]

theorem dlog_single_fiber_amplitude (p q : ℕ) [NeZero p] (g x : ZMod p)
    (hp : 1 < p) (hpq : p < q) (ho : orderOf g = p-1) (r k : ℕ)
    (hx : x = g ^ r) (c d : Fin q) :
    dlogTwoDimState p q g x (c, d, g ^ k) =
      ((p-1 : ℕ) : ℂ)⁻¹ * (q : ℂ)⁻¹ * ∑ b : Fin (p-1),
        Complex.exp (2*Real.pi*Complex.I*
          (((((r*b.val+k) % (p-1)) : ℕ) : ℝ)*c.val + (b.val : ℝ)*d.val)/(q : ℝ)) := by
  have hP : 0 < p-1 := by omega
  have hq : 0 < q := by omega
  let a := fun b : Fin (p-1) => (⟨(r*b.val+k)%(p-1), Nat.mod_lt _ hP⟩ : Fin (p-1))
  have hf (z b : Fin (p-1)) : g ^ z.val * x ^ (p-1-b.val) = g ^ k ↔ z = a b := by
    rw [dlog_generator_fiber p g x hp ho r k hx]
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  have hsum (b : Fin (p-1)) :
      (∑ z : Fin (p-1), if g ^ z.val * x ^ (p-1-b.val) = g ^ k then
        offGridPhase q ((z.val : ℝ)/(q : ℝ)) c * offGridPhase q ((b.val : ℝ)/(q : ℝ)) d else 0) =
      offGridPhase q (((a b).val : ℝ)/(q : ℝ)) c * offGridPhase q ((b.val : ℝ)/(q : ℝ)) d := by
    simp only [hf]
    simp
  have hphase (b : Fin (p-1)) : offGridPhase q (((a b).val : ℝ)/(q : ℝ)) c *
      offGridPhase q ((b.val : ℝ)/(q : ℝ)) d = (q : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*
          (((a b).val : ℝ)*c.val + (b.val : ℝ)*d.val)/(q : ℝ)) := by
    rw [offGridPhase, offGridPhase]
    push_cast
    calc
      _ = ((Real.sqrt (q : ℝ) : ℂ)⁻¹ * (Real.sqrt (q : ℝ) : ℂ)⁻¹) *
        (Complex.exp (2*Real.pi*Complex.I*((c.val : ℂ)*(((a b).val : ℂ)/(q : ℂ)))) *
          Complex.exp (2*Real.pi*Complex.I*((d.val : ℂ)*((b.val : ℂ)/(q : ℂ))))) := by ring
      _ = _ := by
        rw [inv_sqrt_mul_inv_sqrt hq, ← Complex.exp_add]
        congr 1
        congr 1
        ring
  unfold dlogTwoDimState
  rw [Finset.sum_comm]
  simp_rw [hsum, hphase]
  rw [← Finset.mul_sum]
  simp only [a, mul_assoc]

end Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

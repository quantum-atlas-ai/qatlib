/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath.BornBridge


namespace Qatlib.Concepts.QuditTeleport.TeleportCore

open Matrix
open scoped Classical

section Char

variable {N : ℕ} [NeZero N]

theorem stdAddChar_eq_primRoot_zpow (t : ZMod N) :
    ZMod.stdAddChar t = primRoot N ^ (t.val : ℤ) := by
  have hlift : ZMod.stdAddChar t
      = Complex.exp (2 * Real.pi * Complex.I * ((t.val : ℤ) : ℂ) / (N : ℂ)) := by
    conv_lhs => rw [show (t : ZMod N) = ((t.val : ℤ) : ZMod N) from by
      rw [show ((t.val : ℤ) : ZMod N) = ((t.val : ℕ) : ZMod N) from by push_cast; simp]
      exact (ZMod.natCast_zmod_val t).symm]
    rw [ZMod.stdAddChar_coe]
  have hpow : primRoot N ^ ((t.val : ℤ))
      = Complex.exp (((t.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I / (N : ℝ))) := by
    rw [primRoot, Complex.exp_int_mul]
  rw [hlift, hpow]
  congr 1
  have hNe : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  push_cast
  field_simp

theorem finEquiv_apply_val (i : Fin N) : (ZMod.finEquiv N) i = (i.val : ZMod N) := by
  have hN : 0 < N := NeZero.pos N
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  refine ZMod.val_injective (n := k + 1) ?_
  rw [show ((ZMod.finEquiv (k + 1)) i).val = i.val from rfl, ZMod.val_natCast,
    Nat.mod_eq_of_lt i.isLt]

theorem finEquiv_symm_apply_val (x : ZMod N) : ((ZMod.finEquiv N).symm x).val = x.val := by
  have hN : 0 < N := NeZero.pos N
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  rfl

theorem qftMatrix_apply' (M : ℕ) (hM : 0 < M) (x y : Fin M) :
    QFTMatrix M x y = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        Complex.exp (((2 * Real.pi * ((x.val * y.val : ℕ) : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [qftMatrix_apply, primRoot, ← Complex.exp_int_mul]
  have hNe : ((M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  congr 2
  push_cast
  field_simp

end Char

section Normalized

variable {N : ℕ} [NeZero N]

noncomputable def zmodQFT (u : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ∑ j : ZMod N, ZMod.stdAddChar (j * k) * u j

theorem zmodQFT_apply (u : ZMod N → ℂ) (k : ZMod N) :
    zmodQFT u k = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ∑ j : ZMod N, ZMod.stdAddChar (j * k) * u j :=
  rfl

theorem zmodQFT_apply_dft (u : ZMod N → ℂ) (k : ZMod N) :
    zmodQFT u k = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.dft u (-k) := by
  rw [zmodQFT_apply, ZMod.dft_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show -(j * (-k)) = j * k from by ring, smul_eq_mul]

noncomputable def zmodQFTInv (u : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.dft u k

theorem zmodQFTInv_apply (u : ZMod N → ℂ) (k : ZMod N) :
    zmodQFTInv u k = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.dft u k :=
  rfl

theorem dft_zmodQFT (u : ZMod N → ℂ) :
    ZMod.dft (zmodQFT u) = fun k => (Real.sqrt (N : ℝ) : ℂ) * u k := by
  have hu : zmodQFT u = (Real.sqrt (N : ℝ) : ℂ)⁻¹ • (fun k => ZMod.dft u (-k)) := by
    funext k
    rw [zmodQFT_apply_dft, Pi.smul_apply, smul_eq_mul]
  have hN : 0 < N := NeZero.pos N
  have hsq : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
    have h2 : ((Real.sqrt (N : ℝ) : ℂ)) ^ 2 = (N : ℂ) :=
      by exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN.le)
    rw [← h2, pow_two]
  rw [hu, ZMod.dft_const_smul, ← ZMod.dft_comp_neg (Φ := u), ZMod.dft_dft]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, neg_neg]
  rw [show (N : ℂ) = (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) from hsq.symm]
  field_simp

theorem zmodQFT_zmodQFT (u : ZMod N → ℂ) :
    zmodQFT (zmodQFT u) = fun k => u (-k) := by
  have hN : 0 < N := NeZero.pos N
  have hz : ((Real.sqrt (N : ℝ) : ℂ)) ≠ 0 := by
    have h0 : (0 : ℝ) < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.mpr (show (0 : ℝ) < N by exact_mod_cast hN)
    exact_mod_cast h0.ne'
  funext k
  rw [zmodQFT_apply_dft (zmodQFT u) k, dft_zmodQFT]
  rw [show ((fun k => (Real.sqrt (N : ℝ) : ℂ) * u k) (-k))
      = ((Real.sqrt (N : ℝ) : ℂ) * u (-k)) from rfl]
  rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

theorem zmodQFTInv_zmodQFT (u : ZMod N → ℂ) : zmodQFTInv (zmodQFT u) = u := by
  have hN : 0 < N := NeZero.pos N
  have hz : ((Real.sqrt (N : ℝ) : ℂ)) ≠ 0 := by
    have h0 : (0 : ℝ) < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.mpr (show (0 : ℝ) < N by exact_mod_cast hN)
    exact_mod_cast h0.ne'
  funext k
  rw [zmodQFTInv_apply, dft_zmodQFT]
  rw [show ((fun k => (Real.sqrt (N : ℝ) : ℂ) * u k) k)
      = ((Real.sqrt (N : ℝ) : ℂ) * u k) from rfl]
  rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

end Normalized

section RelabelGate

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in

theorem relabelGate_mul (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e A * relabelGate e B = relabelGate e (A * B) := by
  simp only [relabelGate, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm

omit [Fintype I] [Fintype J] in

theorem relabelGate_one (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  rw [relabelGate, Matrix.reindex_apply]
  exact Matrix.submatrix_one_equiv e.symm

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in

theorem relabelGate_conjTranspose (e : I ≃ J) (A : Matrix I I ℂ) :
    (relabelGate e A)ᴴ = relabelGate e Aᴴ :=
  Matrix.conjTranspose_reindex e e A

end RelabelGate

theorem qftMatrix_mul_conjTranspose (M : ℕ) (hM : 0 < M) :
    QFTMatrix M * (QFTMatrix M)ᴴ = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (qftMatrix_unitary hM)
  rw [Matrix.star_eq_conjTranspose] at h
  exact mul_eq_one_comm.mp h

section Gate

variable {N : ℕ} [NeZero N]

omit [NeZero N] in

theorem primRoot_zpow_zmod (hN : 0 < N) {a b : ℤ} (h : (a - b) % (N : ℤ) = 0) :
    primRoot N ^ a = primRoot N ^ b := by
  have hone := (primRoot_zpow_eq_one_iff hN _).mpr (Int.dvd_iff_emod_eq_zero.mpr h)
  rw [show a = a - b + b from by ring, zpow_add₀ (primRoot_ne_zero N), hone, one_mul]

omit [NeZero N] in

theorem primRoot_zpow_natCast_mod (hN : 0 < N) (m : ℕ) :
    primRoot N ^ ((m : ℤ)) = primRoot N ^ (((m % N : ℕ) : ℤ)) := by
  have hm : (m % N) + N * (m / N) = m := Nat.mod_add_div m N
  refine primRoot_zpow_zmod hN ?_
  have hconv : (((m : ℤ)) - (((m % N : ℕ) : ℤ))) = ((N * (m / N : ℕ)) : ℤ) := by
    have hm' : ((m % N : ℕ) : ℤ) + (N : ℤ) * ((m / N : ℕ) : ℤ) = (m : ℤ) :=
      by exact_mod_cast hm
    linarith
  rw [hconv]
  simp

theorem conj_stdAddChar (t : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  exact (ZMod.stdAddChar.map_neg_eq_conj t).symm

theorem norm_stdAddChar (t : ZMod N) : ‖ZMod.stdAddChar t‖ = 1 := by
  exact ZMod.stdAddChar.norm_apply t

theorem qftMatrix_stdAddChar (x y : ZMod N) :
    QFTMatrix N ((ZMod.finEquiv N).symm x) ((ZMod.finEquiv N).symm y)
      = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (x * y) := by
  have hN : 0 < N := NeZero.pos N
  rw [qftMatrix_apply, stdAddChar_eq_primRoot_zpow (x * y), ZMod.val_mul,
    finEquiv_symm_apply_val, finEquiv_symm_apply_val,
    show ((x.val : ℤ) * (y.val : ℤ)) = (((x.val * y.val : ℕ) : ℤ)) from by push_cast; ring,
    primRoot_zpow_natCast_mod hN (x.val * y.val)]

noncomputable def zmodQFTGate : Matrix (ZMod N) (ZMod N) ℂ :=
  relabelGate (ZMod.finEquiv N).toEquiv (QFTMatrix N)

theorem zmodQFTGate_eq_relabelGate :
    zmodQFTGate (N := N) = relabelGate (ZMod.finEquiv N).toEquiv (QFTMatrix N) :=
  rfl

theorem zmodQFTGate_apply (x y : ZMod N) :
    zmodQFTGate x y = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (x * y) := by
  exact qftMatrix_stdAddChar x y

theorem applyGate_zmodQFTGate (u : QState (ZMod N)) : ApplyGate zmodQFTGate u = zmodQFT u := by
  funext k
  simp only [ApplyGate, zmodQFT, Matrix.mulVec, dotProduct, zmodQFTGate_apply,
    mul_assoc, ← Finset.mul_sum, mul_comm k]

theorem zmodQFTGate_unitary (hN : 0 < N) : zmodQFTGate ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, zmodQFTGate_eq_relabelGate,
    relabelGate_conjTranspose, relabelGate_mul]
  have h := (Matrix.mem_unitaryGroup_iff').mp (qftMatrix_unitary hN)
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h, relabelGate_one]

theorem applyGate_zmodQFTGate_conjTranspose (u : QState (ZMod N)) :
    ApplyGate (zmodQFTGate (N := N))ᴴ u = zmodQFTInv u := by
  funext k
  simp only [ApplyGate, zmodQFTInv, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    zmodQFTGate_apply, ZMod.dft_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal, conj_stdAddChar]
  ring

theorem zmodQFTGate_mul_conjTranspose (hN : 0 < N) :
    zmodQFTGate (N := N) * (zmodQFTGate (N := N))ᴴ = 1 := by
  rw [zmodQFTGate_eq_relabelGate, relabelGate_conjTranspose, relabelGate_mul,
    qftMatrix_mul_conjTranspose N hN, relabelGate_one]

theorem zmodQFT_zmodQFTInv (u : QState (ZMod N)) : zmodQFT (zmodQFTInv u) = u := by
  rw [← applyGate_zmodQFTGate (zmodQFTInv u), ← applyGate_zmodQFTGate_conjTranspose u]
  simp only [ApplyGate, Matrix.mulVec_mulVec,
    zmodQFTGate_mul_conjTranspose (NeZero.pos N), Matrix.one_mulVec]

end Gate

section Equivariance

variable {N : ℕ} [NeZero N]

theorem zmodQFT_comp_unitsMul (u : ZMod N → ℂ) (a : (ZMod N)ˣ) (k : ZMod N) :
    zmodQFT (fun j => u (a.val * j)) k = zmodQFT u (a⁻¹.val * k) := by
  rw [zmodQFT_apply_dft (fun j => u (a.val * j)) k, ZMod.dft_comp_unitMul u a (-k),
    show a⁻¹.val * (-k) = -(a⁻¹.val * k) from by ring, ← zmodQFT_apply_dft u (a⁻¹.val * k)]

theorem zmodQFT_comp_add (u : ZMod N → ℂ) (s k : ZMod N) :
    zmodQFT (fun x => u (x + s)) k = ZMod.stdAddChar (-(k * s)) * zmodQFT u k := by
  rw [zmodQFT_apply (fun x => u (x + s)) k, zmodQFT_apply u k]
  have hperm : ∑ x : ZMod N, ZMod.stdAddChar (x * k) * u (x + s)
      = ZMod.stdAddChar (-(k * s)) * ∑ y : ZMod N, ZMod.stdAddChar (y * k) * u y := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight s) _ _ ?_
    intro x
    change ZMod.stdAddChar (x * k) * u (x + s) =
      ZMod.stdAddChar (-(k * s)) * (ZMod.stdAddChar ((x + s) * k) * u (x + s))
    rw [show (x + s) * k = x * k + k * s from by ring, AddChar.map_add_eq_mul,
      show ZMod.stdAddChar (-(k * s))
            * (ZMod.stdAddChar (x * k) * ZMod.stdAddChar (k * s) * u (x + s))
          = (ZMod.stdAddChar (-(k * s)) * ZMod.stdAddChar (k * s))
            * (ZMod.stdAddChar (x * k) * u (x + s)) from by ring,
      ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  rw [hperm]
  ring

end Equivariance

section Sampling

variable {N : ℕ} [NeZero N]

def annihilatorOf (H : AddSubgroup (ZMod N)) : AddSubgroup (ZMod N) where
  carrier := {t | ∀ h ∈ H, t * h = 0}
  add_mem' := by
    intro a b ha hb h hh
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_mul, ha h hh, hb h hh, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro h _
    rw [zero_mul]
  neg_mem' := by
    intro a ha h hh
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_mul, ha h hh, neg_zero]

omit [NeZero N] in

theorem mem_annihilatorOf {H : AddSubgroup (ZMod N)} {t : ZMod N} :
    t ∈ annihilatorOf H ↔ ∀ ⦃h : ZMod N⦄, h ∈ H → t * h = 0 :=
  Iff.rfl

theorem sum_ite_subtype {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype (Subtype p)] (g : α → M) :
    ∑ x : α, (if p x then g x else 0) = ∑ y : Subtype p, g (y : α) := by
  classical
  rw [show ∑ x : α, (if p x then g x else 0) = ∑ x ∈ Finset.univ.filter p, g x from by
      rw [Finset.sum_filter]]
  exact Finset.sum_subtype _ (fun x => by simp [Finset.mem_filter]) g

theorem sum_stdAddChar_subgroup (H : AddSubgroup (ZMod N)) [Fintype ↥H] (t : ZMod N) :
    ∑ h : ↥H, ZMod.stdAddChar (t * (h : ZMod N)) =
      if t ∈ annihilatorOf H then (Fintype.card ↥H : ℂ) else 0 := by
  have hψ : ∀ h : ↥H, (ZMod.stdAddChar.compAddMonoidHom ((AddMonoidHom.mulLeft t).comp H.subtype)
      : AddChar ↥H ℂ) h = ZMod.stdAddChar (t * (h : ZMod N)) := fun h => rfl
  have hzero : (ZMod.stdAddChar.compAddMonoidHom ((AddMonoidHom.mulLeft t).comp H.subtype)
      : AddChar ↥H ℂ) = 0 ↔ t ∈ annihilatorOf H := by
    constructor
    · intro h0
      refine mem_annihilatorOf.mpr fun h hh => ?_
      have h1 : ((ZMod.stdAddChar.compAddMonoidHom ((AddMonoidHom.mulLeft t).comp H.subtype)
          : AddChar ↥H ℂ) : ↥H → ℂ) ⟨h, hh⟩
          = ((0 : AddChar ↥H ℂ) : ↥H → ℂ) ⟨h, hh⟩ := by rw [h0]
      rw [AddChar.zero_apply] at h1
      rw [hψ ⟨h, hh⟩] at h1
      exact ZMod.injective_stdAddChar
        (by simpa using h1)
    · intro ht
      have hcoe : ((ZMod.stdAddChar.compAddMonoidHom ((AddMonoidHom.mulLeft t).comp H.subtype)
          : AddChar ↥H ℂ) : ↥H → ℂ)
          = ((0 : AddChar ↥H ℂ) : ↥H → ℂ) := by
        funext h
        rw [hψ h, AddChar.zero_apply, mem_annihilatorOf.mp ht h.2,
          AddChar.map_zero_eq_one]
      exact DFunLike.coe_injective hcoe
  rw [Finset.sum_congr rfl (fun h _ => (hψ h).symm), AddChar.sum_eq_ite]
  simp only [hzero]

theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ x : ZMod N, ZMod.stdAddChar (t * x) = if t = 0 then (N : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht]
  · simpa only [if_neg ht] using!
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ht)

noncomputable def charState (j : ZMod N) : QState (ZMod N) :=
  fun x => (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (j * x)

theorem charState_apply (j x : ZMod N) :
    charState j x = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (j * x) :=
  rfl

theorem normalized_charState (j : ZMod N) : Normalized (charState j) := by
  have hN : 0 < N := NeZero.pos N
  unfold Normalized
  have hterm : ∀ x : ZMod N, ‖charState j x‖ ^ 2 = (N : ℝ)⁻¹ := by
    intro x
    rw [charState_apply, norm_mul, mul_pow, norm_stdAddChar, one_pow,
      show ((Real.sqrt (N : ℝ) : ℂ)⁻¹) = ((Real.sqrt (N : ℝ))⁻¹ : ℝ) from by
        rw [Complex.ofReal_inv],
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN.le), mul_one]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul,
    show (N : ℝ) * (N : ℝ)⁻¹ = 1 from mul_inv_cancel₀ (by exact_mod_cast (NeZero.ne N))]

theorem zmodQFT_charState (j : ZMod N) : zmodQFT (charState j) = Ket (-j) := by
  have hN : 0 < N := NeZero.pos N
  have hsq : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
    have h2 : ((Real.sqrt (N : ℝ) : ℂ)) ^ 2 = (N : ℂ) :=
      by exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN.le)
    rw [← h2, pow_two]
  have hne : ((Real.sqrt (N : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < N by exact_mod_cast hN)).ne'
  funext k
  have hterm : ∀ x : ZMod N,
      ZMod.stdAddChar (x * k) * (charState j x)
        = (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar ((k + j) * x) := by
    intro x
    rw [charState_apply, show (k + j) * x = x * k + j * x from by ring,
      AddChar.map_add_eq_mul]
    ring
  show (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ∑ x : ZMod N, ZMod.stdAddChar (x * k) * charState j x
      = Ket (-j) k
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum, sum_stdAddChar_mul (k + j)]
  by_cases hk : k + j = 0
  · have hk' : k = -j := eq_neg_of_add_eq_zero_left hk
    simp only [if_pos hk, Ket, if_pos hk']
    rw [← hsq]
    field_simp
  · have hk' : k ≠ -j := fun h => hk (by rw [h]; ring)
    simp [hk, Ket, hk']

theorem measureProb_zmodQFTGate_charState (j : ZMod N) :
    MeasureProb (ApplyGate zmodQFTGate (charState j)) ({-j} : Finset (ZMod N)) = 1 := by
  rw [applyGate_zmodQFTGate, zmodQFT_charState]
  simp [MeasureProb, bornProb_ket]

noncomputable def subgroupCharState (H : AddSubgroup (ZMod N)) [Fintype ↥H] (j : ZMod N) :
    QState (ZMod N) :=
  fun x => if x ∈ H
    then (Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (j * x) else 0

theorem subgroupCharState_apply_of_mem {H : AddSubgroup (ZMod N)} [Fintype ↥H]
    {x : ZMod N} (hx : x ∈ H) (j : ZMod N) :
    subgroupCharState H j x = (Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)⁻¹
      * ZMod.stdAddChar (j * x) := by
  rw [subgroupCharState, if_pos hx]

theorem subgroupCharState_apply_of_not_mem {H : AddSubgroup (ZMod N)} [Fintype ↥H]
    {x : ZMod N} (hx : x ∉ H) (j : ZMod N) :
    subgroupCharState H j x = 0 := by
  rw [subgroupCharState, if_neg hx]

theorem normalized_subgroupCharState {H : AddSubgroup (ZMod N)} [Fintype ↥H]
    (j : ZMod N) : Normalized (subgroupCharState H j) := by
  haveI : Nonempty ↥H := ⟨⟨(0 : ZMod N), H.zero_mem⟩⟩
  have hcardpos : (0 : ℝ) < (Fintype.card ↥H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcardne : (Fintype.card ↥H : ℝ) ≠ 0 := ne_of_gt hcardpos
  unfold Normalized
  have hterm : ∀ x : ZMod N, ‖subgroupCharState H j x‖ ^ 2
      = if x ∈ H then (Fintype.card ↥H : ℝ)⁻¹ else 0 := by
    intro x
    by_cases hx : x ∈ H
    · rw [subgroupCharState_apply_of_mem hx, norm_mul, mul_pow, norm_stdAddChar, one_pow,
        show ((Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)⁻¹)
            = ((Real.sqrt (Fintype.card ↥H : ℝ))⁻¹ : ℝ) from by rw [Complex.ofReal_inv],
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
        Real.sq_sqrt hcardpos.le, if_pos hx, mul_one]
    · rw [subgroupCharState_apply_of_not_mem hx]
      simp only [norm_zero, if_neg hx]
      ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x),
    sum_ite_subtype (p := (· ∈ H)) (fun _ => (Fintype.card ↥H : ℝ)⁻¹),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ hcardne]

theorem applyGate_zmodQFTGate_subgroupCharState {H : AddSubgroup (ZMod N)} [Fintype ↥H]
    (j k : ZMod N) :
    ApplyGate zmodQFTGate (subgroupCharState H j) k =
      if k + j ∈ annihilatorOf H
      then (Real.sqrt (Fintype.card ↥H : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ)⁻¹
      else 0 := by
  haveI : Nonempty ↥H := ⟨⟨(0 : ZMod N), H.zero_mem⟩⟩
  have hcardpos : (0 : ℝ) < (Fintype.card ↥H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hzC : ((Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hcardpos).ne'
  have hzN : ((Real.sqrt (N : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < N by exact_mod_cast NeZero.pos N)).ne'
  have hterm : ∀ h : ↥H,
      (zmodQFTGate k (h : ZMod N)) * (subgroupCharState H j (h : ZMod N))
        = ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)⁻¹)
          * ZMod.stdAddChar ((k + j) * (h : ZMod N)) := by
    intro h
    rw [zmodQFTGate_apply, subgroupCharState_apply_of_mem h.2,
      show (k + j) * (h : ZMod N) = k * (h : ZMod N) + j * (h : ZMod N) from by ring,
      AddChar.map_add_eq_mul]
    ring
  have hite : ∀ x : ZMod N,
      zmodQFTGate k x * subgroupCharState H j x
        = if x ∈ H then zmodQFTGate k x * subgroupCharState H j x else 0 := by
    intro x
    by_cases hx : x ∈ H
    · rw [if_pos hx]
    · rw [subgroupCharState_apply_of_not_mem hx, mul_zero, if_neg hx]
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun x _ => hite x),
    sum_ite_subtype (p := (· ∈ H)) (fun h => zmodQFTGate k h * subgroupCharState H j h),
    Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.mul_sum,
    sum_stdAddChar_subgroup H (k + j)]
  by_cases hmem : k + j ∈ annihilatorOf H
  · simp only [if_pos hmem]
    have hcard : ((Fintype.card ↥H : ℂ))
        = ((Real.sqrt (Fintype.card ↥H : ℝ) : ℂ))
          * ((Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)) := by
      have h2 : ((Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)) ^ 2 = (Fintype.card ↥H : ℂ) :=
        by exact_mod_cast Real.sq_sqrt hcardpos.le
      rw [← h2, pow_two]
    rw [hcard]
    field_simp
  · simp only [if_neg hmem, mul_zero]

theorem bornProb_zmodQFTGate_subgroupCharState {H : AddSubgroup (ZMod N)} [Fintype ↥H]
    (j k : ZMod N) :
    BornProb (ApplyGate zmodQFTGate (subgroupCharState H j)) k =
      if k + j ∈ annihilatorOf H then (Fintype.card ↥H : ℝ) / (N : ℝ) else 0 := by
  rw [BornProb, applyGate_zmodQFTGate_subgroupCharState (H := H) j k]
  split_ifs <;> simp only [norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

theorem card_annihilatorOf {H : AddSubgroup (ZMod N)} [Fintype ↥H] :
    Fintype.card ↥(annihilatorOf H) * Fintype.card ↥H = N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hnorm := normalized_applyGate (zmodQFTGate_unitary (NeZero.pos N))
    (normalized_subgroupCharState (H := H) 0)
  have hsum : (∑ k : ZMod N, BornProb (ApplyGate zmodQFTGate (subgroupCharState H 0)) k)
      = 1 := by
    have := measureProb_univ hnorm
    simpa [MeasureProb] using this
  have hpoint : ∀ k : ZMod N, BornProb (ApplyGate zmodQFTGate (subgroupCharState H 0)) k
      = if k ∈ annihilatorOf H then (Fintype.card ↥H : ℝ) / (N : ℝ) else 0 := by
    intro k
    have h := bornProb_zmodQFTGate_subgroupCharState (H := H) 0 k
    rw [add_zero] at h
    exact h
  rw [Finset.sum_congr rfl (fun k _ => hpoint k),
    sum_ite_subtype (p := (· ∈ annihilatorOf H))
      (fun _ => (Fintype.card ↥H : ℝ) / (N : ℝ)),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [mul_div_assoc', div_eq_iff hN, one_mul] at hsum
  exact_mod_cast hsum

noncomputable def cosetState (H : AddSubgroup (ZMod N)) [Fintype ↥H] (s : ZMod N) :
    QState (ZMod N) :=
  fun x => if x - s ∈ H then (Real.sqrt (Fintype.card ↥H : ℝ) : ℂ)⁻¹ else 0

theorem cosetState_eq (H : AddSubgroup (ZMod N)) [Fintype ↥H] (s : ZMod N) :
    cosetState H s = fun x => subgroupCharState H 0 (x + (-s)) := by
  funext x
  by_cases hx : x - s ∈ H
  · rw [cosetState, subgroupCharState]
    rw [if_pos hx, if_pos (by rwa [show x + (-s) = x - s from (sub_eq_add_neg x s).symm]),
      zero_mul, AddChar.map_zero_eq_one, mul_one]
  · rw [cosetState, subgroupCharState]
    rw [if_neg hx, if_neg (by rwa [show x + (-s) = x - s from (sub_eq_add_neg x s).symm])]

theorem normalized_cosetState (H : AddSubgroup (ZMod N)) [Fintype ↥H] (s : ZMod N) :
    Normalized (cosetState H s) := by
  have hφ := normalized_subgroupCharState (H := H) 0
  unfold Normalized at hφ ⊢
  rw [cosetState_eq]
  exact (Fintype.sum_equiv (Equiv.addRight (-s)) _ _ (fun x => rfl)).trans hφ

theorem applyGate_zmodQFTGate_cosetState (H : AddSubgroup (ZMod N)) [Fintype ↥H]
    (s k : ZMod N) :
    ApplyGate zmodQFTGate (cosetState H s) k
      = if k ∈ annihilatorOf H
        then ZMod.stdAddChar (k * s)
          * ((Real.sqrt (Fintype.card ↥H : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ)⁻¹)
        else 0 := by
  rw [applyGate_zmodQFTGate, cosetState_eq, zmodQFT_comp_add _ (-s) k,
    show -(k * (-s)) = k * s from by ring,
    ← applyGate_zmodQFTGate (subgroupCharState H 0),
    applyGate_zmodQFTGate_subgroupCharState (H := H) 0 k, add_zero]
  by_cases hmem : k ∈ annihilatorOf H
  · simp only [if_pos hmem]
  · simp only [if_neg hmem, mul_zero]

theorem bornProb_zmodQFTGate_cosetState (H : AddSubgroup (ZMod N)) [Fintype ↥H]
    (s k : ZMod N) :
    BornProb (ApplyGate zmodQFTGate (cosetState H s)) k =
      if k ∈ annihilatorOf H then (Fintype.card ↥H : ℝ) / (N : ℝ) else 0 := by
  rw [BornProb, applyGate_zmodQFTGate_cosetState H s k]
  split_ifs <;> simp only [norm_mul, mul_pow, norm_inv, norm_stdAddChar, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

end Sampling

section FiniteAbelian
variable {G : Type*} [AddCommGroup G] [Fintype G]

def restrictCharacter (H : AddSubgroup G) : AddChar G ℂ →+ AddChar H ℂ where
  toFun χ := χ.compAddMonoidHom H.subtype
  map_zero' := by ext; simp
  map_add' χ ψ := by ext; simp

def characterAnnihilator (H : AddSubgroup G) : AddSubgroup (AddChar G ℂ) :=
  (restrictCharacter H).ker

omit [Fintype G] in

theorem mem_characterAnnihilator (H : AddSubgroup G) (χ : AddChar G ℂ) :
    χ ∈ characterAnnihilator H ↔ ∀ h : H, χ h = 1 := by
  change χ.compAddMonoidHom H.subtype = 0 ↔ _
  simp only [DFunLike.ext_iff, AddChar.compAddMonoidHom_apply, AddSubgroup.subtype_apply,
    AddChar.zero_apply]

theorem sum_character_subgroup (H : AddSubgroup G) (χ : AddChar G ℂ) :
    ∑ h : H, χ h = if χ ∈ characterAnnihilator H then (Fintype.card H : ℂ) else 0 := by
  exact AddChar.sum_eq_ite (χ.compAddMonoidHom H.subtype)

theorem sum_character_mul_conj (χ ψ : AddChar G ℂ) :
    ∑ x : G, χ x * star (ψ x) = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  simpa only [AddChar.sub_apply, AddChar.map_neg_eq_conj, RCLike.star_def,
    sub_eq_zero] using AddChar.sum_eq_ite (χ - ψ)

theorem sum_character_eval_mul_conj (x y : G) :
    ∑ χ : AddChar G ℂ, χ x * star (χ y) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  simpa only [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj,
    RCLike.star_def, sub_eq_zero] using AddChar.sum_apply_eq_ite (x - y)

noncomputable def abelianQFTMatrix : Matrix (AddChar G ℂ) G ℂ :=
  fun χ x => (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ * χ x

noncomputable def abelianQFT (u : QState G) : QState (AddChar G ℂ) :=
  (abelianQFTMatrix (G := G)) *ᵥ u

omit [AddCommGroup G] in

private theorem inv_sqrt_card_sq :
    ((Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹) ^ 2 = (Fintype.card G : ℂ)⁻¹ := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem abelianQFTMatrix_mul_conjTranspose :
    (abelianQFTMatrix (G := G)) * (abelianQFTMatrix (G := G))ᴴ = 1 := by
  ext χ ψ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, abelianQFTMatrix,
    star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal, Matrix.one_apply]
  calc
    _ = ((Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹)^2 *
        ∑ x : G, χ x * star (ψ x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Complex.star_def]
      ring
    _ = _ := by
      rw [inv_sqrt_card_sq, sum_character_mul_conj]
      split_ifs <;> simp [Fintype.card_ne_zero]

theorem abelianQFTMatrix_conjTranspose_mul :
    (abelianQFTMatrix (G := G))ᴴ * (abelianQFTMatrix (G := G)) = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, abelianQFTMatrix,
    star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal, Matrix.one_apply]
  calc
    _ = ((Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹)^2 *
        ∑ χ : AddChar G ℂ, χ y * star (χ x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Complex.star_def]
      ring
    _ = _ := by
      rw [inv_sqrt_card_sq, sum_character_eval_mul_conj]
      by_cases h : x = y
      · simp [h, Fintype.card_ne_zero]
      · simp [h, Ne.symm h]

noncomputable def abelianQFTInv (u : QState (AddChar G ℂ)) : QState G :=
  (abelianQFTMatrix (G := G))ᴴ *ᵥ u

theorem abelianQFTInv_abelianQFT (u : QState G) : abelianQFTInv (abelianQFT u) = u := by
  rw [abelianQFTInv, abelianQFT, Matrix.mulVec_mulVec, abelianQFTMatrix_conjTranspose_mul,
    Matrix.one_mulVec]

theorem abelianQFT_abelianQFTInv (u : QState (AddChar G ℂ)) :
    abelianQFT (abelianQFTInv u) = u := by
  rw [abelianQFT, abelianQFTInv, Matrix.mulVec_mulVec, abelianQFTMatrix_mul_conjTranspose,
    Matrix.one_mulVec]

theorem inner_abelianQFT (u v : QState G) :
    Qatlib.Foundations.PureStateMath.Inner (abelianQFT u) (abelianQFT v) = Qatlib.Foundations.PureStateMath.Inner u v := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, abelianQFT]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    abelianQFTMatrix_conjTranspose_mul, Matrix.vecMul_one]

theorem normalized_abelianQFT {u : QState G} (hu : Normalized u) :
    Normalized (abelianQFT u) := by
  rw [normalized_iff_inner_self, inner_abelianQFT]
  exact (normalized_iff_inner_self u).mp hu

noncomputable def abelianCosetState (H : AddSubgroup G) (s : G) : QState G :=
  fun x => if x - s ∈ H then (Real.sqrt (Fintype.card H : ℝ) : ℂ)⁻¹ else 0

private theorem sum_ite_subgroup {A : Type*} [AddCommMonoid A]
    (H : AddSubgroup G) (f : G → A) :
    ∑ x : G, (if x ∈ H then f x else 0) = ∑ h : H, f h := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem abelianQFT_cosetState (H : AddSubgroup G) (s : G) (χ : AddChar G ℂ) :
    abelianQFT (abelianCosetState H s) χ =
      if χ ∈ characterAnnihilator H then
        χ s * ((Real.sqrt (Fintype.card H : ℝ) : ℂ) *
          (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹) else 0 := by
  have hsum : ∑ x : G, χ x * abelianCosetState H s x =
      ∑ h : H, χ (s + h) * (Real.sqrt (Fintype.card H : ℝ) : ℂ)⁻¹ := by
    calc
      _ = ∑ x : G, χ (s + x) * abelianCosetState H s (s + x) := by
        exact (Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun _ => rfl)).symm
      _ = ∑ x : G, if x ∈ H then χ (s + x) *
          (Real.sqrt (Fintype.card H : ℝ) : ℂ)⁻¹ else 0 := by
        simp only [abelianCosetState, add_sub_cancel_left, mul_ite, mul_zero]
      _ = _ := sum_ite_subgroup H _
  have hcard : (Fintype.card H : ℂ) =
      (Real.sqrt (Fintype.card H : ℝ) : ℂ)^2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hne : (Real.sqrt (Fintype.card H : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < Fintype.card H by
      exact_mod_cast Fintype.card_pos)).ne'
  simp only [abelianQFT, abelianQFTMatrix, Matrix.mulVec, dotProduct, mul_assoc,
    ← Finset.mul_sum]
  rw [hsum]
  simp only [AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_character_subgroup]
  by_cases hχ : χ ∈ characterAnnihilator H
  · simp only [if_pos hχ]
    rw [hcard]
    field_simp
  · simp [hχ]

theorem bornProb_abelianQFT_cosetState (H : AddSubgroup G) (s : G)
    (χ : AddChar G ℂ) :
    BornProb (abelianQFT (abelianCosetState H s)) χ =
      if χ ∈ characterAnnihilator H then
        (Fintype.card H : ℝ) / (Fintype.card G : ℝ) else 0 := by
  rw [BornProb, abelianQFT_cosetState]
  split_ifs <;> simp only [norm_mul, mul_pow, norm_inv, χ.norm_apply, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

theorem normalized_abelianCosetState (H : AddSubgroup G) (s : G) :
    Normalized (abelianCosetState H s) := by
  unfold Normalized
  calc
    _ = ∑ x : G, ‖abelianCosetState H s (s + x)‖ ^ 2 := by
      exact (Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun _ => rfl)).symm
    _ = ∑ x : G, if x ∈ H then (Fintype.card H : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [abelianCosetState, add_sub_cancel_left]
      split_ifs <;> simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
        norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    _ = ∑ _ : H, (Fintype.card H : ℝ)⁻¹ := sum_ite_subgroup H _
    _ = 1 := by simp [Fintype.card_ne_zero]

theorem card_characterAnnihilator (H : AddSubgroup G) :
    Fintype.card (characterAnnihilator H) * Fintype.card H = Fintype.card G := by
  have h := normalized_abelianQFT (normalized_abelianCosetState H 0)
  change (∑ χ : AddChar G ℂ, BornProb (abelianQFT (abelianCosetState H 0)) χ) = 1 at h
  simp_rw [bornProb_abelianQFT_cosetState] at h
  rw [sum_ite_subgroup, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_div_assoc, div_eq_iff (by exact_mod_cast Fintype.card_ne_zero (α := G)),
    one_mul] at h
  exact_mod_cast h

noncomputable def abelianCharacterState (χ : AddChar G ℂ) : QState G :=
  fun x => (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ * χ x

theorem abelianQFT_characterState (χ : AddChar G ℂ) :
    abelianQFT (abelianCharacterState χ) = Ket (-χ) := by
  funext ψ
  simp only [abelianQFT, abelianQFTMatrix, abelianCharacterState, Matrix.mulVec, dotProduct]
  calc
    _ = ((Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹)^2 *
        ∑ x : G, (ψ + χ) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [AddChar.add_apply]
      ring
    _ = _ := by
      rw [inv_sqrt_card_sq, AddChar.sum_eq_ite]
      by_cases h : ψ + χ = 0
      · have heq : ψ = -χ := eq_neg_of_add_eq_zero_left h
        simp [Ket, heq, Fintype.card_ne_zero]
      · have heq : ψ ≠ -χ := fun hh => h (by simp [hh])
        simp [h, Ket, heq]

end FiniteAbelian

theorem zmodAddEquiv_apply_stdAddChar {N : ℕ} [NeZero N] (k x : ZMod N) :
    (AddChar.zmodAddEquiv k) x = ZMod.stdAddChar (k * x) := by
  rfl

theorem abelianQFT_zmodAddEquiv {N : ℕ} [NeZero N] (u : QState (ZMod N)) (k : ZMod N) :
    abelianQFT u (AddChar.zmodAddEquiv k) = zmodQFT u k := by
  simp only [abelianQFT, abelianQFTMatrix, Matrix.mulVec, dotProduct, ZMod.card,
    zmodAddEquiv_apply_stdAddChar, zmodQFT, mul_assoc, ← Finset.mul_sum, mul_comm k]

theorem zmodAddEquiv_mem_characterAnnihilator {N : ℕ} [NeZero N]
    (H : AddSubgroup (ZMod N)) (k : ZMod N) :
    AddChar.zmodAddEquiv k ∈ characterAnnihilator H ↔ k ∈ annihilatorOf H := by
  rw [mem_characterAnnihilator, mem_annihilatorOf]
  constructor
  · intro h x hx
    apply ZMod.injective_stdAddChar
    simpa only [zmodAddEquiv_apply_stdAddChar, AddChar.map_zero_eq_one] using h ⟨x, hx⟩
  · intro h x
    rw [zmodAddEquiv_apply_stdAddChar, h x.property, AddChar.map_zero_eq_one]

theorem normalized_abelianCharacterState {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) : Normalized (abelianCharacterState χ) := by
  rw [normalized_iff_inner_self, ← inner_abelianQFT, abelianQFT_characterState]
  exact (normalized_iff_inner_self _).mp (normalized_ket (-χ))

end Qatlib.Concepts.QuditTeleport.TeleportCore

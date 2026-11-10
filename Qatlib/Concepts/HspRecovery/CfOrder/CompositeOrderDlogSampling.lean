/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.BackendAudit.CountedCharacterTableDecoder
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
set_option warningAsError false
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree

namespace Qatlib.Concepts.HspRecovery.CfOrder

open Matrix
open scoped Classical

variable {p : ℕ}

private theorem cyclic_pos {p : ℕ} [NeZero p] : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)

private theorem nsmul_mul_nat {C : Type} [AddCommGroup C] (n m : ℕ) (a : C) :
    (n * m) • a = n • (m • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1) * m = n * m + m := by ring
    rw [h, add_nsmul, ih]
    simp only [succ_nsmul]

private theorem nsmul_mul_mod {C : Type} [AddCommGroup C] (a : C) (hp : (p : ℕ) • a = 0)
    (m : ℕ) : m • a = (m % p) • a := by
  calc
    m • a = ((m / p * p + m % p) : ℕ) • a := by
      have h := Nat.div_add_mod m p
      rw [mul_comm p (m / p)] at h
      rw [h]
    _ = (m / p * p) • a + (m % p) • a := add_nsmul _ _ _
    _ = 0 + (m % p) • a := by
      rw [nsmul_mul_nat, hp, smul_zero]
    _ = (m % p) • a := by simp

private theorem stdAddChar_val {p : ℕ} [NeZero p] (j : ZMod p) :
    ZMod.stdAddChar (N := p) j = Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) / (p : ℝ))) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  field_simp

private theorem stdAddChar_eq_one_iff {p : ℕ} [NeZero p] (j : ZMod p) :
    ZMod.stdAddChar (N := p) j = 1 ↔ j = 0 := by
  haveI : NeZero p := ⟨NeZero.ne p⟩
  rw [stdAddChar_val]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have hP : ((p : ℕ) : ℂ) ≠ 0 := by
      intro hz
      exact NeZero.ne p (by exact_mod_cast hz)
    have h1 : (2 * (Real.pi : ℂ) * Complex.I) * ((j.val : ℕ) : ℂ) * ((p : ℕ) : ℂ)⁻¹ =
        ((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [div_eq_mul_inv, ← mul_assoc] at hn
      exact hn
    have hdiv : (2 * (Real.pi : ℂ) * Complex.I) * ((j.val : ℕ) : ℂ) =
        ((n : ℤ) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I) * ((p : ℕ) : ℂ)) := by
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * ((j.val : ℕ) : ℂ) =
            ((2 * (Real.pi : ℂ) * Complex.I) * ((j.val : ℕ) : ℂ) * ((p : ℕ) : ℂ)⁻¹) *
              ((p : ℕ) : ℂ) := by field_simp
        _ = (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * ((p : ℕ) : ℂ) := by rw [h1]
        _ = ((n : ℤ) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I) * ((p : ℕ) : ℂ)) := by ring
    have hW : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      intro hz
      have h1 := (mul_eq_zero.mp hz : ((2 : ℂ) * (Real.pi : ℂ)) = 0 ∨ Complex.I = 0)
      rcases h1 with h1 | h1
      · have h2 : (2 : ℝ) * Real.pi = 0 := by exact_mod_cast h1
        linarith [Real.pi_pos]
      · exact Complex.I_ne_zero h1
    have hmul' : (2 * (Real.pi : ℂ) * Complex.I) * ((j.val : ℕ) : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * (((n : ℤ) : ℂ) * ((p : ℕ) : ℂ)) := by
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * ((j.val : ℕ) : ℂ) = _ := hdiv
        _ = _ := by ring
    have hmul : ((j.val : ℕ) : ℂ) = ((n : ℤ) : ℂ) * ((p : ℕ) : ℂ) := by
      rcases mul_eq_mul_left_iff.mp hmul' with heq | hz
      · exact heq
      · exact absurd hz hW
    have hre : ((j.val : ℕ) : ℝ) = ((n : ℤ) : ℝ) * ((p : ℕ) : ℝ) :=
      Complex.ofReal_inj.mp (by exact_mod_cast hmul)
    have hjlt : (j.val : ℕ) < p := ZMod.val_lt j
    have hz : (j.val : ℕ) = 0 := by
      by_contra hc
      have hposR : (0 : ℝ) < ((j.val : ℕ) : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hc)
      have hjltR : ((j.val : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hjlt
      have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p))
      rcases Int.lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have hnR : (n : ℝ) < 0 := by exact_mod_cast hn0
        have hnp : ((n : ℝ)) * (p : ℝ) < 0 := mul_neg_of_neg_of_pos hnR hpR
        linarith [hre, hnp]
      · have hnR : ((n : ℤ) : ℝ) = 0 := by exact_mod_cast hn0
        rw [hnR, zero_mul] at hre
        exact hc (Nat.cast_eq_zero.mp hre)
      · have hnn : (1 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (show (1 : ℤ) ≤ n by omega)
        have hle : ((n : ℝ)) * (p : ℝ) ≥ (p : ℝ) := by
          calc ((n : ℝ)) * (p : ℝ) ≥ (1 : ℝ) * (p : ℝ) :=
              mul_le_mul_of_nonneg_right hnn (le_of_lt hpR)
            _ = p := by ring
        linarith [hre, hle]
    exact ZMod.val_eq_zero j |>.mp (by rw [hz])
  · intro h
    subst h
    simp

noncomputable def cyclicDlogCharacters (p : ℕ) [NeZero p] :
    (ZMod p × ZMod p) ≃ AddChar (ZMod p × ZMod p) ℂ :=
  (Equiv.prodCongr (AddEquiv.toEquiv (AddChar.zmodAddEquiv (n := p)))
    (AddEquiv.toEquiv (AddChar.zmodAddEquiv (n := p)))).trans
    (AddEquiv.toEquiv (prodDualEquiv (G := ZMod p) (H := ZMod p)))

theorem cyclicDlogCharacters_eq_stdAddChar (p : ℕ) [NeZero p] (a b u v : ZMod p) :
    cyclicDlogCharacters p (a, b) (u, v) = ZMod.stdAddChar (N := p) (a * u + b * v) := by
  simp only [cyclicDlogCharacters, Equiv.trans_apply, Equiv.prodCongr_apply]
  change (⇑(prodDualEquiv (G := ZMod p) (H := ZMod p)))
    (AddChar.zmodAddEquiv (n := p) a, AddChar.zmodAddEquiv (n := p) b) (u, v) = _
  rw [prodDualEquiv_apply, zmodAddEquiv_apply_stdAddChar, zmodAddEquiv_apply_stdAddChar,
    ← AddChar.map_add_eq_mul]

noncomputable def cyclicDlogHidden (p : ℕ) [NeZero p] (d : ZMod p) :
    AddSubgroup (ZMod p × ZMod p) where
  carrier := {x | x.1 + d * x.2 = 0}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    change (0 : ZMod p) + d * 0 = 0
    ring
  add_mem' := by
    intro a b ha hb
    have hpa : a.1 = -(d * a.2) := (add_eq_zero_iff_eq_neg.mp ha)
    have hpb : b.1 = -(d * b.2) := (add_eq_zero_iff_eq_neg.mp hb)
    show (a + b).1 + d * (a + b).2 = 0
    simp only [Prod.fst_add, Prod.snd_add, hpa, hpb]
    ring
  neg_mem' := by
    intro a ha
    have hpa : a.1 = -(d * a.2) := (add_eq_zero_iff_eq_neg.mp ha)
    show (-a).1 + d * (-a).2 = 0
    simp only [Prod.fst_neg, Prod.snd_neg, hpa]
    ring

theorem mem_cyclicDlogHidden (p : ℕ) [NeZero p] (d : ZMod p) (x : ZMod p × ZMod p) :
    x ∈ cyclicDlogHidden p d ↔ x.1 + d * x.2 = 0 := Iff.rfl

noncomputable def cyclicDlogHiddenSubtypeEquiv (p : ℕ) [NeZero p] (d : ZMod p) :
    ZMod p ≃ ↥(cyclicDlogHidden p d) where
  toFun v := ⟨⟨-(d * v), v⟩, by show -(d * v) + d * v = 0; ring⟩
  invFun hv := hv.1.2
  left_inv v := rfl
  right_inv hv := by
    obtain ⟨x, hx⟩ := hv
    apply Subtype.ext
    change (-(d * x.2), x.2) = x
    have hx' : x.1 + d * x.2 = 0 := (mem_cyclicDlogHidden p d x).mp hx
    rw [(add_eq_zero_iff_eq_neg.mp hx').symm]

theorem card_cyclicDlogHidden (p : ℕ) [NeZero p] (d : ZMod p) :
    Fintype.card ↥(cyclicDlogHidden p d) = p := by
  calc
    Fintype.card ↥(cyclicDlogHidden p d) = Fintype.card (ZMod p) :=
      (Fintype.card_congr (cyclicDlogHiddenSubtypeEquiv p d)).symm
    _ = p := ZMod.card p

theorem card_characterAnnihilator_cyclicDlogHidden (p : ℕ) [NeZero p] (d : ZMod p) :
    Fintype.card (characterAnnihilator (cyclicDlogHidden p d)) = p := by
  have h1 : p * Fintype.card ↥(characterAnnihilator (cyclicDlogHidden p d)) = p * p := by
    calc
      p * Fintype.card ↥(characterAnnihilator (cyclicDlogHidden p d)) =
          Fintype.card ↥(characterAnnihilator (cyclicDlogHidden p d)) *
            Fintype.card ↥(cyclicDlogHidden p d) := by
              rw [card_cyclicDlogHidden p d]
              ring
      _ = Fintype.card (ZMod p × ZMod p) := card_characterAnnihilator (cyclicDlogHidden p d)
      _ = p * p := by simp only [Fintype.card_prod, ZMod.card]
  exact Nat.mul_left_cancel (cyclic_pos) h1

private theorem mod_eq_val_sum {p : ℕ} [NeZero p] (x y d : ZMod p) :
    (x.val + y.val * d.val) % p = (x + d * y).val := by
  have hcast : ((x.val + y.val * d.val : ℕ) : ZMod p) = x + d * y := by
    calc
      ((x.val + y.val * d.val : ℕ) : ZMod p) =
          ((x.val : ℕ) : ZMod p) + ((y.val : ℕ) : ZMod p) * ((d.val : ℕ) : ZMod p) := by
            rw [Nat.cast_add, Nat.cast_mul]
      _ = x + d * y := by
        rw [ZMod.natCast_zmod_val x, ZMod.natCast_zmod_val y, ZMod.natCast_zmod_val d]
        ring
  have := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast] at this

theorem cyclicDlogCharacters_mem_annihilator (p : ℕ) [NeZero p] (a b d : ZMod p) :
    cyclicDlogCharacters p (a, b) ∈ characterAnnihilator (cyclicDlogHidden p d) ↔ b = d * a := by
  rw [mem_characterAnnihilator]
  constructor
  · intro h
    have hx := h ⟨⟨-(d : ZMod p), 1⟩, by
      simp only [mem_cyclicDlogHidden]
      ring⟩
    rw [cyclicDlogCharacters_eq_stdAddChar, stdAddChar_eq_one_iff] at hx
    have hb : a * (-(d : ZMod p)) + b * 1 = 0 := hx
    have : b = d * a := by linear_combination hb
    exact this
  · intro h hv
    have hv' : hv.1.1 + d * hv.1.2 = 0 := (mem_cyclicDlogHidden p d hv).mp hv.property
    have hu : hv.1 = (hv.1.1, hv.1.2) := rfl
    have hz : a * hv.1.1 + b * hv.1.2 = 0 := by
      have h' : b = d * a := h
      calc
        a * hv.1.1 + b * hv.1.2 = a * hv.1.1 + (d * a) * hv.1.2 := by rw [h']
        _ = a * (hv.1.1 + d * hv.1.2) := by ring
        _ = a * 0 := by rw [hv']
        _ = 0 := by ring
    rw [hu, cyclicDlogCharacters_eq_stdAddChar, hz, AddChar.map_zero_eq_one]

noncomputable def cyclicDlogFunction (p : ℕ) [NeZero p] {C : Type} [AddCommGroup C]
    (g h : C) : (ZMod p × ZMod p) → C :=
  fun x => x.1.val • g + x.2.val • h

noncomputable def cyclicDlogRecordDist (p : ℕ) [NeZero p] {C : Type}
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) :
    FinDist (ZMod p × ZMod p) :=
  tableGroupRecordDist (cyclicDlogFunction p g h) (cyclicDlogCharacters p)

private theorem cyclicDlogFunction_eq_nsmul {p : ℕ} [NeZero p] {C : Type} [AddCommGroup C]
    (g h : C) (d : ZMod p) (hh : h = d.val • g) (x : ZMod p × ZMod p) :
    cyclicDlogFunction p g h x = (x.1.val + x.2.val * d.val) • g := by
  have hsmul : x.2.val • h = (x.2.val * d.val) • g := by
    rw [hh, (nsmul_mul_nat x.2.val d.val g).symm]
  rw [cyclicDlogFunction, hsmul, add_nsmul]

private theorem cyclicDlogFunction_eq_val {p : ℕ} [NeZero p] {C : Type} [AddCommGroup C]
    (g h : C) (d : ZMod p) (hp : (p : ℕ) • g = 0) (hh : h = d.val • g)
    (x : ZMod p × ZMod p) :
    cyclicDlogFunction p g h x = (x.1 + d * x.2).val • g := by
  rw [cyclicDlogFunction_eq_nsmul g h d hh x, nsmul_mul_mod g hp,
    mod_eq_val_sum x.1 x.2 d]

theorem hidesSubgroup_cyclicDlogFunction {p : ℕ} [NeZero p] {C : Type} [AddCommGroup C]
    (g h : C) (d : ZMod p) (hp : (p : ℕ) • g = 0) (hh : h = d.val • g)
    (hinj : Function.Injective (fun a : ZMod p => a.val • g)) :
    HidesSubgroup (cyclicDlogFunction p g h) (cyclicDlogHidden p d) := by
  show ∀ x y, cyclicDlogFunction p g h x = cyclicDlogFunction p g h y ↔
    x - y ∈ cyclicDlogHidden p d
  intro x y
  constructor
  · intro hxy
    have hn1 : (x.1 + d * x.2).val • g = (y.1 + d * y.2).val • g := by
      rw [← cyclicDlogFunction_eq_val g h d hp hh x,
        ← cyclicDlogFunction_eq_val g h d hp hh y, hxy]
    have hxy' : x.1 + d * x.2 = y.1 + d * y.2 := hinj hn1
    rw [mem_cyclicDlogHidden]
    calc
      (x - y).1 + d * (x - y).2 = (x.1 + d * x.2) - (y.1 + d * y.2) := by
        simp only [Prod.fst_sub, Prod.snd_sub]
        ring
      _ = 0 := sub_eq_zero.mpr hxy'
  · intro hmem
    have hmem' : (x - y).1 + d * (x - y).2 = 0 := (mem_cyclicDlogHidden p d (x - y)).mp hmem
    have hxy' : x.1 + d * x.2 = y.1 + d * y.2 := by
      calc
        x.1 + d * x.2 = (x - y).1 + d * (x - y).2 + (y.1 + d * y.2) := by
          simp only [Prod.fst_sub, Prod.snd_sub]
          ring
        _ = y.1 + d * y.2 := by rw [hmem', zero_add]
    have hn' : (x.1 + d * x.2).val • g = (y.1 + d * y.2).val • g :=
      congrArg (fun m : ℕ => m • g) (congrArg ZMod.val hxy')
    exact (cyclicDlogFunction_eq_val g h d hp hh x).trans
      (hn'.trans (cyclicDlogFunction_eq_val g h d hp hh y).symm)

noncomputable def cyclicDlogUniformVector (p : ℕ) [NeZero p] :
    (ZMod p × ZMod p) → ℝ :=
  fun _ => (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)⁻¹

theorem cyclicDlogUniformVector_nonneg (p : ℕ) [NeZero p] :
    ∀ x, 0 ≤ cyclicDlogUniformVector p x := by
  intro x
  simp only [cyclicDlogUniformVector]
  positivity

private theorem uniformVector_sqrt_ne_zero (p : ℕ) [NeZero p] :
    (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ) ≠ 0 := by
  have : 0 < Fintype.card (ZMod p × ZMod p) := Fintype.card_pos
  positivity

private theorem uniformVector_sq (p : ℕ) [NeZero p] :
    (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)^2 =
      (Fintype.card (ZMod p × ZMod p) : ℝ) :=
  Real.sq_sqrt (by exact_mod_cast (Nat.cast_nonneg _))

theorem cyclicDlogUniformVector_norm (p : ℕ) [NeZero p] :
    (∑ x, (cyclicDlogUniformVector p x)^2) = 1 := by
  calc
    (∑ x, (cyclicDlogUniformVector p x)^2) = ∑ _ : ZMod p × ZMod p,
        ((Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)⁻¹)^2 := rfl
    _ = Fintype.card (ZMod p × ZMod p) *
        ((Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)⁻¹)^2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
      rw [inv_pow, uniformVector_sq p, mul_comm]
      have hc : (0 : ℝ) < (Fintype.card (ZMod p × ZMod p) : ℝ) := by positivity
      exact inv_mul_cancel₀ (ne_of_gt hc)

noncomputable def cyclicDlogSamplingPrepare (p : ℕ) [NeZero p] :
    Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (cyclicDlogUniformVector p) (0, 0)

theorem cyclicDlogSamplingPrepare_unitary (p : ℕ) [NeZero p] :
    cyclicDlogSamplingPrepare p ∈ Matrix.unitaryGroup (ZMod p × ZMod p) ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_unitary _ _ (cyclicDlogUniformVector_nonneg p)
    (cyclicDlogUniformVector_norm p)

theorem cyclicDlogSamplingPrepare_prepares (p : ℕ) [NeZero p] :
    cyclicDlogSamplingPrepare p *ᵥ Ket (0, 0) = Uniform (ZMod p × ZMod p) := by
  have h := Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_mulVec_ket
    (cyclicDlogUniformVector p) (0, 0)
    (cyclicDlogUniformVector_nonneg p)
  show Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (cyclicDlogUniformVector p) (0, 0) *ᵥ
      Ket (0, 0) = Uniform (ZMod p × ZMod p)
  show Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (cyclicDlogUniformVector p) (0, 0) *ᵥ
      Ket (0, 0) = fun _ => (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℂ)⁻¹
  rw [h]
  funext x
  show ((cyclicDlogUniformVector p x : ℝ) : ℂ) =
    (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℂ)⁻¹
  simp only [cyclicDlogUniformVector]
  push_cast
  rfl

end Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.CfOrder
open Matrix Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open scoped Classical

theorem composite_dlog_explicit_character_and_real_program (r : ℕ) [NeZero r]
    (a b u v : ZMod r) :
    cyclicDlogCharacters r (a,b) (u,v) = ZMod.stdAddChar (N := r) (a*u+b*v) ∧
    cyclicDlogSamplingPrepare r ∈ Matrix.unitaryGroup (ZMod r × ZMod r) ℂ ∧
    cyclicDlogSamplingPrepare r *ᵥ Ket (0,0) = Uniform (ZMod r × ZMod r) :=
  ⟨cyclicDlogCharacters_eq_stdAddChar r a b u v,
    cyclicDlogSamplingPrepare_unitary r, cyclicDlogSamplingPrepare_prepares r⟩

theorem composite_dlog_actual_line_law (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d a b : ZMod r)
    (_hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g) :
    (cyclicDlogRecordDist r g h).prob (a,b) = if b = d*a then 1/(r : ℝ) else 0 := by
  have hf := hidesSubgroup_cyclicDlogFunction g h d hp hh hinj
  have hcard := card_characterAnnihilator_cyclicDlogHidden r d
  have hann := cyclicDlogCharacters_mem_annihilator r a b d
  show (hiddenSubgroupSampleDist (cyclicDlogFunction r g h) (cyclicDlogCharacters r)).prob
      (cyclicDlogCharacters r (a,b)) = _
  rw [hiddenSubgroupSampleDist_prob (cyclicDlogFunction r g h) (cyclicDlogHidden r d) hf
    (cyclicDlogCharacters r) (cyclicDlogCharacters r (a,b)), hann, hcard]
  by_cases hba : b = d*a <;> simp [hba]

theorem cyclicDlogSampling_run (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) :
    Run (AddOracle (cyclicDlogFunction r g h))
      (tableSamplingCircuit (R := C) (cyclicDlogCharacters r) (cyclicDlogSamplingPrepare r))
      (TensorState (Ket (0 : ZMod r × ZMod r)) (Ket (0 : C))) =
    Run (AddOracle (cyclicDlogFunction r g h))
      (hiddenSubgroupSamplingCircuit (R := C) (cyclicDlogCharacters r))
      (TensorState (Uniform (ZMod r × ZMod r)) (Ket (0 : C))) :=
  run_tableSamplingCircuit _ _ _ (cyclicDlogSamplingPrepare_prepares r)

end Qatlib.Concepts.HspRecovery.CfOrder

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.BackendAudit.CountedCharacterTableDecoder
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary

/-!
# Prime-order discrete logarithm Fourier sampling

Constructs the product characters and linear hidden subgroup for discrete logarithms over `ZMod
p` with prime `p`. The annihilator condition becomes the line equation `b = d * a`, and the
record distribution is uniform on this line under the cyclic oracle hypotheses.

The module also constructs a unitary uniform-state preparation and counts queries and gate
macros in repeated table sampling circuits. These are components of the discrete logarithm
algorithm of [Shor1997].

## Main statements

* `prime_dlog_actual_character_dot_product`: gives the explicit character phase.
* `prime_dlog_actual_fourier_line_law`: proves the exact record probabilities.
* `prime_dlog_sampling_actual_query_macro_ledger`: counts repeated sampling resources.

## References

* [Shor, 1997][Shor1997]
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree

open Qatlib.Concepts.HspRecovery.BackendAudit

namespace Qatlib.Concepts.HspRecovery.CfOrder

open Matrix
open scoped Classical

variable {p : ℕ}

/-- A prime natural modulus is positive. -/
private theorem prime_pos {p : ℕ} [hp : Fact (Nat.Prime p)] : 0 < p := by
  have h : Nat.Prime p := hp.1
  exact Nat.Prime.pos h

/-- A prime natural modulus is nonzero. -/
private theorem prime_ne_zero {p : ℕ} [hp : Fact (Nat.Prime p)] : p ≠ 0 := by
  have h : Nat.Prime p := hp.1
  exact Nat.ne_of_gt (Nat.Prime.pos h)

/-- Multiplication of natural scalars agrees with successive scalar multiplication in an
additive commutative group. -/
private theorem nsmul_mul_nat {C : Type} [AddCommGroup C] (n m : ℕ) (a : C) :
    (n * m) • a = n • (m • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1) * m = n * m + m := by ring
    rw [h, add_nsmul, ih]
    simp only [succ_nsmul]

/-- If `p • a = 0`, scalar multiplication by `m` equals scalar multiplication by its remainder
modulo `p`. -/
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

/-- When `p • g = 0`, multiplication by canonical residue representatives sends addition in
`ZMod p` to addition in the group. -/
private theorem nsmul_val_add {C : Type} [AddCommGroup C] [Fact p.Prime] (g : C)
    (hp : (p : ℕ) • g = 0) (x y : ZMod p) : (x + y).val • g = x.val • g + y.val • g := by
  have hval : (x.val + y.val) % p = (x + y).val := (ZMod.val_add x y).symm
  have hdm := Nat.div_add_mod (x.val + y.val) p
  rw [hval] at hdm
  have hsplit : x.val + y.val = (x + y).val + p * ((x.val + y.val) / p) := by omega
  calc
    (x + y).val • g = (x.val + y.val) • g := by
      rw [hsplit, add_nsmul, mul_comm p ((x.val + y.val) / p), nsmul_mul_nat, hp, smul_zero,
        add_zero]
    _ = x.val • g + y.val • g := by rw [← add_nsmul]

/-- Injectivity of multiplication by canonical residue representatives implies that equal
multiples `m • g` and `n • g` with `m, n < p` have `m = n`. -/
private theorem nsmul_val_cancel {C : Type} [AddCommGroup C] [Fact p.Prime] (g : C)
    (hinj : Function.Injective (fun a : ZMod p => a.val • g)) (m n : ℕ) (hm : m < p) (hn : n < p)
    (h : m • g = n • g) : m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : m • g + (n - m) • g = n • g := by
      calc m • g + (n - m) • g = (m + (n - m)) • g := (add_nsmul _ _ _).symm
        _ = n • g := by rw [Nat.add_sub_of_le hlt.le]
    have hsub : n - m < p := by omega
    have h2 : (n - m) • g = 0 := by
      have hx : (n - m) • g + m • g = 0 + m • g := by
        calc (n - m) • g + m • g = m • g + (n - m) • g := add_comm _ _
          _ = n • g := h1
          _ = m • g := h.symm
          _ = 0 + m • g := by simp
      exact add_right_cancel hx
    have h3 : ((n - m : ℕ) : ZMod p) = 0 := by
      refine hinj ?_
      change ((n - m : ℕ) : ZMod p).val • g = (0 : ZMod p).val • g
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsub, h2, ZMod.val_zero, zero_smul]
    have h4 : n - m = 0 := by
      have := congrArg ZMod.val h3
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsub, ZMod.val_zero] at this
      exact this
    omega
  · have h1 : n • g + (m - n) • g = m • g := by
      calc n • g + (m - n) • g = (n + (m - n)) • g := (add_nsmul _ _ _).symm
        _ = m • g := by rw [Nat.add_sub_of_le hlt.le]
    have hsub : m - n < p := by omega
    have h2 : (m - n) • g = 0 := by
      have hx : (m - n) • g + n • g = 0 + n • g := by
        calc (m - n) • g + n • g = n • g + (m - n) • g := add_comm _ _
          _ = m • g := h1
          _ = n • g := h
          _ = 0 + n • g := by simp
      exact add_right_cancel hx
    have h3 : ((m - n : ℕ) : ZMod p) = 0 := by
      refine hinj ?_
      change ((m - n : ℕ) : ZMod p).val • g = (0 : ZMod p).val • g
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsub, h2, ZMod.val_zero, zero_smul]
    have h4 : m - n = 0 := by
      have := congrArg ZMod.val h3
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsub, ZMod.val_zero] at this
      exact this
    omega

/-- Expresses the standard additive character of `ZMod p` as the complex exponential of `2πi *
j.val / p`. -/
private theorem stdAddChar_val {p : ℕ} [NeZero p] (j : ZMod p) :
    ZMod.stdAddChar (N := p) j = Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) / (p : ℝ))) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  field_simp

/-- The standard additive character of `ZMod p` equals one exactly at zero. -/
private theorem stdAddChar_eq_one_iff {p : ℕ} [Fact p.Prime] (j : ZMod p) :
    ZMod.stdAddChar (N := p) j = 1 ↔ j = 0 := by
  have : NeZero p := ⟨prime_ne_zero⟩
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

/-- Identifies pairs of residues modulo `p` with complex additive characters of `ZMod p × ZMod
p` using the product duality equivalence. -/
noncomputable def primeDlogCharacters (p : ℕ) [Fact p.Prime] :
    (ZMod p × ZMod p) ≃ AddChar (ZMod p × ZMod p) ℂ :=
  (Equiv.prodCongr (AddEquiv.toEquiv (AddChar.zmodAddEquiv (n := p)))
    (AddEquiv.toEquiv (AddChar.zmodAddEquiv (n := p)))).trans
    (AddEquiv.toEquiv (prodDualEquiv (G := ZMod p) (H := ZMod p)))

/-- Evaluates the character indexed by `(a, b)` at `(u, v)` as the standard character of `a * u
+ b * v`. -/
theorem primeDlogCharacters_eq_stdAddChar (p : ℕ) [Fact p.Prime] (a b u v : ZMod p) :
    primeDlogCharacters p (a, b) (u, v) = ZMod.stdAddChar (N := p) (a * u + b * v) := by
  simp only [primeDlogCharacters, Equiv.trans_apply, Equiv.prodCongr_apply]
  change (⇑(prodDualEquiv (G := ZMod p) (H := ZMod p)))
    (AddChar.zmodAddEquiv (n := p) a, AddChar.zmodAddEquiv (n := p) b) (u, v) = _
  rw [prodDualEquiv_apply, zmodAddEquiv_apply_stdAddChar, zmodAddEquiv_apply_stdAddChar,
    ← AddChar.map_add_eq_mul]

/-- The additive subgroup of residue pairs satisfying `x.1 + d * x.2 = 0`. -/
noncomputable def primeDlogHidden (p : ℕ) [Fact p.Prime] (d : ZMod p) :
    AddSubgroup (ZMod p × ZMod p) where
  carrier := {x | x.1 + d * x.2 = 0}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
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

/-- Membership in the discrete logarithm hidden subgroup is equivalent to its defining linear
equation. -/
theorem mem_primeDlogHidden (p : ℕ) [Fact p.Prime] (d : ZMod p) (x : ZMod p × ZMod p) :
    x ∈ primeDlogHidden p d ↔ x.1 + d * x.2 = 0 := Iff.rfl

/-- Parametrizes the hidden subgroup by sending `v` to `(-d * v, v)`. -/
noncomputable def primeDlogHiddenSubtypeEquiv (p : ℕ) [Fact p.Prime] (d : ZMod p) :
    ZMod p ≃ ↥(primeDlogHidden p d) where
  toFun v := ⟨⟨-(d * v), v⟩, by show -(d * v) + d * v = 0; ring⟩
  invFun hv := hv.1.2
  left_inv v := rfl
  right_inv hv := by
    obtain ⟨x, hx⟩ := hv
    apply Subtype.ext
    change (-(d * x.2), x.2) = x
    have hx' : x.1 + d * x.2 = 0 := (mem_primeDlogHidden p d x).mp hx
    rw [(add_eq_zero_iff_eq_neg.mp hx').symm]

/-- The discrete logarithm hidden subgroup has cardinality `p`. -/
theorem card_primeDlogHidden (p : ℕ) [Fact p.Prime] (d : ZMod p) :
    Fintype.card ↥(primeDlogHidden p d) = p := by
  calc
    Fintype.card ↥(primeDlogHidden p d) = Fintype.card (ZMod p) :=
      (Fintype.card_congr (primeDlogHiddenSubtypeEquiv p d)).symm
    _ = p := ZMod.card p

/-- The character annihilator of the discrete logarithm hidden subgroup has cardinality `p`. -/
theorem card_characterAnnihilator_primeDlogHidden (p : ℕ) [Fact p.Prime] (d : ZMod p) :
    Fintype.card (characterAnnihilator (primeDlogHidden p d)) = p := by
  have h1 : p * Fintype.card ↥(characterAnnihilator (primeDlogHidden p d)) = p * p := by
    calc
      p * Fintype.card ↥(characterAnnihilator (primeDlogHidden p d)) =
          Fintype.card ↥(characterAnnihilator (primeDlogHidden p d)) *
            Fintype.card ↥(primeDlogHidden p d) := by
              rw [card_primeDlogHidden p d]
              ring
      _ = Fintype.card (ZMod p × ZMod p) := card_characterAnnihilator (primeDlogHidden p d)
      _ = p * p := by simp only [Fintype.card_prod, ZMod.card]
  exact Nat.mul_left_cancel (prime_pos) h1

/-- Reducing `x.val + y.val * d.val` modulo `p` gives the canonical representative of `x + d *
y`. -/
private theorem mod_eq_val_sum {p : ℕ} [Fact p.Prime] (x y d : ZMod p) :
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

/-- The character indexed by `(a, b)` annihilates the hidden subgroup exactly when `b = d * a`. -/
theorem primeDlogCharacters_mem_annihilator (p : ℕ) [Fact p.Prime] (a b d : ZMod p) :
    primeDlogCharacters p (a, b) ∈ characterAnnihilator (primeDlogHidden p d) ↔ b = d * a := by
  rw [mem_characterAnnihilator]
  constructor
  · intro h
    have hx := h ⟨⟨-(d : ZMod p), 1⟩, by
      simp only [mem_primeDlogHidden]
      ring⟩
    rw [primeDlogCharacters_eq_stdAddChar, stdAddChar_eq_one_iff] at hx
    have hb : a * (-(d : ZMod p)) + b * 1 = 0 := hx
    have : b = d * a := by linear_combination hb
    exact this
  · intro h hv
    have hv' : hv.1.1 + d * hv.1.2 = 0 := (mem_primeDlogHidden p d hv).mp hv.property
    have hu : hv.1 = (hv.1.1, hv.1.2) := rfl
    have hz : a * hv.1.1 + b * hv.1.2 = 0 := by
      have h' : b = d * a := h
      calc
        a * hv.1.1 + b * hv.1.2 = a * hv.1.1 + (d * a) * hv.1.2 := by rw [h']
        _ = a * (hv.1.1 + d * hv.1.2) := by ring
        _ = a * 0 := by rw [hv']
        _ = 0 := by ring
    rw [hu, primeDlogCharacters_eq_stdAddChar, hz, AddChar.map_zero_eq_one]

/-- The discrete logarithm oracle function sending `(u, v)` to `u.val • g + v.val • h`. -/
noncomputable def primeDlogFunction (p : ℕ) [Fact p.Prime] {C : Type} [AddCommGroup C]
    (g h : C) : (ZMod p × ZMod p) → C :=
  fun x => x.1.val • g + x.2.val • h

/-- The finite distribution of Fourier record pairs for the discrete logarithm oracle with the
explicit cyclic character indexing. -/
noncomputable def primeDlogRecordDist (p : ℕ) [Fact p.Prime] {C : Type}
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) :
    FinDist (ZMod p × ZMod p) :=
  tableGroupRecordDist (primeDlogFunction p g h) (primeDlogCharacters p)

/-- When `h = d.val • g`, rewrites the oracle output as `(x.1.val + x.2.val * d.val) • g`. -/
private theorem primeDlogFunction_eq_nsmul {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    (g h : C) (d : ZMod p) (hh : h = d.val • g) (x : ZMod p × ZMod p) :
    primeDlogFunction p g h x = (x.1.val + x.2.val * d.val) • g := by
  have hsmul : x.2.val • h = (x.2.val * d.val) • g := by
    rw [hh, (nsmul_mul_nat x.2.val d.val g).symm]
  rw [primeDlogFunction, hsmul, add_nsmul]

/-- When `p • g = 0` and `h = d.val • g`, the oracle output is `(x.1 + d * x.2).val • g`. -/
private theorem primeDlogFunction_eq_val {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    (g h : C) (d : ZMod p) (hp : (p : ℕ) • g = 0) (hh : h = d.val • g)
    (x : ZMod p × ZMod p) :
    primeDlogFunction p g h x = (x.1 + d * x.2).val • g := by
  rw [primeDlogFunction_eq_nsmul g h d hh x, nsmul_mul_mod g hp,
    mod_eq_val_sum x.1 x.2 d]

/-- The cyclic discrete logarithm oracle hides `primeDlogHidden p d` when `p • g = 0`, `h =
d.val • g`, and multiplication by canonical residue representatives is injective. -/
theorem hidesSubgroup_primeDlogFunction {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    (g h : C) (d : ZMod p) (hp : (p : ℕ) • g = 0) (hh : h = d.val • g)
    (hinj : Function.Injective (fun a : ZMod p => a.val • g)) :
    HidesSubgroup (primeDlogFunction p g h) (primeDlogHidden p d) := by
  show ∀ x y, primeDlogFunction p g h x = primeDlogFunction p g h y ↔
    x - y ∈ primeDlogHidden p d
  intro x y
  constructor
  · intro hxy
    have hn1 : (x.1 + d * x.2).val • g = (y.1 + d * y.2).val • g := by
      rw [← primeDlogFunction_eq_val g h d hp hh x,
        ← primeDlogFunction_eq_val g h d hp hh y, hxy]
    have hval : (x.1 + d * x.2).val = (y.1 + d * y.2).val :=
      nsmul_val_cancel g hinj _ _ (ZMod.val_lt _) (ZMod.val_lt _) hn1
    have hxy' : x.1 + d * x.2 = y.1 + d * y.2 := ZMod.val_injective p hval
    rw [mem_primeDlogHidden]
    calc
      (x - y).1 + d * (x - y).2 = (x.1 + d * x.2) - (y.1 + d * y.2) := by
        simp only [Prod.fst_sub, Prod.snd_sub]
        ring
      _ = 0 := sub_eq_zero.mpr hxy'
  · intro hmem
    have hmem' : (x - y).1 + d * (x - y).2 = 0 := (mem_primeDlogHidden p d (x - y)).mp hmem
    have hxy' : x.1 + d * x.2 = y.1 + d * y.2 := by
      calc
        x.1 + d * x.2 = (x - y).1 + d * (x - y).2 + (y.1 + d * y.2) := by
          simp only [Prod.fst_sub, Prod.snd_sub]
          ring
        _ = y.1 + d * y.2 := by rw [hmem', zero_add]
    have hn' : (x.1 + d * x.2).val • g = (y.1 + d * y.2).val • g :=
      congrArg (fun m : ℕ => m • g) (congrArg ZMod.val hxy')
    exact (primeDlogFunction_eq_val g h d hp hh x).trans
      (hn'.trans (primeDlogFunction_eq_val g h d hp hh y).symm)

/-- The constant real amplitude vector with value the reciprocal square root of the number of
residue pairs. -/
noncomputable def primeDlogUniformVector (p : ℕ) [Fact p.Prime] :
    (ZMod p × ZMod p) → ℝ :=
  fun _ => (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)⁻¹

/-- Every amplitude of `primeDlogUniformVector` is nonnegative. -/
theorem primeDlogUniformVector_nonneg (p : ℕ) [Fact p.Prime] :
    ∀ x, 0 ≤ primeDlogUniformVector p x := by
  intro x
  simp only [primeDlogUniformVector]
  positivity

/-- The square root of the number of residue pairs modulo a nonzero modulus is nonzero. -/
private theorem uniformVector_sqrt_ne_zero (p : ℕ) [Fact p.Prime] :
    (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ) ≠ 0 := by
  have : 0 < Fintype.card (ZMod p × ZMod p) := Fintype.card_pos
  positivity

/-- Squaring the square root of the number of residue pairs recovers that cardinality. -/
private theorem uniformVector_sq (p : ℕ) [Fact p.Prime] :
    (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)^2 =
      (Fintype.card (ZMod p × ZMod p) : ℝ) :=
  Real.sq_sqrt (by exact_mod_cast (Nat.cast_nonneg _))

/-- The sum of squared amplitudes of `primeDlogUniformVector` is one. -/
theorem primeDlogUniformVector_norm (p : ℕ) [Fact p.Prime] :
    (∑ x, (primeDlogUniformVector p x)^2) = 1 := by
  calc
    (∑ x, (primeDlogUniformVector p x)^2) = ∑ _ : ZMod p × ZMod p,
        ((Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)⁻¹)^2 := rfl
    _ = Fintype.card (ZMod p × ZMod p) *
        ((Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℝ)⁻¹)^2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
      rw [inv_pow, uniformVector_sq p, mul_comm]
      have hc : (0 : ℝ) < (Fintype.card (ZMod p × ZMod p) : ℝ) := by positivity
      exact inv_mul_cancel₀ (ne_of_gt hc)

/-- The preparation matrix obtained from the nonnegative uniform amplitude vector and the basis
index `(0, 0)`. -/
noncomputable def primeDlogSamplingPrepare (p : ℕ) [Fact p.Prime] :
    Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (primeDlogUniformVector p) (0, 0)

/-- The cyclic discrete logarithm preparation matrix is unitary. -/
theorem primeDlogSamplingPrepare_unitary (p : ℕ) [Fact p.Prime] :
    primeDlogSamplingPrepare p ∈ Matrix.unitaryGroup (ZMod p × ZMod p) ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_unitary _ _ (primeDlogUniformVector_nonneg p)
    (primeDlogUniformVector_norm p)

/-- The preparation matrix sends the basis state at `(0, 0)` to the uniform state on residue
pairs. -/
theorem primeDlogSamplingPrepare_prepares (p : ℕ) [Fact p.Prime] :
    primeDlogSamplingPrepare p *ᵥ Qatlib.Foundations.PureStateMath.Ket (0, 0) = Uniform (ZMod p × ZMod p) := by
  have h := Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_mulVec_ket
    (primeDlogUniformVector p) (0, 0)
    (primeDlogUniformVector_nonneg p)
  show Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (primeDlogUniformVector p) (0, 0) *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (0, 0) = Uniform (ZMod p × ZMod p)
  show Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (primeDlogUniformVector p) (0, 0) *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (0, 0) = fun _ => (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℂ)⁻¹
  rw [h]
  funext x
  show ((primeDlogUniformVector p x : ℝ) : ℂ) =
    (Real.sqrt (Fintype.card (ZMod p × ZMod p)) : ℂ)⁻¹
  simp only [primeDlogUniformVector]
  push_cast
  rfl

/-- The query count of concatenated circuits is the sum of their query counts. -/
private theorem queryCount_append {I : Type} (C D : Circuit I) :
    QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp [QueryCount]
  | cons s C ih => cases s <;> simp [QueryCount, ih, Nat.add_assoc, Nat.add_comm 1]

/-- The gate count of concatenated circuits is the sum of their gate counts. -/
private theorem gateCount_append {I : Type} (C D : Circuit I) :
    GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp [GateCount]
  | cons s C ih => cases s <;> simp [GateCount, ih, Nat.add_assoc, Nat.add_comm 1]

/-- Repeating a circuit `m` times multiplies its query count by `m`. -/
private theorem queryCount_repeat {I : Type} (C : Circuit I) (m : ℕ) :
    QueryCount (RepeatCircuit C m) = m * QueryCount C := by
  induction m with
  | zero => rw [RepeatCircuit, QueryCount, Nat.zero_mul]
  | succ m ih =>
    rw [RepeatCircuit, queryCount_append, ih]
    ring

/-- Repeating a circuit `m` times multiplies its gate count by `m`. -/
private theorem gateCount_repeat {I : Type} (C : Circuit I) (m : ℕ) :
    GateCount (RepeatCircuit C m) = m * GateCount C := by
  induction m with
  | zero => rw [RepeatCircuit, GateCount, Nat.zero_mul]
  | succ m ih =>
    rw [RepeatCircuit, gateCount_append, ih]
    ring

end Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.CfOrder

open Matrix
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open scoped Classical

/-- The character indexed by `(a, b)` evaluates at `(u, v)` as the complex exponential of `2πi`
times the canonical representative of `a * u + b * v` divided by `p` [Shor1997]. -/
theorem prime_dlog_actual_character_dot_product (p : ℕ) [Fact p.Prime] (a b u v : ZMod p) :
    primeDlogCharacters p (a, b) (u, v) =
      Complex.exp (2 * Real.pi * Complex.I * ((((a * u + b * v).val : ℕ) : ℝ) / (p : ℝ))) := by
  rw [primeDlogCharacters_eq_stdAddChar, stdAddChar_val]

/-- Under the prime-order cyclic oracle hypotheses, a record `(a, b)` has probability `1 / p` on
the line `b = d * a` and zero off that line [Shor1997]. -/
theorem prime_dlog_actual_fourier_line_law (p : ℕ) [Fact p.Prime] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod p) (hp : (p : ℕ) • g = 0)
    (hinj : Function.Injective (fun a : ZMod p => a.val • g)) (hh : h = d.val • g)
    (a b : ZMod p) :
    (primeDlogRecordDist p g h).prob (a, b) = if b = d * a then 1 / (p : ℝ) else 0 := by
  have hf := hidesSubgroup_primeDlogFunction g h d hp hh hinj
  have hcard := card_characterAnnihilator_primeDlogHidden p d
  have hann := primeDlogCharacters_mem_annihilator p a b d
  show (hiddenSubgroupSampleDist (primeDlogFunction p g h) (primeDlogCharacters p)).prob
      (primeDlogCharacters p (a, b)) = _
  rw [hiddenSubgroupSampleDist_prob (primeDlogFunction p g h) (primeDlogHidden p d) hf
    (primeDlogCharacters p) (primeDlogCharacters p (a, b)), hann, hcard]
  by_cases hba : b = d * a <;> simp [hba]

/-- Repeating the prime-order table sampling circuit `m` times uses exactly `m` oracle queries
and `2 * m` gate macros. -/
theorem prime_dlog_sampling_actual_query_macro_ledger (p : ℕ) [Fact p.Prime] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C]
    (A : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ) (m : ℕ) :
    let cs := tableSamplingCircuit (R := C) (primeDlogCharacters p) A
    QueryCount (RepeatCircuit cs m) = m ∧ GateCount (RepeatCircuit cs m) = 2 * m := by
  (try dsimp only)
  have hq := queryCount_repeat (tableSamplingCircuit (R := C) (primeDlogCharacters p) A) m
  have hg := gateCount_repeat (tableSamplingCircuit (R := C) (primeDlogCharacters p) A) m
  have h := (tableSamplingCircuit_resources (R := C) (primeDlogCharacters p) A)
  rw [hq, hg, h.1, h.2]
  constructor <;> omega

end Qatlib.Concepts.HspRecovery.CfOrder

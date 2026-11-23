/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GaussSumEst02.RingEstimate.RamanujanSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section

/-!
# Corrected imprimitive lift for prime-power Gauss sums

Fixed source: [van Dam and Seroussi, 2002](https://arxiv.org/abs/quant-ph/0207131),
Fact 11 (page 9).
The printed Eq. (16) reverses the divisibility to `β ∣ p^s` and uses the factor
`p^(s - 1) * (p - 1)`; both are wrong for a nontrivial induced character.  This
module proves the corrected statement by the geometric fiber sum: residues modulo
`p^r` are grouped into the fibers `x = a + t * p^(r - s)` with `t` running over
the residues modulo `p^s`, and the inner geometric sum over `t` vanishes unless
`p^s` divides the frequency.

## Main statements

* `IsInducedBy`: the lift relation identifying a Dirichlet character modulo
  `p^r` with one modulo `p^(r - s)`.
* `ringGaussSum_induced`: the corrected Fact 11 dichotomy — the imprimitive
  prime-power Gauss sum is zero unless `p^s` divides the frequency, and at
  frequencies `β = p^s * b` it equals `p^s` times the Gauss sum of the inducing
  character at `b`.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.RingEstimate.ImprimitiveLift

open Qatlib.Papers.GaussSumEst02.MainResults.Source
open Qatlib.Papers.GaussSumEst02.RingEstimate

/-- A Dirichlet character modulo `p^r` is induced by a character modulo
`p^(r - s)` when its values agree after casting residues down by their canonical
representatives.  No primitivity or nontriviality of the inducing character is
required for the lift identity itself. -/
def IsInducedBy {p r s : ℕ} (χ : DirichletChar (p ^ r))
    (χs : DirichletChar (p ^ (r - s))) : Prop :=
  ∀ x : ZMod (p ^ r), χ.toFun x = χs.toFun ((x.val : ℕ) : ZMod (p ^ (r - s)))

/-- The standard additive character at `p^u` times a cast natural agrees with the
standard additive character at the co-factor modulus: both evaluate to
`exp (2 * π * I * k / M)`.  This is the exact root-of-unity compatibility
`ζ_(p^u * M)^(p^u * k) = ζ_M^k` with no periodicity step. -/
theorem zmodAddChar_natCast_mul {p N M u : ℕ} [NeZero N] [NeZero M]
    (hNM : N = p ^ u * M) (hu : 0 < u) (hbig : 1 < N) (hsmall : 1 < M) (k : ℕ) :
    (zmodAddChar N hbig).toFun (((p ^ u : ℕ) : ZMod N) * ((k : ℕ) : ZMod N))
      = (zmodAddChar M hsmall).toFun ((k : ℕ) : ZMod M) := by
  have hcast : (((p ^ u : ℕ) : ZMod N) * ((k : ℕ) : ZMod N))
      = ((p ^ u * k : ℕ) : ZMod N) := by
    push_cast
    ring
  rw [hcast]
  rw [show (zmodAddChar N hbig).toFun ((p ^ u * k : ℕ) : ZMod N)
      = ↑(ZMod.toCircle ((p ^ u * k : ℕ) : ZMod N)) from rfl,
    show (zmodAddChar M hsmall).toFun ((k : ℕ) : ZMod M)
      = ↑(ZMod.toCircle ((k : ℕ) : ZMod M)) from rfl]
  rw [ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by
    have hne : N ≠ 0 := NeZero.ne N
    rcases Nat.eq_zero_or_pos p with hp | hp
    · rw [hp, zero_pow hu.ne', zero_mul] at hNM
      rw [← hNM] at hne
      exact absurd rfl hne
    · exact_mod_cast (Nat.ne_of_gt hp)
  have hm0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  rw [hNM]
  push_cast
  field_simp

/-- The fibers of the residue ring modulo `p^r`: summing over `ZMod (p^r)`
equals summing over the base residues `a` modulo `p^(r - s)` and the fiber
parameters `t` modulo `p^s`, with `x = a + t * p^(r - s)`.  The map
`(a, t) ↦ a + t * p^(r - s)` is a bijection by division with remainder. -/
theorem sum_zmod_fibers {p r s : ℕ} (hrs : s ≤ r)
    [NeZero (p ^ r)] [NeZero (p ^ (r - s))] [NeZero (p ^ s)]
    (f : ZMod (p ^ r) → ℂ) :
    (∑ x : ZMod (p ^ r), f x)
      = ∑ a : ZMod (p ^ (r - s)), ∑ t : ZMod (p ^ s),
          f (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))) := by
  have hq : 0 < p ^ (r - s) := Nat.pos_of_ne_zero (NeZero.ne (p ^ (r - s)))
  have hsplit : p ^ r = p ^ (r - s) * p ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hrs]
  have hbound : ∀ (a : ZMod (p ^ (r - s))) (t : ZMod (p ^ s)),
      a.val + t.val * p ^ (r - s) < p ^ r := by
    intro a t
    have e1 := a.val_lt
    have e2 := t.val_lt
    nlinarith [hsplit]
  have hdivlt : ∀ y : ZMod (p ^ r), y.val / p ^ (r - s) < p ^ s := by
    intro y
    exact (Nat.div_lt_iff_lt_mul hq).mpr (by rw [Nat.mul_comm, ← hsplit]; exact y.val_lt)
  let fiberEquiv : ZMod (p ^ (r - s)) × ZMod (p ^ s) ≃ ZMod (p ^ r) :=
    { toFun := fun x => (((x.1.val + x.2.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
      invFun := fun y => (((y.val % p ^ (r - s) : ℕ) : ZMod (p ^ (r - s))),
        ((y.val / p ^ (r - s) : ℕ) : ZMod (p ^ s)))
      left_inv := fun x => by
        have hval : (((ZMod.val (((x.1.val + x.2.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
            % p ^ (r - s) : ℕ) : ZMod (p ^ (r - s))) = x.1 := by
          rw [ZMod.val_natCast_of_lt (hbound x.1 x.2), Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt x.1.val_lt, ZMod.natCast_zmod_val]
        have hdiv : (((ZMod.val (((x.1.val + x.2.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
            / p ^ (r - s) : ℕ) : ZMod (p ^ s)) = x.2 := by
          rw [ZMod.val_natCast_of_lt (hbound x.1 x.2), Nat.add_comm,
            Nat.mul_comm (x.2.val) (p ^ (r - s)), Nat.mul_add_div hq,
            Nat.div_eq_of_lt x.1.val_lt, Nat.add_zero, ZMod.natCast_zmod_val]
        exact Prod.ext hval hdiv
      right_inv := fun y => by
        simp only []
        rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hq), ZMod.val_natCast_of_lt (hdivlt y),
          Nat.mul_comm (y.val / p ^ (r - s)) (p ^ (r - s)),
          Nat.mod_add_div y.val (p ^ (r - s)), ZMod.natCast_zmod_val] }
  rw [(show (∑ a : ZMod (p ^ (r - s)), ∑ t : ZMod (p ^ s),
      f (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
    = ∑ x : ZMod (p ^ (r - s)) × ZMod (p ^ s),
      f (((x.1.val + x.2.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
    from by rw [← Finset.sum_product', Finset.univ_product_univ])]
  exact (Equiv.sum_comp fiberEquiv (fun y : ZMod (p ^ r) => f y)).symm

/-- Corrected Fact 11.  Let `χ` modulo `p^r` be induced by `χs` modulo
`p^(r - s)` with `1 ≤ s < r`, and let `e` and `eLow` be the standard primitive
additive characters.  Then the imprimitive prime-power Gauss sum `G(χ, β)`
vanishes unless `p^s` divides the frequency `β`, and at frequencies
`β = p^s * b` it equals `p^s` times the Gauss sum of the inducing character at
`b` [VanDamSeroussi2002].  This corrects the printed Eq. (16), which reverses
the divisibility and uses the wrong factor `p^(s - 1) * (p - 1)`.  Only the
prime-power modulus, the lift relation, and the standard primitive additive
characters enter; no primitivity of the inducing character is needed. -/
theorem ringGaussSum_induced {p r s : ℕ} (hp : p.Prime) (hs : 0 < s) (hr : s < r)
    [NeZero (p ^ r)] [NeZero (p ^ (r - s))] [NeZero (p ^ s)]
    (χ : DirichletChar (p ^ r)) (χs : DirichletChar (p ^ (r - s)))
    (hind : IsInducedBy χ χs) :
    (∀ β : ZMod (p ^ r), ¬ (p ^ s : ℕ) ∣ β.val →
      ringGaussSum χ (zmodAddChar (p ^ r) (by
        have h2 := hp.two_le
        exact one_lt_pow₀ (Nat.lt_of_lt_of_le Nat.one_lt_two h2) (by omega : r ≠ 0))) β = 0) ∧
    (∀ (β : ZMod (p ^ r)) (b : ZMod (p ^ (r - s))),
      β = ((p ^ s : ℕ) : ZMod (p ^ r)) * ((b.val : ℕ) : ZMod (p ^ r)) →
      ringGaussSum χ (zmodAddChar (p ^ r) (by
        have h2 := hp.two_le
        exact one_lt_pow₀ (Nat.lt_of_lt_of_le Nat.one_lt_two h2) (by omega : r ≠ 0))) β
        = (p ^ s : ℂ) * ringGaussSum χs (zmodAddChar (p ^ (r - s)) (by
          have h2 := hp.two_le
          exact one_lt_pow₀ (Nat.lt_of_lt_of_le Nat.one_lt_two h2) (by omega : r - s ≠ 0))) b) := by
  classical
  have h1r : 1 < p ^ r := one_lt_pow₀ (Nat.lt_of_lt_of_le Nat.one_lt_two hp.two_le) (by omega : r ≠ 0)
  have h1s : 1 < p ^ s := one_lt_pow₀ (Nat.lt_of_lt_of_le Nat.one_lt_two hp.two_le) (by omega : s ≠ 0)
  have h1rs : 1 < p ^ (r - s) :=
    one_lt_pow₀ (Nat.lt_of_lt_of_le Nat.one_lt_two hp.two_le) (by omega : r - s ≠ 0)
  set e := zmodAddChar (p ^ r) h1r with he
  set eLow := zmodAddChar (p ^ (r - s)) h1rs with heLow
  set eFib := zmodAddChar (p ^ s) h1s with heFib
  have hsr : s ≤ r := hr.le
  have hsplit : p ^ r = p ^ (r - s) * p ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hsr]
  have hsplit' : p ^ r = p ^ s * p ^ (r - s) := by
    rw [← pow_add, add_comm, Nat.sub_add_cancel hsr]
  have hfiber : ∀ (a : ZMod (p ^ (r - s))) (t : ZMod (p ^ s)),
      a.val + t.val * p ^ (r - s) < p ^ r := by
    intro a t
    have e1 := a.val_lt
    have e2 := t.val_lt
    nlinarith [hsplit]
  have hχ : ∀ (a : ZMod (p ^ (r - s))) (t : ZMod (p ^ s)),
      χ.toFun (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
        = χs.toFun a := by
    intro a t
    rw [hind, ZMod.val_natCast_of_lt (hfiber a t)]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]
  have hid_t : ∀ (β : ZMod (p ^ r)) (t : ZMod (p ^ s)),
      e.toFun (β * (((t.val : ℕ) : ZMod (p ^ r)) * ((p ^ (r - s) : ℕ) : ZMod (p ^ r))))
        = eFib.toFun ((((β.val : ℕ) : ZMod (p ^ s))) * t) := by
    intro β t
    have harg : β * (((t.val : ℕ) : ZMod (p ^ r)) * ((p ^ (r - s) : ℕ) : ZMod (p ^ r)))
        = ((p ^ (r - s) : ℕ) : ZMod (p ^ r)) * ((β.val * t.val : ℕ) : ZMod (p ^ r)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val β]
      push_cast
      ring
    rw [harg, zmodAddChar_natCast_mul hsplit (by omega : 0 < r - s) h1r h1s (β.val * t.val)]
    congr 1
    rw [show (((β.val : ℕ) : ZMod (p ^ s))) * t
        = ((β.val * t.val : ℕ) : ZMod (p ^ s)) by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val t]]
  constructor
  · intro β hβ
    have hβ0 : (((β.val : ℕ) : ZMod (p ^ s))) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hβ h0
    have hsum : (∑ t : ZMod (p ^ s), eFib.toFun ((((β.val : ℕ) : ZMod (p ^ s))) * t)) = 0 := by
      rw [sum_primitive_shift eFib (zmodAddChar_primitive (p ^ s) h1s) _]
      rw [ite_eq_right hβ0]
    rw [ringGaussSum, sum_zmod_fibers hsr (fun x : ZMod (p ^ r) => χ.toFun x * e.toFun (β * x))]
    have hinner : ∀ (a : ZMod (p ^ (r - s))) (t : ZMod (p ^ s)),
        χ.toFun (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
          * e.toFun (β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
        = (χs.toFun a * e.toFun (β * ((a.val : ℕ) : ZMod (p ^ r))))
          * eFib.toFun ((((β.val : ℕ) : ZMod (p ^ s))) * t) := by
      intro a t
      rw [hχ a t]
      have harg : β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
          = β * ((a.val : ℕ) : ZMod (p ^ r))
            + β * (((t.val : ℕ) : ZMod (p ^ r)) * ((p ^ (r - s) : ℕ) : ZMod (p ^ r))) := by
        push_cast
        ring
      rw [harg, e.map_add', hid_t]
      ring
    have hpera : ∀ a : ZMod (p ^ (r - s)),
        (∑ t : ZMod (p ^ s),
            χ.toFun (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
              * e.toFun (β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
        = 0) := by
      intro a
      have hstep : (∑ t : ZMod (p ^ s),
            χ.toFun (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
              * e.toFun (β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
          = (χs.toFun a * e.toFun (β * ((a.val : ℕ) : ZMod (p ^ r))))
            * (∑ t : ZMod (p ^ s), eFib.toFun ((((β.val : ℕ) : ZMod (p ^ s))) * t))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => hinner a t)
      rw [hstep, hsum, mul_zero]
    rw [Finset.sum_congr rfl (fun a _ => hpera a)]
    exact Finset.sum_const_zero
  · intro β b hβ
    have hps_lt_pr : p ^ s < p ^ r := by
      exact Nat.pow_lt_pow_right (by have := hp.two_le; omega : 1 < p) hr
    have hps_b_lt : p ^ s * b.val < p ^ r := by
      have e2 := b.val_lt
      have hpos : 0 < p ^ s := pow_pos hp.pos s
      nlinarith [e2, hpos, hsplit']
    have hb_lt_pr : b.val < p ^ r :=
      lt_of_lt_of_le b.val_lt (Nat.pow_le_pow_right hp.pos (Nat.sub_le r s))
    have hβdvd : (p ^ s : ℕ) ∣ β.val := by
      rw [hβ, ZMod.val_mul, ZMod.val_natCast_of_lt hps_lt_pr,
        ZMod.val_natCast_of_lt hb_lt_pr, Nat.mod_eq_of_lt hps_b_lt]
      exact dvd_mul_right _ _
    have hβ0 : (((β.val : ℕ) : ZMod (p ^ s))) = 0 :=
      (ZMod.natCast_eq_zero_iff β.val (p ^ s)).mpr hβdvd
    have hone : ∀ t : ZMod (p ^ s),
        eFib.toFun ((((β.val : ℕ) : ZMod (p ^ s))) * t) = 1 := by
      intro t
      rw [hβ0, zero_mul, eFib.map_zero']
    have hid_a : ∀ a : ZMod (p ^ (r - s)),
        e.toFun (β * ((a.val : ℕ) : ZMod (p ^ r))) = eLow.toFun (b * a) := by
      intro a
      have harg : β * ((a.val : ℕ) : ZMod (p ^ r))
          = ((p ^ s : ℕ) : ZMod (p ^ r)) * ((b.val * a.val : ℕ) : ZMod (p ^ r)) := by
        rw [hβ]
        push_cast
        ring
      rw [harg, zmodAddChar_natCast_mul hsplit' hs h1r h1rs (b.val * a.val)]
      congr 1
      rw [show b * a = ((b.val * a.val : ℕ) : ZMod (p ^ (r - s))) by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val b, ZMod.natCast_zmod_val a]]
    rw [ringGaussSum, sum_zmod_fibers hsr (fun x : ZMod (p ^ r) => χ.toFun x * e.toFun (β * x))]
    have hpera : ∀ a : ZMod (p ^ (r - s)),
        (∑ t : ZMod (p ^ s),
            χ.toFun (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
              * e.toFun (β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
        = ((p ^ s : ℕ) : ℂ) * (χs.toFun a * eLow.toFun (b * a))) := by
      intro a
      have hper : ∀ t : ZMod (p ^ s),
          χ.toFun (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
            * e.toFun (β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r))))
          = χs.toFun a * eLow.toFun (b * a) := by
        intro t
        rw [hχ a t]
        have harg : β * (((a.val + t.val * p ^ (r - s) : ℕ) : ZMod (p ^ r)))
            = β * ((a.val : ℕ) : ZMod (p ^ r))
              + β * (((t.val : ℕ) : ZMod (p ^ r)) * ((p ^ (r - s) : ℕ) : ZMod (p ^ r))) := by
          push_cast
          ring
        rw [harg, e.map_add', hid_t, hone t, mul_one, hid_a a]
      rw [Finset.sum_congr rfl (fun t _ => hper t), Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, ZMod.card]
    rw [Finset.sum_congr rfl (fun a _ => hpera a), ringGaussSum, ← Finset.mul_sum,
      Nat.cast_pow]

end Qatlib.Papers.GaussSumEst02.RingEstimate.ImprimitiveLift

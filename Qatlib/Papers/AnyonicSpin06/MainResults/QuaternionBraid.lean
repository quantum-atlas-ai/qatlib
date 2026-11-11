/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
# Quaternionic braid relations

This module studies the conjugation expression `phi g P = g * P * star g` and the scalar pairing
`qdot` on real quaternions. Identities for pure unit quaternions yield `braid_relation_iff`,
including the two signs of the imaginary coefficient, and the dot-product criterion
`braid_condition_dot` [KauffmanLomonaco2006].

## Main statements

* `braid_relation_iff`: characterizes the braid relation for normalized quaternion pairs.
* `braid_condition_dot`: rewrites the conjugation condition as a scalar pairing identity.

## References

* [Kauffman and Lomonaco, 2006][KauffmanLomonaco2006]
-/

set_option autoImplicit false
noncomputable section

open scoped Quaternion
open Quaternion

namespace Qatlib.Papers.AnyonicSpin06.MainResults.QuaternionBraid

/-- The quaternionic conjugation expression `g * P * star g`. -/
def phi (g P : ℍ[ℝ]) : ℍ[ℝ] := g * P * star g

/-- The scalar pairing `-(u * v).re`, which is the Euclidean dot product on pure quaternions. -/
def qdot (u v : ℍ[ℝ]) : ℝ := -(u * v).re

/-- The conjugate of a quaternion with zero real part equals its negative. -/
lemma star_eq_neg_of_re_zero {u : ℍ[ℝ]} (hu : u.re = 0) : star u = -u := by
  ext <;> simp [hu]

/-- The real part of a quaternion product is unchanged by reversing the two factors. -/
lemma re_mul_comm (x y : ℍ[ℝ]) : (x * y).re = (y * x).re := by
  simp only [re_mul]
  ring

/-- For a pure unit quaternion `u`, the squared norm of `a + b * u` equals `a ^ 2 + b ^ 2`. -/
lemma normSq_add_mul {a b : ℝ} {u : ℍ[ℝ]} (hu : u.re = 0) (hn : normSq u = 1) :
    normSq ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*u) = a^2 + b^2 := by
  rw [normSq_add]
  have hmul : normSq ((b:ℍ[ℝ])*u) = b^2 := by
    rw [map_mul, Quaternion.normSq_coe, hn, mul_one]
  have hcross : (2 * (((a:ℍ[ℝ]) * star ((b:ℍ[ℝ])*u)).re)) = 0 := by
    rw [re_mul]
    simp only [re_coe, imI_coe, imJ_coe, imK_coe, re_star, zero_mul, sub_zero]
    have h2 : ((b:ℍ[ℝ]) * u).re = 0 := by
      rw [re_mul]
      simp only [re_coe, imI_coe, imJ_coe, imK_coe, hu]
      ring
    rw [h2]
    ring
  rw [Quaternion.normSq_coe, hmul, hcross]
  ring

/-- The squared norm of `phi g P` equals `normSq g * normSq P * normSq g`. -/
lemma phi_normSq (g P : ℍ[ℝ]) : normSq (phi g P) = normSq g * normSq P * normSq g := by
  unfold phi
  rw [map_mul, map_mul, normSq_star]

/-- The expression `phi g` sends the negative of a quaternion to the negative of its image. -/
lemma phi_neg (g P : ℍ[ℝ]) : phi g (-P) = -phi g P := by
  unfold phi
  calc g * -P * star g = (g * -P) * star g := rfl
    _ = (-(g * P)) * star g := by rw [mul_neg g P]
    _ = -((g * P) * star g) := neg_mul (g * P) (star g)

/-- Conjugation by a unit quaternion preserves zero real part. -/
lemma phi_re_zero {g P : ℍ[ℝ]} (hg : normSq g = 1) (hP : P.re = 0) : (phi g P).re = 0 := by
  unfold phi
  rw [re_mul_comm (g * P) (star g)]
  rw [← mul_assoc, star_mul_self]
  rw [re_mul]
  simp only [re_coe, imI_coe, imJ_coe, imK_coe, hg, hP]
  ring

/-- The square of a pure unit quaternion equals minus one. -/
lemma sq_eq_neg_one {u : ℍ[ℝ]} (hu : u.re = 0) (hn : normSq u = 1) :
    u * u = ((-1 : ℝ) : ℍ[ℝ]) := by
  ext <;> simp [re_mul, imI_mul, imJ_mul, imK_mul, hu, normSq_def'] at * <;> nlinarith

/-- For pure quaternions `u` and `v`, the sum `u * v + v * u` is the real scalar `-2 * qdot u
v`. -/
lemma uv_add_vu {u v : ℍ[ℝ]} (hu : u.re = 0) (hv : v.re = 0) :
    u * v + v * u = ((-2 * qdot u v : ℝ) : ℍ[ℝ]) := by
  ext <;> simp only [re_add, imI_add, imJ_add, imK_add, re_mul, imI_mul, imJ_mul, imK_mul,
    re_coe, imI_coe, imJ_coe, imK_coe, qdot, hu, hv] <;> ring

/-- For pure `u` and `v` with `u` of squared norm one, `u * v * u = v - (2 * qdot u v) • u`. -/
lemma uvu_eq {u v : ℍ[ℝ]} (hu : u.re = 0) (hv : v.re = 0) (hn : normSq u = 1) :
    u * v * u = v - (2 * qdot u v) • u := by
  have hsq : u * u = ((-1 : ℝ) : ℍ[ℝ]) := sq_eq_neg_one hu hn
  have hadd := uv_add_vu hu hv
  have hmain : u * (u * v + v * u) = u * u * v + u * v * u := by noncomm_ring
  rw [hadd, hsq] at hmain
  rw [← Quaternion.coe_commutes] at hmain
  rw [Quaternion.coe_mul_eq_smul] at hmain
  have h2 : (((-1 : ℝ)) : ℍ[ℝ]) * v = -v := by
    rw [Quaternion.coe_mul_eq_smul, neg_one_smul]
  rw [h2] at hmain
  have hsc : (-2 * qdot u v : ℝ) = -(2 * qdot u v) := by ring
  have hX : (2 * qdot u v) • u = v - u * v * u := by
    have hL : (((-(2 * qdot u v)) : ℝ) • u) = -v + u * v * u := by
      rw [← hsc]; exact hmain
    calc (2 * qdot u v) • u = -(((-(2 * qdot u v)) : ℝ) • u) := by
          rw [neg_smul (2 * qdot u v) u]; simp
      _ = -(-v + u * v * u) := by rw [hL]
      _ = v - u * v * u := by abel
  calc u * v * u = v + (u * v * u - v) := by abel
    _ = v + (-((2 * qdot u v) • u)) := by rw [hX]; abel
    _ = v - (2 * qdot u v) • u := by rw [sub_eq_add_neg]

/-- For pure `u` and `v` with `v` of squared norm one, `v * u * v = u - (2 * qdot u v) • v`. -/
lemma vuv_eq {u v : ℍ[ℝ]} (hu : u.re = 0) (hv : v.re = 0) (hn : normSq v = 1) :
    v * u * v = u - (2 * qdot u v) • v := by
  have hsq : v * v = ((-1 : ℝ) : ℍ[ℝ]) := sq_eq_neg_one hv hn
  have hadd := uv_add_vu hu hv
  have hmain : v * (u * v + v * u) = v * u * v + v * v * u := by noncomm_ring
  rw [hadd, hsq] at hmain
  rw [← Quaternion.coe_commutes] at hmain
  rw [Quaternion.coe_mul_eq_smul] at hmain
  have h2 : (((-1 : ℝ)) : ℍ[ℝ]) * u = -u := by
    rw [Quaternion.coe_mul_eq_smul, neg_one_smul]
  rw [h2] at hmain
  have hsc : (-2 * qdot u v : ℝ) = -(2 * qdot u v) := by ring
  have hX : (2 * qdot u v) • v = u - v * u * v := by
    have hL : (((-(2 * qdot u v)) : ℝ) • v) = v * u * v + -u := by
      rw [← hsc]; exact hmain
    calc (2 * qdot u v) • v = -(((-(2 * qdot u v)) : ℝ) • v) := by
          rw [neg_smul (2 * qdot u v) v]; simp
      _ = -(v * u * v + -u) := by rw [hL]
      _ = u - v * u * v := by abel
  calc v * u * v = u + (v * u * v - u) := by abel
    _ = u + (-((2 * qdot u v) • v)) := by rw [hX]; abel
    _ = u - (2 * qdot u v) • v := by rw [sub_eq_add_neg]

/-- For pure `u` and real `a`, `b`, the conjugate of `a + b * u` equals `a - b * u`. -/
lemma star_add_mul_of_re_zero {a b : ℝ} {u : ℍ[ℝ]} (hu : u.re = 0) :
    star ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*u) = (a:ℍ[ℝ]) - (b:ℍ[ℝ])*u := by
  rw [star_add, star_mul, star_coe, star_coe, star_eq_neg_of_re_zero hu]
  rw [neg_mul, ← Quaternion.coe_commutes b u, sub_eq_add_neg]

/-- For pure `u`, conjugation by `a + b * u` expands as `a ^ 2 * v + a * b * (u * v - v * u) - b
^ 2 * (u * v * u)`. -/
lemma phi_expand {a b : ℝ} {u v : ℍ[ℝ]} (hu : u.re = 0) :
    phi ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*u) v
      = ((a:ℍ[ℝ])^2) * v + ((a:ℍ[ℝ])*(b:ℍ[ℝ])) * (u*v - v*u) - ((b:ℍ[ℝ])^2) * (u*v*u) := by
  unfold phi
  rw [star_add_mul_of_re_zero hu]
  ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_add, imI_add, imJ_add, imK_add,
    re_sub, imI_sub, imJ_sub, imK_sub, re_coe, imI_coe, imJ_coe,
    imK_coe, pow_two] <;> ring

/-- For pure unit `u` and `v`, the difference between `phi (a + b * u) v` and `phi (star (a + b
* v)) u` equals the real scalar `(a ^ 2 - b ^ 2) - 2 * qdot u v * b ^ 2` times `v - u`. -/
lemma phi_diff {a b : ℝ} {u v : ℍ[ℝ]} (hu : u.re = 0) (hv : v.re = 0)
    (hnu : normSq u = 1) (hnv : normSq v = 1) :
    phi ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*u) v - phi (star ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*v)) u
      = (((a^2 - b^2) - 2*(qdot u v)*b^2 : ℝ) : ℍ[ℝ]) * (v - u) := by
  have h1 := phi_expand (a := a) (b := b) (u := u) (v := v) hu
  have h2 : phi (star ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*v)) u
      = ((a:ℍ[ℝ])^2) * u + ((a:ℍ[ℝ])*(b:ℍ[ℝ])) * (u*v - v*u) - ((b:ℍ[ℝ])^2) * (v*u*v) := by
    have h := phi_expand (a := a) (b := -b) (u := v) (v := u) hv
    have hstar : star ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*v) = (a:ℍ[ℝ]) + ((-b:ℝ):ℍ[ℝ])*v := by
      rw [star_add_mul_of_re_zero hv]
      rw [show ((-b:ℝ):ℍ[ℝ]) = -(b:ℍ[ℝ]) by rw [Quaternion.coe_neg]]
      rw [neg_mul, sub_eq_add_neg]
    rw [← hstar] at h
    rw [h]
    rw [show ((-b:ℝ):ℍ[ℝ]) = -(b:ℍ[ℝ]) by rw [Quaternion.coe_neg]]
    noncomm_ring
  rw [h1, h2, uvu_eq hu hv hnu, vuv_eq hu hv hnv]
  ext <;> simp [re_mul, imI_mul, imJ_mul, imK_mul, re_add, imI_add, imJ_add, imK_add,
    re_sub, imI_sub, imJ_sub, imK_sub, qdot, pow_two, smul_eq_mul] <;> ring

/-- A nonzero real number remains nonzero when embedded in the real quaternions. -/
lemma coe_real_ne_zero {b : ℝ} (hb : b ≠ 0) : ((b:ℝ):ℍ[ℝ]) ≠ 0 := by
  intro h
  exact hb (Quaternion.coe_inj.mp (by simpa using h))

/-- For pure unit axes `u`, `v`, normalized `g = a + b * u` and `h = c + d * v`, and `b ≠ 0`,
the braid relation holds exactly when `c = a` and either `d = b` with `phi g v = phi (star
h) u`, or `d = -b` with `phi g v = -phi (star h) u` [KauffmanLomonaco2006]. -/
theorem braid_relation_iff
    (a b c d : ℝ) (u v g h : ℍ[ℝ])
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : normSq u = 1) (hnv : normSq v = 1)
    (hg : g = (a:ℍ[ℝ]) + (b:ℍ[ℝ])*u)
    (hh : h = (c:ℍ[ℝ]) + (d:ℍ[ℝ])*v)
    (ha : a^2 + b^2 = 1) (hc : c^2 + d^2 = 1)
    (hb : b ≠ 0) :
    (g*h*g = h*g*h) ↔
      (c = a ∧ ((d = b ∧ phi g v = phi (star h) u) ∨
                (d = -b ∧ phi g v = -(phi (star h) u)))) := by
  subst hg
  subst hh
  set G : ℍ[ℝ] := (a:ℍ[ℝ]) + (b:ℍ[ℝ])*u with hG
  set H : ℍ[ℝ] := (c:ℍ[ℝ]) + (d:ℍ[ℝ])*v with hH
  have hnG : normSq G = 1 := by rw [hG, normSq_add_mul hu hnu, ha]
  have hnH : normSq H = 1 := by rw [hH, normSq_add_mul hv hnv, hc]
  have hGG : G * star G = 1 := by
    rw [Quaternion.self_mul_star, hnG]
    norm_num
  have hGstarG : star G * G = 1 := by
    rw [Quaternion.star_mul_self, hnG]
    norm_num
  have hHH : H * star H = 1 := by
    rw [Quaternion.self_mul_star, hnH]
    norm_num
  have hHH' : star H * H = 1 := by
    rw [Quaternion.star_mul_self, hnH]
    norm_num
  have hneG : G ≠ 0 := by
    intro hz
    have := hnG
    rw [normSq_eq_zero.mpr hz] at this
    norm_num at this
  have hneH : H ≠ 0 := by
    intro hz
    have := hnH
    rw [normSq_eq_zero.mpr hz] at this
    norm_num at this
  have hbq : ((b:ℝ):ℍ[ℝ]) ≠ 0 := coe_real_ne_zero hb
  have hcG : G * (c:ℍ[ℝ]) = (c:ℍ[ℝ]) * G := (Quaternion.coe_commutes c G).symm
  have hdG : G * (d:ℍ[ℝ]) = (d:ℍ[ℝ]) * G := (Quaternion.coe_commutes d G).symm
  have haSH : star H * (a:ℍ[ℝ]) = (a:ℍ[ℝ]) * star H :=
    (Quaternion.coe_commutes a (star H)).symm
  have hbSH : star H * (b:ℍ[ℝ]) = (b:ℍ[ℝ]) * star H :=
    (Quaternion.coe_commutes b (star H)).symm
  have hexpL : G*H*star G = (c:ℍ[ℝ]) + (d:ℍ[ℝ])*phi G v := by
    calc G*H*star G = G*((c:ℍ[ℝ])+(d:ℍ[ℝ])*v)*star G := by rw [hH]
      _ = G*(c:ℍ[ℝ])*star G + G*((d:ℍ[ℝ])*v)*star G := by noncomm_ring
      _ = (c:ℍ[ℝ])*(G*star G) + (d:ℍ[ℝ])*(G*v*star G) := by
            rw [hcG, ← mul_assoc G (d:ℍ[ℝ]) v, hdG]; noncomm_ring
      _ = (c:ℍ[ℝ]) * 1 + (d:ℍ[ℝ]) * (phi G v) := by
            rw [hGG, show phi G v = G*v*star G from rfl]
      _ = (c:ℍ[ℝ]) + (d:ℍ[ℝ])*phi G v := by noncomm_ring
  have hexpR : star H*G*H = (a:ℍ[ℝ]) + (b:ℍ[ℝ])*phi (star H) u := by
    calc star H*G*H = star H*((a:ℍ[ℝ])+(b:ℍ[ℝ])*u)*H := by rw [hG]
      _ = star H*(a:ℍ[ℝ])*H + star H*((b:ℍ[ℝ])*u)*H := by noncomm_ring
      _ = (a:ℍ[ℝ])*(star H*H) + (b:ℍ[ℝ])*(star H*u*H) := by
            rw [haSH, ← mul_assoc (star H) (b:ℍ[ℝ]) u, hbSH]; noncomm_ring
      _ = (a:ℍ[ℝ]) * 1 + (b:ℍ[ℝ]) * (phi (star H) u) := by
            rw [hHH', show phi (star H) u = star H*u*star (star H) from rfl, star_star]
      _ = (a:ℍ[ℝ]) + (b:ℍ[ℝ])*phi (star H) u := by noncomm_ring
  constructor
  · intro hbraid
    have hconv : G*H*star G = star H*G*H := by
      have key1 : H*(G*H*star G) = G*H := by
        calc H*(G*H*star G) = (H*G*H)*star G := by noncomm_ring
          _ = (G*H*G)*star G := by rw [← hbraid]
          _ = G*H*(G*star G) := by noncomm_ring
          _ = G*H := by rw [hGG, mul_one]
      have key2 : H*(star H*G*H) = G*H := by
        calc H*(star H*G*H) = (H*star H)*G*H := by noncomm_ring
          _ = G*H := by rw [hHH, one_mul]
      exact mul_left_cancel₀ hneH (key1.trans key2.symm)
    have heq : (c:ℍ[ℝ]) + (d:ℍ[ℝ])*phi G v = (a:ℍ[ℝ]) + (b:ℍ[ℝ])*phi (star H) u := by
      rw [← hexpL, ← hexpR]
      exact hconv
    have hp1 : (phi G v).re = 0 := phi_re_zero hnG hv
    have hp2 : (phi (star H) u).re = 0 :=
      phi_re_zero (by rw [normSq_star, hnH]) hu
    have hca : c = a := by
      have hre := congrArg (fun z : ℍ[ℝ] => z.re) heq
      simp only [re_add, re_mul, re_coe, imI_coe, imJ_coe, imK_coe, hp1, hp2,
        mul_zero, sub_zero, zero_mul, add_zero] at hre
      linarith
    have hvec : (d:ℍ[ℝ]) * phi G v = (b:ℍ[ℝ]) * phi (star H) u := by
      have h' := heq
      rw [hca] at h'
      exact add_left_cancel h'
    have hphi1 : normSq (phi G v) = 1 := by
      rw [phi_normSq, hnG, hnv]; ring
    have hphi2 : normSq (phi (star H) u) = 1 := by
      rw [phi_normSq, normSq_star, hnH, hnu]; ring
    have hd2 : d^2 = b^2 := by
      have hn := congrArg normSq hvec
      rw [map_mul, map_mul, hphi1, hphi2, Quaternion.normSq_coe, Quaternion.normSq_coe] at hn
      simpa using hn
    refine ⟨hca, ?_⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hd2 with hdb | hdb
    · left
      refine ⟨hdb, ?_⟩
      rw [hdb] at hvec
      exact mul_left_cancel₀ hbq hvec
    · right
      refine ⟨hdb, ?_⟩
      rw [hdb] at hvec
      have hcoeneg : ((-b:ℝ):ℍ[ℝ]) = -(b:ℍ[ℝ]) := Quaternion.coe_neg b
      have h1 : (-(b:ℍ[ℝ])) * phi G v = (b:ℍ[ℝ]) * phi (star H) u := by
        rw [← hcoeneg]
        exact hvec
      have hR : (-(b:ℍ[ℝ])) * (-(phi (star H) u)) = (b:ℍ[ℝ]) * phi (star H) u := by
        calc (-(b:ℍ[ℝ])) * (-(phi (star H) u))
            = -((b:ℍ[ℝ]) * (-(phi (star H) u))) := neg_mul (b:ℍ[ℝ]) (-(phi (star H) u))
          _ = -(-((b:ℍ[ℝ]) * phi (star H) u)) := by
              rw [mul_neg (b:ℍ[ℝ]) (phi (star H) u)]
          _ = (b:ℍ[ℝ]) * phi (star H) u := neg_neg _
      have h5 : (-(b:ℍ[ℝ])) * phi G v = (-(b:ℍ[ℝ])) * (-(phi (star H) u)) := by
        rw [hR]
        exact h1
      exact mul_left_cancel₀ (neg_ne_zero.mpr hbq) h5
  · rintro ⟨hca, hdisj⟩
    have hcoeneg : ((-b:ℝ):ℍ[ℝ]) = -(b:ℍ[ℝ]) := Quaternion.coe_neg b
    have hR : (-(b:ℍ[ℝ])) * (-(phi (star H) u)) = (b:ℍ[ℝ]) * phi (star H) u := by
      calc (-(b:ℍ[ℝ])) * (-(phi (star H) u))
          = -((b:ℍ[ℝ]) * (-(phi (star H) u))) := neg_mul (b:ℍ[ℝ]) (-(phi (star H) u))
        _ = -(-((b:ℍ[ℝ]) * phi (star H) u)) := by
            rw [mul_neg (b:ℍ[ℝ]) (phi (star H) u)]
        _ = (b:ℍ[ℝ]) * phi (star H) u := neg_neg _
    have hmain : G*H*star G = star H*G*H := by
      rcases hdisj with ⟨hdb, hphi⟩ | ⟨hdb, hphi⟩
      · rw [hexpL, hexpR, hca, hdb, hphi]
      · rw [hexpL, hexpR, hca, hdb, hphi, hcoeneg, hR]
    have k1 : H*(G*H*star G) = G*H := by
      calc H*(G*H*star G) = H*(star H*G*H) := by rw [hmain]
        _ = (H*star H)*G*H := by noncomm_ring
        _ = G*H := by rw [hHH, one_mul]
    have k2 : (H*(G*H*star G))*G = H*G*H := by
      calc (H*(G*H*star G))*G = H*G*H*(star G*G) := by noncomm_ring
        _ = H*G*H := by rw [hGstarG, mul_one]
    calc G*H*G = (G*H)*G := rfl
      _ = (H*(G*H*star G))*G := by rw [k1]
      _ = H*G*H := k2

/-- For distinct pure unit axes `u`, `v` and nonzero `b`, the equality `phi (a + b * u) v = phi
(star (a + b * v)) u` is equivalent to `qdot u v = (a ^ 2 - b ^ 2) / (2 * b ^ 2)`
[KauffmanLomonaco2006]. -/
theorem braid_condition_dot
    (a b : ℝ) (u v : ℍ[ℝ])
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : normSq u = 1) (hnv : normSq v = 1)
    (hb : b ≠ 0) (huv : u ≠ v) :
    phi ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*u) v = phi (star ((a:ℍ[ℝ]) + (b:ℍ[ℝ])*v)) u ↔
      qdot u v = (a^2 - b^2)/(2*b^2) := by
  have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb
  have hd := phi_diff (a := a) (b := b) (u := u) (v := v) hu hv hnu hnv
  have hvune : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  constructor
  · intro heq
    have hzero : ((((a^2 - b^2) - 2*(qdot u v)*b^2 : ℝ) : ℍ[ℝ]) * (v - u)) = 0 := by
      rw [← hd, heq, sub_self]
    rcases mul_eq_zero.mp hzero with h1 | h1
    · have hr : (a^2 - b^2) - 2*(qdot u v)*b^2 = 0 := Quaternion.coe_inj.mp h1
      field_simp
      nlinarith
    · exact absurd h1 hvune
  · intro hq
    rw [← sub_eq_zero, hd]
    have hzero : (a^2 - b^2) - 2*(qdot u v)*b^2 = 0 := by
      rw [hq]
      field_simp
      ring
    rw [hzero]
    simp

end Qatlib.Papers.AnyonicSpin06.MainResults.QuaternionBraid

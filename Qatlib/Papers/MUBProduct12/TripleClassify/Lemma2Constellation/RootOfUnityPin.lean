/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — the cube-root-of-unity contradiction in the proof of Lemma 2

McNulty–Weigert, fixed arXiv:1203.6887v2, Lemma 2 proof, pp. 9–10, Eqs. (33)–(38).

The second branch `S2` of the constellation admits a completing state of the form

> `|ψ₂⟩ = α |0_y, A^⊥⊥⟩ + β |1_y, B^⊥⊥⟩`   (Eq. (33)),

and the unbiasedness conditions `|⟨0_z, J_z | ψ₂⟩|² = 1/6` become, after writing the two
qutrit coefficients as third roots of unity `ω_J`, `ω'_J` (with `ω_0 = ω'_0 = 1`),

> `α β̄ ω_J ω̄'_J + ᾱ β ω̄_J ω'_J = 0`,  `J = 0, 1, 2`   (Eq. (36)).

The paper's argument (Eqs. (37)–(38)) is: `J = 0` forces `αβ̄ + ᾱβ = 0`, i.e. `t = αβ̄` is
purely imaginary; then for `J = 1, 2` the phase product `ω_J ω̄'_J` must be real; a real
third root of unity is `1`, so `ω_J = ω'_J`; comparing `J = 1, 2` gives `A^⊥⊥ = B^⊥⊥`,
contradicting their being distinct.  Hence `t = 0`, i.e. `α = 0` or `β = 0`, and `|ψ₂⟩` is
a product state.

This file formalises exactly that contradiction:
* `real_cube_eq_one` / `cube_root_real_eq_one` — a *real* cube root of `1` is `1`;
* `mu_cross_term_zero` — the expansion of the unbiasedness condition into Eq. (36);
* `root_of_unity_pin` — the pure algebra of Eqs. (37)–(38);
* `s2_completing_state_product` — the combined statement: the `S2` completing state is a
  product state because one of its two amplitudes vanishes.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-! ### A real cube root of unity is one -/

/-- A real number whose cube is `1` equals `1`. -/
theorem real_cube_eq_one {x : ℝ} (h : x ^ 3 = 1) : x = 1 := by
  have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by
    have h' : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
    rw [← h', h]; ring
  have hpos : 0 < x ^ 2 + x + 1 := by nlinarith [sq_nonneg (x + 1 / 2)]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · exact absurd h2 (ne_of_gt hpos)

/-- A complex cube root of unity that happens to be real equals `1`. -/
theorem cube_root_real_eq_one {z : ℂ} (hz : z ^ 3 = 1) (him : z.im = 0) : z = 1 := by
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hre : z.re ^ 3 = 1 := by
    have : ((z.re : ℂ)) ^ 3 = 1 := by rw [← hzr]; exact hz
    rw [← Complex.ofReal_inj]; push_cast; exact this
  rw [hzr, real_cube_eq_one hre]; simp

/-- The modulus squared of a cube is the cube of the modulus squared. -/
theorem normSq_cube (z : ℂ) : Complex.normSq (z ^ 3) = (Complex.normSq z) ^ 3 := by
  have h : z ^ 3 = z * (z * z) := by ring
  rw [h, Complex.normSq_mul, Complex.normSq_mul]
  ring

/-- A complex number with `z ^ 3 = 1` has modulus squared `1`. -/
theorem normSq_eq_one_of_cube {z : ℂ} (hz : z ^ 3 = 1) : Complex.normSq z = 1 := by
  have h3 : (Complex.normSq z) ^ 3 = 1 := by rw [← normSq_cube, hz]; simp
  exact real_cube_eq_one h3

/-! ### From unbiasedness to Eq. (36) -/

/-- **Expansion of the `S2` unbiasedness condition** (Eq. (34) → Eq. (36)).

Let `u J`, `v J` be two qutrit coefficient sequences with `‖u J‖² = ‖v J‖² = 1` (rescaling
of `⟨A^⊥⊥|J_z⟩`, `⟨B^⊥⊥|J_z⟩` by `√3`), and let `α, β` have `‖α‖² + ‖β‖² = 1`.
If every `|α u J + β v J|² = 1`, then the cross terms

> `Re (α β̄ · u J · conj (v J)) = 0`

vanish, which is Eq. (36) in `re` form. -/
theorem mu_cross_term_zero
    (α β : ℂ) (u v : Fin 3 → ℂ)
    (hu : ∀ J, Complex.normSq (u J) = 1) (hv : ∀ J, Complex.normSq (v J) = 1)
    (hαβ : Complex.normSq α + Complex.normSq β = 1)
    (hMU : ∀ J, Complex.normSq (α * u J + β * v J) = 1) :
    ∀ J, ((α * starRingEnd ℂ β) * (u J * starRingEnd ℂ (v J))).re = 0 := by
  intro J
  have h := hMU J
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul, hu J, hv J] at h
  have hcross : (2 * ((α * u J) * starRingEnd ℂ (β * v J)).re) = 0 := by linarith
  have hconv : ((α * u J) * starRingEnd ℂ (β * v J))
      = (α * starRingEnd ℂ β) * (u J * starRingEnd ℂ (v J)) := by
    rw [map_mul]; ring
  rw [hconv] at hcross
  linarith

/-! ### The pure algebra of Eqs. (37)–(38) -/

/-- **The cube-root pinning lemma** (Eqs. (37)–(38)).

Let `u, v : Fin 3 → ℂ` be third roots of unity with `u 0 = v 0 = 1` (the `J = 0`
coefficient is `1` in the paper's normal form).  If the pair `(u 1, u 2)` differs from
`(v 1, v 2)` — the states `|A^⊥⊥⟩`, `|B^⊥⊥⟩` are distinct — and the cross terms vanish
(Eq. (36)), then `α = 0` or `β = 0`. -/
theorem root_of_unity_pin
    (α β : ℂ) (u v : Fin 3 → ℂ)
    (hu0 : u 0 = 1) (hv0 : v 0 = 1)
    (hu : ∀ J, u J ^ 3 = 1) (hv : ∀ J, v J ^ 3 = 1)
    (hne : (u 1, u 2) ≠ (v 1, v 2))
    (heq : ∀ J, ((α * starRingEnd ℂ β) * (u J * starRingEnd ℂ (v J))).re = 0) :
    α = 0 ∨ β = 0 := by
  set t : ℂ := α * starRingEnd ℂ β with ht
  -- `J = 0` coefficient is `1`, so `t` is purely imaginary.
  have h0 : u 0 * starRingEnd ℂ (v 0) = 1 := by rw [hu0, hv0]; simp
  have ht_re : t.re = 0 := by
    have := heq 0
    rw [h0, mul_one] at this
    simpa [ht] using this
  have ht_eq : t = Complex.I * (t.im : ℂ) := by
    have hI : Complex.I * (t.im : ℂ) = ⟨0, t.im⟩ :=
      Complex.ext (by simp) (by simp)
    rw [show t = ⟨t.re, t.im⟩ from rfl, ht_re, hI]
  -- Auxiliary: if `t ≠ 0` then the `J`-th coefficients of the two states coincide.
  have key : ∀ J, t ≠ 0 → u J = v J := by
    intro J htne
    have him_ne : t.im ≠ 0 := by
      intro h
      apply htne
      rw [ht_eq, h]; simp
    set z : ℂ := u J * starRingEnd ℂ (v J) with hz
    have hz_re : (t * z).re = 0 := by
      rw [hz]
      simpa [ht] using heq J
    have hz_re2 : (Complex.I * ((t.im : ℂ) * z)).re = 0 := by
      have h := hz_re
      rw [ht_eq, mul_assoc] at h
      exact h
    rw [Complex.I_mul_re, Complex.mul_im] at hz_re2
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hz_re2
    have hprod : t.im * z.im = 0 := by linarith
    have hz_im : z.im = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h him_ne
      · exact h
    have hz3 : z ^ 3 = 1 := by
      rw [hz, mul_pow, ← map_pow (starRingEnd ℂ), hu J, hv J]
      simp
    have hz1 : z = 1 := cube_root_real_eq_one hz3 hz_im
    have hnorm : Complex.normSq (v J) = 1 := normSq_eq_one_of_cube (hv J)
    have h1 : u J * (starRingEnd ℂ (v J) * v J) = v J := by
      rw [← mul_assoc, ← hz, hz1, one_mul]
    rw [mul_comm (starRingEnd ℂ (v J)) (v J), Complex.mul_conj, hnorm] at h1
    simpa using h1
  by_contra hcon
  push Not at hcon
  obtain ⟨hα, hβ⟩ := hcon
  have htne : t ≠ 0 := by
    intro h
    rw [ht] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hα h'
    · exact hβ (by
        have := congrArg (starRingEnd ℂ) h'
        simpa using this)
  exact hne (by rw [key 1 htne, key 2 htne])

/-! ### The `S2` completing state is a product state -/

/-- **Lemma 2, `S2` branch** (Eqs. (33)–(38)): the completing state
`|ψ₂⟩ = α |0_y, A^⊥⊥⟩ + β |1_y, B^⊥⊥⟩` is a product state, i.e. `α = 0` or `β = 0`.

The hypotheses encode the paper's data: `u`, `v` are the rescaled qutrit coefficient
sequences of `|A^⊥⊥⟩`, `|B^⊥⊥⟩` (third roots of unity with first entry `1`), distinct; `α`,
`β` are normalized; and the three unbiasedness conditions read `|α u J + β v J|² = 1`
(Eq. (34) divided by the factor `1/6`). -/
theorem s2_completing_state_product
    (α β : ℂ) (u v : Fin 3 → ℂ)
    (hu0 : u 0 = 1) (hv0 : v 0 = 1)
    (hu : ∀ J, u J ^ 3 = 1) (hv : ∀ J, v J ^ 3 = 1)
    (hne : (u 1, u 2) ≠ (v 1, v 2))
    (hαβ : Complex.normSq α + Complex.normSq β = 1)
    (hMU : ∀ J, Complex.normSq (α * u J + β * v J) = 1) :
    α = 0 ∨ β = 0 :=
  root_of_unity_pin α β u v hu0 hv0 hu hv hne
    (mu_cross_term_zero α β u v
      (fun J => normSq_eq_one_of_cube (hu J))
      (fun J => normSq_eq_one_of_cube (hv J)) hαβ hMU)

end Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation

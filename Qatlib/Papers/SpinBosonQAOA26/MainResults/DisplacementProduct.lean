/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1 — products of displacement operators conditioned on `Z` values

Fixed source: arXiv:2505.07929v2, Lemma 1, Appendix IV, PDF p. 22, eqs. (92)–(94),
proved on pp. 22–24 (induction, eqs. (95)–(104)).

For spin values `a ∈ {1,-1}^p` the product of the displacement operators of the
generalized QAOA layer obeys

  `∏_{t=1}^{←p} D(-i γ_t a_t L_{:,t})
     = exp(-½ ∑_{r,s} i Im G^(sym)_{r,s} γ_r γ_s a_r a_s) D(-i ∑_t γ_t a_t L_{:,t})`  (92)

and, applied to the ground state `|0⟩^{⊗p'}`,

  `∏_{t=1}^{←p} D(-i γ_t a_t L_{:,t}) |0⟩^{⊗p'}
     = exp(-½ ∑_{r,s} i Im G^(sym)_{r,s} γ_r γ_s a_r a_s) | -i ∑_t γ_t a_t L_{:,t} ⟩`  (93).

This file proves the general Weyl-chain identity (the induction of eqs. (95)–(104) at
the level of the abstract `WeylFock` data) as `weyl_foldl`, and states the paper's
closed-form Lemma 1 as `lemma1_displacement_product` and `lemma1_on_vacuum`.

Convention note: `WeylFock.weyl` is the Weyl law of eq. (75), i.e.
`D z (D w b) = exp(i Im⟨z,w⟩) D(z+w) b` with `⟨z,w⟩ = ∑_l z_l \overline{w_l}`
(linear in the first argument, the `cdot` of `SourceDefinitions`).  The paper's
eqs. (100)–(104) use the same identity with the scalar bilinear in the other argument,
which is the conjugate form `exp(-i Im⟨z,w⟩)`; both describe the same Heisenberg group
law, and the sign in the exponent below is fixed by the `WeylFock.weyl` field.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.DisplacementProduct

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Total displacement of a list of displacement vectors (the argument of the single
`D` on the right-hand side of eq. (92)). -/
def weylSum {p' : ℕ} : List (Fin p' → ℂ) → (Fin p' → ℂ)
  | [] => 0
  | v :: vs => weylSum vs + v

/-- Accumulated phase of a list of displacement vectors: the exponent of eqs. (92),
(95), written as the sum over the induction steps of eqs. (96)–(104), namely
`i ∑_{s<t} Im⟨v_t, v_s⟩` (in the order in which the displacements are applied). -/
def weylPhase {p' : ℕ} : List (Fin p' → ℂ) → ℂ
  | [] => 0
  | v :: vs => weylPhase vs + Complex.I * (cdot (weylSum vs) v).im

/-- `cdot` is conjugate-linear in the second argument. -/
lemma cdot_add_right {N : ℕ} (z w w' : Fin N → ℂ) : cdot z (w + w') = cdot z w + cdot z w' := by
  simp only [cdot, Pi.add_apply, map_add, mul_add]
  rw [← Finset.sum_add_distrib]

/-- `cdot z 0 = 0`. -/
lemma cdot_zero_right {N : ℕ} (z : Fin N → ℂ) : cdot z 0 = 0 := by
  simp [cdot]

/-- Appending a displacement vector at the end of the list adds it to the total. -/
theorem weylSum_append {p' : ℕ} (vs : List (Fin p' → ℂ)) (w : Fin p' → ℂ) :
    weylSum (vs ++ [w]) = w + weylSum vs := by
  induction vs with
  | nil => simp [weylSum]
  | cons u us ih =>
      have h1 : weylSum ((u :: us) ++ [w]) = weylSum (us ++ [w]) + u := rfl
      rw [h1, ih]
      funext l
      simp only [weylSum, Pi.add_apply]
      ring

/-- Appending a displacement `w` at the end of the chain contributes the phase
`i Im⟨w, earlier total⟩` (note the argument order: the appended vector is the *first*
argument of `cdot`, unlike the head vector in the defining recursion). -/
theorem weylPhase_append {p' : ℕ} (vs : List (Fin p' → ℂ)) (w : Fin p' → ℂ) :
    weylPhase (vs ++ [w]) = weylPhase vs + Complex.I * (cdot w (weylSum vs)).im := by
  induction vs with
  | nil => simp [weylPhase, weylSum, cdot]
  | cons u us ih =>
      have h1 : weylPhase ((u :: us) ++ [w]) = weylPhase (us ++ [w])
          + Complex.I * (cdot (weylSum (us ++ [w])) u).im := rfl
      have h2 : weylPhase (u :: us) = weylPhase us
          + Complex.I * (cdot (weylSum us) u).im := rfl
      rw [h1, h2, ih, weylSum_append]
      simp only [weylSum]
      rw [cdot_add_left w (weylSum us) u, cdot_add_right w (weylSum us) u]
      rw [Complex.add_im, Complex.add_im]
      push_cast
      ring

/-- The total displacement of the ordered chain `f 0, …, f (n-1)`. -/
theorem weylSum_map_range {p' : ℕ} (f : ℕ → (Fin p' → ℂ)) (n : ℕ) :
    weylSum ((List.range n).map f) = fun l => ∑ k ∈ Finset.range n, f k l := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, weylSum_append, ih]
      funext l
      simp only [Pi.add_apply]
      rw [Finset.sum_range_succ]
      ring

/-- The phase of the ordered chain `f 0, …, f (n-1)` as the sum over strict pairs:
`i ∑_k Im⟨f k, ∑_{j < k} f j⟩`. -/
theorem weylPhase_map_range {p' : ℕ} (f : ℕ → (Fin p' → ℂ)) (n : ℕ) :
    weylPhase ((List.range n).map f) = Complex.I * ∑ k ∈ Finset.range n,
      (cdot (f k) (∑ j ∈ Finset.range k, f j)).im := by
  induction n with
  | zero => simp [weylPhase]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, weylPhase_append, ih,
        weylSum_map_range]
      rw [Finset.sum_range_succ]
      have hfun : (fun l => ∑ j ∈ Finset.range n, f j l) = ∑ j ∈ Finset.range n, f j :=
        funext fun l => (Finset.sum_apply l _ _).symm
      rw [hfun, Complex.ofReal_add]
      ring

/-- **The Weyl chain identity** (the induction of arXiv:2505.07929v2, Appendix IV,
eqs. (95)–(104), PDF p. 22–23).  The ordered product of displacement operators,
applied to any vector `b`, is a phase times the single displacement by the total vector.
This is the general form of Lemma 1, before specialising the displacement vectors to
`-i γ_t a_t L_{:,t}` and evaluating the phase as the quadratic form of eq. (92). -/
theorem weyl_foldl {p' : ℕ} (W : WeylFock p') (vs : List (Fin p' → ℂ)) (b : B) :
    vs.foldl (fun b v => (W.D v) b) b
      = (Complex.exp (weylPhase vs) : ℂ) • W.D (weylSum vs) b := by
  induction vs generalizing b with
  | nil =>
    simp [weylPhase, weylSum, WeylFock.D_zero_apply]
  | cons v vs ih =>
    rw [List.foldl_cons, ih (W.D v b), W.weyl (weylSum vs) v b, smul_smul]
    simp only [weylPhase, weylSum]
    rw [Complex.exp_add]

/-- **Lemma 1**, eq. (92) of arXiv:2505.07929v2 (PDF p. 22).  For a list of spin values
`a : Fin p → ℝ` (standing for `a ∈ {1,-1}^p`, eq. (91)) the ordered product of the
displacement operators `D(-i γ_t a_t L_{:,t})` equals the phase

  `exp(-½ ∑_{r,s} i Im G^(sym)_{r,s} γ_r γ_s a_r a_s)`

times the single displacement by `-i ∑_t γ_t a_t L_{:,t}`; the statement is the
operator identity evaluated at an arbitrary vector `b`. -/
theorem lemma1_displacement_product {p' p : ℕ} (W : WeylFock p')
    (L : Matrix (Fin p') (Fin p) ℂ) (γ a : Fin p → ℝ) (b : B) :
    (List.ofFn (fun t : Fin p => fun l => -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t)).foldl
        (fun y v => (W.D v) y) b
      = (Complex.exp ((-(1 / 2) : ℂ) * Complex.I *
          ((∑ r : Fin p, ∑ s : Fin p,
            (gramSym p' p L r s).im * (γ r * γ s * a r * a s)) : ℝ)) : ℂ) •
        W.D (fun l => ∑ t : Fin p, -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t) b := by
  classical
  -- The displacement chain as an ℕ-indexed family.
  set f : ℕ → (Fin p' → ℂ) := fun k =>
      if h : k < p then fun l => -Complex.I * (γ ⟨k, h⟩ : ℝ) * (a ⟨k, h⟩ : ℝ) * L l ⟨k, h⟩
      else 0 with hf
  have hofFn : (List.ofFn fun t : Fin p => fun l => -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t)
      = (List.range p).map f := by
    refine List.ext_getElem (by simp) ?_
    intro n h1 h2
    have hn : n < p := by simpa using h1
    have hlen : n < (List.range p).length := by
      rw [List.length_range]
      exact hn
    have h3 : (List.range p)[n]'hlen = n := List.getElem_range hlen
    rw [List.getElem_ofFn (by simpa using h1), List.getElem_map, h3]
    simp [hf, hn]
  -- The `cdot` of two chain vectors, as the conjugate Gram entry.
  have hgram : ∀ (r s : Fin p), ∑ l, L l r * starRingEnd ℂ (L l s)
      = starRingEnd ℂ (gramHerm p' p L r s) := by
    intro r s
    rw [gramHerm_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hss : starRingEnd ℂ (starRingEnd ℂ (L l r)) = L l r := by simp
    rw [map_mul, hss]
  have hcdot : ∀ k j, ∀ (hk : k < p) (hj : j < p), cdot (f k) (f j)
      = ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ) : ℂ)
        * starRingEnd ℂ (gramHerm p' p L ⟨k, hk⟩ ⟨j, hj⟩) := by
    intro k j hk hj
    have hc : starRingEnd ℂ ((γ ⟨j, hj⟩ : ℝ) : ℂ) = ((γ ⟨j, hj⟩ : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    have ha : starRingEnd ℂ ((a ⟨j, hj⟩ : ℝ) : ℂ) = ((a ⟨j, hj⟩ : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    rw [cdot]
    have h1 : ∀ l, f k l * starRingEnd ℂ (f j l)
        = ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ) : ℂ)
          * L l ⟨k, hk⟩ * starRingEnd ℂ (L l ⟨j, hj⟩) := by
      intro l
      simp only [hf, dif_pos hk, dif_pos hj, map_mul]
      rw [map_neg, Complex.conj_I, neg_neg, hc, ha]
      have hgroup : (-Complex.I * ((γ ⟨k, hk⟩ : ℝ) : ℂ) * ((a ⟨k, hk⟩ : ℝ) : ℂ)
            * L l ⟨k, hk⟩) * (Complex.I * ((γ ⟨j, hj⟩ : ℝ) : ℂ) * ((a ⟨j, hj⟩ : ℝ) : ℂ)
            * starRingEnd ℂ (L l ⟨j, hj⟩))
          = -((Complex.I : ℂ) * Complex.I)
            * (((γ ⟨k, hk⟩ : ℝ) : ℂ) * ((γ ⟨j, hj⟩ : ℝ) : ℂ)
              * ((a ⟨k, hk⟩ : ℝ) : ℂ) * ((a ⟨j, hj⟩ : ℝ) : ℂ))
            * L l ⟨k, hk⟩ * starRingEnd ℂ (L l ⟨j, hj⟩) := by ring
      have hmerge : (((γ ⟨k, hk⟩ : ℝ) : ℂ) * ((γ ⟨j, hj⟩ : ℝ) : ℂ)
            * ((a ⟨k, hk⟩ : ℝ) : ℂ) * ((a ⟨j, hj⟩ : ℝ) : ℂ))
          = ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hgroup, Complex.I_mul_I, hmerge]
      ring
    have hsum : ∑ l, ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ) : ℂ)
        * L l ⟨k, hk⟩ * starRingEnd ℂ (L l ⟨j, hj⟩)
      = ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ) : ℂ)
        * ∑ l, L l ⟨k, hk⟩ * starRingEnd ℂ (L l ⟨j, hj⟩) := by
      rw [Finset.sum_congr rfl fun l _ => mul_assoc _ _ _, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun l _ => h1 l, hsum, hgram ⟨k, hk⟩ ⟨j, hj⟩]
  -- `cdot` over a sum in the second argument.
  have hcdotsum : ∀ (z : Fin p' → ℂ) (g : ℕ → (Fin p' → ℂ)) (s : Finset ℕ),
      cdot z (∑ j ∈ s, g j) = ∑ j ∈ s, cdot z (g j) := by
    intro z g s
    classical
    induction s using Finset.induction_on with
    | empty => simp [cdot_zero_right]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, cdot_add_right, ih]
  -- The diagonal of `G^(sym)` has vanishing imaginary part.
  have hTdiag : ∀ r : Fin p,
      (gramSym p' p L r r).im * (γ r * γ r * a r * a r) = 0 := by
    intro r
    rw [gramSym_apply_of_le L (le_refl r), gramHerm_diag_im_zero L r]
    ring
  -- Double-sum vs strict-pairs identity (trichotomy, no symmetry needed).
  have hpair : ∑ r : Fin p, ∑ s : Fin p,
      (gramSym p' p L r s).im * (γ r * γ s * a r * a s)
      = 2 * ∑ r : Fin p, ∑ s : Fin p,
          if s < r then (gramHerm p' p L r s).im * (γ r * γ s * a r * a s) else 0 := by
    have hsplit : ∀ r s : Fin p,
        (if s < r then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0)
        + (if r < s then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0)
        = (gramSym p' p L r s).im * (γ r * γ s * a r * a s) := by
      intro r s
      rcases lt_trichotomy s r with h | h | h
      · rw [if_pos h, if_neg (by omega), add_zero]
      · rw [h, if_neg (lt_irrefl r), hTdiag r]
        ring
      · rw [if_neg (by omega), if_pos h, zero_add]
    have hA : ∑ r : Fin p, ∑ s : Fin p,
        (if s < r then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0)
        = ∑ r : Fin p, ∑ s : Fin p,
            if s < r then (gramHerm p' p L r s).im * (γ r * γ s * a r * a s) else 0 := by
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      by_cases h : s < r
      · rw [if_pos h, if_pos h, gramSym_apply_of_gt L (not_le_of_gt h)]
      · rw [if_neg h, if_neg h]
    have hB : ∑ r : Fin p, ∑ s : Fin p,
        (if r < s then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0)
        = ∑ r : Fin p, ∑ s : Fin p,
            if s < r then (gramHerm p' p L r s).im * (γ r * γ s * a r * a s) else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      by_cases h : s < r
      · rw [if_pos h, if_pos h, gramSym_apply_of_le L (le_of_lt h)]
        ring
      · rw [if_neg h, if_neg h]
    calc ∑ r : Fin p, ∑ s : Fin p,
          (gramSym p' p L r s).im * (γ r * γ s * a r * a s)
        = ∑ r : Fin p, ∑ s : Fin p,
            ((if s < r then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0)
              + if r < s then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0) :=
          Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => (hsplit r s).symm
      _ = (∑ r : Fin p, ∑ s : Fin p,
            if s < r then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0)
          + ∑ r : Fin p, ∑ s : Fin p,
            if r < s then (gramSym p' p L r s).im * (γ r * γ s * a r * a s) else 0 :=
          by simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hA, hB]; ring
  -- The phase of the chain, evaluated on the concrete displacement vectors.
  have hphase : weylPhase ((List.range p).map f)
      = (-(1 / 2 : ℂ) * Complex.I *
          ((∑ r : Fin p, ∑ s : Fin p,
            (gramSym p' p L r s).im * (γ r * γ s * a r * a s)) : ℝ) : ℂ) := by
    rw [weylPhase_map_range]
    have himc : ∀ z : ℂ, (starRingEnd ℂ z).im = -z.im := fun _ => rfl
    have e2 : ∀ (k j : ℕ), ∀ (hk : k < p) (hj : j < p), (cdot (f k) (f j)).im
        = -((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ)
            * (gramHerm p' p L ⟨k, hk⟩ ⟨j, hj⟩).im) := by
      intro k j hk hj
      rw [hcdot k j hk hj, Complex.im_ofReal_mul, himc, mul_neg]
    have e1 : ∀ k, ∀ (hkm : k ∈ Finset.range p),
        (cdot (f k) (∑ j ∈ Finset.range k, f j)).im
        = -(if hk : k < p then ∑ j ∈ Finset.range k,
            if hj : j < p then
              ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ)
                * (gramHerm p' p L ⟨k, hk⟩ ⟨j, hj⟩).im) else 0 else 0) := by
      intro k hkm
      have hk' : k < p := Finset.mem_range.mp hkm
      rw [dif_pos hk', hcdotsum, Complex.im_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hjm => ?_
      have hj' : j < p := lt_of_lt_of_le (Finset.mem_range.mp hjm) (le_of_lt hk')
      rw [dif_pos hj']
      exact e2 k j hk' hj'
    have hinner : ∀ (k : ℕ) (h : k ≤ p) (g : ℕ → ℝ),
        ∑ j ∈ Finset.range k, g j
          = ∑ s : Fin p, if s.val < k then g s.val else 0 := by
      intro k h g
      have hfilter : (Finset.range p).filter (fun n => n < k) = Finset.range k := by
        refine Finset.ext fun j => ?_
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      calc ∑ j ∈ Finset.range k, g j
          = ∑ j ∈ (Finset.range p).filter (fun n => n < k), g j := by rw [hfilter]
        _ = ∑ j ∈ Finset.range p, if j < k then g j else 0 := by
            rw [Finset.sum_filter]
        _ = ∑ s : Fin p, if s.val < k then g s.val else 0 := by
            rw [← Fin.sum_univ_eq_sum_range (fun n => if n < k then g n else 0)]
    have hconv : (∑ k ∈ Finset.range p, if hk : k < p then
          ∑ j ∈ Finset.range k, if hj : j < p then
            ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ)
              * (gramHerm p' p L ⟨k, hk⟩ ⟨j, hj⟩).im) else 0
        else 0)
      = ∑ r : Fin p, ∑ s : Fin p,
          if s < r then (gramHerm p' p L r s).im * (γ r * γ s * a r * a s) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => if hk : k < p then
        ∑ j ∈ Finset.range k, if hj : j < p then
          ((γ ⟨k, hk⟩ * γ ⟨j, hj⟩ * a ⟨k, hk⟩ * a ⟨j, hj⟩ : ℝ)
            * (gramHerm p' p L ⟨k, hk⟩ ⟨j, hj⟩).im) else 0
        else 0)]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hr : r.val < p := r.isLt
      rw [dif_pos hr]
      rw [hinner r.val (Nat.le_of_lt hr) (fun j => if hj : j < p then
        ((γ ⟨r.val, hr⟩ * γ ⟨j, hj⟩ * a ⟨r.val, hr⟩ * a ⟨j, hj⟩ : ℝ)
          * (gramHerm p' p L ⟨r.val, hr⟩ ⟨j, hj⟩).im) else 0)]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : s < r
      · rw [if_pos (show s.val < r.val from hs), if_pos hs,
          dif_pos (show s.val < p from s.isLt)]
        have hre : (⟨r.val, hr⟩ : Fin p) = r := Fin.eta r hr
        have hse : (⟨s.val, s.isLt⟩ : Fin p) = s := Fin.eta s s.isLt
        rw [hre, hse]
        ring
      · rw [if_neg hs, if_neg (show ¬ s.val < r.val from hs)]
    rw [Finset.sum_congr rfl e1, Finset.sum_neg_distrib, hconv, hpair]
    push_cast
    norm_num
    ring
  -- The total displacement of the chain.
  have hsumq : ∀ l, ∑ k ∈ Finset.range p, f k l
      = ∑ t : Fin p, -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t := by
    intro l
    have hF : ∀ k ∈ Finset.range p, f k l
        = (fun k => if hk : k < p then
            -Complex.I * (γ ⟨k, hk⟩ : ℝ) * (a ⟨k, hk⟩ : ℝ) * L l ⟨k, hk⟩ else 0) k := by
      intro k hk
      have hk' : k < p := Finset.mem_range.mp hk
      simp [hf, hk']
    rw [Finset.sum_congr rfl hF,
      ← Fin.sum_univ_eq_sum_range (fun k => if hk : k < p then
        -Complex.I * (γ ⟨k, hk⟩ : ℝ) * (a ⟨k, hk⟩ : ℝ) * L l ⟨k, hk⟩ else 0)]
    refine Finset.sum_congr rfl fun t _ => ?_
    have ht : t.val < p := t.isLt
    simp [ht]
  have hweylSum : weylSum ((List.range p).map f)
      = fun l => ∑ t : Fin p, -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t := by
    rw [weylSum_map_range]
    exact funext hsumq
  rw [hofFn, weyl_foldl, hphase, hweylSum]

/-- **Lemma 1 on the ground state**, eq. (93) of arXiv:2505.07929v2 (PDF p. 22):
the same identity applied to the vacuum, giving the coherent state
`| -i ∑_t γ_t a_t L_{:,t} ⟩ = D(-i ∑_t γ_t a_t L_{:,t}) |0⟩^{⊗p'}` (eq. (105)). -/
theorem lemma1_on_vacuum {p' p : ℕ} (W : WeylFock (B := B) p')
    (L : Matrix (Fin p') (Fin p) ℂ) (γ a : Fin p → ℝ) :
    (List.ofFn (fun t : Fin p => fun l => -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t)).foldl
        (fun y v => (W.D v) y) W.vacuum
      = (Complex.exp ((-(1 / 2) : ℂ) * Complex.I *
          ((∑ r : Fin p, ∑ s : Fin p,
            (gramSym p' p L r s).im * (γ r * γ s * a r * a s)) : ℝ)) : ℂ) •
        W.D (fun l => ∑ t : Fin p, -Complex.I * (γ t : ℂ) * (a t : ℂ) * L l t) W.vacuum :=
  lemma1_displacement_product (B := B) W L γ a W.vacuum

end Qatlib.Papers.SpinBosonQAOA26.MainResults.DisplacementProduct

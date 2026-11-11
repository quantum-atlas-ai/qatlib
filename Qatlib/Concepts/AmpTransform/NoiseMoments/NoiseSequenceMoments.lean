/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Uniform noise-sequence moments and corrected variance

This module defines `noiseAverage` and `noiseCharacterSum`, proves finite-average identities,
and computes character-sum mixed moments through degree four.
`noise_sequence_variance_corrected` includes the order-two resonance correction needed for the
affine-intensity variance in the noise model associated with [Cornwell2014].

## Main statements

* `noise_sequence_mixed_moments`: For nonzero frequency, computes the character sum's first and
  mixed moments through degree four, including the correction δ = 1 when 2y=0.
* `noise_sequence_second_moment`: At nonzero frequency, a uniform noise character sum has mean
  squared norm L, and its affine intensity has mean ‖c‖²+b²L.
* `noise_sequence_variance_corrected`: The centered affine intensity has variance
  b⁴(L²−L+δ(L²−L))+2b²L‖c‖²+2b²L · Re(c²)δ, where δ indicates 2y=0 and y is nonzero.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.AmpTransform.NoiseMoments
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The uniform finite average of a complex-valued function, defined as its sum divided by the
cardinality of the index type. -/
noncomputable def noiseAverage {A : Type} [Fintype A] (f : A→ℂ) : ℂ :=
  (Fintype.card A : ℂ)⁻¹*∑ a,f a

/-- The uniform finite average preserves addition. -/
@[simp] theorem noiseAverage_add {A : Type} [Fintype A] (f g : A→ℂ) :
    noiseAverage (fun a => f a+g a)=noiseAverage f+noiseAverage g := by
  simp [noiseAverage,Finset.sum_add_distrib,mul_add]

/-- The uniform finite average preserves subtraction. -/
@[simp] theorem noiseAverage_sub {A : Type} [Fintype A] (f g : A→ℂ) :
    noiseAverage (fun a => f a-g a)=noiseAverage f-noiseAverage g := by
  simp [noiseAverage,Finset.sum_sub_distrib,mul_sub]

/-- A constant complex factor on the left can be pulled outside the uniform finite average. -/
@[simp] theorem noiseAverage_mul_left {A : Type} [Fintype A] (c : ℂ) (f : A→ℂ) :
    noiseAverage (fun a => c*f a)=c*noiseAverage f := by simp [noiseAverage,← Finset.mul_sum,mul_left_comm]

/-- A constant complex factor on the right can be pulled outside the uniform finite average. -/
@[simp] theorem noiseAverage_mul_right {A : Type} [Fintype A] (f : A→ℂ) (c : ℂ) :
    noiseAverage (fun a => f a*c)=noiseAverage f*c := by simp [noiseAverage,← Finset.sum_mul,mul_assoc]

/-- On a nonempty finite type, the average of a constant is that constant. -/
@[simp] theorem noiseAverage_const {A : Type} [Fintype A] [Nonempty A] (c : ℂ) :
    noiseAverage (fun _ : A => c)=c := by
  have hn : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [noiseAverage,Finset.sum_const,hn]

/-- The uniform finite average commutes with complex conjugation. -/
@[simp] theorem noiseAverage_star {A : Type} [Fintype A] (f : A→ℂ) :
    noiseAverage (fun a => star (f a))=star (noiseAverage f) := by
  simp [noiseAverage,map_mul,map_sum,Complex.star_def,Complex.conj_natCast]

/-- The uniform finite average is unchanged by reindexing along an equivalence. -/
theorem noiseAverage_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : B→ℂ) :
    noiseAverage (fun a => f (e a))=noiseAverage f := by
  rw [noiseAverage,noiseAverage,Fintype.card_congr e,e.sum_comp]

/-- The average over a finite product equals the iterated uniform average. -/
theorem noiseAverage_prod {A B : Type} [Fintype A] [Fintype B] (f : A×B→ℂ) :
    noiseAverage f=noiseAverage (fun a => noiseAverage (fun b => f (a,b))) := by
  simp only [noiseAverage,Fintype.card_prod,Nat.cast_mul,_root_.mul_inv_rev,Fintype.sum_prod_type]
  rw [← Finset.mul_sum]
  ring

/-- The sum of the standard additive character at frequency y over the L labels in the noise
sequence. -/
noncomputable def noiseCharacterSum {N L : ℕ} [NeZero N] (y : ZMod N) (omega : Fin L→ZMod N) : ℂ :=
  ∑ i,ZMod.stdAddChar (omega i*y)

/-- Prepending a noise label adds its character value to `noiseCharacterSum`. -/
theorem noiseCharacterSum_cons {N L : ℕ} [NeZero N] (y x : ZMod N) (omega : Fin L→ZMod N) :
    noiseCharacterSum y (Fin.cons x omega)=noiseCharacterSum y omega+ZMod.stdAddChar (x*y) := by
  simp [noiseCharacterSum,Fin.sum_univ_succ,add_comm]

/-- Averaging a function of an (L+1)-tuple can be performed by first averaging over its head and
then its remaining L coordinates. -/
theorem noiseAverage_tuple_succ {N L : ℕ} [NeZero N] (f : (Fin (L+1)→ZMod N)→ℂ) :
    noiseAverage f=noiseAverage (fun omega : Fin L→ZMod N =>
      noiseAverage (fun x : ZMod N => f (Fin.cons x omega))) := by
  rw [← noiseAverage_equiv (Fin.consEquiv (fun _ : Fin (L+1) => ZMod N)),noiseAverage_prod]
  unfold noiseAverage
  simp only [← Finset.mul_sum,Fin.consEquiv_apply]
  rw [Finset.sum_comm]
  change (Fintype.card (ZMod N) : ℂ)⁻¹*((Fintype.card (Fin L→ZMod N) : ℂ)⁻¹*
    ∑ omega,∑ x,f (Fin.cons x omega)) =
    (Fintype.card (Fin L→ZMod N) : ℂ)⁻¹*((Fintype.card (ZMod N) : ℂ)⁻¹*∑ omega,∑ x,f (Fin.cons x omega))
  ring

/-- At nonzero frequency, a uniform character has mean zero, second moment one exactly when
2y=0, and pointwise squared modulus one. -/
theorem noise_single_character {N : ℕ} [NeZero N] (y : ZMod N) (hy : y≠0) :
    noiseAverage (fun x : ZMod N => ZMod.stdAddChar (x*y))=0 ∧
    noiseAverage (fun x : ZMod N => (ZMod.stdAddChar (x*y))^2)=
      (if 2*y=0 then 1 else 0 : ℂ) ∧
    (∀ x : ZMod N, ZMod.stdAddChar (x*y)*star (ZMod.stdAddChar (x*y))=1) := by
  have hm (t : ZMod N) : noiseAverage (fun x : ZMod N => ZMod.stdAddChar (x*t)) = if t=0 then 1 else 0 := by
    unfold noiseAverage
    simp_rw [mul_comm _ t]
    rw [sum_stdAddChar_mul]
    by_cases ht : t=0 <;> simp [ht,ZMod.card,NeZero.ne N]
  refine ⟨by simpa [hy] using hm y,?_,?_⟩
  · have hs (x : ZMod N) : (ZMod.stdAddChar (x*y))^2=ZMod.stdAddChar (x*(2*y)) := by
      rw [pow_two,← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [hs]
    exact hm (2*y)
  · intro x
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_stdAddChar]
    norm_num

/-- For a centered unit-modulus variable with real second moment δ, computes the first, second,
norm-square, cubic mixed, and fourth mixed moments after adding a constant shift. -/
theorem noise_fresh_moments {A : Type} [Fintype A] [Nonempty A] (X : A→ℂ) (delta s : ℂ)
    (h0 : noiseAverage X=0) (h2 : noiseAverage (fun x => X x^2)=delta)
    (hdelta : star delta=delta) (hu : ∀ x,X x*star (X x)=1) :
    noiseAverage (fun x => s+X x)=s ∧
    noiseAverage (fun x => (s+X x)^2)=s^2+delta ∧
    noiseAverage (fun x => (s+X x)*star (s+X x))=s*star s+1 ∧
    noiseAverage (fun x => (s+X x)^2*star (s+X x))=s^2*star s+2*s+delta*star s ∧
    noiseAverage (fun x => (s+X x)^2*(star (s+X x))^2)=
      s^2*(star s)^2+4*(s*star s)+1+delta*(s^2+(star s)^2) := by
  have hs0 : noiseAverage (fun x => star (X x))=0 := by rw [noiseAverage_star,h0];simp
  have hs2 : noiseAverage (fun x => (star (X x))^2)=delta := by
    rw [show (fun x => (star (X x))^2)=(fun x => star (X x^2)) by ext x;rw [star_pow],
      noiseAverage_star,h2,hdelta]
  refine ⟨by simp only [noiseAverage_add,noiseAverage_const,noiseAverage_mul_left,noiseAverage_mul_right,h0,mul_zero,zero_mul,zero_add,add_zero],?_,?_,?_,?_⟩
  · rw [show (fun x => (s+X x)^2)=(fun x => s^2+2*s*X x+X x^2) by ext x;ring]
    simp only [noiseAverage_add,noiseAverage_const,noiseAverage_mul_left,noiseAverage_mul_right,h0,h2,mul_zero,zero_mul,zero_add,add_zero]
  · rw [show (fun x => (s+X x)*star (s+X x))=
      (fun x => s*star s+s*star (X x)+(star s)*X x+1) by
        ext x;simp only [star_add];linear_combination hu x]
    simp only [noiseAverage_add,noiseAverage_const,noiseAverage_mul_left,noiseAverage_mul_right,h0,hs0,mul_zero,zero_mul,zero_add,add_zero]
  · rw [show (fun x => (s+X x)^2*star (s+X x))=
      (fun x => s^2*star s+s^2*star (X x)+(2*s*star s)*X x+
        2*s+(star s)*X x^2+X x) by
        ext x;simp only [star_add];linear_combination (2*s+X x)*(hu x)]
    simp only [noiseAverage_add,noiseAverage_const,noiseAverage_mul_left,noiseAverage_mul_right,h0,hs0,h2,mul_zero,zero_mul,zero_add,add_zero]
    ring
  · rw [show (fun x => (s+X x)^2*(star (s+X x))^2)=
      (fun x => s^2*(star s)^2+4*s*star s+1+
        (2*s^2*star s)*star (X x)+(2*s*(star s)^2)*X x+
        s^2*(star (X x))^2+(star s)^2*X x^2+
        (2*s)*star (X x)+(2*star s)*X x) by
        ext x;simp only [star_add]
        linear_combination (4*s*star s+2*s*star (X x)+2*star s*X x+X x*star (X x)+1)*(hu x)]
    simp only [noiseAverage_add,noiseAverage_const,noiseAverage_mul_left,noiseAverage_mul_right,h0,hs0,h2,hs2,mul_zero,zero_mul,zero_add,add_zero]
    ring

/-- For nonzero frequency, computes the character sum's first and mixed moments through degree
four, including the correction δ = 1 when 2y=0. -/
theorem noise_sequence_mixed_moments (N L : ℕ) [NeZero N] (y : ZMod N) (hy : y≠0) :
    let delta : ℂ := if 2*y=0 then 1 else 0;
    let S := noiseCharacterSum (L := L) y;
    noiseAverage S=0 ∧ noiseAverage (fun omega => S omega^2)=delta*(L : ℂ) ∧
    noiseAverage (fun omega => S omega*star (S omega))=(L : ℂ) ∧
    noiseAverage (fun omega => S omega^2*star (S omega))=0 ∧
    noiseAverage (fun omega => S omega^2*(star (S omega))^2)=
      2*(L : ℂ)^2-L+delta*((L : ℂ)^2-L) := by
  (try dsimp only)
  let delta : ℂ := if 2*y=0 then 1 else 0
  have hdelta : star delta=delta := by dsimp [delta];split_ifs <;> simp
  obtain ⟨h0,h2,hu⟩ := noise_single_character y hy
  induction L with
  | zero =>
    have hz : noiseCharacterSum (L := 0) y = (fun _ : Fin 0→ZMod N => (0 : ℂ)) := by
      ext omega;simp [noiseCharacterSum]
    rw [hz]
    simp
  | succ L ih =>
    have hstep := noise_fresh_moments (fun x : ZMod N => ZMod.stdAddChar (x*y)) delta
    simp only [Nat.cast_add,Nat.cast_one]
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [noiseAverage_tuple_succ]
      simp only [noiseCharacterSum_cons]
      simp only [(hstep _ h0 h2 hdelta hu).1]
      exact ih.1
    · rw [noiseAverage_tuple_succ]
      simp only [noiseCharacterSum_cons]
      simp only [(hstep _ h0 h2 hdelta hu).2.1,noiseAverage_add,noiseAverage_const,ih.2.1]
      ring
    · rw [noiseAverage_tuple_succ]
      simp only [noiseCharacterSum_cons]
      simp only [(hstep _ h0 h2 hdelta hu).2.2.1,noiseAverage_add,noiseAverage_const,ih.2.2.1]
    · rw [noiseAverage_tuple_succ]
      simp only [noiseCharacterSum_cons]
      simp only [(hstep _ h0 h2 hdelta hu).2.2.2.1,noiseAverage_add,noiseAverage_mul_left,
        noiseAverage_star,ih.1,ih.2.2.2.1,star_zero,mul_zero,zero_add,add_zero]
    · rw [noiseAverage_tuple_succ]
      simp only [noiseCharacterSum_cons]
      have hstarsq : noiseAverage (fun omega : Fin L→ZMod N => (star (noiseCharacterSum y omega))^2)=delta*(L : ℂ) := by
        rw [show (fun omega : Fin L→ZMod N => (star (noiseCharacterSum y omega))^2)=
          (fun omega => star ((noiseCharacterSum y omega)^2)) by ext omega;rw [star_pow],
          noiseAverage_star,ih.2.1,star_mul,hdelta]
        simp
        ring
      simp only [(hstep _ h0 h2 hdelta hu).2.2.2.2,noiseAverage_add,noiseAverage_const,
        noiseAverage_mul_left,ih.2.2.2.2,ih.2.2.1,ih.2.1,hstarsq]
      by_cases hr : 2*y=0 <;> simp only [delta,hr,if_true,if_false] <;> ring

/-- Averaging a real-valued function after embedding in ℂ equals the complex embedding of its
real uniform average. -/
theorem noiseAverage_real {A : Type} [Fintype A] (f : A→ℝ) :
    noiseAverage (fun a => (f a : ℂ)) = (((Fintype.card A : ℝ)⁻¹*∑ a,f a : ℝ) : ℂ) := by
  unfold noiseAverage
  push_cast
  rfl

/-- The type of length-L sequences in `ZMod N` has cardinality Nᴸ. -/
theorem noise_tuple_card (N L : ℕ) [NeZero N] : Fintype.card (Fin L→ZMod N)=N^L := by
  simp [Fintype.card_fun,ZMod.card]

/-- At nonzero frequency, a uniform noise character sum has mean squared norm L, and its affine
intensity has mean ‖c‖²+b²L. -/
theorem noise_sequence_second_moment : ∀ (N L : ℕ) [NeZero N] (y : ZMod N)
    (c : ℂ) (b : ℝ), y≠0 →
    let S := fun omega : Fin L→ZMod N => ∑ i,ZMod.stdAddChar (omega i*y);
    ((N : ℝ)^L)⁻¹*(∑ omega,‖S omega‖^2)=(L : ℝ) ∧
    ((N : ℝ)^L)⁻¹*(∑ omega,‖c+(b : ℂ)*S omega‖^2)=‖c‖^2+b^2*(L : ℝ) := by
  intro N L _ y c b hy
  (try dsimp only)
  obtain ⟨h0,h2,hn,h3,h4⟩ := noise_sequence_mixed_moments N L y hy
  have hnorm : noiseAverage (fun omega : Fin L→ZMod N => ((‖noiseCharacterSum y omega‖^2 : ℝ) : ℂ))=(L : ℂ) := by
    simpa only [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq] using hn
  have hshift : noiseAverage (fun omega : Fin L→ZMod N =>
      ((‖c+(b : ℂ)*noiseCharacterSum y omega‖^2 : ℝ) : ℂ))=
      (((‖c‖^2+b^2*(L : ℝ) : ℝ)) : ℂ) := by
    have he (omega : Fin L→ZMod N) : ((‖c+(b : ℂ)*noiseCharacterSum y omega‖^2 : ℝ) : ℂ) =
        (c*star c)+(b : ℂ)^2*(noiseCharacterSum y omega*star (noiseCharacterSum y omega))+
          ((b : ℂ)*star c)*noiseCharacterSum y omega+
          ((b : ℂ)*c)*star (noiseCharacterSum y omega) := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
      simp only [star_add,star_mul,Complex.star_def,map_add,map_mul,Complex.conj_ofReal]
      ring
    simp_rw [he]
    simp only [noiseAverage_add,noiseAverage_const,noiseAverage_mul_left,noiseAverage_star,
      h0,hn,star_zero,mul_zero,zero_add,add_zero]
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [noiseAverage_real,noise_tuple_card] at hnorm hshift
  exact ⟨by simpa only [Complex.ofReal_re,Complex.natCast_re,Nat.cast_pow,noiseCharacterSum] using congrArg Complex.re hnorm,
    by simpa only [Complex.ofReal_re,Nat.cast_pow,noiseCharacterSum] using congrArg Complex.re hshift⟩

/-- The centered affine intensity has variance b⁴(L²−L+δ(L²−L))+2b²L‖c‖²+2b²L · Re(c²)δ, where δ
indicates 2y=0 and y is nonzero. -/
theorem noise_sequence_variance_corrected : ∀ (N L : ℕ) [NeZero N] (y : ZMod N)
    (c : ℂ) (b : ℝ), y≠0 →
    let S := fun omega : Fin L→ZMod N => ∑ i,ZMod.stdAddChar (omega i*y);
    let mu := ‖c‖^2+b^2*(L : ℝ);
    let delta : ℝ := if 2*y=0 then 1 else 0;
    ((N : ℝ)^L)⁻¹*(∑ omega,(‖c+(b : ℂ)*S omega‖^2-mu)^2) =
      b^4*((L : ℝ)^2-L+delta*((L : ℝ)^2-L))+
        2*b^2*(L : ℝ)*‖c‖^2+2*b^2*(L : ℝ)*(c^2).re*delta := by
  intro N L _ y c b hy
  (try dsimp only)
  let S := noiseCharacterSum (L := L) y
  let delta : ℂ := if 2*y=0 then 1 else 0
  let mu : ℝ := ‖c‖^2+b^2*(L : ℝ)
  obtain ⟨h0,h2,hn,h3,h4⟩ := noise_sequence_mixed_moments N L y hy
  change noiseAverage S=0 at h0
  change noiseAverage (fun omega => S omega^2)=delta*(L : ℂ) at h2
  change noiseAverage (fun omega => S omega*star (S omega))=(L : ℂ) at hn
  change noiseAverage (fun omega => S omega^2*star (S omega))=0 at h3
  change noiseAverage (fun omega => S omega^2*(star (S omega))^2)=
    2*(L : ℂ)^2-L+delta*((L : ℂ)^2-L) at h4
  have h2bar : noiseAverage (fun omega : Fin L→ZMod N => (star (S omega))^2)=delta*(L : ℂ) := by
    rw [show (fun omega : Fin L→ZMod N => (star (S omega))^2)=
      (fun omega => star ((S omega)^2)) by ext omega;rw [star_pow],noiseAverage_star,h2]
    by_cases hr : 2*y=0 <;> simp [delta,hr]
  have h3bar : noiseAverage (fun omega : Fin L→ZMod N => S omega*(star (S omega))^2)=0 := by
    rw [show (fun omega : Fin L→ZMod N => S omega*(star (S omega))^2)=
      (fun omega => star ((S omega)^2*star (S omega))) by
        ext omega;simp only [star_mul,star_pow,star_star],noiseAverage_star,h3]
    simp
  have hm : (mu : ℂ)=c*star c+(b : ℂ)^2*(L : ℂ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    dsimp [mu]
    push_cast
    ring
  have hpoly (omega : Fin L→ZMod N) : (((‖c+(b : ℂ)*S omega‖^2-mu)^2 : ℝ) : ℂ) =
      (b : ℂ)^4*((S omega)^2*(star (S omega))^2)-
        (2*(b : ℂ)^4*(L : ℂ))*(S omega*star (S omega))+(b : ℂ)^4*(L : ℂ)^2+
        ((b : ℂ)^2*(star c)^2)*(S omega)^2+((b : ℂ)^2*c^2)*(star (S omega))^2+
        (2*(b : ℂ)^2*c*star c)*(S omega*star (S omega))+
        (2*(b : ℂ)^3*star c)*((S omega)^2*star (S omega))+
        (2*(b : ℂ)^3*c)*(S omega*(star (S omega))^2)-
        (2*(b : ℂ)^3*(L : ℂ)*star c)*S omega-
        (2*(b : ℂ)^3*(L : ℂ)*c)*star (S omega) := by
    rw [← Complex.normSq_eq_norm_sq]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self,hm]
    simp only [Complex.star_def,map_add,map_mul,Complex.conj_ofReal]
    ring
  have havg : noiseAverage (fun omega : Fin L→ZMod N =>
      (((‖c+(b : ℂ)*S omega‖^2-mu)^2 : ℝ) : ℂ)) =
      (b : ℂ)^4*((L : ℂ)^2-L+delta*((L : ℂ)^2-L))+
        2*(b : ℂ)^2*(L : ℂ)*(c*star c)+
        (b : ℂ)^2*(L : ℂ)*delta*(c^2+(star c)^2) := by
    simp_rw [hpoly]
    simp only [noiseAverage_add,noiseAverage_sub,noiseAverage_mul_left,noiseAverage_const,
      noiseAverage_star,h0,h2,hn,h3,h4,h2bar,h3bar,star_zero,mul_zero,zero_add,add_zero,sub_zero]
    ring
  have hc2 : c^2+(star c)^2=((2*(c^2).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two] <;> ring
  rw [hc2,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq] at havg
  have havgr : noiseAverage (fun omega : Fin L→ZMod N =>
      (((‖c+(b : ℂ)*S omega‖^2-mu)^2 : ℝ) : ℂ)) =
      ((b^4*((L : ℝ)^2-L+(if 2*y=0 then 1 else 0)*((L : ℝ)^2-L))+
        2*b^2*(L : ℝ)*‖c‖^2+2*b^2*(L : ℝ)*(c^2).re*(if 2*y=0 then 1 else 0) : ℝ) : ℂ) := by
    rw [havg]
    by_cases hr : 2*y=0 <;> simp only [delta,hr,if_true,if_false]
    all_goals push_cast
    all_goals ring
  rw [noiseAverage_real,noise_tuple_card] at havgr
  simpa only [Complex.ofReal_re,Nat.cast_pow,mu,S,noiseCharacterSum] using congrArg Complex.re havgr

end Qatlib.Concepts.AmpTransform.NoiseMoments

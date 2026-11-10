/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ConditionalAmplifiedNoise
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open scoped Classical BigOperators

private def bernoulliLevelWeight (n : ℕ) (p : ℝ) (l : ℕ) : ℝ :=
  (n.choose l : ℝ) * p^l * (1-p)^(n-l)

private theorem bernoulli_level_succ (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    (∑ l ∈ Finset.range (n+2), bernoulliLevelWeight (n+1) p l * f l) =
      (1-p)*(∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l * f l) +
      p*(∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l * f (l+1)) := by
  simp only [bernoulliLevelWeight]
  simp_rw [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => p^i * ((1-p)^j * f i)) n]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro l hl
    have hln : l ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    rw [show n+1-l = (n-l)+1 by omega, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro l _hl
    rw [pow_succ]
    ring

private theorem bernoulli_level_mass (n : ℕ) (p : ℝ) :
    (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l) = 1 := by
  induction n with
  | zero => simp [bernoulliLevelWeight]
  | succ n ih =>
    have h := bernoulli_level_succ n p (fun _ => 1)
    simp only [mul_one] at h
    rw [h, ih]
    ring

private theorem bernoulli_level_first (n : ℕ) (p : ℝ) :
    (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l * (l : ℝ)) = (n : ℝ)*p := by
  induction n with
  | zero => simp [bernoulliLevelWeight]
  | succ n ih =>
    rw [show n+1+1 = n+2 by omega, bernoulli_level_succ]
    have hshift : (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l * ((l+1 : ℕ) : ℝ)) =
        (n : ℝ)*p+1 := by
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Finset.sum_add_distrib]
      rw [ih, bernoulli_level_mass]
    rw [ih, hshift, Nat.cast_add, Nat.cast_one]
    ring

private theorem bernoulli_level_factorial (n : ℕ) (p : ℝ) :
    (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l * ((l : ℝ)*((l : ℝ)-1))) =
      (n : ℝ)*((n : ℝ)-1)*p^2 := by
  induction n with
  | zero => simp [bernoulliLevelWeight]
  | succ n ih =>
    rw [show n+1+1 = n+2 by omega, bernoulli_level_succ]
    have hshift : (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l *
        (((l+1 : ℕ) : ℝ)*(((l+1 : ℕ) : ℝ)-1))) =
        (n : ℝ)*((n : ℝ)-1)*p^2 + 2*((n : ℝ)*p) := by
      calc
        _ = (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l *
            ((l : ℝ)*((l : ℝ)-1))) +
            2*(∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l * (l : ℝ)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro l _
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        _ = _ := by rw [ih, bernoulli_level_first]
    rw [ih, hshift, Nat.cast_add, Nat.cast_one]
    ring

theorem bernoulli_quadratic_level_sum (n : ℕ) (p a b c : ℝ) :
    (∑ l ∈ Finset.range (n+1), (n.choose l : ℝ)*p^l*(1-p)^(n-l)*
      (a+b*(l : ℝ)+c*((l : ℝ)*((l : ℝ)-1)))) =
      a+b*((n : ℝ)*p)+c*((n : ℝ)*((n : ℝ)-1)*p^2) := by
  change (∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l *
    (a+b*(l : ℝ)+c*((l : ℝ)*((l : ℝ)-1)))) = _
  calc
    _ = a*(∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l) +
        b*(∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l*(l : ℝ)) +
        c*(∑ l ∈ Finset.range (n+1), bernoulliLevelWeight n p l*
          ((l : ℝ)*((l : ℝ)-1))) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [bernoulli_level_mass, bernoulli_level_first, bernoulli_level_factorial]
      ring

private theorem bernoulli_layer_sum {X : Type} [DecidableEq X]
    (C : Finset X) (f : ℕ → ℝ) :
    (∑ S ∈ C.powerset, f S.card) =
      ∑ l ∈ Finset.range (C.card+1), (C.card.choose l : ℝ)*f l := by
  simpa only [nsmul_eq_mul] using (Finset.sum_powerset_apply_card f (x := C))

private theorem bernoulli_subset_card_expect {X : Type} [DecidableEq X]
    (C : Finset X) (p : ℝ) (f : ℕ → ℝ) :
    (∑ S ∈ C.powerset, p^S.card*(1-p)^(C.card-S.card)*f S.card) =
      ∑ l ∈ Finset.range (C.card+1), bernoulliLevelWeight C.card p l * f l := by
  simpa only [bernoulliLevelWeight, mul_assoc] using
    bernoulli_layer_sum C (fun l => p^l*(1-p)^(C.card-l)*f l)

def bernoulliSubsetLaw (N : ℕ) [NeZero N] (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FinDist (Finset (ZMod N)) where
  prob S := p^S.card*(1-p)^(N-S.card)
  nonneg S := mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  sum_one := by
    have h := bernoulli_subset_card_expect (Finset.univ : Finset (ZMod N)) p (fun _ => 1)
    simp only [Finset.powerset_univ, Finset.card_univ, ZMod.card, mul_one] at h
    exact h.trans (bernoulli_level_mass N p)

theorem bernoulli_subset_actual_law :
  ∀ (N : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∃ d : FinDist (Finset (ZMod N)),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) ∧
      (∀ L : ℕ, ∑ S ∈ (Finset.univ : Finset (ZMod N)).powersetCard L, d.prob S =
        ((N.choose L : ℝ)) * p ^ L * (1 - p) ^ (N - L)) ∧
      d.expect (fun S => (S.card : ℝ)) = (N : ℝ) * p ∧
      d.expect (fun S => ((S.card : ℝ) - (N : ℝ) * p) ^ 2) = (N : ℝ) * p * (1 - p) := by
  intro N _ p hp hp1
  refine ⟨bernoulliSubsetLaw N p hp hp1, fun _ => rfl, ?_, ?_, ?_⟩
  · intro L
    change (∑ S ∈ (Finset.univ : Finset (ZMod N)).powersetCard L,
      p^S.card*(1-p)^(N-S.card)) = _
    rw [Finset.sum_powersetCard L (Finset.univ : Finset (ZMod N))
      (fun l => p^l*(1-p)^(N-l))]
    simp only [nsmul_eq_mul, Finset.card_univ, ZMod.card]
    ring
  · have h := bernoulli_subset_card_expect (Finset.univ : Finset (ZMod N)) p (fun l => (l : ℝ))
    simp only [Finset.powerset_univ, Finset.card_univ, ZMod.card] at h
    exact h.trans (bernoulli_level_first N p)
  · change (∑ S : Finset (ZMod N), p^S.card*(1-p)^(N-S.card)*
      ((S.card : ℝ)-(N : ℝ)*p)^2) = _
    have h := bernoulli_subset_card_expect (Finset.univ : Finset (ZMod N)) p
      (fun l => ((l : ℝ)-(N : ℝ)*p)^2)
    simp only [Finset.powerset_univ, Finset.card_univ, ZMod.card] at h
    rw [h]
    calc
      _ = ∑ l ∈ Finset.range (N+1), bernoulliLevelWeight N p l *
          (((N : ℝ)*p)^2+(1-2*(N : ℝ)*p)*(l : ℝ)+
            1*((l : ℝ)*((l : ℝ)-1))) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ((N : ℝ)*p)^2+(1-2*(N : ℝ)*p)*((N : ℝ)*p)+
          1*((N : ℝ)*((N : ℝ)-1)*p^2) :=
        bernoulli_quadratic_level_sum N p (((N : ℝ)*p)^2) (1-2*(N : ℝ)*p) 1
      _ = _ := by ring

private theorem bernoulli_fixed_level_sum (N : ℕ) [NeZero N] (p : ℝ)
    (d : FinDist (Finset (ZMod N)))
    (hd : ∀ S, d.prob S = p^S.card*(1-p)^(N-S.card))
    (C : Finset (ZMod N)) (L : ℕ) (f : Finset (ZMod N) → ℝ) :
    (∑ S ∈ C.powersetCard L, d.prob S*f S) =
      p^L*(1-p)^(N-L)*(∑ S ∈ C.powersetCard L, f S) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [hd S, (Finset.mem_powersetCard.mp hS).2]

theorem bernoulli_complement_transport (N : ℕ) [NeZero N] (p : ℝ)
    (d : FinDist (Finset (ZMod N)))
    (hd : ∀ S, d.prob S = p^S.card*(1-p)^(N-S.card))
    (A : Finset (ZMod N)) (f : Finset (ZMod N) → ℝ) :
    let C := Finset.univ \ A
    (∑ S ∈ C.powerset, d.prob S*f S) = (1-p)^A.card *
      ∑ L ∈ Finset.range (C.card+1), p^L*(1-p)^(C.card-L)*
        ∑ S ∈ C.powersetCard L, f S := by
  (try dsimp only)
  let C := Finset.univ \ A
  have hcard : C.card+A.card = N := by
    simpa only [Finset.card_univ, ZMod.card] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hcard' : N = A.card+C.card := by omega
  calc
    _ = (1-p)^A.card *
        ∑ S ∈ C.powerset, p^S.card*(1-p)^(C.card-S.card)*f S := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      have hSC := Finset.card_le_card (Finset.mem_powerset.mp hS)
      have hexp : N-S.card = A.card+(C.card-S.card) := by
        exact (congrArg (fun n : ℕ => n-S.card) hcard').trans (Nat.add_sub_assoc hSC A.card)
      rw [hd S, hexp, pow_add]
      ring
    _ = _ := by
      rw [Finset.sum_powerset]
      congr 1
      apply Finset.sum_congr rfl
      intro L _hL
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]

theorem bernoulli_conditional_complement_uniform :
  ∀ (N : ℕ) [NeZero N] (p : ℝ), 0 < p → p < 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
      ∀ (A : Finset (ZMod N)) (L : ℕ),
        let C := Finset.univ \ A
        L ≤ C.card →
        let T := C.powersetCard L
        (∑ S ∈ T, d.prob S) = (C.card.choose L : ℝ) * p ^ L * (1 - p) ^ (N - L) ∧
        (∀ f : Finset (ZMod N) → ℝ,
          (∑ S ∈ T, d.prob S)⁻¹ * (∑ S ∈ T, d.prob S * f S) =
            conditionalNoiseMean C L f) ∧
        (∀ f : Finset (ZMod N) → ℝ,
          (∑ S ∈ C.powerset, d.prob S * f S) =
            (1 - p) ^ A.card *
              ∑ L ∈ Finset.range (C.card + 1), p ^ L * (1 - p) ^ (C.card - L) *
                ∑ S ∈ C.powersetCard L, f S) := by
  intro N _ p hp hp1 d hd A L C hL
  (try dsimp only)
  have hmass : (∑ S ∈ C.powersetCard L, d.prob S) =
      (C.card.choose L : ℝ)*p^L*(1-p)^(N-L) := by
    have h := bernoulli_fixed_level_sum N p d hd C L (fun _ => 1)
    simpa only [mul_one, one_mul, Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, mul_comm, mul_left_comm, mul_assoc] using h
  refine ⟨hmass, ?_, bernoulli_complement_transport N p d hd A⟩
  intro f
  rw [hmass, bernoulli_fixed_level_sum N p d hd C L f,
    conditionalNoiseMean, Finset.card_powersetCard]
  have hc : (C.card.choose L : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hL).ne'
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  field_simp

theorem bernoulli_complement_mean_transport (N : ℕ) [NeZero N] (p : ℝ)
    (d : FinDist (Finset (ZMod N)))
    (hd : ∀ S, d.prob S = p^S.card*(1-p)^(N-S.card))
    (A : Finset (ZMod N)) (f : Finset (ZMod N) → ℝ) :
    let C := Finset.univ \ A
    (∑ S ∈ C.powerset, d.prob S*f S) = (1-p)^A.card *
      ∑ L ∈ Finset.range (C.card+1), (C.card.choose L : ℝ)*p^L*(1-p)^(C.card-L)*
        conditionalNoiseMean C L f := by
  (try dsimp only)
  rw [bernoulli_complement_transport N p d hd A f]
  congr 1
  apply Finset.sum_congr rfl
  intro L hL
  have hc : ((Finset.univ \ A).card.choose L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hL))).ne'
  rw [conditionalNoiseMean, Finset.card_powersetCard]
  field_simp

theorem bernoulli_mixed_second_moment :
  ∀ (N : ℕ) [NeZero N] (p : ℝ), 0 ≤ p → p ≤ 1 →
    ∀ (d : FinDist (Finset (ZMod N))),
      (∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card)) →
      ∀ (A : Finset (ZMod N)) (y : ZMod N),
        let C := Finset.univ \ A
        2 ≤ C.card →
        let a := distinctNoiseFourier A y
        let c := distinctNoiseFourier C y
        (∑ L ∈ Finset.range (C.card + 1), (C.card.choose L : ℝ) * p ^ L *
            (1 - p) ^ (C.card - L) *
            conditionalNoiseMean C L (fun S => ‖distinctNoiseFourier (A ∪ S) y‖ ^ 2)) =
          ‖a‖ ^ 2 + 2 * p * (a * star c).re + (C.card : ℝ) * p +
            p ^ 2 * (‖c‖ ^ 2 - (C.card : ℝ)) ∧
        (∑ S ∈ C.powerset, d.prob S * ‖distinctNoiseFourier (A ∪ S) y‖ ^ 2) =
          (1 - p) ^ A.card *
            (‖a‖ ^ 2 + 2 * p * (a * star c).re + (C.card : ℝ) * p +
              p ^ 2 * (‖c‖ ^ 2 - (C.card : ℝ))) := by
  intro N _ p _hp _hp1 d hd A y C hC
  (try dsimp only)
  let a := distinctNoiseFourier A y
  let c := distinctNoiseFourier C y
  have hn : (C.card : ℝ) ≠ 0 := by exact_mod_cast (show C.card ≠ 0 by omega)
  have hn1 : (C.card : ℝ)-1 ≠ 0 := by
    have hc : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hC
    linarith
  have hmix : (∑ L ∈ Finset.range (C.card+1), bernoulliLevelWeight C.card p L *
      conditionalNoiseMean C L (fun S => ‖distinctNoiseFourier (A ∪ S) y‖^2)) =
      ‖a‖^2+2*p*(a*star c).re+(C.card : ℝ)*p+p^2*(‖c‖^2-(C.card : ℝ)) := by
    calc
      _ = ∑ L ∈ Finset.range (C.card+1), bernoulliLevelWeight C.card p L *
          (‖a‖^2+2*(L : ℝ)/C.card*(a*star c).re+(L : ℝ)+
            ((L : ℝ)*((L : ℝ)-1)/((C.card : ℝ)*((C.card : ℝ)-1)))*
              (‖c‖^2-(C.card : ℝ))) := by
        apply Finset.sum_congr rfl
        intro L hL
        apply congrArg (bernoulliLevelWeight C.card p L * ·)
        exact (conditional_signal_noise_mixed_second_moment N L A y hC
          (Nat.le_of_lt_succ (Finset.mem_range.mp hL))).2
      _ = ∑ L ∈ Finset.range (C.card+1), bernoulliLevelWeight C.card p L *
          (‖a‖^2+(2*(a*star c).re/(C.card : ℝ)+1)*(L : ℝ)+
            ((‖c‖^2-(C.card : ℝ))/((C.card : ℝ)*((C.card : ℝ)-1)))*
              ((L : ℝ)*((L : ℝ)-1))) := by
        apply Finset.sum_congr rfl
        intro L _
        ring
      _ = ‖a‖^2+(2*(a*star c).re/(C.card : ℝ)+1)*((C.card : ℝ)*p)+
          ((‖c‖^2-(C.card : ℝ))/((C.card : ℝ)*((C.card : ℝ)-1)))*
            ((C.card : ℝ)*((C.card : ℝ)-1)*p^2) :=
        bernoulli_quadratic_level_sum C.card p (‖a‖^2)
          (2*(a*star c).re/(C.card : ℝ)+1)
          ((‖c‖^2-(C.card : ℝ))/((C.card : ℝ)*((C.card : ℝ)-1)))
      _ = _ := by
        field_simp
        ring
  refine ⟨hmix, ?_⟩
  rw [bernoulli_complement_mean_transport N p d hd A]
  exact congrArg ((1-p)^A.card * ·) hmix

end Qatlib.Concepts.AmpTransform.ErrorStream

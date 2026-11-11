/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.VertexSamplingQuan
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

/-!
# Finite majority concentration

`uniformFiniteLaw` equips a nonempty finite type with its uniform distribution. The module
translates indicator expectations and independent-sample event probabilities into cardinality
ratios, then bounds the probability that at least half of the rounds satisfy a predicate of
frequency at most `1 / 5`.

These finite concentration estimates support repetition and error reduction in search algorithms
[BoyerEtAl1998].

## Main statements

* `finite_bad_round_majority`: the bound `2 * exp (-9 * K / 50)` for a bad majority.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

/-- The uniform probability distribution on a nonempty finite type, assigning mass `1 /
Fintype.card X` to every element. -/
def uniformFiniteLaw (X : Type) [Fintype X] [Nonempty X] : FinDist X where
  prob _ := 1/(Fintype.card X:ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hp : (0:ℝ)<Fintype.card X := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card X)
    field_simp

/-- The expectation of a predicate indicator under the uniform law equals the fraction of
elements satisfying the predicate. -/
theorem uniformFiniteLaw_indicator_mean {X : Type} [Fintype X] [Nonempty X]
    (P : X→Prop) [DecidablePred P] :
    (uniformFiniteLaw X).expect (fun x=>if P x then 1 else 0) =
      ((Finset.univ.filter P).card:ℝ)/(Fintype.card X:ℝ) := by
  simp only [FinDist.expect,uniformFiniteLaw,mul_ite,mul_one,mul_zero,← Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul]
  ring

/-- Under independent uniform sampling, an event on `K` samples has probability equal to its
cardinality divided by the sample-space cardinality. -/
theorem uniformFiniteLaw_event_card {X : Type} [Fintype X] [Nonempty X] (K : ℕ)
    (P : (Fin K→X)→Prop) [DecidablePred P] :
    (∑ ω∈Finset.univ.filter P,(independentSampleLaw (fun _ : Fin K=>uniformFiniteLaw X)).prob ω) =
      ((Finset.univ.filter P).card:ℝ)/(Fintype.card (Fin K→X):ℝ) := by
  simp only [independentSampleLaw,uniformFiniteLaw,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,one_div,Finset.sum_const,nsmul_eq_mul,Fintype.card_fun,Nat.cast_pow]
  ring

/-- The sum of the real-valued predicate indicators equals the number of rounds satisfying the
predicate. -/
theorem sum_round_indicators {X : Type} (K : ℕ) (P : X→Prop) [DecidablePred P] (ω : Fin K→X) :
    (∑ i : Fin K,if P (ω i) then (1:ℝ) else 0)=((Finset.univ.filter (fun i=>P (ω i))).card:ℝ) := by
  simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

/-- If a predicate holds on at most one fifth of a finite space, the fraction of `K`-sample
tapes with at least half bad rounds is at most `2 * Real.exp (-9 * K / 50)`. -/
theorem finite_bad_round_majority {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (K : ℕ) (hK : 0<K) (P : X→Prop) [DecidablePred P]
    (hP : ((Finset.univ.filter P).card:ℝ)/(Fintype.card X:ℝ)≤1/5) :
    ((Finset.univ.filter (fun ω : Fin K→X=>K≤2*(Finset.univ.filter (fun i=>P (ω i))).card)).card:ℝ)/
      (Fintype.card (Fin K→X):ℝ) ≤ 2*Real.exp (-9*(K:ℝ)/50) := by
  let p := uniformFiniteLaw X
  let f : (Fin K→X)→ℝ := fun ω=>∑ i : Fin K,if P (ω i) then 1 else 0
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  have hd : ∀ i (ω τ : Fin K→X),(∀ j,j≠i→ω j=τ j)→|f ω-f τ|≤(1:ℝ) := by
    intro i ω τ h
    have he : f ω-f τ=(if P (ω i) then (1:ℝ) else 0)-(if P (τ i) then 1 else 0) := by
      dsimp [f]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_eq_single i (fun j _ hj=>by rw [h j hj,sub_self])
          (fun hi=>False.elim (hi (Finset.mem_univ i)))
    rw [he]
    split_ifs <;> norm_num
  have hm : (independentSampleLaw (fun _ : Fin K=>p)).expect f ≤ (K:ℝ)/5 := by
    have he : (independentSampleLaw (fun _ : Fin K=>p)).expect f =
        (K:ℝ)*p.expect (fun x=>if P x then 1 else 0) := by
      calc
        (independentSampleLaw (fun _ : Fin K=>p)).expect f =
            ∑ i : Fin K,(independentSampleLaw (fun _ : Fin K=>p)).expect (fun ω=>if P (ω i) then 1 else 0) := by
          simp only [FinDist.expect,f,Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = ∑ _i : Fin K,p.expect (fun x=>if P x then 1 else 0) := Finset.sum_congr rfl (fun i _=>independentSampleLaw_expect_coord (fun _ : Fin K=>p) i (fun x=>if P x then 1 else 0))
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hP hKR.le
    simpa only [p,uniformFiniteLaw_indicator_mean,mul_one_div] using hh
  have ht := (finite_product_bounded_differences_tail X K (fun _=>p) f (fun _=>1) (3*(K:ℝ)/10)
    (fun _=>by norm_num) (by simpa only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hKR) (by positivity) hd).2
  have hs : (Finset.univ.filter (fun ω : Fin K→X=>K≤2*(Finset.univ.filter (fun i=>P (ω i))).card)) ⊆
      Finset.univ.filter (fun ω=>3*(K:ℝ)/10≤|f ω-(independentSampleLaw (fun _ : Fin K=>p)).expect f|) := by
    intro ω hω
    have hh : (K:ℝ)≤2*((Finset.univ.filter (fun i=>P (ω i))).card:ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hω).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have he : f ω=((Finset.univ.filter (fun i=>P (ω i))).card:ℝ) := sum_round_indicators K P ω
    have ha := le_abs_self (f ω-(independentSampleLaw (fun _ : Fin K=>p)).expect f)
    linarith [he]
  have hb :=
      (Finset.sum_le_sum_of_subset_of_nonneg hs (fun ω _ _=>(independentSampleLaw (fun _ : Fin K=>p)).nonneg ω)).trans ht
  have hevent :=
      uniformFiniteLaw_event_card (X:=X) K
      (fun ω : Fin K→X=>K≤2*(Finset.univ.filter (fun i=>P (ω i))).card)
  calc
    _ = ∑ ω∈Finset.univ.filter (fun ω : Fin K→X=>K≤2*(Finset.univ.filter (fun i=>P (ω i))).card),
        (independentSampleLaw (fun _ : Fin K=>p)).prob ω := hevent.symm
    _ ≤ _ := hb
    _ = _ := by
      simp only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      congr 2
      field_simp
      ring
end Qatlib.Concepts.WalkSearch.Primitives

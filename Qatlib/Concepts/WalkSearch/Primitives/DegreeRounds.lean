/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.FiniteMajority
import Qatlib.Concepts.WalkSearch.Primitives.TriangleSearchCorrectedDefinitions

/-!
# Sampling bounds for degree-test rounds

Counts the tapes on which a single neighbor-sampling round misses a vertex's neighborhood and
bounds the corresponding hit and miss fractions. The module also identifies the hit-round
counter and controls the exponential tail for the prescribed logarithmic round count, supporting
degree tests in the graph-search setting of [Ambainis2005].

## Main statements

* `miss_round_fraction`: For `n > 0`, the fraction of length-`c` tapes missing the neighborhood
  of `v` is `(1 - degOf G.edges v / n) ^ c`.
* `logarithmic_round_tail`: For `n > 0`, the exponential majority-tail expression with `64 *
  (Nat.log 2 n + 2)` rounds is at most `1 / n ^ 3`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n c : ℕ}

/-- The event that at least one of the `c` sampled vertices is adjacent to `v`. -/
def roundHit (G : UGraph n) (v : Fin n) (s : Fin c→Fin n) : Prop := ∃ j,(v,s j)∈G.edges

/-- The number of length-`c` sampling tapes that miss the neighborhood of `v` is `(n - degOf
G.edges v) ^ c`. -/
theorem miss_round_card (G : UGraph n) (v : Fin n) :
    (Finset.univ.filter (fun s : Fin c→Fin n=>¬roundHit G v s)).card=(n-degOf G.edges v)^c := by
  have he : Finset.univ.filter (fun s : Fin c→Fin n=>¬roundHit G v s) =
      Finset.univ.filter (fun s=>∀ j,s j∉nbrOf G.edges v) := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,roundHit,not_exists,mem_graph_nbr_iff]
  rw [he,avoiding_tape_card]
  rfl

/-- For `n > 0`, the fraction of length-`c` tapes missing the neighborhood of `v` is `(1 - degOf
G.edges v / n) ^ c`. -/
theorem miss_round_fraction (G : UGraph n) (v : Fin n) (hn : 0<n) :
    ((Finset.univ.filter (fun s : Fin c→Fin n=>¬roundHit G v s)).card:ℝ)/
      (Fintype.card (Fin c→Fin n):ℝ) = (1-(degOf G.edges v:ℝ)/(n:ℝ))^c := by
  have hd : degOf G.edges v≤n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [miss_round_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Nat.cast_pow,Nat.cast_pow,← div_pow,Nat.cast_sub hd]
  congr 1
  field_simp

/-- If `degOf G.edges v * c / n ≥ 10` and `n > 0`, the fraction of single-round tapes missing
the neighborhood is at most `1 / 5`. -/
theorem high_degree_miss_fraction (G : UGraph n) (v : Fin n) (hn : 0<n)
    (hlarge : 10≤(degOf G.edges v:ℝ)*(c:ℝ)/(n:ℝ)) :
    ((Finset.univ.filter (fun s : Fin c→Fin n=>¬roundHit G v s)).card:ℝ)/
      (Fintype.card (Fin c→Fin n):ℝ)≤1/5 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hd : (degOf G.edges v:ℝ)≤n := by
    exact_mod_cast ((Finset.card_le_univ (nbrOf G.edges v)).trans_eq (Fintype.card_fin n))
  rw [miss_round_fraction G v hn]
  have hbase : 1-(degOf G.edges v:ℝ)/(n:ℝ)≤Real.exp (-(degOf G.edges v:ℝ)/(n:ℝ)) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using
        Real.add_one_le_exp (-(degOf G.edges v:ℝ)/(n:ℝ))
  have h0 : 0≤1-(degOf G.edges v:ℝ)/(n:ℝ) := by rw [sub_nonneg,div_le_one hnR];exact hd
  calc
    _ ≤ Real.exp (-(degOf G.edges v:ℝ)/(n:ℝ))^c := pow_le_pow_left₀ h0 hbase c
    _ = Real.exp (-((degOf G.edges v:ℝ)*(c:ℝ)/(n:ℝ))) := by rw [← Real.exp_nat_mul];congr 1;ring
    _ ≤ Real.exp (-10) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1/5 := by
      rw [Real.exp_neg,← one_div,div_le_div_iff₀ (Real.exp_pos 10) (by norm_num : (0:ℝ)<5)]
      have hh:=Real.add_one_le_exp 10
      norm_num at hh ⊢
      linarith

/-- If `c * degOf G.edges v / n ≤ 1 / 5` and `n > 0`, the fraction of single-round tapes hitting
the neighborhood is at most `1 / 5`. -/
theorem low_degree_hit_fraction (G : UGraph n) (v : Fin n) (hn : 0<n)
    (hsmall : (c:ℝ)*(degOf G.edges v:ℝ)/(n:ℝ)≤1/5) :
    ((Finset.univ.filter (fun s : Fin c→Fin n=>roundHit G v s)).card:ℝ)/
      (Fintype.card (Fin c→Fin n):ℝ)≤1/5 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hd : (degOf G.edges v:ℝ)≤n := by
    exact_mod_cast ((Finset.card_le_univ (nbrOf G.edges v)).trans_eq (Fintype.card_fin n))
  have hcard :=
      Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun s : Fin c→Fin n=>roundHit G v s)
  have hR : ((Finset.univ.filter (fun s : Fin c→Fin n=>roundHit G v s)).card:ℝ)+
      ((Finset.univ.filter (fun s : Fin c→Fin n=>¬roundHit G v s)).card:ℝ)=Fintype.card (Fin c→Fin n) := by exact_mod_cast hcard
  have hf := miss_round_fraction (c:=c) G v hn
  have hN : (0:ℝ)<Fintype.card (Fin c→Fin n) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Nat.cast_pow]
    positivity
  have hsum : ((Finset.univ.filter (fun s : Fin c→Fin n=>roundHit G v s)).card:ℝ)/(Fintype.card (Fin c→Fin n):ℝ)+
      (1-(degOf G.edges v:ℝ)/(n:ℝ))^c=1 := by rw [← hf,← add_div,hR];exact div_self hN.ne'
  have hber := one_add_mul_le_pow (a:=-(degOf G.edges v:ℝ)/(n:ℝ)) (by
    have hh : (degOf G.edges v:ℝ)/(n:ℝ)≤1 := (div_le_one hnR).mpr hd
    rw [neg_div]
    linarith : (-2:ℝ)≤-(degOf G.edges v:ℝ)/(n:ℝ)) c
  have he : 1+(c:ℝ)*(-(degOf G.edges v:ℝ)/(n:ℝ))=1-(c:ℝ)*(degOf G.edges v:ℝ)/(n:ℝ) := by ring
  rw [he,show 1+(-(degOf G.edges v:ℝ)/(n:ℝ))=1-(degOf G.edges v:ℝ)/(n:ℝ) by ring] at hber
  linarith

/-- The counter `hitRounds` equals the number of round indices whose sampling tapes satisfy
`roundHit`. -/
theorem hitRounds_eq_card_roundHit (G : UGraph n) (v : Fin n) (K c : ℕ) (tape : Fin K→Fin c→Fin n) :
    hitRounds G v K c tape=(Finset.univ.filter (fun i=>roundHit G v (tape i))).card := by
  unfold hitRounds
  apply congrArg Finset.card
  ext i
  simp [roundHit]

/-- For `n > 0`, the exponential majority-tail expression with `64 * (Nat.log 2 n + 2)` rounds
is at most `1 / n ^ 3`. -/
theorem logarithmic_round_tail (n : ℕ) (hn : 0<n) :
    2*Real.exp (-9*(64*(Nat.log 2 n+2):ℕ)/50)≤1/(n:ℝ)^3 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hlog:=natLog_padding_ge_log n hn
  have hlog0 : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  have hlog2 : Real.log 2≤1 := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2);linarith
  have ha : Real.log 2-9*(64*(Nat.log 2 n+2):ℕ)/50≤-3*Real.log (n:ℝ) := by
    norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at hlog ⊢
    linarith
  calc
    _ = Real.exp (Real.log 2-9*(64*(Nat.log 2 n+2):ℕ)/50) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)];congr 1;congr 1;ring
    _ ≤ Real.exp (-3*Real.log (n:ℝ)) := Real.exp_le_exp.mpr ha
    _ = 1/(n:ℝ)^3 := by
      rw [show -3*Real.log (n:ℝ)=-(3*Real.log (n:ℝ)) by ring,Real.exp_neg]
      have he : Real.exp (3*Real.log (n:ℝ))=(n:ℝ)^3 := by
        simpa only [Real.exp_log hnR] using! Real.exp_nat_mul (Real.log (n:ℝ)) 3
      rw [he,one_div]
end Qatlib.Concepts.WalkSearch.Primitives

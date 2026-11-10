/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphFraction.CoverLP.WeightedCover
import QuantumInfo.ForMathlib.Minimax

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.GraphFraction.CoverLP
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def payoff (G : SimpleGraph V) (w : V → ℝ) (q : Context G → ℝ) : ℝ :=
  ∑ I, q I * ∑ i∈I.val,w i

def contextPair (G : SimpleGraph V) (w : V → ℝ) : (Context G → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := payoff G w
    map_add' := by
      intro q r
      simp [payoff,add_mul,Finset.sum_add_distrib]
    map_smul' := by
      intro r q
      simp [payoff,Finset.mul_sum,mul_assoc]
  }

def gamePair (G : SimpleGraph V) : (V → ℝ) →L[ℝ] (Context G → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := contextPair G
    map_add' := by
      intro w v
      ext q
      change payoff G (w+v) q = payoff G w q + payoff G v q
      simp [payoff,Finset.sum_add_distrib,mul_add]
    map_smul' := by
      intro r w
      ext q
      change payoff G (r•w) q = r * payoff G w q
      simp [payoff,Finset.mul_sum,mul_left_comm]
  }

def independentSupport (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  sSup (Set.range (fun I : Context G => ∑ i∈I.val,w i))

theorem independentSupport_bddAbove (G : SimpleGraph V) (w : V → ℝ) :
    BddAbove (Set.range (fun I : Context G => ∑ i∈I.val,w i)) := Set.Finite.bddAbove (Set.finite_range _)

theorem context_le_support (G : SimpleGraph V) (w : V → ℝ) (I : Context G) :
    (∑ i∈I.val,w i)  ≤  independentSupport G w :=
  le_csSup (independentSupport_bddAbove G w) (Set.mem_range_self I)

theorem payoff_le_support (G : SimpleGraph V) (w : V → ℝ) (q : Context G → ℝ)
    (hq : q∈stdSimplex ℝ (Context G)) : payoff G w q  ≤  independentSupport G w := by
  calc _  ≤  ∑ I,q I*independentSupport G w := by
         apply Finset.sum_le_sum
         intro I _
         exact mul_le_mul_of_nonneg_left (context_le_support G w I) (hq.1 I)
       _ = independentSupport G w := by rw [← Finset.sum_mul,hq.2,one_mul]

theorem payoff_dirac (G : SimpleGraph V) (w : V → ℝ) (I : Context G) :
    payoff G w (Pi.single I 1) = ∑ i∈I.val,w i := by
  simp [payoff,Pi.single_apply]

theorem support_eq_context_sup (G : SimpleGraph V) (w : V → ℝ) :
    independentSupport G w = ⨆ q : stdSimplex ℝ (Context G),payoff G w q := by
  have hb : BddAbove (Set.range (fun q : stdSimplex ℝ (Context G) => payoff G w q)) :=
    ⟨independentSupport G w,by rintro _ ⟨q,rfl⟩;exact payoff_le_support G w q q.2⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨I,rfl⟩
    have h := le_ciSup hb (⟨Pi.single I 1,single_mem_stdSimplex ℝ I⟩ : stdSimplex ℝ (Context G))
    change payoff G w (Pi.single I 1)  ≤  _ at h
    rw [payoff_dirac] at h
    exact h
  · apply ciSup_le
    intro q
    exact payoff_le_support G w q q.2

theorem context_game_minimax (G : SimpleGraph V) [Nonempty V] :
    (⨅ w : stdSimplex ℝ V,⨆ q : stdSimplex ℝ (Context G),payoff G w q) =
      ⨆ q : stdSimplex ℝ (Context G),⨅ w : stdSimplex ℝ V,payoff G w q := by
  exact minimax (gamePair G) (stdSimplex ℝ (Context G)) (stdSimplex ℝ V)
    (isCompact_stdSimplex ℝ _) (isCompact_stdSimplex ℝ _)
    (convex_stdSimplex ℝ _) (convex_stdSimplex ℝ _)
    (by exact ⟨Pi.single (Classical.choice (contextNonempty G)) 1,single_mem_stdSimplex ℝ _⟩)
    (by exact ⟨Pi.single (Classical.choice ‹Nonempty V›) 1,single_mem_stdSimplex ℝ _⟩)

theorem payoff_eq_coverage (G : SimpleGraph V) (w : V → ℝ) (q : Context G → ℝ) :
    payoff G w q = ∑ i,w i*coverage G q i := by
  have hi (I : Context G) : (∑ i∈I.val,w i)=∑ i,w i*incidence G I i := by
    simp [incidence]
  simp only [payoff,hi,coverage,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem payoff_vertex_dirac (G : SimpleGraph V) (q : Context G → ℝ) (i : V) :
    payoff G (Pi.single i 1) q = coverage G q i := by
  rw [payoff_eq_coverage]
  simp [Pi.single_apply]

theorem payoff_nonneg (G : SimpleGraph V) (w : V → ℝ) (q : Context G → ℝ)
    (hw : w∈stdSimplex ℝ V) (hq : q∈stdSimplex ℝ (Context G)) : 0 ≤ payoff G w q := by
  unfold payoff
  apply Finset.sum_nonneg
  intro I _
  exact mul_nonneg (hq.1 I) (Finset.sum_nonneg (fun i _ => hw.1 i))

theorem payoff_le_mass_support (G : SimpleGraph V) (w : V → ℝ) (x : Context G → ℝ)
    (hx : ∀ I,0 ≤ x I) : payoff G w x  ≤  independentSupport G w*(∑ I,x I) := by
  calc _  ≤  ∑ I,x I*independentSupport G w := by
         apply Finset.sum_le_sum
         intro I _
         exact mul_le_mul_of_nonneg_left (context_le_support G w I) (hx I)
       _ = independentSupport G w*(∑ I,x I) := by rw [← Finset.sum_mul,mul_comm]

theorem one_le_support_mass (G : SimpleGraph V) (w : V → ℝ)
    (hw : w∈stdSimplex ℝ V) (x : Context G → ℝ) (hx : Feasible G (fun _ => 1) x) :
    1 ≤ independentSupport G w*(∑ I,x I) := by
  have hl : 1 ≤ payoff G w x := by
    rw [payoff_eq_coverage]
    calc 1 = ∑ i,w i*1 := by simpa using hw.2.symm
         _  ≤  ∑ i,w i*coverage G x i := by
           apply Finset.sum_le_sum
           intro i _
           exact mul_le_mul_of_nonneg_left (hx.2 i) (hw.1 i)
  exact hl.trans (payoff_le_mass_support G w x hx.1)

theorem coverValue_le_mass (G : SimpleGraph V) (a : V → ℝ) (x : Context G → ℝ)
    (hx : Feasible G a x) : coverValue G a ≤ ∑ I,x I := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    exact Finset.sum_nonneg (fun I _ => hy.1 I)
  · exact ⟨x,hx,rfl⟩

theorem coverage_div (G : SimpleGraph V) (q : Context G → ℝ) (r : ℝ) (i : V) :
    coverage G (fun I => q I/r) i=coverage G q i/r := by
  unfold coverage
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem unweighted_cover_pos (G : SimpleGraph V) [Nonempty V] : 0<coverValue G (fun _ => 1) :=
  (attained_strategy G (fun _ => 1) (by intro i;norm_num)
    (Classical.choice ‹Nonempty V›) (by norm_num)).1

theorem context_min_le_inverse_cover (G : SimpleGraph V) [Nonempty V]
    (q : stdSimplex ℝ (Context G)) :
    (⨅ w : stdSimplex ℝ V,payoff G w q)  ≤  1/coverValue G (fun _ => 1) := by
  have hc := unweighted_cover_pos G
  let t : ℝ := ⨅ w : stdSimplex ℝ V,payoff G w q
  have hb : BddBelow (Set.range (fun w : stdSimplex ℝ V => payoff G w q)) :=
    ⟨0,by rintro _ ⟨w,rfl⟩;exact payoff_nonneg G w q w.2 q.2⟩
  change t ≤ _
  by_cases ht : t ≤ 0
  · exact ht.trans (one_div_pos.mpr hc).le
  · have htp : 0<t := lt_of_not_ge ht
    have hi (i : V) : t ≤ coverage G q i := by
      have h := ciInf_le hb (⟨Pi.single i 1,single_mem_stdSimplex ℝ i⟩ : stdSimplex ℝ V)
      change t ≤ payoff G (Pi.single i 1) q at h
      rw [payoff_vertex_dirac] at h
      exact h
    have hf : Feasible G (fun _ => 1) (fun I => q I/t) := by
      refine ⟨fun I => div_nonneg (q.2.1 I) htp.le,?_⟩
      intro i
      rw [coverage_div]
      exact (le_div_iff₀ htp).mpr (by simpa using hi i)
    have hmass : (∑ I,q I/t)=1/t := by
      rw [← Finset.sum_div]
      exact congrArg (fun r : ℝ => r/t) q.2.2
    have hc' := coverValue_le_mass G (fun _ => 1) (fun I => q I/t) hf
    rw [hmass] at hc'
    apply (le_div_iff₀ hc).mpr
    have hh := (le_div_iff₀ htp).mp hc'
    nlinarith

theorem support_min_eq_inverse_cover (G : SimpleGraph V) [Nonempty V] :
    (⨅ w : stdSimplex ℝ V,independentSupport G w)=1/coverValue G (fun _ => 1) := by
  have hc := unweighted_cover_pos G
  apply le_antisymm
  · simp_rw [support_eq_context_sup]
    rw [context_game_minimax]
    apply ciSup_le
    intro q
    exact context_min_le_inverse_cover G q
  · obtain ⟨x,hx,hval⟩ := coverValue_attained G (fun _ => 1) (by intro i;norm_num)
    apply le_ciInf
    intro w
    apply (div_le_iff₀ hc).mpr
    rw [hval]
    exact one_le_support_mass G w w.2 x hx

end Qatlib.Foundations.GraphFraction.CoverLP

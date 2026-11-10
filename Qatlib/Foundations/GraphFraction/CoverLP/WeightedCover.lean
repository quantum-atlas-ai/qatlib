/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.GraphFraction.CoverLP
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def Context (G : SimpleGraph V) := {I : Finset V // G.IsIndepSet (I : Set V)}

instance contextFintype (G : SimpleGraph V) : Fintype (Context G) := by
  classical
  unfold Context
  infer_instance

instance contextNonempty (G : SimpleGraph V) : Nonempty (Context G) := ⟨⟨∅,by simp⟩⟩

def singletonContext (G : SimpleGraph V) (i : V) : Context G := ⟨{i},by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Finset.mem_coe,Finset.mem_singleton] at hx hy
  exact False.elim (hxy (hx.trans hy.symm))⟩

def incidence (G : SimpleGraph V) (I : Context G) (i : V) : ℝ := if i∈I.val then 1 else 0

def coverage (G : SimpleGraph V) (x : Context G → ℝ) (i : V) : ℝ :=
  ∑ I, x I * incidence G I i

def Feasible (G : SimpleGraph V) (a : V → ℝ) (x : Context G → ℝ) : Prop :=
  (∀ I,0 ≤ x I) ∧ ∀ i,a i ≤ coverage G x i

def coverValue (G : SimpleGraph V) (a : V → ℝ) : ℝ :=
  sInf ((fun x : Context G → ℝ => ∑ I,x I) '' {x | Feasible G a x})

omit [Fintype V] in

theorem incidence_bounds (G : SimpleGraph V) (I : Context G) (i : V) :
    0 ≤ incidence G I i ∧ incidence G I i ≤ 1 := by
  unfold incidence
  split_ifs <;> norm_num

theorem constant_cover_feasible (G : SimpleGraph V) (a : V → ℝ) (ha : ∀ i,0 ≤ a i) :
    Feasible G a (fun _ => ∑ i,a i) := by
  have hC : 0 ≤ ∑ i,a i := Finset.sum_nonneg (fun i _ => ha i)
  refine ⟨fun _ => hC,?_⟩
  intro i
  have hi : a i ≤ ∑ j,a j := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hs : (∑ j,a j)*incidence G (singletonContext G i) i ≤
      coverage G (fun _ => ∑ j,a j) i := by
    unfold coverage
    exact Finset.single_le_sum (fun I _ => mul_nonneg hC (incidence_bounds G I i).1)
      (Finset.mem_univ (singletonContext G i))
  have hs' : (∑ j,a j) ≤ coverage G (fun _ => ∑ j,a j) i := by
    simpa only [incidence,singletonContext,Finset.mem_singleton,ite_true,mul_one] using hs
  exact hi.trans hs'

theorem coverage_continuous (G : SimpleGraph V) (i : V) : Continuous (fun x => coverage G x i) := by
  unfold coverage
  fun_prop

theorem feasible_closed (G : SimpleGraph V) (a : V → ℝ) : IsClosed {x | Feasible G a x} := by
  simp only [Feasible,Set.setOf_and,Set.setOf_forall]
  exact (isClosed_iInter (fun I => isClosed_le continuous_const (continuous_apply I))).inter
    (isClosed_iInter (fun i => isClosed_le continuous_const (coverage_continuous G i)))

theorem coordinate_le_total (G : SimpleGraph V) {x : Context G → ℝ}
    (hx : ∀ I,0 ≤ x I) (I : Context G) : x I ≤ ∑ J,x J :=
  Finset.single_le_sum (fun J _ => hx J) (Finset.mem_univ I)

theorem exists_min_cover (G : SimpleGraph V) (a : V → ℝ) (ha : ∀ i,0 ≤ a i) :
    ∃ x : Context G → ℝ,Feasible G a x ∧
      ∀ y : Context G → ℝ,Feasible G a y → (∑ I,x I) ≤ ∑ I,y I := by
  let x0 : Context G → ℝ := fun _ => ∑ i,a i
  let M : ℝ := ∑ I,x0 I
  let K : Set (Context G → ℝ) := {x | Feasible G a x ∧ (∑ I,x I) ≤ M}
  have hx0 : Feasible G a x0 := constant_cover_feasible G a ha
  have htotal : Continuous (fun x : Context G → ℝ => ∑ I,x I) := by fun_prop
  have hKclosed : IsClosed K :=
    (feasible_closed G a).inter (isClosed_le htotal continuous_const)
  have hKsub : K ⊆ Set.Icc (fun _ => (0:ℝ)) (fun _ => M) := by
    intro x hx
    exact ⟨hx.1.1,fun I => (coordinate_le_total G hx.1.1 I).trans hx.2⟩
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed hKsub
  obtain ⟨x,hx,hmin⟩ := hKcompact.exists_isMinOn ⟨x0,hx0,le_rfl⟩ htotal.continuousOn
  refine ⟨x,hx.1,?_⟩
  intro y hy
  by_cases hM : (∑ I,y I) ≤ M
  · exact hmin ⟨hy,hM⟩
  · exact hx.2.trans (le_of_lt (lt_of_not_ge hM))

theorem coverValue_attained (G : SimpleGraph V) (a : V → ℝ) (ha : ∀ i,0 ≤ a i) :
    ∃ x : Context G → ℝ,Feasible G a x ∧ coverValue G a=∑ I,x I := by
  obtain ⟨x,hx,hmin⟩ := exists_min_cover G a ha
  refine ⟨x,hx,?_⟩
  unfold coverValue
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0,?_⟩
      rintro y ⟨z,hz,rfl⟩
      exact Finset.sum_nonneg (fun I _ => hz.1 I)
    · exact ⟨x,hx,rfl⟩
  · apply le_csInf
    · exact ⟨_,x,hx,rfl⟩
    · rintro y ⟨z,hz,rfl⟩
      exact hmin z hz

theorem coverage_le_total (G : SimpleGraph V) {x : Context G → ℝ}
    (hx : ∀ I,0 ≤ x I) (i : V) : coverage G x i ≤ ∑ I,x I := by
  unfold coverage
  apply Finset.sum_le_sum
  intro I _
  simpa using mul_le_mul_of_nonneg_left (incidence_bounds G I i).2 (hx I)

theorem total_pos (G : SimpleGraph V) {a : V → ℝ} {x : Context G → ℝ}
    (hx : Feasible G a x) (i : V) (ha : 0<a i) : 0<∑ I,x I :=
  lt_of_lt_of_le ha ((hx.2 i).trans (coverage_le_total G hx.1 i))

theorem normalized_cover_simplex (G : SimpleGraph V) {a : V → ℝ} {x : Context G → ℝ}
    (hx : Feasible G a x) (ht : 0<∑ I,x I) :
    (fun I => x I/(∑ J,x J))∈stdSimplex ℝ (Context G) := by
  constructor
  · intro I
    exact div_nonneg (hx.1 I) ht.le
  · rw [← Finset.sum_div,div_self ht.ne']

theorem normalized_coverage (G : SimpleGraph V) (x : Context G → ℝ) (i : V) :
    coverage G (fun I => x I/(∑ J,x J)) i = coverage G x i/(∑ J,x J) := by
  unfold coverage
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem attained_strategy (G : SimpleGraph V) (a : V → ℝ) (ha : ∀ i,0 ≤ a i)
    (i0 : V) (hi0 : 0<a i0) :
    0<coverValue G a ∧ ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧
      ∀ i,a i/coverValue G a ≤ coverage G q i := by
  obtain ⟨x,hx,hval⟩ := coverValue_attained G a ha
  have ht := total_pos G hx i0 hi0
  refine ⟨by rwa [hval],fun I => x I/(∑ J,x J),normalized_cover_simplex G hx ht,?_⟩
  intro i
  rw [normalized_coverage,hval]
  exact div_le_div_of_nonneg_right (hx.2 i) ht.le

end Qatlib.Foundations.GraphFraction.CoverLP

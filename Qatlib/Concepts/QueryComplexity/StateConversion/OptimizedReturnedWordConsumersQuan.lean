/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GramRealization.NoncoherentStateConversion
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedReturnedWordConsumersStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.DualNormSDPAndClosureQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan

/-!
# Optimized state-conversion words

This module constructs legal `SourceWord` programs from coherent and noncoherent approximate
Gram-matrix budgets. Compactness gives budget witnesses, while basis-frame compilation transfers
enlarged data spaces to native work registers and preserves the required output overlaps.

The mathematical background is described in [LeeEtAl2011].

## Main statements

* `sourceCoherent_raw_budget_word`: coherent conversion from a raw approximate budget.
* `sourceNoncoherent_raw_budget_word`: conversion with a normalized garbage state.
* `optimizedReturnedWordConsumers`: the uniform optimized consumer interface.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics

namespace Qatlib.Concepts.QueryComplexity.StateConversion
open Matrix Filter Topology
open scoped Classical BigOperators ENNReal ComplexOrder

section SourceOptimizedAttainment
open scoped Matrix.Norms.Elementwise

open scoped Matrix.Norms.L2Operator in

 /-- Filtered rectangular norm bounds pass to limits of matrices and convergent nonnegative real
 budgets. -/
 theorem sourceRectValue_limit_sublevel {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (Z : Fin n → Matrix R S ℂ) (A : ℕ → Matrix R S ℂ) (B : Matrix R S ℂ)
    (a : ℕ → ℝ) (b : ℝ) (ha : ∀ k, 0≤a k)
    (hA : Tendsto A atTop (𝓝 B)) (hab : Tendsto a atTop (𝓝 b))
    (hb : ∀ k, sourceRectValue (A k) Z≤ENNReal.ofReal (a k)) :
    sourceRectValue B Z≤ENNReal.ofReal b := by
  letI : NormedAddCommGroup (Matrix R S ℂ) := Matrix.instL2OpNormedAddCommGroup
  apply sourceRectValue_le_of_dual_norm_bound
  intro M hM
  have hm (k : ℕ) : ‖A k ⊙ M‖≤a k := (ENNReal.ofReal_le_ofReal_iff (ha k)).mp
    ((sourceRectValue_dual_norm_le (A k) Z M hM).trans (hb k))
  have hh : Continuous (fun C : Matrix R S ℂ => C ⊙ M) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    change Continuous (fun C : Matrix R S ℂ => C r s*M r s)
    fun_prop
  have hc : Continuous (fun C : Matrix R S ℂ => ‖C ⊙ M‖) :=
    (@continuous_norm (Matrix R S ℂ) Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup).comp hh
  exact ENNReal.ofReal_le_ofReal (le_of_tendsto_of_tendsto (hc.tendsto B |>.comp hA) hab
    (Eventually.of_forall hm))

/-- The finite-dimensional set of positive semidefinite complex matrices with unit diagonal is
compact. -/
theorem sourceNormalizedPSD_compact (X : Type) [Fintype X] [DecidableEq X] :
    IsCompact {T : Matrix X X ℂ | T.PosSemidef ∧ ∀ x, T x x=1} := by
  have hc : IsClosed {T : Matrix X X ℂ | T.PosSemidef ∧ ∀ x, T x x=1} := by
    apply IsClosed.inter sourcePSD_closed
    change IsClosed {T : Matrix X X ℂ | ∀ x, T x x=1}
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_eq <;> fun_prop
  apply (isCompact_closedBall (0 : Matrix X X ℂ) 1).of_isClosed_subset hc
  intro T hT
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro y
  apply gamma2_psd_entry_norm_le T hT.1 1 zero_le_one
  intro z
  simp [hT.2 z]

/-- Finiteness of the alphabet-filtered value of `R - T` forces `T` to have unit diagonal when
`R` does. -/
theorem sourceAlphabet_finite_diagonal {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (R T : Matrix X X ℂ)
    (hR : ∀ x, R x x=1) (hfinite : sourceRectValue (R-T) (sourceAlphabetDelta input)<⊤) :
    ∀ x, T x x=1 := by
  have hs := (sourceRectValue_finite_iff (R-T) (sourceAlphabetDelta input)).mp hfinite
  intro x
  have he : R x x-T x x=0 := by
    by_contra hh
    obtain ⟨j,hj⟩ := hs x x hh
    simp [sourceAlphabetDelta] at hj
  rw [hR x] at he
  exact (sub_eq_zero.mp he).symm

/-- A nonnegative upper bound on `sourceQDelta` is realized by a positive semidefinite
intermediate matrix satisfying both the approximation and filtered-budget bounds. -/
theorem sourceQDelta_raw_attainment {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (δ W : ℝ) (R S : Matrix X X ℂ)
    (hδ : 0≤δ) (hW : 0≤W) (_hR : R.PosSemidef) (hRdiag : ∀ x, R x x=1)
    (hQ : sourceQDelta input δ R S≤ENNReal.ofReal W) :
    ∃ T : Matrix X X ℂ, T.PosSemidef ∧ sourceUnfiltered (T-S)≤ENNReal.ofReal δ ∧
      sourceRectValue (R-T) (sourceAlphabetDelta input)≤ENNReal.ofReal W := by
  let ε : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hε (k : ℕ) : 0<ε k := by dsimp [ε]; positivity
  have happ (k : ℕ) : ∃ T : {T : Matrix X X ℂ // T.PosSemidef ∧ sourceUnfiltered (T-S)≤ENNReal.ofReal δ},
      sourceRectValue (R-T.val) (sourceAlphabetDelta input)<ENNReal.ofReal (W+ε k) := by
    have hh : sourceQDelta input δ R S<ENNReal.ofReal (W+ε k) := hQ.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hW).mpr (lt_add_of_pos_right W (hε k)))
    exact iInf_lt_iff.mp hh
  choose T hT using happ
  have htNorm (k : ℕ) : (T k).val ∈ {T : Matrix X X ℂ | T.PosSemidef ∧ ∀ x, T x x=1} := by
    refine ⟨(T k).property.1,?_⟩
    exact sourceAlphabet_finite_diagonal input R (T k).val hRdiag
      ((hT k).trans ENNReal.ofReal_lt_top)
  obtain ⟨τ,hτ,φ,hφ,hτt⟩ := (sourceNormalizedPSD_compact X).tendsto_subseq htNorm
  have hδlim : sourceUnfiltered (τ-S)≤ENNReal.ofReal δ := by
    have hc : Continuous (fun T : Matrix X X ℂ => T-S) := by fun_prop
    exact sourceRectValue_limit_sublevel (fun _ : Fin 1 => fun _ _ => (1 : ℂ))
      (fun k => (T (φ k)).val-S) (τ-S) (fun _ => δ) δ (fun _ => hδ)
      (hc.tendsto τ |>.comp hτt) tendsto_const_nhds (fun k => (T (φ k)).property.2)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hob : sourceRectValue (R-τ) (sourceAlphabetDelta input)≤ENNReal.ofReal W := by
    have hc : Continuous (fun T : Matrix X X ℂ => R-T) := by fun_prop
    have ht : Tendsto (fun k => W+ε (φ k)) atTop (𝓝 W) := by
      convert! tendsto_const_nhds.add (hεt.comp hφ.tendsto_atTop) using 1
      simp
    exact sourceRectValue_limit_sublevel (sourceAlphabetDelta input)
      (fun k => R-(T (φ k)).val) (R-τ) (fun k => W+ε (φ k)) W
      (fun k => add_nonneg hW (hε _).le) (hc.tendsto τ |>.comp hτt) ht (fun k => (hT (φ k)).le)
  exact ⟨τ,hτ.1,hδlim,hob⟩

/-- A nonnegative upper bound on `sourceQNoncoherentDelta` is realized by positive semidefinite
matrices `T` and `K`, with unit diagonal for `K` and the stated approximation and budget
bounds. -/
theorem sourceQNoncoherentDelta_raw_attainment {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (δ W : ℝ) (R S : Matrix X X ℂ)
    (hδ : 0≤δ) (hW : 0≤W) (_hR : R.PosSemidef) (hRdiag : ∀ x, R x x=1)
    (hQ : sourceQNoncoherentDelta input δ R S≤ENNReal.ofReal W) :
    ∃ T K : Matrix X X ℂ, T.PosSemidef ∧ K.PosSemidef ∧ (∀ x, K x x=1) ∧
      sourceUnfiltered (T-S ⊙ K)≤ENNReal.ofReal δ ∧
      sourceRectValue (R-T) (sourceAlphabetDelta input)≤ENNReal.ofReal W := by
  let ε : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hε (k : ℕ) : 0<ε k := by dsimp [ε]; positivity
  have happ (k : ℕ) : ∃ T K : Matrix X X ℂ, T.PosSemidef ∧ K.PosSemidef ∧ (∀ x, K x x=1) ∧
      sourceUnfiltered (T-S ⊙ K)≤ENNReal.ofReal δ ∧
      sourceRectValue (R-T) (sourceAlphabetDelta input)<ENNReal.ofReal (W+ε k) := by
    have hh : sourceQNoncoherentDelta input δ R S<ENNReal.ofReal (W+ε k) := hQ.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hW).mpr (lt_add_of_pos_right W (hε k)))
    obtain ⟨T,hT⟩ := iInf_lt_iff.mp hh
    obtain ⟨K,hK⟩ := iInf_lt_iff.mp hT
    by_cases hd : sourceUnfiltered (T.val-S ⊙ K.val)≤ENNReal.ofReal δ
    · rw [if_pos hd] at hK
      exact ⟨T.val,K.val,T.property,K.property.1,K.property.2,hd,hK⟩
    · rw [if_neg hd] at hK
      exact (not_top_lt hK).elim
  choose T K hTPSD hKPSD hKdiag hFeas hObj using happ
  have htNorm (k : ℕ) : T k ∈ {T : Matrix X X ℂ | T.PosSemidef ∧ ∀ x, T x x=1} :=
    ⟨hTPSD k,sourceAlphabet_finite_diagonal input R (T k) hRdiag ((hObj k).trans ENNReal.ofReal_lt_top)⟩
  have hkNorm (k : ℕ) : K k ∈ {K : Matrix X X ℂ | K.PosSemidef ∧ ∀ x, K x x=1} := ⟨hKPSD k,hKdiag k⟩
  have hboth (k : ℕ) : (T k,K k) ∈
      ({T : Matrix X X ℂ | T.PosSemidef ∧ ∀ x, T x x=1}).prod
      ({K : Matrix X X ℂ | K.PosSemidef ∧ ∀ x, K x x=1}) := ⟨htNorm k,hkNorm k⟩
  obtain ⟨⟨τ,κ⟩,⟨hτ,hκ⟩,φ,hφ,hlim⟩ :=
      ((sourceNormalizedPSD_compact X).prod (sourceNormalizedPSD_compact X)).tendsto_subseq hboth
  have hδlim : sourceUnfiltered (τ-S ⊙ κ)≤ENNReal.ofReal δ := by
    have hc : Continuous (fun p : Matrix X X ℂ × Matrix X X ℂ => p.1-S ⊙ p.2) := by
      apply continuous_pi
      intro x
      apply continuous_pi
      intro y
      change Continuous (fun p : Matrix X X ℂ × Matrix X X ℂ => p.1 x y-S x y*p.2 x y)
      fun_prop
    exact sourceRectValue_limit_sublevel (fun _ : Fin 1 => fun _ _ => (1 : ℂ))
      (fun k => T (φ k)-S ⊙ K (φ k)) (τ-S ⊙ κ) (fun _ => δ) δ (fun _ => hδ)
      (hc.tendsto (τ,κ) |>.comp hlim) tendsto_const_nhds (fun k => hFeas (φ k))
  have hεt : Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hob : sourceRectValue (R-τ) (sourceAlphabetDelta input)≤ENNReal.ofReal W := by
    have hc : Continuous (fun p : Matrix X X ℂ × Matrix X X ℂ => R-p.1) := by fun_prop
    have ht : Tendsto (fun k => W+ε (φ k)) atTop (𝓝 W) := by
      convert! tendsto_const_nhds.add (hεt.comp hφ.tendsto_atTop) using 1
      simp
    exact sourceRectValue_limit_sublevel (sourceAlphabetDelta input)
      (fun k => R-T (φ k)) (R-τ) (fun k => W+ε (φ k)) W
      (fun k => add_nonneg hW (hε _).le) (hc.tendsto (τ,κ) |>.comp hlim) ht (fun k => (hObj (φ k)).le)
  exact ⟨τ,κ,hτ.1,hκ.1,hκ.2,hδlim,hob⟩

end SourceOptimizedAttainment

/-- Lifts a map of work-register labels while preserving the query and alphabet coordinates. -/
def sourceWorkCode {A B : Type} {n q : ℕ} (e : A → B) :
    ((Fin (n+1)×Fin (q+1))×A) → ((Fin (n+1)×Fin (q+1))×B) :=
  fun p => (p.1,e p.2)

/-- An injective work-register map induces an injective `sourceWorkCode`. -/
theorem sourceWorkCode_injective {A B : Type} {n q : ℕ} (e : A → B)
    (he : Function.Injective e) : Function.Injective (sourceWorkCode (n:=n) (q:=q) e) := by
  intro p t h
  exact Prod.ext (congrArg (fun v : (Fin (n+1)×Fin (q+1))×B => v.1) h)
    (he (congrArg (fun v : (Fin (n+1)×Fin (q+1))×B => v.2) h))

/-- The basis frame induced by a work-register map intertwines the corresponding alphabet
oracles. -/
theorem sourceWorkFrame_oracle {X A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (e : A → B) (x : X) :
    sourceAlphabetOracle input x*sourceBasisFrame (sourceWorkCode e)=
      sourceBasisFrame (sourceWorkCode e)*sourceAlphabetOracle input x := by
  change permMatrix (sourceGramAlphabetEquiv (S:=B) input x)*sourceBasisFrame (sourceWorkCode e)=
    sourceBasisFrame (sourceWorkCode e)*permMatrix (sourceGramAlphabetEquiv (S:=A) input x)
  apply sourceBasisFrame_permutation
  intro t
  rfl

/-- Compiles a legal source word along an injective work-register map, intertwining its
evaluation and using at most twice as many oracle calls. -/
theorem sourceWork_compile {X A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (e : A → B) (he : Function.Injective e)
    (C : SourceWord ((Fin (n+1)×Fin (q+1))×A)) (hC : sourceWordLegal C) :
    ∃ D : SourceWord ((Fin (n+1)×Fin (q+1))×B),
      sourceWordLegal D ∧ sourceWordCalls D≤2*sourceWordCalls C ∧ ∀ x,
      sourceWordMatrix (sourceAlphabetOracle input x) D*sourceBasisFrame (sourceWorkCode e)=
        sourceBasisFrame (sourceWorkCode e)*sourceWordMatrix (sourceAlphabetOracle input x) C := by
  let F := sourceBasisFrame (sourceWorkCode (n:=n) (q:=q) e)
  have hF : Fᴴ*F=1 := sourceBasisFrame_isometry _ (sourceWorkCode_injective e he)
  apply sourceWordCompile F hF (sourceAlphabetOracle input) (sourceAlphabetOracle input)
    (sourceAlphabetOracle_unitary input) (sourceAlphabetOracle_unitary input)
    [.inr false] (by intro s hs; simp only [List.mem_singleton] at hs; subst s; trivial)
    (by simp [sourceWordCalls])
    (fun x => by simpa [sourceWordMatrix] using! sourceWorkFrame_oracle input e x) C hC

/-- Encodes an additional direct-sum data register into an enlarged clock register using a fixed
data label for the added summand. -/
def sourcePaddingWorkCode {H K : Type} [Fintype K] (r : ℕ) (h0 : H) :
    ((Bool×(H⊕K))×Fin r) → ((Bool×H)×Fin ((Fintype.card K+1)*r))
  | ((tag,.inl h),a) => ((tag,h),finProdFinEquiv (0,a))
  | ((tag,.inr k),a) => ((tag,h0),finProdFinEquiv (((Fintype.equivFin K) k).succ,a))

/-- The work-register encoding `sourcePaddingWorkCode` is injective. -/
theorem sourcePaddingWorkCode_injective {H K : Type} [Fintype K] (r : ℕ) (h0 : H) :
    Function.Injective (sourcePaddingWorkCode (K:=K) r h0) := by
  intro p t h
  rcases p with ⟨⟨b,p⟩,a⟩
  rcases t with ⟨⟨c,t⟩,z⟩
  have htag := congrArg (fun v => v.1.1) h
  have hanc := congrArg Prod.snd h
  cases p with
  | inl p =>
    cases t with
    | inl t =>
      have hd := congrArg (fun v => v.1.2) h
      have ha := congrArg Prod.snd (finProdFinEquiv.injective hanc)
      simp only [sourcePaddingWorkCode] at htag hd
      subst c
      subst t
      dsimp only [Prod.snd] at ha
      subst z
      rfl
    | inr t =>
      have hh := congrArg (fun v => v.1.val) (finProdFinEquiv.injective hanc)
      simp only [Fin.val_zero,Fin.val_succ] at hh
      omega
  | inr p =>
    cases t with
    | inl t =>
      have hh := congrArg (fun v => v.1.val) (finProdFinEquiv.injective hanc)
      simp only [Fin.val_zero,Fin.val_succ] at hh
      omega
    | inr t =>
      have hh := finProdFinEquiv.injective hanc
      have ha := congrArg Prod.snd hh
      have hk : p=t := (Fintype.equivFin K).injective (Fin.succ_inj.mp (congrArg Prod.fst hh))
      simp only [sourcePaddingWorkCode] at htag
      subst c
      subst t
      dsimp only [Prod.snd] at ha
      subst z
      rfl

/-- Multiplication of basis frames agrees with composition of their underlying label maps. -/
theorem sourceBasisFrame_comp {S T U : Type} [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : T → S) (f : U → T) : sourceBasisFrame e*sourceBasisFrame f=sourceBasisFrame (e ∘ f) := by
  ext s u
  simp only [Matrix.mul_apply,sourceBasisFrame,Function.comp_apply]
  rw [Finset.sum_eq_single (f u)]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

/-- The basis frame at zero query and clock coordinates sends a data state to its clean source
embedding. -/
theorem sourceClean_basisFrame {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (fun h : H => ((0,0),((tag,h),(⟨0,hr⟩ : Fin r))) :
      H → SourceSpace n q H r) *ᵥ ψ=sourceClean n q r hr tag ψ := by
  ext p
  simp only [Matrix.mulVec,dotProduct,sourceBasisFrame]
  rw [Finset.sum_eq_single p.2.1.2]
  · simp [sourceClean,TensorState,Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff]
    split_ifs <;> simp_all
  · intro h _ hh
    have hp : p≠((0,0),((tag,h),(⟨0,hr⟩ : Fin r))) := by
      intro he
      exact hh (congrArg (fun v : SourceSpace n q H r => v.2.1.2) he).symm
    simp [hp]
  · simp

/-- The basis frame into the left data summand sends a state to the clean embedding of its
extension by zero. -/
theorem sourceClean_inl_basisFrame {H K : Type} [Fintype H] [DecidableEq H] [DecidableEq K]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (fun h : H => ((0,0),((tag,Sum.inl h),(⟨0,hr⟩ : Fin r))) :
      H → SourceSpace n q (H⊕K) r) *ᵥ ψ=sourceClean n q r hr tag (Sum.elim ψ 0) := by
  ext p
  cases hd : p.2.1.2 with
  | inl h =>
    simp only [Matrix.mulVec,dotProduct,sourceBasisFrame]
    rw [Finset.sum_eq_single h]
    · simp [sourceClean,TensorState,Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff,hd]
      split_ifs <;> simp_all
    · intro t _ ht
      have hp : p≠((0,0),((tag,Sum.inl t),(⟨0,hr⟩ : Fin r))) := by
        intro he
        have hh := congrArg (fun v : SourceSpace n q (H⊕K) r => v.2.1.2) he
        (try dsimp only at hh)
        rw [hd] at hh
        exact ht (Sum.inl.inj hh).symm
      simp [hp]
    · simp
  | inr k =>
    have hp (h : H) : p≠((0,0),((tag,Sum.inl h),(⟨0,hr⟩ : Fin r))) := by
      intro he
      have hh := congrArg (fun v : SourceSpace n q (H⊕K) r => v.2.1.2) he
      (try dsimp only at hh)
      rw [hd] at hh
      cases hh
    simp [Matrix.mulVec,dotProduct,sourceBasisFrame,hp,sourceClean,TensorState,hd]

/-- The padding frame sends a clean state in the left data summand to the same clean data state
with an enlarged clock register. -/
theorem sourcePaddingFrame_clean {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (n q r : ℕ) (hr : 0<r) (h0 : H)
    (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (sourceWorkCode (sourcePaddingWorkCode (K:=K) r h0)) *ᵥ
      sourceClean n q r hr tag (Sum.elim ψ (0 : QState K))=
      sourceClean n q ((Fintype.card K+1)*r) (by positivity) tag ψ := by
  rw [← sourceClean_inl_basisFrame]
  rw [Matrix.mulVec_mulVec,sourceBasisFrame_comp]
  have he : sourceWorkCode (n:=n) (q:=q) (sourcePaddingWorkCode (K:=K) r h0) ∘
      (fun h : H => ((0,0),((tag,Sum.inl h),(⟨0,hr⟩ : Fin r))))=
      (fun h : H => ((0,0),((tag,h),(⟨0,by positivity⟩ : Fin ((Fintype.card K+1)*r))))) := by
    funext h
    simp only [Function.comp_apply,sourceWorkCode,sourcePaddingWorkCode]
    congr 1
  rw [he]
  exact sourceClean_basisFrame n q _ _ tag ψ

/-- Transfers a legal conversion program from `H ⊕ K` to `H` with enlarged workspace, preserving
the error bound and at most doubling oracle calls. -/
theorem sourcePadding_program {X H K : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (r : ℕ) (hr : 0<r)
    (C : SourceWord (SourceSpace n q (H⊕K) r)) (hC : sourceWordLegal C)
    (e : ℝ) (herr : ∀ x, ‖toEuclidean_fromVec
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (Sum.elim (ρ x) 0)-
        sourceClean n q r hr true (Sum.elim (σ x) 0))‖≤e) :
    ∃ (s : ℕ) (hs : 0<s) (D : SourceWord (SourceSpace n q H s)),
      sourceWordLegal D ∧ sourceWordCalls D≤2*sourceWordCalls C ∧ ∀ x,
      ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
        sourceClean n q s hs false (ρ x)-sourceClean n q s hs true (σ x))‖≤e := by
  let h0 : H := Classical.choice inferInstance
  let s := (Fintype.card K+1)*r
  have hs : 0<s := by dsimp [s]; positivity
  let code := sourcePaddingWorkCode (K:=K) r h0
  let F := sourceBasisFrame (sourceWorkCode (n:=n) (q:=q) code)
  have hF : Fᴴ*F=1 := sourceBasisFrame_isometry _
    (sourceWorkCode_injective code (sourcePaddingWorkCode_injective r h0))
  obtain ⟨D,hD,hcalls,hact⟩ := sourceWork_compile input code
    (sourcePaddingWorkCode_injective r h0) C hC
  refine ⟨s,hs,D,hD,hcalls,?_⟩
  intro x
  have hp := sourcePaddingFrame_clean (K:=K) n q r hr h0 false (ρ x)
  have ht := sourcePaddingFrame_clean (K:=K) n q r hr h0 true (σ x)
  change F *ᵥ _=sourceClean n q s hs false (ρ x) at hp
  change F *ᵥ _=sourceClean n q s hs true (σ x) at ht
  rw [← hp,← ht,Matrix.mulVec_mulVec,hact x,← Matrix.mulVec_mulVec,← Matrix.mulVec_sub,
    Qatlib.Concepts.BlockEncoding.EncodingCore.isometry_mulVec_norm hF]
  exact herr x

/-- Every finite positive semidefinite matrix with unit diagonal is the Gram matrix of a family
of normalized states. -/
theorem sourcePSD_normalized_family {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ) (hT : T.PosSemidef) (hd : ∀ x,T x x=1) :
    ∃ τ : X → QState X,(∀ x,Normalized (τ x))∧gramStateMatrix τ=T := by
  obtain ⟨V,hV⟩ := gram_positive_matrix_actual_factorization X T hT
  let τ : X → QState X := fun x k => V k x
  have hg : gramStateMatrix τ=T := by
    change Vᴴ*V=T
    exact hV
  refine ⟨τ,?_,hg⟩
  intro x
  apply (normalized_iff_inner_self _).mpr
  have hh := congrFun (congrFun hg x) x
  exact hh.trans (hd x)

/-- Extension by zero into a left direct summand preserves a family's Gram matrix. -/
theorem sourceSum_left_gram {X H K : Type} [Fintype H] [Fintype K]
    (ρ : X → QState H) : gramStateMatrix (fun x => Sum.elim (ρ x) (0 : QState K))=
      gramStateMatrix ρ := by
  ext x y
  simp [gramStateMatrix,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_sum_type]

/-- Extension by zero into a right direct summand preserves a family's Gram matrix. -/
theorem sourceSum_right_gram {X H K : Type} [Fintype H] [Fintype K]
    (ρ : X → QState K) : gramStateMatrix (fun x => Sum.elim (0 : QState H) (ρ x))=
      gramStateMatrix ρ := by
  ext x y
  simp [gramStateMatrix,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_sum_type]

/-- Extension by zero into a left direct summand preserves normalization. -/
theorem sourceSum_left_normalized {H K : Type} [Fintype H] [Fintype K]
    (ρ : QState H) (hρ : Normalized ρ) : Normalized (Sum.elim ρ (0 : QState K)) := by
  simp only [Normalized,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,
    norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]
  exact hρ

/-- Extension by zero into a right direct summand preserves normalization. -/
theorem sourceSum_right_normalized {H K : Type} [Fintype H] [Fintype K]
    (ρ : QState K) (hρ : Normalized ρ) : Normalized (Sum.elim (0 : QState H) ρ) := by
  simp only [Normalized,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,
    norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,zero_add]
  exact hρ

/-- Lifts a matrix on the data register to the source space, acting identically on the other
registers. -/
def sourceDataGate {H : Type} [DecidableEq H] (n q r : ℕ) (U : Matrix H H ℂ) :
    Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ :=
  TensorGate (1 : Matrix (Fin (n+1)×Fin (q+1)) _ ℂ)
    (TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) U) (1 : Matrix (Fin r) _ ℂ))

/-- Lifting a unitary data matrix by `sourceDataGate` yields a unitary source-space matrix. -/
theorem sourceDataGate_unitary {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (U : Matrix H H ℂ) (hU : U∈Matrix.unitaryGroup _ ℂ) :
    sourceDataGate n q r U∈Matrix.unitaryGroup _ ℂ := by
  exact tensorGate_unitary (Submonoid.one_mem _) (tensorGate_unitary
    (tensorGate_unitary (Submonoid.one_mem _) hU) (Submonoid.one_mem _))

/-- A lifted data gate acts on a clean source state by applying its matrix to the data state. -/
theorem sourceDataGate_clean {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (U : Matrix H H ℂ) (tag : Bool) (ψ : QState H) :
    sourceDataGate n q r U *ᵥ sourceClean n q r hr tag ψ=
      sourceClean n q r hr tag (U *ᵥ ψ) := by
  unfold sourceDataGate sourceClean
  rw [← ApplyGate,applyGate_tensorGate,applyGate_one,applyGate_tensorGate,
    applyGate_tensorGate,applyGate_one,applyGate_one]
  rfl

/-- The clean source embedding preserves subtraction of data states. -/
theorem sourceClean_sub {H : Type} [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ φ : QState H) :
    sourceClean n q r hr tag ψ-sourceClean n q r hr tag φ=
      sourceClean n q r hr tag (ψ-φ) := by
  ext p
  simp only [sourceClean,TensorState,Pi.sub_apply]
  ring

/-- The clean source embedding preserves the Euclidean norm. -/
theorem sourceClean_norm {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState H) :
    ‖toEuclidean_fromVec (sourceClean n q r hr tag ψ)‖=‖toEuclidean_fromVec ψ‖ := by
  rw [sourceClean,tensorState_l2_norm,tensorState_l2_norm,tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _),(normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _),(normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _),
    one_mul,one_mul,mul_one]

/-- Appends a unitary data correction to a legal conversion word without changing its
oracle-call count, adding the two error bounds. -/
theorem sourceDataGate_append {X H : Type} [Fintype H] [DecidableEq H]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (ρ τ σ : X → QState H)
    (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)) (hC : sourceWordLegal C)
    (U : Matrix H H ℂ) (hU : U∈Matrix.unitaryGroup _ ℂ) (e d : ℝ)
    (hc : ∀ x,‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (τ x))‖≤e)
    (hu : ∀ x,‖toEuclidean_fromVec (U *ᵥ τ x-σ x)‖≤d) :
    ∃ D : SourceWord (SourceSpace n q H r),sourceWordLegal D∧sourceWordCalls D=sourceWordCalls C∧
      ∀ x,‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖≤e+d := by
  let G := sourceDataGate n q r U
  have hG : G∈Matrix.unitaryGroup _ ℂ := sourceDataGate_unitary n q r U hU
  refine ⟨C++[.inl G],sourceWordLegal_append C _ hC ?_,?_,?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hG
  · rw [sourceWordCalls_append]
    simp [sourceWordCalls]
  · intro x
    rw [sourceWordMatrix_append]
    have hmat : sourceWordMatrix (sourceAlphabetOracle input x) [.inl G]=G := by
      simp [sourceWordMatrix]
    rw [hmat,← Matrix.mulVec_mulVec]
    let out := sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ sourceClean n q r hr false (ρ x)
    let t := sourceClean n q r hr true (τ x)
    let s := sourceClean n q r hr true (σ x)
    have he : G *ᵥ out-s=G *ᵥ (out-t)+(G *ᵥ t-s) := by rw [Matrix.mulVec_sub]; abel
    change ‖toEuclidean_fromVec (G *ᵥ out-s)‖≤e+d
    rw [he]
    change ‖toEuclidean_fromVec (G *ᵥ (out-t))+toEuclidean_fromVec (G *ᵥ t-s)‖≤e+d
    apply (norm_add_le _ _).trans
    apply add_le_add
    · change ‖toEuclidean_fromVec (ApplyGate G (out-t))‖≤e
      rw [norm_applyGate_of_mem_unitaryGroup hG]
      exact hc x
    · change ‖toEuclidean_fromVec (sourceDataGate n q r U *ᵥ
        sourceClean n q r hr true (τ x)-sourceClean n q r hr true (σ x))‖≤d
      rw [sourceDataGate_clean,sourceClean_sub,sourceClean_norm]
      exact hu x

/-- The stated ceiling-based call bound is at most `131072 * c * W * log (1 / ε) / ε²` for the
given positive error and budget range. -/
theorem sourceOptimized_resources (W ε : ℝ) (c T : ℕ)
    (hε : 0<ε) (hε1 : ε≤1/3) (hW : ε/64≤W)
    (hT : T≤2*c*Nat.ceil (W*Real.log (2/(ε/64))/(ε/64)^2)) :
    (T : ℝ)≤((131072*c : ℕ) : ℝ)*W*Real.log (1/ε)/ε^2 := by
  let y := W/ε^2
  let L := Real.log (1/ε)
  let A := W*Real.log (2/(ε/64))/(ε/64)^2
  let X := W*L/ε^2
  have hWp : 0<W := lt_of_lt_of_le (by positivity : (0 : ℝ)<ε/64) hW
  have hεle : ε≤1 := by linarith
  have hL2 : Real.log 2≤L := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hε).mpr (by linarith : (2 : ℝ)*ε≤1))
  have hLp : (1/2 : ℝ)≤L := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log (2/(ε/64))=7*Real.log 2+L := by
    have he : 2/(ε/64)=(128 : ℝ)*(1/ε) := by field_simp; norm_num
    rw [he,Real.log_mul (by norm_num : (128 : ℝ)≠0) (by positivity : (1/ε : ℝ)≠0)]
    have hp : Real.log (128 : ℝ)=7*Real.log 2 := by
      rw [show (128 : ℝ)=2^7 by norm_num,Real.log_pow]
      norm_num
    rw [hp]
  have hy : (1/64 : ℝ)≤y := by
    apply (le_div_iff₀ (by positivity : 0<ε^2)).mpr
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεle)]
  have hA : A=4096*y*Real.log (2/(ε/64)) := by dsimp [A,y]; field_simp; ring
  have hX : X=y*L := by dsimp [X,y]; ring
  have hAL : A=4096*y*(7*Real.log 2+L) := by rw [hA,hlog]
  have hloglow : (1/2 : ℝ)≤7*Real.log 2+L := by linarith [Real.log_two_gt_d9]
  have hAb : 1≤A := by
    rw [hAL]
    have hh := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hloglow)
    nlinarith
  have hAup : A≤32768*X := by
    rw [hAL,hX]
    have hh : 7*Real.log 2+L≤8*L := by linarith
    have hm := mul_le_mul_of_nonneg_left hh (show 0≤4096*y by positivity)
    nlinarith
  have hceil : (Nat.ceil A : ℝ)≤2*A := by
    have hh := Nat.ceil_lt_add_one (show 0≤A by linarith)
    linarith
  have hTr : (T : ℝ)≤2*(c : ℝ)*(Nat.ceil A : ℝ) := by exact_mod_cast hT
  have hf : (T : ℝ)≤131072*(c : ℝ)*X := by
    calc
      _ ≤ 2*(c : ℝ)*(Nat.ceil A : ℝ) := hTr
      _ ≤ 2*(c : ℝ)*(2*A) := mul_le_mul_of_nonneg_left hceil (by positivity)
      _ ≤ 2*(c : ℝ)*(2*(32768*X)) := by gcongr
      _ = _ := by ring
  push_cast
  convert! hf using 1
  dsimp [X,L]
  ring

/-- Relabeling states by direct-sum associativity reassociates their componentwise direct sum. -/
theorem sourceRelabel_sum_assoc {H J K : Type} (ρ : QState H) (σ : QState J) (τ : QState K) :
    relabelState (Equiv.sumAssoc H J K) (Sum.elim (Sum.elim ρ σ) τ)=
      Sum.elim ρ (Sum.elim σ τ) := by
  ext p
  cases p with
  | inl h => rfl
  | inr p => cases p <;> rfl

/-- Normalized families with unfiltered Gram discrepancy at most `δ` possess a unitary on an
enlarged data space with pointwise error at most `sqrt (2 * δ)`. -/
theorem sourceFreeData_completion {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J] (ρ σ : X → QState J) (δ : ℝ)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) (hδ : 0≤δ)
    (hg : sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ)≤ENNReal.ofReal δ) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
      (U : Matrix (J⊕K) (J⊕K) ℂ),U∈Matrix.unitaryGroup _ ℂ∧∀ x,
      ‖toEuclidean_fromVec (U *ᵥ Sum.elim (ρ x) (0 : QState K)-Sum.elim (σ x) 0)‖≤
        Real.sqrt (2*δ) := by
  have hc : gramFilteredCert (gramStateMatrix ρ-gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) δ := by
    unfold sourceUnfiltered at hg
    rw [sourceSquareValue_eq] at hg
    exact (filteredGamma2_budget_boundary X 1 _ _ δ hδ).mp hg
  exact sourceGram_unitary_L2_of_cert hδ ρ σ (fun x => (hn x).1) (fun x => (hn x).2) hc

/-- Combines a data matrix with a flip of the Boolean source tag, leaving query and clock
coordinates unchanged. -/
def sourceFlipDataGate {H : Type} [DecidableEq H] (n q r : ℕ) (U : Matrix H H ℂ) :
    Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ :=
  TensorGate (1 : Matrix (Fin (n+1)×Fin (q+1)) _ ℂ)
    (TensorGate (TensorGate PauliX U) (1 : Matrix (Fin r) _ ℂ))

/-- The tag-flipping lift of a unitary data matrix is unitary. -/
theorem sourceFlipDataGate_unitary {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (U : Matrix H H ℂ) (hU : U∈Matrix.unitaryGroup _ ℂ) :
    sourceFlipDataGate n q r U∈Matrix.unitaryGroup _ ℂ := by
  exact tensorGate_unitary (Submonoid.one_mem _) (tensorGate_unitary
    (tensorGate_unitary pauliX_unitary hU) (Submonoid.one_mem _))

/-- The tag-flipping data gate sends a clean false-tagged state to the true-tagged clean
embedding of the transformed data state. -/
theorem sourceFlipDataGate_clean {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (U : Matrix H H ℂ) (ψ : QState H) :
    sourceFlipDataGate n q r U *ᵥ sourceClean n q r hr false ψ=
      sourceClean n q r hr true (U *ᵥ ψ) := by
  unfold sourceFlipDataGate sourceClean
  rw [← ApplyGate,applyGate_tensorGate,applyGate_one,applyGate_tensorGate,
    applyGate_tensorGate,applyGate_pauliX_ket,applyGate_one]
  rfl

/-- A positive semidefinite intermediate Gram matrix within `ε⁴ / 16` of the target yields a
legal enlarged-space conversion word with squared error at most `ε` and the stated call
bound. -/
theorem sourceOptimized_public_program {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J] [Nonempty J] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState J) (T : Matrix X X ℂ)
    (W ε : ℝ) (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x))
    (hW : 0≤W) (hε : 0<ε) (hε1 : ε≤1/3) (hT : T.PosSemidef)
    (hnear : sourceUnfiltered (T-gramStateMatrix σ)≤ENNReal.ofReal (ε^4/16))
    (hbudget : sourceRectValue (gramStateMatrix ρ-T) (sourceAlphabetDelta input)≤ENNReal.ofReal W) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (r : ℕ) (hr : 0<r)
      (C : SourceWord (SourceSpace n q (J⊕K) r)),sourceWordLegal C∧
      (sourceWordCalls C : ℝ)≤8589934592*W*Real.log (1/ε)/ε^2∧∀ x,
      ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (Sum.elim (ρ x) 0)-
        sourceClean n q r hr true (Sum.elim (σ x) 0))‖^2≤ε := by
  have he1 : ε≤1 := by linarith
  have he2 : ε^2≤ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr he1)]
  have he4 : ε^4≤ε^2 := by
    calc
      ε^4 = (ε^2)*(ε^2) := by ring
      _ ≤ 1*(ε^2) := mul_le_mul_of_nonneg_right (he2.trans he1) (sq_nonneg ε)
      _ = ε^2 := one_mul _
  have he2half : ε^2≤1/2 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
  have he4half : 2*ε^4≤ε^2 := by
    calc
      2*ε^4 = (2*ε^2)*(ε^2) := by ring
      _ ≤ 1*(ε^2) := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ε)
      _ = ε^2 := one_mul _
  have hlog : 0≤Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have free (δ : ℝ) (hδ : 0≤δ) (hsmall : 2*δ≤ε)
      (hval : sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ)≤ENNReal.ofReal δ) :
      ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (r : ℕ) (hr : 0<r)
        (C : SourceWord (SourceSpace n q (J⊕K) r)),sourceWordLegal C∧
        (sourceWordCalls C : ℝ)≤8589934592*W*Real.log (1/ε)/ε^2∧∀ x,
        ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (Sum.elim (ρ x) 0)-
          sourceClean n q r hr true (Sum.elim (σ x) 0))‖^2≤ε := by
    obtain ⟨K,hK,hKeq,U,hU,hu⟩ := sourceFreeData_completion ρ σ δ hn hδ hval
    let G := sourceFlipDataGate n q 1 U
    have hG : G∈Matrix.unitaryGroup _ ℂ := sourceFlipDataGate_unitary n q 1 U hU
    refine ⟨K,hK,hKeq,1,by norm_num,[.inl G],?_,by have hc : sourceWordCalls [.inl G]=0 := rfl; rw [hc,Nat.cast_zero]; positivity,?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact hG
    · intro x
      simp only [sourceWordMatrix,List.map_cons,List.map_nil,List.reverse_singleton,
        List.prod_cons,List.prod_nil,Matrix.mul_one]
      rw [sourceFlipDataGate_clean,sourceClean_sub,sourceClean_norm]
      have hs := Real.sq_sqrt (show 0≤2*δ by positivity)
      have hx := hu x
      nlinarith [norm_nonneg (toEuclidean_fromVec (U *ᵥ Sum.elim (ρ x) (0 : QState K)-Sum.elim (σ x) 0))]
  by_cases hd : n=0 ∨ q=0
  · have hdiff : gramStateMatrix ρ-T=0 := sourceAlphabet_degenerate_gram input _ W hW hbudget (Or.inr hd)
    have heq : gramStateMatrix ρ=T := sub_eq_zero.mp hdiff
    apply free (ε^4/16) (by positivity) (by nlinarith [sq_nonneg ε,sq_nonneg (ε^2)])
    simpa only [heq] using! hnear
  by_cases hsmall : W≤ε/64
  · have he : gramStateMatrix ρ-gramStateMatrix σ=
        (gramStateMatrix ρ-T)+(T-gramStateMatrix σ) := by abel
    have hb := sourceAlphabet_unfiltered_budget input (gramStateMatrix ρ-T) W hW hbudget
    have hv : sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ)≤
        ENNReal.ofReal (2*W+ε^4/16) := by
      rw [he]
      exact (sourceRectValue_add_le _ _ (fun _ : Fin 1 => fun _ _ => (1 : ℂ))).trans
        ((add_le_add hb hnear).trans_eq (ENNReal.ofReal_add (by positivity) (by positivity)).symm)
    exact free (2*W+ε^4/16) (by positivity) (by nlinarith [sq_nonneg ε,sq_nonneg (ε^2)]) hv
  have hWp : 0<W := by linarith
  have hq : 0<q := by
    have hh : q≠0 := by intro he; exact hd (Or.inr he)
    omega
  have hRdiag (x : X) : gramStateMatrix ρ x x=1 := (normalized_iff_inner_self _).mp (hn x).1
  have hTdiag := sourceAlphabet_finite_diagonal input (gramStateMatrix ρ) T hRdiag
    (hbudget.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨τ,hτ,hτGram⟩ := sourcePSD_normalized_family T hT hTdiag
  let ρ0 : X → QState (J⊕X) := fun x => Sum.elim (ρ x) 0
  let τ0 : X → QState (J⊕X) := fun x => Sum.elim 0 (τ x)
  let σ0 : X → QState (J⊕X) := fun x => Sum.elim (σ x) 0
  have hn0 : ∀ x,Normalized (τ0 x)∧Normalized (σ0 x) := fun x =>
    ⟨sourceSum_right_normalized _ (hτ x),sourceSum_left_normalized _ (hn x).2⟩
  have hnear0 : sourceUnfiltered (gramStateMatrix τ0-gramStateMatrix σ0)≤ENNReal.ofReal (ε^4/16) := by
    rw [sourceSum_right_gram,sourceSum_left_gram,hτGram]
    exact hnear
  obtain ⟨K,hK,hKeq,U,hU,hu⟩ := sourceFreeData_completion τ0 σ0 (ε^4/16) hn0 (by positivity) hnear0
  let E := Equiv.sumAssoc J X K
  let R : X → QState (J⊕(X⊕K)) := fun x => Sum.elim (ρ x) 0
  let V : X → QState (J⊕(X⊕K)) := fun x => Sum.elim 0 (Sum.elim (τ x) 0)
  let S : X → QState (J⊕(X⊕K)) := fun x => Sum.elim (σ x) 0
  let G : Matrix (J⊕(X⊕K)) (J⊕(X⊕K)) ℂ := relabelGate E U
  have hG : G∈Matrix.unitaryGroup _ ℂ := (relabelGate_mem_unitaryGroup E U).mpr hU
  have hRelT (x : X) : relabelState E (Sum.elim (τ0 x) (0 : QState K))=V x :=
    sourceRelabel_sum_assoc 0 (τ x) 0
  have hz : Sum.elim (0 : QState X) (0 : QState K)=(0 : QState (X⊕K)) := by
    ext p
    cases p <;> rfl
  have hRelS (x : X) : relabelState E (Sum.elim (σ0 x) (0 : QState K))=S x := by
    simpa only [E,σ0,S,hz] using! sourceRelabel_sum_assoc (σ x) (0 : QState X) (0 : QState K)
  have herrG (x : X) : ‖toEuclidean_fromVec (G *ᵥ V x-S x)‖≤Real.sqrt (2*(ε^4/16)) := by
    rw [← hRelT,← hRelS]
    change ‖toEuclidean_fromVec (ApplyGate (relabelGate E U)
      (relabelState E (Sum.elim (τ0 x) 0))-relabelState E (Sum.elim (σ0 x) 0))‖≤_
    rw [applyGate_relabelGate]
    have hd : relabelState E (ApplyGate U (Sum.elim (τ0 x) (0 : QState K)))-
        relabelState E (Sum.elim (σ0 x) (0 : QState K))=
        relabelState E (U *ᵥ Sum.elim (τ0 x) 0-Sum.elim (σ0 x) 0) := by
      ext p
      rfl
    rw [hd,norm_toEuclidean_relabelState]
    exact hu x
  have hnRV : ∀ x,Normalized (R x)∧Normalized (V x) := fun x =>
    ⟨sourceSum_left_normalized _ (hn x).1,
      sourceSum_right_normalized _ (sourceSum_left_normalized _ (hτ x))⟩
  have hbudRV : sourceRectValue (gramStateMatrix R-gramStateMatrix V) (sourceAlphabetDelta input)≤ENNReal.ofReal W := by
    rw [sourceSum_left_gram,sourceSum_right_gram,sourceSum_left_gram,hτGram]
    exact hbudget
  obtain ⟨m,u,v,hEq,huv,hvv⟩ := (sourceRectValue_budget_boundary _ _ W hW).mp hbudRV
  let ζ := ε/64
  let L := max 1 (Nat.ceil (W/ζ^2))
  let a := Nat.clog 2 (2048*L)
  have hζ : 0<ζ := by dsimp [ζ]; positivity
  have hζ1 : ζ≤1/3 := by dsimp [ζ]; linarith
  have hζW : ζ≤W := by dsimp [ζ]; linarith
  obtain ⟨hM,hMl,_,hqueries⟩ := sourceOnePass_resources W ζ hζ hζ1 (by linarith)
  obtain ⟨r,hr,C,hC,hcalls,herr⟩ := source_onepass_native_algorithm input R V u v W (ζ/64)
    hnRV hq hWp (by positivity) (by linarith) a hM hEq (fun x => ⟨huv x,hvv x⟩)
  have hsize : 2048*(W/ζ^2)≤(2^a : ℕ) := by
    have hc : Nat.ceil (W/ζ^2)≤L := le_max_right _ _
    have hl : W/ζ^2≤(L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hc)
    have hm : (2048 : ℝ)*(L : ℝ)≤(2^a : ℕ) := by exact_mod_cast hMl
    exact (mul_le_mul_of_nonneg_left hl (by norm_num)).trans hm
  have herrC (x : X) : ‖toEuclidean_fromVec (@sourceWordMatrix (SourceSpace n q (J⊕(X⊕K)) r) _
        (instDecidableEqProd : DecidableEq (SourceSpace n q (J⊕(X⊕K)) r))
        (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (R x)-sourceClean n q r hr true (V x))‖≤ζ/4 :=
    (herr x).trans (sourceOnePass_error_bound W ζ hζ (by linarith) (2^a) (by have hh : 2≤2^a := hM; omega) hsize)
  obtain ⟨D,hD,hDC,herrD⟩ := sourceDataGate_append input R V S r hr C hC G hG
    (ζ/4) (Real.sqrt (2*(ε^4/16))) herrC herrG
  have hDcalls : sourceWordCalls D≤2*65536*Nat.ceil (W*Real.log (2/(ε/64))/(ε/64)^2) := by
    rw [hDC]
    have hh := hcalls.trans hqueries
    change sourceWordCalls C≤65536*Nat.ceil (W*Real.log (2/(ε/64))/(ε/64)^2) at hh
    omega
  have hreal := sourceOptimized_resources W ε 65536 (sourceWordCalls D) hε hε1 (by linarith) hDcalls
  refine ⟨X⊕K,inferInstance,inferInstance,r,hr,D,hD,by simpa using! hreal,?_⟩
  intro x
  have hx := herrD x
  have hsqrt : Real.sqrt (2*(ε^4/16))≤ε/4 := by
    have hs := Real.sq_sqrt (show 0≤2*(ε^4/16) by positivity)
    nlinarith [Real.sqrt_nonneg (2*(ε^4/16)),sq_nonneg ε,sq_nonneg (ε^2)]
  have hb : ‖toEuclidean_fromVec (@sourceWordMatrix (SourceSpace n q (J⊕(X⊕K)) r) _
        (instDecidableEqProd : DecidableEq (SourceSpace n q (J⊕(X⊕K)) r))
        (sourceAlphabetOracle input x) D *ᵥ
      sourceClean n q r hr false (R x)-sourceClean n q r hr true (S x))‖≤ε/2 := by
    dsimp only [ζ] at hx
    linarith
  nlinarith [norm_nonneg (toEuclidean_fromVec (@sourceWordMatrix (SourceSpace n q (J⊕(X⊕K)) r) _
        (instDecidableEqProd : DecidableEq (SourceSpace n q (J⊕(X⊕K)) r))
        (sourceAlphabetOracle input x) D *ᵥ
    sourceClean n q r hr false (R x)-sourceClean n q r hr true (S x)))]

/-- A coherent raw budget `W` at tolerance `ε⁴ / 16` yields a legal word with real output
overlap at least `sqrt (1 - ε)` and at most `17179869184 * W * log (1 / ε) / ε²` calls. See
[LeeEtAl2011]. -/
theorem sourceCoherent_raw_budget_word {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε W : ℝ)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) (hε : 0<ε) (hε1 : ε≤1/3) (hW : 0≤W)
    (hQ : sourceQDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ)≤ENNReal.ofReal W) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),sourceWordLegal C∧
      (sourceWordCalls C : ℝ)≤17179869184*W*Real.log (1/ε)/ε^2∧∀ x,
      (∑ p,star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re≥Real.sqrt (1-ε) := by
  have hd (x : X) : gramStateMatrix ρ x x=1 := (normalized_iff_inner_self _).mp (hn x).1
  obtain ⟨T,hT,hnear,hbudget⟩ := sourceQDelta_raw_attainment input (ε^4/16) W
    (gramStateMatrix ρ) (gramStateMatrix σ) (by positivity) hW (gramStateMatrix_posSemidef ρ) hd hQ
  obtain ⟨K,hK,hKeq,r,hr,C,hC,hcount,herr⟩ := sourceOptimized_public_program input ρ σ T W ε
    hn hW hε hε1 hT hnear hbudget
  have he1 : ε≤1 := by linarith
  have hroot := Real.sq_sqrt hε.le
  have hnerr (x : X) : ‖toEuclidean_fromVec
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (Sum.elim (ρ x) (0 : QState K))-
        sourceClean n q r hr true (Sum.elim (σ x) 0))‖≤Real.sqrt ε := by
    have hh := herr x
    nlinarith [Real.sqrt_nonneg ε,norm_nonneg (toEuclidean_fromVec
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (Sum.elim (ρ x) (0 : QState K))-
        sourceClean n q r hr true (Sum.elim (σ x) 0)))]
  obtain ⟨s,hs,D,hD,hcalls,hDerr⟩ := sourcePadding_program input ρ σ r hr C hC (Real.sqrt ε) hnerr
  have hreal : (sourceWordCalls D : ℝ)≤17179869184*W*Real.log (1/ε)/ε^2 := by
    calc
      _ ≤ 2*(sourceWordCalls C : ℝ) := by exact_mod_cast hcalls
      _ ≤ 2*(8589934592*W*Real.log (1/ε)/ε^2) := mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = _ := by ring
  refine ⟨s,hs,D,hD,hreal,?_⟩
  intro x
  have hx := hDerr x
  have hd2 : ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
      sourceClean n q s hs false (ρ x)-sourceClean n q s hs true (σ x))‖^2≤ε := by
    nlinarith [norm_nonneg (toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
      sourceClean n q s hs false (ρ x)-sourceClean n q s hs true (σ x)))]
  exact source_overlap_of_distance _ _
    (normalized_applyGate (sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) D hD)
      (sourceClean_normalized n q s hs false (ρ x) (hn x).1))
    (sourceClean_normalized n q s hs true (σ x) (hn x).2) ε hε.le he1 hd2

/-- Encodes a garbage-state label in the record block following the distinguished zero record. -/
def sourceNCYRecord {Y K : Type} [Fintype Y] [Fintype K] (y : Y) :
    Fin (Fintype.card Y+1+Fintype.card K) := ((Fintype.equivFin Y) y).succ.castAdd (Fintype.card K)
/-- Encodes an auxiliary data label in the record block following the garbage-label records. -/
def sourceNCKRecord {Y K : Type} [Fintype Y] [Fintype K] (k : K) :
    Fin (Fintype.card Y+1+Fintype.card K) := Fin.natAdd (Fintype.card Y+1) ((Fintype.equivFin K) k)

/-- Encodes the nested data sum into a data label and a finite record, using a fixed data label
for the auxiliary summand. -/
def sourceNCDataRecord {H Y K : Type} [Fintype Y] [Fintype K] (h0 : H) :
    ((H⊕(H×Y))⊕K) → H×Fin (Fintype.card Y+1+Fintype.card K)
  | .inl (.inl h) => (h,⟨0,by omega⟩)
  | .inl (.inr (h,y)) => (h,sourceNCYRecord (K:=K) y)
  | .inr k => (h0,sourceNCKRecord (Y:=Y) k)

/-- The nested-data record encoding is injective. -/
theorem sourceNCDataRecord_injective {H Y K : Type} [Fintype Y] [Fintype K] (h0 : H) :
    Function.Injective (sourceNCDataRecord (Y:=Y) (K:=K) h0) := by
  intro p t he
  have hd := congrArg Prod.fst he
  have hr := congrArg (fun v => v.2.val) he
  cases p with
  | inl p =>
    cases p with
    | inl p =>
      cases t with
      | inl t =>
        cases t with
        | inl t => exact congrArg (Sum.inl ∘ Sum.inl) hd
        | inr t => simp [sourceNCDataRecord,sourceNCYRecord] at hr
      | inr t => simp [sourceNCDataRecord,sourceNCKRecord] at hr; omega
    | inr p =>
      rcases p with ⟨h,y⟩
      cases t with
      | inl t =>
        cases t with
        | inl t => simp [sourceNCDataRecord,sourceNCYRecord] at hr
        | inr t =>
          rcases t with ⟨j,z⟩
          have hh : h=j := hd
          have hy : y=z := (Fintype.equivFin Y).injective (Fin.ext (by
            simp [sourceNCDataRecord,sourceNCYRecord] at hr
            omega))
          subst j
          subst z
          rfl
      | inr t =>
        have hy := ((Fintype.equivFin Y) y).isLt
        simp [sourceNCDataRecord,sourceNCYRecord,sourceNCKRecord] at hr
        omega
  | inr p =>
    cases t with
    | inl t =>
      cases t with
      | inl t => simp [sourceNCDataRecord,sourceNCKRecord] at hr
      | inr t =>
        have hy := ((Fintype.equivFin Y) t.2).isLt
        simp [sourceNCDataRecord,sourceNCYRecord,sourceNCKRecord] at hr
        omega
    | inr t =>
      apply congrArg Sum.inr
      apply (Fintype.equivFin K).injective
      apply Fin.ext
      simp [sourceNCDataRecord,sourceNCKRecord] at hr
      omega

/-- Combines the noncoherent data-record encoding with the Boolean tag and clock coordinates. -/
def sourceNCWorkCode {H Y K : Type} [Fintype Y] [Fintype K] (r : ℕ) (h0 : H) :
    ((Bool×((H⊕(H×Y))⊕K))×Fin r) →
      ((Bool×H)×Fin ((Fintype.card Y+1+Fintype.card K)*r)) := fun p =>
  ((p.1.1,(sourceNCDataRecord (Y:=Y) (K:=K) h0 p.1.2).1),
    finProdFinEquiv ((sourceNCDataRecord (Y:=Y) (K:=K) h0 p.1.2).2,p.2))

/-- The noncoherent work-register encoding is injective. -/
theorem sourceNCWorkCode_injective {H Y K : Type} [Fintype Y] [Fintype K]
    (r : ℕ) (h0 : H) : Function.Injective (sourceNCWorkCode (Y:=Y) (K:=K) r h0) := by
  intro p t he
  have hf := congrArg (fun v => v.1.1) he
  have hd := congrArg (fun v => v.1.2) he
  have hr := finProdFinEquiv.injective (congrArg Prod.snd he)
  have hclock := congrArg Prod.snd hr
  have hrecord := congrArg Prod.fst hr
  have hdata := sourceNCDataRecord_injective (Y:=Y) (K:=K) h0 (Prod.ext hd hrecord)
  exact Prod.ext (Prod.ext hf hdata) hclock

/-- Encodes a garbage label as its record together with the zero clock value in the enlarged
clock register. -/
def sourceNCYClockCode {Y K : Type} [Fintype Y] [Fintype K] (r : ℕ) (hr : 0<r)
    (y : Y) : Fin ((Fintype.card Y+1+Fintype.card K)*r) :=
  finProdFinEquiv (sourceNCYRecord (K:=K) y,(⟨0,hr⟩ : Fin r))

/-- The garbage-label clock encoding is injective when the original clock size is positive. -/
theorem sourceNCYClockCode_injective {Y K : Type} [Fintype Y] [Fintype K]
    (r : ℕ) (hr : 0<r) : Function.Injective (sourceNCYClockCode (Y:=Y) (K:=K) r hr) := by
  intro y z he
  have h := congrArg (fun v => v.1.val) (finProdFinEquiv.injective he)
  apply (Fintype.equivFin Y).injective
  apply Fin.ext
  simp only [sourceNCYRecord,Fin.val_castAdd,Fin.val_succ] at h
  omega

/-- Embeds a garbage state into the zero query register, true tag, and encoded garbage-label
clock positions. -/
def sourceNCGarbageState {Y K : Type} [Fintype Y] [DecidableEq Y] [Fintype K]
    (n q r : ℕ) (hr : 0<r) (ξ : QState Y) :
    QState ((Fin (n+1)×Fin (q+1))×(Bool×Fin ((Fintype.card Y+1+Fintype.card K)*r))) :=
  TensorState (Qatlib.Foundations.PureStateMath.Ket (0,0)) (TensorState (Qatlib.Foundations.PureStateMath.Ket true)
    (sourceBasisFrame (sourceNCYClockCode (Y:=Y) (K:=K) r hr) *ᵥ ξ))

/-- The encoded noncoherent garbage state is normalized when its input state is normalized. -/
theorem sourceNCGarbageState_normalized {Y K : Type} [Fintype Y] [DecidableEq Y] [Fintype K]
    (n q r : ℕ) (hr : 0<r) (ξ : QState Y) (hξ : Normalized ξ) :
    Normalized (sourceNCGarbageState (K:=K) n q r hr ξ) := by
  have hF : (sourceBasisFrame (sourceNCYClockCode (Y:=Y) (K:=K) r hr))ᴴ*
      sourceBasisFrame (sourceNCYClockCode (Y:=Y) (K:=K) r hr)=(1 : Matrix Y Y ℂ) :=
    sourceBasisFrame_isometry _ (sourceNCYClockCode_injective (Y:=Y) (K:=K) r hr)
  apply normalized_tensorState (normalized_ket _)
  apply normalized_tensorState (normalized_ket _)
  apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.isometry_mulVec_norm hF,(normalized_iff_norm_toEuclidean_fromVec _).mp hξ]

/-- The basis frame of the left injection acts by extension by zero into the right summand. -/
theorem sourceBasisFrame_inl_action {H K : Type} [Fintype H] [DecidableEq H] [DecidableEq K]
    (ψ : QState H) : sourceBasisFrame (Sum.inl : H → H⊕K) *ᵥ ψ=Sum.elim ψ 0 := by
  ext p
  cases p <;> simp [sourceBasisFrame,Matrix.mulVec,dotProduct]

/-- The basis frame of the right injection acts by extension by zero into the left summand. -/
theorem sourceBasisFrame_inr_action {H K : Type} [Fintype K] [DecidableEq H] [DecidableEq K]
    (ψ : QState K) : sourceBasisFrame (Sum.inr : K → H⊕K) *ᵥ ψ=Sum.elim (0 : QState H) ψ := by
  ext p
  cases p <;> simp [sourceBasisFrame,Matrix.mulVec,dotProduct]

/-- The basis frame into the first nested data summand agrees with the clean embedding of the
twice extended state. -/
theorem sourceClean_nested_left_frame {H B K : Type} [Fintype H] [Fintype B]
    [DecidableEq H] [DecidableEq B] [DecidableEq K]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (fun h : H => ((0,0),((tag,Sum.inl (Sum.inl h)),(⟨0,hr⟩ : Fin r))) :
      H → SourceSpace n q ((H⊕B)⊕K) r) *ᵥ ψ=
      sourceClean n q r hr tag (Sum.elim (Sum.elim ψ 0) 0) := by
  ext p
  cases hd : p.2.1.2 with
  | inl d =>
    cases d with
    | inl h =>
      simp only [Matrix.mulVec,dotProduct,sourceBasisFrame]
      rw [Finset.sum_eq_single h]
      · simp [sourceClean,TensorState,Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff,hd]
        split_ifs <;> simp_all
      · intro t _ ht
        have hp : p≠((0,0),((tag,Sum.inl (Sum.inl t)),(⟨0,hr⟩ : Fin r))) := by
          intro he
          have hh := congrArg (fun v : SourceSpace n q ((H⊕B)⊕K) r => v.2.1.2) he
          (try dsimp only at hh)
          rw [hd] at hh
          exact ht (Sum.inl.inj (Sum.inl.inj hh)).symm
        simp [hp]
      · simp
    | inr d => simp [sourceBasisFrame,Matrix.mulVec,dotProduct,Prod.ext_iff,hd,sourceClean,TensorState]
  | inr d => simp [sourceBasisFrame,Matrix.mulVec,dotProduct,Prod.ext_iff,hd,sourceClean,TensorState]

/-- The basis frame into the second nested data summand agrees with its clean embedding after
extension by zero. -/
theorem sourceClean_nested_right_frame {H B K : Type} [Fintype H] [Fintype B]
    [DecidableEq H] [DecidableEq B] [DecidableEq K]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState B) :
    sourceBasisFrame (fun h : B => ((0,0),((tag,Sum.inl (Sum.inr h)),(⟨0,hr⟩ : Fin r))) :
      B → SourceSpace n q ((H⊕B)⊕K) r) *ᵥ ψ=
      sourceClean n q r hr tag (Sum.elim (Sum.elim 0 ψ) 0) := by
  ext p
  cases hd : p.2.1.2 with
  | inl d =>
    cases d with
    | inl d => simp [sourceBasisFrame,Matrix.mulVec,dotProduct,Prod.ext_iff,hd,sourceClean,TensorState]
    | inr h =>
      simp only [Matrix.mulVec,dotProduct,sourceBasisFrame]
      rw [Finset.sum_eq_single h]
      · simp [sourceClean,TensorState,Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff,hd]
        split_ifs <;> simp_all
      · intro t _ ht
        have hp : p≠((0,0),((tag,Sum.inl (Sum.inr t)),(⟨0,hr⟩ : Fin r))) := by
          intro he
          have hh := congrArg (fun v : SourceSpace n q ((H⊕B)⊕K) r => v.2.1.2) he
          (try dsimp only at hh)
          rw [hd] at hh
          exact ht (Sum.inr.inj (Sum.inl.inj hh)).symm
        simp [hp]
      · simp
  | inr d => simp [sourceBasisFrame,Matrix.mulVec,dotProduct,Prod.ext_iff,hd,sourceClean,TensorState]

/-- Embedding a tensor-product data and garbage state by the record frame yields the
corresponding `sourceGarbageTarget`. -/
theorem sourceRecord_frame_tensor {H Y : Type} [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] {r : ℕ} (n q : ℕ) (e : Y → Fin r)
    (σ : QState H) (ξ : QState Y) :
    sourceBasisFrame (fun p : H×Y => ((0,0),((true,p.1),e p.2)) :
      H×Y → SourceSpace n q H r) *ᵥ TensorState σ ξ=
      sourceGarbageTarget n q r σ (TensorState (Qatlib.Foundations.PureStateMath.Ket (0,0))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket true) (sourceBasisFrame e *ᵥ ξ))) := by
  ext p
  simp only [Matrix.mulVec,dotProduct,sourceBasisFrame,TensorState,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p.2.1.2]
  · by_cases ha : p.1=(0,0)
    · by_cases ht : p.2.1.1=true
      · simp only [sourceGarbageTarget,TensorState,Qatlib.Foundations.PureStateMath.Ket,ha,ht,if_true,one_mul,
          Matrix.mulVec,dotProduct,sourceBasisFrame,Prod.ext_iff,true_and]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> simp_all
      · simp [Prod.ext_iff,sourceGarbageTarget,TensorState,Qatlib.Foundations.PureStateMath.Ket,ht]
    · simp [Prod.ext_iff,sourceGarbageTarget,TensorState,Qatlib.Foundations.PureStateMath.Ket,ha]
  · intro h _ hh
    apply Finset.sum_eq_zero
    intro y _
    have hp : p≠((0,0),((true,h),e y)) := by
      intro he
      exact hh (congrArg (fun v : SourceSpace n q H r => v.2.1.2) he).symm
    simp [hp]
  · simp

/-- The noncoherent compilation frame sends a clean state in the first nested summand to the
native clean state with enlarged workspace. -/
theorem sourceNCFrame_clean {H Y K : Type} [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] [Fintype K] [DecidableEq K]
    (n q r : ℕ) (hr : 0<r) (h0 : H) (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (sourceWorkCode (sourceNCWorkCode (Y:=Y) (K:=K) r h0)) *ᵥ
      sourceClean n q r hr tag (Sum.elim (Sum.elim ψ (0 : QState (H×Y))) (0 : QState K))=
      sourceClean n q ((Fintype.card Y+1+Fintype.card K)*r) (by positivity) tag ψ := by
  rw [← sourceClean_nested_left_frame]
  rw [Matrix.mulVec_mulVec,sourceBasisFrame_comp]
  have he : sourceWorkCode (n:=n) (q:=q) (sourceNCWorkCode (Y:=Y) (K:=K) r h0) ∘
      (fun h : H => ((0,0),((tag,Sum.inl (Sum.inl h)),(⟨0,hr⟩ : Fin r))))=
      (fun h : H => ((0,0),((tag,h),
        (⟨0,by positivity⟩ : Fin ((Fintype.card Y+1+Fintype.card K)*r))))) := by
    funext h
    simp only [Function.comp_apply,sourceWorkCode,sourceNCWorkCode,sourceNCDataRecord]
    congr 1
  rw [he]
  exact sourceClean_basisFrame n q _ _ tag ψ

/-- The noncoherent compilation frame turns the tensor-product target in the nested data sum
into a native target with `sourceNCGarbageState`. -/
theorem sourceNCFrame_target {H Y K : Type} [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] [Fintype K] [DecidableEq K]
    (n q r : ℕ) (hr : 0<r) (h0 : H) (σ : QState H) (ξ : QState Y) :
    sourceBasisFrame (sourceWorkCode (sourceNCWorkCode (Y:=Y) (K:=K) r h0)) *ᵥ
      sourceClean n q r hr true (Sum.elim (Sum.elim (0 : QState H) (TensorState σ ξ)) (0 : QState K))=
      sourceGarbageTarget n q ((Fintype.card Y+1+Fintype.card K)*r) σ
        (sourceNCGarbageState (K:=K) n q r hr ξ) := by
  rw [← sourceClean_nested_right_frame]
  rw [Matrix.mulVec_mulVec,sourceBasisFrame_comp]
  have he : sourceWorkCode (n:=n) (q:=q) (sourceNCWorkCode (Y:=Y) (K:=K) r h0) ∘
      (fun p : H×Y => ((0,0),((true,Sum.inl (Sum.inr p)),(⟨0,hr⟩ : Fin r))))=
      (fun p : H×Y => ((0,0),((true,p.1),sourceNCYClockCode (K:=K) r hr p.2))) := by
    rfl
  rw [he]
  exact sourceRecord_frame_tensor n q (sourceNCYClockCode (K:=K) r hr) σ ξ

set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1000000

/-- Transfers an enlarged-space conversion word to a native noncoherent word with at most twice
the calls and overlap at least `sqrt (1 - ε)` against some normalized garbage state. -/
theorem sourceNC_program {X H Y K : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype Y] [DecidableEq Y] [Fintype K] [DecidableEq K] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ξ : X → QState Y)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) (hξ : ∀ x,Normalized (ξ x))
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (r : ℕ) (hr : 0<r)
    (C : SourceWord (SourceSpace n q ((H⊕(H×Y))⊕K) r))
    (hC : @sourceWordLegal (SourceSpace n q ((H⊕(H×Y))⊕K) r)
      (instFintypeProd _ _) (fun a b => instDecidableEqProd a b) C)
    (herr : ∀ x,‖toEuclidean_fromVec
      (@sourceWordMatrix (SourceSpace n q ((H⊕(H×Y))⊕K) r)
        (instFintypeProd _ _) (fun a b => instDecidableEqProd a b)
        (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (Sum.elim (Sum.elim (ρ x) 0) 0)-
      sourceClean n q r hr true (Sum.elim (Sum.elim 0 (TensorState (σ x) (ξ x))) 0))‖^2≤ε) :
    ∃ (s : ℕ) (hs : 0<s) (D : SourceWord (SourceSpace n q H s)),
      sourceWordLegal D∧sourceWordCalls D≤2*sourceWordCalls C∧∀ x,
      ∃ η : QState ((Fin (n+1)×Fin (q+1))×(Bool×Fin s)),Normalized η∧
        ‖∑ p,star ((sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
          sourceClean n q s hs false (ρ x)) p)*sourceGarbageTarget n q s (σ x) η p‖≥Real.sqrt (1-ε) := by
  let h0 : H := Classical.choice inferInstance
  let s := (Fintype.card Y+1+Fintype.card K)*r
  have hs : 0<s := by dsimp [s]; positivity
  let code := sourceNCWorkCode (Y:=Y) (K:=K) r h0
  have hcode : Function.Injective (sourceWorkCode (n:=n) (q:=q) code) :=
    sourceWorkCode_injective code (sourceNCWorkCode_injective (Y:=Y) (K:=K) r h0)
  let F : Matrix (SourceSpace n q H s) (SourceSpace n q ((H⊕(H×Y))⊕K) r) ℂ :=
    sourceBasisFrame (sourceWorkCode (n:=n) (q:=q) code)
  have hF : Fᴴ*F=(1 : Matrix (SourceSpace n q ((H⊕(H×Y))⊕K) r) _ ℂ) :=
    sourceBasisFrame_isometry _ hcode
  obtain ⟨D,hD,hcalls,hact⟩ := sourceWork_compile
    (A:=((Bool×((H⊕(H×Y))⊕K))×Fin r))
    (B:=((Bool×H)×Fin ((Fintype.card Y+1+Fintype.card K)*r)))
    input code (sourceNCWorkCode_injective (Y:=Y) (K:=K) r h0) C hC
  refine ⟨s,hs,D,hD,hcalls,?_⟩
  intro x
  let η := sourceNCGarbageState (K:=K) n q r hr (ξ x)
  have hη : Normalized η := sourceNCGarbageState_normalized (K:=K) n q r hr (ξ x) (hξ x)
  refine ⟨η,hη,?_⟩
  have hp := sourceNCFrame_clean (Y:=Y) (K:=K) n q r hr h0 false (ρ x)
  have ht := sourceNCFrame_target (K:=K) n q r hr h0 (σ x) (ξ x)
  change F *ᵥ _=sourceClean n q s hs false (ρ x) at hp
  change F *ᵥ _=sourceGarbageTarget n q s (σ x) η at ht
  have hd : ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
      sourceClean n q s hs false (ρ x)-sourceGarbageTarget n q s (σ x) η)‖^2≤ε := by
    rw [← hp,← ht,Matrix.mulVec_mulVec,hact x,← Matrix.mulVec_mulVec,← Matrix.mulVec_sub,
      Qatlib.Concepts.BlockEncoding.EncodingCore.isometry_mulVec_norm hF]
    exact herr x
  have htarget : Normalized (sourceGarbageTarget n q s (σ x) η) := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
    rw [← ht,Qatlib.Concepts.BlockEncoding.EncodingCore.isometry_mulVec_norm hF]
    exact (normalized_iff_norm_toEuclidean_fromVec _).mp (sourceClean_normalized n q r hr true _
      (sourceSum_left_normalized _ (sourceSum_right_normalized _
        (normalized_tensorState (hn x).2 (hξ x)))))
  have hout := normalized_applyGate (sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) D hD)
    (sourceClean_normalized n q s hs false (ρ x) (hn x).1)
  exact (source_overlap_of_distance _ _ hout htarget ε hε hε1 hd).trans
    (Complex.re_le_norm _)

/-- A noncoherent raw budget `W` at tolerance `ε⁴ / 16` yields a legal word with
target-and-garbage overlap at least `sqrt (1 - ε)` and the stated `17179869184 * W * log (1
/ ε) / ε²` call bound. See [LeeEtAl2011]. -/
theorem sourceNoncoherent_raw_budget_word {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε W : ℝ)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) (hε : 0<ε) (hε1 : ε≤1/3) (hW : 0≤W)
    (hQ : sourceQNoncoherentDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ)≤ENNReal.ofReal W) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),sourceWordLegal C∧
      (sourceWordCalls C : ℝ)≤17179869184*W*Real.log (1/ε)/ε^2∧∀ x,
      ∃ η : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
        Normalized η ∧ ‖∑ p,star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)) p)*sourceGarbageTarget n q r (σ x) η p‖≥Real.sqrt (1-ε) := by
  have hd (x : X) : gramStateMatrix ρ x x=1 := (normalized_iff_inner_self _).mp (hn x).1
  obtain ⟨T,K,hT,hK,hKdiag,hnear,hbudget⟩ := sourceQNoncoherentDelta_raw_attainment input (ε^4/16) W
    (gramStateMatrix ρ) (gramStateMatrix σ) (by positivity) hW (gramStateMatrix_posSemidef ρ) hd hQ
  obtain ⟨ξ,hξ,hKgram⟩ := sourcePSD_normalized_family K hK hKdiag
  let ρ0 : X → QState (H⊕(H×X)) := fun x => Sum.elim (ρ x) (0 : QState (H×X))
  let σ0 : X → QState (H⊕(H×X)) := fun x => Sum.elim (0 : QState H) (TensorState (σ x) (ξ x))
  have hn0 : ∀ x,Normalized (ρ0 x)∧Normalized (σ0 x) := by
    intro x
    exact ⟨sourceSum_left_normalized (H:=H) (K:=H×X) (ρ x) (hn x).1,
      sourceSum_right_normalized (H:=H) (K:=H×X) _
        (normalized_tensorState (hn x).2 (hξ x))⟩
  have hρ0gram : gramStateMatrix ρ0=gramStateMatrix ρ :=
    sourceSum_left_gram (H:=H) (K:=H×X) ρ
  have hσ0gram : gramStateMatrix σ0=gramStateMatrix σ ⊙ K := by
    rw [sourceSum_right_gram (H:=H) (K:=H×X),← hKgram]
    exact gramStateMatrix_qStateTensor σ ξ
  have hnear0 : sourceUnfiltered (T-gramStateMatrix σ0)≤ENNReal.ofReal (ε^4/16) := by
    rw [hσ0gram]
    exact hnear
  have hbudget0 : sourceRectValue (gramStateMatrix ρ0-T) (sourceAlphabetDelta input)≤ENNReal.ofReal W := by
    rw [hρ0gram]
    exact hbudget
  obtain ⟨Kpad,_hKpad,_hKeq,r,hr,C,hC,hcount,herr⟩ := sourceOptimized_public_program
    (J:=H⊕(H×X)) input ρ0 σ0 T W ε hn0 hW hε hε1 hT hnear0 hbudget0
  have hε1' : ε≤1 := by linarith
  have herr' : ∀ x,‖toEuclidean_fromVec
      (@sourceWordMatrix (SourceSpace n q ((H⊕(H×X))⊕Kpad) r)
        (instFintypeProd _ _) (fun a b => instDecidableEqProd a b)
        (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (Sum.elim (Sum.elim (ρ x) 0) 0)-
      sourceClean n q r hr true (Sum.elim (Sum.elim 0 (TensorState (σ x) (ξ x))) 0))‖^2≤ε := by
    intro x
    have hx := herr x
    dsimp [ρ0,σ0] at hx
    exact hx
  obtain ⟨s,hs,D,hD,hcalls,hout⟩ :=
      sourceNC_program (Y:=X) (K:=Kpad) input ρ σ ξ hn hξ ε hε.le hε1' r hr C hC herr'
  have he1 : ε≤1 := hε1'
  have hreal : (sourceWordCalls D : ℝ)≤17179869184*W*Real.log (1/ε)/ε^2 := by
    calc
      _ ≤ 2*(sourceWordCalls C : ℝ) := by exact_mod_cast hcalls
      _ ≤ 2*(8589934592*W*Real.log (1/ε)/ε^2) := mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = _ := by ring
  exact ⟨s,hs,D,hD,hreal,hout⟩

/-- A real upper bound on a source word's oracle-call count implies the corresponding
natural-number ceiling bound. -/
theorem sourceCall_le_ceil {n q : ℕ} {H : Type} {c : ℕ} {W ε : ℝ} {r : ℕ}
    {C : SourceWord (SourceSpace n q H r)}
    (h : (sourceWordCalls C : ℝ)≤c*W*Real.log (1/ε)/ε^2) :
    sourceWordCalls C ≤ Nat.ceil (c*W*Real.log (1/ε)/ε^2) := by
  have h2 : (sourceWordCalls C : ℝ) ≤ (Nat.ceil (c*W*Real.log (1/ε)/ε^2) : ℝ) :=
    h.trans (Nat.le_ceil _)
  exact_mod_cast h2

/-- Establishes the uniform coherent and noncoherent optimized returned-word guarantees of
`OptimizedReturnedWordConsumers`; see [Lee et al., Theorem 4.9][LeeEtAl2011]. -/
theorem optimizedReturnedWordConsumers : OptimizedReturnedWordConsumers := by
  refine ⟨17179869184,by norm_num,?_⟩
  intro X _ _ H _ _ _ n q input ρ σ ε W hn hε hε1 hW
  refine ⟨?_,?_⟩
  · intro hQ
    obtain ⟨r,hr,C,hC,hreal,hok⟩ := sourceCoherent_raw_budget_word input ρ σ ε W
      hn hε hε1 hW hQ
    exact ⟨r,hr,C,hC,sourceCall_le_ceil hreal,hok⟩
  · intro hQ
    obtain ⟨r,hr,C,hC,hreal,hok⟩ := sourceNoncoherent_raw_budget_word input ρ σ ε W
      hn hε hε1 hW hQ
    exact ⟨r,hr,C,hC,sourceCall_le_ceil hreal,hok⟩

end Qatlib.Concepts.QueryComplexity.StateConversion

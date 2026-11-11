/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesStat
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Mathlib.Tactic.LinearCombination
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Gram bounds and general output states

Relates alphabet query words and output overlaps to filtered and unfiltered Gram bounds. A legal
word has a filtered certificate with budget twice its query count, while sufficiently close
normalized states have a controlled unfiltered Gram difference [LeeEtAl2011].

Conversely, an unfiltered certificate yields a unitary approximation after finite padding and
hence a legal word with zero oracle calls.

## Main statements

* `sourceGram_word_cert`: bounds Gram change by twice the call count.
* `sourceGram_overlap_budget`: bounds unfiltered Gram distance using real overlaps.
* `sourceGram_free_word`: constructs a zero-query approximate conversion.
* `generalOutputGramBridges`: proves the combined Gram bridge specification.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators

/-- The total squared amplitude of a finite pure state, expressed as a sum of `Complex.normSq`. -/
private noncomputable def sourceGramMass {H : Type} [Fintype H] (ψ : QState H) : ℝ :=
  ∑ i, Complex.normSq (ψ i)

/-- The total squared amplitude `sourceGramMass ψ` is nonnegative. -/
private theorem sourceGramMass_nonneg {H : Type} [Fintype H] (ψ : QState H) : 0 ≤ sourceGramMass ψ :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (ψ i)

/-- A normalized state has total squared amplitude one. -/
private theorem sourceGramMass_normalized {H : Type} [Fintype H] {ψ : QState H}
    (hψ : Normalized ψ) : sourceGramMass ψ = 1 := by
  simpa only [sourceGramMass, Complex.normSq_eq_norm_sq] using! hψ

/-- Expands the total squared amplitude of a real linear combination using the two masses and
the real part of their inner product. -/
private theorem sourceGramMass_combination {H : Type} [Fintype H] (ψ φ : QState H) (a b : ℝ) :
    sourceGramMass (fun i => (a : ℂ) * ψ i + (b : ℂ) * φ i) =
      a ^ 2 * sourceGramMass ψ + b ^ 2 * sourceGramMass φ + 2 * a * b * (Qatlib.Foundations.PureStateMath.Inner ψ φ).re := by
  classical
  have he (z w : ℂ) : Complex.normSq ((a : ℂ) * z + (b : ℂ) * w) =
      a ^ 2 * Complex.normSq z + b ^ 2 * Complex.normSq w +
        2 * a * b * (star z * w).re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      RCLike.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp only [sourceGramMass, he, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show (Qatlib.Foundations.PureStateMath.Inner ψ φ).re = ∑ i, (star (ψ i) * φ i).re by
    simp [inner_apply, RCLike.star_def]]

/-- Expands the inner product of two real linear combinations into its four pairwise inner
products. -/
private theorem sourceGram_inner_combination {H : Type} [Fintype H]
    (ψ φ ξ η : QState H) (a b c d : ℝ) :
    Qatlib.Foundations.PureStateMath.Inner (fun i => (a : ℂ) * ψ i + (b : ℂ) * φ i)
      (fun i => (c : ℂ) * ξ i + (d : ℂ) * η i) =
      ((a * c : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner ψ ξ + ((a * d : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner ψ η +
      ((b * c : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner φ ξ + ((b * d : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner φ η := by
  classical
  simp only [inner_apply, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [show (∑ i, ((a : ℂ) * (starRingEnd ℂ) (ψ i) +
      (b : ℂ) * (starRingEnd ℂ) (φ i)) * ((c : ℂ) * ξ i + (d : ℂ) * η i)) =
      ∑ i, (((a : ℂ) * c) * ((starRingEnd ℂ) (ψ i) * ξ i) +
        ((a : ℂ) * d) * ((starRingEnd ℂ) (ψ i) * η i) +
        ((b : ℂ) * c) * ((starRingEnd ℂ) (φ i) * ξ i) +
        ((b : ℂ) * d) * ((starRingEnd ℂ) (φ i) * η i)) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Conjugating a pure state inner product exchanges its arguments. -/
private theorem sourceGram_inner_conj {H : Type} [Fintype H] (ψ φ : QState H) :
    star (Qatlib.Foundations.PureStateMath.Inner ψ φ) = Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  classical
  simp only [inner_apply, RCLike.star_def, map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The inner product of states on a sum type is the sum of the inner products on its two
components. -/
private theorem sourceGram_inner_sum {H K : Type} [Fintype H] [Fintype K]
    (a b : QState H) (p q : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (Sum.elim a p) (Sum.elim b q) = Qatlib.Foundations.PureStateMath.Inner a b + Qatlib.Foundations.PureStateMath.Inner p q := by
  classical
  simp only [inner_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

set_option maxHeartbeats 1000000 in

/-- A nonnegative unfiltered certificate budget `ε` between normalized state families yields a
unitary on a finite padded space with pointwise Euclidean error at most `Real.sqrt (2*ε)`. -/
theorem sourceGram_unitary_L2_of_cert {H X : Type}
    [Fintype H] [DecidableEq H] [Fintype X] [DecidableEq X]
    {ε : ℝ} (hε : 0 ≤ ε) (ρ σ : X → QState H)
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (hcert : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) ε) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (U : Matrix (H ⊕ K) (H ⊕ K) ℂ),
      U ∈ Matrix.unitaryGroup (H ⊕ K) ℂ ∧
      ∀ x, ‖toEuclidean_fromVec
        (ApplyGate U (Sum.elim (ρ x) (0 : K → ℂ))-
          Sum.elim (σ x) (0 : K → ℂ))‖ ≤ Real.sqrt (2*ε) := by
  classical
  rcases hcert with ⟨K, hK, u, v, hu, hv, huv⟩
  simp only [Fin.sum_univ_one, gramFilterAllOnes, one_mul] at hu hv huv
  let α := u 0
  let β := v 0
  have hab (x y : X) : Qatlib.Foundations.PureStateMath.Inner (α x) (β y) = Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) :=
    (huv x y).symm
  have hba (x y : X) : Qatlib.Foundations.PureStateMath.Inner (β x) (α y) = Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) := by
    rw [← sourceGram_inner_conj, hab]
    simp only [star_sub, sourceGram_inner_conj]
  have hdiag (x : X) : Qatlib.Foundations.PureStateMath.Inner (α x) (β x) = 0 := by
    rw [hab, (normalized_iff_inner_self _).mp (hρ x),
      (normalized_iff_inner_self _).mp (hσ x), sub_self]
  let p (x : X) (k : K) := ((1 / 2 : ℝ) : ℂ) * α x k + ((-1 / 2 : ℝ) : ℂ) * β x k
  let q (x : X) (k : K) := ((1 / 2 : ℝ) : ℂ) * α x k + ((1 / 2 : ℝ) : ℂ) * β x k
  have hp (x : X) : sourceGramMass (p x) ≤ ε / 2 := by
    have hm := sourceGramMass_combination (α x) (β x) (1 / 2) (-1 / 2)
    rw [hdiag, Complex.zero_re] at hm
    have hux : sourceGramMass (α x) ≤ ε := hu x
    have hvx : sourceGramMass (β x) ≤ ε := hv x
    change sourceGramMass (fun k => _) ≤ ε / 2
    nlinarith only [hm, hux, hvx]
  have hq (x : X) : sourceGramMass (q x) ≤ ε / 2 := by
    have hm := sourceGramMass_combination (α x) (β x) (1 / 2) (1 / 2)
    rw [hdiag, Complex.zero_re] at hm
    have hux : sourceGramMass (α x) ≤ ε := hu x
    have hvx : sourceGramMass (β x) ≤ ε := hv x
    change sourceGramMass (fun k => _) ≤ ε / 2
    nlinarith only [hm, hux, hvx]
  have hgram (x y : X) : Qatlib.Foundations.PureStateMath.Inner (q x) (q y) - Qatlib.Foundations.PureStateMath.Inner (p x) (p y) =
      Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) := by
    dsimp only [p, q]
    rw [sourceGram_inner_combination, sourceGram_inner_combination, hab, hba]
    norm_num
    ring
  let V : Matrix (H ⊕ K) X ℂ := fun i x => Sum.elim (ρ x) (p x) i
  let W : Matrix (H ⊕ K) X ℂ := fun i x => Sum.elim (σ x) (q x) i
  have hVW : Vᴴ * V = Wᴴ * W := by
    ext x y
    change Qatlib.Foundations.PureStateMath.Inner (Sum.elim (ρ x) (p x)) (Sum.elim (ρ y) (p y)) =
      Qatlib.Foundations.PureStateMath.Inner (Sum.elim (σ x) (q x)) (Sum.elim (σ y) (q y))
    rw [sourceGram_inner_sum, sourceGram_inner_sum]
    linear_combination -(hgram x y)
  obtain ⟨U,hU,hUV⟩ := gram_equal_actual_unitary_transport (H ⊕ K) X V W hVW
  refine ⟨K,hK,inferInstance,U,hU,?_⟩
  intro x
  let a : QState (H ⊕ K) := Sum.elim (ρ x) 0
  let b : QState (H ⊕ K) := Sum.elim (σ x) 0
  let pe : QState (H ⊕ K) := Sum.elim 0 (p x)
  let qe : QState (H ⊕ K) := Sum.elim 0 (q x)
  have hact : ApplyGate U (a+pe)=b+qe := by
    have he : a+pe=fun i => V i x := by
      ext i
      cases i <;> simp [a,pe,V]
    rw [he]
    ext i
    change (U*V) i x=_
    rw [hUV]
    cases i <;> simp [W,b,qe]
  have herr : ApplyGate U a-b=qe-ApplyGate U pe := by
    change U *ᵥ (a+pe)=b+qe at hact
    change U *ᵥ a-b=qe-U *ᵥ pe
    rw [Matrix.mulVec_add] at hact
    linear_combination hact
  have hpm : ‖toEuclidean_fromVec pe‖^2≤ε/2 := by
    rw [norm_toEuclidean_fromVec_sq]
    simpa [pe,sourceGramMass,Fintype.sum_sum_type,Complex.normSq_eq_norm_sq] using! hp x
  have hqm : ‖toEuclidean_fromVec qe‖^2≤ε/2 := by
    rw [norm_toEuclidean_fromVec_sq]
    simpa [qe,sourceGramMass,Fintype.sum_sum_type,Complex.normSq_eq_norm_sq] using! hq x
  have hn := norm_sub_le (toEuclidean_fromVec qe) (toEuclidean_fromVec (ApplyGate U pe))
  rw [norm_applyGate_of_mem_unitaryGroup hU] at hn
  have he : ‖toEuclidean_fromVec (qe-ApplyGate U pe)‖ ≤ Real.sqrt (2*ε) := by
    have hs := Real.sq_sqrt (show 0≤2*ε by positivity)
    have hnp := norm_nonneg (toEuclidean_fromVec pe)
    have hnq := norm_nonneg (toEuclidean_fromVec qe)
    have hdiff := sq_nonneg (‖toEuclidean_fromVec qe‖-‖toEuclidean_fromVec pe‖)
    have hsum : ‖toEuclidean_fromVec qe‖+‖toEuclidean_fromVec pe‖≤Real.sqrt (2*ε) := by
      nlinarith [Real.sqrt_nonneg (2*ε)]
    exact hn.trans hsum
  change ‖toEuclidean_fromVec (ApplyGate U a-b)‖≤_
  rw [herr]
  exact he

/-- For normalized states and `0 ≤ ε ≤ 1`, real overlaps at least `Real.sqrt (1-ε)` bound the
unfiltered Gram difference by `2*Real.sqrt (2*ε)`. -/
theorem sourceGram_overlap_budget {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (ρ σ : X → QState H) (ε : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hε : 0≤ε) (hε1 : ε≤1)
    (hov : ∀ x, (∑ p,star (ρ x p)*σ x p).re≥Real.sqrt (1-ε)) :
    sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ)≤ENNReal.ofReal (2*Real.sqrt (2*ε)) := by
  have hc := gramFilteredCert_of_realPart_overlap hε hε1 ρ σ
    (fun x => (hn x).1) (fun x => (hn x).2) hov
  unfold sourceUnfiltered
  rw [sourceSquareValue_eq]
  apply (filteredGamma2_le_of_gramFilteredCert hc).trans
  apply ENNReal.ofReal_le_ofReal
  have hh := Real.sqrt_le_sqrt (show ε≤2*ε by linarith)
  linarith

/-- Encodes an original state basis with a chosen Boolean tag and places auxiliary basis
elements in distinct nonzero workspace positions. -/
def sourceGramPaddingCode {H K : Type} [Fintype K] (h0 : H) (tag : Bool) :
    H ⊕ K → SourceSpace 0 0 H (Fintype.card K+1)
  | .inl h => ((0,0),((tag,h),0))
  | .inr k => ((0,0),((false,h0),((Fintype.equivFin K) k).succ))

/-- The tagged padding code for a state space and a finite auxiliary space is injective. -/
theorem sourceGramPaddingCode_injective {H K : Type} [Fintype K] (h0 : H) (tag : Bool) :
    Function.Injective (sourceGramPaddingCode (K:=K) h0 tag) := by
  intro p t he
  cases p with
  | inl p =>
    cases t with
    | inl t =>
      have hh := congrArg (fun v => v.2.1.2) he
      exact congrArg Sum.inl hh
    | inr t =>
      have hh := congrArg (fun v => v.2.2.val) he
      simp only [sourceGramPaddingCode,Fin.val_zero,Fin.val_succ] at hh
      omega
  | inr p =>
    cases t with
    | inl t =>
      have hh := congrArg (fun v => v.2.2.val) he
      simp only [sourceGramPaddingCode,Fin.val_zero,Fin.val_succ] at hh
      omega
    | inr t =>
      have hh := congrArg (fun v => v.2.2.val) he
      simp only [sourceGramPaddingCode,Fin.val_succ] at hh
      have hpt := (Fintype.equivFin K).injective (Fin.ext (Nat.add_right_cancel hh))
      exact congrArg Sum.inr hpt

/-- The standard basis frame associated with a basis map `e`. -/
def sourceGramFrame {S T : Type} [DecidableEq S] (e : T → S) : Matrix S T ℂ :=
  fun s t => if s=e t then 1 else 0

/-- An injective basis map gives an isometric standard basis frame. -/
theorem sourceGramFrame_isometry {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : T → S) (he : Function.Injective e) :
    (sourceGramFrame e)ᴴ*sourceGramFrame e=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,sourceGramFrame]
  rw [Finset.sum_eq_single (e i)]
  · simp [Matrix.one_apply,he.eq_iff]
  · intro s _ hs
    simp [hs]
  · simp

/-- The padding frame sends an original state with zero auxiliary component to its tagged clean
source embedding. -/
theorem sourceGramFrame_clean {H K : Type} [Fintype H] [DecidableEq H] [Fintype K]
    (h0 : H) (tag : Bool) (ψ : QState H) :
    sourceGramFrame (sourceGramPaddingCode (K:=K) h0 tag) *ᵥ Sum.elim ψ (0 : K → ℂ)=
      sourceClean 0 0 (Fintype.card K+1) (by omega) tag ψ := by
  ext p
  simp [sourceGramFrame,sourceGramPaddingCode,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    sourceClean,TensorState,Ket,Prod.ext_iff]
  rw [Finset.sum_eq_single p.2.1.2]
  · split_ifs <;> simp_all
  · intro h _ hh
    simp [Ne.symm hh]
  · simp

/-- For normalized states and nonnegative `δ`, an unfiltered Gram bound of `δ` yields a legal
zero-query word converting clean source states within Euclidean error `Real.sqrt (2*δ)`. -/
theorem sourceGram_free_word {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (ρ σ : X → QState H) (δ : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hδ : 0≤δ)
    (hval : sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ)≤ENNReal.ofReal δ) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace 0 0 H r)),
      sourceWordLegal C ∧ sourceWordCalls C=0 ∧ ∀ x,
      ‖toEuclidean_fromVec (sourceWordMatrix (1 : Matrix _ _ ℂ) C *ᵥ
        sourceClean 0 0 r hr false (ρ x)-sourceClean 0 0 r hr true (σ x))‖≤Real.sqrt (2*δ) := by
  have hc : gramFilteredCert (gramStateMatrix ρ-gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) δ := by
    unfold sourceUnfiltered at hval
    rw [sourceSquareValue_eq] at hval
    exact (filteredGamma2_budget_boundary X 1 _ _ δ hδ).mp hval
  obtain ⟨K,hK,hKeq,U,hU,herr⟩ := sourceGram_unitary_L2_of_cert hδ ρ σ
    (fun x => (hn x).1) (fun x => (hn x).2) hc
  let h0 : H := Classical.choice inferInstance
  let E0 := sourceGramFrame (sourceGramPaddingCode (K:=K) h0 false)
  let E1 := sourceGramFrame (sourceGramPaddingCode (K:=K) h0 true)
  have hE0 : E0ᴴ*E0=1 := sourceGramFrame_isometry _ (sourceGramPaddingCode_injective h0 false)
  have hE1 : E1ᴴ*E1=1 := sourceGramFrame_isometry _ (sourceGramPaddingCode_injective h0 true)
  have hu : Uᴴ*U=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  have hGram : E0ᴴ*E0=(E1*U)ᴴ*(E1*U) := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E1ᴴ E1,hE1,Matrix.one_mul,hu,hE0]
  obtain ⟨G,hG,hGE⟩ := gram_equal_actual_unitary_transport _ _ E0 (E1*U) hGram
  refine ⟨Fintype.card K+1,by omega,[.inl G],?_,rfl,?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hG
  · intro x
    simp only [sourceWordMatrix,List.map_cons,List.map_nil,List.reverse_singleton,
      List.prod_cons,List.prod_nil,Matrix.mul_one]
    rw [← sourceGramFrame_clean (K:=K) h0 false,← sourceGramFrame_clean (K:=K) h0 true]
    change ‖toEuclidean_fromVec (G *ᵥ (E0 *ᵥ Sum.elim (ρ x) 0)-E1 *ᵥ Sum.elim (σ x) 0)‖≤_
    rw [Matrix.mulVec_mulVec,hGE,← Matrix.mulVec_mulVec,← Matrix.mulVec_sub]
    rw [isometry_mulVec_norm hE1]
    exact herr x

/-- The alphabet oracle permutation that adds the padded input symbol to the answer register and
preserves the address and workspace. -/
def sourceGramAlphabetEquiv {X S : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    ((Fin (n+1) × Fin (q+1)) × S) ≃ ((Fin (n+1) × Fin (q+1)) × S) where
  toFun p := ((p.1.1,p.1.2+sourcePaddedSymbol input x p.1.1),p.2)
  invFun p := ((p.1.1,p.1.2-sourcePaddedSymbol input x p.1.1),p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The conjugate transpose of a permutation matrix is the permutation matrix of the inverse
equivalence. -/
theorem sourceGramPermutation_adjoint {S : Type} [DecidableEq S] (e : S ≃ S) :
    (permMatrix e)ᴴ=permMatrix e.symm := by
  ext i j
  simp [permMatrix,Matrix.conjTranspose_apply,Equiv.eq_symm_apply,eq_comm]

/-- A permutation matrix acts on amplitudes by composition with the inverse permutation. -/
theorem sourceGramPermutation_apply {S : Type} [Fintype S] [DecidableEq S]
    (e : S ≃ S) (ψ : QState S) (p : S) : (permMatrix e *ᵥ ψ) p=ψ (e.symm p) := by
  simp only [Matrix.mulVec,dotProduct,permMatrix,Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm p)]
  · simp
  · intro t _ ht
    have he : p≠e t := by intro h; exact ht ((e.symm_apply_eq.mpr h).symm)
    simp [he]
  · simp

/-- A forward alphabet oracle shifts the argument of each amplitude by the negative input
symbol, while its adjoint shifts by the positive input symbol. -/
theorem sourceGramAlphabet_apply {X S : Type} [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) (adj : Bool)
    (ψ : QState ((Fin (n+1) × Fin (q+1)) × S)) (j : Fin (n+1)) (a : Fin (q+1)) (w : S) :
    ((if adj then (sourceAlphabetOracle input x)ᴴ else sourceAlphabetOracle input x) *ᵥ ψ) ((j,a),w)=
      ψ ((j,a+(if adj then sourcePaddedSymbol input x j else -sourcePaddedSymbol input x j)),w) := by
  have he : sourceAlphabetOracle (W:=S) input x=permMatrix (sourceGramAlphabetEquiv input x) := rfl
  cases adj with
  | false =>
    rw [he]
    simpa only [Bool.false_eq_true,if_false,sourceGramAlphabetEquiv,Equiv.coe_fn_symm_mk,
      sub_eq_add_neg] using! sourceGramPermutation_apply (sourceGramAlphabetEquiv input x) ψ ((j,a),w)
  | true =>
    simp only [ite_true,he,sourceGramPermutation_adjoint]
    simpa only [Equiv.symm_symm,sourceGramAlphabetEquiv,Equiv.coe_fn_mk] using!
      sourceGramPermutation_apply (sourceGramAlphabetEquiv input x).symm ψ ((j,a),w)

/-- Simultaneously translating the alphabet coordinate of two state slices preserves their inner
product. -/
private theorem sourceGram_slice_shift_inner {S : Type} [Fintype S] {q : ℕ}
    (a b : QState (Fin (q+1) × S)) (s : Fin (q+1)) :
    Qatlib.Foundations.PureStateMath.Inner (fun p : Fin (q+1) × S => a (p.1+s,p.2)) (fun p => b (p.1+s,p.2))=Qatlib.Foundations.PureStateMath.Inner a b := by
  let e := Equiv.prodCongr (Equiv.addRight s) (Equiv.refl S)
  exact e.sum_comp (fun p => star (a p)*b p)

/-- Translating the alphabet coordinate preserves the sum of squared amplitudes of a state
slice. -/
private theorem sourceGram_slice_shift_mass {S : Type} [Fintype S] {q : ℕ}
    (a : QState (Fin (q+1) × S)) (s : Fin (q+1)) :
    (∑ p : Fin (q+1) × S,Complex.normSq (a (p.1+s,p.2)))=
      ∑ p,Complex.normSq (a p) := by
  let e := Equiv.prodCongr (Equiv.addRight s) (Equiv.refl S)
  exact e.sum_comp (fun p => Complex.normSq (a p))

/-- A forward or adjoint alphabet oracle call changes the Gram matrix of normalized states by a
filtered certificate with budget two. -/
theorem sourceGram_one_query_cert {X S : Type} [Fintype X] [DecidableEq X]
    [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (adj : Bool)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × S)) (hn : ∀ x, Normalized (ψ x)) :
    gramFilteredCert (gramStateMatrix ψ-gramStateMatrix
      (fun x => (if adj then (sourceAlphabetOracle input x)ᴴ else sourceAlphabetOracle input x) *ᵥ ψ x))
      (sourceAlphabetDelta input) 2 := by
  let a (j : Fin (n+1)) (x : X) (aw : Fin (q+1) × S) := ψ x ((j,aw.1),aw.2)
  let shift (j : Fin (n+1)) (x : X) :=
    if adj then sourcePaddedSymbol input x j else -sourcePaddedSymbol input x j
  let b (j : Fin (n+1)) (x : X) (aw : Fin (q+1) × S) := a j x (aw.1+shift j x,aw.2)
  have hm (x : X) : (∑ j : Fin (n+1),∑ aw,Complex.normSq (a j x aw))=1 := by
    simpa only [Normalized,Complex.normSq_eq_norm_sq,a,Fintype.sum_prod_type] using! hn x
  have ha (x : X) : (∑ j : Fin n,∑ aw,Complex.normSq (a j.castSucc x aw))≤1 := by
    have hmx := hm x
    rw [Fin.sum_univ_castSucc] at hmx
    have hh : 0≤∑ aw,Complex.normSq (a (Fin.last n) x aw) :=
      Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
    linarith
  have hb (j : Fin (n+1)) (x : X) :
      (∑ aw,Complex.normSq (b j x aw))=∑ aw,Complex.normSq (a j x aw) :=
    sourceGram_slice_shift_mass (a j x) (shift j x)
  refine ⟨(Fin (q+1) × S) ⊕ (Fin (q+1) × S),inferInstance,
    fun j x => Sum.elim (a j.castSucc x) (b j.castSucc x),
    fun j x => Sum.elim (a j.castSucc x) (fun aw => -b j.castSucc x aw),?_,?_,?_⟩
  · intro x
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,hb,Finset.sum_add_distrib]
    linarith [ha x]
  · intro x
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Complex.normSq_neg,hb,Finset.sum_add_distrib]
    linarith [ha x]
  · intro x y
    have hslot (j : Fin n) : sourceAlphabetDelta input j x y *
        (star (Sum.elim (a j.castSucc x) (b j.castSucc x)) ⬝ᵥ
          Sum.elim (a j.castSucc y) (fun aw => -b j.castSucc y aw)) =
        Qatlib.Foundations.PureStateMath.Inner (a j.castSucc x) (a j.castSucc y)-Qatlib.Foundations.PureStateMath.Inner (b j.castSucc x) (b j.castSucc y) := by
      simp only [dotProduct,Pi.star_apply,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
        mul_neg,Finset.sum_neg_distrib]
      by_cases he : input x j=input y j
      · have hshift : shift j.castSucc x=shift j.castSucc y := by
          simp only [shift,sourcePaddedSymbol,Fin.val_castSucc,dif_pos j.isLt]
          rw [he]
        have hi : Qatlib.Foundations.PureStateMath.Inner (b j.castSucc x) (b j.castSucc y)=Qatlib.Foundations.PureStateMath.Inner (a j.castSucc x) (a j.castSucc y) := by
          dsimp only [b]
          rw [← hshift]
          exact sourceGram_slice_shift_inner _ _ _
        simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,RCLike.star_def] at hi ⊢
        simp [sourceAlphabetDelta,he,hi]
      · simp [sourceAlphabetDelta,he,Qatlib.Foundations.PureStateMath.Inner,dotProduct,sub_eq_add_neg]
    simp_rw [hslot]
    have hlast (x : X) : b (Fin.last n) x=a (Fin.last n) x := by
      ext aw
      simp [b,shift,sourcePaddedSymbol]
    have hi : Qatlib.Foundations.PureStateMath.Inner (ψ x) (ψ y)=∑ j,Qatlib.Foundations.PureStateMath.Inner (a j x) (a j y) := by
      simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct,a,Fintype.sum_prod_type]
    have ho : Qatlib.Foundations.PureStateMath.Inner ((if adj then (sourceAlphabetOracle input x)ᴴ else sourceAlphabetOracle input x) *ᵥ ψ x)
        ((if adj then (sourceAlphabetOracle input y)ᴴ else sourceAlphabetOracle input y) *ᵥ ψ y)=
      ∑ j,Qatlib.Foundations.PureStateMath.Inner (b j x) (b j y) := by
      simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,Fintype.sum_prod_type,sourceGramAlphabet_apply,b,a,shift]
    change Qatlib.Foundations.PureStateMath.Inner (ψ x) (ψ y)-
      Qatlib.Foundations.PureStateMath.Inner ((if adj then (sourceAlphabetOracle input x)ᴴ else sourceAlphabetOracle input x) *ᵥ ψ x)
        ((if adj then (sourceAlphabetOracle input y)ᴴ else sourceAlphabetOracle input y) *ᵥ ψ y)=_
    rw [hi,ho,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc,hlast,hlast]
    rw [Finset.sum_sub_distrib]
    abel

/-- A legal alphabet oracle word changes the Gram matrix of normalized states by a filtered
certificate with budget twice its call count. -/
theorem sourceGram_word_cert {X S : Type} [Fintype X] [DecidableEq X]
    [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1))
    (C : SourceWord ((Fin (n+1) × Fin (q+1)) × S)) (hC : sourceWordLegal C)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × S)) (hn : ∀ x, Normalized (ψ x)) :
    gramFilteredCert (gramStateMatrix ψ-gramStateMatrix
      (fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ ψ x))
      (sourceAlphabetDelta input) (2*sourceWordCalls C) := by
  induction C generalizing ψ with
  | nil => simpa [sourceWordMatrix,sourceWordCalls] using!
      gramFilteredCert_zero (sourceAlphabetDelta input) (by norm_num : (0 : ℝ)≤0)
  | cons s C ih =>
    have ht : sourceWordLegal C := fun t ht => hC t (List.mem_cons_of_mem s ht)
    have hs := hC s List.mem_cons_self
    have hrun (x : X) : sourceWordMatrix (sourceAlphabetOracle input x) (s::C) *ᵥ ψ x=
        sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          (sourceWordMatrix (sourceAlphabetOracle input x) [s] *ᵥ ψ x) := by
      have he : sourceWordMatrix (sourceAlphabetOracle input x) (s::C)=
          sourceWordMatrix (sourceAlphabetOracle input x) C*sourceWordMatrix (sourceAlphabetOracle input x) [s] :=
        sourceWordMatrix_append (sourceAlphabetOracle input x) [s] C
      rw [he,← Matrix.mulVec_mulVec]
    cases s with
    | inl G =>
      have hg : gramStateMatrix (fun x => G *ᵥ ψ x)=gramStateMatrix ψ := by
        ext x y
        exact inner_applyGate hs (ψ x) (ψ y)
      have hi := ih ht (fun x => G *ᵥ ψ x) (fun x => normalized_applyGate hs (hn x))
      simp only [sourceWordMatrix,List.map_cons,List.map_nil,List.reverse_singleton,
        List.prod_cons,List.prod_nil,Matrix.mul_one] at hrun
      have he : (fun x => sourceWordMatrix (sourceAlphabetOracle input x) (.inl G::C) *ᵥ ψ x)=
          (fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ (G *ᵥ ψ x)) := by
        funext x
        exact hrun x
      rw [he]
      simpa only [hg,sourceWordCalls,List.countP_cons,Bool.false_eq_true,if_false,zero_add] using!
          hi
    | inr adj =>
      let O (x : X) : Matrix ((Fin (n+1) × Fin (q+1)) × S) ((Fin (n+1) × Fin (q+1)) × S) ℂ :=
        if adj then (sourceAlphabetOracle input x)ᴴ else sourceAlphabetOracle input x
      have hO (x : X) : O x ∈ Matrix.unitaryGroup _ ℂ := by
        cases adj with
        | false => exact sourceAlphabetOracle_unitary input x
        | true => simpa only [O,ite_true,Matrix.star_eq_conjTranspose] using!
            Unitary.star_mem (sourceAlphabetOracle_unitary (S:=S) input x)
      have hi := ih ht (fun x => O x *ᵥ ψ x) (fun x => normalized_applyGate (hO x) (hn x))
      have h := gramFilteredCert_add (sourceGram_one_query_cert input adj ψ hn) hi
      have he : (gramStateMatrix ψ-gramStateMatrix (fun x => O x *ᵥ ψ x))+
          (gramStateMatrix (fun x => O x *ᵥ ψ x)-gramStateMatrix
            (fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ (O x *ᵥ ψ x)))=
          gramStateMatrix ψ-gramStateMatrix
            (fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ (O x *ᵥ ψ x)) := by abel
      rw [he] at h
      have hb : (2 : ℝ)+2*sourceWordCalls C=2*(sourceWordCalls (.inr adj::C) : ℕ) := by
        simp only [sourceWordCalls,List.countP_cons,ite_true]
        push_cast
        ring
      rw [hb] at h
      simp only [sourceWordMatrix,List.map_cons,List.map_nil,List.reverse_singleton,
        List.prod_cons,List.prod_nil,Matrix.mul_one] at hrun
      have he : (fun x => sourceWordMatrix (sourceAlphabetOracle input x) (.inr adj::C) *ᵥ ψ x)=
          (fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ (O x *ᵥ ψ x)) := by
        funext x
        exact hrun x
      rw [he]
      exact h

/-- The clean source embedding with any fixed tag preserves the Gram matrix of a state family. -/
theorem sourceGram_clean_gram {X H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : X → QState H) :
    gramStateMatrix (fun x => sourceClean n q r hr tag (ψ x))=gramStateMatrix ψ := by
  ext x y
  simp [gramStateMatrix,Qatlib.Foundations.PureStateMath.Inner,dotProduct,sourceClean,TensorState,Ket,Fintype.sum_prod_type]

/-- Proves the query, overlap, and zero-query conversion bounds packaged by
`GeneralOutputGramBridges`, including the Gram estimates of [Lee et al., Lemmas 4.7 and
4.8][LeeEtAl2011]. -/
theorem generalOutputGramBridges : GeneralOutputGramBridges := by
  refine ⟨?_,?_,?_⟩
  · intro X H _ _ _ _ n q r hr input ρ C hρ hC
    have hc := sourceGram_word_cert input C hC
      (fun x => sourceClean n q r hr false (ρ x))
      (fun x => sourceClean_normalized n q r hr false (ρ x) (hρ x))
    rw [sourceGram_clean_gram] at hc
    have hb := filteredGamma2_le_of_gramFilteredCert hc
    rw [← sourceSquareValue_eq] at hb
    exact hb
  · intro X H _ _ _ _ ρ σ ε hn hε hε1 hov
    exact sourceGram_overlap_budget ρ σ ε hn hε hε1 hov
  · intro X H _ _ _ _ _ ρ σ δ hn hδ hval
    exact sourceGram_free_word ρ σ δ hn hδ hval

end Qatlib.Concepts.GramQueryCore.LowerBoundTools

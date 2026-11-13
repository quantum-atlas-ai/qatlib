/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.QueryDirectSumConsumerStat
import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState

/-!
# Direct sums of function evaluation queries

Coordinate lifts combine a single-instance adversary matrix into an adversary for independent
copies, with norm scaling linearly in the copy count. Prefix labels provide a matching
linear-budget construction for rectangular filtered certificates.

`queryDirectSumConsumer` combines these estimates with the function evaluation adversary
characterization to compare the query cost of `m` independent evaluations with `m` times the
single-instance cost. This realizes the direct-sum conclusion of [LeeEtAl2011].

## Main statements

* `sourceIndependentAdversary_norm`: linear norm scaling for the summed coordinate lifts.
* `sourceRectCert_independent`: linear-budget certificates for independent copies.
* `queryDirectSumConsumer`: complexity comparison and actual evaluation words.

## References

* [Lee et al., 2011, Corollary 5.3][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The matrix acting as `G` on coordinate `j` and as identity on all other coordinates of an
`m`-tuple. -/
def sourceCoordinateLift {X : Type} [DecidableEq X] {m : ℕ}
    (G : Matrix X X ℂ) (j : Fin m) : Matrix (Fin m → X) (Fin m → X) ℂ :=
  relabelGate (Equiv.funSplitAt j X).symm
    (sourceTensor G (1 : Matrix ({i : Fin m // i≠j} → X) ({i : Fin m // i≠j} → X) ℂ))

/-- The coordinate lift has entry `G (x j) (y j)` when all other coordinates agree, and zero
otherwise. -/
theorem sourceCoordinateLift_apply {X : Type} [DecidableEq X] {m : ℕ}
    (G : Matrix X X ℂ) (j : Fin m) (x y : Fin m → X) :
    sourceCoordinateLift G j x y=G (x j) (y j)*(if ∀ i, i≠j → x i=y i then 1 else 0) := by
  have he : (fun i : {i : Fin m // i≠j} => x i)=(fun i : {i : Fin m // i≠j} => y i) ↔ ∀ i, i≠j → x i=y i := by
    constructor
    · intro h i hi
      exact congrFun h ⟨i,hi⟩
    · intro h
      funext i
      exact h i i.property
  simp only [sourceCoordinateLift,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,sourceTensor,
    Equiv.symm_symm,Equiv.funSplitAt_apply,Matrix.one_apply,he]

/-- The operator norm of a coordinate lift is at most the operator norm of the original matrix. -/
theorem sourceCoordinateLift_norm_le {X : Type} [Fintype X] [DecidableEq X] {m : ℕ}
    (G : Matrix X X ℂ) (j : Fin m) : ‖sourceCoordinateLift G j‖ ≤ ‖G‖ := by
  rw [sourceCoordinateLift,l2_norm_relabelGate,sourceTensor_norm]
  exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg G)).trans (by simp)

/-- Lifting a Hermitian matrix to one coordinate preserves Hermitian symmetry. -/
theorem sourceCoordinateLift_isHermitian {X : Type} [Fintype X] [DecidableEq X] {m : ℕ}
    (G : Matrix X X ℂ) (hG : G.IsHermitian) (j : Fin m) : (sourceCoordinateLift G j).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply,sourceCoordinateLift_apply,star_mul,hG.apply]
  have he : (∀ i, i≠j → y i=x i) ↔ (∀ i, i≠j → x i=y i) := by
    constructor <;> intro h i hi <;> exact (h i hi).symm
  by_cases hr : ∀ i, i≠j → x i=y i <;> simp [he,hr]

/-- The adversary matrix for `m` independent inputs obtained by summing the coordinate lifts of
`G`. -/
def sourceIndependentAdversary {X : Type} [Fintype X] [DecidableEq X] (m : ℕ)
    (G : Matrix X X ℂ) : Matrix (Fin m → X) (Fin m → X) ℂ := ∑ j, sourceCoordinateLift G j

/-- Filtering the independent adversary at coordinate `(p,k)` gives the coordinate-`p` lift of
the single-instance adversary filtered at `k`. -/
theorem sourceIndependentAdversary_filter {X : Type} [Fintype X] [DecidableEq X]
    {n m q : ℕ} (input : X → Fin n → Fin (q+1)) (G : Matrix X X ℂ)
    (p : Fin m) (k : Fin n) :
    sourceIndependentAdversary m G ⊙ sourceAlphabetDelta (sourceIndependentInput input m) (finProdFinEquiv (p,k))=
      sourceCoordinateLift (G ⊙ sourceAlphabetDelta input k) p := by
  ext x y
  simp only [sourceIndependentAdversary,Matrix.hadamard_apply,Matrix.sum_apply,
    sourceCoordinateLift_apply,sourceAlphabetDelta,sourceIndependentInput,Equiv.symm_apply_apply,Finset.sum_mul]
  rw [Finset.sum_eq_single p]
  · ring
  · intro j _ hj
    by_cases he : ∀ i, i≠j → x i=y i
    · have hp := he p (Ne.symm hj)
      simp [hp]
    · simp [he]
  · simp

/-- The tensor power state splits at any coordinate into that state and the tensor power on the
remaining coordinates, up to relabeling. -/
theorem sourcePiState_split {X : Type} [Fintype X] [DecidableEq X] {m : ℕ}
    (u : QState X) (j : Fin m) :
    PiTensorState (fun _ : Fin m => u)=relabelState (Equiv.funSplitAt j X).symm
      (TensorState u (PiTensorState (fun _ : {i : Fin m // i≠j} => u))) := by
  ext x
  simp only [PiTensorState,relabelState,Function.comp_apply,Equiv.symm_symm,TensorState,Equiv.funSplitAt_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  exact Finset.prod_subtype (Finset.univ.erase j) (by simp) (fun i => u (x i))

/-- If `u` is an eigenvector of `G` with eigenvalue `c`, its tensor power is an eigenvector with
eigenvalue `c` of every coordinate lift. -/
theorem sourceCoordinateLift_eigen {X : Type} [Fintype X] [DecidableEq X] {m : ℕ}
    (G : Matrix X X ℂ) (u : QState X) (c : ℂ) (he : G*ᵥu=c • u) (j : Fin m) :
    sourceCoordinateLift G j *ᵥ PiTensorState (fun _ : Fin m => u)=
      c • PiTensorState (fun _ : Fin m => u) := by
  rw [sourceCoordinateLift,sourcePiState_split u j]
  change ApplyGate (relabelGate (Equiv.funSplitAt j X).symm (TensorGate G 1))
    (relabelState (Equiv.funSplitAt j X).symm (TensorState u (PiTensorState (fun _ : {i : Fin m // i≠j} => u))))=_
  rw [applyGate_relabelGate,applyGate_tensorGate,applyGate_one]
  change relabelState (Equiv.funSplitAt j X).symm (TensorState (G*ᵥu)
    (PiTensorState (fun _ : {i : Fin m // i≠j} => u)))=_
  rw [he]
  ext x
  simp only [relabelState,TensorState,Function.comp_apply,Pi.smul_apply]
  ring

/-- For Hermitian `G`, the norm of the sum of its `m` coordinate lifts is `m*‖G‖`. -/
theorem sourceIndependentAdversary_norm {X : Type} [Fintype X] [DecidableEq X]
    (m : ℕ) (G : Matrix X X ℂ) (hG : G.IsHermitian) :
    ‖sourceIndependentAdversary m G‖=(m : ℝ)*‖G‖ := by
  have hupper : ‖sourceIndependentAdversary m G‖ ≤ (m : ℝ)*‖G‖ := by
    calc
      _ ≤ ∑ j : Fin m, ‖sourceCoordinateLift G j‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin m, ‖G‖ := Finset.sum_le_sum fun j _ => sourceCoordinateLift_norm_le G j
      _ = _ := by simp
  apply le_antisymm hupper
  by_cases hz : ‖G‖=0
  · simp [hz]
  have hpos : 0<‖G‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  letI : Nonempty X := weightedAdv_nonempty_of_norm_pos G hpos
  obtain ⟨u,lam,hn,habs,he,_⟩ :=
      negative_adversary_extreme_eigenvector_and_start X Unit G (Ket ()) hG
      (by simp [Normalized,Ket])
  let w := PiTensorState (fun _ : Fin m => u)
  have hwn : Normalized w := normalized_piTensorState (fun _ => hn)
  have hw0 : w≠0 := by
    intro he0
    rw [he0] at hwn
    simp [Normalized] at hwn
  have hwe : sourceIndependentAdversary m G*ᵥw=(((m : ℝ)*lam : ℝ) : ℂ) • w := by
    ext x
    simp only [sourceIndependentAdversary,Matrix.mulVec,dotProduct,Matrix.sum_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    change (∑ j : Fin m, (sourceCoordinateLift G j *ᵥw) x)=_
    simp_rw [show ∀ j : Fin m, sourceCoordinateLift G j *ᵥw=(lam : ℂ) • w from fun j => sourceCoordinateLift_eigen G u (lam : ℂ) he j]
    simp [Pi.smul_apply,nsmul_eq_mul,mul_assoc]
  have hl := weightedAdv_eigenvalue_norm_le (sourceIndependentAdversary m G) w hw0 ((m : ℝ)*lam) hwe
  simpa only [abs_mul,abs_of_nonneg (show (0 : ℝ)≤(m : ℝ) from Nat.cast_nonneg m),habs] using! hl

set_option maxHeartbeats 1000000 in

/-- The adversary value for `m` independent evaluations is at least `m` times the
single-instance adversary value. -/
theorem sourceAdversary_independent_ge {X E : Type} [Fintype X] [DecidableEq X]
    [DecidableEq E] {n m q : ℕ} (input : X → Fin n → Fin (q+1)) (f : X → E) :
    (m : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f ≤
      sourceAdversary (sourceAlphabetDelta (sourceIndependentInput input m)) (fun xs => fun j => f (xs j)) := by
  unfold sourceAdversary
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro G
  let H := sourceIndependentAdversary m G.val
  have hH : H.IsHermitian := by
    unfold H sourceIndependentAdversary
    ext x y
    simp only [Matrix.conjTranspose_apply,Matrix.sum_apply,star_sum]
    exact Finset.sum_congr rfl fun j _ => (sourceCoordinateLift_isHermitian G.val G.property.1 j).apply x y
  have hreal (x y : Fin m → X) : (H x y).im=0 := by
    simp only [H,sourceIndependentAdversary,Matrix.sum_apply,Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [sourceCoordinateLift_apply]
    split_ifs <;> simp [G.property.2.1]
  have hzero (x y : Fin m → X) (he : (fun j => f (x j))=(fun j => f (y j))) : H x y=0 := by
    simp only [H,sourceIndependentAdversary,Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [sourceCoordinateLift_apply,G.property.2.2.1 _ _ (congrFun he j),zero_mul]
  have hf (k : Fin (m*n)) : ‖H ⊙ sourceAlphabetDelta (sourceIndependentInput input m) k‖ ≤ 1 := by
    rcases he : finProdFinEquiv.symm k with ⟨p,j⟩
    have hk : k=finProdFinEquiv (p,j) := by
      rw [← he]; exact (finProdFinEquiv.apply_symm_apply k).symm
    change ‖sourceIndependentAdversary m G.val ⊙ sourceAlphabetDelta
        (sourceIndependentInput input m) k‖ ≤ 1
    rw [hk,sourceIndependentAdversary_filter input G.val p j]
    exact (sourceCoordinateLift_norm_le _ p).trans (G.property.2.2.2 j)
  have hm : ENNReal.ofReal ‖H‖=(m : ℝ≥0∞)*ENNReal.ofReal ‖G.val‖ := by
    rw [sourceIndependentAdversary_norm m G.val G.property.1,ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast]
  rw [← hm]
  exact le_iSup_of_le ⟨H,hH,hreal,hzero,hf⟩ le_rfl

/-- The output tuple restricted to coordinates strictly before `j`, with `none` at all later
coordinates. -/
def sourceOutputPrefix {E : Type} {m : ℕ} (a : Fin m → E) (j : Fin m) : Fin m → Option E :=
  fun i => if i.val<j.val then some (a i) else none

/-- Two output prefixes at `j` agree exactly when the original tuples agree at every coordinate
before `j`. -/
theorem sourceOutputPrefix_eq_iff {E : Type} {m : ℕ} (a b : Fin m → E) (j : Fin m) :
    sourceOutputPrefix a j=sourceOutputPrefix b j ↔ ∀ i, i<j → a i=b i := by
  constructor
  · intro h i hi
    simpa [sourceOutputPrefix,show i.val<j.val from hi] using! congrFun h i
  · intro h
    funext i
    by_cases he : i<j
    · simp [sourceOutputPrefix,show i.val<j.val from he,h i he]
    · simp [sourceOutputPrefix,show ¬i.val<j.val from he]

/-- The sum of the indicators that `j` is the first differing coordinate equals zero for equal
tuples and one otherwise. -/
theorem sourceFirstDifference_sum {E : Type} [DecidableEq E] {m : ℕ} (a b : Fin m → E) :
    (∑ j : Fin m, (if sourceOutputPrefix a j=sourceOutputPrefix b j then
      (if a j=b j then (0 : ℂ) else 1) else 0))=if a=b then 0 else 1 := by
  by_cases he : a=b
  · subst b
    simp
  rw [if_neg he]
  let s := Finset.univ.filter (fun j : Fin m => a j≠b j)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := Function.ne_iff.mp he
    exact ⟨j,by simp [s,hj]⟩
  let j := s.min' hs
  have hj : a j≠b j := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hpre : ∀ i, i<j → a i=b i := by
    intro i hi
    by_contra hh
    have his : i ∈ s := by simp [s,hh]
    exact (not_le_of_gt hi) (Finset.min'_le s i his)
  rw [Finset.sum_eq_single j]
  · simp [(sourceOutputPrefix_eq_iff a b j).mpr hpre,hj]
  · intro i _ hij
    rcases lt_or_gt_of_ne hij with hi | hi
    · simp [hpre i hi]
    · have hp : sourceOutputPrefix a i≠sourceOutputPrefix b i := fun hh => hj ((sourceOutputPrefix_eq_iff a b i).mp hh j hi)
      simp [hp]
  · simp

/-- The sum of squared absolute values of a basis ket is one. -/
theorem sourceKet_normSq_sum {T : Type} [Fintype T] [DecidableEq T] (a : T) :
    (∑ t, Complex.normSq (Ket a t))=1 := by simp [Ket]

/-- The inner product of two basis kets is one when their labels agree and zero otherwise. -/
theorem sourceKet_inner {T : Type} [Fintype T] [DecidableEq T] (a b : T) :
    (∑ t, star (Ket a t)*Ket b t)=if a=b then (1 : ℂ) else 0 := by
  simp [Ket,eq_comm]

 /-- A rectangular filtered certificate of budget `w` for one evaluation yields a certificate of
 budget `m*w` for `m` independent evaluations. -/
 theorem sourceRectCert_independent {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n m q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) (w : ℝ)
    (hc : sourceRectCert n (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input) w) :
    sourceRectCert (m*n) (gramFunctionEvaluationMatrix (fun xs : Fin m → X => fun j => f (xs j)))
      (sourceAlphabetDelta (sourceIndependentInput input m)) ((m : ℝ)*w) := by
  obtain ⟨d,u,v,he,hu,hv⟩ := hc
  let pref (xs : Fin m → X) (j : Fin m) := sourceOutputPrefix (fun i => f (xs i)) j
  let u' (xs : Fin m → X) (l : Fin (m*n)) (p : Fin d × (Fin m → Option E)) :=
    u (xs (finProdFinEquiv.symm l).1) (finProdFinEquiv.symm l).2 p.1*Ket (pref xs (finProdFinEquiv.symm l).1) p.2
  let v' (xs : Fin m → X) (l : Fin (m*n)) (p : Fin d × (Fin m → Option E)) :=
    v (xs (finProdFinEquiv.symm l).1) (finProdFinEquiv.symm l).2 p.1*Ket (pref xs (finProdFinEquiv.symm l).1) p.2
  apply sourceRectCert_of_finiteWitness u' v'
  · intro xs ys
    rw [sourceFinProd_sum_apply (n := m) (m := n)]
    simp only [sourceAlphabetDelta,sourceIndependentInput,Equiv.symm_apply_apply,u',v',
      Fintype.sum_prod_type]
    have hinner (j : Fin m) (k : Fin n) :
        (∑ a : Fin d, ∑ b : Fin m → Option E,
          star (u (xs j) k a*Ket (pref xs j) b)*(v (ys j) k a*Ket (pref ys j) b))=
        (∑ a : Fin d, star (u (xs j) k a)*v (ys j) k a)*(if pref xs j=pref ys j then (1 : ℂ) else 0) := by
      rw [← sourceKet_inner,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [star_mul]
      ring
    have hsum : (∑ j : Fin m, ∑ k : Fin n,
        (if input (xs j) k=input (ys j) k then (0 : ℂ) else 1)*
        ((∑ a : Fin d, star (u (xs j) k a)*v (ys j) k a)*(if pref xs j=pref ys j then 1 else 0)))=
        ∑ j : Fin m, if pref xs j=pref ys j then gramFunctionEvaluationMatrix f (xs j) (ys j) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show (∑ k, (if input (xs j) k=input (ys j) k then (0 : ℂ) else 1)*
          ((∑ a, star (u (xs j) k a)*v (ys j) k a)*(if pref xs j=pref ys j then 1 else 0)))=
          (∑ k, sourceAlphabetDelta input k (xs j) (ys j)*∑ a, star (u (xs j) k a)*v (ys j) k a)*
            (if pref xs j=pref ys j then 1 else 0) by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; simp only
            [sourceAlphabetDelta]; ring]
      rw [← he]
      split_ifs <;> simp
    simp_rw [hinner]
    rw [hsum]
    simp only [pref,gramFunctionEvaluationMatrix]
    exact (sourceFirstDifference_sum (fun j => f (xs j)) (fun j => f (ys j))).symm
  · intro xs
    have hmass (j : Fin m) (k : Fin n) :
        (∑ p : Fin d × (Fin m → Option E), Complex.normSq (u (xs j) k p.1*Ket (pref xs j) p.2))=
        ‖toEuclidean_fromVec (u (xs j) k)‖^2 := by
      rw [Fintype.sum_prod_type]
      simp_rw [Complex.normSq_mul]
      simp only [← Finset.mul_sum,sourceKet_normSq_sum,mul_one]
      rw [norm_toEuclidean_fromVec_sq]
      simp only [Complex.normSq_eq_norm_sq]
    rw [sourceFinProd_sum_apply (n := m) (m := n)]
    simp only [u',Equiv.symm_apply_apply]
    simp_rw [hmass]
    exact (Finset.sum_le_sum fun j _ => hu (xs j)).trans (by simp)
  · intro ys
    have hmass (j : Fin m) (k : Fin n) :
        (∑ p : Fin d × (Fin m → Option E), Complex.normSq (v (ys j) k p.1*Ket (pref ys j) p.2))=
        ‖toEuclidean_fromVec (v (ys j) k)‖^2 := by
      rw [Fintype.sum_prod_type]
      simp_rw [Complex.normSq_mul]
      simp only [← Finset.mul_sum,sourceKet_normSq_sum,mul_one]
      rw [norm_toEuclidean_fromVec_sq]
      simp only [Complex.normSq_eq_norm_sq]
    rw [sourceFinProd_sum_apply (n := m) (m := n)]
    simp only [v',Equiv.symm_apply_apply]
    simp_rw [hmass]
    exact (Finset.sum_le_sum fun j _ => hv (ys j)).trans (by simp)

/-- The rectangular filtered value for `m` independent evaluations is at most `m` times the
single-instance value. -/
theorem sourceRectValue_independent_le {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n m q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) :
    sourceRectValue (gramFunctionEvaluationMatrix (fun xs : Fin m → X => fun j => f (xs j)))
      (sourceAlphabetDelta (sourceIndependentInput input m)) ≤
      (m : ℝ≥0∞)*sourceRectValue (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input) := by
  by_cases hm : m=0
  · subst m
    have hz : gramFunctionEvaluationMatrix (fun xs : Fin 0 → X => fun j => f (xs j))=0 := by
      ext xs ys
      simp [gramFunctionEvaluationMatrix,Subsingleton.elim (fun j => f (xs j)) (fun j => f (ys j))]
    simp [hz,sourceRectValue_zero]
  by_cases ht : sourceRectValue (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input)=⊤
  · have hmc : (m : ℝ≥0∞)≠0 := by exact_mod_cast hm
    rw [ht,ENNReal.mul_top hmc]
    exact le_top
  let w := (sourceRectValue (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input)).toReal
  have hc : sourceRectCert n (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input) w :=
    (sourceRectValue_budget_boundary _ _ w ENNReal.toReal_nonneg).mp
      (le_of_eq (ENNReal.ofReal_toReal ht).symm)
  have hh := sourceRectValue_le_of_cert (mul_nonneg (Nat.cast_nonneg m) ENNReal.toReal_nonneg)
    (sourceRectCert_independent (m := m) input f w hc)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast,ENNReal.ofReal_toReal ht] using! hh

/-- The rectangular filtered value of a function evaluation matrix is at most twice its general
adversary value. -/
theorem sourceRectValue_function_le_two_adversary {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) :
    sourceRectValue (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input) ≤
      2*sourceAdversary (sourceAlphabetDelta input) f := by
  have hh := (functionEvaluationNormSandwich X E n q input f).2.2.2
  have hc : ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ))) ≤ 2 := by
    calc
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by
        have hp : 0≤1/(Fintype.card E : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
        linarith)
      _ = 2 := by norm_num
  exact hh.trans (mul_le_mul hc le_rfl zero_le zero_le)

/-- The adversary value for `m` independent evaluations is at most `2*m` times the
single-instance adversary value. -/
theorem sourceAdversary_independent_le {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n m q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) :
    sourceAdversary (sourceAlphabetDelta (sourceIndependentInput input m)) (fun xs => fun j => f (xs j)) ≤
      2*(m : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f := by
  have hh := (functionEvaluationNormSandwich (Fin m → X) (Fin m → E) (m*n) q
    (sourceIndependentInput input m) (fun xs => fun j => f (xs j))).2.2.1
  calc
    _ ≤ sourceRectValue (gramFunctionEvaluationMatrix (fun xs : Fin m → X => fun j => f (xs j)))
        (sourceAlphabetDelta (sourceIndependentInput input m)) := hh
    _ ≤ (m : ℝ≥0∞)*sourceRectValue (gramFunctionEvaluationMatrix f) (sourceAlphabetDelta input) := sourceRectValue_independent_le input f
    _ ≤ (m : ℝ≥0∞)*(2*sourceAdversary (sourceAlphabetDelta input) f) :=
      mul_le_mul le_rfl (sourceRectValue_function_le_two_adversary input f) zero_le zero_le
    _ = _ := by ring

 /-- The function evaluation adversary characterization implies the direct-sum query comparison
 and its budgeted word construction. -/
 theorem queryDirectSumConsumer_of_functionEvaluation
    (h19 : FunctionEvaluationAdversaryAlgorithm) : QueryDirectSumConsumer := by
  obtain ⟨c,hc,h19⟩ := h19
  refine ⟨2*c*c,by positivity,?_⟩
  intro X E _ _ _ _ n m q input f
  (try dsimp only)
  let many := fun xs : Fin m → X => fun j => f (xs j)
  let allInput := sourceIndependentInput input m
  have hb := h19 X E n q input f
  have hp := h19 (Fin m → X) (Fin m → E) (m*n) q allInput many
  have hlow := sourceAdversary_independent_ge (m := m) input f
  have hup := sourceAdversary_independent_le (m := m) input f
  have hcc : (c : ℝ≥0∞)*(c : ℝ≥0∞) ≤ ((2*c*c : ℕ) : ℝ≥0∞) := by
    norm_cast
    nlinarith
  refine ⟨?_,?_,?_⟩
  · calc
      (m : ℝ≥0∞)*sourceFunctionQ input f ≤ (m : ℝ≥0∞)*((c : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f) :=
        mul_le_mul le_rfl hb.2.1 zero_le zero_le
      _ = (c : ℝ≥0∞)*((m : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f) := by ring
      _ ≤ (c : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta allInput) many := mul_le_mul le_rfl hlow zero_le zero_le
      _ ≤ (c : ℝ≥0∞)*((c : ℝ≥0∞)*sourceFunctionQ allInput many) := mul_le_mul le_rfl hp.1 zero_le zero_le
      _ ≤ ((2*c*c : ℕ) : ℝ≥0∞)*sourceFunctionQ allInput many := by
        rw [← mul_assoc]
        exact mul_le_mul hcc le_rfl zero_le zero_le
  · calc
      sourceFunctionQ allInput many ≤ (c : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta allInput) many := hp.2.1
      _ ≤ (c : ℝ≥0∞)*(2*(m : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f) := mul_le_mul le_rfl hup zero_le zero_le
      _ ≤ (c : ℝ≥0∞)*(2*(m : ℝ≥0∞)*((c : ℝ≥0∞)*sourceFunctionQ input f)) := by
        exact mul_le_mul le_rfl (mul_le_mul le_rfl hb.1 zero_le zero_le) zero_le zero_le
      _ = ((2*c*c : ℕ) : ℝ≥0∞)*(m : ℝ≥0∞)*sourceFunctionQ input f := by push_cast; ring
  · intro Q hQ hBQ
    have hbase : sourceAdversary (sourceAlphabetDelta input) f ≤ ENNReal.ofReal ((c : ℝ)*Q) := by
      calc
        _ ≤ (c : ℝ≥0∞)*sourceFunctionQ input f := hb.1
        _ ≤ (c : ℝ≥0∞)*ENNReal.ofReal Q := mul_le_mul le_rfl hBQ zero_le zero_le
        _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg c),ENNReal.ofReal_natCast]
    have hprod : sourceAdversary (sourceAlphabetDelta allInput) many ≤ ENNReal.ofReal (2*m*c*Q) := by
      calc
        _ ≤ 2*(m : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f := hup
        _ ≤ 2*(m : ℝ≥0∞)*ENNReal.ofReal ((c : ℝ)*Q) := mul_le_mul le_rfl hbase zero_le zero_le
        _ = ENNReal.ofReal (2*(m : ℝ))*ENNReal.ofReal ((c : ℝ)*Q) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_natCast]
          norm_num
        _ = ENNReal.ofReal ((2*(m : ℝ))*((c : ℝ)*Q)) :=
          (ENNReal.ofReal_mul (by positivity : (0 : ℝ)≤2*(m : ℝ))).symm
        _ = _ := by congr 1; ring
    obtain ⟨r,hr,C,hC,hCalls,hSuccess⟩ := hp.2.2 (2*m*c*Q) (by positivity) hprod
    refine ⟨r,hr,C,hC,?_,hSuccess⟩
    have he : (c : ℝ)*(2*m*c*Q)=((2*c*c : ℕ) : ℝ)*m*Q := by push_cast; ring
    simpa only [he] using! hCalls

/-- The query complexity of independent function evaluations scales linearly in the copy count
up to a universal constant, with actual budgeted evaluation words. This is the direct-sum
statement of [Lee et al., Corollary 5.3][LeeEtAl2011]. -/
theorem queryDirectSumConsumer : QueryDirectSumConsumer :=
  queryDirectSumConsumer_of_functionEvaluation functionEvaluationAdversaryAlgorithm

end Qatlib.Concepts.ConversionCore.WitnessCompile

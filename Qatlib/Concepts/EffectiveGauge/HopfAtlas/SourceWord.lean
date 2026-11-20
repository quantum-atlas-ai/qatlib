/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceJets
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-!
# Ordered coordinate derivatives of the original source

Higher source bounds are given for multi-indices, while the transport
majorants differentiate products in coordinate words. Smoothness justifies
permuting those words; the bridge is proved rather than strengthening the
input to bounds on an unknown lift or on full operator norms.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

section Words
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition of spatial Word Partial in the Hopf Atlas construction. -/
def spatialWordPartial (f : SpatialPoint → E) : List (Fin 3) → SpatialPoint → E
  | [] => f
  | i::w => fun x => fderiv ℝ (spatialWordPartial f w) x (EuclideanSpace.single i 1)

/-- Every finite iterated coordinate derivative of a smooth field into `E` is smooth. -/
theorem contDiff_spatialWordPartial (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f)
    (w : List (Fin 3)) : ContDiff ℝ ∞ (spatialWordPartial f w) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const

/-- Differentiating along the concatenation `w ++ w'` equals applying the derivatives of `w` to the
result of applying those of `w'`. -/
theorem spatialWordPartial_append (f : SpatialPoint → E) (w w' : List (Fin 3)) :
    spatialWordPartial f (w++w')=spatialWordPartial (spatialWordPartial f w') w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append,spatialWordPartial,ih]

/-- Iterated coordinate-word differentiation distributes over addition of two smooth fields. -/
theorem spatialWordPartial_add (f g : SpatialPoint → E) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (w : List (Fin 3)) :
    spatialWordPartial (fun x => f x+g x) w=
      fun x => spatialWordPartial f w x+spatialWordPartial g w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [spatialWordPartial,ih]
    have hd := ((contDiff_spatialWordPartial f hf w).differentiable (by simp) x).hasFDerivAt.add
      ((contDiff_spatialWordPartial g hg w).differentiable (by simp) x).hasFDerivAt
    change HasFDerivAt (fun y => spatialWordPartial f w y+spatialWordPartial g w y) _ x at hd
    rw [hd.fderiv]
    rfl

/-- Every coordinate-word derivative commutes with multiplication of a smooth field by a fixed real
scalar. -/
theorem spatialWordPartial_const_smul (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (w : List (Fin 3)) :
    spatialWordPartial (fun x => r • f x) w=fun x => r • spatialWordPartial f w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [spatialWordPartial,ih]
    have hd := ((contDiff_spatialWordPartial f hf w).differentiable (by simp) x).hasFDerivAt.const_smul r
    change HasFDerivAt (fun y => r • spatialWordPartial f w y) _ x at hd
    rw [hd.fderiv]
    rfl

/-- The empty derivative word returns the original constant field, and every nonempty word gives
the zero field. -/
theorem spatialWordPartial_const (c : E) (w : List (Fin 3)) :
    spatialWordPartial (fun _ : SpatialPoint => c) w=fun _ => if w=[] then c else 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [spatialWordPartial,ih,List.cons_ne_nil,ite_false]
    split_ifs <;> simp

/-- For a smooth field, differentiating its `j`-directional derivative along `i` is the second
Fréchet derivative evaluated on the coordinate axes in order `i, j`. -/
private theorem coordinateSecond (g : SpatialPoint → E) (hg : ContDiff ℝ ∞ g)
    (x : SpatialPoint) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)=
      fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hd := (((hg.fderiv_right (m := ∞) (by rfl)).differentiable (by simp) x).hasFDerivAt).clm_apply
    (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  rw [hd.fderiv]
  simp

/-- Interchanging the first two coordinate directions in a derivative word leaves the derivative of
a smooth field unchanged for any suffix word. -/
theorem spatialWordPartial_swap (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (w : List (Fin 3)) :
    spatialWordPartial f (i::j::w)=spatialWordPartial f (j::i::w) := by
  funext x
  have hg := contDiff_spatialWordPartial f hf w
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  have hsym := (hg.contDiffAt (x := x)).isSymmSndFDerivAt htwo
  simp only [spatialWordPartial]
  rw [coordinateSecond _ hg,coordinateSecond _ hg]
  exact hsym (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Permuting a derivative word leaves the iterated coordinate derivative of a smooth field
unchanged. -/
theorem spatialWordPartial_perm (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f)
    {w w' : List (Fin 3)} (h : w.Perm w') :
    spatialWordPartial f w=spatialWordPartial f w' := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [spatialWordPartial,ih]
  | swap i j w => exact spatialWordPartial_swap f hf j i w
  | trans h h' ih ih' => exact ih.trans ih'

end Words

/-- Definition of source Word Multi Index in the Hopf Atlas construction. -/
def sourceWordMultiIndex (w : List (Fin 3)) : Fin 3 → ℕ := fun i => w.count i

/-- Definition of source Canonical Word in the Hopf Atlas construction. -/
def sourceCanonicalWord (alpha : Fin 3 → ℕ) : List (Fin 3) :=
  List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2

/-- The canonical word associated to the multi-index `alpha` contains exactly `alpha i` copies of
direction `i`. -/
theorem sourceCanonicalWord_count (alpha : Fin 3 → ℕ) (i : Fin 3) :
    (sourceCanonicalWord alpha).count i=alpha i := by
  fin_cases i <;> simp [sourceCanonicalWord,List.count_replicate]

/-- The canonical derivative word has length equal to the sum of the three entries of its
multi-index. -/
theorem sourceCanonicalWord_length (alpha : Fin 3 → ℕ) :
    (sourceCanonicalWord alpha).length=∑ i : Fin 3, alpha i := by
  simp [sourceCanonicalWord,Fin.sum_univ_three,Nat.add_assoc]

/-- Sorting a derivative word by its direction counts gives a permutation of the original word. -/
theorem sourceWordMultiIndex_perm (w : List (Fin 3)) :
    w.Perm (sourceCanonicalWord (sourceWordMultiIndex w)) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [sourceCanonicalWord_count]
  rfl

/-- The sum of the three direction counts of any derivative word equals its length. -/
theorem sourceWordMultiIndex_order (w : List (Fin 3)) :
    (∑ i : Fin 3, sourceWordMultiIndex w i)=w.length := by
  rw [← sourceCanonicalWord_length]
  exact (sourceWordMultiIndex_perm w).length_eq.symm

/-- Definition of source Canonical Jet in the Hopf Atlas construction. -/
def sourceCanonicalJet (v : SpatialPoint → SpatialPoint) (alpha : Fin 3 → ℕ) : SpatialPoint → SpatialPoint :=
  spatialWordPartial v (sourceCanonicalWord alpha)

/-- The canonical jet of multi-index zero is the source field itself. -/
theorem sourceCanonicalJet_zero (v : SpatialPoint → SpatialPoint) : sourceCanonicalJet v 0=v := rfl

/-- The canonical jet for the first-order multi-index in direction `i` is the corresponding
physical partial derivative. -/
theorem sourceCanonicalJet_first (v : SpatialPoint → SpatialPoint) (i : Fin 3) :
    sourceCanonicalJet v (firstJetIndex i)=sourcePhysicalPartial v i := by
  fin_cases i <;> funext x <;>
    simp [sourceCanonicalJet,sourceCanonicalWord,firstJetIndex,spatialWordPartial,sourcePhysicalPartial]

/-- The original all-order jet promise, at legal physical rational points. -/
def OriginalAllJetAccurate (v : SpatialPoint → SpatialPoint) (source : RationalJetSource) : Prop :=
  ∀ (a : Fin 3 → ℚ) (alpha : Fin 3 → ℕ) (b : ℕ),
    (∀ i, 0 ≤ (a i : ℝ) ∧ (a i : ℝ) ≤ physicalPeriod) → ∀ j,
    |(source ((a,alpha),b) j : ℝ)-sourceCanonicalJet v alpha (rationalSpatialPoint a) j| ≤ (2^b : ℝ)⁻¹

/-- An all-orders accurate rational jet source is also accurate for the value and first derivative
queries. -/
theorem OriginalAllJetAccurate.first (v : SpatialPoint → SpatialPoint) (source : RationalJetSource)
    (hs : OriginalAllJetAccurate v source) : OriginalFirstJetAccurate v source := by
  intro a b ha
  constructor
  · simpa only [sourceCanonicalJet_zero] using hs a 0 b ha
  · intro i j
    simpa only [sourceCanonicalJet_first,sourcePhysicalPartial] using hs a (firstJetIndex i) b ha j

/-- Original bound-program accuracy for all positive total derivative orders.
Order zero is supplied by the separate unit-source hypothesis. -/
def OriginalPositiveJetBounds (v : SpatialPoint → SpatialPoint) (bounds : ℕ → ℚ) : Prop :=
  ∀ alpha : Fin 3 → ℕ, 0<(∑ i : Fin 3, alpha i) → ∀ x, InFundamentalCube x →
    ‖sourceCanonicalJet v alpha x‖ ≤ (bounds (∑ i : Fin 3, alpha i) : ℝ)

/-- Every ordered derivative inherits the very same total-order original
bound, by proved mixed-partial symmetry and exact multiplicities. -/
theorem OriginalPositiveJetBounds.word (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (w : List (Fin 3)) (hw : w≠[]) (x : SpatialPoint) (hx : InFundamentalCube x) :
    ‖spatialWordPartial v w x‖ ≤ (bounds w.length : ℝ) := by
  have hperm := sourceWordMultiIndex_perm w
  have hpos : 0<(∑ i : Fin 3, sourceWordMultiIndex w i) := by
    rw [sourceWordMultiIndex_order]
    exact List.length_pos_iff.mpr hw
  have h := hb (sourceWordMultiIndex w) hpos x hx
  rw [sourceCanonicalJet,← spatialWordPartial_perm v hv hperm,sourceWordMultiIndex_order] at h
  exact h

/-- The already consumed all-direction first/second contract is a genuine
projection of the original multi-index bound program. -/
theorem OriginalPositiveJetBounds.first_second (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) :
    SourceAllRescalingBounds v (bounds 1 : ℝ) (bounds 2 : ℝ) := by
  constructor
  · intro x hx i
    exact hb.word v hv bounds [i] (by simp) x hx
  · intro i x hx j
    exact hb.word v hv bounds [j,i] (by simp) x hx

/-- Positivity of a genuine norm upper bound follows from the original
promise at the origin; it need not be added as a new input assumption. -/
theorem OriginalPositiveJetBounds.nonneg (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) (n : ℕ) (hn : 0<n) :
    0 ≤ bounds n := by
  let w : List (Fin 3) := List.replicate n 0
  have hw : w≠[] := by
    apply List.length_pos_iff.mp
    simpa only [w,List.length_replicate] using hn
  have hzero : InFundamentalCube (0 : SpatialPoint) := fun _ => ⟨le_rfl,physicalPeriod_pos.le⟩
  have h := hb.word v hv bounds w hw 0 hzero
  have hR : (0 : ℝ) ≤ bounds n := by
    simpa only [w,List.length_replicate] using (norm_nonneg _).trans h
  exact Rat.cast_nonneg.mp hR

end Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootReturnedList

set_option backward.isDefEq.respectTransparency false

/-! The actual source-ordered returned list is paired with ALL inside roots
of the original target, with multiplicity. Counts refer to computed list/data
checks. This is still a typed decoded model, not a Python/fee theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays


/-- The finite construction in `NativeRootReturnedCompleteness` satisfies `filter_nsmul` under the displayed hypotheses. -/
private theorem filter_nsmul {α : Type} (p : α → Prop) [DecidablePred p]
    (n : ℕ) (s : Multiset α) : (n • s).filter p=n • s.filter p := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul,Multiset.filter_add,ih]

/-- The finite construction in `NativeRootReturnedCompleteness` satisfies `bind_nsmul` under the displayed hypotheses. -/
private theorem bind_nsmul {α β : Type} (s : Multiset α) (f : α → Multiset β)
    (n : ℕ) : s.bind (fun a => n • f a)=n • s.bind f := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul,Multiset.bind_add,ih]

/-- Construction for root Selected in the native root returned completeness model. -/
private def rootSelected {α : Type} {m : ℕ} (d e : Fin m → ℕ)
    (tag : (j : Fin m) → Fin (d j) → Bool)
    (w : (j : Fin m) → Fin (d j) → α) : List α :=
  (List.finRange m).flatMap (fun j => (List.finRange (d j)).flatMap
    (fun i => if tag j i=true then List.replicate (e j) (w j i) else []))

/-- The finite construction in `NativeRootReturnedCompleteness` satisfies `rootSelected_multiset` under the displayed hypotheses. -/
private theorem rootSelected_multiset {α : Type} {m : ℕ} (d e : Fin m → ℕ)
    (tag : (j : Fin m) → Fin (d j) → Bool)
    (w : (j : Fin m) → Fin (d j) → α)
    (p : α → Prop) [DecidablePred p]
    (hside : ∀ j i,p (w j i) ↔ tag j i=true) :
    (rootSelected d e tag w : Multiset α)=
      ((Finset.univ : Finset (Fin m)).val.bind
        (fun j => e j • (Finset.univ.val.map (w j)))).filter p := by
  unfold rootSelected
  rw [← Multiset.coe_bind,Multiset.filter_bind,Finset.val_univ_fin]
  apply Multiset.bind_congr
  intro j _
  rw [filter_nsmul,Multiset.filter_eq_bind,Multiset.bind_map,← bind_nsmul]
  rw [← Multiset.coe_bind,Finset.val_univ_fin]
  apply Multiset.bind_congr
  intro i _
  by_cases ht : tag j i=true
  · have hp := (hside j i).mpr ht
    simp [ht,hp,Multiset.nsmul_singleton,Multiset.coe_replicate]
  · have hp : ¬p (w j i) := fun h => ht ((hside j i).mp h)
    simp [ht,hp]

/-- The same emitted instruction list satisfies `rootSelected_length` with the displayed gate and query accounting. -/
private theorem rootSelected_length {α : Type} {m : Nat} (d e : Fin m → Nat)
    (tag : (j : Fin m) → Fin (d j) → Bool)
    (w : (j : Fin m) → Fin (d j) → α) :
    (rootSelected d e tag w).length=
      ((List.finRange m).map (fun j =>
        ((List.finRange (d j)).map
          (fun i => if tag j i=true then e j else 0)).sum)).sum := by
  unfold rootSelected
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  by_cases ht : tag j i=true
  · simp [ht]
  · simp [ht]

/-- Any coordinate map preserves source order and every exponent copy. -/
private theorem rootSelected_map {α β : Type} {m : Nat} (d e : Fin m → Nat)
    (tag : (j : Fin m) → Fin (d j) → Bool)
    (w : (j : Fin m) → Fin (d j) → α) (v : α → β) :
    (rootSelected d e tag w).map v=rootSelected d e tag (fun j i => v (w j i)) := by
  unfold rootSelected
  rw [List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  rw [List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  by_cases ht : tag j i=true
  · simp [ht]
  · simp [ht]

/-- Construction for root Selection Count in the native root returned completeness model. -/
private def rootSelectionCount {m : Nat} (d e : Fin m → Nat)
    (tag : (j : Fin m) → Fin (d j) → Bool) : Nat :=
  ((List.finRange m).map (fun j =>
    ((List.finRange (d j)).map (fun i => if tag j i=true then e j else 0)).sum)).sum

/-- The finite construction in `NativeRootReturnedCompleteness` satisfies `sum_map_add` under the displayed hypotheses. -/
private theorem sum_map_add {α : Type} (l : List α) (a b : α → Nat) :
    (l.map a).sum+(l.map b).sum=(l.map (fun i => a i+b i)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [← ih]
    simp only [Nat.add_assoc,Nat.add_left_comm]

/-- The finite construction in `NativeRootReturnedCompleteness` satisfies `sum_const` under the displayed hypotheses. -/
private theorem sum_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum=l.length*c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.succ_mul]
    exact Nat.add_comm _ _

/-- Positional inside plus complementary outside rootSelectionCount is the weighted degree. -/
private theorem rootSelectionCount_complement {m : Nat} (d e : Fin m → Nat)
    (tag : (j : Fin m) → Fin (d j) → Bool) :
    rootSelectionCount d e tag+rootSelectionCount d e (fun j i => !(tag j i))=
      ((List.finRange m).map (fun j => d j*e j)).sum := by
  unfold rootSelectionCount
  rw [sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  rw [sum_map_add]
  have h : ((List.finRange (d j)).map (fun i =>
      (if tag j i=true then e j else 0)+
      (if (!(tag j i))=true then e j else 0))).sum=
        ((List.finRange (d j)).map (fun _ => e j)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    cases tag j i <;> simp
  rw [h,sum_const,List.length_finRange]


/-- The finite construction in `NativeRootReturnedCompleteness` satisfies `sum_map_le` under the displayed hypotheses. -/
private theorem sum_map_le {α : Type} (l : List α) (a b : α → Nat)
    (h : ∀ i,a i≤b i) : (l.map a).sum≤(l.map b).sum := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    exact Nat.add_le_add (h x) ih

/-- Positive factor degrees bound the number of actual powering iterations. -/
private theorem rootExponent_loop_bound {m : Nat} (d e : Fin m → Nat)
    (hd : ∀ j,1≤d j) :
    ((List.finRange m).map e).sum≤
      ((List.finRange m).map (fun j => d j*e j)).sum := by
  apply sum_map_le
  intro j
  have h := Nat.mul_le_mul_right (e j) (hd j)
  simpa only [Nat.one_mul] using h

/-- Positive exponents bound the number of supplied disk positions. -/
private theorem rootDisk_loop_bound {m : Nat} (d e : Fin m → Nat)
    (he : ∀ j,1≤e j) :
    ((List.finRange m).map d).sum≤
      ((List.finRange m).map (fun j => d j*e j)).sum := by
  apply sum_map_le
  intro j
  have h := Nat.mul_le_mul_left (d j) (he j)
  simpa only [Nat.mul_one] using h

/-- Generated copies remain bounded even when returned coordinates collide. -/
private theorem rootSelected_copy_bound {α : Type} {m : Nat} (d e : Fin m → Nat)
    (tag : (j : Fin m) → Fin (d j) → Bool)
    (w : (j : Fin m) → Fin (d j) → α) :
    (rootSelected d e tag w).length≤
      ((List.finRange m).map (fun j => d j*e j)).sum := by
  rw [rootSelected_length]
  change rootSelectionCount d e tag≤_
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq (rootSelectionCount_complement d e tag))

/-- Applying an early numeric guard gives all three finite loop caps. This
does not establish interpreter or bit-operation costs. -/
private theorem rootEarly_guard_loop_caps {α : Type} {m : Nat} (d e : Fin m → Nat)
    (tag : (j : Fin m) → Fin (d j) → Bool)
    (w : (j : Fin m) → Fin (d j) → α) (N : Nat)
    (hd : ∀ j,1≤d j) (he : ∀ j,1≤e j)
    (hg : ((List.finRange m).map (fun j => d j*e j)).sum=N) :
    ((List.finRange m).map e).sum≤N ∧
    ((List.finRange m).map d).sum≤N ∧
    (rootSelected d e tag w).length≤N := by
  rw [← hg]
  exact ⟨rootExponent_loop_bound d e hd,rootDisk_loop_bound d e he,
    rootSelected_copy_bound d e tag w⟩


/-- Actual source inside multiplicity, independent of grid coordinate values. -/
def rootDecodedInsideCount {m : ℕ} (f : Fin m → RootIntegerFactorData) : ℕ :=
  rootSelectionCount (fun j => (f j).n+1) (fun j => (f j).exponent)
    (fun j i => rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i))

/-- Complementary outside increment count, used with successful classification. -/
def rootDecodedOutsideCount {m : ℕ} (f : Fin m → RootIntegerFactorData) : ℕ :=
  rootSelectionCount (fun j => (f j).n+1) (fun j => (f j).exponent)
    (fun j i => !(rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)))

/-- Construction for root Decoded Weighted Degree in the native root returned completeness model. -/
def rootDecodedWeightedDegree {m : ℕ} (f : Fin m → RootIntegerFactorData) : ℕ :=
  ((List.finRange m).map (fun j => ((f j).n+1)*(f j).exponent)).sum

/-- The same emitted instruction list satisfies `rootDecodedReturnList_length` with the displayed gate and query accounting. -/
theorem rootDecodedReturnList_length {m : ℕ} (f : Fin m → RootIntegerFactorData) (eta : ℚ) :
    (rootDecodedReturnList f eta).length=rootDecodedInsideCount f := by
  unfold rootDecodedReturnList
  rw [List.length_map]
  exact rootSelected_length _ _ _ _

/-- The same emitted instruction list satisfies `rootDecodedCounts_add` with the displayed gate and query accounting. -/
theorem rootDecodedCounts_add {m : ℕ} (f : Fin m → RootIntegerFactorData) :
    rootDecodedInsideCount f+rootDecodedOutsideCount f=rootDecodedWeightedDegree f :=
  rootSelectionCount_complement _ _ _

/-- This is the source's numeric outside guard from its early weighted-degree
check and final actual inside-list length check; no root count is supplied. -/
theorem rootDecodedOutsideCount_of_guards {m : ℕ} (target : List ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ) (k : ℕ)
    (hweighted : rootDecodedWeightedDegree f=(rootCanonicalCoefficients target).length-1)
    (hcount : (rootDecodedReturnList f eta).length=k) :
    rootDecodedOutsideCount f=(rootCanonicalCoefficients target).length-1-k := by
  have hi : rootDecodedInsideCount f=k := (rootDecodedReturnList_length f eta).symm.trans hcount
  have h := rootDecodedCounts_add f
  rw [hi,hweighted] at h
  exact Nat.eq_sub_of_add_eq (by simpa only [Nat.add_comm] using h)

/-- Source factor-power loop iterations, before polynomial arithmetic fees. -/
def rootDecodedExponentIterations {m : ℕ} (f : Fin m → RootIntegerFactorData) : ℕ :=
  ((List.finRange m).map (fun j => (f j).exponent)).sum

/-- Construction for root Decoded Disk Positions in the native root returned completeness model. -/
def rootDecodedDiskPositions {m : ℕ} (f : Fin m → RootIntegerFactorData) : ℕ :=
  ((List.finRange m).map (fun j => (f j).n+1)).sum

/-- The actual early degree guard bounds powering iterations, supplied disk
positions and generated coordinate copies. It is not a bit-fee theorem. -/
theorem rootDecodedEarlyGuard_loop_caps {m : ℕ} (target : List ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ)
    (he : ∀ j,0<(f j).exponent)
    (hweighted : rootDecodedWeightedDegree f=(rootCanonicalCoefficients target).length-1) :
    rootDecodedExponentIterations f≤(rootCanonicalCoefficients target).length-1 ∧
    rootDecodedDiskPositions f≤(rootCanonicalCoefficients target).length-1 ∧
    (rootDecodedReturnList f eta).length≤(rootCanonicalCoefficients target).length-1 := by
  have h := rootEarly_guard_loop_caps (fun j => (f j).n+1) (fun j => (f j).exponent)
    (fun j i => rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i))
    (fun j i => (⟨j,i⟩ : RootDecodedIndex f))
    ((rootCanonicalCoefficients target).length-1)
    (fun j => Nat.succ_le_succ (Nat.zero_le _)) he hweighted
  refine ⟨h.1,h.2.1,?_⟩
  simpa only [rootDecodedReturnList,rootDecodedReturnIndices,rootSelected,List.length_map] using h.2.2

/-- The mapped IDEAL roots, not approximate coordinates, form the filtered
original root multiset. Return coordinates may collide even within a factor. -/
theorem rootDecodedCertificate_returned (m : ℕ) (target : List ℤ) (content : ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ) (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) :
    ∃ zs : List ℂ,
      (zs : Multiset ℂ)=(rootIntegerListPolynomial target).roots.filter (fun z => ‖z‖<1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
        ‖rootRationalCoordinate q-z‖≤(eta : ℝ)) (rootDecodedReturnList f eta) zs := by
  obtain ⟨w,hw,hinj,hroots,hside,hreturn⟩ :=
    rootDecodedCertificate_sound m target content f eta hcontent hguard haccepted
  refine ⟨(rootDecodedReturnIndices f).map (fun s => w s.1 s.2),?_,
    rootDecodedReturnList_pairing f eta w hreturn⟩
  have hmap : (rootDecodedReturnIndices f).map (fun s => w s.1 s.2)=
      rootSelected (fun j => (f j).n+1) (fun j => (f j).exponent)
        (fun j i => rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)) w := by
    exact rootSelected_map _ _ _ (fun j i => (⟨j,i⟩ : RootDecodedIndex f))
      (fun s => w s.1 s.2)
  rw [hmap,hroots]
  have himage (j : Fin m) : (Finset.univ.image (w j)).val=Finset.univ.val.map (w j) :=
    Finset.image_val_of_injOn (fun _ _ _ _ h => hinj j h)
  have h := rootSelected_multiset (fun j => (f j).n+1) (fun j => (f j).exponent)
    (fun j i => rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)) w
    (fun z => ‖z‖<1) hside
  simpa only [himage] using h

/-- The caller's checked actual output length gives the ORIGINAL inside root
count with multiplicity; the count conclusion is never an input premise. -/
theorem rootDecodedCertificate_inside_count (m : ℕ) (target : List ℤ) (content : ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ) (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) (k : ℕ)
    (hcount : (rootDecodedReturnList f eta).length=k) :
    ((rootIntegerListPolynomial target).roots.filter (fun z => ‖z‖<1)).card=k := by
  obtain ⟨zs,hm,hpair⟩ :=
    rootDecodedCertificate_returned m target content f eta hcontent hguard haccepted
  rw [← hm]
  change zs.length=k
  exact hpair.length_eq.symm.trans hcount

/-- Successful classifications exclude unit-circle roots. The source's early
weighted degree and final returned-length guards therefore give the TRUE
strictly outside root count, including all factor exponent copies. -/
theorem rootDecodedCertificate_outside_count (m : ℕ) (target : List ℤ) (content : ℤ)
    (f : Fin m → RootIntegerFactorData) (eta : ℚ) (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) (k : ℕ)
    (hweighted : rootDecodedWeightedDegree f=(rootCanonicalCoefficients target).length-1)
    (hcount : (rootDecodedReturnList f eta).length=k) :
    ((rootIntegerListPolynomial target).roots.filter (fun z => 1<‖z‖)).card=
      (rootCanonicalCoefficients target).length-1-k := by
  obtain ⟨w,hw,hinj,hroots,hside,hreturn⟩ :=
    rootDecodedCertificate_sound m target content f eta hcontent hguard haccepted
  have houtside : ∀ j i,1<‖w j i‖ ↔
      (!(rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)))=true := by
    intro j i
    have hc := rootRationalDiskClassify_computed_tag ((f j).centers i)
      ((f j).radii i) ((haccepted j).classified i)
    cases hb : rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i) with
    | false =>
      have hs := rootRationalDiskClassify_root_side ((f j).centers i)
        ((f j).radii i) ((haccepted j).radius_pos i) (w j i) (hw j i).2 false
        (by simpa only [hb] using hc)
      simpa [hb] using hs
    | true =>
      have hn : ¬1<‖w j i‖ := not_lt_of_ge ((hside j i).mpr hb).le
      simpa [hb] using hn
  have himage (j : Fin m) : (Finset.univ.image (w j)).val=Finset.univ.val.map (w j) :=
    Finset.image_val_of_injOn (fun _ _ _ _ h => hinj j h)
  let zs := rootSelected (fun j => (f j).n+1) (fun j => (f j).exponent)
    (fun j i => !(rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i))) w
  have hm : (zs : Multiset ℂ)=
      (rootIntegerListPolynomial target).roots.filter (fun z => 1<‖z‖) := by
    rw [hroots]
    have h := rootSelected_multiset (fun j => (f j).n+1) (fun j => (f j).exponent)
      (fun j i => !(rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i))) w
      (fun z => 1<‖z‖) houtside
    simpa only [himage] using h
  have hl : zs.length=rootDecodedOutsideCount f := rootSelected_length _ _ _ _
  rw [← hm]
  change zs.length=(rootCanonicalCoefficients target).length-1-k
  exact hl.trans (rootDecodedOutsideCount_of_guards target f eta k hweighted hcount)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

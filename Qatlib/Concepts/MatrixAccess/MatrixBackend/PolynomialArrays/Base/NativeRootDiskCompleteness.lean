/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskInclusion

set_option backward.isDefEq.respectTransparency false

/-! Mathematical soundness of the actual disjoint-disk certificate pattern.
Squarefreeness is derived from degree-many disjoint included roots. The exact
factor-product stage retains multiplicities, including roots shared by factors.
This is not yet a Python interpreter or serialization theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open scoped BigOperators

/-- Degree-many distinct included roots exhaust the actual polynomial multiset;
there is no external simple-root or squarefree assumption. -/
theorem polynomial_roots_eq_degree_many_image (f : ℂ[X]) (hf0 : f≠0)
    (w : Fin f.natDegree → ℂ) (hroot : ∀ i,f.eval (w i)=0)
    (hinj : Function.Injective w) :
    f.roots=(Finset.univ.image w).val := by
  classical
  let S := Finset.univ.image w
  have hS : S.card=f.natDegree := by
    simp only [S,Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  have hsub : S⊆f.roots.toFinset := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf0).mpr (hroot i))
  have hcard : f.roots.card=f.natDegree :=
    (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
  have hle : f.roots.toFinset.card≤S.card := by
    rw [hS,←hcard]
    exact Multiset.toFinset_card_le _
  have heq : S=f.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hle
  have hnodup : f.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (by
    rw [←heq,hS,hcard])
  change f.roots=S.val
  rw [heq]
  exact (Multiset.dedup_eq_self.mpr hnodup).symm

/-- The coordinate tests and separation are the actual certificate predicates.
The resulting image is the entire root multiset, with each factor root simple. -/
theorem polynomial_disjoint_coordinate_disks_complete (f : ℂ[X])
    (hf : 0<f.natDegree) (c : Fin f.natDegree → ℂ) (r : Fin f.natDegree → ℝ)
    (hr : ∀ i,0<r i)
    (htest : ∀ i,(f.natDegree : ℝ)*(|(f.eval (c i)).re|+|(f.eval (c i)).im|)≤
      r i*max |(f.derivative.eval (c i)).re| |(f.derivative.eval (c i)).im|)
    (hsep : ∀ i j,i≠j → (r i+r j)^2<(c i-c j).re^2+(c i-c j).im^2) :
    ∃ w : Fin f.natDegree → ℂ,
      (∀ i,f.eval (w i)=0 ∧ ‖w i-c i‖≤r i) ∧
      Function.Injective w ∧ f.roots=(Finset.univ.image w).val := by
  classical
  choose w hw using fun i => polynomial_root_disk_of_coordinate_test
    f hf (c i) (r i) (hr i) (htest i)
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hne
    have hclose : ‖c i-c j‖≤r i+r j := by
      calc
        _≤‖c i-w i‖+‖w i-c j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _≤r i+r j := add_le_add (by simpa only [norm_sub_rev] using (hw i).2)
          (by rw [hij]; exact (hw j).2)
    have hsq : (r i+r j)^2<‖c i-c j‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      nlinarith [hsep i j hne]
    have hfar := (sq_lt_sq₀ (add_nonneg (hr i).le (hr j).le)
      (norm_nonneg (c i-c j))).mp hsq
    exact (not_lt_of_ge hclose) hfar
  have hf0 : f≠0 := by intro hz; simp [hz] at hf
  exact ⟨w,hw,hinj,polynomial_roots_eq_degree_many_image f hf0 w
    (fun i => (hw i).1) hinj⟩

/-- The exact factor identity recovers H's actual root MULTISET. No coprimality
between factors is needed, so shared roots add their true multiplicities. -/
theorem polynomial_factor_certificate_root_multiset {ι : Type} [DecidableEq ι]
    (S : Finset ι) (H : ℂ[X]) (content : ℂ) (f : ι → ℂ[X]) (e : ι → ℕ)
    (hcontent : content≠0) (hf : ∀ i∈S,f i≠0)
    (hproduct : H=C content*∏ i∈S,(f i)^e i) :
    H.roots=S.val.bind (fun i => e i • (f i).roots) := by
  rw [hproduct,Polynomial.roots_C_mul _ hcontent]
  rw [Polynomial.roots_prod _ S (Finset.prod_ne_zero_iff.mpr
    (fun i hi => pow_ne_zero _ (hf i hi)))]
  simp only [Polynomial.roots_pow]

/-- Uniform forward precision for the actual returned coordinates, using the
same componentwise rational upper bound as the standalone certificate checker. -/
theorem root_disk_returned_coordinate_error (c z q : ℂ) (r eta : ℝ)
    (hz : ‖z-c‖≤r)
    (hbudget : r+|(q-c).re|+|(q-c).im|≤eta) : ‖q-z‖≤eta := by
  calc
    _≤‖q-c‖+‖c-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(|(q-c).re|+|(q-c).im|)+r :=
      add_le_add (Complex.norm_le_abs_re_add_abs_im _) (by simpa only [norm_sub_rev] using hz)
    _≤eta := by linarith

/-- Exact squared-norm inside classification of the whole closed disk. -/
theorem root_disk_inside_of_squared_test (c z : ℂ) (r : ℝ)
    (hr : r<1) (hc : ‖c‖^2<(1-r)^2) (hz : ‖z-c‖≤r) : ‖z‖<1 := by
  have hcenter : ‖c‖<1-r := (sq_lt_sq₀ (norm_nonneg c) (by linarith)).mp hc
  have hnorm : ‖z‖≤r+‖c‖ := by
    calc
      _≤‖z-c‖+‖c‖ := norm_le_norm_sub_add _ _
      _≤r+‖c‖ := add_le_add hz le_rfl
  linarith

/-- Exact squared-norm outside classification of the whole closed disk. -/
theorem root_disk_outside_of_squared_test (c z : ℂ) (r : ℝ)
    (hr : 0≤r) (hc : (1+r)^2<‖c‖^2) (hz : ‖z-c‖≤r) : 1<‖z‖ := by
  have hcenter : 1+r<‖c‖ := (sq_lt_sq₀ (by linarith) (norm_nonneg c)).mp hc
  have hnorm : ‖c‖≤r+‖z‖ := by
    calc
      _≤‖c-z‖+‖z‖ := norm_le_norm_sub_add _ _
      _≤r+‖z‖ := add_le_add (by simpa only [norm_sub_rev] using hz) le_rfl
  linarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

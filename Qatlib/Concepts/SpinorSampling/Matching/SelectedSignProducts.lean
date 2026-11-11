/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.SignedRecordDecomposition
import Mathlib.Logic.Function.Basic

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Selected Sign Products

Selected Sign Products constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {I J X Y : Type} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Complete original `product_supported_on_injection` guarantee for `SelectedSignProducts`; all source hypotheses and output obligations are retained. -/
theorem product_supported_on_injection (f : I → J) (hf : Function.Injective f)
    (G : J → ℝ) (H : I → ℝ) (hon : ∀ i, G (f i)=H i)
    (hoff : ∀ j, (¬∃ i, f i=j) → G j=1) : (∏ j : J, G j)=∏ i : I, H i := by
  classical
  calc
    _ = ∏ j ∈ Finset.univ.image f, G j :=
      (Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => hoff j (by
        rintro ⟨i,hi⟩
        exact hj (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)))).symm
    _ = ∏ i : I, G (f i) := Finset.prod_image hf.injOn
    _ = _ := Finset.prod_congr rfl (fun i _ => hon i)

/-- Complete original `independent_product_along_injection` guarantee for `SelectedSignProducts`; all source hypotheses and output obligations are retained. -/
theorem independent_product_along_injection {n : ℕ} (p : Fin n → FinDist X)
    (f : I → Fin n) (hf : Function.Injective f) (H : I → X → ℝ) :
    (independentSampleLaw p).expect (fun ω => ∏ i : I, H i (ω (f i)))=
      ∏ i : I, (p (f i)).expect (H i) := by
  classical
  let G : Fin n → X → ℝ := Function.extend f H (fun _ _ => 1)
  have hon (i : I) : G (f i)=H i := hf.extend_apply H (fun _ _ => 1) i
  have hoff (j : Fin n) (hj : ¬∃ i, f i=j) : G j=(fun _ => 1) :=
    Function.extend_apply' H (fun _ _ => 1) j hj
  have hfun (ω : Fin n → X) : (∏ j : Fin n, G j (ω j))=∏ i : I, H i (ω (f i)) :=
    product_supported_on_injection f hf _ _ (fun i => by rw [hon i])
      (fun j hj => by rw [hoff j hj])
  calc
    _ = (independentSampleLaw p).expect (fun ω => ∏ j : Fin n, G j (ω j)) := by
      congr 1
      funext ω
      exact (hfun ω).symm
    _ = ∏ j : Fin n, (p j).expect (G j) := independentSampleLaw_expect_prod p G
    _ = _ := product_supported_on_injection f hf _ _ (fun i => by rw [hon i])
      (fun j hj => by rw [hoff j hj]; exact finite_expect_const _ _)

/-- Construction for product Law in the selected sign products model. -/
def productLaw (p : FinDist X) (q : FinDist Y) : FinDist (X × Y) where
  prob z := p.prob z.1*q.prob z.2
  nonneg z := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,q.sum_one,mul_one]
    exact p.sum_one

omit [DecidableEq X] [DecidableEq Y] in
/-- Complete original `product_law_expect` guarantee for `SelectedSignProducts`; all source hypotheses and output obligations are retained. -/
theorem product_law_expect (p : FinDist X) (q : FinDist Y) (F : X × Y → ℝ) :
    (productLaw p q).expect F=p.expect (fun x => q.expect (fun y => F (x,y))) := by
  unfold FinDist.expect productLaw
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Complete original `independent_selected_pair_product` guarantee for `SelectedSignProducts`; all source hypotheses and output obligations are retained. -/
theorem independent_selected_pair_product {n m : ℕ} (p : Fin n → FinDist X)
    (q : Fin m → FinDist Y) (f : I → Fin n) (g : I → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) (H : I → X → Y → ℝ) :
    (productLaw (independentSampleLaw p) (independentSampleLaw q)).expect
      (fun z => ∏ i : I, H i (z.1 (f i)) (z.2 (g i)))=
      ∏ i : I, (p (f i)).expect (fun x => (q (g i)).expect (H i x)) := by
  rw [product_law_expect]
  have hinner (ω : Fin n → X) :
      (independentSampleLaw q).expect (fun ν => ∏ i : I, H i (ω (f i)) (ν (g i)))=
        ∏ i : I, (q (g i)).expect (H i (ω (f i))) :=
    independent_product_along_injection q g hg _
  simp_rw [hinner]
  exact independent_product_along_injection p f hf (fun i x => (q (g i)).expect (H i x))

/-- Complete original `selected_sign_product_mgf` guarantee for `SelectedSignProducts`; all source hypotheses and output obligations are retained. -/
theorem selected_sign_product_mgf {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1)
    (f : I → Fin n) (g : I → Fin m) (hf : Function.Injective f) (hg : Function.Injective g)
    (t : ℝ) :
    (productLaw (independentSampleLaw (fun i => signLaw (a i) (ha i)))
      (independentSampleLaw (fun i => signLaw (b i) (hb i)))).expect
      (fun z => Real.exp (t*(∑ i : I,
        (recordSign (z.1 (f i))*recordSign (z.2 (g i))-a (f i)*b (g i))))) ≤
        Real.exp ((Fintype.card I : ℝ)*t^2/2) := by
  have hfun (ω : Fin n → Bool) (ν : Fin m → Bool) :
      Real.exp (t*(∑ i : I, (recordSign (ω (f i))*recordSign (ν (g i))-a (f i)*b (g i))))=
        ∏ i : I, Real.exp (t*(recordSign (ω (f i))*recordSign (ν (g i))-a (f i)*b (g i))) := by
    rw [Finset.mul_sum,Real.exp_sum]
  simp_rw [hfun]
  rw [independent_selected_pair_product (fun i => signLaw (a i) (ha i))
    (fun i => signLaw (b i) (hb i)) f g hf hg
    (fun i x y => Real.exp (t*(recordSign x*recordSign y-a (f i)*b (g i))))]
  have hbnd (i : I) : (signLaw (a (f i)) (ha (f i))).expect
      (fun x => (signLaw (b (g i)) (hb (g i))).expect
        (fun y => Real.exp (t*(recordSign x*recordSign y-a (f i)*b (g i))))) ≤ Real.exp (t^2/2) := by
    have h := paired_sign_mgf (a (f i)) (b (g i)) (ha (f i)) (hb (g i)) t
    change (productLaw (signLaw (a (f i)) (ha (f i))) (signLaw (b (g i)) (hb (g i)))).expect _ ≤ _ at h
    rw [product_law_expect] at h
    exact h
  apply (Finset.prod_le_prod₀ (fun i _ => finite_expect_nonneg _ _ (fun x =>
    finite_expect_nonneg _ _ (fun y => (Real.exp_pos _).le))) (fun i _ => hbnd i)).trans_eq
  simp only [Finset.prod_const,Finset.card_univ]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.independent_product_along_injection
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.product_law_expect
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.independent_selected_pair_product
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.selected_sign_product_mgf

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.FullCarrier
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.PairResampling

/-!
# Counting sums over coordinate replacements

Proves exact multiplicity identities for sums over one or two coordinate replacements in the
full tuple carrier. For distinct coordinates and functions vanishing when their values coincide,
`sum_pair_slices` restricts the replacement pair to distinct labels without changing the
resulting multiplicity. See [MagniezZur2026] for related background.

## Main statements

* `sum_update`: Summing a function over all tuples and all updates of one coordinate equals
  `Fintype.card L` times its sum over all tuples.
* `sum_pair_slices`: For distinct coordinates, if a function vanishes whenever their values
  coincide, its sum over all tuples and distinct replacement pairs equals `Fintype.card L *
  Fintype.card L` times its total sum.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]
omit [Fintype I] [Fintype L] in

/-- Updating the distinguished coordinate of a tuple reconstructed by `Equiv.piSplitAt` changes
only the distinguished value in that reconstruction. -/
theorem split_restore_update (i : I) (a x : L) (z : Off I i → L) :
    Function.update ((Equiv.piSplitAt i (fun _ : I => L)).symm (a,z)) i x=
      (Equiv.piSplitAt i (fun _ : I => L)).symm (x,z) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt,hj]

/-- Summing a function over all tuples and all updates of one coordinate equals `Fintype.card L`
times its sum over all tuples. -/
theorem sum_update {K : Type*} [AddCommMonoid K] (H : (I → L) → K) (i : I) :
    (∑ f : I → L,∑ x : L,H (Function.update f i x))=Fintype.card L • ∑ f : I → L,H f := by
  let e := Equiv.piSplitAt i (fun _ : I => L)
  have he := Fintype.sum_equiv e
    (fun f : I → L => ∑ x : L,H (Function.update f i x))
    (fun p : L × (Off I i → L) => ∑ x : L,H (Function.update (e.symm p) i x))
    (fun f => by (try dsimp only);rw [e.symm_apply_apply])
  rw [he,Fintype.sum_prod_type]
  dsimp only [e]
  simp_rw [split_restore_update]
  rw [Finset.sum_const]
  congr 1
  have hH :=
      Fintype.sum_equiv e H (fun p => H (e.symm p))
      (fun f => by (try dsimp only);rw [e.symm_apply_apply])
  rw [hH,Fintype.sum_prod_type,Finset.sum_comm]

/-- Summing a function over all tuples and both replacement labels for two successive coordinate
updates equals `Fintype.card L * Fintype.card L` times its total sum. -/
theorem sum_double_update {K : Type*} [AddCommMonoid K] (H : (I → L) → K) (i j : I) :
    (∑ f : I → L,∑ x : L,∑ y : L,H (Function.update (Function.update f i x) j y))=
      (Fintype.card L*Fintype.card L) • ∑ f : I → L,H f := by
  rw [sum_update (fun g => ∑ y : L,H (Function.update g j y)) i,sum_update H j,smul_smul]

/-- For distinct coordinates, if a function vanishes whenever their values coincide, its sum
over all tuples and distinct replacement pairs equals `Fintype.card L * Fintype.card L`
times its total sum. -/
theorem sum_pair_slices {K : Type*} [AddCommMonoid K] (H : (I → L) → K) (i j : I) (hij : i ≠ j)
    (hz : ∀ f : I → L,f i=f j → H f=0) :
    (∑ f : I → L,∑ p : Pair L,H (Function.update (Function.update f i p.val.1) j p.val.2))=
      (Fintype.card L*Fintype.card L) • ∑ f : I → L,H f := by
  have he (f : I → L) : (∑ p : Pair L,H (Function.update (Function.update f i p.val.1) j p.val.2))=
      ∑ x : L,∑ y : L,H (Function.update (Function.update f i x) j y) := by
    rw [sum_pair (fun x y => H (Function.update (Function.update f i x) j y))]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hxy : x ≠ y
    · rw [if_pos hxy]
    · rw [if_neg hxy]
      symm
      apply hz
      simp [Function.update_of_ne hij,not_ne_iff.mp hxy]
  simp_rw [he]
  exact sum_double_update H i j
end Qatlib.Foundations.MatrixGeometry.TupleDeletion

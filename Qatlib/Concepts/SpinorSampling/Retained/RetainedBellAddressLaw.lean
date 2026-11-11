/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellSparseTail
import Qatlib.Concepts.SpinorSampling.Matching.DenseMatchedMoments

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Address Law

Retained Bell Address Law constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

/-- Complete original `cohort_expect_cons` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem cohort_expect_cons {X : Type} [Fintype X] (p : FinDist X) (N : ℕ)
    (f : (Fin (N+1) → X) → ℝ) :
    (cohortLaw p (N+1)).expect f=
      p.expect (fun x => (cohortLaw p N).expect (fun η => f (Fin.cons x η))) :=
  product_expect_cons p f

/-- Complete original `cohort_expect_projection` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem cohort_expect_projection {X Y : Type} [Fintype X] [Fintype Y]
    (p : FinDist X) (q : FinDist Y) (π : X → Y)
    (hπ : ∀ f : Y → ℝ,p.expect (fun x => f (π x))=q.expect f)
    (N : ℕ) (f : (Fin N → Y) → ℝ) :
    (cohortLaw p N).expect (fun ω => f (π ∘ ω))=(cohortLaw q N).expect f := by
  induction N with
  | zero =>
    have hp (ω : Fin 0 → X) : f (π ∘ ω)=f (fun i => Fin.elim0 i) :=
      congrArg f (Subsingleton.elim _ _)
    have hq (ω : Fin 0 → Y) : f ω=f (fun i => Fin.elim0 i) :=
      congrArg f (Subsingleton.elim _ _)
    calc
      _ = (cohortLaw p 0).expect (fun _ => f (fun i => Fin.elim0 i)) := by
        apply congrArg (cohortLaw p 0).expect
        funext ω
        exact hp ω
      _ = f (fun i => Fin.elim0 i) := finite_expect_const _ _
      _ = (cohortLaw q 0).expect f := by
        symm
        calc
          _ = (cohortLaw q 0).expect (fun _ => f (fun i => Fin.elim0 i)) := by
            apply congrArg (cohortLaw q 0).expect
            funext ω
            exact hq ω
          _ = _ := finite_expect_const _ _
  | succ N ih =>
    rw [cohort_expect_cons,cohort_expect_cons]
    have hmap (x : X) (η : Fin N → X) :
        π ∘ Fin.cons x η=Fin.cons (π x) (π ∘ η) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hinner (x : X) :
        (cohortLaw p N).expect (fun η => f (π ∘ Fin.cons x η))=
          (cohortLaw q N).expect (fun η => f (Fin.cons (π x) η)) := by
      have hh := ih (fun η => f (Fin.cons (π x) η))
      simpa only [hmap] using hh
    simp_rw [hinner]
    exact hπ (fun y => (cohortLaw q N).expect (fun η => f (Fin.cons y η)))

/-- Complete original `uniform_expect_equiv` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem uniform_expect_equiv {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ Y) (f : Y → ℝ) :
    (uniformLaw X).expect (fun x => f (e x))=(uniformLaw Y).expect f := by
  have h := e.sum_comp (fun y => (1/(Fintype.card Y : ℝ))*f y)
  simpa only [FinDist.expect,uniformLaw,Fintype.card_congr e] using h

/-- Complete original `uniform_product_expect` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem uniform_product_expect {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X × Y → ℝ) :
    (productLaw (uniformLaw X) (uniformLaw Y)).expect f=(uniformLaw (X × Y)).expect f := by
  unfold FinDist.expect productLaw uniformLaw
  simp only [Fintype.card_prod,Nat.cast_mul,one_div_mul_one_div]

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Complete original `uniform_cohort_expect` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem uniform_cohort_expect (N : ℕ) (f : (Fin N → S) → ℝ) :
    (cohortLaw (uniformLaw S) N).expect f=(uniformLaw (Fin N → S)).expect f := by
  unfold FinDist.expect
  apply Finset.sum_congr rfl
  intro ω _
  rw [uniform_cohort_address_prob]
  simp [uniformLaw]

/-- Complete original `uniform_address_pair_expect` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem uniform_address_pair_expect (n m : ℕ) (f : (Fin n → S) × (Fin m → S) → ℝ) :
    (productLaw (cohortLaw (uniformLaw S) n) (cohortLaw (uniformLaw S) m)).expect f=
      (uniformLaw ((Fin n → S) × (Fin m → S))).expect f := by
  rw [product_law_expect]
  simp_rw [uniform_cohort_expect]
  rw [← product_law_expect,uniform_product_expect]

-- The only output being projected out is the actual measured native hit data.
/-- Complete original `observation_blocks_address_expect` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem observation_blocks_address_expect (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (n m K : ℕ)
    (f : (Fin K → (Fin n → S) × (Fin m → S)) → ℝ) :
    (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
      (fun ω => f (fun j => ((ω j).1,(ω j).2.1)))=
        (cohortLaw (productLaw (cohortLaw (uniformLaw S) n)
          (cohortLaw (uniformLaw S) m)) K).expect f := by
  exact cohort_expect_projection _ _ (fun ω : CohortObservation n m τ => (ω.1,ω.2.1))
    (cohort_observation_address_expect a b c k hz τ) K f

/-- Abbreviation for Address Index in the retained bell address law model. -/
abbrev AddressIndex (n m K : ℕ) := Fin K × (Fin n ⊕ Fin m)

/-- Construction for address Code in the retained bell address law model. -/
def addressCode (n m K : ℕ) : AddressIndex n m K ≃ Fin (Fintype.card (AddressIndex n m K)) :=
  Fintype.equivFin _

-- This equivalence relabels classical records for analysis. It is not a
/-- physical permutation of retained spins or an implementation of routing. -/
def addressBlocksEquiv (n m K : ℕ) :
    (Fin (Fintype.card (AddressIndex n m K)) → S) ≃
      (Fin K → (Fin n → S) × (Fin m → S)) where
  toFun A j := (fun i => A (addressCode n m K (j,Sum.inl i)),
    fun i => A (addressCode n m K (j,Sum.inr i)))
  invFun z t := match ((addressCode n m K).symm t).2 with
    | Sum.inl i => (z ((addressCode n m K).symm t).1).1 i
    | Sum.inr i => (z ((addressCode n m K).symm t).1).2 i
  left_inv A := by
    funext t
    rcases h : (addressCode n m K).symm t with ⟨j,v⟩
    cases v with
    | inl i =>
      simp only [h]
      exact congrArg A (by simpa only [h] using (addressCode n m K).apply_symm_apply t)
    | inr i =>
      simp only [h]
      exact congrArg A (by simpa only [h] using (addressCode n m K).apply_symm_apply t)
  right_inv z := by
    funext j
    apply Prod.ext <;> funext i <;> simp only [Equiv.symm_apply_apply]

/-- Complete original `grouped_address_expect_flat` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem grouped_address_expect_flat (n m K : ℕ)
    (f : (Fin K → (Fin n → S) × (Fin m → S)) → ℝ) :
    (cohortLaw (productLaw (cohortLaw (uniformLaw S) n)
      (cohortLaw (uniformLaw S) m)) K).expect f=
        (cohortLaw (uniformLaw S) (Fintype.card (AddressIndex n m K))).expect
          (fun A => f (addressBlocksEquiv n m K A)) := by
  calc
    _ = (cohortLaw (uniformLaw ((Fin n → S) × (Fin m → S))) K).expect f :=
      cohort_expect_projection _ _ id (uniform_address_pair_expect n m) K f
    _ = (uniformLaw (Fin K → (Fin n → S) × (Fin m → S))).expect f :=
      uniform_cohort_expect K f
    _ = (uniformLaw (Fin (Fintype.card (AddressIndex n m K)) → S)).expect
        (fun A => f (addressBlocksEquiv n m K A)) :=
      (uniform_expect_equiv (addressBlocksEquiv n m K) f).symm
    _ = _ := (uniform_cohort_expect _ _).symm

/-- Complete original `observation_blocks_flat_address_expect` guarantee for `RetainedBellAddressLaw`; all source hypotheses and output obligations are retained. -/
theorem observation_blocks_flat_address_expect (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (n m K : ℕ)
    (f : (Fin K → (Fin n → S) × (Fin m → S)) → ℝ) :
    (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
      (fun ω => f (fun j => ((ω j).1,(ω j).2.1)))=
        (cohortLaw (uniformLaw S) (Fintype.card (AddressIndex n m K))).expect
          (fun A => f (addressBlocksEquiv n m K A)) := by
  rw [observation_blocks_address_expect,grouped_address_expect_flat]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.cohort_expect_projection
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_blocks_address_expect
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.addressBlocksEquiv
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_blocks_flat_address_expect

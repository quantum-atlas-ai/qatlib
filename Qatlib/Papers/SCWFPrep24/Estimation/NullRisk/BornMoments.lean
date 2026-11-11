/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.SharedPhases
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PairCoefficients

set_option backward.isDefEq.respectTransparency false

/-!
# Born Moments

The actual full-address amplitude against one effect vector, for one shared hidden phase assignment.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The actual full-address amplitude against one effect vector, for one shared hidden phase assignment. -/
def phaseAmplitude {A : Type*} [Fintype A] (c : A → ℂ) (ω : A → Fin 4) : ℂ :=
  ∑ x, c x*fourthPhase (ω x)

/-- The complete phase prior average commutes with a finite sum. -/
theorem phaseMean_sum {A B : Type*} [Fintype A] [Fintype B]
    (f : B → (A → Fin 4) → ℂ) :
    phaseMean (fun ω => ∑ b, f b ω) = ∑ b, phaseMean (f b) := by
  unfold phaseMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A fixed complex coefficient factors out of the actual complete phase prior average. -/
theorem phaseMean_const_mul {A : Type*} [Fintype A] (c : ℂ)
    (f : (A → Fin 4) → ℂ) :
    phaseMean (fun ω => c*f ω) = c*phaseMean f := by
  unfold phaseMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Inclusion-exclusion retains the coincident-pair diagonal exactly once. -/
theorem pair_indicator_inclusion {A : Type*} [DecidableEq A] (x y u v : A) :
    (if (x=u ∧ y=v) ∨ (x=v ∧ y=u) then (1:ℂ) else 0) =
      (if x=u ∧ y=v then 1 else 0) + (if x=v ∧ y=u then 1 else 0) -
        (if (x=u ∧ y=v) ∧ (x=v ∧ y=u) then 1 else 0) := by
  by_cases ha : x=u ∧ y=v <;> by_cases hb : x=v ∧ y=u <;> simp [ha, hb]

/-- Four actual amplitude sums expand in their original address order. -/
theorem phaseAmplitude_product_expand {A : Type*} [Fintype A]
    (a b : A → ℂ) (ω : A → Fin 4) :
    (Complex.normSq (phaseAmplitude a ω) : ℂ) * Complex.normSq (phaseAmplitude b ω) =
      ∑ x, ∑ y, ∑ u, ∑ v,
        (a x*b y*star (a u)*star (b v)) *
          (fourthPhase (ω x)*fourthPhase (ω y)*star (fourthPhase (ω u))*star (fourthPhase (ω v))) := by
  have hn (z : ℂ) : (Complex.normSq z : ℂ) = z*star z := (Complex.mul_conj z).symm
  rw [hn, hn]
  have he : (phaseAmplitude a ω*star (phaseAmplitude a ω))*
      (phaseAmplitude b ω*star (phaseAmplitude b ω)) =
        phaseAmplitude a ω*phaseAmplitude b ω*star (phaseAmplitude a ω)*star (phaseAmplitude b ω) := by ring
  rw [he]
  simp only [phaseAmplitude, Complex.star_def, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  let addressReverse : (A × A × A × A) ≃ (A × A × A × A) :=
    { toFun := fun (p : A × A × A × A) => (p.2.2.2, p.2.2.1, p.2.1, p.1)
      invFun := fun (p : A × A × A × A) => (p.2.2.2, p.2.2.1, p.2.1, p.1)
      left_inv := by intro p; rcases p with ⟨x,y,u,v⟩; rfl
      right_inv := by intro p; rcases p with ⟨x,y,u,v⟩; rfl }
  have hs := Fintype.sum_equiv addressReverse
    (fun p => (a p.2.2.2*fourthPhase (ω p.2.2.2))*(b p.2.2.1*fourthPhase (ω p.2.2.1))*
      (star (a p.2.1)*star (fourthPhase (ω p.2.1)))*(star (b p.1)*star (fourthPhase (ω p.1))))
    (fun p => (a p.1*b p.2.1*star (a p.2.2.1)*star (b p.2.2.2))*
      (fourthPhase (ω p.1)*fourthPhase (ω p.2.1)*star (fourthPhase (ω p.2.2.1))*star (fourthPhase (ω p.2.2.2))))
    (by
      intro p
      rcases p with ⟨x,y,u,v⟩
      dsimp [addressReverse]
      ring)
  simpa only [Fintype.sum_prod_type, Complex.star_def] using hs

/-- The actual shared-phase full-address fourth moment contracts to the literal paired coefficient expression. -/
theorem phaseMean_full_address_product {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A → ℂ) :
    phaseMean (fun ω => (Complex.normSq (phaseAmplitude a ω) : ℂ) *
      Complex.normSq (phaseAmplitude b ω)) = (pairedCoefficientMass a b : ℂ) := by
  simp_rw [phaseAmplitude_product_expand, phaseMean_sum, phaseMean_const_mul,
    fourthPhase_shared_moment, pair_indicator_inclusion, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hdir : (∑ x, ∑ y, ∑ u, ∑ v,
      (a x*b y*star (a u)*star (b v))*(if x=u ∧ y=v then (1:ℂ) else 0)) =
        (∑ x, (Complex.normSq (a x) : ℂ))*(∑ x, (Complex.normSq (b x) : ℂ)) := by
    simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    simp only [Complex.star_def]
    ring
  have hswap : (∑ x, ∑ y, ∑ u, ∑ v,
      (a x*b y*star (a u)*star (b v))*(if x=v ∧ y=u then (1:ℂ) else 0)) =
        (Complex.normSq (∑ x, a x*star (b x)) : ℂ) := by
    simp only [ite_and, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
    rw [← Complex.mul_conj]
    simp only [Complex.star_def, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hdiag : (∑ x, ∑ y, ∑ u, ∑ v,
      (a x*b y*star (a u)*star (b v))*
        (if (x=u ∧ y=v) ∧ (x=v ∧ y=u) then (1:ℂ) else 0)) =
          ∑ x, (Complex.normSq (a x*b x) : ℂ) := by
    simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Complex.mul_conj]
    simp only [Complex.star_def, map_mul]
    ring
  rw [hdir, hswap, hdiag]
  simp only [pairedCoefficientMass, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_sum]

/-- The literal real probability average over one hidden fourth-root assignment shared by both copies. -/
def phaseMeanReal {A : Type*} [Fintype A] (f : (A → Fin 4) → ℝ) : ℝ :=
  ∑ ω : A → Fin 4, (∏ _ : A, (1/4 : ℝ))*f ω

/-- The real physical prior average is exactly the real cast of the complex character average. -/
theorem phaseMeanReal_cast {A : Type*} [Fintype A] (f : (A → Fin 4) → ℝ) :
    (phaseMeanReal f : ℂ) = phaseMean (fun ω => (f ω : ℂ)) := by
  simp [phaseMeanReal, phaseMean]

/-- The finite phase prior has nonnegative actual weights. -/
theorem phaseMeanReal_nonneg {A : Type*} [Fintype A] (f : (A → Fin 4) → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ phaseMeanReal f := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg
    (Finset.prod_nonneg fun _ _ => by norm_num) (hf ω)

/-- The actual finite phase prior is normalized, including an empty address set. -/
theorem phaseMeanReal_one {A : Type*} [Fintype A] :
    phaseMeanReal (fun _ : A → Fin 4 => 1) = 1 := by
  apply Complex.ofReal_injective
  rw [phaseMeanReal_cast]
  have h := phaseMean_prod (fun _ : A => fun _ : Fin 4 => (1 : ℂ))
  norm_num at h
  exact h

/-- The actual product Born numerator, averaged over the shared physical phase prior, equals the proved coefficient mass. -/
theorem phaseMeanReal_product {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A → ℂ) :
    phaseMeanReal (fun ω => Complex.normSq (phaseAmplitude a ω)*
      Complex.normSq (phaseAmplitude b ω)) = pairedCoefficientMass a b := by
  apply Complex.ofReal_injective
  rw [phaseMeanReal_cast]
  simp_rw [Complex.ofReal_mul]
  exact phaseMean_full_address_product a b

/-- The real product probability numerator retains the dimension-independent half-product lower bound for every full-address effect vector. -/
theorem phaseMeanReal_product_lower {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A → ℂ) :
    (∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x))/2 ≤
      phaseMeanReal (fun ω => Complex.normSq (phaseAmplitude a ω)*
        Complex.normSq (phaseAmplitude b ω)) := by
  rw [phaseMeanReal_product]
  exact pairedCoefficientMass_lower a b

/-- The same actual shared-phase numerator obeys the two-product upper bound for every full-address effect vector. -/
theorem phaseMeanReal_product_upper {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A → ℂ) :
    phaseMeanReal (fun ω => Complex.normSq (phaseAmplitude a ω)*
      Complex.normSq (phaseAmplitude b ω)) ≤
        2*(∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x)) := by
  rw [phaseMeanReal_product]
  exact pairedCoefficientMass_upper a b

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

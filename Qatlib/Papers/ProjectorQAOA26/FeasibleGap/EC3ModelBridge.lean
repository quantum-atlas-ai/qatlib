/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformSecular
import Qatlib.Papers.ProjectorQAOA26.StageStability.EC3FeasibleGap
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix BigOperators
open Qatlib.Papers.ProjectorQAOA26.StageStability

def ec3TensorAmplitude (m f : ℕ) (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool) : ℂ :=
  (((∏ c : Fin m, if ec3SatB (fun j => g (Sum.inl (c,j))) = true
      then (1/Real.sqrt 3 : ℝ) else 0) *
    ∏ _k : Fin f, (1/Real.sqrt 2 : ℝ)) : ℝ)

theorem ec3TensorAmplitude_feasible (m f : ℕ) (g : EC3Feasible m f) :
    ec3TensorAmplitude m f g.1 = uniformReference g := by
  have hcard : (Fintype.card (EC3Feasible m f):ℝ)=(3:ℝ)^m*(2:ℝ)^f := by
    rw [card_EC3Feasible]
    push_cast
    rfl
  have hsq : ((Real.sqrt 3)^m*(Real.sqrt 2)^f)^2=(Fintype.card (EC3Feasible m f):ℝ) := by
    rw [mul_pow,pow_right_comm (Real.sqrt 3) m 2,pow_right_comm (Real.sqrt 2) f 2,
      Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sq_sqrt (by norm_num : (0:ℝ)≤2),hcard]
  have hs : Real.sqrt (Fintype.card (EC3Feasible m f):ℝ)=(Real.sqrt 3)^m*(Real.sqrt 2)^f :=
    (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (by positivity)).mpr hsq.symm
  have hamp : (1/Real.sqrt 3)^m*(1/Real.sqrt 2)^f =
      1/Real.sqrt (Fintype.card (EC3Feasible m f):ℝ) := by
    rw [hs]
    simp only [one_div,inv_pow,mul_inv]
  unfold ec3TensorAmplitude uniformReference
  simp only [g.2,ite_true,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact congrArg Complex.ofReal hamp

theorem ec3TensorAmplitude_outside (m f : ℕ) (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool)
    (hg : ¬∀ c : Fin m, ec3SatB (fun j => g (Sum.inl (c,j)))=true) :
    ec3TensorAmplitude m f g=0 := by
  obtain ⟨c,hc⟩ := not_forall.mp hg
  have hp : (∏ c' : Fin m, if ec3SatB (fun j => g (Sum.inl (c',j)))=true
      then (1/Real.sqrt 3 : ℝ) else 0)=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp [hc]
  simp only [ec3TensorAmplitude,hp,zero_mul,Complex.ofReal_zero]

theorem ec3TensorAmplitude_normalized (m f : ℕ) : l2norm (ec3TensorAmplitude m f)=1 := by
  letI : Nonempty (EC3Feasible m f) :=
    ⟨(ec3FeasibleEquiv m f).symm ((fun _ => 0),(fun _ => false))⟩
  have hi : ∑ g : EC3Feasible m f,Complex.normSq (ec3TensorAmplitude m f g.1)=1 := by
    have hn := l2norm_sq (uniformReference (I := EC3Feasible m f))
    rw [uniformReference_normalized] at hn
    simpa only [ec3TensorAmplitude_feasible,one_pow] using! hn.symm
  have ho : ∑ g : {g : ((Fin m × Fin 3) ⊕ Fin f) → Bool //
      ¬∀ c : Fin m,ec3SatB (fun j => g (Sum.inl (c,j)))=true},
      Complex.normSq (ec3TensorAmplitude m f g.1)=0 := by
    apply Finset.sum_eq_zero
    intro g _
    rw [ec3TensorAmplitude_outside m f g.1 g.2,Complex.normSq_zero]
  have ht := Fintype.sum_subtype_add_sum_subtype
    (fun g : ((Fin m × Fin 3) ⊕ Fin f) → Bool => ∀ c : Fin m,ec3SatB (fun j => g (Sum.inl (c,j)))=true)
    (fun g => Complex.normSq (ec3TensorAmplitude m f g))
  change (∑ g : EC3Feasible m f,Complex.normSq (ec3TensorAmplitude m f g.1))+_=_ at ht
  rw [hi,ho,add_zero] at ht
  unfold l2norm
  rw [← ht,Real.sqrt_one]

theorem ec3Tensor_projector_restrict (m f : ℕ) (x y : EC3Feasible m f) :
    rankOne (ec3TensorAmplitude m f) x.1 y.1 = rankOne uniformReference x y := by
  simp only [rankOne,Matrix.vecMulVec_apply,Pi.star_apply,
    ec3TensorAmplitude_feasible m f x,ec3TensorAmplitude_feasible m f y]

def ec3PhysicalHamiltonian (m f : ℕ)
    (C : (((Fin m × Fin 3) ⊕ Fin f) → Bool) → ℝ) (s : ℝ) :
    Matrix ((((Fin m × Fin 3) ⊕ Fin f) → Bool)) ((((Fin m × Fin 3) ⊕ Fin f) → Bool)) ℂ :=
  (1-s) • (1-rankOne (ec3TensorAmplitude m f)) + s • Matrix.diagonal (fun g => (C g:ℂ))

theorem ec3PhysicalHamiltonian_compress (m f : ℕ)
    (C : (((Fin m × Fin 3) ⊕ Fin f) → Bool) → ℝ) (s : ℝ) :
    (ec3PhysicalHamiltonian m f C s).submatrix
        (fun g : EC3Feasible m f => g.1) (fun g : EC3Feasible m f => g.1) =
      hamiltonian (fun g : EC3Feasible m f => C g.1) s := by
  ext x y
  simp only [ec3PhysicalHamiltonian,Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,
    Matrix.sub_apply,ec3Tensor_projector_restrict,hamiltonian,uniformMixer,
    learnedGenerator,costOperator,Matrix.one_apply,Matrix.diagonal_apply,Subtype.val_inj]
  split_ifs <;> first | rfl | contradiction

theorem ec3PhysicalHamiltonian_no_leak (m f : ℕ)
    (C : (((Fin m × Fin 3) ⊕ Fin f) → Bool) → ℝ) (s : ℝ)
    (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool)
    (hg : ¬∀ c : Fin m,ec3SatB (fun j => g (Sum.inl (c,j)))=true)
    (x : EC3Feasible m f) : ec3PhysicalHamiltonian m f C s g x.1=0 := by
  have hne : g≠x.1 := by intro h;rw [h] at hg;exact hg x.2
  simp [ec3PhysicalHamiltonian,rankOne,Matrix.vecMulVec_apply,
    ec3TensorAmplitude_outside m f g hg,hne]

def ec3ClauseEnergy (v : Fin 3 → Bool) : ℝ :=
  ((∑ j : Fin 3, if v j then (1:ℝ) else 0)-1)^2

theorem ec3ClauseEnergy_nonneg (v : Fin 3 → Bool) : 0≤ec3ClauseEnergy v := sq_nonneg _

theorem ec3ClauseEnergy_cases (v : Fin 3 → Bool) :
    ec3ClauseEnergy v=0 ∨ ec3ClauseEnergy v=1 ∨ ec3ClauseEnergy v=4 := by
  unfold ec3ClauseEnergy
  rw [Fin.sum_univ_three]
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    norm_num [h0,h1,h2]

theorem ec3ClauseEnergy_zero_iff (v : Fin 3 → Bool) :
    ec3ClauseEnergy v=0 ↔ ec3SatB v=true := by
  unfold ec3ClauseEnergy
  rw [Fin.sum_univ_three]
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    norm_num [ec3SatB,h0,h1,h2]

def ec3Cost {m f : ℕ} (r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f))
    (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool) : ℝ :=
  ∑ c : Fin r,ec3ClauseEnergy (fun j => g (clauses c j))

theorem ec3Cost_zero_iff {m f : ℕ} (r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f))
    (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool) :
    ec3Cost r clauses g=0 ↔ ∀ c,ec3SatB (fun j => g (clauses c j))=true := by
  unfold ec3Cost
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => ec3ClauseEnergy_nonneg (fun j => g (clauses c j)))]
  simp only [Finset.mem_univ,forall_true_left,ec3ClauseEnergy_zero_iff]

theorem ec3Cost_le {m f : ℕ} (r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f))
    (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool) : ec3Cost r clauses g≤4*(r:ℝ) := by
  calc _ ≤ ∑ _c : Fin r,(4:ℝ) := by
         apply Finset.sum_le_sum
         intro c _
         rcases ec3ClauseEnergy_cases (fun j => g (clauses c j)) with h|h|h <;> linarith
       _ = 4*(r:ℝ) := by simp [mul_comm]

theorem ec3Cost_unique_bounds {m f : ℕ} (r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f)) (zero : EC3Feasible m f)
    (hunique : ∀ g : EC3Feasible m f,
      (∀ c,ec3SatB (fun j => g.1 (clauses c j))=true) ↔ g=zero) :
    ec3Cost r clauses zero.1=0 ∧
      ∀ g : EC3Feasible m f,g≠zero → 1≤ec3Cost r clauses g.1 ∧ ec3Cost r clauses g.1≤4*(r:ℝ) := by
  refine ⟨(ec3Cost_zero_iff r clauses zero.1).mpr ((hunique zero).mpr rfl),?_⟩
  intro g hg
  have hn : ¬∀ c,ec3SatB (fun j => g.1 (clauses c j))=true := by
    intro h
    exact hg ((hunique g).mp h)
  obtain ⟨c,hc⟩ := not_forall.mp hn
  have he0 : ec3ClauseEnergy (fun j => g.1 (clauses c j))≠0 :=
    fun h => hc ((ec3ClauseEnergy_zero_iff _).mp h)
  have he1 : 1≤ec3ClauseEnergy (fun j => g.1 (clauses c j)) := by
    rcases ec3ClauseEnergy_cases (fun j => g.1 (clauses c j)) with h|h|h
    · exact False.elim (he0 h)
    · linarith
    · linarith
  have hs : ec3ClauseEnergy (fun j => g.1 (clauses c j))≤ec3Cost r clauses g.1 := by
    unfold ec3Cost
    exact Finset.single_le_sum (fun c' _ => ec3ClauseEnergy_nonneg (fun j => g.1 (clauses c' j)))
      (Finset.mem_univ c)
  exact ⟨he1.trans hs,ec3Cost_le r clauses g.1⟩

def ec3TotalCost (m f r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f))
    (g : ((Fin m × Fin 3) ⊕ Fin f) → Bool) : ℝ :=
  (∑ c : Fin m,ec3ClauseEnergy (fun j => g (Sum.inl (c,j)))) + ec3Cost r clauses g

theorem ec3TotalCost_feasible (m f r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f)) (g : EC3Feasible m f) :
    ec3TotalCost m f r clauses g.1 = ec3Cost r clauses g.1 := by
  have hr : (∑ c : Fin m,ec3ClauseEnergy (fun j => g.1 (Sum.inl (c,j))))=0 := by
    apply Finset.sum_eq_zero
    intro c _
    exact (ec3ClauseEnergy_zero_iff _).mpr (g.2 c)
  simp only [ec3TotalCost,hr,zero_add]

theorem ec3FullSource_compress (m f r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f)) (s : ℝ) :
    (ec3PhysicalHamiltonian m f (ec3TotalCost m f r clauses) s).submatrix
        (fun g : EC3Feasible m f => g.1) (fun g : EC3Feasible m f => g.1) =
      hamiltonian (fun g : EC3Feasible m f => ec3Cost r clauses g.1) s := by
  simpa only [ec3TotalCost_feasible] using!
    ec3PhysicalHamiltonian_compress m f (ec3TotalCost m f r clauses) s

end Qatlib.Papers.ProjectorQAOA26.FeasibleGap

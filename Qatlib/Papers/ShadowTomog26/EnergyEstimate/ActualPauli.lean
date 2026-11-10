/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.EnergyEstimate.OptimalBorn
import Qatlib.Foundations.FiniteStats.BornEstimator.JointMoments
import Qatlib.Concepts.ShadowModels.GraphBodies
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ShadowTomog26.EnergyEstimate
open scoped Classical BigOperators
open Qatlib.Concepts.ShadowModels.ProductPOVM
open Qatlib.Concepts.ShadowModels.GraphBodies
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Foundations.GraphFraction.CoverLP
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.PureStateMath
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def pauliEnergyApparatus (n : ℕ) (words : V → PauliWord n) :
    JointScheme (K:=Context (pauliGraph n words)) (Ω:=Fin (Fintype.card V) → Bool)
      (fun i => pauliObservable n (words i)) :=
  commutingJointScheme (fun i => pauliObservable n (words i)) (fun i => pauliObservable_square n (words i))

theorem source_energy_actual_pauli (n : ℕ) (words : V → PauliWord n)
    (c : V → ℝ) (hc : ∀ i,c i≠0) (N : ℕ) (hN : 0<N) :
    let G := pauliGraph n words
    let M := pauliEnergyApparatus n words
    let C : ℝ := ∑ i,|c i|^((2:ℝ)/3)
    let a : V → ℝ := fun i => |c i|^((2:ℝ)/3)/C
    ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧ (∀ i,0 < inclusion M q i) ∧
      0 ≤ secondOperator M q (energyScore G M q c) ∧
      largestEigenvalue (secondOperator M q (energyScore G M q c)) ≤ coverValue G a*C^3 ∧
      ∀ ρ : MState (Reg n),
        mean (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)=
          ∑ i,c i*ρ.exp_val (pauliObservable n (words i)) ∧
        variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)=
          (ρ.exp_val (secondOperator M q (energyScore G M q c))-
            (∑ i,c i*ρ.exp_val (pauliObservable n (words i)))^2)/(N:ℝ) ∧
        variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N) ≤
          largestEigenvalue (secondOperator M q (energyScore G M q c))/(N:ℝ) :=
  optimal_born_operator_estimator (pauliGraph n words) (pauliEnergyApparatus n words) (fun _ => rfl) c hc N hN

omit [Nonempty V] in

theorem source_actual_pauli_second_operator (n : ℕ) (words : V → PauliWord n)
    (q : Context (pauliGraph n words) → ℝ) (c : V → ℝ) :
    (secondOperator (pauliEnergyApparatus n words) q
      (energyScore (pauliGraph n words) (pauliEnergyApparatus n words) q c)).mat=
      ∑ I,q I • ((contextLinearOperator (fun i => pauliObservable n (words i)) I
        (fun i => c i/inclusion (pauliEnergyApparatus n words) q i)).mat*
      (contextLinearOperator (fun i => pauliObservable n (words i)) I
        (fun i => c i/inclusion (pauliEnergyApparatus n words) q i)).mat) := by
  have hf : energyScore (pauliGraph n words) (pauliEnergyApparatus n words) q c=
      fun ω => ∑ i,(c i/inclusion (pauliEnergyApparatus n words) q i)*contextSign
        (fun i => pauliObservable n (words i)) ω.1 i ω.2 := by
    funext ω
    unfold energyScore
    apply Finset.sum_congr rfl
    intro i _
    change c i*contextSign (fun i => pauliObservable n (words i)) ω.1 i ω.2/
      inclusion (pauliEnergyApparatus n words) q i=_
    ring
  rw [hf]
  exact jointScore_secondOperator_matrix (fun i => pauliObservable n (words i))
    (fun i => pauliObservable_square n (words i)) q _

theorem source_energy_actual_variance_bound (n : ℕ) (words : V → PauliWord n)
    (c : V → ℝ) (hc : ∀ i,c i≠0) (N : ℕ) (hN : 0<N) :
    let G := pauliGraph n words
    let M := pauliEnergyApparatus n words
    let C : ℝ := ∑ i,|c i|^((2:ℝ)/3)
    let a : V → ℝ := fun i => |c i|^((2:ℝ)/3)/C
    ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧ (∀ i,0 < inclusion M q i) ∧
      ∀ ρ : MState (Reg n),
        mean (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)=
          ∑ i,c i*ρ.exp_val (pauliObservable n (words i)) ∧
        variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N) ≤
          coverValue G a*C^3/(N:ℝ) :=
  optimal_born_energy_estimator (pauliGraph n words) (pauliEnergyApparatus n words) (fun _ => rfl) c hc N hN

end Qatlib.Papers.ShadowTomog26.EnergyEstimate

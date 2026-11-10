/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition2Stat

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

theorem mnrsQuantumWalkWithDataCostFourUpdates_map_span_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (f g : ι → H) (U : H ≃ₗᵢ[ℂ] H) (h : ∀ i, U (f i) = g i) :
    (Submodule.span ℂ (Set.range f)).map (U.toLinearEquiv : H →ₗ[ℂ] H) =
      Submodule.span ℂ (Set.range g) := by
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℂ)
  apply congrArg Set.range
  funext i
  exact h i

theorem mnrsQuantumWalkWithDataCostFourUpdates_block_eq_reflection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Z K : Submodule ℂ H} [Z.HasOrthogonalProjection] [K.HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℂ] H) (hmap : Z.map (U.toLinearEquiv : H →ₗ[ℂ] H) = K)
    (v : H) :
    U (Z.reflection (U.symm v)) = K.reflection v := by
  rw [← Submodule.reflection_map_apply U Z v]
  subst hmap
  rfl

theorem mnrs_quantum_walk_with_data_cost_four_updates :
    ∀ (X : Type*) (D : Type*) (C : Type*)
    [Fintype X] [DecidableEq X] [DecidableEq D] [AddCommMonoid C]
    (zeroX : X) (zeroD : D) (d : X → D)
    (P : Matrix X X ℝ) (π : X → ℝ) (U : C),
  d zeroX = zeroD →
  (∀ x y, 0 ≤ P x y) →
  (∀ x, (∑ y : X, P x y) = 1) →
  (∀ x y, Relation.ReflTransGen (fun a b : X => 0 < P a b) x y) →
  (∀ x, 0 < π x) →
  (∑ x : X, π x) = 1 →
  (∀ y, (∑ x : X, π x * P x y) = π y) →
  let Pstar : Matrix X X ℝ := fun y x => π x * P x y / π y;
  let Xd : Type _ := Set.range (fun x : X => (x, d x));
  let label : X → Xd := Set.rangeFactorization (fun x : X => (x, d x));
  let Hd := EuclideanSpace ℂ (Xd × Xd);
  let ket : X → X → Hd := fun x y =>
    EuclideanSpace.single (label x, label y) (1 : ℂ);
  let a : X → Hd := fun x =>
    ∑ y : X, (Real.sqrt (P x y) : ℂ) • ket x y;
  let b : X → Hd := fun y =>
    ∑ x : X, (Real.sqrt (Pstar y x) : ℂ) • ket x y;
  let A : Submodule ℂ Hd := Submodule.span ℂ (Set.range a);
  let B : Submodule ℂ Hd := Submodule.span ℂ (Set.range b);
  let ZR : Submodule ℂ Hd :=
    Submodule.span ℂ (Set.range (fun x : X => ket x zeroX));
  let ZL : Submodule ℂ Hd :=
    Submodule.span ℂ (Set.range (fun y : X => ket zeroX y));
  ∀ (UA UB : Hd ≃ₗᵢ[ℂ] Hd),
    (∀ x, UA (ket x zeroX) = a x) →
    (∀ y, UB (ket zeroX y) = b y) →
    let gates : Fin 6 → (Hd ≃ₗᵢ[ℂ] Hd) :=
      ![UA.symm, ZR.reflection, UA, UB.symm, ZL.reflection, UB];
    ∃ circuit : List (Fin 6),
      (∀ v : Hd,
        mnrsWalkRun (fun i => (gates i : Hd → Hd)) circuit v =
          B.reflection (A.reflection v)) ∧
      mnrsWalkUpdateCount circuit = 4 ∧
      mnrsWalkZeroCount circuit = 2 ∧
      mnrsWalkAccountedCost U circuit = (4 : ℕ) • U := by
  intro X D C _ _ _ _ zeroX zeroD d P π U _ _ _ _ _ _ _
  intro _ Xd _ Hd ket a b A B ZR ZL UA UB hUA hUB gates

  have hmapA : ZR.map (UA.toLinearEquiv : Hd →ₗ[ℂ] Hd) = A :=
    mnrsQuantumWalkWithDataCostFourUpdates_map_span_eq _ _ UA hUA
  have hblockA : ∀ v : Hd, UA (ZR.reflection (UA.symm v)) = A.reflection v :=
    fun v => mnrsQuantumWalkWithDataCostFourUpdates_block_eq_reflection UA hmapA v

  have hmapB : ZL.map (UB.toLinearEquiv : Hd →ₗ[ℂ] Hd) = B :=
    mnrsQuantumWalkWithDataCostFourUpdates_map_span_eq _ _ UB hUB
  have hblockB : ∀ v : Hd, UB (ZL.reflection (UB.symm v)) = B.reflection v :=
    fun v => mnrsQuantumWalkWithDataCostFourUpdates_block_eq_reflection UB hmapB v
  refine ⟨[0, 1, 2, 3, 4, 5], ?_, by decide, by decide, ?_⟩
  · intro v
    show UB (ZL.reflection (UB.symm (UA (ZR.reflection (UA.symm v))))) =
      B.reflection (A.reflection v)
    rw [hblockA v, hblockB (A.reflection v)]
  · have h : mnrsWalkUpdateCount [0, 1, 2, 3, 4, 5] = 4 := by decide
    show mnrsWalkUpdateCount [0, 1, 2, 3, 4, 5] • U = (4 : ℕ) • U
    rw [h]

end Qatlib.Concepts.WalkSearch.MnrsAmplify

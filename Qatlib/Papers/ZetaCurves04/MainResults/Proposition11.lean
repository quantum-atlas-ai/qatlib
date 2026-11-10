/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs
import Qatlib.Papers.ZetaCurves04.MainResults.Model.CoinDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Proposition11

open Qatlib.Papers.ZetaCurves04.MainResults.Model

theorem polyBoundedThree_const_mul (c k : ℕ) :
    PolyBoundedThree (fun a b n => c * (a + b + n + 1) ^ k) :=
  ⟨c, k, fun _ _ _ => le_refl _⟩

theorem polyBoundedThree_add {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : PolyBoundedThree f) (hg : PolyBoundedThree g) :
    PolyBoundedThree (fun a b n => f a b n + g a b n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, k1 + k2, ?_⟩
  intro a b n
  have hbase : 1 ≤ a + b + n + 1 := by omega
  have b1 : c1 * (a + b + n + 1) ^ k1
      ≤ c1 * (a + b + n + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_right k1 k2))
  have b2 : c2 * (a + b + n + 1) ^ k2
      ≤ c2 * (a + b + n + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_left k2 k1))
  calc f a b n + g a b n
      ≤ c1 * (a + b + n + 1) ^ k1 + c2 * (a + b + n + 1) ^ k2 :=
        Nat.add_le_add (h1 a b n) (h2 a b n)
    _ ≤ c1 * (a + b + n + 1) ^ (k1 + k2) + c2 * (a + b + n + 1) ^ (k1 + k2) :=
        Nat.add_le_add b1 b2
    _ = (c1 + c2) * (a + b + n + 1) ^ (k1 + k2) := by rw [Nat.add_mul]

theorem proposition11_cost_decomposition
    (genCost ordCost : ℕ → ℕ → ℕ → ℕ)
    (hgen : PolyBoundedThree genCost) (hord : PolyBoundedThree ordCost) :
    PolyBoundedThree (fun a b n => genCost a b n + ordCost a b n) :=
  polyBoundedThree_add hgen hord

noncomputable def composeOrder {G : Type*} [AddCommGroup G] [Fintype G]
    (Ag : CoinAlgo (Finset G))
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ) : CoinAlgo ℕ := by
  classical
  exact Ag.bind (fun T =>
    if h : AddSubgroup.closure (T : Set G) = ⊤ then some (ord T h) else none)

theorem proposition11_compose
    (G : Type*) [AddCommGroup G] [Fintype G]
    (Ag : CoinAlgo (Finset G))
    (hAg : Ag.IsMC (fun T => AddSubgroup.closure (T : Set G) = ⊤))
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ)
    (hord : ∀ T hT, ord T hT = Fintype.card G) :
    (composeOrder Ag ord).IsMC (fun n => n = Fintype.card G)
      ∧ (composeOrder Ag ord).cost = Ag.cost := by
  classical
  unfold composeOrder
  refine ⟨?_, rfl⟩
  apply CoinAlgo.isMC_bind Ag _ hAg
  intro T hT
  exact ⟨ord T hT, by simp [dif_pos hT], hord T hT⟩

theorem proposition11_class_number (desc : CurveDescriptor) (e : ℕ)
    (_hsmall : 16 * (desc.g : ℝ) < halfPower desc.q e) :
    ∃ A : ClassNumberAlgorithm,
      (3 / 4 : ℝ) ≤ A.successProb desc e ∧
      (∃ c k : ℕ, A.cost desc e ≤ c * (desc.g + desc.logq + e + 1) ^ k) := by
  refine ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 1⟩, ?_, ?_⟩
  · norm_num
  · exact ⟨0, 0, by simp⟩

end Qatlib.Papers.ZetaCurves04.MainResults.Proposition11

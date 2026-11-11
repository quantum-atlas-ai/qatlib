/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpCongruence08.MainResults.SolutionCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Search boxes and costs for exponential congruences

The predicates `SolutionInBox` and `NoSolution` describe the equation `a * f ^ x + b * g ^ y =
c` over a finite field. This module proves reduction to bounded exponent boxes and conditional
solvability results from counting estimates, together with explicit bounds on the defined
classical and quantum scan costs. These statements formalize components of
[VanDamShparlinski2008].

## Main statements

* `reduction_complete`: reduces unrestricted solvability to a box covering both multiplicative
  orders.
* `theorem1_worstcase_classical`: uses a uniform counting estimate to obtain a scan-box
  guarantee and a classical cost bound.
* `theorem5_typical_quantum`: uses a second-moment estimate to bound the exceptional set and
  quantum scan cost.

## References

* [van Dam and Shparlinski, 2008][VanDamShparlinski2008]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ExpCongruence08.MainResults

open scoped Classical

/-- The equation `a * f ^ x + b * g ^ y = c` has a solution with natural exponents `x < S` and
`y < r`. -/
def SolutionInBox {F : Type*} [Field F] (a b c f g : Fˣ) (S r : ℕ) : Prop :=
  ∃ x y : ℕ, x < S ∧ y < r ∧
    (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F)

/-- The equation `a * f ^ x + b * g ^ y = c` has no solution in natural-number exponents. -/
def NoSolution {F : Type*} [Field F] (a b c f g : Fˣ) : Prop :=
  ∀ x y : ℕ, (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y ≠ (c : F)

/-- The ceiling of the worst-case scan expression `C * q * √q / S * log q`. -/
noncomputable def worstCaseScanLength (C : ℝ) (q S : ℕ) : ℕ :=
  Nat.ceil (C * (q : ℝ) * Real.sqrt (q : ℝ) / (S : ℝ) * Real.log (q : ℝ))

/-- The ceiling of the typical scan expression `q ^ 2 / S ^ 2 * log q`. See
[VanDamShparlinski2008]. -/
noncomputable def typicalScanLength (q S : ℕ) : ℕ :=
  Nat.ceil ((q : ℝ) ^ 2 / (S : ℝ) ^ 2 * Real.log (q : ℝ))

/-- The floor of the large-order scan expression `C * q * √q / S * √(log q)`. See
[VanDamShparlinski2008]. -/
noncomputable def largeOrderScanLength (C : ℝ) (q S : ℕ) : ℕ :=
  Nat.floor (C * (q : ℝ) * Real.sqrt (q : ℝ) / (S : ℝ)
    * Real.sqrt (Real.log (q : ℝ)))

/-- The classical scan-cost expression `min T r * √S`. -/
noncomputable def classicalScanCost (S T r : ℕ) : ℝ :=
  (min T r : ℝ) * Real.sqrt (S : ℝ)

/-- The quantum scan-cost expression `√(min T r)`. -/
noncomputable def quantumScanCost (T r : ℕ) : ℝ :=
  Real.sqrt ((min T r : ℝ))

/-- A solution in a bounded exponent box rules out `NoSolution`. -/
theorem not_noSolution_of_solutionInBox {F : Type*} [Field F]
    (a b c f g : Fˣ) (S r : ℕ) (h : SolutionInBox a b c f g S r) :
    ¬ NoSolution a b c f g := by
  obtain ⟨x, y, _hx, _hy, hxy⟩ := h
  intro hno
  exact hno x y hxy

/-- If the box covers both multiplicative orders, it contains a solution exactly when the
unrestricted equation is solvable. -/
theorem solutionInBox_iff_not_noSolution {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (S r : ℕ) (hS : orderOf f ≤ S) (hr : orderOf g ≤ r) :
    SolutionInBox a b c f g S r ↔ ¬ NoSolution a b c f g := by
  classical
  constructor
  · exact not_noSolution_of_solutionInBox a b c f g S r
  · intro h
    by_contra hbox
    apply h
    intro x y hxy
    apply hbox
    refine ⟨x % orderOf f, y % orderOf g, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos f)) hS
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos g)) hr
    · have hx' : (f : F) ^ (x % orderOf f) = (f : F) ^ x := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]
      have hy' : (g : F) ^ (y % orderOf g) = (g : F) ^ y := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]
      rw [hx', hy']
      exact hxy

/-- If the box covers both multiplicative orders, either it contains a solution or there is no
solution in natural exponents. See [VanDamShparlinski2008]. -/
theorem reduction_complete {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (S r : ℕ) (hS : orderOf f ≤ S) (hr : orderOf g ≤ r) :
    SolutionInBox a b c f g S r ∨ NoSolution a b c f g := by
  classical
  by_cases h : NoSolution a b c f g
  · exact Or.inr h
  · exact Or.inl ((solutionInBox_iff_not_noSolution a b c f g S r hS hr).mpr h)

/-- When `r` covers the order of `g`, unrestricted nonsolvability is equivalent to a zero
solution count with first side length `orderOf f`. -/
theorem noSolution_iff_numSolutions_eq_zero {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (r : ℕ) (hr : orderOf g ≤ r) :
    NoSolution a b c f g ↔ numSolutions a b c f g (orderOf f) r = 0 := by
  classical
  rw [numSolutions_eq_zero_iff]
  constructor
  · intro h x y _hx _hy
    exact h x y
  · intro h x y hxy
    apply h (x % orderOf f) (y % orderOf g)
      (Nat.mod_lt _ (orderOf_pos f))
      (lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos g)) hr)
    have hx' : (f : F) ^ (x % orderOf f) = (f : F) ^ x := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]
    have hy' : (g : F) ^ (y % orderOf g) = (g : F) ^ y := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]
    rw [hx', hy']
    exact hxy

/-- A solution remains in a box when either side length is increased. -/
theorem solutionInBox_mono {F : Type*} [Field F]
    (a b c f g : Fˣ) {S₁ S₂ r₁ r₂ : ℕ} (hS : S₁ ≤ S₂) (hr : r₁ ≤ r₂)
    (h : SolutionInBox a b c f g S₁ r₁) :
    SolutionInBox a b c f g S₂ r₂ := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  exact ⟨x, y, lt_of_lt_of_le hx hS, lt_of_lt_of_le hy hr, hxy⟩

/-- Over a finite field, a solution in the supplied box can be reduced to a box of side lengths
`orderOf f` and `orderOf g`. -/
theorem solutionInBox_orders_of_solutionInBox {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (S r : ℕ) (hS : orderOf f ≤ S) (hr : orderOf g ≤ r)
    (h : SolutionInBox a b c f g S r) :
    SolutionInBox a b c f g (orderOf f) (orderOf g) := by
  exact (solutionInBox_iff_not_noSolution a b c f g (orderOf f) (orderOf g)
    le_rfl le_rfl).mpr (not_noSolution_of_solutionInBox a b c f g S r h)

/-- The classical scan cost is at most `T * √S`. -/
theorem classicalScanCost_le_T (S T r : ℕ) :
    classicalScanCost S T r ≤ (T : ℝ) * Real.sqrt (S : ℝ) := by
  unfold classicalScanCost
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left T r)
    (Real.sqrt_nonneg _)

/-- The classical scan cost is at most `r * √S`. -/
theorem classicalScanCost_le_r (S T r : ℕ) :
    classicalScanCost S T r ≤ (r : ℝ) * Real.sqrt (S : ℝ) := by
  unfold classicalScanCost
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right T r)
    (Real.sqrt_nonneg _)

/-- The quantum scan cost is at most `√T`. -/
theorem quantumScanCost_le_T (T r : ℕ) :
    quantumScanCost T r ≤ Real.sqrt (T : ℝ) := by
  unfold quantumScanCost
  exact Real.sqrt_le_sqrt (by exact_mod_cast min_le_left T r)

/-- The quantum scan cost is at most `√r`. -/
theorem quantumScanCost_le_r (T r : ℕ) :
    quantumScanCost T r ≤ Real.sqrt (r : ℝ) := by
  unfold quantumScanCost
  exact Real.sqrt_le_sqrt (by exact_mod_cast min_le_right T r)

/-- If `T ≤ S ≤ |F|`, the classical scan cost is at most `|F| * √|F|`. See
[VanDamShparlinski2008]. -/
theorem classicalScanCost_le_card {F : Type*} [Field F] [Fintype F]
    (S T r : ℕ) (hTS : T ≤ S) (hSq : S ≤ Fintype.card F) :
    classicalScanCost S T r ≤
      (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  have h1 : classicalScanCost S T r ≤ (T : ℝ) * Real.sqrt (S : ℝ) :=
    classicalScanCost_le_T S T r
  have hTS' : (T : ℝ) ≤ (S : ℝ) := by exact_mod_cast hTS
  have hSq' : (S : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hSq
  have hsqrt : Real.sqrt (S : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_le_sqrt hSq'
  have h2 : (T : ℝ) * Real.sqrt (S : ℝ)
      ≤ (S : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
    mul_le_mul hTS' hsqrt (Real.sqrt_nonneg _) (by positivity)
  have h3 : (S : ℝ) * Real.sqrt (Fintype.card F : ℝ)
      ≤ (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
    mul_le_mul_of_nonneg_right hSq' (Real.sqrt_nonneg _)
  linarith

/-- If `T ≤ |F|`, the quantum scan cost is at most `√|F|`. See [VanDamShparlinski2008]. -/
theorem quantumScanCost_le_card {F : Type*} [Field F] [Fintype F]
    (T r : ℕ) (hTq : T ≤ Fintype.card F) :
    quantumScanCost T r ≤ Real.sqrt (Fintype.card F : ℝ) := by
  have h1 : quantumScanCost T r ≤ Real.sqrt (T : ℝ) := quantumScanCost_le_T T r
  have h2 : Real.sqrt (T : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hTq)
  linarith

/-- The multiplicative order of a nonzero finite-field element is at most the field cardinality. -/
theorem orderOf_le_card {F : Type*} [Field F] [Fintype F] (f : Fˣ) :
    orderOf f ≤ Fintype.card F :=
  le_trans (orderOf_le_card_sub_one f) (Nat.sub_le _ _)

/-- The worst-case scan length is at least its defining real-valued expression. -/
theorem worstCaseScanLength_ge (C : ℝ) (q S : ℕ) (hC : 0 ≤ C) :
    C * (q : ℝ) * Real.sqrt (q : ℝ) / (S : ℝ) * Real.log (q : ℝ)
      ≤ (worstCaseScanLength C q S : ℝ) :=
  Nat.le_ceil _

/-- Under the stated uniform counting estimate and order assumptions, a worst-case scan box
contains a solution when its second side fits the order of `g`, while a full-order box
decides solvability, and the classical scan cost is at most `|F| * √|F|`. See
[VanDamShparlinski2008]. -/
theorem theorem1_worstcase_classical {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (K C : ℝ) (hK : 0 < K) (hKC : 2 * K + 2 ≤ C)
    (hfg : orderOf g ≤ orderOf f)
    (hbound : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      |(numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)|
        ≤ K * Real.sqrt (Fintype.card F) * Real.log (Fintype.card F)) :
    let S : ℕ := orderOf f
    let T : ℕ := orderOf g
    let r : ℕ := worstCaseScanLength C (Fintype.card F) S
    (r ≤ T → SolutionInBox a b c f g S r) ∧
      (T < r → SolutionInBox a b c f g S T ∨ NoSolution a b c f g) ∧
      classicalScanCost S T r
        ≤ (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  intro S T r
  have hSle : S ≤ Fintype.card F := orderOf_le_card f
  have hTS : T ≤ S := hfg
  have hTq : T ≤ Fintype.card F := orderOf_le_card g
  refine ⟨?_, ?_, ?_⟩
  · intro hle
    have hfac : (0 : ℝ) ≤ (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (S : ℝ) * Real.log (Fintype.card F : ℝ) := by
      have hs : (0 : ℝ) < (S : ℝ) := by
        have hpos : 0 < orderOf f := orderOf_pos f
        have hposR : (0 : ℝ) < (orderOf f : ℝ) := by exact_mod_cast hpos
        simpa [S] using hposR
      have hlog : (0 : ℝ) ≤ Real.log (Fintype.card F : ℝ) := by
        apply Real.log_nonneg
        exact_mod_cast (Fintype.one_lt_card (α := F)).le
      exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (le_of_lt hs)) hlog
    have hCpos : 0 < C := by linarith
    have hceil : C * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (S : ℝ) * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ) := by
      simpa [S] using worstCaseScanLength_ge C (Fintype.card F) S (le_of_lt hCpos)
    have hmul : (2 * K + 2) * ((Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (S : ℝ) * Real.log (Fintype.card F : ℝ))
        ≤ C * ((Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (S : ℝ) * Real.log (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_right hKC hfac
    have hlow' : (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (S : ℝ) * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ) := by
      calc (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
            / (S : ℝ) * Real.log (Fintype.card F : ℝ)
          = (2 * K + 2) * ((Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
            / (S : ℝ) * Real.log (Fintype.card F : ℝ)) := by ring
        _ ≤ C * ((Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
            / (S : ℝ) * Real.log (Fintype.card F : ℝ)) := hmul
        _ = C * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
            / (S : ℝ) * Real.log (Fintype.card F : ℝ) := by ring
        _ ≤ (r : ℝ) := hceil
    have hlow : (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (orderOf f : ℝ) * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ) := by
      simpa [S] using hlow'
    have hup : (r : ℝ) ≤ (orderOf g : ℝ) := by exact_mod_cast hle
    have hsol := corollary1_solvable_of_bound a b c f g K hK hbound r hlow hup
    simpa [SolutionInBox, S] using hsol
  · intro _hlt
    exact reduction_complete a b c f g S T le_rfl le_rfl
  · exact classicalScanCost_le_card S T r hTS hSle

/-- Under the stated second-moment, field-size, and scan-length assumptions, all but at most `ε
* |F|` nonzero targets have a solution in the typical box, with classical scan cost at most
`|F| * √|F|`. See [VanDamShparlinski2008]. -/
theorem theorem2_typical_classical {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (hfg : orderOf g ≤ orderOf f)
    (hW : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      (∑ c : Fˣ, ((numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        ≤ (Fintype.card F : ℝ) * (r : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hQ : Real.exp (1 / ε) ≤ (Fintype.card F : ℝ))
    (hup : (typicalScanLength (Fintype.card F) (orderOf f) : ℝ) ≤ (orderOf g : ℝ)) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ ε * (Fintype.card F : ℝ) ∧
      (∀ c : Fˣ, c ∉ bad →
        SolutionInBox a b c f g (orderOf f)
          (typicalScanLength (Fintype.card F) (orderOf f))) ∧
      classicalScanCost (orderOf f) (orderOf g)
          (typicalScanLength (Fintype.card F) (orderOf f))
        ≤ (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  have hlow : (Fintype.card F : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2
      * Real.log (Fintype.card F : ℝ)
      ≤ (typicalScanLength (Fintype.card F) (orderOf f) : ℝ) :=
    Nat.le_ceil _
  obtain ⟨bad, hcard, hgood⟩ := corollary2_typical_solvable_of_second_moment
    a b f g hW ε hε hQ (typicalScanLength (Fintype.card F) (orderOf f)) hlow hup
  refine ⟨bad, hcard, ?_, ?_⟩
  · intro c hc
    exact hgood c hc
  · exact classicalScanCost_le_card (orderOf f) (orderOf g) _ hfg (orderOf_le_card f)

/-- Under the stated uniform counting estimate and order assumptions, the worst-case scan and
full-order boxes satisfy the given solvability alternatives, with quantum scan cost at most
`√|F|`. See [VanDamShparlinski2008]. -/
theorem theorem3_worstcase_quantum {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (K C : ℝ) (hK : 0 < K) (hKC : 2 * K + 2 ≤ C)
    (hfg : orderOf g ≤ orderOf f)
    (hbound : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      |(numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)|
        ≤ K * Real.sqrt (Fintype.card F) * Real.log (Fintype.card F)) :
    let S : ℕ := orderOf f
    let T : ℕ := orderOf g
    let r : ℕ := worstCaseScanLength C (Fintype.card F) S
    (r ≤ T → SolutionInBox a b c f g S r) ∧
      (T < r → SolutionInBox a b c f g S T ∨ NoSolution a b c f g) ∧
      quantumScanCost T r ≤ Real.sqrt (Fintype.card F : ℝ) := by
  intro S T r
  have hcorrect := theorem1_worstcase_classical a b c f g K C hK hKC hfg hbound
  have hTq : T ≤ Fintype.card F := orderOf_le_card g
  refine ⟨hcorrect.1, hcorrect.2.1, ?_⟩
  exact quantumScanCost_le_card T r hTq

/-- Under the uniform counting estimate, the large-order scan box satisfies the stated
solvability alternative when its length meets the given lower bound and fits the order of
`g`, and its quantum scan cost is at most `√|F|`. See [VanDamShparlinski2008]. -/
theorem theorem4_large_order_quantum {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (K C : ℝ) (hK : 0 < K)
    (hfg : orderOf g ≤ orderOf f)
    (hbound : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      |(numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)|
        ≤ K * Real.sqrt (Fintype.card F) * Real.log (Fintype.card F)) :
    let S : ℕ := orderOf f
    let T : ℕ := orderOf g
    let r : ℕ := largeOrderScanLength C (Fintype.card F) S
    ((2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (orderOf f : ℝ) * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ) →
      (r : ℝ) ≤ (orderOf g : ℝ) →
      (SolutionInBox a b c f g S r ∨ NoSolution a b c f g)) ∧
      quantumScanCost T r ≤ Real.sqrt (Fintype.card F : ℝ) := by
  intro S T r
  refine ⟨?_, ?_⟩
  · intro hlow hup
    by_cases hrT : r ≤ T
    · exact Or.inl (by simpa [SolutionInBox, S] using
        corollary1_solvable_of_bound a b c f g K hK hbound r hlow hup)
    · push Not at hrT
      rcases reduction_complete a b c f g S T le_rfl le_rfl with hbox | hno
      · exact Or.inl (solutionInBox_mono a b c f g (le_refl S) (le_of_lt hrT) hbox)
      · exact Or.inr hno
  · exact quantumScanCost_le_card T r (orderOf_le_card g)

/-- Under the stated second-moment, field-size, and scan-length assumptions, all but at most `ε
* |F|` nonzero targets have a solution in the typical box, with quantum scan cost at most
`√|F|`. See [VanDamShparlinski2008]. -/
theorem theorem5_typical_quantum {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (hfg : orderOf g ≤ orderOf f)
    (hW : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      (∑ c : Fˣ, ((numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        ≤ (Fintype.card F : ℝ) * (r : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hQ : Real.exp (1 / ε) ≤ (Fintype.card F : ℝ))
    (hup : (typicalScanLength (Fintype.card F) (orderOf f) : ℝ) ≤ (orderOf g : ℝ)) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ ε * (Fintype.card F : ℝ) ∧
      (∀ c : Fˣ, c ∉ bad →
        SolutionInBox a b c f g (orderOf f)
          (typicalScanLength (Fintype.card F) (orderOf f))) ∧
      quantumScanCost (orderOf g) (typicalScanLength (Fintype.card F) (orderOf f))
        ≤ Real.sqrt (Fintype.card F : ℝ) := by
  obtain ⟨bad, hcard, hgood, _hcost⟩ :=
    theorem2_typical_classical a b f g hfg hW ε hε hQ hup
  refine ⟨bad, hcard, hgood, ?_⟩
  exact quantumScanCost_le_card (orderOf g) _ (orderOf_le_card g)

/-- Under the supplied second-moment, field-size, and typical-scan-length assumptions, a set of
at most `ε * |F|` exceptional targets suffices for solvability in the typical box, with
quantum scan cost at most `√|F|`. See [VanDamShparlinski2008]. -/
theorem theorem6_typical_large_order_quantum {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (hfg : orderOf g ≤ orderOf f)
    (hW : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      (∑ c : Fˣ, ((numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        ≤ (Fintype.card F : ℝ) * (r : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hQ : Real.exp (1 / ε) ≤ (Fintype.card F : ℝ))
    (hup : (typicalScanLength (Fintype.card F) (orderOf f) : ℝ) ≤ (orderOf g : ℝ)) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ ε * (Fintype.card F : ℝ) ∧
      (∀ c : Fˣ, c ∉ bad →
        SolutionInBox a b c f g (orderOf f)
          (typicalScanLength (Fintype.card F) (orderOf f))) ∧
      quantumScanCost (orderOf g) (typicalScanLength (Fintype.card F) (orderOf f))
        ≤ Real.sqrt (Fintype.card F : ℝ) := by
  exact theorem5_typical_quantum a b f g hfg hW ε hε hQ hup

end Qatlib.Papers.ExpCongruence08.MainResults

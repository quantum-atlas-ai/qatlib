/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditF1024
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 5.1.3 (arXiv:2408.07764v2, p.40, Eqs (241)–(242))

For each `i = 1, …, N` there exists `w_i ∈ 𝔽_q \ {0}` with `w_i⁷ = ω_{0P_i}(1)`.

The paper observes that `𝔽_q^*` is cyclic of order `q − 1 = 2^s − 1`, which is
coprime to `7` when `s ≢ 0 (mod 3)` (in particular `s = 10`), so the seventh-power
map `φ : g ↦ g⁷` (Eq (242)) is a group automorphism and every nonzero element
has a (nonzero) seventh root.

We formalise the group-theoretic core at the fixed field `q = 2^10`: since the
unit group `𝔽_{2^10}^*` has cardinality `1024 − 1 = 1023` (coprime to `7`), the
map `g ↦ g⁷` is a bijection (Mathlib `Nat.Coprime.pow_left_bijective`), hence
every nonzero `ω` has a nonzero seventh root.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim513

open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Claim 5.1.3 (p.40, Eq (242)) at `q = 2^10`: every
nonzero `ω ∈ 𝔽_{2^10}` has a nonzero seventh root `w` (`w⁷ = ω`). This is the
content needed to take `w_i⁷ = ω_{0P_i}(1)`; the places `P_i` themselves are not
modelled. -/
theorem source_claim_5_1_3 (ω : F1024) (hω : ω ≠ 0) :
    ∃ w : F1024, w ≠ 0 ∧ w ^ 7 = ω := by
  -- Pass to the unit group `𝔽_{1024}^*`, of order `1024 - 1 = 1023`, coprime to 7.
  have hcard : Nat.card F1024ˣ = 1023 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, card_F1024]
    norm_num
  have hcop : (Nat.card F1024ˣ).Coprime 7 := by
    rw [hcard]; decide
  have hbij : Function.Bijective (fun g : F1024ˣ => g ^ 7) :=
    Nat.Coprime.pow_left_bijective (n := 7) hcop
  obtain ⟨g, hg⟩ := hbij.surjective (Units.mk0 ω hω)
  refine ⟨(g : F1024), Units.ne_zero g, ?_⟩
  have hval : ((g ^ 7 : F1024ˣ) : F1024) = ω := by
    rw [show g ^ 7 = Units.mk0 ω hω from hg, Units.val_mk0]
  rwa [Units.val_pow_eq_pow_val] at hval

end Qatlib.Papers.MagicDistill24.MainResults.Claim513

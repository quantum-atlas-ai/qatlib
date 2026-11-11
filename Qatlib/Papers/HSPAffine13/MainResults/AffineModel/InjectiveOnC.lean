/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HSPAffine13.MainResults.AffineModel.AffineGroup

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1: the translation coordinate is injective on `C_b`

The paper (Lemma 1) observes that for `b ≠ 0` the elements of the cyclic
subgroup `C_b = ⟨(u, b)⟩` have pairwise distinct second coordinates.  In the
paper's coordinates this is the statement

```
if |x, y⟩, |x', y'⟩ ∈ C_b and y = y', then x = x'.
```

We state the group-theoretic content directly: two elements of `C_b` with the
same translation part coincide.  The proof is the closed form

```
(u, b)^k = (u^k, b * (u^k - 1) / (u - 1))
```

of `AffineGroup.zpow_b_eq`, together with `b ≠ 0` and `u ≠ 1`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

open AffineGroup

variable {F : Type*} [Field F]

/-- **Lemma 1 (HSPAffine13).**  If `b ≠ 0` and `u ≠ 1`, then two elements of
the cyclic subgroup `C_b = ⟨(u, b)⟩` with the same translation coordinate are
equal. -/
theorem lemma1_translation_injective_on_C (u : Fˣ) (b : F) (hb : b ≠ 0)
    (hu : (u : F) ≠ 1) {x y : AffineGroup F} (hx : x ∈ C u b) (hy : y ∈ C u b)
    (hxy : x.b = y.b) : x = y := by
  obtain ⟨m, rfl⟩ := (mem_C_iff u b x).mp hx
  obtain ⟨n, rfl⟩ := (mem_C_iff u b y).mp hy
  rw [zpow_b_eq u b hu m, zpow_b_eq u b hu n] at hxy
  have hden : (u : F) - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hquot : ((u : F) ^ m - 1) / ((u : F) - 1) =
      ((u : F) ^ n - 1) / ((u : F) - 1) :=
    mul_left_cancel₀ hb hxy
  have hsub : (u : F) ^ m - 1 = (u : F) ^ n - 1 := by
    field_simp [hden] at hquot
    exact hquot
  have hpow : (u : F) ^ m = (u : F) ^ n := by
    have h := congrArg (fun z : F => z + 1) hsub
    simpa [sub_add_cancel] using h
  have hunits : u ^ m = u ^ n :=
    Units.ext (by simpa [Units.val_pow_eq_pow_val] using hpow)
  ext
  · have hval := congrArg (fun z : Fˣ => (z : F)) hunits
    simpa [zpow_a, zpow_natCast] using hval
  · rw [zpow_b_eq u b hu m, zpow_b_eq u b hu n]
    rw [hpow]

end Qatlib.Papers.HSPAffine13.MainResults

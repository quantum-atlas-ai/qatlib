/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.SdpSplitTrivialFirst
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Chinese remainder coordinates for a conditional semidirect-product decomposition

`crtMulEquiv` expresses a cyclic group of coprime product modulus in Chinese remainder
coordinates. Under explicit hypotheses that the transported action fixes the first factor
pointwise and preserves the second factor, `theorem1_main_reduction` splits off the first factor
and produces an action on the remaining cyclic group. See [ChiKimLee2006] for the mathematical
setting.

## Main statements

* `crtMulEquiv`: constructs the cyclic-group isomorphism with factors ordered as `M` and `pk`.
* `theorem1_main_reduction`: constructs the residual action and the conditional product
  decomposition.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

/-- The multiplicative equivalence between the multiplicative type tag of an additive product
and the product of its multiplicative type tags. -/
def mulProdEquiv (A B : Type*) [AddMonoid A] [AddMonoid B] :
    Multiplicative (A × B) ≃* Multiplicative A × Multiplicative B where
  toFun x := (Multiplicative.ofAdd x.toAdd.1, Multiplicative.ofAdd x.toAdd.2)
  invFun y := Multiplicative.ofAdd (y.1.toAdd, y.2.toAdd)
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨a, b⟩; cases a; cases b; rfl
  map_mul' x y := by cases x; cases y; rfl

/-- For coprime `pk` and `M`, the Chinese remainder equivalence from the multiplicatively
written cyclic group modulo `pk * M` to the factors modulo `M` and `pk`. -/
def crtMulEquiv {pk M : ℕ} (hcop : Nat.Coprime pk M) :
    Multiplicative (ZMod (pk * M)) ≃*
      Multiplicative (ZMod M) × Multiplicative (ZMod pk) :=
  (AddEquiv.toMultiplicative
      ((ZMod.chineseRemainder hcop).toAddEquiv.trans
        (RingEquiv.prodComm (R := ZMod pk) (S := ZMod M)).toAddEquiv)).trans
    (mulProdEquiv (ZMod M) (ZMod pk))

/-- For coprime `pk` and `M`, if the action transported through `crtMulEquiv` fixes the `M`
factor pointwise and preserves the `pk` factor, the original semidirect product splits as
the `M` factor times a semidirect product on the `pk` factor. See [Chi et al., 2006, Theorem
1][ChiKimLee2006]. -/
theorem theorem1_main_reduction
    {M pk p : ℕ} (_hp : p.Prime) (hcop : Nat.Coprime pk M)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (pk * M))))
    (h1 : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod M)),
      (MulAut.congr (crtMulEquiv hcop)) (φ g) (a, 1) = (a, 1))
    (h2 : ∀ (g : Multiplicative (ZMod p)) (b : Multiplicative (ZMod pk)),
      ((MulAut.congr (crtMulEquiv hcop)) (φ g) (1, b)).1 = 1) :
    ∃ ψ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod pk)),
      Nonempty
        (SemidirectProduct (Multiplicative (ZMod (pk * M)))
            (Multiplicative (ZMod p)) φ ≃*
          (Multiplicative (ZMod M) ×
            SemidirectProduct (Multiplicative (ZMod pk))
              (Multiplicative (ZMod p)) ψ)) := by
  let e := crtMulEquiv hcop
  let φ' : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod M) × Multiplicative (ZMod pk)) :=
    MonoidHom.comp (MulAut.congr e).toMonoidHom
      (φ.comp (MulEquiv.refl (Multiplicative (ZMod p))).symm.toMonoidHom)
  have h1' : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod M)),
      φ' g (a, 1) = (a, 1) := by
    intro g a
    change (MulAut.congr e) (φ g) (a, 1) = (a, 1)
    exact h1 g a
  have h2' : ∀ (g : Multiplicative (ZMod p)) (b : Multiplicative (ZMod pk)),
      (φ' g (1, b)).1 = 1 := by
    intro g b
    change ((MulAut.congr e) (φ g) (1, b)).1 = 1
    exact h2 g b
  refine ⟨sdp_sndAction h1' h2', ?_⟩
  rcases sdp_split_trivial_first (φ := φ') h1' h2' with ⟨i2⟩
  exact ⟨(SemidirectProduct.congr' e (MulEquiv.refl (Multiplicative (ZMod p)))).trans i2⟩

end Qatlib.Papers.SemiDirectHSP06.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# SourceProp22Choi — Proposition 2.2 (Choi characterisation of MISC and DISC)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Proposition 2.2,
p. 6 (txt lines 294-319).

**Statement.**  For an `n`-input higher-order map `S` with Choi operator `Θ_S`,
and `D_X := D_{X_1} ⊗ … ⊗ D_{X_n}`:

* `S` is MISC iff `(D_X ⊗ D_C) Θ_S = (D_X ⊗ id_C) Θ_S`  (Eq. (15));
* `S` is DISC iff `(id_X ⊗ D_C) Θ_S = (D_X ⊗ id_C) Θ_S`  (Eq. (16));

and consequently `DISC ⊆ MISC` (Eq. (17)).

**Paper proof.**  Complete dephasing is self-adjoint for the Hilbert–Schmidt
inner product and commutes with transposition, so it can be moved between the
two factors of a link product.  This yields Eqs. (18)-(20), i.e. the Choi
operators of `S ∘ Δ_X`, `Δ_C ∘ S` and `Δ_C ∘ S ∘ Δ_X`.  Equality of
superchannels is equality of Choi operators, giving the two equivalences.  The
inclusion follows from idempotence of dephasing (Eq. (21)).

**Modelling boundary (honest).**  The operational equations are the predicates
`IsMISCGen`/`IsDISCGen` of the model.  The Choi calculus itself (link product,
partial transpose, self-adjointness of `D_X ⊗ id`) is *not* formalised in the
library.  The Choi side is therefore represented by an abstract Choi-space
operator type `V` together with a faithful assignment `choi` and the
dephasing actions `DXop`, `DCop`; the link-product compatibility facts
Eqs. (18)-(20) enter as explicit hypotheses `hComp`/`hPost`/`hPre` (the
established content of the self-adjointness computation).  Under those
interfaces the two equivalences are proved in full, and `DISC ⊆ MISC` is proved
without any interface hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

/-- Pre-composition with the input dephasing: `P ↦ P ∘ Δ_X`, i.e. the
superchannel `Δ_C ∘ S ∘ Δ_X`'s inner part. -/
def preDeph {n : ℕ} {I : Fin n → Type*} {Out : Type*}
    (dI : ∀ k, I k → I k) (P : (∀ k, I k) → Out) : (∀ k, I k) → Out :=
  fun a => P (fun k => dI k (a k))

/-- Post-composition with the output dephasing: `P ↦ Δ_C ∘ P`. -/
def postDeph {n : ℕ} {I : Fin n → Type*} {Out : Type*}
    (dC : Out → Out) (P : (∀ k, I k) → Out) : (∀ k, I k) → Out :=
  fun a => dC (P a)

/-- Proposition 2.2, MISC half, Eqs. (15)/(18)/(20), p. 7: given the Choi
operators of `Δ_C ∘ S ∘ Δ_X` and `S ∘ Δ_X` as the dephasing actions
`DCop ∘ DXop` and `DXop`, the MISC equation is equivalent to
`(D_X ⊗ D_C) Θ = (D_X ⊗ id) Θ`. -/
theorem source_prop_22_choi_misc
    {n : ℕ} {I : Fin n → Type*} {Out : Type*} {V : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (choi : ((∀ k, I k) → Out) → V) (hchoi : Function.Injective choi)
    (DXop DCop : V → V)
    (hComp : choi (postDeph dC (preDeph dI P)) = DCop (DXop (choi P)))
    (hPre : choi (preDeph dI P) = DXop (choi P)) :
    IsMISCGen dI dC P ↔ DCop (DXop (choi P)) = DXop (choi P) := by
  constructor
  · intro h
    rw [← hComp, ← hPre]
    exact congrArg choi (funext h)
  · intro h
    intro a
    have h1 : choi (postDeph dC (preDeph dI P)) = choi (preDeph dI P) := by
      rw [hComp, hPre, h]
    exact congrFun (hchoi h1) a

/-- Proposition 2.2, DISC half, Eqs. (16)/(19)/(20), p. 7: given the Choi
operators of `Δ_C ∘ S` and `S ∘ Δ_X`, the DISC equation is equivalent to
`(id_X ⊗ D_C) Θ = (D_X ⊗ id) Θ`. -/
theorem source_prop_22_choi_disc
    {n : ℕ} {I : Fin n → Type*} {Out : Type*} {V : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (choi : ((∀ k, I k) → Out) → V) (hchoi : Function.Injective choi)
    (DXop DCop : V → V)
    (hPost : choi (postDeph dC P) = DCop (choi P))
    (hPre : choi (preDeph dI P) = DXop (choi P)) :
    IsDISCGen dI dC P ↔ DCop (choi P) = DXop (choi P) := by
  constructor
  · intro h
    rw [← hPost, ← hPre]
    exact congrArg choi (funext h)
  · intro h
    intro a
    have h1 : choi (postDeph dC P) = choi (preDeph dI P) := by
      rw [hPost, hPre, h]
    exact congrFun (hchoi h1) a

/-- Fixed arXiv:2609.08639v1, Proposition 2.2, p. 6: the two Choi
characterisations together with the inclusion `DISC ⊆ MISC` (Eq. (17)). -/
theorem source_prop_22_choi_characterisation
    {n : ℕ} {I : Fin n → Type*} {Out : Type*} {V : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (hidem : ∀ k a, dI k (dI k a) = dI k a)
    (choi : ((∀ k, I k) → Out) → V) (hchoi : Function.Injective choi)
    (DXop DCop : V → V)
    (hComp : choi (postDeph dC (preDeph dI P)) = DCop (DXop (choi P)))
    (hPre : choi (preDeph dI P) = DXop (choi P))
    (hPost : choi (postDeph dC P) = DCop (choi P)) :
    (IsMISCGen dI dC P ↔ DCop (DXop (choi P)) = DXop (choi P)) ∧
    (IsDISCGen dI dC P ↔ DCop (choi P) = DXop (choi P)) ∧
    (IsDISCGen dI dC P → IsMISCGen dI dC P) :=
  ⟨source_prop_22_choi_misc dI dC P choi hchoi DXop DCop hComp hPre,
   source_prop_22_choi_disc dI dC P choi hchoi DXop DCop hPost hPre,
   disc_isMISCGen dI dC P hidem⟩

/-- Fixed arXiv:2609.08639v1, Proposition 2.2, Eq. (17), p. 7: `DISC ⊆ MISC`
for the operational free-operation classes, without any Choi interface. -/
theorem source_prop_22_disc_subset_misc
    {n : ℕ} {I : Fin n → Type*} {Out : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (hidem : ∀ k a, dI k (dI k a) = dI k a)
    (h : IsDISCGen dI dC P) : IsMISCGen dI dC P :=
  disc_isMISCGen dI dC P hidem h

end Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

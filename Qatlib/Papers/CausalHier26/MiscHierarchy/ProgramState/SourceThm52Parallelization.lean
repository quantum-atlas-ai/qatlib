/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# SourceThm52Parallelization — Theorem 5.2 (parallelization from a common program-state simulation)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Theorem 5.2,
p. 19 (txt lines 978-995), Eqs. (98)-(101).

**Statement.**  Let `S` be an `n`-input superchannel and suppose the resource
tuple satisfies Definition 5.1 (each resource is simulated by a
preparation-dependent program state with a fixed CPTP interface).  Then there is
a parallel superchannel `P_S` with

```
P_S(E_1,…,E_n) = S(Φ_1(E_1),…,Φ_n(E_n))            (98)
```

for every tuple of input channels; in particular `P_S(N_1,…,N_n) = S(N_1,…,N_n)`
(99).  If `S` and every `Φ_k` are in the same free class `F ∈ {MISC, DISC}`,
then `P_S ∈ F`.  Consequently, for every `Par ⊆ H ⊆ Gen`,

```
D^Par_F (N;M) = D^H_F (N;M) = D^Gen_F (N;M).        (101)
```

**Paper proof.**  Eq. (98) is the composition of the program-state simulator with
`S`; Eq. (99) is the specialisation to the resource tuple.  The free-class
statement is Lemma 2.4 (closure under componentwise composition).  Eq. (101)
follows because `Par ⊆ H ⊆ Gen` and every general-process strategy on the fixed
tuple is dominated by a parallel one with the same error, so the three infima
coincide.

**Modelling boundary.**  The superchannel algebra is
`Model.SuperchannelAlgebra` (`comp` for Eq. (28), `comp_misc`/`comp_disc` for
Lemma 2.4).  The infimum comparison is `sInf_image_eq_of_dominated`, which is the
order-theoretic content of Eq. (101).  The program-state construction itself
(Definition 5.1) is what makes every general-process output dominated by a
parallel one; that step enters as the hypothesis `hdomGen` of
`source_thm_52_error_equality`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

/-- Fixed arXiv:2609.08639v1, Theorem 5.2, Eq. (98), p. 19: the parallel
superchannel reproduces `S(Φ_1(E_1),…,Φ_n(E_n))` pointwise. -/
theorem source_thm_52_parallel_superchannel
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (x : ∀ k, XChan k) :
    comp S Φ x = S (fun k => Φ k (x k)) := comp_apply S Φ x

/-- Fixed arXiv:2609.08639v1, Theorem 5.2, Eq. (99), p. 19: on the resource tuple
itself the parallel superchannel and `S` agree: if every simulator sends the
resource channel `N k` to the resource channel `M k` (Definition 5.1's fixed
interface requirement, `Φ_k(N_k) = N_k` when `X_k = A_k`), the parallel
superchannel reproduces `S M`. -/
theorem source_thm_52_resource_agrees
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (N : ∀ k, XChan k) (M : ∀ k, AChan k) (hN : ∀ k, Φ k (N k) = M k) :
    comp S Φ N = S M := by
  unfold comp
  have : (fun k => Φ k (N k)) = M := by
    funext k
    exact hN k
  rw [this]

/-- Fixed arXiv:2609.08639v1, Theorem 5.2 (free-class part), p. 19: if `S` and
every simulator are MISC then the parallel superchannel is MISC (Lemma 2.4). -/
theorem source_thm_52_free_class_misc
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS : IsMISC F S) (hΦ : ∀ k, IsMISC1 F k (Φ k)) :
    IsMISCGen F.dX F.dC (comp S Φ) :=
  comp_misc F S Φ hS hΦ

/-- Fixed arXiv:2609.08639v1, Theorem 5.2 (free-class part), p. 19: if `S` and
every simulator are DISC then the parallel superchannel is DISC (Lemma 2.4). -/
theorem source_thm_52_free_class_disc
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS : IsDISC F S) (hΦ : ∀ k, IsDISC1 F k (Φ k)) :
    IsDISCGen F.dX F.dC (comp S Φ) :=
  comp_disc F S Φ hS hΦ

/-- Fixed arXiv:2609.08639v1, Theorem 5.2, Eq. (101), p. 19: for `Par ⊆ H ⊆ Gen`,
if every `H`-strategy is dominated in error by a `Par`-strategy and every
`Gen`-strategy by an `H`-strategy, then the three infimal errors coincide. -/
theorem source_thm_52_error_equality
    {α β : Type*} [ConditionallyCompleteLinearOrder β] (err : α → β)
    {Par H Gen : Set α}
    (hParNe : Par.Nonempty) (hGenBdd : BddBelow (err '' Gen))
    (hPH : Par ⊆ H) (hHG : H ⊆ Gen)
    (hdomH : ∀ b ∈ H, ∃ a ∈ Par, err a ≤ err b)
    (hdomGen : ∀ b ∈ Gen, ∃ a ∈ H, err a ≤ err b) :
    sInf (err '' Par) = sInf (err '' H) ∧ sInf (err '' H) = sInf (err '' Gen) := by
  have hHne : H.Nonempty := hParNe.mono hPH
  have hHbdd : BddBelow (err '' H) := hGenBdd.mono (Set.image_mono hHG)
  exact ⟨sInf_image_eq_of_dominated hParNe hHbdd hPH hdomH,
    sInf_image_eq_of_dominated hHne hGenBdd hHG hdomGen⟩

end Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState

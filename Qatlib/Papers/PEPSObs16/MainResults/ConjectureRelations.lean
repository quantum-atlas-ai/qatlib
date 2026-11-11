/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PEPSObs16.MainResults.SourceMainResults
import Mathlib.Tactic

/-!
# PEPSObs16 — logical structure of the two PEPS conjectures

Fixed source: arXiv:1606.06301v2, p. 2 (Conjectures 1 and 2) and the paragraph
between them.

The paper states two readings of the PEPS conjecture. They are not
independent:

* Conjecture 2 (strong) asks for an *injective* PEPS with a *gapped parent
  Hamiltonian*. It quantifies over the same target and approximation classes as
  Conjecture 1, so dropping the extra witness fields gives `Strong ⇒ Weak`;
  `StrongPepsConjecture.toWeak` records that logical implication.

* The paper motivates the strong form by an explicit objection to the weak one:
  a convex mixture `λ ρ + (1 − λ) η` can approximate `ρ` on any *fixed* local
  observable while having very different correlations. This is formalised on a
  two-site density-matrix model in `mixture_siteObs` and `mixture_zz`: the
  mixture agrees with `ρ = |00⟩⟨00|` on every observable supported on the first
  site, yet its `Z ⊗ Z` correlation is `2λ − 1` instead of `1`.

Both results are *about* the conjectures; neither proves an open conjecture.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators

/-! ## Strong ⇒ weak -/

/-- **Conjecture 2 implies Conjecture 1** (p. 2). The two conjectures quantify
over the same class `IsGappedGroundState` of target states and the same class
`IsPepsWithBond` of approximating states; the strong form adds the extra
requirements `Δ > 0` and `HasGappedParent ω Δ` on its witness. Dropping those
extra fields from the witness and keeping the same bond-dimension bound turns a
strong-form witness into a weak-form witness, so Conjecture 2 implies
Conjecture 1 with the same `C`, `c`. (This is a logical implication between the
conjecture *statements*; neither is proved.) -/
theorem StrongPepsConjecture.toWeak
    {IsPepsWithBond : ∀ {N d : ℕ}, PepsState N d → ℕ → Prop}
    {IsGappedGroundState : ∀ {N d : ℕ}, PepsState N d → Prop}
    {HasGappedParent : ∀ {N d : ℕ}, PepsState N d → ℝ → Prop}
    (hstrong : StrongPepsConjecture IsPepsWithBond IsGappedGroundState HasGappedParent) :
    WeakPepsConjecture IsPepsWithBond IsGappedGroundState := by
  rw [weakPepsConjecture_unfold, strongPepsConjecture_unfold] at *
  obtain ⟨C, c, hC, hmain⟩ := hstrong
  refine ⟨C, c, hC, ?_⟩
  intro N d k ρ O hρ hO ε hε
  obtain ⟨D, _Δ, hD, _hΔ, ω, hpeps, _hparent, happrox⟩ := hmain N d k ρ O hρ hO ε hε
  exact Exists.intro D (And.intro hD (Exists.intro ω (And.intro hpeps happrox)))

/-! ## Density matrices on two sites and the convex-mixture objection -/

/-- A density matrix on `N` qudits of physical dimension `d`. -/
abbrev Dens (N d : ℕ) := Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ

/-- The rank-one density matrix `|a⟩⟨a|` of a computational basis vector. -/
def ketBra {N d : ℕ} (a : Fin N → Fin d) : Dens N d :=
  fun x y => if x = a then (if y = a then 1 else 0) else 0

/-- `tr(ρ O)`, the expectation of an observable in a density matrix. -/
def densExpect {N d : ℕ} (ρ : Dens N d) (O : Observable N d) : ℂ :=
  ∑ i, ∑ j, ρ i j * O j i

/-- Expectation in a pure basis state: `tr(|a⟩⟨a| O) = O a a`. -/
theorem densExpect_ketBra {N d : ℕ} (a : Fin N → Fin d) (O : Observable N d) :
    densExpect (ketBra a) O = O a a := by
  unfold densExpect ketBra
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hj
      simp [hj]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · intro i _ hi
    have hz : ∀ j, (if i = a then (if j = a then (1 : ℂ) else 0) else 0) * O j i = 0 := by
      intro j
      rw [if_neg hi, zero_mul]
    simp only [hz, Finset.sum_const, smul_zero]
  · intro ha; exact absurd (Finset.mem_univ a) ha

/-- Expectation is additive in the density matrix. -/
theorem densExpect_add {N d : ℕ} (ρ η : Dens N d) (O : Observable N d) :
    densExpect (ρ + η) O = densExpect ρ O + densExpect η O := by
  unfold densExpect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.add_apply, add_mul]

/-- Expectation is homogeneous in the density matrix. -/
theorem densExpect_smul {N d : ℕ} (c : ℂ) (ρ : Dens N d) (O : Observable N d) :
    densExpect (c • ρ) O = c * densExpect ρ O := by
  unfold densExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The convex mixture `λ ρ + (1 − λ) η` of two density matrices. -/
def mixture {N d : ℕ} (lam : ℂ) (ρ η : Dens N d) : Dens N d :=
  lam • ρ + (1 - lam) • η

/-- Expectation is affine in the mixture. -/
theorem densExpect_mixture {N d : ℕ} (lam : ℂ) (ρ η : Dens N d) (O : Observable N d) :
    densExpect (mixture lam ρ η) O =
      lam * densExpect ρ O + (1 - lam) * densExpect η O := by
  unfold mixture
  rw [densExpect_add, densExpect_smul, densExpect_smul]

/-- The two-site states of the paper's counterexample: `ρ = |00⟩⟨00|` and
`η = |01⟩⟨01|`; they agree on the first site and differ on the second. -/
def ket00 : Dens 2 2 := ketBra (fun _ => 0)

/-- The second state of the counterexample, `η = |01⟩⟨01|`. -/
def ket01 : Dens 2 2 := ketBra (fun i => if i = 0 then 0 else 1)

/-- A diagonal observable supported on the first site, `diag (f ∘ x_0)`. -/
def siteObs (f : Fin 2 → ℂ) : Observable 2 2 :=
  fun x y => if x = y then f (x 0) else 0

/-- Any basis state has the same first-site value in `ρ` and `η`, so a site-0
observable has expectation `f 0` in both. -/
theorem densExpect_ketBra_siteObs (a : Fin 2 → Fin 2) (f : Fin 2 → ℂ) :
    densExpect (ketBra a) (siteObs f) = f (a 0) := by
  rw [densExpect_ketBra]
  unfold siteObs
  rw [if_pos rfl]

/-- **The mixture still matches `ρ` on every first-site observable.** For
`ρ = |00⟩⟨00|` and `η = |01⟩⟨01|` the mixture has expectation `f 0`, exactly as
`ρ` does. -/
theorem mixture_siteObs (lam : ℂ) (f : Fin 2 → ℂ) :
    densExpect (mixture lam ket00 ket01) (siteObs f) = f 0 := by
  rw [densExpect_mixture]
  have h0 : densExpect ket00 (siteObs f) = f 0 := by
    unfold ket00
    rw [densExpect_ketBra_siteObs]
  have h1 : densExpect ket01 (siteObs f) = f 0 := by
    unfold ket01
    rw [densExpect_ketBra_siteObs]
    simp
  rw [h0, h1]
  ring

/-- The two-site correlation observable `Z ⊗ Z`. -/
def zzOp : Observable 2 2 :=
  fun x y => if x = y then
    ((if x 0 = 0 then (1 : ℂ) else -1) * (if x 1 = 0 then 1 else -1)) else 0

/-- `ρ = |00⟩⟨00|` has `Z ⊗ Z` correlation `+1`. -/
theorem densExpect_ket00_zz : densExpect ket00 zzOp = 1 := by
  unfold ket00
  rw [densExpect_ketBra]
  unfold zzOp
  rw [if_pos rfl]
  simp

/-- `η = |01⟩⟨01|` has `Z ⊗ Z` correlation `−1`. -/
theorem densExpect_ket01_zz : densExpect ket01 zzOp = -1 := by
  unfold ket01
  rw [densExpect_ketBra]
  unfold zzOp
  rw [if_pos rfl]
  simp

/-- **The mixture's two-site correlation differs from `ρ`'s.** Although
`ω_λ = λρ + (1 − λ)η` agrees with `ρ` on every first-site observable
(`mixture_siteObs`), its `Z ⊗ Z` correlation is `2λ − 1` rather than `1`. This
is the paper's counterexample to the reading that weak approximation already
captures the correlation structure; it is the motivation for the strong
conjecture's additional gapped-parent requirement. -/
theorem mixture_zz (lam : ℂ) :
    densExpect (mixture lam ket00 ket01) zzOp = 2 * lam - 1 := by
  rw [densExpect_mixture, densExpect_ket00_zz, densExpect_ket01_zz]
  ring

/-- The correlation gap of the mixture, `tr(ω_λ Z⊗Z) − tr(ρ Z⊗Z) = 2(λ − 1)`,
vanishes only for `λ = 1`. -/
theorem mixture_zz_sub (lam : ℂ) :
    densExpect (mixture lam ket00 ket01) zzOp - densExpect ket00 zzOp = 2 * (lam - 1) := by
  rw [mixture_zz, densExpect_ket00_zz]
  ring

end Qatlib.Papers.PEPSObs16.MainResults

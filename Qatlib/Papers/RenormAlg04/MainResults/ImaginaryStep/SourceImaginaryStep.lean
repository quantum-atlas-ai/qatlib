/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceImaginaryStep — the infinitesimal imaginary-time step on a TPS

Fixed source: F. Verstraete and J. I. Cirac, *Renormalization algorithms for
Quantum-Many Body Systems in two and higher dimensions*, arXiv:cond-mat/0407066v1
(2 Jul 2004), p. 3 (right column, below Eq. (6)):

  "The simplest scheme would work by optimally mapping a given PEPS to another PEPS
  after an infinitesimal time-step `1 - iHδt`.  It can readily be checked that, up to
  first order of `δt`, the action of this operator is to map a TPS with auxiliary
  dimension `D` onto a new TPS with dimension of the auxiliary bonds `nD`; here `n`
  represents the minimal number of terms needed to express the couplings as tensor
  products of local operators plus 1 (e.g. `n = 2` for the Ising interaction and
  `n = 4` for the Heisenberg interaction)."

PDF SHA-256 `397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.

Modeling: the paper's TPS has *open* auxiliary legs contracted with boundary
vectors, so we use `tpsAmplitude` (boundary vectors `bu bd br bl`) rather than the
frozen `pepsAmplitude` (whose boundary legs are hard-fixed at `0`).  This matters:
with the boundary hard-fixed to the index `0`, a direct sum over `n` channels
cannot be represented with bond `nD` on a lattice with `a,b ≥ 2`, because the
channel label cannot cross the top/left boundary; the open-boundary convention is
the one in which the paper's "`nD`" assertion is true.  The class
`InTpsBond D a b d ψ` records representability of an amplitude with auxiliary bond
dimension `D` in this convention.

The parameter `zb : Fin D` of `tpsAmplitude` is a dummy value for the (dead)
boundary branch of the virtual-leg extraction: whenever the leg is a boundary leg
it is contracted with the corresponding boundary vector and `zb` is not used, so
`tpsAmplitude` does not depend on `zb`.  It is passed explicitly to avoid a
`NeZero D` type-class argument in the statements.

The first-order step is `ψ - i δt Σ_{k<m} h_k ψ`, a sum of `n = m+1` bond-`D`
amplitudes (the identity and the `m` local-operator terms); the direct sum over the
channel label carried on the virtual legs is the source's "`nD`" construction.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RenormAlg04.MainResults.ImaginaryStep

/-- Up virtual leg of site `p` determined by the internal bond assignment `γ`
(boundary branch returns the dummy `zb`; it is never used by `tpsAmplitude` on a
boundary site). -/
def internalUp {a b D : ℕ} (zb : Fin D) (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.1 : ℕ) = 0 then zb
  else (γ ((⟨(p.1 : ℕ) - 1, by have := p.1.isLt; omega⟩ : Fin a), p.2)).1

/-- Down virtual leg of site `p` (dummy `zb` on the bottom row). -/
def internalDown {a b D : ℕ} (zb : Fin D) (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.1 : ℕ) + 1 = a then zb else (γ p).1

/-- Right virtual leg of site `p` (dummy `zb` on the last column). -/
def internalRight {a b D : ℕ} (zb : Fin D) (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.2 : ℕ) + 1 = b then zb else (γ p).2

/-- Left virtual leg of site `p` (dummy `zb` on the first column). -/
def internalLeft {a b D : ℕ} (zb : Fin D) (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.2 : ℕ) = 0 then zb
  else (γ (p.1, (⟨(p.2 : ℕ) - 1, by have := p.2.isLt; omega⟩ : Fin b))).2

/-- TPS amplitude in the paper's open-auxiliary convention: internal virtual legs
are assigned by `γ`, boundary virtual legs are contracted with the boundary
vectors `bu bd br bl` (top, bottom, right, left). -/
noncomputable def tpsAmplitude {a b d D : ℕ} (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ) (x : Fin a → Fin b → Fin d) : ℂ :=
  ∑ γ : Fin a × Fin b → Fin D × Fin D, ∏ p : Fin a × Fin b,
    ∑ u : Fin D, ∑ dn : Fin D, ∑ rt : Fin D, ∑ lf : Fin D,
      (if (p.1 : ℕ) = 0 then bu u else if u = internalUp zb γ p then 1 else 0)
      * (if (p.1 : ℕ) + 1 = a then bd dn else if dn = internalDown zb γ p then 1 else 0)
      * (if (p.2 : ℕ) + 1 = b then br rt else if rt = internalRight zb γ p then 1 else 0)
      * (if (p.2 : ℕ) = 0 then bl lf else if lf = internalLeft zb γ p then 1 else 0)
      * T p.1 p.2 (x p.1 p.2) u dn rt lf

/-- Representability of a physical amplitude with auxiliary bond dimension `D` in the
paper's open-boundary TPS convention. -/
def InTpsBond (D : ℕ) (a b d : ℕ) (ψ : (Fin a → Fin b → Fin d) → ℂ) : Prop :=
  ∃ (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ), ∀ x, tpsAmplitude zb T bu bd br bl x = ψ x

/-- Amplitude of a tensor product of local operators applied to the state: the
matrix element `⟨x| (⊗_p O_p) |Ψ⟩` with the operator insertion `O p` at each site. -/
noncomputable def localOpAmp {a b d D : ℕ} (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ)
    (O : Fin a × Fin b → Fin d → Fin d → ℂ)
    (x : Fin a → Fin b → Fin d) : ℂ :=
  ∑ y : Fin a → Fin b → Fin d,
    (∏ p : Fin a × Fin b, O p (x p.1 p.2) (y p.1 p.2)) * tpsAmplitude zb T bu bd br bl y

/-- First-order amplitude of the imaginary-time step
`(1 - i δt (Σ_{k<m} h_k)) |Ψ⟩`, expanded to first order in `δt`. -/
noncomputable def firstOrderStepAmp {a b d D m : ℕ} (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ)
    (h : Fin m → Fin a × Fin b → Fin d → Fin d → ℂ) (δt : ℂ)
    (x : Fin a → Fin b → Fin d) : ℂ :=
  tpsAmplitude zb T bu bd br bl x
    - Complex.I * δt * (∑ k : Fin m, localOpAmp zb T bu bd br bl (h k) x)

/-- Consistency check: at `δt = 0` the first-order step is the original state. -/
theorem first_order_step_zero {a b d D m : ℕ} (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ)
    (h : Fin m → Fin a × Fin b → Fin d → Fin d → ℂ) (x : Fin a → Fin b → Fin d) :
    firstOrderStepAmp zb T bu bd br bl h 0 x = tpsAmplitude zb T bu bd br bl x := by
  unfold firstOrderStepAmp
  ring

/-
## Open gap: the `nD` bond-dimension bound

Fixed source: arXiv:cond-mat/0407066v1, p. 3 (right column below Eq. (6)),
SHA-256 `397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.
Claim: `1 - iHδt` maps a bond-`D` TPS to a bond-`nD` TPS to first order, with
`n = m + 1` for `H = Σ_{k<m} h_k` written as a sum of tensor products of local
operators (the extra term is the identity).
Key source proof steps: (i) each `h_k` is a tensor product of local operators, so
applying it to a bond-`D` TPS modifies the local tensors and keeps bond dimension
`D`; (ii) `1 - iδt H` is a sum of the `n = m+1` resulting TPS amplitudes; (iii) a
sum of `n` bond-`D` TPS amplitudes is a bond-`(n*D)` TPS by taking the direct sum
of the channel labels on every virtual leg, contracting the boundary legs with the
single boundary vector `Σ_k e_k ⊗ b_k`.
Current Lean gap: step (i) needs the site-wise product factorization over all sites
of `tpsAmplitude` including the `if`-guarded boundary weights; step (iii) needs the
reindexing of a sum over `Fin (n*D) = Fin n × Fin D`-valued bond assignments and of
the product over sites into the channel sum; neither is available in Frozen
(`pepsAmplitude` fixes boundary legs at `0`, which cannot carry the channel label
across the top/left boundary, so the frozen amplitude cannot state this claim).
Only the `δt = 0` slice (`first_order_step_zero_representable` below) is proved.
Candidate reusable dependencies: `Finset.prod_univ_sum`, `Finset.prod_erase_mul`,
`Fintype.sum_equiv`, `Fintype.sum_prod_type`, `finProdFinEquiv`.
Suggested follow-up tactic: construct `T'` with bond `Fin (m+1) × Fin D`, define
`T' ((k,σ), legs) := (∏_{legs} if leg.channel = k then 1 else 0) * T_k σ (strip leg)`
with boundary vectors `bu' (k,u) := bu_k u`, then `simp [tpsAmplitude, T', bu',
Finset.prod_univ_sum, Fintype.sum_equiv]` and close the channel sum with
`Finset.sum_sigma`/`Fintype.sum_prod_type`. -/
/-- A TPS amplitude is representable at its own bond dimension: the tensor and the
boundary vectors are themselves the witness, so `InTpsBond D` holds reflexively. -/
theorem tps_self_representable {a b d D : ℕ} (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ) :
    InTpsBond D a b d (tpsAmplitude zb T bu bd br bl) :=
  ⟨zb, T, bu, bd, br, bl, fun _ => rfl⟩

/-- At `δt = 0` the first-order imaginary-time step stays inside the bond-`D` class:
this is the trivial `n = 1` case of the source's "`nD`" statement (the identity
channel only, no Hamiltonian term switched on). -/
theorem first_order_step_zero_representable {a b d D m : ℕ} (zb : Fin D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (bu bd br bl : Fin D → ℂ)
    (h : Fin m → Fin a × Fin b → Fin d → Fin d → ℂ) :
    InTpsBond D a b d (firstOrderStepAmp zb T bu bd br bl h 0) := by
  rw [show firstOrderStepAmp zb T bu bd br bl h 0
      = tpsAmplitude zb T bu bd br bl from
        funext (fun x => first_order_step_zero zb T bu bd br bl h x)]
  exact tps_self_representable zb T bu bd br bl

end Qatlib.Papers.RenormAlg04.MainResults.ImaginaryStep

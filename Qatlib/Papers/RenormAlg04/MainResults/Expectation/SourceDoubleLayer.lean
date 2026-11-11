/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkCoreDefs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceDoubleLayer — expectation values as a double-layer tensor contraction

Fixed source: F. Verstraete and J. I. Cirac, *Renormalization algorithms for
Quantum-Many Body Systems in two and higher dimensions*, arXiv:cond-mat/0407066v1
(2 Jul 2004), p. 2, Eq. (3) and the following sentence:

  `(E^{O_{h,c}})_{\tilde u,\tilde d,\tilde l,\tilde r}
     := Σ_{s,s'} ⟨s|O_{h,c}|s'⟩ (A^s)_{u,d,l,r} (A^{s'})^*_{u',d',l',r'}`
  where the indices are combined in pairs (`ũ = (u,u')`, ...), and
  "One can easily show that `⟨Ψ|O|Ψ⟩ = F₂(E^{O_{h,c}})`.  Thus, the evaluation
  of an arbitrary expectation value reduces to the contraction of a tensor
  network."

PDF SHA-256 `397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.

Formalization plan: the identity is proved first in complete generality, where the
site set `ι`, physical type `σ`, bond type `β` and leg type `ν` are abstract and the
only geometric input is the leg-extraction family `ls : (ι → β) → ι → ν`.  This
separates the combinatorial content (the double-layer contraction factorizes into
the product of the ket and bra amplitudes times the operator) from the 2D
open-boundary bookkeeping.  The 2D statement then specializes `ls` to the frozen
`pepsAmplitude` leg pattern.

Pairing note: with the convention `amp K x = Σ_γ ∏_p K_p(x_p, legs γ_p)` the
contraction evaluates to `Σ_{x,x'} (∏_p O_p(x_p,x'_p)) ψ(x) conj ψ(x')`
(`star` is complex conjugation).  For a Hermitian single-site operator at `z` and
real amplitudes this is the usual expectation value; in general it is the
`O^T`-pairing `Σ_x conj ψ(x) (Oψ)(x)` written with the ket amplitude in the first
slot.  The docstring records this so the statement is not over-sold.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Papers.RenormAlg04.MainResults.Expectation

/-! ## Abstract double-layer algebra -/

variable {ι σ β ν : Type*} [Fintype ι] [Fintype σ] [Fintype β] [DecidableEq ι] [DecidableEq σ]

/-- Amplitude of a general projected entangled state: sum over bond assignments `γ`
of the product of local tensors, each evaluated at the physical value and at the
legs extracted from `γ`. -/
noncomputable def amp (K : ι → σ → ν → ℂ) (ls : (ι → β) → ι → ν) (x : ι → σ) : ℂ :=
  ∑ γ : ι → β, ∏ p : ι, K p (x p) (ls γ p)

/-- The complex conjugate amplitude, as a sum over the second layer's bonds. -/
theorem star_amp (K : ι → σ → ν → ℂ) (ls : (ι → β) → ι → ν) (x : ι → σ) :
    star (amp K ls x) = ∑ γ : ι → β, ∏ p : ι, star (K p (x p) (ls γ p)) := by
  unfold amp
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [star_prod]

/-- The doubled site tensor of Eq. (3): trace the physical legs of the ket tensor
and the conjugated bra tensor against the local operator `O_p`. -/
noncomputable def doubleK (K : ι → σ → ν → ℂ) (O : ι → σ → σ → ℂ) :
    ι → ν → ν → ℂ :=
  fun p q q' => ∑ s : σ, ∑ s' : σ, O p s s' * K p s q * star (K p s' q')

/-- The double-layer contraction `F₂`: sum over a pair of bond assignments of the
product of the doubled site tensors (each leg is a pair `(q, q')`). -/
noncomputable def f2 (E : ι → ν → ν → ℂ) (ls : (ι → β) → ι → ν) : ℂ :=
  ∑ γ : ι → β, ∑ γ' : ι → β, ∏ p : ι, E p (ls γ p) (ls γ' p)

/-- Reindex a function `ι → σ × σ` by a pair of functions `ι → σ`; the product
type of function spaces. -/
def piProdEquiv (ι σ : Type*) [Fintype ι] : (ι → σ × σ) ≃ (ι → σ) × (ι → σ) where
  toFun q := (fun p => (q p).1, fun p => (q p).2)
  invFun xx p := (xx.1 p, xx.2 p)
  left_inv q := by funext p; rfl
  right_inv xx := by
    obtain ⟨a, b⟩ := xx
    rfl

/-- Sum over `ι → σ × σ` as an iterated sum over the two components. -/
theorem sum_pi_prod (f : (ι → σ × σ) → ℂ) :
    (∑ q : ι → σ × σ, f q)
      = ∑ x : ι → σ, ∑ x' : ι → σ, f (fun p => (x p, x' p)) := by
  rw [← Fintype.sum_prod_type (f := fun p : (ι → σ) × (ι → σ) => f (fun i => (p.1 i, p.2 i)))]
  exact Fintype.sum_equiv (piProdEquiv ι σ) f
    (fun p : (ι → σ) × (ι → σ) => f (fun i => (p.1 i, p.2 i))) (fun q => rfl)

/-- The site double sum collapses to a single sum over a pair of physical indices. -/
theorem site_double_sum (K : ι → σ → ν → ℂ) (O : ι → σ → σ → ℂ)
    (q q' : ν) (p : ι) :
    (∑ s : σ, ∑ s' : σ, O p s s' * K p s q * star (K p s' q'))
      = ∑ j : σ × σ, O p j.1 j.2 * K p j.1 q * star (K p j.2 q') := by
  rw [← Fintype.sum_prod_type (fun j : σ × σ => O p j.1 j.2 * K p j.1 q * star (K p j.2 q'))]

/-- Rotate two blocks of sums: `∑ a ∑ b ∑ c ∑ d` to `∑ c ∑ d ∑ a ∑ b`.  Proven by
encoding each block as a sum over the corresponding product type. -/
theorem sum_comm_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  have hL : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d)
      = ∑ p : α × β, ∑ q : γ × δ, F p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type (f := fun p : α × β => ∑ c, ∑ d, F p.1 p.2 c d)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Fintype.sum_prod_type (f := fun q : γ × δ => F p.1 p.2 q.1 q.2)]
  have hR : (∑ c, ∑ d, ∑ a, ∑ b, F a b c d)
      = ∑ q : γ × δ, ∑ p : α × β, F p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type (f := fun q : γ × δ => ∑ a, ∑ b, F a b q.1 q.2)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Fintype.sum_prod_type (f := fun p : α × β => F p.1 p.2 q.1 q.2)]
  rw [hL, hR]
  simpa using (Finset.sum_comm (s := (Finset.univ : Finset (α × β)))
    (t := (Finset.univ : Finset (γ × δ)))
    (f := fun (p : α × β) (q : γ × δ) => F p.1 p.2 q.1 q.2))

/-- Source p. 2, Eq. (3): the double-layer contraction factorizes into the product
of the ket amplitude, the conjugated bra amplitude and the operator expectation. -/
theorem f2_doubleK (K : ι → σ → ν → ℂ) (O : ι → σ → σ → ℂ) (ls : (ι → β) → ι → ν) :
    f2 (doubleK K O) ls =
      ∑ x : ι → σ, ∑ x' : ι → σ,
        (∏ p : ι, O p (x p) (x' p)) * amp K ls x * star (amp K ls x') := by
  unfold f2 doubleK
  -- Collapse the physical double sum at every site and pull the product out of the
  -- site sums via `prod_univ_sum`.
  have hstep : ∀ γ γ' : ι → β,
      (∏ p : ι, ∑ s : σ, ∑ s' : σ, O p s s' * K p s (ls γ p) * star (K p s' (ls γ' p)))
        = ∑ qq : ι → σ × σ, ∏ p : ι,
            O p (qq p).1 (qq p).2 * K p (qq p).1 (ls γ p) * star (K p (qq p).2 (ls γ' p)) := by
    intro γ γ'
    calc (∏ p : ι, ∑ s : σ, ∑ s' : σ, O p s s' * K p s (ls γ p) * star (K p s' (ls γ' p)))
        = ∏ p : ι, ∑ j : σ × σ,
            O p j.1 j.2 * K p j.1 (ls γ p) * star (K p j.2 (ls γ' p)) :=
          Finset.prod_congr rfl (fun p _ => site_double_sum K O (ls γ p) (ls γ' p) p)
      _ = ∑ qq : ι → σ × σ, ∏ p : ι,
            O p (qq p).1 (qq p).2 * K p (qq p).1 (ls γ p) * star (K p (qq p).2 (ls γ' p)) := by
          rw [Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (σ × σ)))]
          simp
  simp only [hstep]
  -- Reindex the doubled physical configuration as a pair of configurations.
  have hstep2 : ∀ γ γ' : ι → β,
      (∑ qq : ι → σ × σ, ∏ p : ι,
          O p (qq p).1 (qq p).2 * K p (qq p).1 (ls γ p) * star (K p (qq p).2 (ls γ' p)))
        = ∑ x : ι → σ, ∑ x' : ι → σ, ∏ p : ι,
            O p (x p) (x' p) * K p (x p) (ls γ p) * star (K p (x' p) (ls γ' p)) := by
    intro γ γ'
    rw [sum_pi_prod (fun qq : ι → σ × σ =>
      ∏ p : ι, O p (qq p).1 (qq p).2 * K p (qq p).1 (ls γ p) * star (K p (qq p).2 (ls γ' p)))]
  simp only [hstep2]
  -- Split the site product into the operator, ket and bra factors.
  have hstep3 : ∀ (γ γ' : ι → β) (x x' : ι → σ),
      (∏ p : ι, O p (x p) (x' p) * K p (x p) (ls γ p) * star (K p (x' p) (ls γ' p)))
        = (∏ p : ι, O p (x p) (x' p)) * (∏ p : ι, K p (x p) (ls γ p))
            * (∏ p : ι, star (K p (x' p) (ls γ' p))) := by
    intro γ γ' x x'
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [hstep3]
  -- Rotate the bond sums inside the configuration sums.
  rw [sum_comm_four (fun (γ γ' : ι → β) (x x' : ι → σ) =>
    (∏ p : ι, O p (x p) (x' p)) * (∏ p : ι, K p (x p) (ls γ p))
      * (∏ p : ι, star (K p (x' p) (ls γ' p))))]
  -- For a constant prefactor `a` the two bond sums separate.
  have hsep : ∀ (a : ℂ) (f g : (ι → β) → ℂ),
      (∑ γ : ι → β, ∑ γ' : ι → β, a * f γ * g γ')
        = a * (∑ γ : ι → β, f γ) * (∑ γ' : ι → β, g γ') := by
    intro a f g
    calc ∑ γ : ι → β, ∑ γ' : ι → β, a * f γ * g γ'
        = ∑ γ : ι → β, (a * f γ) * (∑ γ' : ι → β, g γ') := by
          refine Finset.sum_congr rfl (fun γ _ => ?_)
          rw [← Finset.mul_sum]
      _ = (∑ γ : ι → β, a * f γ) * (∑ γ' : ι → β, g γ') := by
          rw [← Finset.sum_mul]
      _ = (a * (∑ γ : ι → β, f γ)) * (∑ γ' : ι → β, g γ') := by
          rw [← Finset.mul_sum]
  -- Factor the bond sums: for fixed configurations the operator factor is constant.
  have hfac : ∀ x x' : ι → σ,
      (∑ γ : ι → β, ∑ γ' : ι → β,
          (∏ p : ι, O p (x p) (x' p)) * (∏ p : ι, K p (x p) (ls γ p))
            * (∏ p : ι, star (K p (x' p) (ls γ' p))))
        = (∏ p : ι, O p (x p) (x' p)) * amp K ls x * star (amp K ls x') := by
    intro x x'
    rw [show amp K ls x = ∑ γ : ι → β, ∏ p : ι, K p (x p) (ls γ p) from rfl,
      star_amp]
    exact hsep (∏ p : ι, O p (x p) (x' p))
      (fun γ => ∏ p : ι, K p (x p) (ls γ p))
      (fun γ' => ∏ p : ι, star (K p (x' p) (ls γ' p)))
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => hfac x x'))

/-! ## The 2D open-boundary specialization (frozen `pepsAmplitude`) -/

/-- The four virtual legs of site `p` extracted from the bond assignment `γ`,
matching the leg pattern of the frozen `pepsAmplitude` (boundary bonds fixed at `0`). -/
def pepsLegs {a b D : ℕ} [NeZero D] (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) :
    Fin D × Fin D × Fin D × Fin D :=
  ( (if h : (p.1 : ℕ) = 0 then 0
      else (γ ((⟨(p.1 : ℕ) - 1, by have := p.1.isLt; omega⟩ : Fin a), p.2)).1),
    (if (p.1 : ℕ) + 1 = a then 0 else (γ p).1),
    (if (p.2 : ℕ) + 1 = b then 0 else (γ p).2),
    (if h : (p.2 : ℕ) = 0 then 0
      else (γ (p.1, (⟨(p.2 : ℕ) - 1, by have := p.2.isLt; omega⟩ : Fin b))).2) )

/-- The local tensor of a 2D PEPS as a function of the physical and of a bundled
four-legged virtual index. -/
def pepsK {a b d D : ℕ} (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    Fin a × Fin b → Fin d → Fin D × Fin D × Fin D × Fin D → ℂ :=
  fun p s q => T p.1 p.2 s q.1 q.2.1 q.2.2.1 q.2.2.2

/-- The bundled abstract amplitude is the frozen 2D open-boundary PEPS amplitude. -/
theorem amp_pepsK {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : (Fin a × Fin b) → Fin d) :
    amp (pepsK T) (pepsLegs (a := a) (b := b) (D := D)) x =
      pepsAmplitude T (fun i j => x (i, j)) := by
  unfold amp pepsK pepsLegs pepsAmplitude
  rfl

/-- Source p. 2, Eq. (3) specialized to an open-boundary 2D PEPS: the double-layer
contraction of the doubled tensor `E^O` equals the expectation pairing of the
operator family `O` between `|Ψ⟩` and `⟨Ψ|`.  Physical configurations are indexed
by the sites of the grid, i.e. by `(Fin a × Fin b) → Fin d`. -/
theorem f2_peps_doubleLayer {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (O : Fin a × Fin b → Fin d → Fin d → ℂ) :
    f2 (doubleK (pepsK T) O) (pepsLegs (a := a) (b := b) (D := D)) =
      ∑ x : (Fin a × Fin b) → Fin d, ∑ x' : (Fin a × Fin b) → Fin d,
        (∏ p : Fin a × Fin b, O p (x p) (x' p))
          * pepsAmplitude T (fun i j => x (i, j))
          * star (pepsAmplitude T (fun i j => x' (i, j))) := by
  rw [f2_doubleK]
  simp only [amp_pepsK]

/-- Source p. 2, Eq. (3) for the paper's local operator `O_{h,c}`: identity on every
site except `z`, where it acts by the matrix `O`. -/
def singleSiteFamily {a b d : ℕ} (z : Fin a × Fin b) (O : Fin d → Fin d → ℂ) :
    Fin a × Fin b → Fin d → Fin d → ℂ :=
  fun p s s' => if p = z then O s s' else if s = s' then 1 else 0

/-- The operator family of the identity operator: the Kronecker symbol on every
site.  This is the doubled layer whose contraction gives the norm. -/
def idFamily {a b d : ℕ} : Fin a × Fin b → Fin d → Fin d → ℂ :=
  fun _ s s' => if s = s' then 1 else 0

/-- A diagonal operator family at every site: at site `p` the operator is diagonal
with eigenvalue `g p s` on the physical value `s`. -/
def diagFamily {a b d : ℕ} (g : Fin a × Fin b → Fin d → ℂ) :
    Fin a × Fin b → Fin d → Fin d → ℂ :=
  fun p s s' => if s = s' then g p s else 0

/-- Two product families with a pointwise-vanishing factor: if `f p s s' = 0`
whenever `s ≠ s'` then the only configuration pair with nonzero weight is the
diagonal one. -/
theorem prod_diagFactor_eq_zero {a b d : ℕ} (G : Fin a × Fin b → Fin d → Fin d → ℂ)
    (hG : ∀ p s s', s ≠ s' → G p s s' = 0)
    (x x' : (Fin a × Fin b) → Fin d) (hne : x ≠ x') :
    ∏ p : Fin a × Fin b, G p (x p) (x' p) = 0 := by
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ x' p := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  exact Finset.prod_eq_zero (Finset.mem_univ p) (hG p (x p) (x' p) hp)

/-- The pointwise collapse behind the identity-operator contraction: only the
diagonal configuration pair `x' = x` survives the Kronecker product. -/
theorem sum_diag_prod {a b d : ℕ} (ψ : ((Fin a × Fin b) → Fin d) → ℂ)
    (x : (Fin a × Fin b) → Fin d) :
    (∑ x' : (Fin a × Fin b) → Fin d,
        (∏ p : Fin a × Fin b, (if x p = x' p then (1 : ℂ) else 0))
          * ψ x * star (ψ x')) = ψ x * star (ψ x) := by
  rw [Finset.sum_eq_single x]
  · simp [Finset.prod_const_one]
  · intro x' _ hne
    rw [prod_diagFactor_eq_zero (fun _ s s' => if s = s' then (1 : ℂ) else 0)
      (fun _ s s' h => by simp [h]) x x' (fun h => hne h.symm)]
    ring
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- The pointwise collapse for a diagonal weight family `g`. -/
theorem sum_diag_prod_weighted {a b d : ℕ} (ψ : ((Fin a × Fin b) → Fin d) → ℂ)
    (g : Fin a × Fin b → Fin d → ℂ) (x : (Fin a × Fin b) → Fin d) :
    (∑ x' : (Fin a × Fin b) → Fin d,
        (∏ p : Fin a × Fin b, (if x p = x' p then g p (x p) else 0))
          * ψ x * star (ψ x')) = (∏ p : Fin a × Fin b, g p (x p)) * (ψ x * star (ψ x)) := by
  rw [Finset.sum_eq_single x]
  · simp
    ring
  · intro x' _ hne
    rw [prod_diagFactor_eq_zero (fun p s s' => if s = s' then g p s else 0)
      (fun _ s s' h => by simp [h]) x x' (fun h => hne h.symm)]
    ring
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- Source p. 2, Eq. (3) with the identity operator: the double-layer contraction of
the Kronecker family is the squared norm `Σ_x |Ψ(x)|²`, i.e. the normalization
appearing in the denominator `x†N̂x` of Eq. (6). -/
theorem f2_peps_identity {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    f2 (doubleK (pepsK T) (idFamily (a := a) (b := b) (d := d)))
        (pepsLegs (a := a) (b := b) (D := D))
      = ∑ x : (Fin a × Fin b) → Fin d,
          pepsAmplitude T (fun i j => x (i, j)) *
            star (pepsAmplitude T (fun i j => x (i, j))) := by
  rw [f2_doubleK]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact sum_diag_prod (fun y => pepsAmplitude T (fun i j => y (i, j))) x

/-- Source p. 2, Eq. (3) for a diagonal observable family: the expectation value is
the weighted sum `Σ_x (∏_p g_p(x_p)) |Ψ(x)|²` of the squared amplitudes.  No
off-diagonal configuration pair survives, so this is the classical-probability
form of the expectation value. -/
theorem f2_peps_diagonal {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (g : Fin a × Fin b → Fin d → ℂ) :
    f2 (doubleK (pepsK T) (diagFamily (a := a) (b := b) (d := d) g))
        (pepsLegs (a := a) (b := b) (D := D))
      = ∑ x : (Fin a × Fin b) → Fin d,
          (∏ p : Fin a × Fin b, g p (x p))
            * (pepsAmplitude T (fun i j => x (i, j))
                * star (pepsAmplitude T (fun i j => x (i, j)))) := by
  rw [f2_doubleK]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact sum_diag_prod_weighted (fun y => pepsAmplitude T (fun i j => y (i, j))) g x


/-- Source p. 2, Eq. (3): for the single-site operator `O_{h,c}` at site `z`, the
doubled tensor `E^{O_{h,c}}` built from `T` contracts to the local expectation
pairing. -/
theorem f2_peps_singleSite {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (z : Fin a × Fin b) (O : Fin d → Fin d → ℂ) :
    f2 (doubleK (pepsK T) (singleSiteFamily z O)) (pepsLegs (a := a) (b := b) (D := D)) =
      ∑ x : (Fin a × Fin b) → Fin d, ∑ x' : (Fin a × Fin b) → Fin d,
        (∏ p : Fin a × Fin b, singleSiteFamily z O p (x p) (x' p))
          * pepsAmplitude T (fun i j => x (i, j))
          * star (pepsAmplitude T (fun i j => x' (i, j))) :=
  f2_peps_doubleLayer T (singleSiteFamily z O)

end Qatlib.Papers.RenormAlg04.MainResults.Expectation

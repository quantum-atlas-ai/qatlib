/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PEPSObs16.MainResults.SourceMainResults
import Mathlib.Tactic

/-!
# PEPSObs16 — patch factorization, eqs. (6), (7), (17), (18)

Fixed source: arXiv:1606.06301v2, Appendix "Proof of Theorem 1" and the main
text right after eq. (5).

Once the boundary tensors have been disentangled, the paper writes the state as
a tensor product `|ω_*⟩ = |ω_R⟩ ⊗ |ω_P⟩` of the remainder and the patch
(eq. (17)), observes that `O_X` acts only on the patch and that `|ω_R⟩` is
normalised, and concludes

`⟨ω_*|O_X|ω_*⟩ = ⟨ω_P|O_X|ω_P⟩`

(eq. (18)). This is what makes the contraction local: no part of the PEPS
outside the patch and no global norm has to be evaluated.

This file formalises that step on an explicit finite bipartite Hilbert space.
A patch state `ψ` and a remainder state `χ` combine into the product state
`prodState ψ χ` on the product index type; the observable supported on the
patch is lifted to `O ⊗ 1`. The weight and the numerator of the expectation
both factorise, and the normalised expectation is exactly the patch
expectation. The generic expectation `expectGen` is definitionally the paper
layer's `expectation` on `Fin N → Fin d`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators

/-- The normalised expectation `⟨ψ|O|ψ⟩/⟨ψ|ψ⟩` on an arbitrary finite index
type. On `Fin N → Fin d` this is definitionally the paper layer's
`expectation`. -/
def expectGen {ι : Type*} [Fintype ι] (ψ : ι → ℂ) (O : Matrix ι ι ℂ) : ℂ :=
  (∑ y, star (ψ y) * ∑ z, O y z * ψ z) / (∑ x, star (ψ x) * ψ x)

/-- `expectGen` is the paper layer's `expectation` on the physical register. -/
theorem expectGen_eq_expectation {N d : ℕ} (ψ : PepsState N d) (O : Observable N d) :
    expectGen ψ O = expectation ψ O := rfl

/-- The product state `|ω_R⟩ ⊗ |ω_P⟩` of eq. (17): the amplitude at patch
configuration `a` and remainder configuration `b` is `ψ a * χ b`. -/
def prodState {ι κ : Type*} (ψ : ι → ℂ) (χ : κ → ℂ) : ι × κ → ℂ :=
  fun ab => ψ ab.1 * χ ab.2

/-- The lift `O ⊗ 1` of an observable supported on the patch: it acts as `O` on
the patch index and as the identity on the remainder. -/
def liftObservable {ι κ : Type*} [DecidableEq κ] (O : Matrix ι ι ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  fun a b => O a.1 b.1 * (if a.2 = b.2 then 1 else 0)

/-- The lifted observable only connects configurations with the same remainder
index (it is `O ⊗ 1`). -/
theorem liftObservable_apply_of_ne {ι κ : Type*} [DecidableEq κ]
    (O : Matrix ι ι ℂ) (a b : ι × κ) (h : a.2 ≠ b.2) : liftObservable O a b = 0 := by
  unfold liftObservable
  rw [if_neg h, mul_zero]

/-- A scalar identity used to cancel the (normalised) remainder weight:
`(a*w)/(b*w) = a/b` for `w ≠ 0`, including the degenerate case `b = 0` where
both sides vanish in Lean's total field convention. -/
theorem mul_div_mul_eq (a b w : ℂ) (hw : w ≠ 0) : a * w / (b * w) = a / b := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hb, hw]

/-- **Norm factorisation.** The total weight `⟨ω_*|ω_*⟩` of the product state is
the product of the patch and remainder weights, the denominator of eq. (18)
splitting as in the paper. -/
theorem weight_prodState {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : ι → ℂ) (χ : κ → ℂ) :
    (∑ ab : ι × κ, star (prodState ψ χ ab) * prodState ψ χ ab) =
      (∑ a, star (ψ a) * ψ a) * (∑ b, star (χ b) * χ b) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have hinner : ∀ a : ι,
      (∑ b : κ, star (prodState ψ χ (a, b)) * prodState ψ χ (a, b)) =
        (star (ψ a) * ψ a) * (∑ b, star (χ b) * χ b) := by
    intro a
    have hterm : ∀ b : κ,
        star (prodState ψ χ (a, b)) * prodState ψ χ (a, b) =
          (star (ψ a) * ψ a) * (star (χ b) * χ b) := by
      intro b
      show star (ψ a * χ b) * (ψ a * χ b) =
        (star (ψ a) * ψ a) * (star (χ b) * χ b)
      rw [star_mul]
      ring
    simp only [hterm]
    rw [Finset.mul_sum]
  simp only [hinner]
  rw [← Finset.sum_mul]

/-- **Numerator factorisation.** The numerator `⟨ω_*|O ⊗ 1|ω_*⟩` of eq. (18) is
the patch numerator times the remainder weight. -/
theorem numerator_prodState {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ψ : ι → ℂ) (χ : κ → ℂ) (O : Matrix ι ι ℂ) :
    (∑ y : ι × κ, star (prodState ψ χ y) *
        ∑ z : ι × κ, liftObservable O y z * prodState ψ χ z) =
      (∑ a, star (ψ a) * ∑ c, O a c * ψ c) * (∑ b, star (χ b) * χ b) := by
  have h1 : (∑ y : ι × κ, star (prodState ψ χ y) *
        ∑ z : ι × κ, liftObservable O y z * prodState ψ χ z) =
      ∑ a : ι, ∑ b : κ, (star (ψ a) * star (χ b)) *
        (∑ c : ι, ∑ d : κ, (O a c * (if b = d then 1 else 0)) * (ψ c * χ d)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    · show star (ψ a * χ b) = star (ψ a) * star (χ b)
      rw [star_mul]
      ring
    · rw [Finset.sum_product]
      simp only [liftObservable, prodState]
  have hinner : ∀ (a : ι) (b : κ),
      (∑ c : ι, ∑ d : κ, (O a c * (if b = d then 1 else 0)) * (ψ c * χ d)) =
        ∑ c : ι, O a c * (ψ c * χ b) := by
    intro a b
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_eq_single b]
    · rw [if_pos rfl]; ring
    · intro d _ hd; rw [if_neg (fun h : b = d => hd h.symm)]; ring
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hcore : ∀ a : ι,
      (∑ b : κ, (star (ψ a) * star (χ b)) *
          (∑ c : ι, O a c * (ψ c * χ b))) =
        (star (ψ a) * ∑ c, O a c * ψ c) * (∑ b, star (χ b) * χ b) := by
    intro a
    have hstep : ∀ b : κ,
        (∑ c : ι, O a c * (ψ c * χ b)) = (∑ c, O a c * ψ c) * χ b := by
      intro b
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun c _ => by ring)
    simp only [hstep]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [h1]
  simp only [hinner]
  simp only [hcore]
  rw [← Finset.sum_mul]

/-- **Eq. (18) (p. 6): the expectation value is local.** If the remainder state
is normalised (`⟨χ|χ⟩ ≠ 0`), the expectation of `O ⊗ 1` in the product state
equals the expectation of `O` in the patch state. In the paper's notation:
`⟨ω_*|O_X|ω_*⟩ = ⟨ω_P|O_X|ω_P⟩`. -/
theorem expectGen_lift_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ψ : ι → ℂ) (χ : κ → ℂ) (O : Matrix ι ι ℂ)
    (hχ : (∑ b, star (χ b) * χ b) ≠ 0) :
    expectGen (prodState ψ χ) (liftObservable O) = expectGen ψ O := by
  unfold expectGen
  rw [numerator_prodState, weight_prodState]
  exact mul_div_mul_eq _ _ _ hχ

/-- The paper's form of eq. (18): the global and patch expectations of a
patch-supported observable have zero difference. -/
theorem expectGen_lift_sub_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (ψ : ι → ℂ) (χ : κ → ℂ) (O : Matrix ι ι ℂ)
    (hχ : (∑ b, star (χ b) * χ b) ≠ 0) :
    expectGen (prodState ψ χ) (liftObservable O) - expectGen ψ O = 0 := by
  rw [expectGen_lift_eq ψ χ O hχ, sub_self]

/-- The exact statement used between eqs. (17) and (18): the error introduced
by replacing the full PEPS value by the patch value is precisely the
disentangling error bounded in eq. (14), and here it is zero. -/
theorem norm_expectGen_lift_sub_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (ψ : ι → ℂ) (χ : κ → ℂ) (O : Matrix ι ι ℂ)
    (hχ : (∑ b, star (χ b) * χ b) ≠ 0) :
    ‖expectGen (prodState ψ χ) (liftObservable O) - expectGen ψ O‖ = 0 := by
  rw [expectGen_lift_eq ψ χ O hχ, sub_self, norm_zero]

end Qatlib.Papers.PEPSObs16.MainResults

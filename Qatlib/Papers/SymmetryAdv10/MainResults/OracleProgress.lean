/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 8 of arXiv:1012.2112v1 (p. 7): progress change under one oracle call

The paper considers a computing-type oracle call.  Just before the call the state is

`ρ̃_t = |F|⁻¹ ∑_{f,f',x,x'} ⟨ψ^t_{f,x}|ψ^t_{f',x'}⟩ |x'⟩⟨x| ⊗ |0⟩⟨0| ⊗ |f'⟩⟨f|`   (eq. (2)),

and the progress before/after the call is

* `W̃^t = tr[Υ ρ̃_t]`   with `Υ   = ⊕_{x,y} Γ   = ∑_x |x⟩⟨x| ⊗ ∑_y |y⟩⟨y| ⊗ Γ`  (eq. (3)),
* `W^{t+1} = tr[Υ' ρ̃_t]` with `Υ'  = ⊕_{x,y} Γ_x = ∑_x |x⟩⟨x| ⊗ ∑_y |y⟩⟨y| ⊗ Γ_x` (eq. (4)).

Because the output register `O` is in the fixed state `|0⟩⟨0|` and `Υ`/`Υ'` act as the
identity on `O`, tracing out `O` multiplies both sides by `1`.  We therefore work on the
reduced input/function register `Hom × F`; this is exactly the computation in the paper's
proof ("From the definition of `Υ` and the fact that `ρ_t = tr_IO ρ̃_t`, we immediately have
`W^t = tr[Υρ̃_t]` ... `ρ̃_{t+1} = Oρ̃_tO†` ...").

The formalised content is the register reduction plus the per-step change formula

`W^{t+1} − W^t = tr[(Υ' − Υ) ρ̃_t] = ∑_x tr[(Γ_x − Γ) ρ̃_t^{(x)}]`,

which is the statement actually consumed by Theorems 10, 12 and 14 ("We have from Lemma 8
`W̃^{t+1} − W̃^t = tr[(Υ̃' − Υ̃)ρ̃_t] ≤ ‖Υ̃' − Υ̃‖ = max_x ‖Γ̃_x − Γ̃‖`").

All three theorems below are proved completely (finite-sum algebra, no axioms).
-/

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.SymmetryAdv10.MainResults.OracleProgress

noncomputable section

variable (P : Problem)

/-- The block of the reduced state `ρ̃_t` at a fixed input `x`, i.e. the function-register
marginal conditioned on the input register being in the basis state `|x⟩`. -/
def block (R : Matrix (P.Hom × P.F) (P.Hom × P.F) ℂ) (x : P.Hom) : Matrix P.F P.F ℂ :=
  fun f g => R (x, f) (x, g)

/-- The operator `Υ = ⊕_{x,y} Γ` of eq. (3): identity on the input register, `Γ` on the
function register (the output register is `|0⟩`, contributing a factor `1`). -/
def Upsilon (Γ : Matrix P.F P.F ℂ) : Matrix (P.Hom × P.F) (P.Hom × P.F) ℂ :=
  fun p q => if p.1 = q.1 then Γ p.2 q.2 else 0

/-- The operator `Υ' = ⊕_{x,y} Γ_x` of eq. (4). -/
def UpsilonPrime (Γ : Matrix P.F P.F ℂ) : Matrix (P.Hom × P.F) (P.Hom × P.F) ℂ :=
  fun p q => if p.1 = q.1 then P.GammaX Γ p.1 p.2 q.2 else 0

/-- **Lemma 8, first identity (arXiv:1012.2112v1, p. 7, eq. (3)).**
`tr[Υ ρ̃_t] = ∑_x tr[Γ ρ̃_t^{(x)}]`: the progress before the oracle call is the sum over
inputs of the function-register progress. -/
theorem trace_upsilon_mul (Γ : Matrix P.F P.F ℂ)
    (R : Matrix (P.Hom × P.F) (P.Hom × P.F) ℂ) :
    (Upsilon P Γ * R).trace = ∑ x : P.Hom, (Γ * block P R x).trace := by
  have hL : (Upsilon P Γ * R).trace
      = ∑ x : P.Hom, ∑ f : P.F, ∑ y : P.Hom, ∑ g : P.F,
          (if x = y then Γ f g else 0) * R (y, g) (x, f) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Upsilon,
      Fintype.sum_prod_type]
  have hR : (∑ x : P.Hom, (Γ * block P R x).trace)
      = ∑ x : P.Hom, ∑ f : P.F, ∑ g : P.F, Γ f g * R (x, g) (x, f) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, block]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [if_neg (Ne.symm hy), zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- **Lemma 8, second identity (arXiv:1012.2112v1, p. 7, eq. (4)).**
`tr[Υ' ρ̃_t] = ∑_x tr[Γ_x ρ̃_t^{(x)}]`: the progress after the oracle call. -/
theorem trace_upsilonPrime_mul (Γ : Matrix P.F P.F ℂ)
    (R : Matrix (P.Hom × P.F) (P.Hom × P.F) ℂ) :
    (UpsilonPrime P Γ * R).trace = ∑ x : P.Hom, (P.GammaX Γ x * block P R x).trace := by
  have hL : (UpsilonPrime P Γ * R).trace
      = ∑ x : P.Hom, ∑ f : P.F, ∑ y : P.Hom, ∑ g : P.F,
          (if x = y then P.GammaX Γ x f g else 0) * R (y, g) (x, f) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, UpsilonPrime,
      Fintype.sum_prod_type]
  have hR : (∑ x : P.Hom, (P.GammaX Γ x * block P R x).trace)
      = ∑ x : P.Hom, ∑ f : P.F, ∑ g : P.F,
          P.GammaX Γ x f g * R (x, g) (x, f) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, block]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [if_neg (Ne.symm hy), zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- **Lemma 8, change formula (arXiv:1012.2112v1, p. 7, used on p. 9).**
The change of the progress function during one computing-type oracle call is
`W^{t+1} − W^t = tr[(Υ' − Υ)ρ̃_t] = ∑_x tr[(Γ_x − Γ) ρ̃_t^{(x)}]`.

This is the exact equality from which the paper derives the per-query bound
`W^{t+1} − W^t ≤ max_x ‖Γ_x − Γ‖` (Theorem 10, p. 9, and Theorem 14, p. 11). -/
theorem lemma8_progress_change (Γ : Matrix P.F P.F ℂ)
    (R : Matrix (P.Hom × P.F) (P.Hom × P.F) ℂ) :
    (UpsilonPrime P Γ * R).trace - (Upsilon P Γ * R).trace =
      ∑ x : P.Hom, ((P.GammaX Γ x - Γ) * block P R x).trace := by
  rw [trace_upsilonPrime_mul, trace_upsilon_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.sub_mul, Matrix.trace_sub]

end
end OracleProgress

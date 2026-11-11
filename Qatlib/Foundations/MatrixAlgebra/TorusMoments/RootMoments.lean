/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Root-of-unity moments and phase twists

The module proves orthogonality of root-of-unity characters on finite cyclic grids and their
products. `monomialValue` extends this calculation to monomials, and the polynomial lemmas show
that pairwise evaluation sums are unchanged by coordinatewise unit phases when every exponent is
smaller than the root order.

`polynomialDensity` packages the averaged outer-product entries of a polynomial family;
`polynomialDensity_twist` and `polynomialDensity_cyclicPhase` establish their phase invariance.
These finite moment identities are used in the phase-based setting of [TangWright2025].

## Main statements

* `tensor_character_sum`: orthogonality of characters on a product of cyclic groups.
* `polynomial_density_sum_invariant`: bounded-exponent polynomial pair sums are invariant under
  unit phase twists.
* `polynomialDensity_twist`: phase invariance of the averaged polynomial matrix.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.TorusMoments

/-- A primitive complex root of positive order has norm one. -/
theorem primitive_norm {q : ℕ} (hq : 0<q) (omega : ℂ) (hw : IsPrimitiveRoot omega q) :
    ‖omega‖=1 := Complex.norm_eq_one_of_pow_eq_one hw.pow_eq_one hq.ne'

/-- The conjugate of any natural power of a primitive root of positive order, multiplied by that
power, equals one. -/
theorem phase_star_mul {q : ℕ} (hq : 0<q) (omega : ℂ) (hw : IsPrimitiveRoot omega q)
    (a : ℕ) : star (omega^a)*(omega^a)=1 := by
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,norm_pow,
    primitive_norm hq omega hw]
  simp

/-- Characters indexed by `Fin q` are orthogonal on the powers of a primitive `q`th root, with
diagonal sum `q`. -/
theorem root_character_sum {q : ℕ} (hq : 0<q) (omega : ℂ)
    (hw : IsPrimitiveRoot omega q) (a b : Fin q) :
    (∑u : Fin q,(omega^u.val)^a.val*star ((omega^u.val)^b.val))=
      if a=b then (q:ℂ) else 0 := by
  classical
  let eta := omega^a.val*star (omega^b.val)
  have hp (u : Fin q) : (omega^u.val)^a.val*star ((omega^u.val)^b.val)=eta^u.val := by
    dsimp [eta]
    rw [mul_pow]
    congr 1
    · simp only [← pow_mul,Nat.mul_comm]
    · rw [← map_pow]
      congr 1
      simp only [← pow_mul,Nat.mul_comm]
  simp_rw [hp]
  by_cases hab : a=b
  · subst b
    have he : eta=1 := by
      dsimp [eta]
      rw [mul_comm]
      exact phase_star_mul hq omega hw a.val
    simp [he]
  · rw [if_neg hab]
    have he : eta≠1 := by
      intro h
      have ht := congrArg (fun z : ℂ => z*omega^b.val) h
      have hh : omega^a.val=omega^b.val := by
        simpa only [eta,mul_assoc,phase_star_mul hq omega hw b.val,mul_one,one_mul] using ht
      exact hab (Fin.ext (hw.pow_inj a.isLt b.isLt hh))
    have heq : eta^q=1 := by
      dsimp [eta]
      rw [mul_pow,← map_pow]
      have h1 : (omega^a.val)^q=1 := by
        rw [← pow_mul,Nat.mul_comm,pow_mul,hw.pow_eq_one,one_pow]
      have h2 : (omega^b.val)^q=1 := by
        rw [← pow_mul,Nat.mul_comm,pow_mul,hw.pow_eq_one,one_pow]
      simp [h1,h2]
    rw [Fin.sum_univ_eq_sum_range]
    have hs := geom_sum_mul eta q
    rw [heq,sub_self] at hs
    exact (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr he)

/-- Product characters on a `d`-fold cyclic grid are orthogonal, with diagonal sum `q^d`. -/
theorem tensor_character_sum {q d : ℕ} (hq : 0<q) (omega : ℂ)
    (hw : IsPrimitiveRoot omega q) (a b : Fin d → Fin q) :
    (∑u : Fin d → Fin q,∏i : Fin d,(omega^(u i).val)^(a i).val *
      star ((omega^(u i).val)^(b i).val)) =
      if a=b then (q:ℂ)^d else 0 := by
  classical
  rw [← Fintype.prod_sum (fun (i : Fin d) (u : Fin q)=>
    (omega^u.val)^(a i).val * star ((omega^u.val)^(b i).val))]
  simp_rw [root_character_sum hq omega hw]
  by_cases hab : a=b
  · subst b
    simp
  · rw [if_neg hab]
    have hex : ∃i,a i≠b i := by
      by_contra hn
      push Not at hn
      exact hab (funext hn)
    obtain ⟨i,hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The value of a coordinate monomial with natural exponents at a complex coordinate vector. -/
def monomialValue {d : ℕ} (z : Fin d → ℂ) (a : Fin d → ℕ) : ℂ :=
  ∏i,z i ^ a i

/-- Evaluating a monomial on a coordinatewise product factors into the product of the two
monomial values. -/
theorem monomialValue_twist {d : ℕ} (D z : Fin d → ℂ) (a : Fin d → ℕ) :
    monomialValue (fun i=>D i*z i) a=monomialValue D a*monomialValue z a := by
  simp only [monomialValue,mul_pow,Finset.prod_mul_distrib]

/-- A monomial evaluated on unit-modulus coordinates has norm one. -/
theorem monomialValue_norm {d : ℕ} (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (a : Fin d → ℕ) : ‖monomialValue D a‖=1 := by
  simp [monomialValue,norm_prod,norm_pow,hD]

/-- A complex number of norm one multiplied by its conjugate equals one. -/
theorem unit_phase_mul_star (z : ℂ) (hz : ‖z‖=1) : z*star z=1 := by
  rw [mul_comm,Complex.star_def,← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq,hz]
  norm_num

/-- For exponents in `Fin q`, the cyclic-grid sum of a monomial times a conjugate monomial is
unchanged by coordinatewise unit phases. -/
theorem twisted_monomial_sum {q d : ℕ} (hq : 0<q) (omega : ℂ)
    (hw : IsPrimitiveRoot omega q) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (a b : Fin d → Fin q) :
    (∑u : Fin d → Fin q,
      monomialValue (fun i=>D i*omega^(u i).val) (fun i=>(a i).val)*
      star (monomialValue (fun i=>D i*omega^(u i).val) (fun i=>(b i).val))) =
    ∑u : Fin d → Fin q,
      monomialValue (fun i=>omega^(u i).val) (fun i=>(a i).val)*
      star (monomialValue (fun i=>omega^(u i).val) (fun i=>(b i).val)) := by
  classical
  have hsum : (∑u : Fin d → Fin q,
      monomialValue (fun i=>omega^(u i).val) (fun i=>(a i).val)*
      star (monomialValue (fun i=>omega^(u i).val) (fun i=>(b i).val))) =
      if a=b then (q:ℂ)^d else 0 := by
    simpa only [monomialValue,star_prod,← Finset.prod_mul_distrib] using
      tensor_character_sum hq omega hw a b
  simp_rw [monomialValue_twist,star_mul]
  calc
    _ = (monomialValue D (fun i=>(a i).val)*star (monomialValue D (fun i=>(b i).val))) *
        (∑u : Fin d → Fin q,
          monomialValue (fun i=>omega^(u i).val) (fun i=>(a i).val)*
          star (monomialValue (fun i=>omega^(u i).val) (fun i=>(b i).val))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by
      rw [hsum]
      split_ifs with hab
      · subst b
        rw [unit_phase_mul_star _ (monomialValue_norm D hD _),one_mul]
      · simp

/-- If each natural exponent is less than `q`, twisting a primitive-root grid by unit phases
leaves the corresponding monomial pair sum unchanged. -/
theorem twisted_monomial_sum_nat {q d : ℕ} (hq : 0<q) (omega : ℂ)
    (hw : IsPrimitiveRoot omega q) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (a b : Fin d → ℕ) (ha : ∀i,a i<q) (hb : ∀i,b i<q) :
    (∑u : Fin d → Fin q,
      monomialValue (fun i=>D i*omega^(u i).val) a *
      star (monomialValue (fun i=>D i*omega^(u i).val) b)) =
    ∑u : Fin d → Fin q,
      monomialValue (fun i=>omega^(u i).val) a *
      star (monomialValue (fun i=>omega^(u i).val) b) :=
  twisted_monomial_sum hq omega hw D hD (fun i=>⟨a i,ha i⟩) (fun i=>⟨b i,hb i⟩)

/-- A polynomial value times a conjugate polynomial value expands as a double sum over their
supports, with coefficient pairs multiplying monomial pairs. -/
theorem polynomial_density_expand {d : ℕ} (P Q : MvPolynomial (Fin d) ℂ)
    (z : Fin d → ℂ) :
    MvPolynomial.eval z P * star (MvPolynomial.eval z Q) =
      ∑a ∈ P.support,∑b ∈ Q.support,
        (P.coeff a*star (Q.coeff b)) * (monomialValue z a * star (monomialValue z b)) := by
  classical
  rw [MvPolynomial.eval_eq',MvPolynomial.eval_eq',star_sum]
  simp_rw [star_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [monomialValue]
  ring

/-- If every exponent in both polynomial supports is less than `q`, their evaluation pair sum
over a primitive-root grid is invariant under coordinatewise unit phases. -/
theorem polynomial_density_sum_invariant {q d : ℕ} (hq : 0<q) (omega : ℂ)
    (hw : IsPrimitiveRoot omega q) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (P Q : MvPolynomial (Fin d) ℂ)
    (hP : ∀a ∈ P.support,∀i,a i<q) (hQ : ∀b ∈ Q.support,∀i,b i<q) :
    (∑u : Fin d → Fin q,
      MvPolynomial.eval (fun i=>D i*omega^(u i).val) P *
      star (MvPolynomial.eval (fun i=>D i*omega^(u i).val) Q)) =
    ∑u : Fin d → Fin q,
      MvPolynomial.eval (fun i=>omega^(u i).val) P *
      star (MvPolynomial.eval (fun i=>omega^(u i).val) Q) := by
  classical
  have hs (z : (Fin d → Fin q) → Fin d → ℂ) :
      (∑u : Fin d → Fin q,MvPolynomial.eval (z u) P * star (MvPolynomial.eval (z u) Q)) =
        ∑a ∈ P.support,∑b ∈ Q.support,
          (P.coeff a*star (Q.coeff b)) *
          ∑u : Fin d → Fin q,monomialValue (z u) a * star (monomialValue (z u) b) := by
    simp_rw [polynomial_density_expand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.mul_sum _ _ _).symm
  rw [hs,hs]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [twisted_monomial_sum_nat hq omega hw D hD a b (hP a ha) (hQ b hb)]

/-- The matrix of averaged products of polynomial evaluations and their complex conjugates over
the finite index grid. -/
def polynomialDensity {q d : ℕ} {O : Type*} (P : O → MvPolynomial (Fin d) ℂ)
    (z : (Fin d → Fin q) → Fin d → ℂ) : Matrix O O ℂ := fun i j=>
  (Fintype.card (Fin d → Fin q) : ℂ)⁻¹ * ∑u : Fin d → Fin q,
    MvPolynomial.eval (z u) (P i)*star (MvPolynomial.eval (z u) (P j))

/-- For a polynomial family with all coordinate exponents less than `q`, twisting the
primitive-root grid by unit phases leaves `polynomialDensity` unchanged. -/
theorem polynomialDensity_twist {q d : ℕ} {O : Type*} (hq : 0<q) (omega : ℂ)
    (hw : IsPrimitiveRoot omega q) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (P : O → MvPolynomial (Fin d) ℂ)
    (hP : ∀o,∀a ∈ (P o).support,∀i,a i<q) :
    polynomialDensity (q := q) P (fun u i=>D i*omega^(u i).val)=
      polynomialDensity (q := q) P (fun u i=>omega^(u i).val) := by
  ext i j
  unfold polynomialDensity
  rw [polynomial_density_sum_invariant hq omega hw D hD (P i) (P j) (hP i) (hP j)]

/-- The complex exponential `exp (2 * π * I / q)`. -/
def cyclicPhase (q : ℕ) : ℂ := Complex.exp (2*Real.pi*Complex.I/(q : ℂ))

/-- For positive `q` and polynomial coordinate exponents less than `q`, the averaged polynomial
matrix built from `cyclicPhase q` is unchanged by coordinatewise unit phases. -/
theorem polynomialDensity_cyclicPhase {q d : ℕ} {O : Type*} (hq : 0<q)
    (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1) (P : O → MvPolynomial (Fin d) ℂ)
    (hP : ∀o,∀a ∈ (P o).support,∀i,a i<q) :
    polynomialDensity (q := q) P (fun u i=>D i*(cyclicPhase q)^(u i).val)=
      polynomialDensity (q := q) P (fun u i=>(cyclicPhase q)^(u i).val) :=
  polynomialDensity_twist hq (cyclicPhase q)
    (Complex.isPrimitiveRoot_exp q hq.ne') D hD P hP

end Qatlib.Foundations.MatrixAlgebra.TorusMoments

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Qatlib.Papers.QSPIto26.MainResults.Lemma5.MQSPNonzero

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6 — parity of the per-variable degrees

Ito--Mori--Sakamoto--Fujii, fixed arXiv:2410.02332v3, Lemma 6 (Appendix A, p. 12),
Eqs. (45)--(47).

Lemma 6. If `(P,Q)` is constructed by m-variable M-QSP in `n` steps via angle parameters
`(φ_0,…,φ_n)` and index parameters `(s_1,…,s_n)`, then for all `j`,
`deg_{a_j} P ≡ |{k | s_k = j}| (mod 2)`; in particular `deg P ≡ n (mod 2)`.

The composition below is complete given the same lex-leading-monomial interface
hypothesis as Lemmas 4--5 (used for `P ≠ 0` via Lemma 5, which ensures the support of
`P` is nonempty so that the supremum defining `degVar` is attained). The sign-change
substitution `a_j ↦ -a_j` is realized as the `ℂ`-algebra homomorphism obtained from
`AddMonoidAlgebra.lift`; applying it entrywise to the word matrix multiplies the whole
word by `(-1)^{c_j}`, where `c_j` counts the factors acting on `a_j`. Comparing
coefficients on the support of `P` then forces `(-1)^{k_j} = (-1)^{c_j}` for every
exponent vector `k` in the support, which transfers the parity of `c_j` to `degVar j P`.
The total degree statement follows by summing the per-variable counts, which telescope
to `n`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma6

open Qatlib.Papers.QSPIto26.MainResults.Core

/-! ### Monomial and scalar lemmas -/

/-- The monomial at the zero exponent vector is the unit. -/
lemma mono_zero {m : ℕ} : mono (0 : ExpVec m) = 1 := by
  simp [mono, AddMonoidAlgebra.one_def]

/-- Multiplying monomials adds exponent vectors. -/
lemma mono_mul {m : ℕ} (x y : ExpVec m) : mono x * mono y = mono (x + y) := by
  simp [mono, AddMonoidAlgebra.single_mul_single]

/-- A scalar multiple of the unit is the corresponding constant. -/
lemma smul_one_eq_C' {m : ℕ} (c : ℂ) : c • (1 : MLaurent m) = C' c := by
  rw [← Lemma3.C'_smul, mul_one]

/-- Scaling by `-1 : ℂ` is negation. -/
lemma neg_one_smul {m : ℕ} (X : MLaurent m) : (-1 : ℂ) • X = -X := by
  ext k
  simp

/-- Scaling a 2×2 matrix by `-1 : ℂ` is negation. -/
lemma neg_one_smul_matrix {m : ℕ} (M : Matrix (Fin 2) (Fin 2) (MLaurent m)) :
    (-1 : ℂ) • M = -M := by
  ext i j
  simp [Matrix.smul_apply, Matrix.neg_apply]

/-! ### The sign-change substitution `a_j ↦ -a_j` -/

/-- The image of the monomial `a^k` under the substitution `a_j ↦ -a_j`. -/
def negAtMon {m : ℕ} (j : Fin m) (k : ExpVec m) : MLaurent m :=
  (-1 : ℂ)^(k j) • mono k

/-- The substitution on monomial generators, as a monoid hom from the multiplicative
wrapping of the exponent group. -/
def negAtHom {m : ℕ} (j : Fin m) : Multiplicative (ExpVec m) →* MLaurent m where
  toFun k := negAtMon j k.toAdd
  map_one' := by
    simp [negAtMon, toAdd_one, mono_zero]
  map_mul' a b := by
    simp only [toAdd_mul, negAtMon]
    rw [smul_mul_smul, mono_mul, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    rfl

/-- `negAtHom` on the image of `ofAdd` is `negAtMon`. -/
lemma negAtHom_ofAdd {m : ℕ} (j : Fin m) (a : ExpVec m) :
    negAtHom j (Multiplicative.ofAdd a) = negAtMon j a := rfl

/-- The substitution `a_j ↦ -a_j` as a `ℂ`-algebra homomorphism. -/
def substNeg {m : ℕ} (j : Fin m) : MLaurent m →ₐ[ℂ] MLaurent m :=
  AddMonoidAlgebra.lift ℂ (MLaurent m) (ExpVec m) (negAtHom j)

/-- `substNeg` sends a monomial to its sign-twisted copy. -/
lemma substNeg_mono {m : ℕ} (j : Fin m) (k : ExpVec m) : substNeg j (mono k) = negAtMon j k := by
  simp only [substNeg, mono, AddMonoidAlgebra.lift_single, negAtHom_ofAdd]
  exact one_smul _ _

/-- `substNeg` fixes constants. -/
lemma substNeg_C' {m : ℕ} (j : Fin m) (c : ℂ) : substNeg j (C' c) = C' c := by
  have h0 : negAtMon j (0 : ExpVec m) = 1 := by
    simp [negAtMon, mono_zero]
  simp only [substNeg, C', AddMonoidAlgebra.lift_single, negAtHom_ofAdd, h0]
  exact smul_one_eq_C' c

/-- `substNeg` negates `a_j`. -/
lemma substNeg_var {m : ℕ} (j : Fin m) : substNeg j (var j) = -var j := by
  rw [var, substNeg_mono, negAtMon, Pi.single_apply, if_pos rfl, zpow_one]
  exact neg_one_smul _

/-- `substNeg` negates `a_j^{-1}`. -/
lemma substNeg_varInv {m : ℕ} (j : Fin m) : substNeg j (varInv j) = -varInv j := by
  rw [varInv, substNeg_mono, negAtMon, Pi.single_apply, if_pos rfl, zpow_neg, zpow_one]
  have h1 : ((-1 : ℂ))⁻¹ = -1 := by norm_num
  rw [h1]
  exact neg_one_smul _

/-- `substNeg` fixes `a_{j'}` for `j' ≠ j`. -/
lemma substNeg_var_of_ne {m : ℕ} (j j' : Fin m) (h : j ≠ j') : substNeg j (var j') = var j' := by
  rw [var, substNeg_mono, negAtMon, Pi.single_apply, if_neg h, zpow_zero, one_smul]

/-- `substNeg` fixes `a_{j'}^{-1}` for `j' ≠ j`. -/
lemma substNeg_varInv_of_ne {m : ℕ} (j j' : Fin m) (h : j ≠ j') :
    substNeg j (varInv j') = varInv j' := by
  rw [varInv, substNeg_mono, negAtMon, Pi.single_apply, if_neg h, zpow_zero, one_smul]

/-- Coefficient of the sign-twisted monomial. -/
lemma negAtMon_apply {m : ℕ} (j : Fin m) (b k : ExpVec m) :
    (negAtMon j b).coeff k = if k = b then (-1 : ℂ)^(b j) else 0 := by
  by_cases h : k = b
  · subst h
    simp [negAtMon, mono, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]
  · simp [negAtMon, mono, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm, h]

/-! ### Action on the operators -/

/-- `substNeg` negates the signal operator of its own variable and fixes the others. -/
lemma substNeg_signalOp {m : ℕ} (j j' : Fin m) :
    RingHom.mapMatrix (substNeg j).toRingHom (signalOp j')
      = if j' = j then -signalOp j' else signalOp j' := by
  by_cases h : j' = j
  · subst h
    rw [if_pos rfl, RingHom.mapMatrix_apply]
    ext i i''
    fin_cases i <;> fin_cases i'' <;>
      simp [Matrix.cons_val', signalOp, Matrix.map_apply, substNeg_C',
        substNeg_var, substNeg_varInv, sub_eq_add_neg]
    all_goals simp only [Lemma3.C'_smul]
    all_goals simp
    all_goals ring
  · rw [if_neg h, RingHom.mapMatrix_apply]
    ext i i''
    fin_cases i <;> fin_cases i'' <;>
      simp [Matrix.map_apply, Matrix.cons_val', signalOp, substNeg_C',
        substNeg_var_of_ne _ _ (Ne.symm h), substNeg_varInv_of_ne _ _ (Ne.symm h)]

/-- `substNeg` fixes the phase operators (they are constant). -/
lemma substNeg_phaseOp {m : ℕ} (j : Fin m) (φ : ℝ) :
    RingHom.mapMatrix (substNeg j).toRingHom (phaseOp φ : Matrix (Fin 2) (Fin 2) (MLaurent m))
      = phaseOp φ := by
  rw [RingHom.mapMatrix_apply]
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [Matrix.map_apply, Matrix.cons_val', phaseOp, substNeg_C']

/-- The word composed with `a_j ↦ -a_j` picks up the sign `(-1)^{c_j}`,
where `c_j` counts the word factors acting on `a_j`. -/
lemma substNeg_wordMatrix {m n : ℕ} (j : Fin m) (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) :
    RingHom.mapMatrix (substNeg j).toRingHom (wordMatrix n φ s)
      = (-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ)
          • (wordMatrix n φ s : Matrix (Fin 2) (Fin 2) (MLaurent m)) := by
  classical
  have key : ∀ L : List (Fin m × ℝ),
      RingHom.mapMatrix (substNeg j).toRingHom ((L.map (fun p => signalOp p.1 * phaseOp p.2)).prod)
        = (-1 : ℂ)^((L.filter (fun p => p.1 = j)).length : ℤ)
            • ((L.map (fun p => signalOp p.1 * phaseOp p.2)).prod
                : Matrix (Fin 2) (Fin 2) (MLaurent m)) := by
    intro L
    induction L with
    | nil =>
        simp
    | cons p L ih =>
        have hsign : RingHom.mapMatrix (substNeg j).toRingHom (signalOp p.1 * phaseOp p.2)
            = ((if p.1 = j then (-1 : ℂ) else 1)
                • (signalOp p.1 * phaseOp p.2 : Matrix (Fin 2) (Fin 2) (MLaurent m))) := by
          by_cases hp : p.1 = j
          · subst hp
            rw [map_mul, substNeg_signalOp, substNeg_phaseOp, if_pos rfl, if_pos rfl, neg_mul,
              ← neg_one_smul_matrix]
          · rw [map_mul, substNeg_signalOp, substNeg_phaseOp, if_neg hp, if_neg hp, one_smul]
        have hlen : (((p :: L).filter (fun q => q.1 = j)).length : ℤ)
            = ((L.filter (fun q => q.1 = j)).length : ℤ)
              + (if p.1 = j then (1 : ℤ) else 0) := by
          by_cases hp : p.1 = j <;> simp [hp]
        rw [List.map_cons, List.prod_cons, map_mul, hsign, ih,
          smul_mul_assoc, mul_smul_comm, smul_smul, hlen]
        by_cases hp : p.1 = j
        · rw [if_pos hp, if_pos hp, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
          congr 1
          ring
        · rw [if_neg hp, if_neg hp, add_zero, one_mul]
  have hlist : (List.ofFn fun k : Fin n => signalOp (s k) * phaseOp (φ k.succ))
      = (List.ofFn fun k : Fin n => (s k, φ k.succ)).map
          (fun p => signalOp p.1 * phaseOp p.2) := by
    rw [List.map_ofFn]
    congr 1
  have ht := key (List.ofFn fun k : Fin n => (s k, φ k.succ))
  have hlenb : ((List.ofFn fun k : Fin n => (s k, φ k.succ)).filter (fun p => p.1 = j)).length
      = (Finset.univ.filter (fun k : Fin n => s k = j)).card := by
    have h1 : (List.ofFn fun k : Fin n => (s k, φ k.succ))
        = (List.finRange n).map (fun k : Fin n => (s k, φ k.succ)) := by
      rw [show List.finRange n = List.ofFn (id : Fin n → Fin n) from rfl, List.map_ofFn]
      rfl
    have hgen : ∀ (l : List (Fin n)) (g : Fin n → Fin m × ℝ),
        (l.map g).filter (fun p => p.1 = j) = (l.filter (fun k => (g k).1 = j)).map g := by
      intro l g
      induction l with
      | nil => simp
      | cons a l ih =>
          by_cases h : (g a).1 = j <;> simp [h, ih]
    rw [h1, hgen _ _, List.length_map, ← List.toFinset_card_of_nodup
      ((List.nodup_finRange n).filter (fun k => s k = j))]
    congr 1
    ext x
    simp [Finset.mem_filter]
  simp only [wordMatrix, hlist]
  rw [map_mul, substNeg_phaseOp, ht, mul_smul_comm, hlenb]

/-! ### Parity bookkeeping -/

/-- Negative one to integer powers determines the exponent modulo two. -/
lemma neg_one_zpow_inj {a b : ℤ} (h : (-1 : ℂ)^a = (-1 : ℂ)^b) : a % 2 = b % 2 := by
  have h0 : (-1 : ℂ) ≠ 0 := by norm_num
  have hd : (-1 : ℂ)^(a - b) = 1 := by
    rw [zpow_sub₀ h0, h, div_self (zpow_ne_zero _ h0)]
  rcases Int.even_or_odd (a - b) with ⟨q, hq⟩ | ⟨q, hq⟩
  · omega
  · exfalso
    simp only [hq, zpow_add₀ h0, zpow_mul, zpow_two, one_zpow, zpow_one, neg_mul_neg,
      one_mul] at hd
    exact absurd hd (by norm_num)

/-! ### Lemma 6 -/

/-- Lemma 6 (arXiv:2410.02332v3, p. 12, Eqs. (45)--(47)): for every variable `a_j`
the degree of `P` in that variable has the parity of the number of word factors acting
on `a_j`, and the total degree of `P` has the parity of the word length `n`.
The proof is complete given the lex-leading-monomial interface hypothesis `hlead`
of Lemmas 4--5 (used through Lemma 5 to ensure `P ≠ 0`). -/
theorem lemma6_parity {m n : ℕ} (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) (P Q : MLaurent m)
    (hw : wordMatrix n φ s = !![P, Q; -starOp Q, starOp P])
    (hlead : ∀ (X : MLaurent m) (j : Fin m), X ≠ 0 →
      degVar j (X * starOp X) = 2 * degVar j X) :
    (∀ j : Fin m, degVar j P % 2 = (Finset.univ.filter (fun k : Fin n => s k = j)).card % 2)
      ∧ degTotal P % 2 = n % 2 := by
  classical
  have hP0 : P ≠ 0 := Lemma5.lemma5_nonzero P Q ⟨φ, s, hw⟩ hlead
  have hne : P.coeff.support.Nonempty := by
    by_contra hcon
    apply hP0
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hcon)
  have hdeg : ∀ j : Fin m,
      degVar j P % 2 = (Finset.univ.filter (fun k : Fin n => s k = j)).card % 2 := by
    intro j
    have h1 := substNeg_wordMatrix j φ s
    rw [hw] at h1
    have h2 : RingHom.mapMatrix (substNeg j).toRingHom (!![P, Q; -starOp Q, starOp P])
        = !![substNeg j P, substNeg j Q; -(substNeg j (starOp Q)), substNeg j (starOp P)] := by
      rw [RingHom.mapMatrix_apply]
      ext i j'
      fin_cases i <;> fin_cases j' <;>
        simp [Matrix.map_apply, Matrix.cons_val']
    have h2b := congrFun (congrFun (h2.symm.trans h1) 0) 0
    simp only [Matrix.smul_apply] at h2b
    have hPe : substNeg j P
        = (-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ) • P := h2b
    have hcoe : ∀ k : ExpVec m, (substNeg j P).coeff k = P.coeff k * (-1 : ℂ)^(k j) := by
      intro k
      have hl : substNeg j P
          = P.coeff.sum (fun a b => b • negAtHom j (Multiplicative.ofAdd a)) :=
        AddMonoidAlgebra.lift_apply _ _
      rw [hl]
      simp only [negAtHom_ofAdd]
      have hsa : ((P.coeff.sum (fun a b => b • negAtMon j a) : MLaurent m)).coeff k
          = P.coeff.sum (fun a b => (b • negAtMon j a).coeff k) := by
        rw [AddMonoidAlgebra.coeff_finsuppSum]
        exact Finsupp.sum_apply
      rw [hsa, Finsupp.sum_eq_single k]
      · simp [negAtMon_apply]
      · intro b _ hbk
        have hbk' : (negAtMon j b).coeff k = 0 := by simp [negAtMon_apply, Ne.symm hbk]
        simp [hbk']
      · intro h0
        simp only [zero_smul]
        rfl
    have hA : ∀ k ∈ P.coeff.support, (-1 : ℂ)^(k j)
        = (-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ) := by
      intro k hk
      have hlk0 := congrArg (fun X : MLaurent m => X.coeff k) hPe
      have hlk : ((substNeg j) P).coeff k
          = ((-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ) • P).coeff k := hlk0
      rw [hcoe k] at hlk
      have hsmul : ((-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ) • P).coeff k
          = (-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ) * P.coeff k := by
        simp
      rw [hsmul] at hlk
      rw [mul_comm ((-1 : ℂ)^((Finset.univ.filter (fun k : Fin n => s k = j)).card : ℤ)) (P.coeff k)]
        at hlk
      exact mul_left_cancel₀ (Finsupp.mem_support_iff.mp hk) hlk
    obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup P.coeff.support hne (fun k => Int.natAbs (k j))
    rw [degVar, hsup]
    have hz := neg_one_zpow_inj (hA k hk)
    omega
  refine ⟨hdeg, ?_⟩
  have hsum : ∑ i : Fin m, (Finset.univ.filter (fun k : Fin n => s k = i)).card = n := by
    have hcard : ∀ i : Fin m, (Finset.univ.filter (fun k => s k = i)).card
        = ∑ k ∈ Finset.univ, if s k = i then (1 : ℕ) else 0 := by
      intro i
      rw [← Finset.sum_filter (fun k => s k = i) (fun _ => (1 : ℕ)), Finset.card_eq_sum_ones]
    rw [Finset.sum_congr rfl (fun i _ => hcard i), Finset.sum_comm]
    have hinner : ∀ k : Fin n, (∑ i : Fin m, if s k = i then (1 : ℕ) else 0) = 1 := by
      intro k
      rw [Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun k _ => hinner k)]
    simp
  have hsummod : ∀ (F : Finset (Fin m)) (f g : Fin m → ℕ),
      (∀ i ∈ F, f i % 2 = g i % 2) → (∑ i ∈ F, f i) % 2 = (∑ i ∈ F, g i) % 2 := by
    intro F
    induction F using Finset.induction with
    | empty => intro f g _; simp
    | insert x F hx ih =>
        intro f g hfg
        simp only [Finset.sum_insert hx]
        rw [Nat.add_mod, Nat.add_mod, hfg x (Finset.mem_insert_self _ _),
          ih f g (fun i hi => hfg i (Finset.mem_insert_of_mem hi))]
        omega
  rw [degTotal, hsummod Finset.univ (fun i => degVar i P)
    (fun i => (Finset.univ.filter (fun k => s k = i)).card) (fun i _ => hdeg i), hsum]

end Qatlib.Papers.QSPIto26.MainResults.Lemma6

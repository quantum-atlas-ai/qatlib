/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenHidShift05.MainResults.MatrixSumCount
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Integer-lattice encoding of matrix-sum solutions (source §4, Lemma 4)

Fixed source: A. M. Childs and W. van Dam, *Quantum algorithm for a generalized
hidden shift problem*, arXiv:quant-ph/0507190v1, §4 (Eqs. 34–39) and the
Appendix proof of Lemma 4.

The source turns the modular equation `b · x = w mod N` into the integer
equation `(b, lam) · (x, N) = w` in `k + 1` variables, observes that `lam` is
determined by `b`, that the integer solutions form a coset of the kernel
lattice, and that a solution exists exactly when `gcd(x₁, …, x_k, N)` divides
`w`.  Those statements are proved here for natural representatives
`x : Fin k → ℕ`, `w : ℕ` and integer coefficients `b : Fin k → ℤ`.

The file also proves the converse half of the fibre-size statement of Lemma 4
(`gcd(b₁, …, b_k, N)` divides the right-hand side whenever the equation is
solvable), which together with `card_dot_eq_of_dvd` gives the "nonempty fibre
iff divisibility" characterisation.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.GenHidShift05.FiberGeometry

open Qatlib.Papers.GenHidShift05.MainResults

/-- The integer matrix-sum form `b · x = ∑ i, b i * x i` for integer
coefficients and natural representatives. -/
def intDot {k : ℕ} (b : Fin k → ℤ) (x : Fin k → ℕ) : ℤ :=
  ∑ i, b i * (x i : ℤ)

/-- The extended integer equation `b · x + lam N = w` of source §4: the extra
variable `lam` records the quotient by `N`. -/
def extDot {k : ℕ} (b : Fin k → ℤ) (lam : ℤ) (x : Fin k → ℕ) (N : ℕ) : ℤ :=
  intDot b x + lam * (N : ℤ)

/-- The modular equation and its integer extension agree: `b · x = w mod N`
holds exactly when there is an integer `lam` with `b · x + lam N = w`.  This is the
bijection of source §4 between extended integer solutions and modular
solutions. -/
theorem modEq_iff_exists_int {k N : ℕ} (_hN : 0 < N) (b : Fin k → ℤ) (x : Fin k → ℕ)
    (w : ℕ) :
    ((intDot b x : ZMod N) = (w : ZMod N)) ↔ ∃ lam : ℤ, extDot b lam x N = (w : ℤ) := by
  have hw : ((w : ZMod N)) = (((w : ℤ)) : ZMod N) := by push_cast; rfl
  rw [hw, ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    unfold extDot
    linarith
  · rintro ⟨lam, hlam⟩
    refine ⟨lam, ?_⟩
    unfold extDot at hlam
    linarith

/-- The multiplier `lam` is unique: the extended equation determines it. -/
theorem ext_lambda_unique {k N : ℕ} (hN : 0 < N) (b : Fin k → ℤ) (x : Fin k → ℕ)
    (w : ℕ) {lam lam' : ℤ} (h : extDot b lam x N = (w : ℤ))
    (h' : extDot b lam' x N = (w : ℤ)) : lam = lam' := by
  unfold extDot at h h'
  have hmul : (lam - lam') * (N : ℤ) = 0 := by linarith
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rcases Int.mul_eq_zero.mp hmul with h0 | h0
  · omega
  · exact absurd h0 hN'

/-- A modular solution is an integer solution after choosing the multiplier
`lam`; this is the inverse direction of the source bijection. -/
def modToExt {k N : ℕ} (hN : 0 < N) (x : Fin k → ℕ) (w : ℕ)
    (q : {b : Fin k → ℤ // (intDot b x : ZMod N) = (w : ZMod N)}) :
    {p : (Fin k → ℤ) × ℤ // extDot p.1 p.2 x N = (w : ℤ)} :=
  ⟨(q.1, Classical.choose ((modEq_iff_exists_int hN q.1 x w).mp q.2)),
    Classical.choose_spec ((modEq_iff_exists_int hN q.1 x w).mp q.2)⟩

/-- Projecting an extended integer solution to its first `k` coordinates. -/
def extProj {k N : ℕ} (hN : 0 < N) (x : Fin k → ℕ) (w : ℕ) :
    {p : (Fin k → ℤ) × ℤ // extDot p.1 p.2 x N = (w : ℤ)} →
      {b : Fin k → ℤ // (intDot b x : ZMod N) = (w : ZMod N)} :=
  fun p => ⟨p.1.1, (modEq_iff_exists_int hN p.1.1 x w).mpr ⟨p.1.2, p.2⟩⟩

/-- The projection is injective because `lam` is determined by the first `k`
coordinates. -/
theorem extProj_injective {k N : ℕ} (hN : 0 < N) (x : Fin k → ℕ) (w : ℕ) :
    Function.Injective (extProj (k := k) (N := N) hN x w) := by
  intro p q hpq
  have hp1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
  have hp2 : extDot p.1.1 q.1.2 x N = (w : ℤ) := by
    rw [hp1]
    exact q.2
  have hlam : p.1.2 = q.1.2 := ext_lambda_unique hN p.1.1 x w p.2 hp2
  exact Subtype.ext (Prod.ext hp1 hlam)

/-- The projection is surjective because every modular solution has a
multiplier. -/
theorem extProj_surjective {k N : ℕ} (hN : 0 < N) (x : Fin k → ℕ) (w : ℕ) :
    Function.Surjective (extProj (k := k) (N := N) hN x w) := by
  intro q
  exact ⟨modToExt hN x w q, Subtype.ext rfl⟩

/-- The extended integer equation `(b, lam) · (x, N) = w` has exactly as many
solutions as the modular equation `b · x = w mod N`. -/
theorem card_ext_solutions_eq {k N : ℕ} (hN : 0 < N) (x : Fin k → ℕ) (w : ℕ) :
    Nat.card {p : (Fin k → ℤ) × ℤ // extDot p.1 p.2 x N = (w : ℤ)}
      = Nat.card {b : Fin k → ℤ // (intDot b x : ZMod N) = (w : ZMod N)} :=
  Nat.card_congr
    (Equiv.ofBijective (extProj (k := k) (N := N) hN x w)
      ⟨extProj_injective hN x w, extProj_surjective hN x w⟩)

/-- `gcd(x₁, …, x_k, N)` divides the integer dot product `b · x`. -/
theorem gcd_dvd_intDot {k N : ℕ} (x : Fin k → ℕ) (b : Fin k → ℤ) :
    (Nat.gcd N (univ.gcd x) : ℤ) ∣ intDot b x := by
  unfold intDot
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right
    (by exact_mod_cast Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Finset.gcd_dvd (mem_univ i))) _

/-- **Solvability criterion.**  The integer equation `(b, lam) · (x, N) = w` has
a solution in `b` and `lam` exactly when `gcd(x₁, …, x_k, N)` divides `w`. -/
theorem exists_int_solution_iff_dvd {k N : ℕ} (_hN : 0 < N) (x : Fin k → ℕ) (w : ℕ) :
    (∃ b : Fin k → ℤ, ∃ lam : ℤ, extDot b lam x N = (w : ℤ))
      ↔ Nat.gcd N (univ.gcd x) ∣ w := by
  constructor
  · rintro ⟨b, lam, h⟩
    have hgN : (Nat.gcd N (univ.gcd x) : ℤ) ∣ (N : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left _ _
    have hglam : (Nat.gcd N (univ.gcd x) : ℤ) ∣ lam * (N : ℤ) := dvd_mul_of_dvd_right hgN _
    have hgb := gcd_dvd_intDot (N := N) x b
    have hgw : (Nat.gcd N (univ.gcd x) : ℤ) ∣ (w : ℤ) := by
      rw [← h]
      unfold extDot
      exact dvd_add hgb hglam
    exact_mod_cast hgw
  · intro hdvd
    obtain ⟨q, hq⟩ := hdvd
    obtain ⟨c, hc⟩ := exists_int_combo_gcd_finset (univ : Finset (Fin k)) x
    refine ⟨fun i => c i * ((q : ℤ) * (N.gcdB (univ.gcd x))), (q : ℤ) * (N.gcdA (univ.gcd x)), ?_⟩
    have hcast : ((Nat.gcd N (univ.gcd x) : ℕ) : ℤ)
        = (N : ℤ) * (N.gcdA (univ.gcd x))
            + ((univ.gcd x : ℕ) : ℤ) * (N.gcdB (univ.gcd x)) :=
      Nat.gcd_eq_gcd_ab N (univ.gcd x)
    have hq' : (w : ℤ) = ((Nat.gcd N (univ.gcd x) : ℕ) : ℤ) * (q : ℤ) := by
      rw [hq]
      push_cast
      ring
    have hsum : (∑ i, c i * ((q : ℤ) * (N.gcdB (univ.gcd x))) * (x i : ℤ))
        = ((q : ℤ) * (N.gcdB (univ.gcd x))) * ∑ i, c i * (x i : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    unfold extDot intDot
    rw [hsum, hq', hcast, hc]
    ring

/-- The modular equation is solvable exactly when the gcd divides the
representative of the right-hand side. -/
theorem mod_solvable_iff_dvd {k N : ℕ} (hN : 0 < N) (x : Fin k → ℕ) (w : ℕ) :
    (∃ b : Fin k → ℤ, (intDot b x : ZMod N) = (w : ZMod N))
      ↔ Nat.gcd N (univ.gcd x) ∣ w := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨lam, hlam⟩ := (modEq_iff_exists_int hN b x w).mp hb
    exact (exists_int_solution_iff_dvd hN x w).mp ⟨b, lam, hlam⟩
  · intro h
    obtain ⟨b, lam, hlam⟩ := (exists_int_solution_iff_dvd hN x w).mpr h
    exact ⟨b, (modEq_iff_exists_int hN b x w).mpr ⟨lam, hlam⟩⟩

/-- The solution set of a solvable equation is a coset of the kernel: any two
solutions differ by a homogeneous solution. -/
theorem solution_sub_is_kernel {k N : ℕ} (x : Fin k → ℕ) (w : ℕ)
    {b b₀ : Fin k → ℤ} (hb : (intDot b x : ZMod N) = (w : ZMod N))
    (hb₀ : (intDot b₀ x : ZMod N) = (w : ZMod N)) :
    (intDot (b - b₀) x : ZMod N) = 0 := by
  have hsub : intDot (b - b₀) x = intDot b x - intDot b₀ x := by
    unfold intDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  push_cast
  rw [hb, hb₀, sub_self]

/-- Conversely, adding a homogeneous solution to one solution gives another
solution of the same coset. -/
theorem kernel_add_solution {k N : ℕ} (x : Fin k → ℕ) (w : ℕ)
    {b b₀ : Fin k → ℤ} (hb₀ : (intDot b₀ x : ZMod N) = (w : ZMod N))
    (hb : (intDot b x : ZMod N) = 0) :
    (intDot (b + b₀) x : ZMod N) = (w : ZMod N) := by
  have hadd : intDot (b + b₀) x = intDot b x + intDot b₀ x := by
    unfold intDot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    ring
  rw [hadd]
  push_cast
  rw [hb, hb₀, zero_add]

/-- The converse fibre-size direction of Lemma 4: if the modular fibre over `w`
is nonempty then `gcd(b₁, …, b_k, N)` divides the representative of `w`. -/
theorem dvd_of_mem_range {k N : ℕ} [NeZero N] (b : Fin k → ZMod N) {w : ZMod N}
    (hw : w ∈ (dotHom N b).range) : matrixGcd N b ∣ w.val := by
  rw [range_dotHom] at hw
  rw [AddSubgroup.mem_zmultiples_iff] at hw
  obtain ⟨z, hz⟩ := hw
  set g : ℕ := matrixGcd N b with hgdef
  have hsplit : g ∣ N := matrixGcd_dvd_left b
  have hzw : w = (z : ZMod N) * ((g : ℕ) : ZMod N) := by
    rw [← hz, zsmul_eq_mul]
  have hmod : (((w.val : ℤ)) : ZMod N) = (((z * (g : ℤ)) : ℤ) : ZMod N) := by
    push_cast
    rw [ZMod.natCast_zmod_val, hzw]
  have hdvd_sub : (N : ℤ) ∣ z * (g : ℤ) - (w.val : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (w.val) (z * (g : ℤ)) N).mp hmod
  have hgN : (g : ℤ) ∣ (N : ℤ) := by exact_mod_cast hsplit
  have hgz : (g : ℤ) ∣ z * (g : ℤ) := dvd_mul_left _ _
  have hwv : (g : ℤ) ∣ (w.val : ℤ) := by
    have h := dvd_sub hgz (dvd_trans hgN hdvd_sub)
    rwa [sub_sub_cancel] at h
  exact_mod_cast hwv

end Qatlib.Papers.GenHidShift05.FiberGeometry

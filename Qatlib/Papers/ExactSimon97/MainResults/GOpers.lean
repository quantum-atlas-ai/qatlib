/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs

/-!
# Fourier commutation laws for translations and phases

The finite abelian Fourier transform exchanges translation with character multiplication. This
module also records the character scalar needed to commute a translation past a phase
multiplication. The development follows [BrassardHoyer1997].

## Main statements

* `theorem11_mu_tau_phi`: gives the translation–phase commutation factor.
* `theorem11_fourier_phi`: turns phase multiplication into translation by the negative label.
* `theorem11_fourier_tau`: turns translation into phase multiplication.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

variable {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]

/-- Translation and phase multiplication commute up to the character scalar `charPair h t`. See
[BrassardHoyer1997]. -/
theorem theorem11_mu_tau_phi (h t : AbGroup n m) (f : AbGroup n m → ℂ) :
    (fun g => charPair (m := m) h t * tau t (phi (m := m) h f) g) =
      phi (m := m) h (tau t f) := by
  funext g
  simp only [tau, phi]
  have hsplit : charPair (m := m) h g =
      charPair (m := m) h (g - t) * charPair (m := m) h t := by
    have h1 := charPair_add_right (m := m) h (g - t) t
    rwa [sub_add_cancel] at h1
  rw [hsplit]
  ring

/-- Fourier transformation carries phase multiplication by `h` to translation of the Fourier
transform by `-h`. See [BrassardHoyer1997]. -/
theorem theorem11_fourier_phi (h : AbGroup n m) (f : AbGroup n m → ℂ) :
    FG (m := m) (phi (m := m) h f) = tau (-h) (FG (m := m) f) := by
  funext g
  simp only [FG, tau, phi, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, ← charPair_add_left (m := m) g h x]

/-- Fourier transformation carries translation by `t` to phase multiplication of the Fourier
transform by `t`. See [BrassardHoyer1997]. -/
theorem theorem11_fourier_tau (t : AbGroup n m) (f : AbGroup n m → ℂ) :
    FG (m := m) (tau t f) = phi (m := m) t (FG (m := m) f) := by
  funext g
  simp only [FG, tau, phi]

  have hinner :
      (∑ x, charPair (m := m) g x * f (x - t)) =
        (∑ u, charPair (m := m) g u * f u) * charPair (m := m) t g := by
    have hreindex :
        (∑ x, charPair (m := m) g x * f (x - t)) =
          ∑ u, charPair (m := m) g (u + t) * f u := by
      refine Fintype.sum_equiv (Equiv.subRight t)
        (fun x => charPair (m := m) g x * f (x - t))
        (fun u => charPair (m := m) g (u + t) * f u) ?_
      intro x
      simp [sub_add_cancel]
    rw [hreindex]
    calc (∑ u, charPair (m := m) g (u + t) * f u)
        = ∑ u, (charPair (m := m) g u * f u) * charPair (m := m) t g := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [charPair_add_right (m := m) g u t, charPair_comm (m := m) g t]
          ring
      _ = (∑ u, charPair (m := m) g u * f u) * charPair (m := m) t g := by
          rw [← Finset.sum_mul]
  rw [hinner]
  ring

/-- Collects the translation–phase commutation identity and the two identities exchanging these
operations under Fourier transformation. See [BrassardHoyer1997]. -/
theorem theorem11_commutative_laws :
    (∀ (h t : AbGroup n m) (f : AbGroup n m → ℂ),
      (fun g => charPair (m := m) h t * tau t (phi (m := m) h f) g) =
        phi (m := m) h (tau t f)) ∧
    (∀ (h : AbGroup n m) (f : AbGroup n m → ℂ),
      FG (m := m) (phi (m := m) h f) = tau (-h) (FG (m := m) f)) ∧
    (∀ (t : AbGroup n m) (f : AbGroup n m → ℂ),
      FG (m := m) (tau t f) = phi (m := m) t (FG (m := m) f)) :=
  ⟨theorem11_mu_tau_phi, theorem11_fourier_phi, theorem11_fourier_tau⟩

end Qatlib.Papers.ExactSimon97.MainResults

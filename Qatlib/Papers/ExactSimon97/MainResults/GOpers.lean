/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

variable {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]

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

theorem theorem11_fourier_phi (h : AbGroup n m) (f : AbGroup n m → ℂ) :
    FG (m := m) (phi (m := m) h f) = tau (-h) (FG (m := m) f) := by
  funext g
  simp only [FG, tau, phi, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, ← charPair_add_left (m := m) g h x]

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

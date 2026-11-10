/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GramRealization.MatrixFactors.RationalLDL
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.GramQueryCore.GramRealization.OrderedSchurConsumer

open Qatlib.Concepts.GramQueryCore.GramRealization.RationalLDL
open Matrix

abbrev State := Sigma (fun n : ℕ => Matrix (Fin n) (Fin n) ℚ)

def trace : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → List State
  | 0, K => [⟨0, K⟩]
  | n + 1, K => ⟨n + 1, K⟩ :: trace n (RationalLDL.schur K)

theorem trace_length (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) :
    (trace n K).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [trace, List.length_cons, ih]

theorem trace_head (n : ℕ) (K : Matrix (Fin n) (Fin n) ℚ) :
    (trace n K).head? = some ⟨n, K⟩ := by
  cases n with
  | zero => rfl
  | succ n => simp only [trace, List.head?_cons]

theorem trace_posSemidef {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : (RationalLDL.realMatrix K).PosSemidef) :
    ∀ s ∈ trace n K, (RationalLDL.realMatrix s.2).PosSemidef := by
  induction n with
  | zero =>
      intro s hs
      simp only [trace, List.mem_singleton] at hs
      subst s
      exact hK
  | succ n ih =>
      intro s hs
      simp only [trace, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hK
      · exact ih (RationalLDL.schur K) (RationalLDL.schur_psd K hK) s hs

theorem consume {n : ℕ} (K : Matrix (Fin n) (Fin n) ℚ)
    (hK : (RationalLDL.realMatrix K).PosSemidef) :
    ∃ F, RationalLDL.compute n K = some F ∧
      RationalLDL.factor F = K ∧ ∀ i, 0 ≤ F.diagonal i := by
  obtain ⟨F, hF⟩ := RationalLDL.compute_complete n K hK
  exact ⟨F, hF, (RationalLDL.compute_sound n K F hF).1,
    (RationalLDL.compute_sound n K F hF).2⟩

end Qatlib.Concepts.GramQueryCore.GramRealization.OrderedSchurConsumer

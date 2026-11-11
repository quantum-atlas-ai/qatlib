/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# HarmonicOscillator — Lemma 3 (arXiv:2303.01471v1, Appendix B.3)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF page 26, equations (B.43)–(B.44).
-/

open scoped Matrix

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.HarmonicOscillator

open Qatlib.Papers.QHamDescent23.MainResults

/-!
### Lemma 3 (B.43)–(B.44)

Source: arXiv:2303.01471v1, Lemma 3, p.26.

For the quantum harmonic oscillator `H = K + V` with eigenvalues
`E_n = (n + ½)ℏω` and eigenstates `|e_n⟩`, both the kinetic and the potential
expectation equal `½E_n` on the eigenstates (B.43), and the matrix elements of
`K` and `V` between `|e_n⟩` and `|e_{n±1}⟩` vanish (B.44):

`⟨e_n|K|e_n⟩ = ⟨e_n|V|e_n⟩ = ½ (n + ½)ℏω`,
`⟨e_n|K|e_{n±1}⟩ = ⟨e_n|V|e_{n±1}⟩ = 0`.

Formal model: `K` and `V` are matrices in the eigenbasis of `H = K + V`,
`e n` is the `n`-th eigenvector, `hEig` is the eigenvalue equation with
`E_n = (n + ½)ℏω`, `hvirial` is the virial identity `⟨K⟩ = ⟨V⟩` on
eigenstates, and `hparK`, `hparV` record that `K` and `V` are parity-even
(even functions of `x̂` and `p̂`), which is what makes the `n ↔ n±1` matrix
elements vanish in (B.44).

Paper proof route: for a harmonic oscillator the virial theorem gives
`⟨K⟩ = ⟨V⟩ = E_n/2` (this is (B.43)); parity of `x̂²` and `p̂²` means `K` and
`V` only connect levels with the same parity, hence the `n ↔ n±1` elements in
(B.44) vanish.

Formal proof: (B.43) follows from the eigenvalue equation: expanding
`⟨e_n|(K+V)e_n⟩` with `Matrix.add_mulVec`/`bracket_add_right` gives
`⟨K⟩_n + ⟨V⟩_n = E_n`, and the virial identity `hvirial` then halves it. For
(B.44) the parity hypotheses `hparK`/`hparV` apply because `n + (n±1)` is odd.
-/
/-- Lemma 3 (B.43)–(B.44): the virial identity for the harmonic-oscillator QHD
evolution. -/
theorem source_lemma3_harmonic_oscillator
    {N : ℕ} (K V : Matrix (Fin N) (Fin N) ℂ) (e : Fin N → Ket (Fin N))
    (ω ħ : ℝ)
    (horth : ∀ n, bracket (e n) (e n) = 1)
    (hEig : ∀ n, (K + V) *ᵥ e n =
      ((((n : ℝ) + 1 / 2) * ħ * ω : ℝ) : ℂ) • e n)
    (hvirial : ∀ n, bracket (e n) (K *ᵥ e n) = bracket (e n) (V *ᵥ e n))
    (hparK : ∀ n m : Fin N, Odd ((n : ℕ) + (m : ℕ)) →
      bracket (e n) (K *ᵥ e m) = 0)
    (hparV : ∀ n m : Fin N, Odd ((n : ℕ) + (m : ℕ)) →
      bracket (e n) (V *ᵥ e m) = 0) :
    (∀ n, bracket (e n) (K *ᵥ e n)
        = (((1 / 2 * ((n : ℝ) + 1 / 2) * ħ * ω : ℝ)) : ℂ) ∧
      bracket (e n) (V *ᵥ e n)
        = (((1 / 2 * ((n : ℝ) + 1 / 2) * ħ * ω : ℝ)) : ℂ)) ∧
    (∀ n m : Fin N,
      ((m : ℕ) = (n : ℕ) + 1 ∨ (n : ℕ) = (m : ℕ) + 1) →
      bracket (e n) (K *ᵥ e m) = 0 ∧ bracket (e n) (V *ᵥ e m) = 0) := by
  constructor
  · intro n
    have hK : bracket (e n) ((K + V) *ᵥ e n)
        = ((((n : ℝ) + 1 / 2) * ħ * ω : ℝ) : ℂ) := by
      rw [hEig n, bracket_smul_right, horth n, mul_one]
    rw [Matrix.add_mulVec, bracket_add_right] at hK
    have hsum := hK
    have h2 : (2 : ℂ) * bracket (e n) (K *ᵥ e n) = ((((n : ℝ) + 1 / 2) * ħ * ω : ℝ) : ℂ) := by
      rw [← hvirial n] at hsum
      linear_combination hsum
    have hx : bracket (e n) (K *ᵥ e n) = ((((n : ℝ) + 1 / 2) * ħ * ω : ℝ) : ℂ) / 2 := by
      linear_combination h2 / 2
    constructor
    · rw [hx]; push_cast; ring
    · rw [← hvirial n, hx]; push_cast; ring
  · intro n m h
    have hodd : Odd ((n : ℕ) + (m : ℕ)) := by
      rcases h with h | h
      · exact ⟨(n : ℕ), by omega⟩
      · exact ⟨(m : ℕ), by omega⟩
    exact ⟨hparK n m hodd, hparV n m hodd⟩



end Qatlib.Papers.QHamDescent23.MainResults.HarmonicOscillator

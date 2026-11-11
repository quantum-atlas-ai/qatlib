/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor PCA (Hastings, arXiv:1907.12724v2) — parameters and numerical layer

This module fixes the *numerical* vocabulary of the source
*Classical and Quantum Algorithms for Tensor Principal Component Analysis*
(Matthew B. Hastings, arXiv:1907.12724v2, 24 Feb 2020 = Quantum 4, 237 (2020)).
Everything here is a definition copied from the source:

* the two Gaussian ensembles and the symmetrized / unsymmetrized choice (§1.1, p.3);
* the spiked tensor parameters `p, N, n_bos, λ` and Assumption 1 (§1.1, p.3);
* the scalar `J` of Lemma 4 / Theorem 1, with its defining series
  `(p/2)! * C(n_bos, p/2) / n_bos^(p/2)` for the real ensemble, twice that for the
  complex ensemble (Lemma 4, p.12; Theorem 1, p.8);
* the thresholds `E_max` (Eqs. (10) set, p.8: even and odd `p`), the tail scale `ξ`
  (Eqs. (11), (12)), the signal energy `E_0` (Eqs. (15), (19)), the detection
  threshold `E_cut = (E_0 + E_max)/2` (Algorithm 2, p.7), and the symmetric-subspace
  dimension `D(N, n_bos) ≈ N^n_bos / n_bos!` (§3.1, p.6).

The module contains no theorems: it is the object layer, shared by every source
statement of the block.  The random objects of the paper (the Gaussian tensor `G`,
the Hamiltonian `H(G)`, the state `Ψ`, the single-particle density matrix `ρ₁`)
are carried by the model structures in `SpectralModel`.
-/

namespace Qatlib.Papers.TensorPCA19.MainResults

set_option autoImplicit false
noncomputable section

/-- The two Gaussian ensembles of §1.1 (p.3): real entries of variance one, or
complex entries with real and imaginary parts of variance `1/2`. -/
inductive TensorEnsemble where
  | real
  | complex
  deriving DecidableEq, Repr

/-- Whether the noise tensor has been symmetrized (§1.1, p.3).  The paper notes
that the symmetrized and unsymmetrized cases reduce to one another; the flag
only selects the constant in `J` (Lemma 4, p.12). -/
inductive Symmetrization where
  | symmetrized
  | unsymmetrized
  deriving DecidableEq, Repr

/-- The spiked tensor model of §1.1 (p.3): order `p`, dimension `N`, number of
bosons `n_bos`, signal-to-noise scalar `λ`, and the ensemble/symmetrization
choice.  `|v_sig| = √N` is part of the model and is not a separate field: the
normalization is used through the energy identity of §3.2.1. -/
structure SpikedTensor where
  /-- Tensor order. -/
  p : ℕ
  /-- Single-particle dimension. -/
  N : ℕ
  /-- Number of bosons. -/
  nbos : ℕ
  /-- Signal-to-noise scalar `λ` of `T₀ = λ v_sig^{⊗p} + G`. -/
  lam : ℝ
  /-- Real or complex Gaussian ensemble. -/
  ensemble : TensorEnsemble
  /-- Symmetrized or not. -/
  symm : Symmetrization
  /-- The paper treats `p ≥ 2`. -/
  hp : 2 ≤ p
  /-- `N ≥ 1`; the asymptotic statements additionally need `log N > 0`. -/
  hN : 0 < N
  /-- `n_bos ≥ 1` (the Hamiltonian is trivial for fewer bosons). -/
  hnbos : 0 < nbos

/-- `p` is even (the case of §3.2.1 and §4.1). -/
def SpikedTensor.evenOrder (s : SpikedTensor) : Prop := s.p % 2 = 0

/-- The even order `2(p-1)` used in the odd-`p` reduction of §3.1/§4.2, Eq. (8). -/
def SpikedTensor.reducedOrder (s : SpikedTensor) : ℕ := 2 * (s.p - 1)

/-- The scalar `J` of Lemma 4 (p.12) at a given order: for the real ensemble it
is `(q/2)! * C(n_bos, q/2) / n_bos^(q/2)`, and twice that for the complex
ensemble. -/
def Jscalar (ensemble : TensorEnsemble) (q nbos : ℕ) : ℝ :=
  match ensemble with
  | .real =>
      (Nat.factorial (q / 2) : ℝ) * (Nat.choose nbos (q / 2) : ℝ) / (nbos : ℝ) ^ (q / 2)
  | .complex =>
      2 * ((Nat.factorial (q / 2) : ℝ) * (Nat.choose nbos (q / 2) : ℝ) / (nbos : ℝ) ^ (q / 2))

/-- The `J` of Theorem 1 / Lemma 4 for even `p`. -/
def Jval (s : SpikedTensor) : ℝ := Jscalar s.ensemble s.p s.nbos

/-- The `J` of Lemma 7 / Theorem 1 for odd `p`: the even-case `J` at order
`2(p-1)` (§4.2, p.17). -/
def JvalOdd (s : SpikedTensor) : ℝ := Jscalar s.ensemble (s.reducedOrder) s.nbos

/-- `E_max` for even `p`, Theorem 1 p.8 / Lemma 5 Eq. (31):
`√(2 J log N) · n_bos^(p/4 + 1/2) · N^(p/4)`. -/
def EmaxEven (s : SpikedTensor) : ℝ :=
  Real.sqrt (2 * Jval s * Real.log (s.N : ℝ)) *
    (s.nbos : ℝ) ^ ((s.p : ℝ) / 4 + 1 / 2) * (s.N : ℝ) ^ ((s.p : ℝ) / 4)

/-- `E_max` for odd `p`, Theorem 1 p.8 / Lemma 7 Eq. (38):
`2 √(J log N) · n_bos^(p/2) · N^(p/2)`. -/
def EmaxOdd (s : SpikedTensor) : ℝ :=
  2 * Real.sqrt (JvalOdd s * Real.log (s.N : ℝ)) *
    (s.nbos : ℝ) ^ ((s.p : ℝ) / 2) * (s.N : ℝ) ^ ((s.p : ℝ) / 2)

/-- The theorem-1 threshold `E_max`, selected by the parity of `p`. -/
def Emax (s : SpikedTensor) : ℝ := if s.p % 2 = 0 then EmaxEven s else EmaxOdd s

/-- The tail scale `ξ` for even `p`, Theorem 1 Eq. (11) / Lemma 5 Eq. (32). -/
def xiEven (s : SpikedTensor) : ℝ :=
  Real.sqrt (Jval s) * (s.nbos : ℝ) ^ ((s.p : ℝ) / 4 - 1 / 2) *
    (s.N : ℝ) ^ ((s.p : ℝ) / 4) / Real.sqrt (2 * Real.log (s.N : ℝ))

/-- The tail scale `ξ` for odd `p`, Theorem 1 Eq. (12) / Lemma 7 Eq. (39). -/
def xiOdd (s : SpikedTensor) : ℝ :=
  Real.sqrt (JvalOdd s) * (s.nbos : ℝ) ^ ((s.p : ℝ) / 2 - 1) *
    (s.N : ℝ) ^ ((s.p : ℝ) / 2) / Real.sqrt (Real.log (s.N : ℝ))

/-- The theorem-1 tail scale, selected by the parity of `p`. -/
def xi (s : SpikedTensor) : ℝ := if s.p % 2 = 0 then xiEven s else xiOdd s

/-- The signal energy `E₀ = λ (p/2)! C(n_bos, p/2) N^{p/2}` for even `p`,
Eq. (15), p.9. -/
def E0Even (s : SpikedTensor) : ℝ :=
  s.lam * (Nat.factorial (s.p / 2) : ℝ) * (Nat.choose s.nbos (s.p / 2) : ℝ) *
    (s.N : ℝ) ^ (s.p / 2)

/-- The signal energy `E₀ = λ² (p-1)! C(n_bos, p-1) N^p` for odd `p`,
Eq. (19), p.10. -/
def E0Odd (s : SpikedTensor) : ℝ :=
  s.lam ^ 2 * (Nat.factorial (s.p - 1) : ℝ) * (Nat.choose s.nbos (s.p - 1) : ℝ) *
    (s.N : ℝ) ^ s.p

/-- The signal energy `E₀`, selected by the parity of `p`. -/
def E0 (s : SpikedTensor) : ℝ := if s.p % 2 = 0 then E0Even s else E0Odd s

/-- The detection threshold of Algorithm 2 (p.7): `E_cut = (E₀ + E_max)/2`. -/
def Ecut (s : SpikedTensor) : ℝ := (E0 s + Emax s) / 2

/-- The dimension `D(N, n_bos)` of the symmetric subspace (§3.1, p.6), in the
standard approximation `N^n_bos / n_bos!`. -/
def symmetricDim (s : SpikedTensor) : ℝ :=
  (s.N : ℝ) ^ s.nbos / (Nat.factorial s.nbos : ℝ)

/-- **Assumption 1** (§1.1, p.3): `n_bos = O(N^θ)` with `p θ < 1` (so that
`n_bos^p / N = o(1)`), `λ = Ω(N^{-θ₀})` with `θ₀ > p/4`, and `λ = O(N^{-p/4})`,
all with `p`-dependent constants. -/
def Assumption1 (s : SpikedTensor) : Prop :=
  ∃ θ θ₀ c C : ℝ,
    0 < θ ∧ (s.p : ℝ) * θ < 1 ∧ (s.p : ℝ) / 4 < θ₀ ∧ 0 < c ∧ 0 < C ∧ 0 < s.lam ∧
    (s.nbos : ℝ) ≤ (s.N : ℝ) ^ θ ∧
    c * (s.N : ℝ) ^ (-θ₀) ≤ s.lam ∧
    s.lam ≤ C * (s.N : ℝ) ^ (-(s.p : ℝ) / 4)

/-- The normalized overlap `⟨v_sig|ρ₁|v_sig⟩ / N` of the source, Eq. (17) and
Eq. (24).  It is represented by an explicit real `ov` together with the model
identity `E_signal = E₀ · ov` proved in §3.2.1 / §3.2.2. -/
abbrev normalizedOverlap := ℝ

/-- The weak-recovery conclusion `corr(x, v_sig) = Ω(1)` of §2 (p.5): the output
vector has a non-vanishing normalized overlap with the signal. -/
def WeakRecovery (corr : ℝ) (c : ℝ) : Prop := 0 < c ∧ c ≤ corr

/-- Strong recovery (§2, p.5): `corr(x, v_sig) = 1 - o(1)`, formalized as
"arbitrarily close to one", i.e. `∀ η > 0, 1 - η ≤ corr`. -/
def StrongRecovery (corr : ℝ) : Prop := ∀ η : ℝ, 0 < η → 1 - η ≤ corr

end

end Qatlib.Papers.TensorPCA19.MainResults

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.ElectricalNetwork

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — Lemma 8: the kernel of `C_{G′}` consists of scaled flows

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

**Lemma 8** (§4.1, p.21, Eq. (108)--(111)).  With `E′ = E ∪ {e₀}`, `|φ_e⟩ = √(w_e)(e⁻ − e⁺)`
(Eq. (84)), `|φ_{e₀}⟩ = −√(2λ)|i_ext⟩` (Eq. (86)), and `C_{G′} = ∑_{e∈E′}|φ_e⟩⟨e|`,

  `ker(C_{G′}) = { g(f) : f a flow consistent with α·i_ext for some α }`,
  `g(f) = (1/√(2λ))h(f)|e₀⟩ + ∑_e f(e)/√(w_e)|e⟩`.

Writing `ψ = β|e₀⟩ + ∑_e β_e|e⟩`, the paper observes `C_{G′}ψ = 0` iff
`(B_G f)(v) = √(2λ)·β·i_ext(v)` for all `v`, i.e. `f(e) := √(w_e)β_e` is consistent with
`√(2λ)β·i_ext` (Eq. (111)).  This file formalises and **proves** that equivalence.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators

namespace Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow

open Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The action of `C_{G′}` on `ψ = β|e₀⟩ + ∑_e β_e|e⟩`, where `E′ = E ∪ {e₀}`:
`(C_{G′}ψ)(v) = −√(2λ)·β·i_ext(v) + ∑_e B_G(v,e)·√(w_e)·β_e`.
This is `∑_{e∈E′}|φ_e⟩⟨e|ψ⟩` with `|φ_e⟩ = √(w_e)(e⁻−e⁺)` and
`|φ_{e₀}⟩ = −√(2λ)|i_ext⟩` (§4.1, Eq. (84)--(87)). -/
def modifiedCAction (G : ElecNetwork V E) (lam : ℝ) (iext : V → ℝ) (beta0 : ℝ)
    (be : E → ℝ) : V → ℝ :=
  fun v => - Real.sqrt (2 * lam) * beta0 * iext v
    + ∑ e, incident G v e * (Real.sqrt (G.w e) * be e)

/-- **Lemma 8 (arXiv:1311.1851v10, §4.1, p.21, Eq. (108)--(111)).**  `C_{G′}ψ = 0` for
`ψ = β|e₀⟩ + ∑_e β_e|e⟩` iff the edge values `f(e) = √(w_e)·β_e` form a flow consistent
with `√(2λ)·β·i_ext`, i.e. `B_G f = √(2λ)β·i_ext`.  This is the paper's reduction of
`ker(C_{G′})` to scaled flows. -/
theorem lemma8_kernel_characterization (G : ElecNetwork V E) (lam : ℝ) (iext : V → ℝ)
    (hlam : 0 < lam) (beta0 : ℝ) (be : E → ℝ) :
    (∀ v, modifiedCAction G lam iext beta0 be v = 0) ↔
      (incident G *ᵥ (fun e => Real.sqrt (G.w e) * be e)
        = fun v => Real.sqrt (2 * lam) * beta0 * iext v) := by
  constructor
  · intro h
    funext v
    have hv := h v
    unfold modifiedCAction at hv
    rw [incident_mulVec_apply]
    linarith
  · intro h v
    unfold modifiedCAction
    have hv := congrFun h v
    rw [incident_mulVec_apply] at hv
    linarith

end Qatlib.Papers.SparseNetwork13.MainResults.ElectricalFlow

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ChannelCaps

@[expose] public section


/-!
# Reviewed closed fragment of Wilde, arXiv:1106.1445v8

Only closed definitions and proofs are present. Capacity records have unconstrained
fields; conditional limits and averaging steps do not establish operational coding
or source algorithm costs. See the per-declaration source review receipt.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.ChannelInfo

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open scoped BigOperators

noncomputable section

variable (C : QChanInfo)

/-- **Regularised limit from additivity** — arXiv:1106.1445v8, Cor. 13.1.1 /
13.3.1 / 13.4.1 / 13.5.1 / 13.6.1, at the five fixed-PDF corollary locators in the review receipt.  If `f` is additive against
every channel (`f(N^{⊗k}) = k·f(N)`, the `Regularises` hypothesis), then the
regularised sequence `(1/k)·f(N^{⊗k})` equals `f(N)` at every `k ≥ 1`, hence
converges to `f(N)`. -/
theorem regularised_tendsto (f : C.Ch → ℝ) (N : C.Ch)
    (h : C.Regularises f N) :
    Filter.Tendsto (fun k => C.reg f N k) Filter.atTop (nhds (f N)) := by
  have hconst : ∀ k, 1 ≤ k → C.reg f N k = f N := by
    intro k hk
    unfold QChanInfo.reg
    rw [h k hk]
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hkpos)]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  exact (Filter.eventually_atTop.2 ⟨1, fun k hk => hconst k hk⟩).mono fun k hk => hk.symm

/-- The regularised abstract mutual-information sequence converges under `Regularises`.
For the target of Corollary 13.1.1 of arXiv:1106.1445v8, fixed PDF p. 393,
the assumed tensor-power scaling makes the positive-length sequence constant.
This does not prove additivity or identify an operational capacity. -/
theorem mutual_info_reg_tendsto_of_regularises (N : C.Ch) (h : C.Regularises C.I N) :
    Filter.Tendsto (fun k => C.reg C.I N k) Filter.atTop (nhds (C.I N)) := by
  exact regularised_tendsto C C.I N h

/-- The abstract Holevo regularisation converges under an explicit `Regularises` premise.
The entanglement-breaking premise is retained for Corollary 13.3.1 of
arXiv:1106.1445v8, fixed PDF p. 404, but is unused in this conditional limit. -/
theorem holevo_reg_tendsto_of_entBreaking_of_regularises (N : C.Ch) (_hEB : C.EntBreaking N)
    (h : C.Regularises C.chi N) :
    Filter.Tendsto (fun k => C.reg C.chi N k) Filter.atTop (nhds (C.chi N)) := by
  exact regularised_tendsto C C.chi N h

/-- The quantum-mutual-information target converges from assumed tensor-power scaling.
For Corollary 13.4.1 of arXiv:1106.1445v8, fixed PDF p. 409, the model uses
the same abstract field `C.I` as the preceding mutual-information target.
Its additivity and operational interpretation are not established here. -/
theorem quantum_mutual_info_reg_tendsto_of_regularises (N : C.Ch) (h : C.Regularises C.I N) :
    Filter.Tendsto (fun k => C.reg C.I N k) Filter.atTop (nhds (C.I N)) := by
  exact regularised_tendsto C C.I N h

/-- The abstract coherent-information regularisation converges under `Regularises`.
The degradability premise is retained for Corollary 13.5.1 of
arXiv:1106.1445v8, fixed PDF p. 414, but the limit uses only the scaling premise. -/
theorem coherent_info_reg_tendsto_of_degradable_of_regularises (N : C.Ch) (_hdeg : C.Degradable N)
    (h : C.Regularises C.Q N) :
    Filter.Tendsto (fun k => C.reg C.Q N k) Filter.atTop (nhds (C.Q N)) := by
  exact regularised_tendsto C C.Q N h

/-- The abstract private-information regularisation converges under `Regularises`.
The degradability premise is retained for Corollary 13.6.1 of
arXiv:1106.1445v8, fixed PDF p. 421, but the limit uses only the scaling premise. -/
theorem private_info_reg_tendsto_of_degradable_of_regularises (N : C.Ch) (_hdeg : C.Degradable N)
    (h : C.Regularises C.P N) :
    Filter.Tendsto (fun k => C.reg C.P N k) Filter.atTop (nhds (C.P N)) := by
  exact regularised_tendsto C C.P N h

end

end Qatlib.Papers.QShannonWilde11.MainResults.ChannelInfo

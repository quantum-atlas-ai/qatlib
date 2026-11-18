/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Foundations.ScaledSqrt.SqrtBounds.RootCountOrder
import Qatlib.Concepts.CircuitLang.CtrlGates
import Qatlib.Concepts.CostModels.Compose
import Qatlib.Concepts.GateKit.Cor74Counts
import Qatlib.Papers.Armillary26.Instances.Routed
import Qatlib.Papers.Armillary26.Instances.Rate
import Qatlib.Papers.CssCodeCS96.Construction.HammingSteane
import Qatlib.Papers.PerfectQEC96.FiveQubit
import Qatlib.Papers.ExactSimon97.SampleStoppingQuantum
import Qatlib.Papers.HamLCUSim12.MultiproductFormula
import Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor
import Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation
import Qatlib.Papers.SuperfluidHel18.Madelung.PolarCurrent
import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
import Qatlib.Papers.KnotLight13.Bateman.Construction
import Qatlib.Papers.HydroSpinLatt21.WaveCoupling.SymmetricEnergy
import Qatlib.Papers.QHamXue25.NSDualLift.Linearization
import Qatlib.Papers.QShannonWilde11.MainResults.StatesChannels.KrausMath

set_option autoImplicit false
set_option warningAsError true

/-! # Ordinary module consumers of the mathematical interfaces -/

#check Qatlib.Concepts.CircuitLang.CtrlGates.cnot_ket
#check Qatlib.Concepts.CostModels.Compose.listQueryFold
#check Qatlib.Concepts.GateKit.cor74BasicBound
#check Qatlib.Papers.Armillary26.Instances.route_shift_pair
#check Qatlib.Papers.Armillary26.Instances.rate_gt_half
#check Qatlib.Papers.CssCodeCS96.Construction.ham3_css_params
#check Qatlib.Papers.PerfectQEC96.five_params
#check Qatlib.Papers.ExactSimon97.SampleStoppingQuantum.recovery_at_observed_stop
#check Qatlib.Papers.HamLCUSim12.MultiproductFormula.suzuki_multiproduct_lemma12_boost
#check Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor.taylor_prepared_born
#check Qatlib.Papers.SuperfoilLift19.QuantumCirc.closed_phase_integral_quantized
#check Qatlib.Papers.SuperfluidHel18.Madelung.polar_current_formula
#check Qatlib.Papers.KnottedLight08.HopfField.null_iff
#check Qatlib.Papers.KnotLight13.Bateman.bateman_null
#check Qatlib.Papers.HydroSpinLatt21.WaveCoupling.network_energy_dissipation
#check Qatlib.Papers.QHamXue25.NSDualLift.lift_tree_bounded
#check Qatlib.Papers.QShannonWilde11.MainResults.StatesChannels.completely_positive_trace_preserving_iff_exists_bounded_kraus

namespace QatlibTests.InterfaceConsumer

/-- The executable count interface is usable in an ordinary definition. -/
def executableCount : ℕ := Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount 8 (1 / 4)

/-- The order theorem retains its public signature in an ordinary module. -/
example (half : ℕ) {p q : ℚ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount half p ≤
      Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount half q :=
  Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount_mono half hp hpq

end QatlibTests.InterfaceConsumer

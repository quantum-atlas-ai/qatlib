/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Surface-code physical cost: 20 million qubits in 8 hours, and the 100x volume gain

Source: Gidney--Ekerå, *How to factor 2048 bit RSA integers in 8 hours using
20 million noisy qubits*, arXiv:1905.09749v3 (13 Apr 2021): title, abstract,
Table 2 (p. 3), §2.11 Eq. (5) (p. 11), §2.13--2.14 (p. 13).

Fixed version: v3 (PDF header `arXiv:1905.09749v3 [quant-ph] 13 Apr 2021`),
accepted Quantum 2021-03-29.

Claims covered:

* c001 (title): *how to factor 2048 bit RSA integers in 8 hours using 20 million
  noisy qubits.*  We formalise the Table 2 row `(ours) 2019 (parallel)` —
  20 million physical qubits at `n = 2048`, expected runtime `0.31` days
  (`0.31 · 24 = 7.44 ≤ 8` hours) — together with the paper's own supporting
  surface-code arithmetic: `2(d+1)²` physical qubits per logical qubit
  (1568 at `d = 27`), the `226 × 63` logical-qubit board at `n = 2048`,
  total `226 · 63 · 1568 = 22,325,184 ≤ 23,000,000` physical qubits from
  §2.14, and the Eq. (5) runtime `4 n_e n` milliseconds
  (`4 · 3072 · 2048 ms ≈ 6.99 h ≤ 8 h`).  The title's figure of 20 million
  (rather than §2.14's 22.3 million) comes from the ancillary
  `estimate costs.py`, as §2.14 explains; both are recorded.
* c003 (abstract): *we estimate the approximate cost … using plausible physical
  assumptions … a planar grid of qubits with nearest-neighbor connectivity, a
  characteristic physical gate error rate of 10⁻³, a surface code cycle time of
  1 microsecond, and a reaction time of 10 microseconds … When factoring 2048
  bit RSA integers, our construction's spacetime volume is a hundredfold less
  than comparable estimates from earlier works (Van Meter et al. 2009,
  Jones et al. 2010, Fowler et al. 2012, Gheorghiu et al. 2019).*
  We formalise the Table 2 rows and prove the 100x volume comparison.  The
  paper's own caveat at Table 2 ("assuming a cycle time that is 5x more
  optimistic will reduce the expected volume by a corresponding factor of 5")
  means the comparison must be taken at a common cycle time; this is exactly
  what the paper means by "accounting for slight remaining differences in the
  cost model".  Raw Table 2 volumes already give ≥ 100x against Van Meter,
  Jones and Fowler; for Gheorghiu the raw ratio is `170/5.9 ≈ 28.8x` and the
  cycle-time-normalised ratio `(170/0.2)/5.9 ≈ 144x`, so we prove both forms.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RSAFactoring19.MainResults.ResourceEstimate

/-! ### Table 2 records -/

/-- One row of Table 2: a historical physical-cost estimate for factoring a
2048 bit RSA integer.  `reactionTimeMicroseconds` is `none` where the paper
writes `N/A`. -/
structure CostEstimate where
  gateErrorRate : ℚ
  cycleTimeMicroseconds : ℚ
  reactionTimeMicroseconds : Option ℚ
  planar : Bool
  physicalQubitsMillions : ℚ
  runtimeDays : ℚ
  volumeMegaQubitDays : ℚ

/-- Van Meter et al. 2009 \[85\], Table 2. -/
def vanMeter2009 : CostEstimate :=
  { gateErrorRate := 2 / 1000, cycleTimeMicroseconds := 49,
    reactionTimeMicroseconds := none, planar := true,
    physicalQubitsMillions := 6500, runtimeDays := 410,
    volumeMegaQubitDays := 2600000 }

/-- Jones et al. 2010 \[46\], Table 2. -/
def jones2010 : CostEstimate :=
  { gateErrorRate := 1 / 1000, cycleTimeMicroseconds := 1 / 4,
    reactionTimeMicroseconds := none, planar := true,
    physicalQubitsMillions := 620, runtimeDays := 10,
    volumeMegaQubitDays := 6200 }

/-- Fowler et al. 2012 \[28\], Table 2. -/
def fowler2012 : CostEstimate :=
  { gateErrorRate := 1 / 1000, cycleTimeMicroseconds := 1,
    reactionTimeMicroseconds := some (1 / 10), planar := true,
    physicalQubitsMillions := 1000, runtimeDays := 11 / 10,
    volumeMegaQubitDays := 1100 }

/-- Gheorghiu et al. 2019 \[30\], Table 2. -/
def gheorghiu2019 : CostEstimate :=
  { gateErrorRate := 1 / 1000, cycleTimeMicroseconds := 1 / 5,
    reactionTimeMicroseconds := some (1 / 10), planar := true,
    physicalQubitsMillions := 170, runtimeDays := 1,
    volumeMegaQubitDays := 170 }

/-- `(ours) 2019 (parallel)`, Table 2 — the paper's main estimate. -/
def oursParallel : CostEstimate :=
  { gateErrorRate := 1 / 1000, cycleTimeMicroseconds := 1,
    reactionTimeMicroseconds := some 10, planar := true,
    physicalQubitsMillions := 20, runtimeDays := 31 / 100,
    volumeMegaQubitDays := 59 / 10 }

/-! ### c003: physical assumptions -/

/-- **c003, physical assumptions.**  The parallel construction uses a planar
nearest-neighbour grid, a physical gate error rate of `10⁻³`, a surface-code
cycle time of 1 µs and a reaction time of 10 µs (abstract and Table 2). -/
theorem oursParallel_assumptions :
    oursParallel.planar = true ∧ oursParallel.gateErrorRate = 1 / 1000 ∧
      oursParallel.cycleTimeMicroseconds = 1 ∧
      oursParallel.reactionTimeMicroseconds = some 10 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### c003: the hundredfold spacetime-volume improvement -/

/-- Volume normalised to a common 1 µs surface-code cycle — the Fig. 2 / Table 2
comparison basis ("assuming a cycle time that is 5x more optimistic will reduce
the expected volume by a corresponding factor of 5"). -/
def normalizedVolume (e : CostEstimate) : ℚ :=
  e.volumeMegaQubitDays / e.cycleTimeMicroseconds

/-- Van Meter et al.: raw Table 2 volume is over 100x ours. -/
theorem vanMeter2009_volume_100x :
    100 * oursParallel.volumeMegaQubitDays ≤ vanMeter2009.volumeMegaQubitDays := by
  norm_num [oursParallel, vanMeter2009]

/-- Jones et al.: raw Table 2 volume is over 100x ours. -/
theorem jones2010_volume_100x :
    100 * oursParallel.volumeMegaQubitDays ≤ jones2010.volumeMegaQubitDays := by
  norm_num [oursParallel, jones2010]

/-- Fowler et al.: raw Table 2 volume is over 100x ours. -/
theorem fowler2012_volume_100x :
    100 * oursParallel.volumeMegaQubitDays ≤ fowler2012.volumeMegaQubitDays := by
  norm_num [oursParallel, fowler2012]

/-- Gheorghiu et al.: after normalising to a common cycle time (their cycle is
0.2 µs, five times faster than ours), the volume is over 100x ours. -/
theorem gheorghiu2019_normalizedVolume_100x :
    100 * normalizedVolume oursParallel ≤ normalizedVolume gheorghiu2019 := by
  norm_num [normalizedVolume, oursParallel, gheorghiu2019]

/-- The raw Gheorghiu volume ratio is only about 28.8x, which is why the
cycle-time normalisation is needed for the 100x claim. -/
theorem gheorghiu2019_raw_volume_less_than_100x :
    ¬ (100 * oursParallel.volumeMegaQubitDays ≤ gheorghiu2019.volumeMegaQubitDays) := by
  norm_num [oursParallel, gheorghiu2019]

/-- **c003.**  At a common surface-code cycle, the parallel construction's
spacetime volume is a hundredfold less than every cited comparable estimate. -/
theorem spacetimeVolume_hundredfold_less :
    100 * normalizedVolume oursParallel ≤ normalizedVolume vanMeter2009 ∧
      100 * normalizedVolume oursParallel ≤ normalizedVolume jones2010 ∧
      100 * normalizedVolume oursParallel ≤ normalizedVolume fowler2012 ∧
      100 * normalizedVolume oursParallel ≤ normalizedVolume gheorghiu2019 := by
  refine ⟨?_, ?_, ?_, gheorghiu2019_normalizedVolume_100x⟩
  · norm_num [normalizedVolume, oursParallel, vanMeter2009]
  · norm_num [normalizedVolume, oursParallel, jones2010]
  · norm_num [normalizedVolume, oursParallel, fowler2012]

/-! ### c001: the title — 20 million qubits in 8 hours at n = 2048 -/

/-- Table 2 records exactly 20 million physical qubits for the parallel
construction. -/
theorem oursParallel_physicalQubitsMillions :
    oursParallel.physicalQubitsMillions = 20 := rfl

/-- The expected runtime is 0.31 days = 7.44 hours. -/
theorem oursParallel_runtime_hours :
    oursParallel.runtimeDays * 24 = 186 / 25 := by
  norm_num [oursParallel]

/-- The expected runtime is under 8 hours, as in the title. -/
theorem oursParallel_runtime_le_eight_hours :
    oursParallel.runtimeDays * 24 ≤ 8 := by
  norm_num [oursParallel]

/-- **c001 (title).**  The parallel construction factors 2048 bit RSA integers
using 20 million noisy qubits in under 8 hours. -/
theorem title_2048_bit_in_eight_hours :
    oursParallel.physicalQubitsMillions = 20 ∧ oursParallel.runtimeDays * 24 ≤ 8 :=
  ⟨oursParallel_physicalQubitsMillions, oursParallel_runtime_le_eight_hours⟩

/-! ### c001 support: surface-code arithmetic (§2.14) -/

/-- `2(d+1)²` physical qubits per logical qubit in lattice surgery (§2.14). -/
def qubitsPerLogical (d : ℕ) : ℕ := 2 * (d + 1) ^ 2

/-- At `d = 27`, each logical qubit covers 1568 physical qubits (§2.14). -/
theorem qubitsPerLogical_27 : qubitsPerLogical 27 = 1568 := by
  norm_num [qubitsPerLogical]

/-- Width of a piece in logical qubits is `113` (§2.10: `15·7 + 7`), and the
board is `113 w` wide with `w = n/c_sep = n/1024` pieces. -/
def boardWidth (n : ℕ) : ℕ := 113 * (n / 1024)

/-- Height of the board is 63 logical qubits (§2.10, Fig. 7). -/
def boardHeight : ℕ := 63

/-- Number of logical qubits on the board. -/
def logicalBoardQubits (n : ℕ) : ℕ := boardWidth n * boardHeight

/-- At `n = 2048` the board is `226 × 63` (§2.13--2.14). -/
theorem boardWidth_2048 : boardWidth 2048 = 226 := by
  norm_num [boardWidth]

/-- The `226 × 63` board holds 14238 logical qubits. -/
theorem logicalBoardQubits_2048 : logicalBoardQubits 2048 = 14238 := by
  norm_num [logicalBoardQubits, boardWidth, boardHeight]

/-- Total physical qubit count implied by §2.14: `226 · 63 · 1568`. -/
def physicalQubits (d n : ℕ) : ℕ := logicalBoardQubits n * qubitsPerLogical d

/-- `226 · 63 · 1568 = 22,325,184` (§2.14). -/
theorem physicalQubits_2048 : physicalQubits 27 2048 = 22325184 := by
  norm_num [physicalQubits, logicalBoardQubits, boardWidth, boardHeight,
    qubitsPerLogical]

/-- §2.14 rounds this to "approximately 23 million qubits". -/
theorem physicalQubits_2048_le_23M : physicalQubits 27 2048 ≤ 23000000 := by
  norm_num [physicalQubits_2048]

/-! ### c001 support: runtime Eq. (5) (§2.11) -/

/-- One lookup addition takes about 14 ms (lookup) + 22 ms (addition) + 1 ms
(remainder) = 37 ms (§2.11). -/
theorem lookupAddition_milliseconds : (14 : ℚ) + 22 + 1 = 37 := by norm_num

/-- Eq. (5): `TotalRuntime(n, n_e) ≈ 4 n_e n` milliseconds. -/
def totalRuntimeMilliseconds (n ne : ℕ) : ℚ := 4 * ne * n

/-- At `n = 2048` the paper uses `n_e = 3n/2 = 3072`. -/
theorem exponentQubits_2048 : (3072 : ℕ) = 3 * 2048 / 2 := by norm_num

/-- Eq. (5) at `n = 2048`, `n_e = 3072`: `4 · 3072 · 2048 = 25,165,824` ms. -/
theorem totalRuntimeMilliseconds_2048 :
    totalRuntimeMilliseconds 2048 3072 = 25165824 := by
  norm_num [totalRuntimeMilliseconds]

/-- Eq. (5) at `n = 2048`: the run takes `25,165,824 ms / 3,600,000 ≈ 6.99 h`,
under 8 hours. -/
theorem totalRuntime_hours_2048_le_eight :
    totalRuntimeMilliseconds 2048 3072 / 3600000 ≤ 8 := by
  norm_num [totalRuntimeMilliseconds]

/-- §2.13: the computation spans `4 n_e n · 1000` surface-code cycles, i.e.
about 25 billion cycles at `n = 2048`. -/
def surfaceCodeCycles (n ne : ℕ) : ℕ := 4 * ne * n * 1000

/-- `4 · 3072 · 2048 · 1000 = 25,165,824,000 ≈ 25` billion cycles (§2.13). -/
theorem surfaceCodeCycles_2048 : surfaceCodeCycles 2048 3072 = 25165824000 := by
  norm_num [surfaceCodeCycles]

/-- **c001, consolidated.**  The paper's title claim together with its two
supporting arithmetic derivations at `n = 2048`. -/
theorem mainResult_2048 :
    oursParallel.physicalQubitsMillions = 20 ∧ oursParallel.runtimeDays * 24 ≤ 8 ∧
      physicalQubits 27 2048 ≤ 23000000 ∧
      totalRuntimeMilliseconds 2048 3072 / 3600000 ≤ 8 :=
  ⟨oursParallel_physicalQubitsMillions, oursParallel_runtime_le_eight_hours,
    physicalQubits_2048_le_23M, totalRuntime_hours_2048_le_eight⟩

/-! ### c001 support: topological error and retry factor (§2.13) -/

/-- Per-cycle logical error probability `10^{-⌈d/2+1⌉}` for code distance `d`
(§2.13, following [29]); for `d = 27` this is `10⁻¹⁵`. -/
def logicalErrorPerCycle (d : ℕ) : ℚ := (1 / 10 : ℚ) ^ ((d + 1) / 2 + 1)

/-- Expected number of topological errors over the whole computation: the
per-cycle logical error times the number of non-distillation logical qubits
(`226 · 63 · 0.75` at `n = 2048`) times the number of surface-code cycles
(§2.13). -/
def topologicalErrorProbability (n d : ℕ) : ℚ :=
  logicalErrorPerCycle d * ((logicalBoardQubits n : ℚ) * (3 / 4)) *
    (surfaceCodeCycles n (3 * n / 2) : ℚ)

/-- At `n = 2048`, `d = 27`: `10⁻¹⁵ · 226 · 63 · 0.75 · 25,165,824,000 ≈ 0.2687`,
so the topological error probability is about 27% (§2.13). -/
theorem topologicalErrorProbability_2048_le :
    topologicalErrorProbability 2048 27 ≤ 27 / 100 := by
  norm_num [topologicalErrorProbability, logicalErrorPerCycle, logicalBoardQubits,
    boardWidth, boardHeight, surfaceCodeCycles]

/-- With a 27% topological error probability, the expected number of runs
`1/(1-p)` is about `1.37`, matching the paper's "roughly 1.4 times" (§2.13). -/
theorem retryFactor_2048_le : (1 : ℚ) / (1 - 27 / 100) ≤ 7 / 5 := by norm_num

/-- Table 3/Table 2 consistency: a per-run runtime of `5.1` hours at a 31%
retry risk gives an expected runtime `5.1/(1-0.31) ≈ 7.39` hours, below the
8-hour title figure. -/
theorem expectedRuntime_hours_le : (51 / 10 : ℚ) / (1 - 31 / 100) ≤ 8 := by
  norm_num

/-- Table 2 row consistency: `5.9` megaqubit-days at `20` megaqubits implies
`0.295` days `= 7.08` hours, compatible with the `0.31` day rounding. -/
theorem oursParallel_volume_implies_hours :
    oursParallel.volumeMegaQubitDays / oursParallel.physicalQubitsMillions * 24 = 177 / 25 := by
  norm_num [oursParallel]

end Qatlib.Papers.RSAFactoring19.MainResults.ResourceEstimate

/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in

/-- The canonical polynomial constraints have no complex solution when `r` squares to three. -/
theorem no_solution (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ)
    (hr : r ^ 2 = 3)
    (h0 : x1*y1 - 1 = 0)
    (h1 : x2*y2 - 1 = 0)
    (h2 : x3*y3 - 1 = 0)
    (h3 : x4*y4 - 1 = 0)
    (h4 : x5*y5 - 1 = 0)
    (h5 : (x1 + x2 + x3 + x4 + x5 + 1) * (y1 + y2 + y3 + y4 + y5 + 1) - 6 = 0)
    (h6 : (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) + x3 + x4*(-1/2 - r*Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) + y3 + y4*(-1/2 + r*Complex.I/2) + y5*(-1/2 - r*Complex.I/2) + 1) - 6 = 0)
    (h7 : (x1*(-1/2 + r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + x3 + x4*(-1/2 + r*Complex.I/2) + x5*(-1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 - r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + y3 + y4*(-1/2 - r*Complex.I/2) + y5*(-1/2 + r*Complex.I/2) + 1) - 6 = 0)
    (h8 : (x1 + x2 - x3 - x4 - x5 + 1) * (y1 + y2 - y3 - y4 - y5 + 1) - 6 = 0)
    (h9 : (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) - x3 + x4*(1/2 + r*Complex.I/2) + x5*(1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) - y3 + y4*(1/2 - r*Complex.I/2) + y5*(1/2 + r*Complex.I/2) + 1) - 6 = 0)
    (h10 : (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) - Complex.I*x3 + x4*(-r/2 + Complex.I/2) + x5*(-r/2 + Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + Complex.I*y3 + y4*(-r/2 - Complex.I/2) + y5*(-r/2 - Complex.I/2) + 1) - 6 = 0)
    (h11 : (x1*(-1/2 + r*Complex.I/2) + x2 - Complex.I*x3 + x4*(r/2 + Complex.I/2) - Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 + Complex.I*y3 + y4*(r/2 - Complex.I/2) + Complex.I*y5 + 1) - 6 = 0)
    (h12 : (x1 + x2*(-1/2 + r*Complex.I/2) - Complex.I*x3 - Complex.I*x4 + x5*(r/2 + Complex.I/2) + 1) * (y1 + y2*(-1/2 - r*Complex.I/2) + Complex.I*y3 + Complex.I*y4 + y5*(r/2 - Complex.I/2) + 1) - 6 = 0)
    (h13 : (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + Complex.I*x3 + x4*(r/2 - Complex.I/2) + x5*(r/2 - Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) - Complex.I*y3 + y4*(r/2 + Complex.I/2) + y5*(r/2 + Complex.I/2) + 1) - 6 = 0)
    (h14 : (x1*(-1/2 + r*Complex.I/2) + x2 + Complex.I*x3 + x4*(-r/2 - Complex.I/2) + Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 - Complex.I*y3 + y4*(-r/2 + Complex.I/2) - Complex.I*y5 + 1) - 6 = 0)
    : False := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  have g0 : x1*y1 - 1 = 0 := h0
  have g1 : x2*y2 - 1 = 0 := h1
  have g2 : x3*y3 - 1 = 0 := h2
  have g3 : x4*y4 - 1 = 0 := h3
  have g4 : x5*y5 - 1 = 0 := h4
  have g5 : x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 = 0 := by
    linear_combination (norm := ring_nf) (1) * h5 + (-1) * g0 + (-1) * g1 + (-1) * g2 + (-1) * g3 + (-1) * g4
  have g6 : x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 = 0 := by
    linear_combination (norm := ring_nf) (-r*Complex.I/3) * h6 + (r*Complex.I/3) * g0 + (r*Complex.I/3) * g1 + (r*Complex.I/3) * g2 + (r*Complex.I/3) * g3 + (r*Complex.I/3) * g4 + (1/2 - r*Complex.I/6) * g5
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have g7 : x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 = 0 := by
    linear_combination (norm := ring_nf) (1/3) * h7 + (-1/3) * g0 + (-1/3) * g1 + (-1/3) * g2 + (-1/3) * g3 + (-1/3) * g4 + (1/6 - r*Complex.I/6) * g5 + (r*Complex.I/3) * g6
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have g8 : -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 = 0 := by
    linear_combination (norm := ring_nf) (-1/2) * h8 + (1/2) * g0 + (1/2) * g1 + (1/2) * g2 + (1/2) * g3 + (1/2) * g4 + (1/2) * g5 + (-1) * g6 + (-1/2 - r*Complex.I/2) * g7
  have g9 : x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 = 0 := by
    linear_combination (norm := ring_nf) (-r*Complex.I/6) * h9 + (r*Complex.I/6) * g0 + (r*Complex.I/6) * g1 + (r*Complex.I/6) * g2 + (r*Complex.I/6) * g3 + (r*Complex.I/6) * g4 + (1/4 - r*Complex.I/12) * g5 + (r*Complex.I/6) * g6 + (-1/2 - r*Complex.I/6) * g7 + (-1/2 + r*Complex.I/6) * g8
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have thresholdGoal : x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 = 0 := by
    linear_combination (norm := ring_nf) (r/6 - Complex.I/2) * h10 + (-r/6 + Complex.I/2) * g0 + (-r/6 + Complex.I/2) * g1 + (-r/6 + Complex.I/2) * g2 + (-r/6 + Complex.I/2) * g3 + (-r/6 + Complex.I/2) * g4 + (-r/6 + Complex.I/2) * g5 + (-1/2 + r/6 - Complex.I/2 + r*Complex.I/6) * g6 + (1/2 + r/3 - r*Complex.I/6) * g7 + (r/6 + 1/2 - Complex.I/2 + r*Complex.I/6) * g8 + (1) * g9
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause11 : x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) = 0 := by
    linear_combination (norm := ring_nf) (r/6 + Complex.I/6) * h11 + (-r/6 - Complex.I/6) * g0 + (-r/6 - Complex.I/6) * g1 + (-r/6 - Complex.I/6) * g2 + (-r/6 - Complex.I/6) * g3 + (-r/6 - Complex.I/6) * g4 + (Complex.I/3) * g5 + (1/3 - Complex.I/3) * g6 + (-1/3 + r/6 - Complex.I/6 + r*Complex.I/3) * g7 + (1/3 - Complex.I/3) * g8 + (r/6 - Complex.I/2) * g9 + (-1/2 + r*Complex.I/6) * thresholdGoal
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause12 : x1*y4 + x2*y5 + y3 = 0 := by
    linear_combination (norm := ring_nf) (-Complex.I/6) * h12 + (Complex.I/6) * g0 + (Complex.I/6) * g1 + (Complex.I/6) * g2 + (Complex.I/6) * g3 + (Complex.I/6) * g4 + (-r/12 - Complex.I/12) * g5 + (r/12 + 1/6 + Complex.I/12) * g6 + (1/12 + r*Complex.I/12 + Complex.I/6) * g7 + (-1/12 + r/12 + Complex.I/12 + r*Complex.I/12) * g8 + (-1/4 + r/6 + r*Complex.I/12) * g9 + (-r*Complex.I/6) * thresholdGoal + (-1/4 - r*Complex.I/4) * clause11
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause13 : x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (-1/4 + r*Complex.I/12) * h13 + (1/4 - r*Complex.I/12) * g0 + (1/4 - r*Complex.I/12) * g1 + (1/4 - r*Complex.I/12) * g2 + (1/4 - r*Complex.I/12) * g3 + (1/4 - r*Complex.I/12) * g4 + (1/4 - r*Complex.I/12) * g5 + (-r/6 - 1/4 + r*Complex.I/12) * g6 + (-1/4 + r/6 - r*Complex.I/12) * g7 + (-1/4 + r/12 + r*Complex.I/12 + Complex.I/4) * g8 + (r/4 + Complex.I/4) * g9 + (-r/4 - Complex.I/4) * thresholdGoal
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause14 : x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (1/12 + r*Complex.I/12) * h14 + (-1/12 - r*Complex.I/12) * g0 + (-1/12 - r*Complex.I/12) * g1 + (-1/12 - r*Complex.I/12) * g2 + (-1/12 - r*Complex.I/12) * g3 + (-1/12 - r*Complex.I/12) * g4 + (-1/12 + r*Complex.I/12) * g5 + (-r/12 + 1/12 - r*Complex.I/12 - Complex.I/12) * g6 + (1/6 + r/6 - Complex.I/6) * g7 + (-r/12 + 1/12 - r*Complex.I/12 - Complex.I/12) * g8 + (1/4 - r*Complex.I/12) * g9 + (r/6) * thresholdGoal + (r/4 + Complex.I/4) * clause11 + (1/2 - r*Complex.I/6) * clause13
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have walkGoal : x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y3*(-1/2 - r*Complex.I/2)) * g4 + (y5*(1/2 + r*Complex.I/2)) * clause14
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause16 : x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) = 0 := by
    linear_combination (norm := ring_nf) (y1*(-3/2 + r*Complex.I/2) + y3*(r/2 - 3*Complex.I/2)) * g4 + (y5*(3/2 - r*Complex.I/2)) * g8 + (y5*(3/2 - r*Complex.I/2)) * g9 + (y5*(-3/2 + r*Complex.I/2)) * thresholdGoal + (y5*(-3/2 + r*Complex.I/2)) * clause11 + (y5*(1 + r*Complex.I)) * clause12 + (y5*(-r/2 + 3*Complex.I/2)) * clause13 + (-r/2 - 3*Complex.I/2) * walkGoal
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause17 : x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y3*(-1/2 - r*Complex.I/2)) * g3 + (y4*(1/2 + r*Complex.I/2)) * clause13 + (-1/2 - r*Complex.I/2) * clause12 + (y4*(-1/2 - r*Complex.I/2)) * clause14 + (-1) * walkGoal
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause18 : x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) = 0 := by
    linear_combination (norm := ring_nf) (y2*(-3/2 + r*Complex.I/2)) * g3 + (y4*(3/2 - r*Complex.I/2)) * clause11 + (y4*(1 - r*Complex.I) + y5*(1/2 + r*Complex.I/2)) * clause12 + (y4*(-r/2 + 3*Complex.I/2)) * clause14
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause19 : -x1/2 + x2*x4*y5 + x3*y5*(-1/2 + r*Complex.I/2) + y2*(-3/4 + 3*r*Complex.I/4) = 0 := by
    linear_combination (norm := ring_nf) (y2*(1/4 - r*Complex.I/4)) * g3 + (x4*(-1/4 + r*Complex.I/4)) * clause17 + (y2*(1/4 - r*Complex.I/4)) * g4 + (y5*(-1/4 + r*Complex.I/4)) * g7 + (y5*(1/4 - r*Complex.I/4)) * clause12 + (-1/2) * clause13 + (1/2) * clause14
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause20 : -x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4 = 0 := by
    linear_combination (norm := ring_nf) (y4*(3/4 - r*Complex.I/4)) * thresholdGoal + (x3*(-3/4 + r*Complex.I/4) - r/4 - 3*Complex.I/4) * clause17 + (-3/4 - r*Complex.I/4) * g2 + (y2*(3/4 - r*Complex.I/4) + y3*(r/4 - 3*Complex.I/4) - 3/4 - r*Complex.I/4) * g3 + (y3*(-r/4 + 3*Complex.I/4) + 3/4 + r*Complex.I/4) * g4 + (y5*(-3/4 + r*Complex.I/4)) * g6 + (-r*Complex.I*y5/2) * g7 + (y5*(3/4 - r*Complex.I/4)) * g9 + (y5*(3/4 - r*Complex.I/4)) * clause11 + (y3*(-1/4 + r*Complex.I/4) - y4 + y5*(1/4 - 3*r*Complex.I/4) + r/4 - 3*Complex.I/4) * clause12 + (y4*(r/4 - 3*Complex.I/4)) * clause14 + (1/2) * clause18
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause22 : x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y4*(1/2 - r*Complex.I/2)) * g9 + (y2*(-1/2 + r*Complex.I/2)) * clause12 + (y5*(1/2 - r*Complex.I/2)) * g1 + (y5*(-1/2 + r*Complex.I/2)) * g3 + (y4*(-1/2 + r*Complex.I/2)) * clause14
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause24 : x2 + y1*(1/2 - r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y1*(-1/2 + r*Complex.I/2)) * g3 + (y4*(1/2 - r*Complex.I/2)) * g7 + (-2*x2 + y1*(-1/2 + r*Complex.I/2)) * g4 + (y4*(-1/2 + r*Complex.I/2)) * clause12 + (-1) * clause14 + (x5*(-1/2 + r*Complex.I/2)) * clause17
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause25 : y1*y2 + 1/2 + r*Complex.I/2 = 0 := by
    linear_combination (norm := ring_nf) (-1/2 - r*Complex.I/2) * g1 + (y2*(1/2 + r*Complex.I/2)) * clause24
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause26 : x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (-1/2 - r*Complex.I/2) * g5 + (y1*(1/2 + r*Complex.I/2)) * clause24 + (1/2 + r*Complex.I/2) * g6 + (-1/2 + r*Complex.I/2) * g7 + (1/2 + r*Complex.I/2) * g8 + (1/2 + r*Complex.I/2) * g9 + (1/2 + r*Complex.I/2) * clause13 + (-1/2 - r*Complex.I/2) * clause14
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause27 : x1 + y2*(1/2 - r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (-2) * clause19 + (2*x4*y5) * clause24 + (y2*(1 - r*Complex.I)) * g4 + (y5*(-1 + r*Complex.I)) * g7 + (y5*(1 - r*Complex.I)) * clause12
  have clause28 : x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2 = 0 := by
    linear_combination (norm := ring_nf) (-1/2 - r*Complex.I/2) * g9 + (y2*(1/2 + r*Complex.I/2)) * clause27 + (1/2 + r*Complex.I/2) * clause14
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause29 : x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2 = 0 := by
    linear_combination (norm := ring_nf) (-1/2 - r*Complex.I/2) * clause16 + (y3*y5*(1/2 + r*Complex.I/2)) * clause27 + (y4*y5*(1/2 - r*Complex.I/2)) * clause24
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause31 : y1*y4^2 + y2*y5^2 + y3^2/2 + y4*y5*(1/2 - r*Complex.I/2) - 3*r*Complex.I/2 = 0 := by
    linear_combination (norm := ring_nf) (-1/2 - r*Complex.I/2) * clause20 + (r*Complex.I*x3*y5 + y4^2*(1/2 + r*Complex.I/2)) * clause24 + (-r*y3 + r*Complex.I) * g4 + (y5*(-3/2 - r*Complex.I/2)) * g6 + (y5*(3/2 - r*Complex.I/2)) * g7 + (y5*(3/2 + r*Complex.I/2)) * g9 + (y5*(3/2 + r*Complex.I/2)) * clause11 + (2*y5) * clause12 + (-r/2 + 3*Complex.I/2) * walkGoal + (y5^2*(1/2 + r*Complex.I/2)) * clause27
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause32 : x5*y4*(-3/2 + r*Complex.I/2) + y1*y3*y4 + y1*y5^2*(1/2 + r*Complex.I/2) + y2*(-3/2 - r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/2) - 2*y4^2 = 0 := by
    linear_combination (norm := ring_nf) (-1/2 - r*Complex.I/2) * clause18 + (y3*y4*(1/2 + r*Complex.I/2) + y5^2*(-1/2 + r*Complex.I/2)) * clause24
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause33 : -r*Complex.I*x3*y4 + x4*y5*(-9/2 - 3*r*Complex.I/2) + y1*y3^2 + y1*y4*y5*(2 - 2*r*Complex.I) - 2*r*Complex.I*y1 - 2*y3*y4 + y5^2*(-5/2 - 5*r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y3*(-3/2 - r*Complex.I/2) + y5*(-3/2 + r*Complex.I/2)) * clause11 + (y2*(3/2 + r*Complex.I/2) + y5*(-r/2 + 3*Complex.I/2)) * clause13 + (y3*(r/2 - 3*Complex.I/2)) * g4 + (-3/2 - r*Complex.I/2) * g9 + (y5*(-3/2 + r*Complex.I/2)) * thresholdGoal + (-2*y3 + y5*(1 + r*Complex.I)) * clause12 + (y2*(-3/2 - r*Complex.I/2) + r*y3 + 3) * clause14 + (-r/2 - 3*Complex.I/2) * walkGoal + (1 - r*Complex.I) * clause16 + (y3^2*(1/2 + r*Complex.I/2) + 4*y4*y5 - 3/2 + r*Complex.I/2) * clause24 + (-3/2 + r*Complex.I/2) * clause28
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have tunableGoal : r*Complex.I*x3*y5 + x5*y4*(3 + r*Complex.I) + y1*y5^2*(1 - r*Complex.I) + y2*y3^2 + r*Complex.I*y2 - y3*y5 + y4^2*(2 + 2*r*Complex.I) = 0 := by
    linear_combination (norm := ring_nf) (r*Complex.I*y2) * g2 + (-r*Complex.I*y3) * thresholdGoal + (-r*Complex.I*y3) * clause11 + (-2*y3) * clause12 + (y3*(-r/2 - 3*Complex.I/2) - 3/2 + r*Complex.I/2) * clause13 + (y3*(r/2 + 3*Complex.I/2) + 3/2 - r*Complex.I/2) * clause14 + (-1 + r*Complex.I) * clause18 + (2*y5^2) * clause24 + (y3^2*(1/2 + r*Complex.I/2) + 3/2 - r*Complex.I/2) * clause27
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have optGoal : x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4) = 0 := by
    linear_combination (norm := ring_nf) (r*Complex.I*y3/6 - r*Complex.I/6) * g8 + (-r*Complex.I*y1/6 - 1/4 + r*Complex.I/4) * clause14 + (-r*Complex.I*y2/6) * g2 + (y1*(-1/4 + r*Complex.I/12) + y2*(-1/4 - r*Complex.I/12)) * g3 + (x2*(-1/2 - r*Complex.I/6) + y1*(-1/4 + r*Complex.I/12)) * g4 + (r*Complex.I/6) * g5 + (y4*(1/4 + r*Complex.I/12) - r*Complex.I/6) * g6 + (1/4 - r*Complex.I/12) * g7 + (r*Complex.I*y3/6 + y4*(-1/4 - r*Complex.I/12) - r*Complex.I/6) * g9 + (y4*(-1/4 + r*Complex.I/12) + y5*(-1/4 - r*Complex.I/12)) * clause12 + (-r*Complex.I/3) * clause13 + (x5*(-1/4 + r*Complex.I/12)) * clause17 + (-1/4 - r*Complex.I/4) * clause18 + (r*Complex.I*y5^2/3 - 1/4 - r*Complex.I/12) * clause24 + (1/4 + r*Complex.I/12) * clause26 + (-r*Complex.I*y3^2/6 + r*Complex.I/6) * clause27 + (1/4 + r*Complex.I/12) * tunableGoal
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause36 : x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4) = 0 := by
    linear_combination (norm := ring_nf) (y1*(1/4 - r*Complex.I/12)) * g2 + (y3*(-1/4 + r*Complex.I/12)) * g6 + (-r*Complex.I*y3/6) * g7 + (y3*(1/4 - r*Complex.I/12)) * g9 + (y3*(1/4 - r*Complex.I/12)) * clause11 + (y3*(1/6 - r*Complex.I/6)) * clause12 + (y3*(-r/12 + Complex.I/4) + 1/4 + r*Complex.I/12) * clause14 + (1/3) * clause16 + (y3^2*(1/12 - r*Complex.I/12) + y4*y5*(1/6 + r*Complex.I/6) - 1/4 - r*Complex.I/12) * clause24 + (1/12 + r*Complex.I/12) * clause33
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause39 : x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6) = 0 := by
    linear_combination (norm := ring_nf) (-2*y2/3) * clause25 + (2*y1/3) * clause28 + (y1*(-1/3 - r*Complex.I/3) + y2*(1/3 - r*Complex.I/3)) * g3 + (x2*(2/3 - 2*r*Complex.I/3) + y1*(-1/3 - r*Complex.I/3) + y2*(-1/3 - r*Complex.I/3)) * g4 + (y4*(-1/3 + r*Complex.I/3)) * g6 + (y5*(1/3 + r*Complex.I/3)) * g7 + (y4*(1/3 - r*Complex.I/3)) * g9 + (y4*(-1/3 - r*Complex.I/3) - 2*r*Complex.I*y5/3) * clause12 + (1/3 - r*Complex.I/3) * clause14 + (x5*(-1/3 - r*Complex.I/3)) * clause17 + (1/3 - r*Complex.I/3) * clause18 + (y5^2*(-1 + r*Complex.I/3) + 1/3 - r*Complex.I/3) * clause24 + (-1/3 + r*Complex.I/3) * clause26 + (-2*r*Complex.I/3) * optGoal
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause41 : -r*Complex.I*y1*y4 + y2*y3*(3 + r*Complex.I) + y3^2*y5*(1/2 - r*Complex.I/2) + y3*y4^2 + y5*(3 + r*Complex.I) = 0 := by
    linear_combination (norm := ring_nf) (y4*(-3/2 + r*Complex.I/2)) * clause14 + (y3*(3/2 - r*Complex.I/2)) * clause39 + (y5*(-3 - r*Complex.I)) * g2 + (-r*Complex.I) * clause22 + (y4*(3/2 - r*Complex.I/2)) * clause24
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause42 : x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) = 0 := by
    linear_combination (norm := ring_nf) (x5/4 + y4*(1/8 + r*Complex.I/24)) * clause17 + (-y2/4) * clause39 + (x2*(1/4 + r*Complex.I/4) + y1/4 + y3*(-r/4 - Complex.I/4)) * g4 + (y5*(1/4 + r*Complex.I/4)) * thresholdGoal + (y5*(1/4 + r*Complex.I/4)) * clause11 + (y5*(1/2 - r*Complex.I/6)) * clause12 + (y5*(r/4 + Complex.I/4)) * clause13 + (1/8 + r*Complex.I/8) * clause14 + (-r/4 + Complex.I/4) * walkGoal + (-1/4 - r*Complex.I/12) * clause16 + (-r*Complex.I*y4*y5/3 + 1/8 + r*Complex.I/8) * clause24 + (1/8 + r*Complex.I/8) * clause28 + (1/8 - r*Complex.I/24) * clause29 + (3/4 + r*Complex.I/4) * clause36
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause43 : x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8) = 0 := by
    linear_combination (norm := ring_nf) (-r*Complex.I) * walkGoal + (r*Complex.I*y5) * clause42 + (y5*(-3/2 + r*Complex.I/2)) * clause24
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause44 : y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4 = 0 := by
    linear_combination (norm := ring_nf) (-3/2 + r*Complex.I/2) * clause22 + (y4*(3/2 - r*Complex.I/2)) * clause42 + (r*Complex.I*y5/4) * g3 + (1/2 + r*Complex.I/2) * clause41
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause46 : y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2 = 0 := by
    linear_combination (norm := ring_nf) (4*r*Complex.I*y4/7) * thresholdGoal + (-4*r*Complex.I*y2/7) * clause42 + (4*r*Complex.I*y2/7 + y3*(2*r/7 + 6*Complex.I/7) + 6/7 - 2*r*Complex.I/7) * g3 + (y3*(-5*r/7 - 12*Complex.I/7) - 27/14 + 9*r*Complex.I/14) * g4 + (-8*r*Complex.I*y5/7) * g6 + (y5*(12/7 + 4*r*Complex.I/7)) * g7 + (8*r*Complex.I*y5/7) * g9 + (y5*(3/14 + 17*r*Complex.I/14)) * clause11 + (y3*(-2/7 - 2*r*Complex.I/7) + y4*(4/7 - 4*r*Complex.I/7) + y5*(2 + 8*r*Complex.I/7) + 2*r/7 + 6*Complex.I/7) * clause12 + (y4*(2*r/7 + 6*Complex.I/7)) * clause14 + (-9*r/14 + 3*Complex.I/14) * walkGoal + (4*y3/7 + 4*r/7) * clause17 + (-2/7 + 2*r*Complex.I/7) * clause18 + (4/7 - 4*r*Complex.I/7) * clause20 + (x3*y5*(-12/7 + 4*r*Complex.I/7) + y3*y5*(11/14 + 11*r*Complex.I/14)) * clause24 + (2*r*Complex.I/7) * clause25 + (y5^2*(-9/14 + 9*r*Complex.I/14)) * clause27
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause47 : y2*y5^2 + 5*y3^2/4 + y4*y5*(-1/2 + r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y4*(-7/8 + 7*r*Complex.I/24)) * g8 + (y1*(7/8 - 7*r*Complex.I/24)) * clause39 + (y2*(7/8 - 7*r*Complex.I/24) + y3*(7*r/24 - 7*Complex.I/8) - 7*r*Complex.I/12) * g3 + (-7*r*y3/4 + 7*r*Complex.I/4) * g4 + (y5*(-21/8 - 7*r*Complex.I/8)) * g6 + (y5*(21/8 - 7*r*Complex.I/8)) * g7 + (y4*(-7/8 + 7*r*Complex.I/24) + y5*(21/8 + 7*r*Complex.I/8)) * g9 + (y4*(7/8 - 7*r*Complex.I/24)) * thresholdGoal + (y5*(21/8 + 7*r*Complex.I/8)) * clause11 + (7*y3/12 - 7*y4/6 + y5*(77/24 - 7*r*Complex.I/24) + 7*r/24 - 7*Complex.I/8) * clause12 + (y4*(7*r/24 - 7*Complex.I/8)) * clause14 + (-7*r/6 + 7*Complex.I/4) * walkGoal + (-7*r/24 - 7*Complex.I/8) * clause17 + (7/12) * clause18 + (-7/24 - 7*r*Complex.I/24) * clause20 + (7*r*Complex.I*x3*y5/12 + 7*y3*y5/12) * clause24 + (-7/8 - 7*r*Complex.I/24) * clause25 + (y5^2*(35/24 + 35*r*Complex.I/24)) * clause27 + (-7/12) * clause31 + (-7/12 + 7*r*Complex.I/12) * clause46
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause48 : x3*y5 - 2*r*Complex.I*y3*y5/3 = 0 := by
    linear_combination (norm := ring_nf) (y4*(2/3 + 2*r*Complex.I/3)) * g6 + (y1*(-2/3 - 2*r*Complex.I/3)) * clause42 + (-4*y1/3 + y2*(-2/3 - 2*r*Complex.I/3)) * g3 + (x2*(-4/3 - 4*r*Complex.I/3) - 4*y1/3 - y2/3) * g4 + (y5/3) * g7 + (y4*(-2/3 - 2*r*Complex.I/3)) * g9 + (-4*y4/3 + y5*(-1 - 2*r*Complex.I/3)) * clause12 + (-2/3 - 2*r*Complex.I/3) * clause14 + (-4*x5/3) * clause17 + (-2/3 - 2*r*Complex.I/3) * clause18 + (4*r*Complex.I*y5^2/3 - 2/3 - 2*r*Complex.I/3) * clause24 + (1/3 + r*Complex.I/3) * clause26 + (2/3 - 2*r*Complex.I/9) * clause32 + (-5/2 - 5*r*Complex.I/6) * optGoal + (-5/12 + 5*r*Complex.I/12) * clause39
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause50 : x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6) = 0 := by
    linear_combination (norm := ring_nf) (1 + r*Complex.I) * walkGoal + (y4*(-1 - r*Complex.I)) * clause48 + (y5*(1 - r*Complex.I)) * clause24 + (2 - 2*r*Complex.I/3) * clause43
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause51 : y1*y4*(3 + r*Complex.I) + y2*y3*(-6 + 2*r*Complex.I) + y4*y5^2 + y5*(-15/2 + 5*r*Complex.I/2) = 0 := by
    linear_combination (norm := ring_nf) (y5*(-3 + r*Complex.I)) * g2 + (y3*(3 - r*Complex.I)) * clause48 + (2 + 2*r*Complex.I) * clause44
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause52 : x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20) = 0 := by
    linear_combination (norm := ring_nf) (y5*(-9/5 + 3*r*Complex.I/5)) * thresholdGoal + (y2*(9/5 - 3*r*Complex.I/5)) * clause48 + (y3*(3*r/5 - 9*Complex.I/5)) * g4 + (y5*(-9/5 + 3*r*Complex.I/5)) * clause11 + (y5*(6/5 + 6*r*Complex.I/5)) * clause12 + (y5*(-3*r/5 + 9*Complex.I/5)) * clause13 + (-3*r/5 - 9*Complex.I/5) * walkGoal + (3/5 - 3*r*Complex.I/5) * clause16 + (18*y4*y5/5) * clause24 + (6/5 + 6*r*Complex.I/5) * clause29 + (-3 + 3*r*Complex.I) * clause36 + (-2*r*Complex.I) * clause42
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause53 : y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3 = 0 := by
    linear_combination (norm := ring_nf) (-5/4 + 5*r*Complex.I/4) * clause43 + (y5*(5/4 - 5*r*Complex.I/4)) * clause52 + (33/16 - 11*r*Complex.I/16) * clause50
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause54 : y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7 = 0 := by
    linear_combination (norm := ring_nf) (y5*(-3/7 - r*Complex.I/7)) * g6 + (y1*(3/7 + r*Complex.I/7)) * clause48 + (-2*r*y3/7 + 2*r*Complex.I/7) * g4 + (y5*(3/7 - r*Complex.I/7)) * g7 + (y5*(3/7 + r*Complex.I/7)) * g9 + (y5*(3/7 + r*Complex.I/7)) * clause11 + (4*y5/7) * clause12 + (-r/7 + 3*Complex.I/7) * walkGoal + (2*y3*y5/7) * clause24 + (y5^2*(2/7 + 2*r*Complex.I/7)) * clause27 + (-3/7 + 3*r*Complex.I/7) * clause46 + (20/49) * clause47
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause55 : y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48 = 0 := by
    linear_combination (norm := ring_nf) (7*r*Complex.I/72) * clause44 + (-7*r*Complex.I*y5/72) * clause54 + (-31/192 - 31*r*Complex.I/576) * clause51
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause56 : x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864) = 0 := by
    linear_combination (norm := ring_nf) (-5/6 - 5*r*Complex.I/18) * clause29 + (y5*(5/6 + 5*r*Complex.I/18)) * clause55 + (-5*r*Complex.I/18) * clause36 + (5/36 + 5*r*Complex.I/36) * clause42 + (5/72 - 5*r*Complex.I/216) * clause52
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause57 : y1*y5 + y3*(13/68 + 13*r*Complex.I/68) = 0 := by
    linear_combination (norm := ring_nf) (-144/2125 + 144*r*Complex.I/2125) * clause50 + (y5*(144/2125 - 144*r*Complex.I/2125)) * clause56 + (-473/2125 + 473*r*Complex.I/6375) * clause53
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause60 : y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2 = 0 := by
    linear_combination (norm := ring_nf) (-4896/25043 - 4896*r*Complex.I/25043) * clause36 + (y4*(4896/25043 + 4896*r*Complex.I/25043)) * clause57 + (4896/25043 + 1632*r*Complex.I/25043) * clause42 + (2688/25043 - 2688*r*Complex.I/25043) * clause52 + (67176/125215 - 22392*r*Complex.I/125215) * clause56
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause61 : y3 = 0 := by
    linear_combination (norm := ring_nf) (-25043*r*Complex.I/51408) * clause53 + (25043*r*Complex.I*y5/51408) * clause60 + (7199/4032 - 7199*r*Complex.I/4032) * clause57
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause62 : y1 = 0 := by
    linear_combination (norm := ring_nf) (25043*r*Complex.I/88026) * clause52 + (-25043*r*Complex.I*y4/88026) * clause61 + (-75129/586840 + 75129*r*Complex.I/586840) * clause56 + (3330719/5633664 - 3330719*r*Complex.I/16900992) * clause60
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause63 : y4*y5 + 1 - r*Complex.I/3 = 0 := by
    linear_combination (norm := ring_nf) (-7/12 - 7*r*Complex.I/12) * clause54 + (y3*(7/12 + 7*r*Complex.I/12)) * clause61
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have clause64 : y5 = 0 := by
    linear_combination (norm := ring_nf) (48/61) * clause55 + (-48*y2/61) * clause61 + (y4*(12/61 + 12*r*Complex.I/61)) * clause62
  have clause65 : (1 : ℂ) = 0 := by
    linear_combination (norm := ring_nf) (3/4 + r*Complex.I/4) * clause63 + (y4*(-3/4 - r*Complex.I/4)) * clause64
    norm_num [hr, hr3, Complex.I_sq]
  norm_num at clause65

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood

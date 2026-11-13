/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
import PDE.Analysis.Scalar.OddPower
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.DomainOfDependence

/-!
# Domain of dependence for odd-power nonlinear waves

We specialize semilinear domain of dependence to

`uₜₜ - Δu + linear * u + nonlinear * u^(2k+1) = 0`.

Odd-power polynomials need not be globally Lipschitz, although the cases `k = 0`
and `nonlinear = 0` are linear. If two classical solutions remain in `[-R, R]`
on a backward cone, the polynomial's restriction to that interval is Lipschitz.
Mathlib's real-valued Lipschitz extension theorem
produces a globally Lipschitz function agreeing with the polynomial on the
solution range. The general cone-energy uniqueness theorem can then be applied
without repeating its transport and Grönwall argument.

The `_of_abs_le` theorems state the bounded-range argument. In the
unsuffixed theorems, global `C²` regularity
implies continuity, hence a common bound on the compact cylinder containing
the cone.

The coefficients are arbitrary real numbers; no defocusing sign condition is
needed for uniqueness on a bounded range.

The underlying result is the finite propagation speed theorem for semilinear wave equations:
two solutions with the same Cauchy data on the base ball `B(c, T - a)` agree on the backward
light cone `{(t, x) : a ≤ t ≤ T, |x - c| ≤ T - t}`. Its proof, in `DomainOfDependence`, is
the energy argument on the cone for a globally Lipschitz nonlinearity; for polynomial
nonlinearities the bounded-range Lipschitz extension `LipschitzOnWith.extend_real` (the
McShane extension) supplies one.

## Main results

* `eq_on_closed_backwardCone_of_eq_cauchyData_oddPower_of_abs_le`,
  `eq_on_open_backwardCone_of_eq_cauchyData_oddPower_of_abs_le`: uniqueness on the closed or
  open cone under an explicit common bound `|u|, |v| ≤ R` on the cone.
* `eq_on_closed_backwardCone_of_eq_cauchyData_oddPower`,
  `eq_on_open_backwardCone_of_eq_cauchyData_oddPower`: the same for arbitrary classical `C²`
  solutions, the bound being supplied by continuity on the compact cylinder.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE.Analysis.Scalar Set

namespace WaveEquation

variable {n : ℕ}

private theorem exists_common_abs_bound_on_closed_backwardCone {u v : ℝ^(n + 1) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (c : ℝ^n) (a T : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
        |u (PDE.Common.timeSpaceCons (n := n) t x)| ≤ R) ∧
      ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
        |v (PDE.Common.timeSpaceCons (n := n) t x)| ≤ R := by
  obtain ⟨Ru, hRu, huBound⟩ := PDE.Common.exists_norm_le_on_timeSpaceCylinder u hu a T c (T - a)
  obtain ⟨Rv, hRv, hvBound⟩ := PDE.Common.exists_norm_le_on_timeSpaceCylinder v hv a T c (T - a)
  refine ⟨max Ru Rv, hRu.trans (le_max_left _ _), ?_, ?_⟩
  · intro t ht x hx
    have hxCylinder : x ∈ Metric.closedBall c (T - a) :=
      Metric.closedBall_subset_closedBall (by linarith [ht.1]) hx
    simpa only [Real.norm_eq_abs] using (huBound t ht x hxCylinder).trans (le_max_left _ _)
  · intro t ht x hx
    have hxCylinder : x ∈ Metric.closedBall c (T - a) :=
      Metric.closedBall_subset_closedBall (by linarith [ht.1]) hx
    simpa only [Real.norm_eq_abs] using (hvBound t ht x hxCylinder).trans (le_max_right _ _)

/-- Two classical odd-power waves that satisfy a common absolute-value bound
and have equal Cauchy data on a closed base ball agree throughout the
corresponding closed backward cone. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_oddPower_of_abs_le [Fact (0 < n)]
    {linear nonlinear : ℝ} (k : ℕ) {R : ℝ} (hR : 0 ≤ R) {u v : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + linear * u p +
      nonlinear * (u p) ^ (2 * k + 1) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + linear * v p +
      nonlinear * (v p) ^ (2 * k + 1) = 0)
    (huBound : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; |u p| ≤ R)
    (hvBound : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; |v p| ≤ R)
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u)
      (PDE.Common.timeSpaceCons (n := n) a x) = (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (PDE.Common.timeSpaceCons (n := n) t
      x) = v (PDE.Common.timeSpaceCons (n := n) t x) := by
  obtain ⟨f, hf, hEq⟩ := (lipschitzOnWith_oddPowerPolynomial linear nonlinear k hR).extend_real
  apply eq_on_closed_backwardCone_of_eq_cauchyData_semilinear (n := n) hf hu hv c
  · intro t ht x hx
    let p := PDE.Common.timeSpaceCons (n := n) t x
    change waveOperator (n := n) u p + f (u p) = 0
    have huMem : u p ∈ Set.Icc (-R) R := abs_le.mp (huBound t ht x hx)
    rw [← hEq huMem]
    simpa only [oddPowerPolynomial, add_assoc] using huwave t ht x hx
  · intro t ht x hx
    let p := PDE.Common.timeSpaceCons (n := n) t x
    change waveOperator (n := n) v p + f (v p) = 0
    have hvMem : v p ∈ Set.Icc (-R) R := abs_le.mp (hvBound t ht x hx)
    rw [← hEq hvMem]
    simpa only [oddPowerPolynomial, add_assoc] using hvwave t ht x hx
  · exact hposition
  · exact hvelocity

/-- Two classical odd-power waves that satisfy a common absolute-value bound
and have equal Cauchy data on an open base ball agree throughout the
corresponding open backward cone. -/
theorem eq_on_open_backwardCone_of_eq_cauchyData_oddPower_of_abs_le [Fact (0 < n)]
    {linear nonlinear : ℝ} (k : ℕ) {R : ℝ} (hR : 0 ≤ R) {u v : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + linear * u p +
      nonlinear * (u p) ^ (2 * k + 1) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + linear * v p +
      nonlinear * (v p) ^ (2 * k + 1) = 0)
    (huBound : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; |u p| ≤ R)
    (hvBound : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; |v p| ≤ R)
    (hposition : ∀ x ∈ Metric.ball c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.ball c (T - a), (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t), u (PDE.Common.timeSpaceCons (n := n) t x) =
      v (PDE.Common.timeSpaceCons (n := n) t x) := by
  obtain ⟨f, hf, hEq⟩ := (lipschitzOnWith_oddPowerPolynomial linear nonlinear k hR).extend_real
  apply eq_on_open_backwardCone_of_eq_cauchyData_semilinear (n := n) hf hu hv c
  · intro t ht x hx
    let p := PDE.Common.timeSpaceCons (n := n) t x
    change waveOperator (n := n) u p + f (u p) = 0
    have huMem : u p ∈ Set.Icc (-R) R := abs_le.mp (huBound t ht x hx)
    rw [← hEq huMem]
    simpa only [oddPowerPolynomial, add_assoc] using huwave t ht x hx
  · intro t ht x hx
    let p := PDE.Common.timeSpaceCons (n := n) t x
    change waveOperator (n := n) v p + f (v p) = 0
    have hvMem : v p ∈ Set.Icc (-R) R := abs_le.mp (hvBound t ht x hx)
    rw [← hEq hvMem]
    simpa only [oddPowerPolynomial, add_assoc] using hvwave t ht x hx
  · exact hposition
  · exact hvelocity

/-- Two classical odd-power waves with equal Cauchy data on a closed base ball
agree throughout the corresponding closed backward cone.

No range bound is required: continuity bounds both solutions on the compact
time-space cylinder containing the cone. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_oddPower [Fact (0 < n)] {linear nonlinear : ℝ}
    (k : ℕ) {u v : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + linear * u p +
      nonlinear * (u p) ^ (2 * k + 1) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + linear * v p +
      nonlinear * (v p) ^ (2 * k + 1) = 0)
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u)
      (PDE.Common.timeSpaceCons (n := n) a x) = (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (PDE.Common.timeSpaceCons (n := n) t
      x) = v (PDE.Common.timeSpaceCons (n := n) t x) := by
  obtain ⟨R, hR, huBound, hvBound⟩ := exists_common_abs_bound_on_closed_backwardCone
      hu.continuous hv.continuous c a T
  apply eq_on_closed_backwardCone_of_eq_cauchyData_oddPower_of_abs_le
    (n := n) k hR hu hv c huwave hvwave
  · intro t ht x hx
    exact huBound t (Set.Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall hx)
  · intro t ht x hx
    exact hvBound t (Set.Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall hx)
  · exact hposition
  · exact hvelocity

/-- Two classical odd-power waves with equal Cauchy data on an open base ball
agree throughout the corresponding open backward cone.

No range bound is required: continuity bounds both solutions on the compact
time-space cylinder containing the cone. -/
theorem eq_on_open_backwardCone_of_eq_cauchyData_oddPower [Fact (0 < n)] {linear nonlinear : ℝ}
    (k : ℕ) {u v : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + linear * u p +
      nonlinear * (u p) ^ (2 * k + 1) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + linear * v p +
      nonlinear * (v p) ^ (2 * k + 1) = 0)
    (hposition : ∀ x ∈ Metric.ball c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.ball c (T - a), (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t), u (PDE.Common.timeSpaceCons (n := n) t x) =
      v (PDE.Common.timeSpaceCons (n := n) t x) := by
  obtain ⟨R, hR, huBound, hvBound⟩ := exists_common_abs_bound_on_closed_backwardCone
      hu.continuous hv.continuous c a T
  apply eq_on_open_backwardCone_of_eq_cauchyData_oddPower_of_abs_le
    (n := n) k hR hu hv c huwave hvwave
  · intro t ht x hx
    exact huBound t (Set.Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall hx)
  · intro t ht x hx
    exact hvBound t (Set.Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall hx)
  · exact hposition
  · exact hvelocity

end WaveEquation

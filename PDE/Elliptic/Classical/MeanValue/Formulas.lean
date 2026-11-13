/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Elliptic.Classical.MeanValue.Definitions
import PDE.Analysis.Calculus.SphericalMean
import PDE.FDeriv.Calculus

/-!
# Spherical and ball mean-value formulas

Write `φ(r)` for the average of `u` over the sphere `∂B(x, r)`, computed on the unit sphere as
`φ(r) = (1/|∂B₁|) ∫_{∂B₁} u(x + r ω) dσ(ω)` (`unitSphereAverage`). The first step of the
classical mean-value argument (Evans, *PDE*, §2.2.2, proof of the mean-value formulas) is the
radial derivative

`φ'(r) = (1/|∂B₁|) ∫_{∂B₁} Du(x + r ω) · ω dσ(ω)`,

obtained by differentiating under the integral sign for a globally `C¹` function `u`, with
the Lipschitz bound of `u` on a compact ball as the dominating function. Evans's next step
rewrites the right-hand side as an integral of `Δu` over the ball by Green's formula. We do not
take it: `PDE.Elliptic.Classical.MeanValue.PDEToMeanValue` derives the mean-value property from
the Poisson representation instead.

The remaining results concern the abstract predicate `HasSphereMeanValueProperty`: a
function whose value at each `x` equals its average on every sphere `∂B(x, r)` with
`closedBall x r ⊆ U`. Integrating the sphere identity in polar coordinates (the coarea formula
on the ball) gives the ball mean-value property, and comparing the value with a bound on one
sphere gives the one-point inequalities that drive the weak maximum principle.

## Main results

* `hasDerivAt_sphereAverage`, `deriv_sphereAverage`: the radial derivative of the geometric
  spherical average of a `C¹` function on `ℝ^n`, obtained from the equation-independent
  `PDE.Analysis.hasDerivAt_unitSphereAverage`.
* `HasSphereMeanValueProperty.eq_ballAverage`: sphere averages determine ball averages,
  `u x = ballAverage n u x r`, assuming `u` is integrable on the ball.
* `HasSphereMeanValueProperty.le_of_forall_sphere_le`,
  `HasSphereMeanValueProperty.ge_of_forall_sphere_ge`: if `u ≤ M` (resp. `m ≤ u`) on one sphere
  around `x` on which `u` is integrable, then `u x ≤ M` (resp. `m ≤ u x`).
* `HasSphereMeanValueProperty.neg`, `.add`, `.sub`, `.const`, `.zero`, and
  `isHarmonicPDE_const`, `isHarmonicPDE_zero`: linear closure and the constant
  examples.

## Implementation notes

The generic theorem `PDE.Analysis.hasDerivAt_unitSphereAverage` assumes `ContDiff ℝ 1 u` on all
of `ℝ^n` rather than on a domain; a function known only on an open set must first be extended
from a neighbourhood of the relevant closed ball. `sphereAverage` agrees with
`unitSphereAverage` for `r > 0`
(`sphereAverage_eq_unitSphereAverage`), which is how the derivative formula transfers to the
geometric average. `ballAverage` is a total function whose defining branch is `r > 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, Theorem 2 (Mean-value formulas for Laplace's
  equation), (16), and steps 1-2 of its proof, pp. 25-26.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open MeasureTheory
open PDE.Analysis
open scoped BigOperators ENNReal

/-- Radial differentiation formula for the geometric spherical average at every positive radius.

The moving-surface Jacobian has cancelled in `sphereAverage_eq_unitSphereAverage`; consequently
only the radial directional derivative of `u` remains. -/
theorem hasDerivAt_sphereAverage {n : ℕ} [Fact (0 < n)]
    (u : ℝ^n → ℝ) (x : ℝ^n)
    (r : ℝ) (hr : 0 < r) (hu : ContDiff ℝ 1 u) :
    HasDerivAt (sphereAverage n u x)
      ((∫ ω,
          fderiv ℝ u (x + r • (ω : ℝ^n))
            (ω : ℝ^n)
          ∂((volume : Measure (ℝ^n)).toSphere)) /
        unitSphereArea n) r := by
  apply
    (PDE.Analysis.hasDerivAt_unitSphereAverage (n := n) u x r hu).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact sphereAverage_eq_unitSphereAverage u x s hs

/-- Closed formula for the radius derivative of a spherical average of a `C¹` function. -/
theorem deriv_sphereAverage {n : ℕ} [Fact (0 < n)]
    (u : ℝ^n → ℝ) (x : ℝ^n)
    (r : ℝ) (hr : 0 < r) (hu : ContDiff ℝ 1 u) :
    deriv (sphereAverage n u x) r =
      (∫ ω,
          fderiv ℝ u (x + r • (ω : ℝ^n))
            (ω : ℝ^n)
          ∂((volume : Measure (ℝ^n)).toSphere)) /
        unitSphereArea n :=
  (hasDerivAt_sphereAverage (n := n) u x r hr hu).deriv

/-- The negative of a function with the sphere mean-value property has the same property. -/
theorem HasSphereMeanValueProperty.neg {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) :
    HasSphereMeanValueProperty n (-u) U := by
  intro x hx r hr hball
  calc
    (-u) x = -u x := rfl
    _ = -sphereAverage n u x r := by rw [hu x hx r hr hball]
    _ = sphereAverage n (-u) x r := (sphereAverage_neg (n := n) u x hr).symm

/-- The sum of two continuous functions with the sphere mean-value property has the same
property. -/
theorem HasSphereMeanValueProperty.add {n : ℕ}
    {u v : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    (hv : HasSphereMeanValueProperty n v U)
    (hu_cont : ContinuousOn u U) (hv_cont : ContinuousOn v U) :
    HasSphereMeanValueProperty n (fun x ↦ u x + v x) U := by
  classical
  intro x hx r hr hball
  have hparam :
      Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        x + r • (ω : ℝ^n)) := by
    fun_prop
  have hparam_mem (ω : Metric.sphere (0 : ℝ^n) 1) :
      x + r • (ω : ℝ^n) ∈ U := by
    apply hball
    have hω : ‖(ω : ℝ^n)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ω.property
    rw [Metric.mem_closedBall]
    simp [dist_eq_norm, norm_smul, hω, abs_of_pos hr]
  have hu_int :
      Integrable
        (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
          u (x + r • (ω : ℝ^n)))
        ((volume : Measure (ℝ^n)).toSphere) := by
    exact (hu_cont.comp_continuous hparam hparam_mem).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure fun _ _ ↦ Set.mem_univ _)
  have hv_int :
      Integrable
        (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
          v (x + r • (ω : ℝ^n)))
        ((volume : Measure (ℝ^n)).toSphere) := by
    exact (hv_cont.comp_continuous hparam hparam_mem).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure fun _ _ ↦ Set.mem_univ _)
  calc
    u x + v x =
        sphereAverage n u x r + sphereAverage n v x r := by
      rw [hu.apply hx hr hball, hv.apply hx hr hball]
    _ = sphereAverage n (fun y ↦ u y + v y) x r :=
      (sphereAverage_add u v x hr hu_int hv_int).symm

/-- The difference of two continuous functions with the sphere mean-value property has the same
property. -/
theorem HasSphereMeanValueProperty.sub {n : ℕ}
    {u v : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    (hv : HasSphereMeanValueProperty n v U)
    (hu_cont : ContinuousOn u U) (hv_cont : ContinuousOn v U) :
    HasSphereMeanValueProperty n (u - v) U := by
  change HasSphereMeanValueProperty n (fun x ↦ u x - v x) U
  simpa [sub_eq_add_neg] using hu.add hv.neg hu_cont hv_cont.neg

/-- Constant functions have the sphere mean-value property. -/
theorem HasSphereMeanValueProperty.const {n : ℕ} [Fact (0 < n)]
    (c : ℝ) (U : Set (ℝ^n)) :
    HasSphereMeanValueProperty n (fun _ : ℝ^n ↦ c) U := by
  intro x _hx r hr _hball
  simp [sphereAverage_const (n := n) c x hr]

/-- The zero function has the sphere mean-value property. -/
theorem HasSphereMeanValueProperty.zero {n : ℕ} [Fact (0 < n)]
    (U : Set (ℝ^n)) :
    HasSphereMeanValueProperty n (fun _ : ℝ^n ↦ (0 : ℝ)) U :=
  HasSphereMeanValueProperty.const (n := n) 0 U

/-- Constant functions are also harmonic in the pointwise PDE sense. -/
theorem isHarmonicPDE_const {n : ℕ}
    (c : ℝ) (U : Set (ℝ^n)) :
    IsHarmonicPDE n (fun _ : ℝ^n ↦ c) U := by
  constructor
  · fun_prop
  · intro x _hx
    exact PDE.laplacian_const (n := n) c x

/-- The zero function is harmonic in the pointwise PDE sense. -/
theorem isHarmonicPDE_zero {n : ℕ}
    (U : Set (ℝ^n)) :
    IsHarmonicPDE n (fun _ : ℝ^n ↦ (0 : ℝ)) U :=
  isHarmonicPDE_const (n := n) 0 U

/-- The ball average equals the value of a function with the sphere mean-value property. -/
theorem HasSphereMeanValueProperty.eq_ballAverage {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) (x : ℝ^n) (hx : x ∈ U)
    (r : ℝ) (hr : r > 0)
    (hball : Metric.closedBall x r ⊆ U)
    (hu_int : IntegrableOn u (Metric.ball x r) (volume : Measure (ℝ^n))) :
    u x = ballAverage n u x r := by
  classical
  have h_sphereIntegral :
      ∀ ρ ∈ Set.Icc (0 : ℝ) r, sphereIntegral n u x ρ = u x * sphereArea n ρ := by
    intro ρ hρ
    rcases hρ.1.eq_or_lt with rfl | hρpos
    · simp [sphereIntegral, sphereArea, unitSphereArea, MeasureTheory.integral_const,
        MeasureTheory.measureReal_def, mul_comm, mul_left_comm]
    · have hmvp : u x = sphereIntegral n u x ρ / sphereArea n ρ := by
        simpa [sphereAverage, hρpos] using
          hu x hx ρ hρpos ((Metric.closedBall_subset_closedBall hρ.2).trans hball)
      exact ((eq_div_iff (sphereArea_ne_zero (n := n) ρ hρpos)).mp hmvp).symm
  have h_volume_relation : ∫ ρ in Set.Icc 0 r, sphereArea n ρ = ballVolume n r := by
    have hco1 := coarea_formula_ball (n := n) (u := fun _ : ℝ^n ↦ (1 : ℝ)) (x := 0) (r := r)
      (integrableOn_const measure_ball_lt_top.ne (by simp))
    simpa [ballIntegral, ballVolume, sphereIntegral, sphereArea, unitSphereArea,
      MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_assoc,
      mul_comm, mul_left_comm] using hco1.symm
  rw [ballAverage, ite_eq_left hr, coarea_formula_ball (n := n) (u := u) (x := x) (r := r) hu_int,
    setIntegral_congr_fun measurableSet_Icc h_sphereIntegral, integral_const_mul,
    h_volume_relation, mul_div_cancel_right₀ _ (ballVolume_ne_zero r hr)]

/-- A one-point bound from the sphere mean-value property.

If `u` has the sphere mean-value property at `x` and is bounded above by `M` on one surrounding
sphere, then `u x ≤ M`. This is the averaging step used in the weak maximum principle, not the
full maximum principle itself; harmonicity enters only through a separate theorem establishing
the mean-value property. See Evans §2.2.2. -/
theorem HasSphereMeanValueProperty.le_of_forall_sphere_le
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) (x : ℝ^n) (hx : x ∈ U)
    (r : ℝ) (hr : r > 0) (hball : Metric.closedBall x r ⊆ U) {M : ℝ}
    (hu_int :
      Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        u (x + r • (ω : ℝ^n)))
        ((volume : Measure (ℝ^n)).toSphere))
    (hle : ∀ ω : Metric.sphere (0 : ℝ^n) 1,
      u (x + r • (ω : ℝ^n)) ≤ M) :
    u x ≤ M := by
  classical
  calc
    u x = unitSphereAverage n u x r := by
      rw [← sphereAverage_eq_unitSphereAverage u x r hr]
      exact hu.apply hx hr hball
    _ ≤ M := by
      rw [unitSphereAverage]
      apply (div_le_iff₀ (unitSphereArea_pos (n := n))).2
      calc
        (∫ ω : Metric.sphere (0 : ℝ^n) 1,
            u (x + r • (ω : ℝ^n))
              ∂((volume : Measure (ℝ^n)).toSphere)) ≤
            ∫ _ω : Metric.sphere (0 : ℝ^n) 1, M
              ∂((volume : Measure (ℝ^n)).toSphere) := by
          exact MeasureTheory.integral_mono hu_int
            (MeasureTheory.integrable_const M) hle
        _ = M * unitSphereArea n := by
          simp [unitSphereArea, MeasureTheory.measureReal_def]
          ring

/-- A lower bound on one surrounding sphere bounds the value at its center. -/
theorem HasSphereMeanValueProperty.ge_of_forall_sphere_ge
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) (x : ℝ^n) (hx : x ∈ U)
    (r : ℝ) (hr : r > 0) (hball : Metric.closedBall x r ⊆ U) {m : ℝ}
    (hu_int :
      Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        u (x + r • (ω : ℝ^n)))
        ((volume : Measure (ℝ^n)).toSphere))
    (hge : ∀ ω : Metric.sphere (0 : ℝ^n) 1,
      m ≤ u (x + r • (ω : ℝ^n))) :
    m ≤ u x := by
  have hneg_int :
      Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        (-u) (x + r • (ω : ℝ^n)))
        ((volume : Measure (ℝ^n)).toSphere) := by
    simpa using hu_int.neg
  have hneg :
      (-u) x ≤ -m := by
    apply hu.neg.le_of_forall_sphere_le x hx r hr hball hneg_int
    intro ω
    simpa using neg_le_neg (hge ω)
  simpa using neg_le_neg hneg

end LaplacianEquation

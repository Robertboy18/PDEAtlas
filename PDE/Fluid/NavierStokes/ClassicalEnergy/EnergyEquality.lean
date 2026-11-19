/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Statement
public import PDE.Fluid.NavierStokes.ClassicalEnergy.Gradient
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Integration.TimeSlice
import PDE.Analysis.MeasureTheory.Lp.PairingConvergence
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.Fluid.NavierStokes.LocalEnergy.Divergence
import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.CubicInterpolation

/-!
# The energy equality of a classical three-dimensional solution

A classical solution of the unforced Navier–Stokes equations on the open slab `(0,T) × ℝ^3` in the
energy class satisfies, for `0 < s ≤ t < T`, `½ ‖u(t)‖₂² + ν ∫ₛᵗ ‖∇u(τ)‖₂² dτ = ½ ‖u(s)‖₂²`
(`kineticEnergy_add_integral_weakGradientDissipation_eq`).

## How it works

We test the local energy balance with the expanding spatial cutoffs `χ_R`, `R = k + 1`. The cutoff
energy changes by the time integral of its derivative, and on each slice the divergence of the
weighted energy flux integrates to zero. As `R → ∞` the weighted energies and dissipations converge
(`tendsto_integral_mul_cutoff`), while the terms carrying `∇χ_R = O(1/R)` are bounded by `1/R` times
`‖u‖₂ ‖∇u‖₂ + ‖u‖₃³ + ‖p‖₂ ‖u‖₂`. The cubic norm is controlled by the Sobolev inequality,
`‖u‖₃³ ≤ C ‖u‖₂^{3/2} ‖∇u‖₂^{3/2}` (`SobolevSpace.Inequalities.exists_integral_norm_cube_le`), which
is integrable in time because `u ∈ L∞L²` and `∇u ∈ L²L²`; the pressure term is integrable because
`p ∈ L¹L²`.
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory Filter IncompressibleFlow PDE PDE.Common
open SobolevSpace.Approximation
open scoped Topology

set_option linter.missingDocs true

/-- The spatial cutoff `χ_R` viewed as a function on spacetime, constant in time. -/
private def spacetimeCutoff (n : ℕ) (R : ℝ) : ℝ^(n + 1) → ℝ :=
  fun z ↦ cutoff R (spatialPartCLM n z)

/-- On a time slice the spacetime cutoff is the spatial cutoff. -/
private theorem spacetimeCutoff_timeSpaceCons {n : ℕ} (R t : ℝ) (x : ℝ^n) :
    spacetimeCutoff n R (timeSpaceCons t x) = cutoff R x := by
  simp [spacetimeCutoff]

/-- The spacetime cutoff is smooth. -/
private theorem contDiff_spacetimeCutoff (n : ℕ) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeCutoff n R) :=
  (cutoff_contDiff R).comp (spatialPartCLM n).contDiff

/-- The derivative of the spacetime cutoff is the derivative of the spatial cutoff composed with
the spatial projection. -/
private theorem fderiv_spacetimeCutoff (n : ℕ) (R : ℝ) (z : ℝ^(n + 1)) :
    fderiv ℝ (spacetimeCutoff n R) z =
      (fderiv ℝ (cutoff R) (spatialPartCLM n z)).comp (spatialPartCLM n) := by
  have hd : DifferentiableAt ℝ (cutoff (n := n) R) (spatialPartCLM n z) :=
    ((cutoff_contDiff R).differentiable (by simp)) _
  exact (hd.hasFDerivAt.comp z (spatialPartCLM n).hasFDerivAt).fderiv

/-- The spacetime cutoff does not depend on time. -/
private theorem partialDeriv_zero_spacetimeCutoff (n : ℕ) (R : ℝ) (z : ℝ^(n + 1)) :
    (∂[0] (spacetimeCutoff n R)) z = 0 := by
  simp [partialDeriv, fderiv_spacetimeCutoff]

/-- A spatial derivative of the spacetime cutoff is the corresponding derivative of the spatial
cutoff. -/
private theorem partialDeriv_succ_spacetimeCutoff {n : ℕ} (R : ℝ) (j : Fin n) (z : ℝ^(n + 1)) :
    (∂[j.succ] (spacetimeCutoff n R)) z = (∂[j] (cutoff R)) (spatialPartCLM n z) := by
  simp [partialDeriv, fderiv_spacetimeCutoff]

/-- A coordinate derivative of the spatial cutoff vanishes outside the ball of twice its
radius. -/
private theorem partialDeriv_cutoff_eq_zero_of_notMem {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n)
    {x : ℝ^n} (hx : x ∉ Metric.closedBall (0 : ℝ^n) (2 * R)) : (∂[j] (cutoff R)) x = 0 :=
  partialDeriv_eq_zero_of_notMem_tsupport j fun h ↦ hx (tsupport_cutoff_subset_closedBall hR h)

/-- The terms of the weighted energy balance that carry a spatial derivative of the weight `χ`:
`∑ⱼ (|u|²/2 + p) uⱼ ∂ⱼχ - ν ∑ⱼ ∂ⱼ(|u|²/2) ∂ⱼχ`. -/
private def cutoffEnergyError {n : ℕ} (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n)
    (p χ : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) : ℝ :=
  ∑ j : Fin n, (specificKineticEnergy u z + p z) * u z j * (∂[j.succ] χ) z -
    (nse.kinematicViscosity : ℝ) *
      ∑ j : Fin n, (∂[j.succ] (specificKineticEnergy u)) z * (∂[j.succ] χ) z

/-- For a time-independent weight and zero forcing, the time derivative of the weighted kinetic
energy at a classical point is a spatial divergence, minus the weighted dissipation, plus the
terms carrying spatial derivatives of the weight. -/
private theorem partialDeriv_energy_mul_eq_of_forcing_eq_zero {n : ℕ} {nse : Problem n}
    (hforce : nse.forcing = 0) {u : ℝ^(n + 1) → ℝ^n} {p χ : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u z) (hp : ContDiffAt ℝ 1 p z) (hχ : DifferentiableAt ℝ χ z)
    (hχ0 : (∂[0] χ) z = 0) (hdiv : DivergenceFreeAt u z)
    (hmom : MomentumEquationAt nse u p z) :
    (∂[0] (fun y ↦ specificKineticEnergy u y * χ y)) z =
      ∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) z -
        (nse.kinematicViscosity : ℝ) * (‖spatialVelocityGradient n u z‖ ^ 2 * χ z) +
        cutoffEnergyError nse u p χ z := by
  have h := partialDeriv_energy_mul_eq_sum hu hp hχ hdiv hmom
  rw [hχ0, hforce] at h
  simp only [Pi.zero_apply, inner_zero_left, zero_mul, mul_zero, sub_zero, add_zero] at h
  unfold cutoffEnergyError
  linarith

/-- The spacetime cutoff vanishes on a slice outside the ball of twice its radius. -/
private theorem spacetimeCutoff_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) (τ : ℝ) {x : ℝ^n}
    (hx : x ∉ Metric.closedBall (0 : ℝ^n) (2 * R)) :
    spacetimeCutoff n R (timeSpaceCons τ x) = 0 := by
  rw [spacetimeCutoff_timeSpaceCons, cutoff_eq_zero_of_notMem_closedBall hR hx]

/-- The cutoff error vanishes on a slice outside the ball of twice the cutoff radius. -/
private theorem cutoffEnergyError_eq_zero {n : ℕ} (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) {R : ℝ} (hR : 0 < R) (τ : ℝ) {x : ℝ^n}
    (hx : x ∉ Metric.closedBall (0 : ℝ^n) (2 * R)) :
    cutoffEnergyError nse u p (spacetimeCutoff n R) (timeSpaceCons τ x) = 0 := by
  simp [cutoffEnergyError, partialDeriv_succ_spacetimeCutoff,
    partialDeriv_cutoff_eq_zero_of_notMem hR _ hx]

/-- The cutoff error is continuous where the velocity is `C²` and the pressure `C¹`. -/
private theorem continuousAt_cutoffEnergyError {n : ℕ} (nse : Problem n)
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} (R : ℝ) {z : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u z) (hp : ContDiffAt ℝ 1 p z) :
    ContinuousAt (cutoffEnergyError nse u p (spacetimeCutoff n R)) z := by
  have he : ContDiffAt ℝ 2 (specificKineticEnergy u) z := contDiffAt_const.mul (hu.norm_sq ℝ)
  have huj : ∀ j : Fin n, ContinuousAt (fun y ↦ u y j) z := fun j ↦
    ((contDiffAt_piLp 2).mp hu j).continuousAt
  have hpc : ContinuousAt p z := hp.continuousAt
  have hec : ContinuousAt (specificKineticEnergy u) z := he.continuousAt
  have hDe : ∀ j : Fin n, ContinuousAt (∂[j.succ] (specificKineticEnergy u)) z := fun j ↦
    (he.of_le (by norm_num)).continuousAt_partialDeriv j.succ
  have hDχ : ∀ j : Fin n, ContinuousAt (∂[j.succ] (spacetimeCutoff n R)) z := fun j ↦
    (((contDiff_spacetimeCutoff n R).of_le (by simp)).continuous_partialDeriv j.succ).continuousAt
  unfold cutoffEnergyError
  fun_prop

/-- The cutoff dissipation density is continuous on the open slab. -/
private theorem continuousAt_sliceGradient_sq_mul_spacetimeCutoff {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {T : ℝ} (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (R : ℝ) {z : ℝ^(n + 1)} (hz : z ∈ finiteTimeDomain n T) :
    ContinuousAt (fun y ↦ ‖sliceGradient u y‖ ^ 2 * spacetimeCutoff n R y) z :=
  ((continuousAt_sliceGradient hu hz).norm.pow 2).mul
    (contDiff_spacetimeCutoff n R).continuous.continuousAt

/-- On a slice at a time in `(0,T)`, the spatial integral of the time derivative of the cutoff
kinetic energy is minus the viscosity times the cutoff dissipation plus the integral of the
cutoff error; the divergence term integrates to zero. -/
private theorem integral_partialDeriv_energy_cutoff_eq {n : ℕ} {nse : Problem n}
    (hforce : nse.forcing = 0) {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    {R : ℝ} (hR : 0 < R) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ < T) :
    ∫ x, (∂[0] (fun y ↦ specificKineticEnergy u y * spacetimeCutoff n R y))
        (timeSpaceCons τ x) =
      -(nse.kinematicViscosity : ℝ) * (∫ x, ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 *
          spacetimeCutoff n R (timeSpaceCons τ x)) +
        ∫ x, cutoffEnergyError nse u p (spacetimeCutoff n R) (timeSpaceCons τ x) := by
  set χ := spacetimeCutoff n R
  set ν : ℝ := (nse.kinematicViscosity : ℝ)
  have hK : IsCompact (Metric.closedBall (0 : ℝ^n) (2 * R)) := isCompact_closedBall _ _
  have hz : ∀ x, timeSpaceCons τ x ∈ finiteTimeDomain n T :=
    timeSpaceCons_mem_finiteTimeDomain ⟨hτ0, hτT⟩
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := contDiff_spacetimeCutoff n R
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hχd : ∀ z, DifferentiableAt ℝ χ z := fun z ↦ (hχ1.differentiable (by simp)) z
  have hχ0 : ∀ z, (∂[0] χ) z = 0 := partialDeriv_zero_spacetimeCutoff n R
  have hχK : ∀ x, x ∉ Metric.closedBall (0 : ℝ^n) (2 * R) → χ (timeSpaceCons τ x) = 0 :=
    fun x hx ↦ spacetimeCutoff_eq_zero hR τ hx
  have he : ∀ x, ContDiffAt ℝ 2 (specificKineticEnergy u) (timeSpaceCons τ x) := fun x ↦
    contDiffAt_const.mul ((hu _ (hz x)).norm_sq ℝ)
  have hG : ∀ x, ContDiffAt ℝ 1 (fun y ↦ specificKineticEnergy u y * χ y)
      (timeSpaceCons τ x) := fun x ↦ ((he x).of_le (by norm_num)).mul hχ1.contDiffAt
  have hpt : ∀ x, (∂[0] (fun y ↦ specificKineticEnergy u y * χ y)) (timeSpaceCons τ x) =
      ∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) (timeSpaceCons τ x) -
        ν * (‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * χ (timeSpaceCons τ x)) +
        cutoffEnergyError nse u p χ (timeSpaceCons τ x) := by
    intro x
    rw [sliceGradient_eq_spatialVelocityGradient (by simpa using hτ0)
      ((hu _ (hz x)).differentiableAt (by norm_num))]
    exact partialDeriv_energy_mul_eq_of_forcing_eq_zero hforce (hu _ (hz x)) (hp _ (hz x))
      (hχd _) (hχ0 _) (hdiv _ (hz x)) (hmom _ (hz x))
  have hflux : ∀ (j : Fin n) x, ContDiffAt ℝ 1 (energyWeightFlux nse u p χ j)
      (timeSpaceCons τ x) := by
    intro j x
    have huj : ContDiffAt ℝ 1 (fun y ↦ u y j) (timeSpaceCons τ x) :=
      ((contDiffAt_piLp 2).mp (hu _ (hz x)) j).of_le (by norm_num)
    have hDe : ContDiffAt ℝ 1 (∂[j.succ] (specificKineticEnergy u)) (timeSpaceCons τ x) :=
      (he x).partialDeriv j.succ (by norm_num)
    exact ((contDiffAt_const.mul hDe).sub ((((he x).of_le (by norm_num)).add
      (hp _ (hz x))).mul huj)).mul hχ1.contDiffAt
  have hfluxK : ∀ j : Fin n,
      HasCompactSupport fun x ↦ energyWeightFlux nse u p χ j (timeSpaceCons τ x) :=
    fun j ↦ HasCompactSupport.intro hK fun x hx ↦ by
      simp only [energyWeightFlux, hχK x hx, mul_zero]
  have hzero := PDE.Analysis.integral_timeSlice_sum_partialDeriv_eq_zero τ hflux hfluxK
  have h1 : Integrable fun x ↦
      (∂[0] (fun y ↦ specificKineticEnergy u y * χ y)) (timeSpaceCons τ x) := by
    refine PDE.Analysis.integrable_timeSlice_of_continuousAt hK τ
      (fun x ↦ (hG x).continuousAt_partialDeriv 0) fun x hx ↦ ?_
    rw [partialDeriv_mul ((he x).differentiableAt (by norm_num)) (hχd _), hχ0, hχK x hx]
    ring
  have h2 : Integrable fun x ↦
      ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * χ (timeSpaceCons τ x) :=
    PDE.Analysis.integrable_timeSlice_of_continuousAt (F := fun z ↦
      ‖sliceGradient u z‖ ^ 2 * χ z) hK τ
      (fun x ↦ continuousAt_sliceGradient_sq_mul_spacetimeCutoff hu R (hz x))
      fun x hx ↦ by simp [hχK x hx]
  have h3 : Integrable fun x ↦ cutoffEnergyError nse u p χ (timeSpaceCons τ x) :=
    PDE.Analysis.integrable_timeSlice_of_continuousAt hK τ
      (fun x ↦ continuousAt_cutoffEnergyError nse R (hu _ (hz x)) (hp _ (hz x)))
      fun x hx ↦ cutoffEnergyError_eq_zero nse u p hR τ hx
  have hdivint : Integrable fun x ↦
      ∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) (timeSpaceCons τ x) := by
    refine ((h1.add (h2.const_mul ν)).sub h3).congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hpt x]
    ring
  have hAB : Integrable fun x ↦
      ∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) (timeSpaceCons τ x) -
        ν * (‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * χ (timeSpaceCons τ x)) :=
    hdivint.sub (h2.const_mul ν)
  calc ∫ x, (∂[0] (fun y ↦ specificKineticEnergy u y * χ y)) (timeSpaceCons τ x)
      = ∫ x, (∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) (timeSpaceCons τ x) -
          ν * (‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * χ (timeSpaceCons τ x)) +
          cutoffEnergyError nse u p χ (timeSpaceCons τ x)) := by
        simp only [hpt]
    _ = _ := by
        rw [integral_add hAB h3, integral_sub hdivint (h2.const_mul ν), hzero,
          integral_const_mul]
        ring

/-- For a fixed radius, the cutoff kinetic energy at time `t` minus that at time `s` is minus the
viscosity times the time integral of the cutoff dissipation, plus the time integral of the
cutoff error. -/
private theorem cutoffEnergy_sub_eq {n : ℕ} {nse : Problem n}
    (hforce : nse.forcing = 0) {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    {R : ℝ} (hR : 0 < R) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    (∫ x, kineticEnergyDensity u t x * cutoff R x) -
        ∫ x, kineticEnergyDensity u s x * cutoff R x =
      -(nse.kinematicViscosity : ℝ) * (∫ τ in s..t, ∫ x,
          ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * spacetimeCutoff n R (timeSpaceCons τ x)) +
        ∫ τ in s..t, ∫ x, cutoffEnergyError nse u p (spacetimeCutoff n R) (timeSpaceCons τ x) := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ^n) (2 * R)) := isCompact_closedBall _ _
  have hslab : ∀ τ ∈ Set.Icc s t, ∀ x, timeSpaceCons τ x ∈ finiteTimeDomain n T :=
    fun τ hτ ↦ timeSpaceCons_mem_finiteTimeDomain ⟨hs.trans_le hτ.1, hτ.2.trans_lt ht⟩
  have hG : ∀ τ ∈ Set.Icc s t, ∀ x, ContDiffAt ℝ 1
      (fun y ↦ specificKineticEnergy u y * spacetimeCutoff n R y) (timeSpaceCons τ x) :=
    fun τ hτ x ↦ ((contDiffAt_const.mul ((hu _ (hslab τ hτ x)).norm_sq ℝ)).of_le
      (by norm_num)).mul ((contDiff_spacetimeCutoff n R).of_le (by simp)).contDiffAt
  have hFTC := PDE.Analysis.integral_timeSlice_sub_eq_intervalIntegral hK
    (fun τ x hx ↦ by simp only [spacetimeCutoff_eq_zero hR τ hx, mul_zero]) hst hG
  simp only [spacetimeCutoff_timeSpaceCons] at hFTC
  have hD : IntervalIntegrable (fun τ ↦ ∫ x,
      ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * spacetimeCutoff n R (timeSpaceCons τ x))
      volume s t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hst]
    exact PDE.Analysis.continuousOn_integral_timeSlice (F := fun z ↦
      ‖sliceGradient u z‖ ^ 2 * spacetimeCutoff n R z) hK
      (fun τ hτ x ↦ continuousAt_sliceGradient_sq_mul_spacetimeCutoff hu R (hslab τ hτ x))
      fun τ x hx ↦ by simp only [spacetimeCutoff_eq_zero hR τ hx, mul_zero]
  have hE : IntervalIntegrable (fun τ ↦ ∫ x,
      cutoffEnergyError nse u p (spacetimeCutoff n R) (timeSpaceCons τ x)) volume s t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hst]
    exact PDE.Analysis.continuousOn_integral_timeSlice hK
      (fun τ hτ x ↦ continuousAt_cutoffEnergyError nse R (hu _ (hslab τ hτ x))
        (hp _ (hslab τ hτ x)))
      fun τ x hx ↦ cutoffEnergyError_eq_zero nse u p hR τ hx
  calc (∫ x, kineticEnergyDensity u t x * cutoff R x) -
        ∫ x, kineticEnergyDensity u s x * cutoff R x
      = ∫ τ in s..t, ∫ x, (∂[0] (fun y ↦ specificKineticEnergy u y * spacetimeCutoff n R y))
          (timeSpaceCons τ x) := hFTC
    _ = ∫ τ in s..t, (-(nse.kinematicViscosity : ℝ) * (∫ x,
          ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * spacetimeCutoff n R (timeSpaceCons τ x)) +
          ∫ x, cutoffEnergyError nse u p (spacetimeCutoff n R) (timeSpaceCons τ x)) := by
        refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
        rw [Set.uIcc_of_le hst] at hτ
        exact integral_partialDeriv_energy_cutoff_eq hforce hu hp hdiv hmom hR
          (hs.trans_le hτ.1) (hτ.2.trans_lt ht)
    _ = _ := by
        rw [intervalIntegral.integral_add (hD.const_mul _) hE,
          intervalIntegral.integral_const_mul]

/-- The time integrals of the cutoff dissipation converge to the time integral of the
dissipation as the cutoff radius grows. -/
private theorem tendsto_intervalIntegral_dissipation_cutoff {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}
    {p : ℝ^(n + 1) → ℝ} {T : ℝ} (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hclass : ClassicalEnergyClass u p T) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    Tendsto (fun k : ℕ ↦ ∫ τ in s..t, ∫ x, ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 *
        spacetimeCutoff n ((k : ℝ) + 1) (timeSpaceCons τ x)) atTop
      (𝓝 (∫ τ in s..t, weakGradientDissipation (sliceGradient u) τ)) := by
  have hslab : ∀ τ ∈ Set.Icc s t, ∀ x, timeSpaceCons τ x ∈ finiteTimeDomain n T :=
    fun τ hτ ↦ timeSpaceCons_mem_finiteTimeDomain ⟨hs.trans_le hτ.1, hτ.2.trans_lt ht⟩
  have hIoc : ∀ τ ∈ Set.Ioc s t, τ ∈ Set.Ioc 0 T :=
    fun τ hτ ↦ ⟨hs.trans hτ.1, hτ.2.trans ht.le⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun τ ↦ n * (eLpNorm (fderiv ℝ (velocitySlice u τ)) 2 volume).toReal ^ 2)
    (Eventually.of_forall fun k ↦ ?_) (Eventually.of_forall fun k ↦ ?_) ?_ ?_
  · have hR : 0 < (k : ℝ) + 1 := by positivity
    rw [Set.uIoc_of_le hst]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (PDE.Analysis.continuousOn_integral_timeSlice (F := fun z ↦
      ‖sliceGradient u z‖ ^ 2 * spacetimeCutoff n ((k : ℝ) + 1) z)
      (isCompact_closedBall (0 : ℝ^n) (2 * ((k : ℝ) + 1)))
      (fun τ hτ x ↦ continuousAt_sliceGradient_sq_mul_spacetimeCutoff hu _ (hslab τ hτ x))
      fun τ x hx ↦ by simp only [spacetimeCutoff_eq_zero hR τ hx, mul_zero]).mono
        Set.Ioc_subset_Icc_self
  · refine Eventually.of_forall fun τ hτ ↦ ?_
    rw [Set.uIoc_of_le hst] at hτ
    have hτ' := hIoc τ hτ
    have hC := hclass.slice_contDiff τ hτ'
    have hD := hclass.gradient_memLp τ hτ'
    calc ‖∫ x, ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 *
          spacetimeCutoff n ((k : ℝ) + 1) (timeSpaceCons τ x)‖
        ≤ ∫ x, n * ‖fderiv ℝ (velocitySlice u τ) x‖ ^ 2 := by
          refine norm_integral_le_of_norm_le ((hD.integrable_norm_pow two_ne_zero).const_mul _)
            (Eventually.of_forall fun x ↦ ?_)
          simp only [spacetimeCutoff_timeSpaceCons]
          rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (cutoff_nonneg _ x))]
          calc ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 * cutoff ((k : ℝ) + 1) x
              ≤ ‖sliceGradient u (timeSpaceCons τ x)‖ ^ 2 :=
                mul_le_of_le_one_right (by positivity) (cutoff_le_one _ x)
            _ ≤ n * ‖fderiv ℝ (velocitySlice u τ) x‖ ^ 2 :=
                norm_sliceGradient_sq_le hτ'.1 (hC.differentiable (by norm_num) x)
      _ = n * (eLpNorm (fderiv ℝ (velocitySlice u τ)) 2 volume).toReal ^ 2 := by
          rw [integral_const_mul, PDE.Analysis.integral_norm_sq_eq_eLpNorm_toReal_sq hD]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
      ((hclass.gradient_sq_integrableOn.mono_set (Set.Ioc_subset_Ioc hs.le ht.le)).const_mul _)
  · refine Eventually.of_forall fun τ hτ ↦ ?_
    rw [Set.uIoc_of_le hst] at hτ
    have hτ' := hIoc τ hτ
    simp only [spacetimeCutoff_timeSpaceCons, weakGradientDissipation,
      weakGradientDissipationDensity, spatialGradientSlice]
    exact tendsto_integral_mul_cutoff ((memLp_spatialGradientSlice_sliceGradient hτ'.1
      (hclass.slice_contDiff τ hτ') (hclass.gradient_memLp τ hτ')).integrable_norm_pow
        two_ne_zero)

/-- On a slice, the cutoff error is bounded by `n C/R` times
`ν |u| |Du| + |u|³/2 + |p| |u|`, where `C/R` bounds the derivative of the cutoff and `Du` is the
derivative of the velocity slice. -/
private theorem norm_cutoffEnergyError_le {n : ℕ} (nse : Problem n) {u : ℝ^(n + 1) → ℝ^n}
    (p : ℝ^(n + 1) → ℝ) {R C : ℝ} (hC : ∀ x : ℝ^n, ‖fderiv ℝ (cutoff R) x‖ ≤ C / R)
    {τ : ℝ} {x : ℝ^n} (hu : DifferentiableAt ℝ u (timeSpaceCons τ x)) :
    ‖cutoffEnergyError nse u p (spacetimeCutoff n R) (timeSpaceCons τ x)‖ ≤
      n * (C / R) * ((nse.kinematicViscosity : ℝ) * (‖u (timeSpaceCons τ x)‖ *
        ‖fderiv ℝ (velocitySlice u τ) x‖) + 1 / 2 * ‖u (timeSpaceCons τ x)‖ ^ 3 +
        ‖p (timeSpaceCons τ x)‖ * ‖u (timeSpaceCons τ x)‖) := by
  set z := timeSpaceCons τ x with hz
  set ν : ℝ := (nse.kinematicViscosity : ℝ)
  set D := ‖fderiv ℝ (velocitySlice u τ) x‖
  have hν : 0 < ν := nse.kinematicViscosity.2
  have hCR : 0 ≤ C / R := (norm_nonneg _).trans (hC x)
  have hχ : ∀ j : Fin n, ‖(∂[j.succ] (spacetimeCutoff n R)) z‖ ≤ C / R := fun j ↦ by
    rw [hz, partialDeriv_succ_spacetimeCutoff, spatialPartCLM_timeSpaceCons]
    exact (norm_partialDeriv_le_norm_fderiv j _ x).trans (hC x)
  have he : ∀ j : Fin n, ‖(∂[j.succ] (specificKineticEnergy u)) z‖ ≤ ‖u z‖ * D := fun j ↦ by
    rw [partialDeriv_specificKineticEnergy_inner hu j.succ, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [hz, ← partialDeriv_timeSpaceCons_spatial j u τ x hu]
    exact norm_partialDeriv_le_norm_fderiv j _ x
  have hep : ‖specificKineticEnergy u z + p z‖ ≤ 1 / 2 * ‖u z‖ ^ 2 + ‖p z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Real.norm_of_nonneg (by unfold specificKineticEnergy; positivity)]
    rfl
  have hA : ∀ j : Fin n,
      ‖(specificKineticEnergy u z + p z) * u z j * (∂[j.succ] (spacetimeCutoff n R)) z‖ ≤
        (1 / 2 * ‖u z‖ ^ 2 + ‖p z‖) * ‖u z‖ * (C / R) := fun j ↦ by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hep (PiLp.norm_apply_le (u z) j) (norm_nonneg _)
      (by positivity)) (hχ j) (norm_nonneg _) (by positivity)
  have hB : ∀ j : Fin n,
      ‖(∂[j.succ] (specificKineticEnergy u)) z * (∂[j.succ] (spacetimeCutoff n R)) z‖ ≤
        ‖u z‖ * D * (C / R) := fun j ↦ by
    rw [norm_mul]
    exact mul_le_mul (he j) (hχ j) (norm_nonneg _) (by positivity)
  unfold cutoffEnergyError
  calc ‖∑ j : Fin n, (specificKineticEnergy u z + p z) * u z j *
          (∂[j.succ] (spacetimeCutoff n R)) z -
        ν * ∑ j : Fin n, (∂[j.succ] (specificKineticEnergy u)) z *
          (∂[j.succ] (spacetimeCutoff n R)) z‖
      ≤ ∑ j : Fin n, ‖(specificKineticEnergy u z + p z) * u z j *
          (∂[j.succ] (spacetimeCutoff n R)) z‖ +
        ν * ∑ j : Fin n, ‖(∂[j.succ] (specificKineticEnergy u)) z *
          (∂[j.succ] (spacetimeCutoff n R)) z‖ := by
        refine (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _) ?_)
        rw [norm_mul, Real.norm_of_nonneg hν.le]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hν.le
    _ ≤ ∑ _j : Fin n, (1 / 2 * ‖u z‖ ^ 2 + ‖p z‖) * ‖u z‖ * (C / R) +
        ν * ∑ _j : Fin n, ‖u z‖ * D * (C / R) := by
        gcongr with j _ j _
        · exact hA j
        · exact hB j
    _ = n * (C / R) * (ν * (‖u z‖ * D) + 1 / 2 * ‖u z‖ ^ 3 + ‖p z‖ * ‖u z‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- For `0 ≤ a ≤ M`, `0 ≤ b` and `0 ≤ q`, the quantity `ν a b + C₃ a^{3/2} b^{3/2} / 2 + q a` is
at most `(ν M + C₃ M^{3/2} / 2 + M) (1 + b² + q)`. -/
private theorem cutoffError_coefficient_le {ν C₃ M a b q : ℝ} (hν : 0 ≤ ν) (hC₃ : 0 ≤ C₃)
    (ha : 0 ≤ a) (haM : a ≤ M) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    ν * (a * b) + 1 / 2 * (C₃ * a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ)) + q * a ≤
      (ν * M + 1 / 2 * (C₃ * M ^ (3 / 2 : ℝ)) + M) * (1 + b ^ 2 + q) := by
  have hM : 0 ≤ M := ha.trans haM
  have hb1 : b ≤ 1 + b ^ 2 + q := by nlinarith [sq_nonneg (b - 1)]
  have hb32 : b ^ (3 / 2 : ℝ) ≤ 1 + b ^ 2 + q := by
    rcases le_total b 1 with h | h
    · have := Real.rpow_le_one hb h (by norm_num : (0 : ℝ) ≤ 3 / 2)
      nlinarith [sq_nonneg b]
    · have h2 : b ^ (3 / 2 : ℝ) ≤ b ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (by norm_num)
      rw [Real.rpow_two] at h2
      linarith
  have ha32 : a ^ (3 / 2 : ℝ) ≤ M ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ha haM (by norm_num)
  have h1 : a * b ≤ M * (1 + b ^ 2 + q) := mul_le_mul haM hb1 hb hM
  have h2 : a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) ≤ M ^ (3 / 2 : ℝ) * (1 + b ^ 2 + q) :=
    mul_le_mul ha32 hb32 (by positivity) (by positivity)
  have h3 : q * a ≤ M * (1 + b ^ 2 + q) := by nlinarith
  have h1' := mul_le_mul_of_nonneg_left h1 hν
  have h2' := mul_le_mul_of_nonneg_left h2 hC₃
  calc ν * (a * b) + 1 / 2 * (C₃ * a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ)) + q * a
      = ν * (a * b) + 1 / 2 * (C₃ * (a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ))) + q * a := by ring
    _ ≤ ν * (M * (1 + b ^ 2 + q)) + 1 / 2 * (C₃ * (M ^ (3 / 2 : ℝ) * (1 + b ^ 2 + q))) +
        M * (1 + b ^ 2 + q) := by gcongr
    _ = _ := by ring

/-- On a slice at a time in `(0,T)`, the integral of the cutoff error is bounded by `3 C/R` times
`ν ‖u‖₂ ‖Du‖₂ + C₃ ‖u‖₂^{3/2} ‖Du‖₂^{3/2} / 2 + ‖p‖₂ ‖u‖₂`, where `C₃` is a constant of the cubic
Sobolev bound. -/
private theorem norm_integral_cutoffEnergyError_le {nse : Problem 3} {u : ℝ^(3 + 1) → ℝ^3}
    {p : ℝ^(3 + 1) → ℝ} {T : ℝ} (hu : ∀ z ∈ finiteTimeDomain 3 T, ContDiffAt ℝ 2 u z)
    (hclass : ClassicalEnergyClass u p T) {C₃ : ℝ}
    (hC₃ : ∀ f : ℝ^3 → ℝ^3, ContDiff ℝ 1 f → MemLp f 2 volume →
      MemLp (fderiv ℝ f) 2 volume → Integrable (fun x ↦ ‖f x‖ ^ 3) ∧
        ∫ x, ‖f x‖ ^ 3 ≤ C₃ * (eLpNorm f 2 volume).toReal ^ (3 / 2 : ℝ) *
          (eLpNorm (fderiv ℝ f) 2 volume).toReal ^ (3 / 2 : ℝ))
    {R C : ℝ} (hC : ∀ x : ℝ^3, ‖fderiv ℝ (cutoff R) x‖ ≤ C / R) {τ : ℝ} (hτ0 : 0 < τ)
    (hτT : τ < T) :
    ‖∫ x, cutoffEnergyError nse u p (spacetimeCutoff 3 R) (timeSpaceCons τ x)‖ ≤
      3 * (C / R) * ((nse.kinematicViscosity : ℝ) *
        ((eLpNorm (velocitySlice u τ) 2 volume).toReal *
          (eLpNorm (fderiv ℝ (velocitySlice u τ)) 2 volume).toReal) +
        1 / 2 * (C₃ * (eLpNorm (velocitySlice u τ) 2 volume).toReal ^ (3 / 2 : ℝ) *
          (eLpNorm (fderiv ℝ (velocitySlice u τ)) 2 volume).toReal ^ (3 / 2 : ℝ)) +
        (eLpNorm (fun x ↦ p (timeSpaceCons τ x)) 2 volume).toReal *
          (eLpNorm (velocitySlice u τ) 2 volume).toReal) := by
  have hτ : τ ∈ Set.Ioc 0 T := ⟨hτ0, hτT.le⟩
  have hU := hclass.velocity_memLp τ hτ
  have hDU := hclass.gradient_memLp τ hτ
  have hP := hclass.pressure_memLp τ ⟨hτ0.le, hτT.le⟩
  set ν : ℝ := (nse.kinematicViscosity : ℝ)
  have hν : 0 < ν := nse.kinematicViscosity.2
  have hCR : 0 ≤ C / R := (norm_nonneg _).trans (hC 0)
  obtain ⟨i2, hcube⟩ := hC₃ _ (hclass.slice_contDiff τ hτ) hU hDU
  have i1 : Integrable fun x ↦ ‖velocitySlice u τ x‖ * ‖fderiv ℝ (velocitySlice u τ) x‖ :=
    hU.norm.integrable_mul hDU.norm
  have i3 : Integrable fun x ↦ ‖p (timeSpaceCons τ x)‖ * ‖velocitySlice u τ x‖ :=
    hP.norm.integrable_mul hU.norm
  have i12 : Integrable fun x ↦
      ν * (‖velocitySlice u τ x‖ * ‖fderiv ℝ (velocitySlice u τ) x‖) +
        1 / 2 * ‖velocitySlice u τ x‖ ^ 3 :=
    (i1.const_mul ν).add (i2.const_mul _)
  calc ‖∫ x, cutoffEnergyError nse u p (spacetimeCutoff 3 R) (timeSpaceCons τ x)‖
      ≤ ∫ x, 3 * (C / R) * (ν * (‖velocitySlice u τ x‖ * ‖fderiv ℝ (velocitySlice u τ) x‖) +
          1 / 2 * ‖velocitySlice u τ x‖ ^ 3 +
          ‖p (timeSpaceCons τ x)‖ * ‖velocitySlice u τ x‖) := by
        refine norm_integral_le_of_norm_le ((i12.add i3).const_mul _)
          (Eventually.of_forall fun x ↦ ?_)
        have h := norm_cutoffEnergyError_le nse p hC (τ := τ) (x := x)
          ((hu _ (timeSpaceCons_mem_finiteTimeDomain ⟨hτ0, hτT⟩ x)).differentiableAt
            (by norm_num))
        exact_mod_cast h
    _ = 3 * (C / R) * (ν * (∫ x, ‖velocitySlice u τ x‖ * ‖fderiv ℝ (velocitySlice u τ) x‖) +
          1 / 2 * (∫ x, ‖velocitySlice u τ x‖ ^ 3) +
          ∫ x, ‖p (timeSpaceCons τ x)‖ * ‖velocitySlice u τ x‖) := by
        rw [integral_const_mul, integral_add i12 i3,
          integral_add (i1.const_mul ν) (i2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        gcongr
        · exact PDE.Analysis.integral_norm_mul_norm_le_eLpNorm_mul hU hDU
        · exact PDE.Analysis.integral_norm_mul_norm_le_eLpNorm_mul hP hU

/-- The time integrals of the cutoff error tend to zero as the cutoff radius grows. -/
private theorem tendsto_intervalIntegral_cutoffEnergyError {nse : Problem 3}
    {u : ℝ^(3 + 1) → ℝ^3} {p : ℝ^(3 + 1) → ℝ} {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain 3 T, ContDiffAt ℝ 2 u z)
    (hclass : ClassicalEnergyClass u p T) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    Tendsto (fun k : ℕ ↦ ∫ τ in s..t, ∫ x,
        cutoffEnergyError nse u p (spacetimeCutoff 3 ((k : ℝ) + 1)) (timeSpaceCons τ x))
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fderiv_cutoff_le (n := 3)
  obtain ⟨C₃, hC₃0, hC₃⟩ := SobolevSpace.Inequalities.exists_integral_norm_cube_le (H := ℝ^3)
  obtain ⟨B, hB⟩ := hclass.velocity_bounded
  set ν : ℝ := (nse.kinematicViscosity : ℝ)
  have hν : 0 < ν := nse.kinematicViscosity.2
  set M := max B 0
  set K := 3 * C * (ν * M + 1 / 2 * (C₃ * M ^ (3 / 2 : ℝ)) + M)
  set H : ℝ → ℝ := fun τ ↦ 1 + (eLpNorm (fderiv ℝ (velocitySlice u τ)) 2 volume).toReal ^ 2 +
    (eLpNorm (fun x ↦ p (timeSpaceCons τ x)) 2 volume).toReal
  have hIoc : Set.Ioc s t ⊆ Set.Ioc 0 T := Set.Ioc_subset_Ioc hs.le ht.le
  have hH : IntervalIntegrable H volume s t := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 ?_
    exact ((integrableOn_const (by simp)).add
      (hclass.gradient_sq_integrableOn.mono_set hIoc)).add
      (hclass.pressure_integrableOn.mono_set hIoc)
  have hbound : ∀ k : ℕ, ‖∫ τ in s..t, ∫ x,
      cutoffEnergyError nse u p (spacetimeCutoff 3 ((k : ℝ) + 1)) (timeSpaceCons τ x)‖ ≤
        1 / ((k : ℝ) + 1) * (K * ∫ τ in s..t, H τ) := by
    intro k
    have hR : 0 < (k : ℝ) + 1 := by positivity
    calc ‖∫ τ in s..t, ∫ x,
          cutoffEnergyError nse u p (spacetimeCutoff 3 ((k : ℝ) + 1)) (timeSpaceCons τ x)‖
        ≤ ∫ τ in s..t, 1 / ((k : ℝ) + 1) * (K * H τ) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hst
            (Eventually.of_forall fun τ hτ ↦ ?_) ((hH.const_mul K).const_mul _)
          have hτ' := hIoc hτ
          have hτT : τ < T := hτ.2.trans_lt ht
          have ha0 := ENNReal.toReal_nonneg (a := eLpNorm (velocitySlice u τ) 2 volume)
          have haM : (eLpNorm (velocitySlice u τ) 2 volume).toReal ≤ M :=
            ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
              ((hB τ hτ').trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
          refine (norm_integral_cutoffEnergyError_le hu hclass hC₃ (hC _ hR) hτ'.1
            hτT).trans ?_
          have he := cutoffError_coefficient_le hν.le hC₃0 ha0 haM
            (ENNReal.toReal_nonneg (a := eLpNorm (fderiv ℝ (velocitySlice u τ)) 2 volume))
            (ENNReal.toReal_nonneg (a := eLpNorm (fun x ↦ p (timeSpaceCons τ x)) 2 volume))
          calc _ ≤ 3 * (C / ((k : ℝ) + 1)) *
                ((ν * M + 1 / 2 * (C₃ * M ^ (3 / 2 : ℝ)) + M) * H τ) := by
                gcongr
            _ = 1 / ((k : ℝ) + 1) * (K * H τ) := by
                simp only [K]
                ring
      _ = 1 / ((k : ℝ) + 1) * (K * ∫ τ in s..t, H τ) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  refine squeeze_zero_norm hbound ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
    (K * ∫ τ in s..t, H τ)

/-- The energy equality on `[s,t] ⊂ (0,T)` for a classical solution in the energy class, with the
slice gradient as dissipation. -/
theorem kineticEnergy_add_integral_weakGradientDissipation_eq {nse : Problem 3}
    (hforce : nse.forcing = 0) {u : ℝ^(3 + 1) → ℝ^3} {p : ℝ^(3 + 1) → ℝ} {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain 3 T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain 3 T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain 3 T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain 3 T, MomentumEquationAt nse u p z)
    (hclass : ClassicalEnergyClass u p T) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    kineticEnergy u t +
        nse.kinematicViscosity * ∫ τ in s..t, weakGradientDissipation (sliceGradient u) τ =
      kineticEnergy u s := by
  have hE (k : ℕ) := cutoffEnergy_sub_eq hforce hu hp hdiv hmom
    (by positivity : (0 : ℝ) < (k : ℝ) + 1) hs hst ht
  have hlimL : Tendsto (fun k : ℕ ↦
      (∫ x, kineticEnergyDensity u t x * cutoff ((k : ℝ) + 1) x) -
        ∫ x, kineticEnergyDensity u s x * cutoff ((k : ℝ) + 1) x)
      atTop (𝓝 (kineticEnergy u t - kineticEnergy u s)) :=
    (tendsto_integral_mul_cutoff (integrable_kineticEnergyDensity_of_memLp
      (hclass.velocity_memLp t ⟨hs.trans_le hst, ht.le⟩))).sub
    (tendsto_integral_mul_cutoff (integrable_kineticEnergyDensity_of_memLp
      (hclass.velocity_memLp s ⟨hs, (hst.trans_lt ht).le⟩)))
  have hlimR := ((tendsto_intervalIntegral_dissipation_cutoff hu hclass hs hst ht).const_mul
    (-(nse.kinematicViscosity : ℝ))).add
    (tendsto_intervalIntegral_cutoffEnergyError (nse := nse) hu hclass hs hst ht)
  have h := tendsto_nhds_unique (hlimL.congr hE) hlimR
  linarith

end NavierStokes

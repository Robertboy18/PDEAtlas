/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import PDE.Hyperbolic.Classical.EnergyIdentity
public import Mathlib.Analysis.Normed.Module.Normalize
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.Models.Wave.Equation

/-!
# Higher-dimensional finite propagation for the classical wave equation

We formalize the shrinking-ball energy argument in the proof of Evans, §2.4.3, Theorem 6. For a
spacetime field `u`, the energy in the backward cone with vertex time `T` is

`E(t) = ∫_{B(c,T-t)} (|u_t|² + |D_x u|²) / 2`.

The pointwise wave equation gives the local conservation law

`∂ₜ e = div_x (u_t D_x u)`.

On the lateral boundary of the cone, Cauchy-Schwarz gives

`u_t D_x u · ν - e ≤ 0`.

The `_of_transport` theorems separate the shrinking-ball energy
argument from the moving-domain calculus: they take the exact Reynolds/Gauss
identity as a hypothesis and derive monotonicity and finite propagation from
the local energy law and the boundary-flux estimate. The companion module
`PDE.Hyperbolic.Classical.MovingBallTransport` proves that transport identity
and derives the corresponding results from classical regularity, the wave equation,
and the stated initial-data hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3, Theorem 6 and its proof, equations (46)-(47).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (coordinateLine)

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis Set
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- Energy flux through the unit outward normal based at `c`, minus the
energy swept out by the shrinking boundary. -/
noncomputable def classicalWaveConeBoundaryFlux (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (t : ℝ)
    (y : ℝ^n) : ℝ :=
  let p := PDE.Common.timeSpaceCons (n := n) t y
  (∂[0] u) p * inner ℝ (classicalWaveSpatialGradient (n := n) u p)
      (NormedSpace.normalize (y - c)) -
    classicalWaveEnergyDensity (n := n) u p

/-- The lateral energy flux is nonpositive at every point of a positive-radius
sphere. This is the inequality (47) in the proof of Evans, §2.4.3, Theorem 6. -/
theorem classicalWaveConeBoundaryFlux_nonpos (u : ℝ^(n + 1) → ℝ) (c y : ℝ^n) {r t : ℝ}
    (hr : 0 < r) (hy : y ∈ Metric.sphere c r) :
    classicalWaveConeBoundaryFlux (n := n) u c t y ≤ 0 := by
  set a := (∂[0] u) (PDE.Common.timeSpaceCons (n := n) t y)
  set g := classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t y)
  have hyne : y - c ≠ 0 := sub_ne_zero.mpr (Metric.ne_of_mem_sphere hy hr.ne')
  have hinner := (abs_real_inner_le_norm g (NormedSpace.normalize (y - c))).trans_eq
    (by rw [NormedSpace.norm_normalize hyne, mul_one])
  have hflux := (le_abs_self (a * inner ℝ g (NormedSpace.normalize (y - c)))).trans_eq
    (abs_mul _ _) |>.trans (mul_le_mul_of_nonneg_left hinner (abs_nonneg a))
  unfold classicalWaveConeBoundaryFlux classicalWaveEnergyDensity
  nlinarith [sq_nonneg (|a| - ‖g‖), sq_abs a]

private theorem integrableOn_classicalWaveEnergyDensity_slice_ball {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ^n) (t r : ℝ) :
    IntegrableOn (fun y ↦ classicalWaveEnergyDensity (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t y)) (Metric.ball c r) (volume : Measure (ℝ^n)) :=
  (((contDiff_classicalWaveEnergyDensity (n := n) hu).continuous.comp
    (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous).continuousOn
      |>.integrableOn_compact (isCompact_closedBall c r)).mono_set Metric.ball_subset_closedBall

/-- Energy on the shrinking spatial ball `B(c,T-t)`. -/
noncomputable def backwardConeEnergy (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (T t : ℝ) : ℝ :=
  ballIntegral n
    (fun y ↦ classicalWaveEnergyDensity (n := n) u (PDE.Common.timeSpaceCons (n := n) t y))
    c (T - t)

/-- The complete lateral-boundary contribution to the shrinking-cone energy
is nonpositive in every spatial dimension. -/
theorem sphereIntegral_classicalWaveConeBoundaryFlux_nonpos (u : ℝ^(n + 1) → ℝ) (c : ℝ^n)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    sphereIntegral n (classicalWaveConeBoundaryFlux (n := n) u c t) c r ≤ 0 :=
  sphereIntegral_nonpos fun y hy ↦
    classicalWaveConeBoundaryFlux_nonpos u c y hr (by simpa [abs_of_pos hr] using hy)

/-- The shrinking-cone energy is antitone once its derivative is the lateral
boundary flux. -/
theorem backwardConeEnergy_antitone (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) {a T : ℝ}
    (hderiv : ∀ t ∈ Set.Ico a T, HasDerivAt (backwardConeEnergy (n := n) u c T)
      (sphereIntegral n (classicalWaveConeBoundaryFlux (n := n) u c t) c (T - t)) t) :
    AntitoneOn (backwardConeEnergy (n := n) u c T) (Set.Ico a T) :=
  antitoneOn_of_deriv_nonpos (convex_Ico a T)
    (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    fun t ht ↦ by
      rw [(hderiv t (interior_subset ht)).deriv]
      exact sphereIntegral_classicalWaveConeBoundaryFlux_nonpos u c t
        (sub_pos.mpr (interior_subset ht).2)

/-- Classical energy on every shrinking-ball slice is nonnegative. -/
theorem backwardConeEnergy_nonneg (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (T t : ℝ) :
    0 ≤ backwardConeEnergy (n := n) u c T t :=
  MeasureTheory.setIntegral_nonneg measurableSet_ball fun _ _ ↦
    classicalWaveEnergyDensity_nonneg (n := n) u _

/-- If the shrinking-cone energy starts at zero, the boundary-flux estimate
forces it to remain zero at every time strictly below the vertex. -/
theorem backwardConeEnergy_eq_zero_of_initial (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) {a T : ℝ} (haT : a < T)
    (hderiv : ∀ t ∈ Set.Ico a T, HasDerivAt (backwardConeEnergy (n := n) u c T)
      (sphereIntegral n (classicalWaveConeBoundaryFlux (n := n) u c t) c (T - t)) t)
    (hzero : backwardConeEnergy (n := n) u c T a = 0) {t : ℝ} (ht : t ∈ Set.Ico a T) :
    backwardConeEnergy (n := n) u c T t = 0 :=
  le_antisymm (hzero ▸ backwardConeEnergy_antitone u c hderiv ⟨le_rfl, haT⟩ ht ht.1)
    (backwardConeEnergy_nonneg u c T t)

/-- Vanishing classical wave energy on a ball forces its continuous
nonnegative density to vanish pointwise in the ball. -/
theorem classicalWaveEnergyDensity_eq_zero_on_ball {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ^n) (t : ℝ) {r : ℝ}
    (henergy : ballIntegral n (fun y ↦ classicalWaveEnergyDensity (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t y)) c r = 0) :
    ∀ y ∈ Metric.ball c r,
      classicalWaveEnergyDensity (n := n) u (PDE.Common.timeSpaceCons (n := n) t y) = 0 :=
  Measure.eqOn_open_of_ae_eq ((MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
    (.of_forall fun _ ↦ classicalWaveEnergyDensity_nonneg (n := n) u _)
    (integrableOn_classicalWaveEnergyDensity_slice_ball hu c t r)).mp henergy)
    Metric.isOpen_ball ((contDiff_classicalWaveEnergyDensity (n := n) hu).continuous.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous).continuousOn
    continuous_const.continuousOn

/-- Zero displacement and velocity on the base ball give zero classical
energy on the base cone slice. -/
theorem backwardConeEnergy_initial_eq_zero {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) = 0) :
    backwardConeEnergy (n := n) u c T a = 0 := by
  refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero (.of_forall fun x hx ↦ ?_)
  -- the displacement vanishes near `x`, so its spatial gradient vanishes at `x`
  have hgrad : classicalWaveSpatialGradient (n := n) u
      (PDE.Common.timeSpaceCons (n := n) a x) = 0 := by
    ext i
    rw [classicalWaveSpatialGradient_apply, ← PDE.partialDeriv_timeSpaceCons_spatial i u a x
      ((hu.differentiable (by norm_num)).differentiableAt),
      PDE.partialDeriv_congr_nhds i (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx)
        fun y hy ↦ hpos y (Metric.ball_subset_closedBall hy))]
    simp
  simp [classicalWaveEnergyDensity, hvel x (Metric.ball_subset_closedBall hx), hgrad]

/-- If every open slice of a backward cone has zero classical wave energy,
then zero displacement on the base ball propagates through the closed cone.

This isolates the last step of the finite-propagation argument from the
particular PDE used to prove that the slice energies vanish. -/
theorem eq_zero_on_closed_backwardCone_of_energy_eq_zero
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ^n) {a T : ℝ}
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (henergyZero : ∀ t ∈ Set.Ico a T, backwardConeEnergy (n := n) u c T t = 0) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  intro t ht x hx
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact hpos x hx
  have hxdist : dist x c ≤ T - t := hx
  -- along the time line through `x` the velocity vanishes, so `u` is constant there
  have hline : (fun s ↦ PDE.Common.timeSpaceCons (n := n) s x) =
      coordinateLine (0 : Fin (n + 1)) (PDE.Common.timeSpaceCons (n := n) a x) := by
    funext s
    ext j
    cases j using Fin.cases <;> simp [coordinateLine]
  have hpathCont : ContinuousOn (fun s ↦ u (PDE.Common.timeSpaceCons (n := n) s x))
      (Set.Icc a t) := (hu.continuous.comp (hline ▸ (PDE.contDiff_coordinateLine
        (0 : Fin (n + 1)) (PDE.Common.timeSpaceCons (n := n) a x)).continuous)).continuousOn
  have hpathDeriv : ∀ s ∈ Set.Ioo a t,
      HasDerivAt (fun s ↦ u (PDE.Common.timeSpaceCons (n := n) s x)) 0 s := fun s hs ↦ by
    have hdensity := classicalWaveEnergyDensity_eq_zero_on_ball hu c s
      (by simpa [backwardConeEnergy] using henergyZero s ⟨hs.1.le, hs.2.trans_le ht.2⟩) x
      (by rw [Metric.mem_ball]; linarith [hs.2])
    have hut : (∂[0] u) (PDE.Common.timeSpaceCons (n := n) s x) = 0 := by
      unfold classicalWaveEnergyDensity at hdensity
      nlinarith [sq_nonneg ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) s x)),
        sq_nonneg ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons s x)‖]
    exact (PDE.hasDerivAt_timeSpaceCons u s x
      ((hu.differentiable (by norm_num)).differentiableAt)).congr_deriv hut
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hat.le hpathCont hpathDeriv
    (IntervalIntegrable.zero : IntervalIntegrable (0 : ℝ → ℝ) volume a t)
  have hpathEq : u (PDE.Common.timeSpaceCons (n := n) t x) =
      u (PDE.Common.timeSpaceCons (n := n) a x) := sub_eq_zero.mp (by simpa using hFTC.symm)
  rw [hpathEq]
  exact hpos x (by rw [Metric.mem_closedBall]; linarith [ht.1])

/-- Finite propagation in `n` spatial dimensions, given the energy transport identity.

Let `u` be a classical homogeneous wave on the backward cone with base time
`a`, vertex time `T`, and base ball `B(c, T - a)`, and assume the moving-ball
transport identity `htransport` for its cone energy. If its displacement and
velocity vanish on that base, then `u` vanishes on the entire closed backward
cone, including its lateral boundary and vertex.

`htransport` is the moving-ball Reynolds/Gauss formula.  Its volume term is
the explicit local energy-balance residual, proved above to vanish from
`waveOperator u = 0`; its surface term is the cone flux.
-/
theorem eq_zero_on_closed_backwardCone_of_transport {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := n) u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (htransport : ∀ t ∈ Set.Ico a T, HasDerivAt (backwardConeEnergy (n := n) u c T)
      (ballIntegral n (fun x ↦ classicalWaveEnergyBalanceResidual (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x)) c (T - t) +
      sphereIntegral n (classicalWaveConeBoundaryFlux (n := n) u c t) c (T - t)) t)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) = 0) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  rcases lt_or_ge a T with haT | hTa
  swap
  · intro t ht x hx
    obtain rfl : t = a := le_antisymm (ht.2.trans hTa) ht.1
    exact hpos x hx
  have hderiv (t) (ht : t ∈ Set.Ico a T) : HasDerivAt (backwardConeEnergy (n := n) u c T)
      (sphereIntegral n (classicalWaveConeBoundaryFlux (n := n) u c t) c (T - t)) t := by
    refine (htransport t ht).congr_deriv ?_
    rw [ballIntegral, MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero (.of_forall fun x hx ↦
      classicalWaveEnergyBalanceResidual_eq_zero hu.contDiffAt (hwave t ht x hx)), zero_add]
  exact eq_zero_on_closed_backwardCone_of_energy_eq_zero hu c hpos fun t ht ↦
    backwardConeEnergy_eq_zero_of_initial u c haT hderiv
      (backwardConeEnergy_initial_eq_zero hu c hpos hvel) ht

/-- Domain of dependence for two classical waves: agreement of displacement
and velocity on the base ball forces agreement throughout the closed backward
cone. -/
theorem eq_on_closed_backwardCone_of_eq_initialData_of_transport {u v : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := n) u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := n) v (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (htransport : ∀ t ∈ Set.Ico a T, HasDerivAt (backwardConeEnergy (n := n) (fun p ↦ u p - v p) c
      T) (ballIntegral n (fun x ↦ classicalWaveEnergyBalanceResidual (n := n) (fun p ↦ u p - v p)
      (PDE.Common.timeSpaceCons (n := n) t x)) c (T - t) + sphereIntegral n
      (classicalWaveConeBoundaryFlux (n := n) (fun p ↦ u p - v p) c t) c (T - t)) t)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvel : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = v (PDE.Common.timeSpaceCons (n := n) t x) := by
  have hzero := eq_zero_on_closed_backwardCone_of_transport (hu.sub hv) c
    (fun t ht x hx ↦ by
      rw [waveOperator_sub hu.contDiffAt hv.contDiffAt, huwave t ht x hx, hvwave t ht x hx,
        sub_self])
    htransport (fun x hx ↦ sub_eq_zero.mpr (hpos x hx)) fun x hx ↦ by
      rw [PDE.partialDeriv_sub ((hu.differentiable (by norm_num)).differentiableAt)
        ((hv.differentiable (by norm_num)).differentiableAt)]
      exact sub_eq_zero.mpr (hvel x hx)
  exact fun t ht x hx ↦ sub_eq_zero.mp (hzero t ht x hx)

end WaveEquation

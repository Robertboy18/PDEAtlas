/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.EnergyFinitePropagation
public import PDE.Hyperbolic.Models.Wave.InitialValueProblem
import PDE.Analysis.Calculus.EuclideanBall
import PDE.Analysis.Calculus.MovingBall
import PDE.FDeriv.SpaceTime

/-!
# Transport of classical energy on a shrinking ball

We specialize the Reynolds and Gauss formulas to the classical wave-energy
density. This gives the exact derivative of the energy on a backward cone, which
is the transport hypothesis of the `_of_transport` finite propagation and
domain-of-dependence theorems in `Classical.EnergyFinitePropagation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3, Theorem 6 and its proof, equation (46).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis PDE.Common Set
open scoped BigOperators RealInnerProductSpace Topology

variable {n : ℕ}

private noncomputable def energyFluxDivergence (u : ℝ^(n + 1) → ℝ) (t : ℝ)
    (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, (∂[i.succ] (classicalWaveEnergyFlux u i)) (timeSpaceCons t x)

private noncomputable def energyNormalFlux (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (t : ℝ)
    (x : ℝ^n) : ℝ :=
  (∂[0] u) (timeSpaceCons t x) *
    inner ℝ (classicalWaveSpatialGradient u (timeSpaceCons t x))
      (NormedSpace.normalize (x - c))

private theorem energyNormalFlux_eq_sum (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (t : ℝ) (x : ℝ^n) :
    energyNormalFlux u c t x = ∑ i : Fin n,
      classicalWaveEnergyFlux u i (timeSpaceCons t x) * (NormedSpace.normalize (x - c)) i := by
  simp only [energyNormalFlux, PiLp.inner_apply, classicalWaveSpatialGradient_apply,
    RCLike.inner_apply, conj_trivial, classicalWaveEnergyFlux]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reynolds's formula separates the time derivative of energy from the energy swept out
by the shrinking boundary. -/
private theorem hasDerivAt_backwardConeEnergy_reynolds [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : t < T) :
    HasDerivAt (backwardConeEnergy u c T) (ballIntegral n (fun x ↦
      (∂[0] (classicalWaveEnergyDensity u)) (timeSpaceCons t x)) c (T - t) - sphereIntegral n
      (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons t x)) c (T - t)) t := by
  let slice : ℝ → ℝ^n → ℝ := fun s x ↦ classicalWaveEnergyDensity u (timeSpaceCons s x)
  have henergy : ContDiff ℝ 1 (classicalWaveEnergyDensity u) :=
    contDiff_classicalWaveEnergyDensity hu
  have hslice : ContDiff ℝ 1 (Function.uncurry slice) :=
    henergy.comp (contDiff_timeSpaceCons_uncurry n)
  have htimeIntegral : ballIntegral n
          (fun x ↦ fderiv ℝ (Function.uncurry slice) (t, x) (1, 0)) c (T - t) = ballIntegral n
          (fun x ↦ (∂[0] (classicalWaveEnergyDensity u)) (timeSpaceCons t x))
          c (T - t) := by
    unfold ballIntegral
    apply setIntegral_congr_fun measurableSet_ball
    intro x _
    exact PDE.fderiv_timeSpaceCons_time (classicalWaveEnergyDensity u) t x
      henergy.differentiable_one.differentiableAt
  exact (hasDerivAt_ballIntegral_shrinking slice hslice c T (sub_pos.mpr ht)).congr_deriv
    (by rw [htimeIntegral])

/-- Gauss's formula identifies the integral of the spatial energy-flux divergence with
its outward normal flux. -/
private theorem ballIntegral_energyFluxDivergence [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ballIntegral n (energyFluxDivergence u t) c r =
      sphereIntegral n (energyNormalFlux u c t) c r := by
  let flux : Fin n → ℝ^n → ℝ := fun i x ↦ classicalWaveEnergyFlux u i (timeSpaceCons t x)
  have hflux (i : Fin n) : ContDiff ℝ 1 (flux i) :=
    (contDiff_classicalWaveEnergyFlux hu i).comp (contDiff_timeSpaceCons_spatial n t)
  have hdiv (x : ℝ^n) :
      (∑ i : Fin n, (∂[i] (flux i)) x) = energyFluxDivergence u t x := by
    apply Finset.sum_congr rfl
    intro i _
    exact PDE.partialDeriv_timeSpaceCons_spatial i (classicalWaveEnergyFlux u i) t x
      (contDiff_classicalWaveEnergyFlux hu i).differentiable_one.differentiableAt
  calc
    ballIntegral n (energyFluxDivergence u t) c r =
        ballIntegral n (fun x ↦ ∑ i : Fin n, (∂[i] (flux i)) x) c r := by
      unfold ballIntegral
      exact setIntegral_congr_fun measurableSet_ball fun x _ ↦ (hdiv x).symm
    _ = sphereIntegral n (fun x ↦ ∑ i : Fin n, flux i x * (NormedSpace.normalize (x - c)) i) c r :=
      ballIntegral_divergence_eq_sphereIntegral_normal_flux flux hflux c hr
    _ = sphereIntegral n (energyNormalFlux u c t) c r := by
      congr 1
      funext x
      exact (energyNormalFlux_eq_sum u c t x).symm

/-- The volume integral of the local energy residual is the difference of two integrable
continuous densities. -/
private theorem ballIntegral_classicalWaveEnergyBalanceResidual
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ^n) (t r : ℝ) :
    ballIntegral n (fun x ↦ classicalWaveEnergyBalanceResidual u (timeSpaceCons t x)) c r =
      ballIntegral n (fun x ↦ (∂[0] (classicalWaveEnergyDensity u)) (timeSpaceCons t x)) c r -
      ballIntegral n (energyFluxDivergence u t) c r := by
  have hspace : Continuous (timeSpaceCons (n := n) t) :=
    (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have htime : Continuous (fun x ↦ (∂[0] (classicalWaveEnergyDensity u)) (timeSpaceCons t x)) :=
    ((contDiff_classicalWaveEnergyDensity hu).continuous_fderiv one_ne_zero
      |>.clm_apply continuous_const).comp hspace
  have hdiv : Continuous (energyFluxDivergence u t) := by
    apply continuous_finsetSum
    intro i _
    exact ((contDiff_classicalWaveEnergyFlux hu i).continuous_fderiv one_ne_zero
      |>.clm_apply continuous_const).comp hspace
  exact integral_sub ((htime.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      Metric.ball_subset_closedBall)
    ((hdiv.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      Metric.ball_subset_closedBall)

/-- On a positive-radius sphere the normal is its unit-sphere parameter. This makes both
terms in the cone boundary flux integrable and permits subtraction under the integral. -/
private theorem sphereIntegral_classicalWaveConeBoundaryFlux {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    sphereIntegral n (classicalWaveConeBoundaryFlux u c t) c r =
      sphereIntegral n (energyNormalFlux u c t) c r -
        sphereIntegral n (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons t x)) c r := by
  have hboundary : Continuous
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ c + r • (ω : ℝ^n)) := by
    have hval : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ (ω : ℝ^n)) := continuous_subtype_val
    exact continuous_const.add (hval.const_smul r)
  have hnormal : Continuous
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ energyNormalFlux u c t (c + r • (ω : ℝ^n))) := by
    have heq : (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ energyNormalFlux u c t (c + r • (ω : ℝ^n))) =
          fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
            ∑ i : Fin n, classicalWaveEnergyFlux u i (timeSpaceCons t (c + r • (ω : ℝ^n))) *
              (ω : ℝ^n) i := by
      funext ω
      rw [energyNormalFlux_eq_sum, add_sub_cancel_left, NormedSpace.normalize_smul_of_pos hr,
        NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp ω.property)]
    rw [heq]
    apply continuous_finsetSum
    intro i _
    exact ((contDiff_classicalWaveEnergyFlux hu i).continuous.comp
      ((contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.comp hboundary)).mul
        ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)
  have henergy : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        classicalWaveEnergyDensity u (timeSpaceCons t (c + r • (ω : ℝ^n)))) :=
    (contDiff_classicalWaveEnergyDensity hu).continuous.comp
      ((contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.comp hboundary)
  have hcompact (f : Metric.sphere (0 : ℝ^n) 1 → ℝ) : HasCompactSupport f :=
    isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ mem_univ _)
  unfold sphereIntegral
  change |r| ^ (n - 1) * (∫ ω, (energyNormalFlux u c t (c + r • (ω : ℝ^n)) -
        classicalWaveEnergyDensity u (timeSpaceCons t (c + r • (ω : ℝ^n))))
      ∂((volume : Measure (ℝ^n)).toSphere)) = _
  rw [integral_sub (hnormal.integrable_of_hasCompactSupport (hcompact _))
    (henergy.integrable_of_hasCompactSupport (hcompact _))]
  ring

/-- The exact Reynolds and Gauss derivative of the shrinking-ball energy, as in (46) of Evans,
§2.4.3.

The volume term is the declared local energy-balance residual, and the
surface term is the declared cone boundary flux. -/
theorem hasDerivAt_backwardConeEnergy [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : t < T) :
    HasDerivAt (backwardConeEnergy (n := n) u c T) (ballIntegral n
      (fun x ↦ classicalWaveEnergyBalanceResidual u (timeSpaceCons t x)) c (T - t) +
      sphereIntegral n (classicalWaveConeBoundaryFlux u c t) c (T - t)) t := by
  apply (hasDerivAt_backwardConeEnergy_reynolds hu c T ht).congr_deriv
  rw [ballIntegral_classicalWaveEnergyBalanceResidual hu,
    sphereIntegral_classicalWaveConeBoundaryFlux hu c t (sub_pos.mpr ht),
    ballIntegral_energyFluxDivergence hu c t (sub_pos.mpr ht)]
  ring

/-- Finite propagation speed in `n` spatial dimensions, Evans, §2.4.3, Theorem 6.

A classical homogeneous wave whose displacement and velocity vanish on the
base ball vanishes on the whole closed backward cone. The moving-ball
transport identity is supplied by `hasDerivAt_backwardConeEnergy`. -/
theorem eq_zero_on_closed_backwardCone [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := n) u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) = 0) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  apply eq_zero_on_closed_backwardCone_of_transport (n := n) hu c hwave
  · intro t ht
    exact hasDerivAt_backwardConeEnergy (n := n) hu c T ht.2
  · exact hpos
  · exact hvel

/-- Domain of dependence for two classical waves, as in Evans, §2.4.3(b), with the moving-ball
transport identity discharged internally. -/
theorem eq_on_closed_backwardCone_of_eq_initialData [Fact (0 < n)] {u v : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := n) u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := n) v (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvel : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = v (PDE.Common.timeSpaceCons (n := n) t x) := by
  apply eq_on_closed_backwardCone_of_eq_initialData_of_transport (n := n) hu hv c huwave hvwave
  · intro t ht
    exact hasDerivAt_backwardConeEnergy (n := n) (hu.sub hv) c T ht.2
  · exact hpos
  · exact hvel

/-- Global uniqueness for classical waves with the same assigned Cauchy data,
at every nonnegative time.

For a requested point `(t,x)`, apply the moving-ball domain-of-dependence
theorem to a backward cone with base time zero and tip time `t + 1`. -/
theorem eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData [Fact (0 < n)]
    {g h : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hsolu : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := n) g h) u)
    (hsolv : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := n) g h) v) {t : ℝ}
    (ht : 0 ≤ t) (x : ℝ^n) :
    u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  have hcone := eq_on_closed_backwardCone_of_eq_initialData
      (n := n) hu hv x (a := 0) (T := t + 1) (fun s hs y _ ↦
        waveResidualAssignedCauchyDataProblem.residual_eq_nonnegative hu hsolu hs.1 y)
      (fun s hs y _ ↦ waveResidualAssignedCauchyDataProblem.residual_eq_nonnegative hv hsolv hs.1 y)
      (fun y _ ↦ by
        rw [ forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq
            hsolu (by simp), forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq
            hsolv (by simp)
        ])
      (fun y _ ↦ by
        rw [ forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq
            hsolu (by simp), forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq
            hsolv (by simp)
        ])
  exact hcone t ⟨ht, by linarith⟩ x (by simp)

end WaveEquation

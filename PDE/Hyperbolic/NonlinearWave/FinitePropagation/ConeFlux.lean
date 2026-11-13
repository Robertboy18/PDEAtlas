/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Basic
public import PDE.Analysis.Integration.Cone.NormalTrace

/-!
# Null energy flux on the lateral cone

The quadratic expression in the flux identity (3) of Evans, §12.1.2, Theorem 2(i), is the
negative of the flux density through the boundary of the shrinking ball, as in the computation
(4) of the proof there. Smoothness and the unit-normal bound make its spatial cone-graph pullback
integrable even at the vertex.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i) and its proof, equations (3)-(4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped RealInnerProductSpace

namespace WaveEquation

variable {n : ℕ}

/-- The quadratic null flux with an independently supplied spatial normal. -/
def semilinearWaveNullFlux (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) (ν : ℝ^n) : ℝ :=
  (1 / 2 : ℝ) * ‖(∂[0] u) p • ν - classicalWaveSpatialGradient u p‖ ^ 2 + V (u p)

/-- The integrand of the flux identity (3) of Evans, §12.1.2, with the radial normal at
nonvertex points. -/
def semilinearWaveConeDissipation (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (c : ℝ^n) (p : ℝ^(n + 1)) : ℝ :=
  semilinearWaveNullFlux V u p (NormedSpace.normalize (spatialPart p - c))

/-- The shrinking-ball boundary flux is the negative null-flux square. -/
theorem semilinearWaveConeBoundaryFlux_eq_neg_dissipation
    (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (c x : ℝ^n) (t : ℝ) (hx : x ≠ c) :
    semilinearWaveConeBoundaryFlux V u c t x =
      -semilinearWaveConeDissipation V u c (timeSpaceCons t x) := by
  have hν := NormedSpace.norm_normalize (sub_ne_zero.mpr hx)
  unfold semilinearWaveConeBoundaryFlux classicalWaveConeBoundaryFlux
    classicalWaveEnergyDensity semilinearWaveConeDissipation semilinearWaveNullFlux
  simp only [spatialPart_timeSpaceCons, norm_sub_sq_real, norm_smul, hν, mul_one,
    Real.norm_eq_abs, sq_abs, real_inner_smul_left]
  rw [real_inner_comm (NormedSpace.normalize (x - c))]
  ring

/-- The null flux is continuous jointly in spacetime and an arbitrary normal. -/
theorem continuous_semilinearWaveNullFlux {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : ContDiff ℝ 2 u) :
    Continuous (Function.uncurry (semilinearWaveNullFlux V u)) := by
  have ht := (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0) hu).continuous
  have hg := (contDiff_classicalWaveSpatialGradient (m := 1) hu).continuous
  exact (continuous_const.mul ((((ht.comp continuous_fst).smul continuous_snd).sub
    (hg.comp continuous_fst)).norm.pow 2)).add (hV.comp (hu.continuous.comp continuous_fst))

/-- The normal's value at the vertex is measurable, although it is not continuous. -/
theorem measurable_semilinearWaveConeDissipation {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) :
    Measurable (semilinearWaveConeDissipation V u c) :=
  PDE.Analysis.measurable_coneNormalTrace (continuous_semilinearWaveNullFlux hV hu) c

/-- Smooth fields have integrable cone-graph null flux on every finite ball.
The unit-normal bound controls the only discontinuity, at the cone vertex. -/
theorem integrableOn_semilinearWaveConeDissipation_graph {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) (T : ℝ) :
    IntegrableOn (fun x ↦ semilinearWaveConeDissipation V u c (backwardConeGraph c T x))
      (Metric.ball c T) :=
  PDE.Analysis.integrableOn_coneNormalTrace_graph (continuous_semilinearWaveNullFlux hV hu) c T T

/-- Unit-sphere parametrization of the null flux. At zero radius it retains
an angular normal and therefore gives a continuous representative in time. -/
def semilinearWaveAngularDissipation (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (c : ℝ^n) (T t : ℝ) : ℝ :=
  |T - t| ^ (n - 1) * ∫ ω : Metric.sphere (0 : ℝ^n) 1,
    semilinearWaveNullFlux V u (timeSpaceCons t (c + (T - t) • (ω : ℝ^n))) ω
      ∂((volume : Measure (ℝ^n)).toSphere)

/-- The angular representation of cone dissipation is continuous through the vertex. -/
theorem continuous_semilinearWaveAngularDissipation {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) (T : ℝ) :
    Continuous (semilinearWaveAngularDissipation V u c T) :=
  PDE.Analysis.continuous_coneAngularIntegral (continuous_semilinearWaveNullFlux hV hu) c T

/-- Away from the vertex, the angular and radial-normal flux expressions coincide. -/
theorem sphereIntegral_semilinearWaveConeDissipation_eq_angular (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : t < T) :
    PDE.Analysis.sphereIntegral n (fun x ↦ semilinearWaveConeDissipation V u c (timeSpaceCons t x))
      c (T - t) = semilinearWaveAngularDissipation V u c T t :=
  PDE.Analysis.sphereIntegral_coneNormalTrace_eq_angular
    (Function.uncurry (semilinearWaveNullFlux V u)) c T ht

/-- Spherical cone dissipation is integrable in time up to the vertex. Only
its terminal value may differ from the continuous angular representation. -/
theorem intervalIntegrable_sphereIntegral_semilinearWaveConeDissipation {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : Continuous V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t ↦ PDE.Analysis.sphereIntegral n
      (fun x ↦ semilinearWaveConeDissipation V u c (timeSpaceCons t x)) c (T - t)) volume 0 T :=
  PDE.Analysis.intervalIntegrable_sphereIntegral_coneNormalTrace
    (continuous_semilinearWaveNullFlux hV hu) c hT le_rfl

end WaveEquation

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity
public import PDE.Hyperbolic.Classical.EnergyFinitePropagation
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Cone energy and boundary flux for semilinear waves

We define the semilinear energy on a shrinking spatial ball and its
lateral cone flux for

`uₜₜ - Δu + V'(u) = 0`.

The nonlinearity is `deriv V`, with primitive `V`. The results identify the
split cone energy with the integral of the full semilinear energy density and
separate the classical and potential contributions to the boundary flux.

The Reynolds derivative is proved in `FinitePropagation.Transport`; the
finite-propagation theorems are in `FinitePropagation.QuadraticLowerBound`.

The cone energy is the local energy `e(t)` of Evans, §12.1.2, Theorem 2, and the lateral flux is
the boundary integrand of the computation (4) in its proof, which equals
`-(|uₜν - Du|² / 2 + V(u))`; its sign for `V ≥ 0` is step 2 of that proof.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2 and its proof, equation (4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis Set
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- Lateral flux `uₜ D_xu · ν - e` through a shrinking cone, where `e` is the
full semilinear energy density. -/
noncomputable def semilinearWaveConeBoundaryFlux (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (t : ℝ)
    (y : ℝ^n) : ℝ :=
  classicalWaveConeBoundaryFlux (n := n) u c t y - V (u (PDE.Common.timeSpaceCons (n := n) t y))

/-- Semilinear energy on the shrinking ball `B(c, T - t)`.

The definition keeps the classical and potential contributions separate so
the generic moving-ball theorem can be reused directly. -/
noncomputable def semilinearBackwardConeEnergy (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (c : ℝ^n)
    (T t : ℝ) : ℝ :=
  backwardConeEnergy (n := n) u c T t +
    ballIntegral n (fun y ↦ V (u (PDE.Common.timeSpaceCons (n := n) t y))) c (T - t)

/-- The split definition of semilinear cone energy is the integral of the
full semilinear energy density. -/
theorem semilinearBackwardConeEnergy_eq_ballIntegral
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : Continuous V) (hu : ContDiff ℝ 1 u) (c : ℝ^n) (T t : ℝ) :
    semilinearBackwardConeEnergy (n := n) V u c T t =
      ballIntegral n
        (fun y ↦ semilinearWaveEnergyDensity (n := n) V u (PDE.Common.timeSpaceCons (n := n) t y))
        c (T - t) := by
  have hspace := (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have hball {f : ℝ^n → ℝ} (hf : Continuous f) : IntegrableOn f (Metric.ball c (T - t)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c (T - t))).mono_set
      Metric.ball_subset_closedBall
  unfold semilinearBackwardConeEnergy backwardConeEnergy semilinearWaveEnergyDensity ballIntegral
  exact (integral_add (hball ((contDiff_classicalWaveEnergyDensity (m := 0) hu).continuous.comp
    hspace)) (hball (hV.comp (hu.continuous.comp hspace)))).symm

/-- For a nonnegative potential, the semilinear lateral cone flux is
nonpositive. -/
theorem semilinearWaveConeBoundaryFlux_nonpos (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    (u : ℝ^(n + 1) → ℝ) (c y : ℝ^n) {r t : ℝ} (hr : 0 < r) (hy : y ∈ Metric.sphere c r) :
    semilinearWaveConeBoundaryFlux (n := n) V u c t y ≤ 0 := by
  unfold semilinearWaveConeBoundaryFlux
  linarith [classicalWaveConeBoundaryFlux_nonpos (t := t) u c y hr hy,
    hVnonneg (u (PDE.Common.timeSpaceCons t y))]

/-- The integrated semilinear lateral cone flux is nonpositive. -/
theorem sphereIntegral_semilinearWaveConeBoundaryFlux_nonpos (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    sphereIntegral n (semilinearWaveConeBoundaryFlux (n := n) V u c t) c r ≤ 0 :=
  sphereIntegral_nonpos fun y hy ↦
    semilinearWaveConeBoundaryFlux_nonpos V hVnonneg u c y hr (by simpa [abs_of_pos hr] using hy)

/-- Sphere integrals of continuous functions are additive under subtraction. -/
private theorem sphereIntegral_sub_of_continuous (f g : ℝ^n → ℝ) (hf : Continuous f)
    (hg : Continuous g) (c : ℝ^n) (r : ℝ) :
    sphereIntegral n (fun x ↦ f x - g x) c r =
      sphereIntegral n f c r - sphereIntegral n g c r := by
  have hi {h : ℝ^n → ℝ} (hh : Continuous h) :
      Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ h (c + r • (ω : ℝ^n))) volume.toSphere :=
    (hh.comp (by fun_prop)).integrable_of_hasCompactSupport (.of_compactSpace _)
  unfold sphereIntegral
  rw [← mul_sub, ← integral_sub (hi hf) (hi hg)]

/-- The integral of the declared semilinear cone flux is the classical cone
flux minus the potential energy swept out by the shrinking boundary. -/
theorem sphereIntegral_semilinearWaveConeBoundaryFlux_eq_sub
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    sphereIntegral n (semilinearWaveConeBoundaryFlux (n := n) V u c t) c r =
      sphereIntegral n (classicalWaveConeBoundaryFlux (n := n) u c t) c r -
        sphereIntegral n (fun x ↦ V (u (PDE.Common.timeSpaceCons (n := n) t x))) c r := by
  have hspace : Continuous (PDE.Common.timeSpaceCons (n := n) t) :=
    (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have h0 := (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0) hu).continuous
  have hgrad := (contDiff_classicalWaveSpatialGradient (n := n) (m := 1) hu).continuous
  have henergy := (contDiff_classicalWaveEnergyDensity (n := n) (m := 1) hu).continuous
  have hflux : EqOn (classicalWaveConeBoundaryFlux u c t) (fun y ↦
      (∂[0] u) (PDE.Common.timeSpaceCons t y) *
        ⟪classicalWaveSpatialGradient u (PDE.Common.timeSpaceCons t y), r⁻¹ • (y - c)⟫ -
      classicalWaveEnergyDensity u (PDE.Common.timeSpaceCons t y)) (Metric.sphere c r) :=
    fun y hy ↦ by
      have hnorm : ‖y - c‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hy
      simp [classicalWaveConeBoundaryFlux, NormedSpace.normalize, hnorm]
  rw [sphereIntegral_congr_on_sphere hr hflux, ← sphereIntegral_sub_of_continuous _
    (fun x ↦ V (u (PDE.Common.timeSpaceCons t x))) (by fun_prop)
    (hV.continuous.comp (hu.continuous.comp hspace))]
  exact sphereIntegral_congr_on_sphere hr fun y hy ↦ by
    rw [semilinearWaveConeBoundaryFlux, hflux hy]

end WaveEquation

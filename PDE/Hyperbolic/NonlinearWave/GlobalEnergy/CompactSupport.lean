/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Differentiation
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SliceSupport
import PDE.Analysis.Calculus.CompactEnergy.Inequality
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.Calculus

/-!
# Compact support and differentiation of wave energy

A compact spatial slice suffices to remove the integrated flux. On an open time
interval with common compact support, the kinetic and potential energy also have
common compact support, which justifies differentiation under the integral.
The latter hypothesis is a local intermediate step; the conservation theorems assume
compact spatial slices separately at each time, as Evans does in §12.1.1, Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Spatial compact support alone gives compact support of the energy flux. -/
theorem hasCompactSupport_semilinearWaveSpatialEnergyFlux {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    (hu : ∀ x, DifferentiableAt ℝ u (timeSpaceCons t x))
    (hs : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) (i : Fin n) :
    HasCompactSupport (semilinearWaveSpatialEnergyFlux u i t) := by
  have heq : semilinearWaveSpatialEnergyFlux u i t = (fun x ↦ (∂[0] u) (timeSpaceCons t x)) *
        (∂[i] (fun x : ℝ^n ↦ u (timeSpaceCons t x))) := by
    funext x
    rw [Pi.mul_apply, PDE.partialDeriv_timeSpaceCons_spatial i u t x (hu x)]
    rfl
  rw [heq]
  exact (hs.partialDeriv i).mul_left

/-- A common compact support for the field also supports its energy density,
provided the potential vanishes at zero. -/
theorem semilinearWaveSpatialEnergyDensity_eq_zero_off_support {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {I : Set ℝ} {K : Set (ℝ^n)} (hVzero : V 0 = 0) (hI : IsOpen I) (hK : IsClosed K)
    (hu : ∀ t ∈ I, ∀ x, ContDiffAt ℝ 1 u (timeSpaceCons t x))
    (hs : ∀ t ∈ I, ∀ x ∉ K, u (timeSpaceCons t x) = 0) {t : ℝ} (ht : t ∈ I) {x : ℝ^n} (hx : x ∉ K) :
    semilinearWaveSpatialEnergyDensity V u t x = 0 := by
  have htime := PDE.Analysis.time_partial_eq_zero_off_support hI hu hs ht hx
  have heq : (fun y : ℝ^n ↦ u (timeSpaceCons t y)) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy using hs t ht y hy
  have hspace (i : Fin n) : (∂[i.succ] u) (timeSpaceCons t x) = 0 := by
    rw [← PDE.partialDeriv_timeSpaceCons_spatial i u t x
      ((hu t ht x).differentiableAt one_ne_zero), PDE.partialDeriv_congr_nhds i heq]
    exact PDE.partialDeriv_const 0
  have hgrad : classicalWaveSpatialGradient u (timeSpaceCons t x) = 0 := by
    ext i
    simpa only [classicalWaveSpatialGradient_apply, PiLp.zero_apply] using hspace i
  simp [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
    classicalWaveEnergyDensity, htime, hgrad, hs t ht x hx, hVzero]

/-- Locally uniform compact support discharges both differentiation under the
integral and the spatial flux assumptions in global energy conservation. -/
theorem hasDerivAt_semilinearWaveSpatialEnergy_of_compact_support {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {I : Set ℝ} {K : Set (ℝ^n)} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hI : IsOpen I)
    (hK : IsCompact K) (hu : ∀ t ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (hs : ∀ t ∈ I, ∀ x ∉ K, u (timeSpaceCons t x) = 0) {t : ℝ} (ht : t ∈ I)
    (hwave : ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    HasDerivAt (semilinearWaveSpatialEnergy V u) 0 t := by
  have henergy := PDE.Analysis.hasDerivAt_integral_compact_support
    hI hK (fun s hsI x ↦ contDiffAt_semilinearWaveEnergyDensity hV.contDiffAt (hu s hsI x))
    (fun s hsI x hx ↦ semilinearWaveSpatialEnergyDensity_eq_zero_off_support
      hVzero hI hK.isClosed (fun r hr y ↦ (hu r hr y).of_le (by norm_num)) hs hsI hx) ht
  change HasDerivAt (semilinearWaveSpatialEnergy V u)
    (∫ x, semilinearWaveSpatialEnergyTimeDerivative V u t x) t at henergy
  rw [integral_semilinearWaveSpatialEnergyTimeDerivative_eq_zero hV (hu t ht) hwave
    (fun i ↦ hasCompactSupport_semilinearWaveSpatialEnergyFlux
      (fun x ↦ (hu t ht x).differentiableAt (by norm_num))
      (HasCompactSupport.intro hK (hs t ht)) i)] at henergy
  exact henergy

/-- The separate compact-slice hypothesis gives zero energy derivative
on a dense set of times in every open lifespan interval. Extending this to all
times still requires propagation of the support obtained by Baire category. -/
theorem dense_hasDerivAt_semilinearWaveSpatialEnergy_eq_zero {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {I : Set ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hI : IsOpen I)
    (hu : ∀ t ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (hs : ∀ t ∈ I, HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x)))
    (hwave : ∀ t ∈ I, ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    Dense {t : I | HasDerivAt (semilinearWaveSpatialEnergy V u) 0 (t : ℝ)} := by
  let : BaireSpace I := hI.baireSpace
  have hc (x : ℝ^n) : Continuous (fun t : I ↦ u (timeSpaceCons t x)) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    have hmap : Continuous (fun s : I ↦ timeSpaceCons (s : ℝ) x) :=
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        (continuous_subtype_val.prodMk continuous_const)
    exact (hu t t.property x).continuousAt.comp (f := fun s : I ↦
      timeSpaceCons (s : ℝ) x) hmap.continuousAt
  apply (dense_locally_uniform_spatial_support hc (fun t ↦ hs t t.property)).mono
  rintro t ⟨R, hR⟩
  have hR' := (eventually_nhds_subtype_iff I t
    (fun s ↦ ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0)).mp hR
  rw [hI.nhdsWithin_eq t.property] at hR'
  obtain ⟨J, hJ, hJo, htJ⟩ := mem_nhds_iff.mp (hR'.and (hI.mem_nhds t.property))
  exact hasDerivAt_semilinearWaveSpatialEnergy_of_compact_support hV hVzero hJo
    (isCompact_closedBall (0 : ℝ^n) (R : ℝ)) (fun s hsJ x ↦ hu s (hJ hsJ).2 x)
    (fun s hsJ x hx ↦ (hJ hsJ).1 x
      (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
    htJ (hwave t t.property)

end WaveEquation

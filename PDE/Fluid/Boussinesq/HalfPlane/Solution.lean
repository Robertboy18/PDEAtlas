/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.LifeSpan
public import PDE.Fluid.Incompressible.HalfPlane.VelocityField
import PDE.Analysis.Calculus.SliceDerivative

/-!
# Classical half-plane Boussinesq solutions with the Biot-Savart velocity

The classical class `IsClassicalVorticityStreamSolutionOn` imposes the equations on the open
upper half-plane but does not determine the velocity: a stream function `ψ + c x₂` solves the
same Poisson problem, and a Galilean change of frame then gives a second solution from the same
data. `IsSolutionOn sol I` adds that at every time the stream function is, on the closed
half-plane, the Green potential of the vorticity, so that the velocity is the half-plane
Biot-Savart velocity `halfPlaneVelocity`, and that the supports are bounded uniformly on compact
time intervals. Only the values on the closed half-plane are determined by the equations; the
fields below the boundary are classical extensions.

On a compact interval `[a, b] ⊆ I` the joint regularity and the common support give uniform
bounds of the fields and their spatial derivatives on the closed half-plane and their continuity
in time uniformly in space (`exists_bounds_of_contDiffOn`), hence the vorticity is a vorticity
history in the sense of `IncompressibleFlow.IsVorticityHistory`.

## Main definitions

* `IsSolutionOn sol I`: classical solution with the Green stream function and bounded supports
  (`HasBoundedSupportOn`, in `LifeSpan`).
* `HasDataAt sol t₀ ω₀ θ₀`: the fields take the values `ω₀, θ₀` at time `t₀` on the closed
  half-plane.

## Main results

* `IsSolutionOn.velocity_eq`: on the closed half-plane the velocity is the half-plane
  Biot-Savart velocity of the vorticity.
* `IsSolutionOn.exists_isVorticityHistory`: on every compact subinterval the vorticity is a
  vorticity history with Hölder exponent `α ∈ (0, 1]`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Boussinesq

open GreenFunction IncompressibleFlow
open PDE.Analysis (evenReflection evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)

/-- The classical class restricts to smaller sets of times. -/
theorem IsClassicalVorticityStreamSolutionOn.mono {sol : VorticityStreamFields} {I J : Set ℝ}
    (h : IsClassicalVorticityStreamSolutionOn sol I) (hJ : J ⊆ I) :
    IsClassicalVorticityStreamSolutionOn sol J where
  regularity :=
    { vorticity_contDiffOn :=
        h.regularity.vorticity_contDiffOn.mono (prod_mono subset_rfl hJ)
      temperature_contDiffOn :=
        h.regularity.temperature_contDiffOn.mono (prod_mono subset_rfl hJ)
      vorticity_differentiableAt_time := fun ht ↦
        h.regularity.vorticity_differentiableAt_time (hJ ht)
      temperature_differentiableAt_time := fun ht ↦
        h.regularity.temperature_differentiableAt_time (hJ ht)
      streamFunction_spatial_contDiff := fun ht ↦
        h.regularity.streamFunction_spatial_contDiff (hJ ht) }
  vorticity_equation := fun _ _ hx ht ↦ h.vorticity_equation hx (hJ ht)
  temperature_equation := fun _ _ hx ht ↦ h.temperature_equation hx (hJ ht)
  streamFunction_equation := fun _ _ hx ht ↦ h.streamFunction_equation hx (hJ ht)
  zero_streamFunction_boundary := fun x₁ _ ht ↦ h.zero_streamFunction_boundary x₁ (hJ ht)

namespace HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- A classical solution of the half-plane Boussinesq system on the times `I` whose stream
function is, at every time, the Green potential of the vorticity on the closed half-plane, and
whose supports are bounded uniformly on compact time intervals. -/
structure IsSolutionOn (sol : VorticityStreamFields) (I : Set ℝ) : Prop where
  /-- The classical equations and regularity. -/
  classical : IsClassicalVorticityStreamSolutionOn sol I
  /-- The stream function is the Green potential of the vorticity on the closed half-plane. -/
  stream : ∀ t ∈ I, ∀ x : ℝ^2, 0 ≤ x 1 →
    sol.streamFunction x t = halfSpaceGreenPotential (fun y ↦ sol.vorticity y t) x
  /-- Supports bounded uniformly on compact time intervals. -/
  support : HasBoundedSupportOn sol I

/-- The fields take the values `ω₀` and `θ₀` at time `t₀` on the closed half-plane. -/
def HasDataAt (sol : VorticityStreamFields) (t₀ : ℝ) (ω₀ θ₀ : ℝ^2 → ℝ) : Prop :=
  ∀ x : ℝ^2, 0 ≤ x 1 → sol.vorticity x t₀ = ω₀ x ∧ sol.temperature x t₀ = θ₀ x

namespace IsSolutionOn

variable {sol : VorticityStreamFields} {I : Set ℝ}

/-- Solutions restrict to smaller sets of times. -/
theorem mono (h : IsSolutionOn sol I) {J : Set ℝ} (hJ : J ⊆ I) : IsSolutionOn sol J where
  classical := h.classical.mono hJ
  stream t ht := h.stream t (hJ ht)
  support := h.support.mono hJ

/-- At every time the vorticity vanishes on the closed half-plane outside a disc. -/
theorem exists_vorticity_eq_zero (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I) :
    ∃ R : ℝ, ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ → sol.vorticity x t = 0 := by
  obtain ⟨R, hR⟩ := h.support t t (by simpa using ht)
  exact ⟨R, fun x hx hxR ↦ (hR t ⟨le_rfl, le_rfl⟩ x hx hxR).1⟩

/-- Every time slice of the vorticity is globally `C¹`. -/
theorem contDiff_vorticity (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ 1 (fun x ↦ sol.vorticity x t) :=
  h.classical.regularity.vorticity_spatial_contDiff ht

/-- Every time slice of the temperature is globally `C¹`. -/
theorem contDiff_temperature (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ 1 (fun x ↦ sol.temperature x t) :=
  h.classical.regularity.temperature_spatial_contDiff ht

/-- On the closed half-plane the velocity of a solution is the half-plane Biot-Savart velocity
of its vorticity. -/
theorem velocity_eq (h : IsSolutionOn sol I) {t : ℝ} (ht : t ∈ I) {x : ℝ^2} (hx : 0 ≤ x 1) :
    vorticityStreamVelocity sol x t = halfPlaneVelocity (fun y ↦ sol.vorticity y t) x := by
  obtain ⟨R, hR⟩ := h.exists_vorticity_eq_zero ht
  set ω : ℝ^2 → ℝ := fun y ↦ sol.vorticity y t
  set φ := halfSpaceGreenPotential (evenReflection ω)
  have hω : Continuous ω := (h.contDiff_vorticity ht).continuous
  have hφ : ContDiff ℝ 1 φ := contDiff_one_halfSpaceGreenPotential
    (continuous_evenReflection hω.continuousOn)
    (hasCompactSupport_evenReflection_of_eq_zero hR)
  have hφω : φ = halfSpaceGreenPotential ω :=
    halfSpaceGreenPotential_congr fun y hy ↦ evenReflection_of_nonneg (le_of_lt hy)
  have hψ : ContDiff ℝ 2 (fun y ↦ sol.streamFunction y t) :=
    h.classical.regularity.streamFunction_spatial_contDiff ht
  have heq : EqOn (fun y ↦ sol.streamFunction y t) φ H̄ := fun y hy ↦ by
    simp only [hφω]
    exact h.stream t ht y hy
  have hderiv : fderiv ℝ (fun y ↦ sol.streamFunction y t) x = fderiv ℝ φ x := by
    have h1 := (hψ.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt (s := H̄)
    have h2 := (hφ.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt (s := H̄)
    exact (uniqueDiffOn_closedUpper x hx).eq h1 (h2.congr (fun y hy ↦ heq hy) (heq hx))
  have hpartial (i : Fin 2) :
      (∂[i] (fun y ↦ sol.streamFunction y t)) x = (∂[i] (halfSpaceGreenPotential ω)) x := by
    simp only [PDE.partialDeriv, hderiv, ← hφω]
  ext k
  fin_cases k
  · simp [vorticityStreamVelocity, halfPlaneVelocity, planarStreamVelocity, hpartial]
  · simp [vorticityStreamVelocity, halfPlaneVelocity, planarStreamVelocity, hpartial]

/-- **Uniform bounds on compact time intervals.** On `[a, b] ⊆ I` with `a < b` the vorticity of a
solution vanishes on the closed half-plane outside a common disc, is bounded together with the
spatial derivatives of its slices on the closed half-plane uniformly in time, and is continuous
in time uniformly on the closed half-plane; for every exponent `α ∈ [0, 1]` it is therefore a
vorticity history whose Hölder constant comes from the gradient bound. -/
theorem exists_isVorticityHistory (h : IsSolutionOn sol I) {a b α : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ I) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ R B B₁ : ℝ, 0 ≤ B ∧ 0 ≤ B₁ ∧
      IsVorticityHistory (fun t x ↦ sol.vorticity x t) a b α R B (max B₁ (2 * B)) ∧
      ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderiv ℝ (fun y ↦ sol.vorticity y t) x‖ ≤ B₁ := by
  obtain ⟨R, hR⟩ := h.support a b hI
  obtain ⟨B, B₁, hB0, hB₁0, hB, hB₁, hu, -⟩ :=
    PDE.Analysis.exists_bounds_of_contDiffOn (f := sol.vorticity) hab hI
      h.classical.regularity.vorticity_contDiffOn fun t ht x hx hxR ↦ (hR t ht x hx hxR).1
  have hc (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (fun x ↦ sol.vorticity x t) :=
    h.contDiff_vorticity (hI ht)
  have hfd (t : ℝ) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderivWithin ℝ (fun y ↦ sol.vorticity y t) H̄ x =
        fderiv ℝ (fun y ↦ sol.vorticity y t) x :=
    ((hc t ht).differentiable (by norm_num) x).fderivWithin (uniqueDiffOn_closedUpper x hx)
  refine ⟨R, B, B₁, hB0, hB₁0, ?_, hB₁⟩
  refine IsVorticityHistory.of_fderivWithin_le (fun t ht ↦ (hc t ht).contDiffOn)
    (fun t ht x hx hxR ↦ (hR t ht x hx hxR).1) hB (fun t ht x hx ↦ ?_) hu hα0 hα1
  rw [hfd t ht hx]
  exact hB₁ t ht x hx

end IsSolutionOn

end HalfPlane

end Boussinesq

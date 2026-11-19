/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BoundaryRegularity
import PDE.Elliptic.Classical.Harmonic.BoundaryUniquenessAtInfinity
import PDE.Elliptic.PotentialTheory.FundamentalSolution.Pole
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.ExteriorPotential
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.Linearity
import PDE.Elliptic.Regularity.Interior.Weyl
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Regularity

/-!
# Green representation of compact `C²` functions with zero boundary values

A compactly supported `C²` function `u` on the plane that vanishes on the boundary line
`{y₁ = 0}` is the half-plane Green potential of `-Δu` on the closed upper half-plane:
`G[-Δu] = u`. The source `-Δu` is only continuous and the odd reflection of `u` is only `C¹`,
so neither the local Poisson equation for the potential nor the whole-plane identity for odd
`C²` functions applies directly.

The proof shows that `w = G[Δu] + u` is a distributional solution of Laplace's equation on the
open upper half-plane. Against a test function `ψ` supported there, `∫ u Δψ = ∫ Δu ψ` by two
integrations by parts, and `∫ G[f] Δψ = -∫ f ψ` for every continuous compact source `f`: the
potential is the logarithmic convolution with the odd extension of `f`, Fubini moves the
Laplacian onto the kernel, and `∫ Φ(x - y) Δψ(x) dx = -ψ(y)`. Weyl's lemma gives a harmonic
representative, which agrees with the continuous function `w` on the open half-plane. Since `w`
vanishes on the boundary and at infinity, the maximum principle gives `w = 0`.

## Main results

* `PotentialTheory.integral_convolution_fundamentalSolution_mul_laplacian`:
  `∫ (Φ * F) Δψ = -∫ F ψ` for integrable compactly supported `F` and compact `C²` `ψ`.
* `integral_halfSpaceGreenPotential_mul_laplacian`: `∫ G[f] Δψ = -∫ f ψ` for continuous compact
  `f` and compact `C²` `ψ` supported in the open upper half-plane.
* `eqOn_halfSpaceGreenPotential_neg_laplacian`: `G[-Δu] = u` on the closed upper half-plane.
* `halfSpaceGreenPotential_laplacian_eqOn_neg`: `G[Δu] = -u` on the closed upper half-plane.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace
open PDE (laplacian)
open scoped Convolution Distributions

namespace PotentialTheory

/-- Moving the Laplacian onto the logarithmic kernel: for an integrable compactly supported
density `F` and a compactly supported `C²` function `ψ`, `∫ (Φ * F) Δψ = -∫ F ψ`. -/
theorem integral_convolution_fundamentalSolution_mul_laplacian {F ψ : ℝ^2 → ℝ}
    (hF : Integrable F) (hFc : HasCompactSupport F) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] F) x * laplacian ψ x =
      -∫ y, F y * ψ y := by
  obtain ⟨A, hA⟩ := hFc.isCompact.isBounded.exists_norm_le
  obtain ⟨B, hB⟩ := hψc.isCompact.isBounded.exists_norm_le
  set K : ℝ^2 → ℝ := (Metric.closedBall (0 : ℝ^2) (A + B)).indicator (fundamentalSolution 2)
  have hK : Integrable K :=
    ((locallyIntegrable_fundamentalSolution 2).integrableOn_isCompact
      (isCompact_closedBall 0 (A + B))).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
  have hΔ : Continuous (laplacian ψ) :=
    (hψ.coordinate_laplacian (k := 0) (by norm_num)).continuous
  obtain ⟨C, hC⟩ := hΔ.bounded_above_of_compact_support hψc.coordinate_laplacian
  have hI : Integrable (fun p : ℝ^2 × ℝ^2 ↦ F p.2 * K (p.1 - p.2)) (volume.prod volume) := by
    simpa using hF.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hK
  have hI2 : Integrable (fun p : ℝ^2 × ℝ^2 ↦ laplacian ψ p.1 * (F p.2 * K (p.1 - p.2)))
      (volume.prod volume) :=
    hI.bdd_mul (c := C) (hΔ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ hC p.1)
  have hpt (x y : ℝ^2) : fundamentalSolution 2 (x - y) * F y * laplacian ψ x =
      laplacian ψ x * (F y * K (x - y)) := by
    by_cases hy : F y = 0
    · simp [hy]
    by_cases hx : laplacian ψ x = 0
    · simp [hx]
    have hyA : ‖y‖ ≤ A := hA y (subset_tsupport F hy)
    have hxB : ‖x‖ ≤ B := by
      by_contra hxB
      exact hx (EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport
        (fun hmem ↦ hxB (hB x hmem)))
    have hmem : x - y ∈ Metric.closedBall (0 : ℝ^2) (A + B) :=
      mem_closedBall_zero_iff.2 ((norm_sub_le x y).trans (by linarith))
    simp only [K, indicator_of_mem hmem]
    ring
  have hI3 : Integrable (Function.uncurry fun x y : ℝ^2 ↦
      fundamentalSolution 2 (x - y) * F y * laplacian ψ x) (volume.prod volume) :=
    hI2.congr (Eventually.of_forall fun p ↦ (hpt p.1 p.2).symm)
  have hconv (x : ℝ^2) : (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] F) x *
      laplacian ψ x = ∫ y, fundamentalSolution 2 (x - y) * F y * laplacian ψ x := by
    rw [convolution_eq_swap, ← integral_mul_const]
    rfl
  simp_rw [hconv]
  rw [integral_integral_swap hI3, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp_rw [mul_right_comm _ (F y), integral_mul_const,
    integral_fundamentalSolution_sub_mul_laplacian (by norm_num) hψ hψc y]
  ring

end PotentialTheory

namespace GreenFunction

/-- The half-plane Green potential is a distributional inverse of `-Δ` on the open upper
half-plane: for a continuous compact source `f` and a compactly supported `C²` function `ψ`
whose support lies in the open upper half-plane, `∫ G[f] Δψ = -∫ f ψ`. -/
theorem integral_halfSpaceGreenPotential_mul_laplacian {f ψ : ℝ^2 → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) (hψH : tsupport ψ ⊆ HalfSpace.upper 2) :
    ∫ x, halfSpaceGreenPotential f x * laplacian ψ x = -∫ y, f y * ψ y := by
  rw [halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension hf hc,
    PotentialTheory.integral_convolution_fundamentalSolution_mul_laplacian
      (integrable_oddHalfSpaceExtension hf hc) (hasCompactSupport_oddHalfSpaceExtension hc)
      hψ hψc]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ HalfSpace.upper 2
  · simp only [oddHalfSpaceExtension_eqOn f hy]
  · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψH h)
    simp [hψy]

/-- **Green representation with zero boundary values.** A compactly supported `C²` function on
the plane that vanishes on the boundary line satisfies `G[Δu] = -u` on the closed upper
half-plane. -/
theorem halfSpaceGreenPotential_laplacian_eqOn_neg {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hb : ∀ x ∈ HalfSpace.boundary 2, u x = 0) :
    EqOn (halfSpaceGreenPotential (laplacian u)) (fun x ↦ -u x)
      (closure (HalfSpace.upper 2)) := by
  intro x hx
  set f : ℝ^2 → ℝ := laplacian u
  have hf : Continuous f := (hu.coordinate_laplacian (k := 0) (by norm_num)).continuous
  have hfc : HasCompactSupport f := hc.coordinate_laplacian
  set w : ℝ^2 → ℝ := fun y ↦ halfSpaceGreenPotential f y + u y
  have hw : Continuous w := (continuous_halfSpaceGreenPotential hf hfc).add hu.continuous
  let Ω : TopologicalSpace.Opens (ℝ^2) := ⟨HalfSpace.upper 2, HalfSpace.isOpen_upper 2⟩
  have hweak : ∀ φ : 𝓓(Ω, ℝ), (∫ y, w y * laplacian (φ : ℝ^2 → ℝ) y) = 0 := by
    intro φ
    have hφ : ContDiff ℝ 2 (φ : ℝ^2 → ℝ) := φ.contDiff.of_le (by simp)
    have hΔφ : Continuous (laplacian (φ : ℝ^2 → ℝ)) :=
      (hφ.coordinate_laplacian (k := 0) (by norm_num)).continuous
    have hΔφc : HasCompactSupport (laplacian (φ : ℝ^2 → ℝ)) :=
      φ.hasCompactSupport.coordinate_laplacian
    have hG : Integrable fun y ↦ halfSpaceGreenPotential f y * laplacian (φ : ℝ^2 → ℝ) y :=
      ((continuous_halfSpaceGreenPotential hf hfc).mul hΔφ).integrable_of_hasCompactSupport
        hΔφc.mul_left
    have hU : Integrable fun y ↦ u y * laplacian (φ : ℝ^2 → ℝ) y :=
      (hu.continuous.mul hΔφ).integrable_of_hasCompactSupport hΔφc.mul_left
    have hsplit : (∫ y, w y * laplacian (φ : ℝ^2 → ℝ) y) =
        (∫ y, halfSpaceGreenPotential f y * laplacian (φ : ℝ^2 → ℝ) y) +
          ∫ y, u y * laplacian (φ : ℝ^2 → ℝ) y := by
      simp only [w, add_mul]
      exact integral_add hG hU
    have hgreen := integral_halfSpaceGreenPotential_mul_laplacian hf hfc hφ φ.hasCompactSupport
      φ.tsupport_subset
    have hu' : (∫ y, u y * laplacian (φ : ℝ^2 → ℝ) y) = ∫ y, f y * φ y :=
      (integral_congr_ae (.of_forall fun y ↦ mul_comm _ _)).trans
        ((PDE.DistributionTheory.integral_mul_laplacian_eq u hφ hu φ.hasCompactSupport).symm.trans
          (integral_congr_ae (.of_forall fun y ↦ mul_comm _ _)))
    rw [hsplit, hgreen, hu']
    ring
  obtain ⟨h, hh, hae⟩ := LaplacianEquation.exists_isHarmonicPDE_ae_eq_of_integral_laplacian_eq_zero
    (Ω := Ω) (hw.locallyIntegrable.locallyIntegrableOn _) hweak
  have heq : EqOn w h (HalfSpace.upper 2) :=
    Measure.eqOn_open_of_ae_eq hae (HalfSpace.isOpen_upper 2) hw.continuousOn
      hh.contDiffOn.continuousOn
  have hharm : LaplacianEquation.IsHarmonicPDE 2 w (HalfSpace.upper 2) := by
    refine ⟨hh.contDiffOn.congr fun y hy ↦ heq hy, fun y hy ↦ ?_⟩
    have hloc : w =ᶠ[𝓝 y] h :=
      heq.eventuallyEq_of_mem ((HalfSpace.isOpen_upper 2).mem_nhds hy)
    rw [EuclideanLaplacian.laplacian_congr_nhds hloc]
    exact hh.laplacian_eq_zero hy
  have hzero := hharm.eq_zero_on_closure_of_boundary_zero_of_tendsto_zero
    (HalfSpace.isOpen_upper 2) hw.continuousOn
    (fun y hy ↦ by
      rw [HalfSpace.frontier_upper] at hy
      simp only [w, halfSpaceGreenPotential_boundary _ hy, hb y hy, add_zero])
    (by simpa only [add_zero] using
      (tendsto_halfSpaceGreenPotential_cocompact hf hfc).add hc.is_zero_at_infty) x hx
  simp only [w] at hzero
  linarith

/-- **Green representation with zero boundary values.** A compactly supported `C²` function on
the plane that vanishes on the boundary line is the half-plane Green potential of `-Δu` on the
closed upper half-plane: `G[-Δu] = u`. Only continuity of `Δu` is used; the odd reflection of
`u` need not be `C²`. -/
theorem eqOn_halfSpaceGreenPotential_neg_laplacian {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hb : ∀ x ∈ HalfSpace.boundary 2, u x = 0) :
    EqOn (halfSpaceGreenPotential fun y ↦ -laplacian u y) u (closure (HalfSpace.upper 2)) := by
  intro x hx
  rw [halfSpaceGreenPotential_neg, halfSpaceGreenPotential_laplacian_eqOn_neg hu hc hb hx,
    neg_neg]

end GreenFunction

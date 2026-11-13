/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
public import PDE.Elliptic.Classical.Harmonic.IteratedDerivativeEstimates
import PDE.Elliptic.Classical.Poisson.PlanarFundamentalSolution

/-!
# Green potentials of sources vanishing on a disc centred on the boundary

The half-space Green potential is odd under the reflection in the boundary hyperplane. In the
plane, the potential `G[Z]` of a continuous compactly supported source `Z` is the Newtonian
potential of the odd extension of `Z`, so it is harmonic on every open set where that extension
vanishes. If `Z` vanishes on the upper half of the disc `B(0, ρ)` centred on the boundary line, its
odd extension vanishes on the whole disc, and `G[Z]` is harmonic on `B(0, ρ)`. By the interior
estimates of harmonic functions and the oddness, every derivative of `G[Z]` at a point at distance
`k r` from the rim is bounded by `2ᵏ M / rᵏ`, where `M` bounds `|G[Z]|` on the upper half of the
disc.

This is how the commutator term of a localized elliptic equation, supported in an annulus, is
controlled inside the annulus by the size of the potential alone, without its source.

## Main results

* `halfSpaceGreenPotential_reflect`: the Green potential is odd under the reflection in the
  boundary hyperplane.
* `isHarmonicPDE_halfSpaceGreenPotential_of_eqOn_zero`: the Green potential is harmonic on every
  open set where the odd extension of the source vanishes.
* `isHarmonicPDE_halfSpaceGreenPotential_of_eq_zero`: if `Z` vanishes on the upper half of
  `B(0, ρ)`, then `G[Z]` is harmonic on `B(0, ρ)`.
* `norm_iteratedFDeriv_halfSpaceGreenPotential_le_of_eq_zero`: under the same hypothesis and
  `|G[Z]| ≤ M` on the upper half of the disc, the `k`-th derivative at every `x` with
  `B̄(x, k r) ⊆ B(0, ρ)` is at most `2ᵏ M / rᵏ`.
* `contDiffOn_halfSpaceGreenPotential_of_eq_zero`: under the same hypothesis `G[Z]` is smooth on
  `B(0, ρ)`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory SobolevSpace
open scoped Topology Convolution

set_option linter.missingDocs true

namespace GreenFunction

/-- The Green function is odd in its field point under the reflection in the boundary. -/
theorem halfSpaceGreenFunction_reflect_right {n : ℕ} [Fact (0 < n)] (x y : ℝ^n) :
    halfSpaceGreenFunction (n := n) y (HalfSpace.reflect n x) =
      -halfSpaceGreenFunction (n := n) y x := by
  have h1 : ‖HalfSpace.reflect n x - y‖ = ‖x - HalfSpace.reflect n y‖ := by
    calc ‖HalfSpace.reflect n x - y‖ = ‖HalfSpace.reflect n (HalfSpace.reflect n x - y)‖ :=
          (HalfSpace.norm_reflect n _).symm
      _ = ‖x - HalfSpace.reflect n y‖ := by
          rw [HalfSpace.reflect_sub n, HalfSpace.reflect_involutive n]
  have h2 : ‖HalfSpace.reflect n x - HalfSpace.reflect n y‖ = ‖x - y‖ := by
    rw [← HalfSpace.reflect_sub n, HalfSpace.norm_reflect n]
  simp only [halfSpaceGreenFunction]
  rw [PotentialTheory.fundamentalSolution_eq_of_norm_eq h1,
    PotentialTheory.fundamentalSolution_eq_of_norm_eq h2]
  ring

/-- **The Green potential is odd** under the reflection in the boundary hyperplane. -/
theorem halfSpaceGreenPotential_reflect {n : ℕ} [Fact (0 < n)] (f : ℝ^n → ℝ) (x : ℝ^n) :
    halfSpaceGreenPotential f (HalfSpace.reflect n x) = -halfSpaceGreenPotential f x := by
  unfold halfSpaceGreenPotential
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  change halfSpaceGreenFunction y (HalfSpace.reflect n x) * f y =
    -(halfSpaceGreenFunction y x * f y)
  rw [halfSpaceGreenFunction_reflect_right, neg_mul]

/-- If `Z` vanishes on the upper half of the disc `B(0, ρ)`, its odd extension vanishes on the
whole disc. -/
theorem oddHalfSpaceExtension_eq_zero_of_eq_zero {Z : ℝ^2 → ℝ} {ρ : ℝ}
    (h0 : ∀ y ∈ HalfSpace.upper 2, ‖y‖ < ρ → Z y = 0) {y : ℝ^2} (hy : ‖y‖ < ρ) :
    oddHalfSpaceExtension Z y = 0 := by
  unfold oddHalfSpaceExtension
  by_cases hyu : y ∈ HalfSpace.upper 2
  · have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
      have h1 : 0 < y (PDE.Common.lastIndex (n := 2)) := hyu
      have h2 : y (PDE.Common.lastIndex (n := 2)) < 0 := h
      linarith
    simp [hyu, hyl, h0 y hyu hy]
  · by_cases hyl : y ∈ HalfSpace.lower 2
    · have hr : HalfSpace.reflect 2 y ∈ HalfSpace.upper 2 :=
        (HalfSpace.mem_upper_reflect_iff (n := 2) y).2 hyl
      have hn : ‖HalfSpace.reflect 2 y‖ < ρ := by rwa [HalfSpace.norm_reflect 2]
      simp [hyu, hyl, h0 _ hr hn]
    · simp [hyu, hyl]

/-- On an open set where the odd extension of a continuous compactly supported source vanishes,
the half-space Green potential is harmonic. -/
theorem isHarmonicPDE_halfSpaceGreenPotential_of_eqOn_zero {Z : ℝ^2 → ℝ} (hZ : Continuous Z)
    (hc : HasCompactSupport Z) {U : Set (ℝ^2)} (hU : IsOpen U)
    (h0 : ∀ y ∈ U, oddHalfSpaceExtension Z y = 0) :
    LaplacianEquation.IsHarmonicPDE 2 (halfSpaceGreenPotential Z) U := by
  set F := oddHalfSpaceExtension Z with hFdef
  have hF : LocallyIntegrable F volume := locallyIntegrable_oddHalfSpaceExtension hZ
  have hFc : HasCompactSupport F := hasCompactSupport_oddHalfSpaceExtension hc
  have hpot : halfSpaceGreenPotential Z =
      PotentialTheory.fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] F := by
    funext z
    calc halfSpaceGreenPotential Z z = halfSpaceGreenPotential F z := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
          rw [show F y = Z y from oddHalfSpaceExtension_eqOn Z hy]
      _ = _ := halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable F
          (oddHalfSpaceExtension_reflect Z) z
          (integrable_fundamentalSolution_mul_oddHalfSpaceExtension hZ hc z)
  have hloc : ∀ z ∈ U, ContDiffAt ℝ 2 (halfSpaceGreenPotential Z) z ∧
      -PDE.laplacian (halfSpaceGreenPotential Z) z = 0 := by
    intro z hz
    have hev : F =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact h0 y hy
    have hlocal : ContDiffAt ℝ 2 F z := contDiffAt_const.congr_of_eventuallyEq hev
    obtain ⟨hreg, hpoisson⟩ :=
      PoissonEquation.fundamentalSolution_convolution_local_poisson hF hFc hlocal
    rw [hpot]
    refine ⟨hreg, ?_⟩
    rw [hpoisson, hev.eq_of_nhds]
  refine ⟨fun z hz ↦ (hloc z hz).1.contDiffWithinAt, fun z hz ↦ ?_⟩
  have := (hloc z hz).2
  linarith

/-- On an open set where the odd extension of a continuous compactly supported source vanishes,
the half-space Green potential is smooth. -/
theorem contDiffOn_halfSpaceGreenPotential_of_eqOn_zero {Z : ℝ^2 → ℝ} (hZ : Continuous Z)
    (hc : HasCompactSupport Z) {U : Set (ℝ^2)} (hU : IsOpen U)
    (h0 : ∀ y ∈ U, oddHalfSpaceExtension Z y = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (halfSpaceGreenPotential Z) U :=
  (isHarmonicPDE_halfSpaceGreenPotential_of_eqOn_zero hZ hc hU h0).contDiffOn_of_isOpen hU

/-- **Harmonicity of the Green potential of a source vanishing on a disc centred on the
boundary.** If `Z` is continuous with compact support and vanishes on the upper half of
`B(0, ρ)`, then `G[Z]` is harmonic on `B(0, ρ)`. -/
theorem isHarmonicPDE_halfSpaceGreenPotential_of_eq_zero {Z : ℝ^2 → ℝ} (hZ : Continuous Z)
    (hc : HasCompactSupport Z) {ρ : ℝ} (h0 : ∀ y ∈ HalfSpace.upper 2, ‖y‖ < ρ → Z y = 0) :
    LaplacianEquation.IsHarmonicPDE 2 (halfSpaceGreenPotential Z) (Metric.ball 0 ρ) :=
  isHarmonicPDE_halfSpaceGreenPotential_of_eqOn_zero hZ hc Metric.isOpen_ball fun _ hy ↦
    oddHalfSpaceExtension_eq_zero_of_eq_zero h0 (by simpa using hy)

/-- **Interior bounds of the harmonic part.** If `Z` is continuous with compact support and
vanishes on the upper half of `B(0, ρ)`, and `|G[Z]| ≤ M` on the closed upper half of the disc,
then at every point `x` with `B̄(x, k r) ⊆ B(0, ρ)` the `k`-th derivative of `G[Z]` is at most
`2ᵏ M / rᵏ`. -/
theorem norm_iteratedFDeriv_halfSpaceGreenPotential_le_of_eq_zero {Z : ℝ^2 → ℝ}
    (hZ : Continuous Z) (hc : HasCompactSupport Z) {ρ : ℝ}
    (h0 : ∀ y ∈ HalfSpace.upper 2, ‖y‖ < ρ → Z y = 0) {M : ℝ}
    (hM : ∀ y : ℝ^2, 0 ≤ y 1 → ‖y‖ < ρ → |halfSpaceGreenPotential Z y| ≤ M)
    (k : ℕ) {x : ℝ^2} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x ((k : ℝ) * r) ⊆ Metric.ball 0 ρ) :
    ‖iteratedFDeriv ℝ k (halfSpaceGreenPotential Z) x‖ ≤ 2 ^ k * M / r ^ k := by
  have hharm := isHarmonicPDE_halfSpaceGreenPotential_of_eq_zero hZ hc h0
  have hM' : ∀ y ∈ Metric.closedBall x ((k : ℝ) * r), |halfSpaceGreenPotential Z y| ≤ M := by
    intro y hy
    have hyρ : ‖y‖ < ρ := by simpa using hball hy
    by_cases hy1 : 0 ≤ y 1
    · exact hM y hy1 hyρ
    · have hR : 0 ≤ (HalfSpace.reflect 2 y) 1 := by
        have : (HalfSpace.reflect 2 y) (PDE.Common.lastIndex (n := 2)) =
            -y (PDE.Common.lastIndex (n := 2)) := HalfSpace.reflect_apply_last 2 y
        change 0 ≤ (HalfSpace.reflect 2 y) (PDE.Common.lastIndex (n := 2))
        rw [this]
        change 0 ≤ -y 1
        linarith
      have h := hM _ hR (by rwa [HalfSpace.norm_reflect 2])
      rwa [halfSpaceGreenPotential_reflect, abs_neg] at h
  simpa using hharm.norm_iteratedFDeriv_le Metric.isOpen_ball hr hball hM'

/-- The Green potential of a source vanishing on the upper half of `B(0, ρ)` is smooth on
`B(0, ρ)`. -/
theorem contDiffOn_halfSpaceGreenPotential_of_eq_zero {Z : ℝ^2 → ℝ} (hZ : Continuous Z)
    (hc : HasCompactSupport Z) {ρ : ℝ} (h0 : ∀ y ∈ HalfSpace.upper 2, ‖y‖ < ρ → Z y = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (halfSpaceGreenPotential Z) (Metric.ball 0 ρ) :=
  contDiffOn_halfSpaceGreenPotential_of_eqOn_zero hZ hc Metric.isOpen_ball fun _ hy ↦
    oddHalfSpaceExtension_eq_zero_of_eq_zero h0 (by simpa using hy)

end GreenFunction

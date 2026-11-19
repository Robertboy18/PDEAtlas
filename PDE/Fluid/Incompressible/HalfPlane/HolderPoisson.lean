/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityHigherOrder

/-!
# Green potentials of Hölder sources

Let `f` be continuous with compact support and `α`-Hölder on the closed upper half-plane. Its
half-plane Green potential `φ` is `C²` within the closed upper half-plane for `0 < α < 1`
(`contDiffOn_halfSpaceGreenPotential_of_holder`) and solves `-Δφ = f` in the open upper
half-plane for `0 < α ≤ 1` (`neg_laplacian_halfSpaceGreenPotential_of_holder`), by the Hölder
theory of the half-plane velocity `∇^⊥φ`.

## Main results

* `contDiffOn_halfSpaceGreenPotential_of_holder`: for `0 < α < 1` the Green potential is `C²`
  within the closed upper half-plane.
* `neg_laplacian_halfSpaceGreenPotential_of_holder`: for `0 < α ≤ 1`, `-Δφ = f` in the open upper
  half-plane.
-/

@[expose] public section

noncomputable section

open Set Filter GreenFunction SobolevSpace
open scoped Topology

namespace IncompressibleFlow

set_option linter.missingDocs true

variable {f : ℝ^2 → ℝ} {α M : ℝ}

/-- **Regularity.** The half-plane Green potential of a continuous compactly supported source,
`α`-Hölder on the closed upper half-plane with `0 < α < 1`, is `C²` within the closed upper
half-plane. -/
theorem contDiffOn_halfSpaceGreenPotential_of_holder (hf : Continuous f)
    (hc : HasCompactSupport f) (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) :
    ContDiffOn ℝ 2 (halfSpaceGreenPotential f) {y : ℝ^2 | 0 ≤ y 1} := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hR : ∀ y : ℝ^2, 0 ≤ y 1 → r < ‖y‖ → f y = 0 := fun y _ hy ↦ by
    by_contra h
    have := hr (subset_tsupport _ h)
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hM' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 0 f {y | 0 ≤ y 1} y - iteratedFDerivWithin ℝ 0 f {y | 0 ≤ y 1} z‖ ≤
        M * ‖y - z‖ ^ α := by
    intro y z hy hz
    rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hM y z hy hz
  simpa using contDiffOn_succ_succ_halfSpaceGreenPotential (k := 0) hα hα1
    (contDiffOn_zero.mpr hf.continuousOn) hR hM'

/-- **The Poisson equation.** The half-plane Green potential of a continuous compactly supported
source, `α`-Hölder on the closed upper half-plane with `0 < α ≤ 1`, solves `-Δφ = f` in the open
upper half-plane. -/
theorem neg_laplacian_halfSpaceGreenPotential_of_holder (hf : Continuous f)
    (hc : HasCompactSupport f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) {x : ℝ^2}
    (hx : 0 < x 1) : -PDE.laplacian (halfSpaceGreenPotential f) x = f x := by
  have hxU : x ∈ HalfSpace.upper 2 := hx
  obtain ⟨-, hcurl⟩ := partialDeriv_halfPlaneVelocity_div_curl hf hc hα hα1 hM hxU
  rw [halfPlaneVelocity_zero, halfPlaneVelocity_one, PDE.partialDeriv_neg] at hcurl
  simp only [PDE.laplacian, Fin.sum_univ_two]
  change -((∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x +
      (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))) x) = f x
  linarith

end IncompressibleFlow

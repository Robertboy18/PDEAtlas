/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Operators
public import PDE.Spaces.Sobolev.Boundary.Flux.MixedGreen
public import PDE.Spaces.Sobolev.Boundary.Flux.GreenIdentity

/-!
# Agreement of the weak and classical normal derivatives

For classical closure data, the weak normal functional is integration against the outward normal
derivative. By `weakNormalTraceOfH2_traceClass` the weak functional at the trace of `g` is
`⟨Δf, g⟩ + ⟨∇f, ∇g⟩`. Once the weak Laplacian and gradients are replaced by their classical
representatives, the statement is Green's first identity
`Boundary.Flux.green_first_identity_of_contDiffUpToBoundary` (Evans App. C.2, Theorem 3(ii), stated
there for C² functions) with `u = g` and `v = f`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 3(ii), p. 712.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary.Geometry.SurfaceMeasure
open scoped Gradient

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Let `Ω` have a C¹ graph boundary. If `ContDiffUpToBoundary 2 f Ω`,
`ContDiffUpToBoundary 1 g Ω` and `g` is continuous on `closure Ω`, then `weakNormalTraceOfH2 f`
at the trace class of `g` is `∫_{∂Ω} g ∂f/∂ν dS`, where `∂f/∂ν` is the normal flux of the
completed gradient of `f`. -/
theorem weakNormalTraceOfH2_toWkpSpaceOn_traceClass
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {f g : ℝ^(m + 1) → ℝ}
    (hf : ContDiffUpToBoundary 2 f Ω)
    (hg : ContDiffUpToBoundary 1 g Ω)
    (hgc : ContinuousOn g (closure Ω)) :
    weakNormalTraceOfH2 (hf.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)
        (traceClass (hg.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) =
      ∫ x, g x * normalFlux (Ω := Ω)
        (hf.of_le (show 1 ≤ 2 by omega)).completedGradient x ∂surfaceMeasure Ω := by
  let hf₁ := hf.of_le (show 1 ≤ 2 by omega)
  have hvol :
      inner ℝ (wkpLaplacianCLM (hf.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2))
          (wkpBaseCoordinateCLM (hg.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) =
        ∫ x in Ω, g x * PDE.laplacian f x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coordinate_laplacian_toWkpSpaceOn_ae hΩ.isOpen hΩ.bounded 2,
      hg.toWkpSpaceOn_base_ae hΩ.isOpen hΩ.bounded 2] with x hx hy
    simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  have hgrad :
      inner ℝ (wkpGradientCLM (hf₁.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2))
          (wkpGradientCLM (hg.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)) =
        ∫ x in Ω, inner ℝ (∇ g x) (∇ f x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf₁.gradient_toWkpSpaceOn_ae hΩ.isOpen hΩ.bounded 2,
      hg.gradient_toWkpSpaceOn_ae hΩ.isOpen hΩ.bounded 2] with x hx hy
    rw [hx, hy, real_inner_comm]
  rw [weakNormalTraceOfH2_traceClass,
    hf.lowerOrder_toWkpSpaceOn hΩ.isOpen hΩ.bounded 2 (show 1 ≤ 2 by omega),
    hvol, hgrad]
  exact (Boundary.Flux.green_first_identity_of_contDiffUpToBoundary
    hgraph hg hgc hf).2.2.2

end SobolevSpace.Trace.C1

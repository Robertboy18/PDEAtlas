/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AveragedDivergence
public import PDE.Hyperbolic.HamiltonJacobi.Weak.ForwardExtension
public import PDE.Hyperbolic.HamiltonJacobi.Weak.Mollification

/-!
# The divergence bound for the mollified Hamilton–Jacobi drift

In the proof of Theorem 7 in Evans, §3.3.3(b), the regularized drift (44) averages `DH`
between the two mollified spatial gradients, and its divergence is bounded above by
`C (1 + 1/s)` (46). We prove the bound `C₁ (1 + 1/t)` with one constant for all mollifiers.
Divergence is the basis-independent trace of the spatial derivative.

Both ingredients are derived: spacetime convolution gives the gradient norm and
upper Hessian bounds, while convexity makes the Hamiltonian Hessian positive.
Compactness bounds its trace on the gradient ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, equations (41)-(46).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory
open scoped Convolution RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- Evans's regularized drift (44): the segment average of `DH` at the
spatial gradients of the two spacetime convolutions. The inputs are held fixed
at their initial values for negative times. -/
def mollifiedDrift (H : E → ℝ) (φ : ContDiffBump (0 : E × ℝ))
    (u v : E × ℝ → ℝ) (z : E × ℝ) : E :=
  ∫ r in (0 : ℝ)..1, ∇ H
    (r • ∇ (fun y : E ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension u) (y, z.2)) z.1 +
      (1 - r) • ∇ (fun y : E ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension v) (y, z.2)) z.1)

/-- Evans's divergence estimate (46), with one constant for every normalized
spacetime bump and all times beyond twice its radius. The two inputs may have
different Lipschitz constants and may be unbounded. -/
theorem exists_trace_fderiv_mollifiedDrift_le {H : E → ℝ} (hH : ContDiff ℝ 2 H)
    (hconv : ConvexOn ℝ Set.univ H) {u v : E × ℝ → ℝ} {Ku Kv : NNReal}
    (hu_lip : LipschitzOnWith Ku u {w | 0 ≤ w.2}) (hv_lip : LipschitzOnWith Kv v {w | 0 ≤ w.2})
    {C : ℝ} (hC : 0 ≤ C)
    (hu_semi : ∀ x z t, 0 < t → u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤
      C * (1 + t⁻¹) * ‖z‖ ^ 2)
    (hv_semi : ∀ x z t, 0 < t → v (x + z, t) - 2 * v (x, t) + v (x - z, t) ≤
      C * (1 + t⁻¹) * ‖z‖ ^ 2) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (φ : ContDiffBump (0 : E × ℝ)) (t : ℝ), 2 * φ.rOut < t → ∀ x : E,
      LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ mollifiedDrift (μ := μ) H φ u v (y, t))
      x).toLinearMap ≤ C₁ * (1 + t⁻¹) := by
  obtain ⟨M, hM, hHM⟩ :=
    PDE.Analysis.exists_trace_hessian_bound_closedBall hH (max (Ku : ℝ) (Kv : ℝ))
  have hu := lipschitzWith_forwardExtension hu_lip
  have hv := lipschitzWith_forwardExtension hv_lip
  have hsemi (w : E × ℝ → ℝ) (hw : ∀ x z t, 0 < t →
        w (x + z, t) - 2 * w (x, t) + w (x - z, t) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2)
      (x z : E) (t : ℝ) (ht : 0 < t) :
      forwardExtension w (x + z, t) - 2 * forwardExtension w (x, t) +
        forwardExtension w (x - z, t) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2 := by
    simpa only [forwardExtension, max_eq_left ht.le] using hw x z t ht
  refine ⟨2 * C * M, by positivity, fun φ t ht x ↦ ?_⟩
  have htpos : 0 < t := lt_trans (mul_pos two_pos φ.rOut_pos) ht
  have htr : φ.rOut < t := by have := φ.rOut_pos; linarith
  have hsmooth (w : E × ℝ → ℝ) (hw : Continuous w) : ContDiff ℝ 2 (fun y : E ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w) (y, t)) :=
    (φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hw.locallyIntegrable).comp
        (contDiff_id.prodMk contDiff_const)
  have hbound (w : E × ℝ → ℝ) (hw : Continuous w) (hw_semi : ∀ x z t, 0 < t →
        w (x + z, t) - 2 * w (x, t) + w (x - z, t) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2) (a : E) :
      ⟪a, fderiv ℝ (∇ (fun y : E ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w) (y, t))) x a⟫ ≤
          (2 * C * (1 + t⁻¹)) * ‖a‖ ^ 2 := by
    rw [real_inner_comm, PDE.Analysis.inner_fderiv_gradient (hsmooth w hw)]
    exact hessian_convolution_spatial_le φ hw hw_semi ht x a
  have h := PDE.Analysis.trace_fderiv_averaged_gradient_le hH hconv
    (PDE.Analysis.contDiff_gradient (n := 1) (hsmooth (forwardExtension u) hu.continuous))
    (PDE.Analysis.contDiff_gradient (n := 1) (hsmooth (forwardExtension v) hv.continuous))
    (show 0 ≤ 2 * C * (1 + t⁻¹) by positivity)
    ((norm_gradient_convolution_spatial_le φ hu.continuous hu.lipschitzOnWith htr x (μ := μ)).trans
      (le_max_left (Ku : ℝ) (Kv : ℝ)))
    ((norm_gradient_convolution_spatial_le φ hv.continuous hv.lipschitzOnWith htr x (μ := μ)).trans
      (le_max_right (Ku : ℝ) (Kv : ℝ)))
    (hbound (forwardExtension u) hu.continuous (hsemi u hu_semi))
    (hbound (forwardExtension v) hv.continuous (hsemi v hv_semi)) hHM
  exact h.trans_eq (mul_right_comm (2 * C) (1 + t⁻¹) M)

end HamiltonJacobi.Weak

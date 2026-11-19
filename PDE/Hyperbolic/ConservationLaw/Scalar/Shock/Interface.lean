/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegrationByParts.Epigraph
public import PDE.Common.Euclidean.SpaceTime.Scalar
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff

/-!
# Integration across a moving scalar shock

The interface `x = s(t)` is a C¹ graph. Integration of a compactly supported
directional derivative on its right leaves the conormal factor
`s'(t) v₀ - v₁`. The shared epigraph theorem proves this identity by a
measure-preserving graph shear and the fundamental theorem of calculus.

These coordinates and trace integrability results support the weak jump
calculation (8)-(9) for varying classical fields in Evans, §3.4.1(a).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1(a), equations (8)-(9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Shock

/-- The time parametrization of the moving interface. -/
def interface (s : ℝ → ℝ) (t : ℝ) : ℝ^2 := !₂[t, s t]

/-- The open region strictly to the right of the interface. -/
def rightRegion (s : ℝ → ℝ) : Set ℝ^2 := {p | s (p 0) < p 1}

/-- A continuous shock curve has an open right-hand region. -/
theorem isOpen_rightRegion {s : ℝ → ℝ} (hs : Continuous s) :
    IsOpen (rightRegion s) :=
  isOpen_lt (hs.comp (EuclideanSpace.proj 0).continuous) (EuclideanSpace.proj 1).continuous

/-- The graph parametrization is continuous whenever the shock position is. -/
theorem continuous_interface {s : ℝ → ℝ} (hs : Continuous s) :
    Continuous (interface s) := by
  change Continuous (fun t ↦ WithLp.toLp 2 ![t, s t])
  fun_prop

/-- A compactly supported spacetime function has compactly supported trace.
The time coordinate controls its support even when the shock position is unbounded. -/
theorem hasCompactSupport_interface_comp {f : ℝ^2 → ℝ} (hf : HasCompactSupport f) (s : ℝ → ℝ) :
    HasCompactSupport (fun t ↦ f (interface s t)) := by
  refine HasCompactSupport.intro (hf.image (EuclideanSpace.proj 0).continuous) ?_
  intro t ht
  exact image_eq_zero_of_notMem_tsupport fun hmem ↦ ht ⟨interface s t, hmem, by simp [interface]⟩

/-- A continuous interface density multiplied by a compact test trace is integrable. -/
theorem integrable_mul_interface_comp {s c : ℝ → ℝ} (hs : Continuous s) (hc : Continuous c)
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hcompact : HasCompactSupport f) :
    Integrable (fun t ↦ c t * f (interface s t)) :=
  (hc.mul (hf.comp (continuous_interface hs))).integrable_of_hasCompactSupport
    (hasCompactSupport_interface_comp hcompact s).mul_left

private def pairEquiv : (ℝ × ℝ) ≃L[ℝ] ℝ^2 :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans scalarSpaceTimeEquiv.symm

private theorem pairEquiv_apply (p : ℝ × ℝ) :
    pairEquiv p = !₂[p.1, p.2] := by
  simp [pairEquiv]

private theorem measurePreserving_pairEquiv :
    MeasurePreserving pairEquiv volume volume := by
  have heq : (pairEquiv : (ℝ × ℝ) → ℝ^2) = spaceTimePair := by
    funext p
    rw [pairEquiv_apply, spaceTimePair_apply]
  rw [heq]
  exact measurePreserving_spaceTimePair

/-- The directional Gauss–Green identity to the right of a C¹ moving interface.
The conormal is `(s'(t), -1)` with respect to the time parametrization. -/
theorem integral_rightRegion_fderiv {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s) {f : ℝ^2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) (v : ℝ^2) :
    (∫ p in rightRegion s, fderiv ℝ f p v) = ∫ t, (deriv s t * v 0 - v 1) * f (interface s t) := by
  let F : ℝ × ℝ → ℝ := f ∘ pairEquiv
  have hF : ContDiff ℝ 1 F := hf.comp pairEquiv.contDiff
  have hFc : HasCompactSupport F :=
    hcompact.comp_isClosedEmbedding pairEquiv.toHomeomorph.isClosedEmbedding
  have hdir : pairEquiv (v 0, v 1) = v := by
    rw [pairEquiv_apply]
    ext i
    fin_cases i <;> simp
  have hd (p : ℝ × ℝ) :
      fderiv ℝ F p (v 0, v 1) = fderiv ℝ f (pairEquiv p) v := by
    rw [show fderiv ℝ F p = (fderiv ℝ f (pairEquiv p)).comp pairEquiv.toContinuousLinearMap from
      ((hf.differentiable_one _).hasFDerivAt.comp p pairEquiv.hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hdir]
  have heq := measurePreserving_pairEquiv.setIntegral_preimage_emb
    pairEquiv.toHomeomorph.measurableEmbedding (fun p ↦ fderiv ℝ f p v) (rightRegion s)
  have hpre : pairEquiv ⁻¹' rightRegion s = {p : ℝ × ℝ | s p.1 < p.2} := by
    ext p
    simp [rightRegion, pairEquiv_apply]
  rw [hpre] at heq
  rw [← heq, Measure.volume_eq_prod]
  simp_rw [← hd]
  rw [integral_epigraph_fderiv hs hF hFc]
  apply integral_congr_ae
  filter_upwards [] with t
  simp [F, pairEquiv_apply, interface, mul_comm]

/-- The time derivative contributes the moving-boundary speed. -/
theorem integral_rightRegion_partialDeriv_time {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s)
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) :
    (∫ p in rightRegion s, (∂[0] f) p) = ∫ t, deriv s t * f (interface s t) := by
  simpa [partialDeriv] using integral_rightRegion_fderiv hs hf hcompact (EuclideanSpace.single 0 1)

/-- The spatial derivative contributes the negative trace on the left boundary
of the right-hand region. -/
theorem integral_rightRegion_partialDeriv_space {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s)
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) :
    (∫ p in rightRegion s, (∂[1] f) p) = -∫ t, f (interface s t) := by
  simpa [partialDeriv, integral_neg] using
    integral_rightRegion_fderiv hs hf hcompact (EuclideanSpace.single 1 1)

end PDE.Hyperbolic.ConservationLaw.Scalar.Shock

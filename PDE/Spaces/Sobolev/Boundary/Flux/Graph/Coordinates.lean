/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
public import PDE.Analysis.Calculus.IntegrationByParts.Epigraph

/-!
# Signed derivative integrals in general linear graph coordinates

A linear change of coordinates transports the C¹ epigraph formula to physical
space. The volume determinant and the signed graph conormal are retained
explicitly. The coordinate change may be nonorthogonal.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Flux.Graph

open Set MeasureTheory Trace.HalfSpace

variable {m : ℕ}

/-- The strict epigraph of a height after a general linear coordinate change. -/
def linearEpigraph (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) :
    Set (ℝ^(m + 1)) :=
  {x | g (splitTangentialNormal (A x)).1 < (A x) (Fin.last m)}

/-- The corresponding physical graph parametrization. -/
def linearGraphParametrization (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1))
    (g : ℝ^m → ℝ) (y : ℝ^m) : ℝ^(m + 1) :=
  A.symm (joinTangentialNormal (y, g y))

/-- Integrating a compactly supported scalar derivative above a graph in
nonorthogonal coordinates gives its signed conormal boundary integral. -/
theorem integral_linearEpigraph_fderiv
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    {f : ℝ^(m + 1) → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (v : ℝ^(m + 1)) :
    ∫ x in linearEpigraph A g, fderiv ℝ f x v =
      |A.symm.toLinearMap.det| *
        ∫ y, (fderiv ℝ g y (splitTangentialNormal (A v)).1 - (A v) (Fin.last m)) *
          f (linearGraphParametrization A g y) := by
  let S := tangentialNormalContinuousLinearEquiv (n := m)
  let H : Set (ℝ^(m + 1)) := {z | g (S z).1 < (S z).2}
  let V : Set (ℝ^m × ℝ) := {z | g z.1 < z.2}
  let B : (ℝ^m × ℝ) ≃L[ℝ] ℝ^(m + 1) := S.symm.trans A.symm
  let F : ℝ^m × ℝ → ℝ := fun z ↦ f (B z)
  have hF : ContDiff ℝ 1 F := hf.comp B.contDiff
  have hFc : HasCompactSupport F :=
    hcompact.comp_isClosedEmbedding B.toHomeomorph.isClosedEmbedding
  have hH : MeasurableSet H :=
    (isOpen_lt (hg.continuous.comp S.continuous.fst) S.continuous.snd).measurableSet
  have himage : A.symm '' H = linearEpigraph A g := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [linearEpigraph, H, S] using hz
    · intro hx
      refine ⟨A x, ?_, A.symm_apply_apply x⟩
      exact hx
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hH
    (fun z _ ↦ A.symm.hasFDerivAt.hasFDerivWithinAt)
    A.symm.injective.injOn (fun x ↦ fderiv ℝ f x v)
  rw [himage] at hchange
  have hsplit :
      ∫ z in H, fderiv ℝ f (A.symm z) v =
        ∫ z in V, fderiv ℝ f (B z) v ∂volume.prod volume := by
    have hmp := measurePreserving_tangentialNormalMeasurableEquiv (n := m)
    have h := hmp.setIntegral_preimage_emb
      tangentialNormalMeasurableEquiv.measurableEmbedding
      (fun z ↦ fderiv ℝ f (B z) v) V
    simpa [H, V, B, S, Measure.volume_eq_prod] using h
  have hd (z : ℝ^m × ℝ) : fderiv ℝ F z (S (A v)) = fderiv ℝ f (B z) v := by
    have h := ((hf.differentiable one_ne_zero _).hasFDerivAt.comp z B.hasFDerivAt).fderiv
    rw [show fderiv ℝ F z = (fderiv ℝ f (B z)).comp B.toContinuousLinearMap from h]
    simp [B]
  have hepigraph := PDE.integral_epigraph_fderiv (μ := volume) hg hF hFc
    (S (A v)).1 (S (A v)).2
  simp only [Prod.mk.eta, hd] at hepigraph
  rw [hchange]
  simp only [smul_eq_mul, integral_const_mul]
  rw [hsplit, hepigraph]
  rfl

end SobolevSpace.Boundary.Flux.Graph

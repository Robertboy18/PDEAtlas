/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Scalar
public import PDE.Analysis.Calculus.Divergence

/-!
# Vector Gauss–Green for surface measure

Summing the directional boundary formulas gives the divergence theorem.
The volume integrability follows from continuous derivatives on the compact
closure; the signed boundary integrability follows from the continuous
intrinsic normal and finite Hausdorff measure.

`integral_divergence_eq_normalFlux` is the divergence theorem, formula (2) of Evans App. C.2,
Theorem 1(ii), for a vector field that is C¹ on `ℝⁿ`. As in Evans, it follows from the directional
formula (1) (`integral_fderiv_eq_normalFlux`) applied to each component. `GaussGreen.Closure` proves
it under Evans's hypothesis `F ∈ C¹(Ū; ℝⁿ)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 1, (1)-(2), pp. 711-712.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.C1 Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- For a C¹ function `f` on `ℝⁿ` and a vector `v`, the directional derivative
`x ↦ fderiv ℝ f x v` is integrable on the bounded set `Ω`. -/
theorem integrableOn_fderiv_apply {f : ℝ^(m + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) (v : ℝ^(m + 1)) :
    IntegrableOn (fun x ↦ fderiv ℝ f x v) Ω := by
  have hc := (hf.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  exact (hc.continuousOn.integrableOn_compact hΩ.bounded.isCompact_closure).mono_set
    subset_closure

/-- The divergence of a C¹ vector field on `ℝⁿ` is integrable on the bounded set `Ω`. -/
theorem integrableOn_divergence {F : ℝ^(m + 1) → ℝ^(m + 1)}
    (hF : ContDiff ℝ 1 F) : IntegrableOn (∇· F) Ω := by
  change Integrable (fun x ↦ ∑ i : Fin (m + 1),
    fderiv ℝ (fun y ↦ F y i) x (EuclideanSpace.single i 1)) (volume.restrict Ω)
  apply integrable_finsetSum
  intro i _
  exact integrableOn_fderiv_apply (Ω := Ω)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF) (EuclideanSpace.single i 1)

/-- Divergence theorem (Evans App. C.2, Theorem 1(ii)): if `Ω` carries a `C1ExtensionAtlas` (so is
bounded and open) and has C¹ graph boundary and `F : ℝⁿ → ℝⁿ` is C¹, then
`∫_Ω div F dx = ∫_{∂Ω} F · ν dS`, with `ν` the intrinsic outward unit normal and `dS` the surface
measure `surfaceMeasure Ω`. -/
theorem integral_divergence_eq_normalFlux (hgraph : HasC1GraphBoundary Ω)
    {F : ℝ^(m + 1) → ℝ^(m + 1)} (hF : ContDiff ℝ 1 F) :
    ∫ x in Ω, ∇· F x =
      ∫ x, normalFlux (Ω := Ω) F x ∂surfaceMeasure Ω := by
  classical
  let e : Fin (m + 1) → ℝ^(m + 1) := fun i ↦ EuclideanSpace.single i 1
  have hFi (i : Fin (m + 1)) : ContDiff ℝ 1 (fun x ↦ F x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  have hs (i : Fin (m + 1)) :
      Integrable (normalFlux (Ω := Ω) (fun x ↦ F x i • e i)) (surfaceMeasure Ω) :=
    integrable_normalFlux ((hFi i).continuous.smul continuous_const).continuousOn
  have hsum (x : ℝ^(m + 1)) : ∑ i, F x i • e i = F x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr (F x)
  calc
    ∫ x in Ω, ∇· F x = ∑ i, ∫ x in Ω, fderiv ℝ (fun y ↦ F y i) x (e i) :=
      integral_finsetSum _ (fun i _ ↦ integrableOn_fderiv_apply (hFi i) (e i))
    _ = ∑ i, ∫ x, normalFlux (Ω := Ω) (fun y ↦ F y i • e i) x ∂surfaceMeasure Ω := by
      simp only [integral_fderiv_eq_normalFlux hgraph (hFi _) (e _)]
    _ = ∫ x, ∑ i, normalFlux (Ω := Ω) (fun y ↦ F y i • e i) x ∂surfaceMeasure Ω :=
      (integral_finsetSum _ (fun i _ ↦ hs i)).symm
    _ = ∫ x, normalFlux (Ω := Ω) F x ∂surfaceMeasure Ω := by
      rw [← normalFlux_sum]
      simp only [hsum]

end SobolevSpace.Boundary.Flux

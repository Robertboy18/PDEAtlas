/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.IntegralHessian
public import PDE.Analysis.Fourier.StationaryPhase.Congruence
public import PDE.Analysis.Fourier.StationaryPhase.Hessian
public import PDE.Analysis.Calculus.InverseFunction.Chart

/-!
# Smooth quadratic coordinates at a nondegenerate critical point

The integral Taylor Hessian is smoothly congruent to its value at the critical
point. Applying that congruence to the displacement constructs a coordinate map
whose derivative is the identity. The inverse function theorem gives a smooth
local chart and an exact quadratic phase, including for indefinite Hessians.

`exists_smooth_morse_chart` is the Morse lemma, Evans, §4.5.3(b), Lemma 3(ii), (46). Evans
rotates so that `A(0)` is diagonal and brings one coordinate at a time into quadratic form,
(49); we obtain the chart instead from the smooth congruence `exists_contDiffAt_congruence`
applied to `integralHessian`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 3(ii), (46), p. 223, and steps 2 and 3
  of its proof, (48)-(49), pp. 224-226. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology Gradient RealInnerProductSpace

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- Congruence of the integral Hessian constructs a smooth quadratic coordinate
map with identity derivative at the critical point. -/
theorem exists_quadratic_coordinate_map {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : fderiv ℝ f p = 0)
    (H : ℝ^n ≃L[ℝ] ℝ^n) (hH : (H : ℝ^n →L[ℝ] ℝ^n) = fderiv ℝ (∇ f) p) :
    ∃ g : ℝ^n → ℝ^n, g p = 0 ∧
      ContDiffAt ℝ (⊤ : ℕ∞) g p ∧
      HasFDerivAt g (ContinuousLinearMap.id ℝ (ℝ^n)) p ∧
      ∀ᶠ x in 𝓝 p, ContDiffAt ℝ (⊤ : ℕ∞) g x ∧
        f x = f p + inner ℝ (H (g x)) (g x) / 2 := by
  have hu : star (H.toUnit : ℝ^n →L[ℝ] ℝ^n) = H.toUnit := by
    change star (H : ℝ^n →L[ℝ] ℝ^n) = H
    rw [hH, ContinuousLinearMap.star_eq_adjoint]
    exact (show (fderiv ℝ (∇ f) p).IsSymmetric from
      fun v w ↦ (hf.contDiffAt.of_le (by simp)).inner_fderiv_gradient_comm v w).clm_adjoint_eq
  have hbase : integralHessian f p p = (H.toUnit : ℝ^n →L[ℝ] ℝ^n) := by
    rw [integralHessian_self, ← hH]
    rfl
  obtain ⟨R, hRp, hR, hRs, hcong⟩ := exists_contDiffAt_congruence H.toUnit hu
    (contDiff_integralHessian hf p) hbase
    (Eventually.of_forall fun x ↦ star_integralHessian (hf.of_le (by simp)) p x)
  let g (x : ℝ^n) : ℝ^n := R x (x - p)
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) g p :=
    hR.clm_apply (contDiffAt_id.sub contDiffAt_const)
  have hd : HasFDerivAt g (ContinuousLinearMap.id ℝ (ℝ^n)) p := by
    have h := (hR.differentiableAt (by simp)).hasFDerivAt.clm_apply
      ((hasFDerivAt_id p).sub_const p)
    simpa [g, hRp, ContinuousLinearMap.one_def] using h
  refine ⟨g, by simp [g], hg, hd, ?_⟩
  filter_upwards [hRs, hcong] with x hx hcx
  refine ⟨hx.clm_apply (contDiffAt_id.sub contDiffAt_const), ?_⟩
  have hq := congrArg (fun L : ℝ^n →L[ℝ] ℝ^n ↦ inner ℝ (L (x - p)) (x - p)) hcx
  change inner ℝ (star (R x) (H (R x (x - p)))) (x - p) =
    inner ℝ (integralHessian f p x (x - p)) (x - p) at hq
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] at hq
  have ht := quadratic_taylor_integralHessian hf p x
  simpa only [hp, zero_apply, add_zero, ← hq, g] using ht

/-- A smooth phase with invertible Hessian at a critical point admits a smooth
local chart in which it is exactly its quadratic Taylor polynomial. -/
theorem exists_smooth_quadratic_chart {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : fderiv ℝ f p = 0)
    (H : ℝ^n ≃L[ℝ] ℝ^n) (hH : (H : ℝ^n →L[ℝ] ℝ^n) = fderiv ℝ (∇ f) p) :
    ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      p ∈ e.source ∧ e p = 0 ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ (ℝ^n)) p ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      ∀ x ∈ e.source, f x = f p + inner ℝ (H (e x)) (e x) / 2 := by
  obtain ⟨g, hgp, _, hd, hnear⟩ := exists_quadratic_coordinate_map hf hp H hH
  obtain ⟨Ω, hΩ, hΩopen, hpΩ⟩ := mem_nhds_iff.mp hnear
  have hgΩ : ContDiffOn ℝ (⊤ : ℕ∞) g Ω :=
    hΩopen.contDiffOn_iff.mpr fun x hx ↦ (hΩ hx).1
  have hdet : (PDE.Analysis.jacobianMatrix g p).det ≠ 0 := by
    rw [PDE.Analysis.det_jacobianMatrix hd.differentiableAt, hd.fderiv]
    simp [ContinuousLinearMap.det]
  obtain ⟨e, he, hpe, heΩ, _, hregular⟩ :=
    PDE.Analysis.exists_regular_contDiffOn_inverse_chart
      hΩopen hpΩ (hgΩ.of_le (by simp)) hdet
  have heSmooth : ContDiffOn ℝ (⊤ : ℕ∞) e e.source := by
    rw [he]
    exact hgΩ.mono heΩ
  refine ⟨e, hpe, by simpa only [he] using hgp, he.symm ▸ hd, heSmooth, ?_, ?_⟩
  · apply e.open_target.contDiffOn_iff.mpr
    intro y hy
    have hz := e.map_target hy
    have hfe := heSmooth.contDiffAt (e.open_source.mem_nhds hz)
    have hdf := hfe.differentiableAt (by simp)
    have hu : IsUnit ((fderiv ℝ e (e.symm y)).det) := by
      apply isUnit_iff_ne_zero.mpr
      rw [← PDE.Analysis.det_jacobianMatrix hdf, he]
      exact hregular (e.symm y) hz
    let D : ℝ^n ≃L[ℝ] ℝ^n :=
      (LinearMap.equivOfIsUnitDet hu).toContinuousLinearEquiv
    have hD : (D : ℝ^n →L[ℝ] ℝ^n) = fderiv ℝ e (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : ℝ^n →ₗ[ℝ] ℝ^n ↦ L v) (LinearMap.coe_equivOfIsUnitDet hu)
    exact e.contDiffAt_symm hy (hD.symm ▸ hdf.hasFDerivAt) hfe
  · intro x hx
    simpa only [he] using (hΩ (heΩ hx)).2

/-- A smooth phase with a nondegenerate critical point has smooth Morse
coordinates preserving its Hessian, with identity derivative at the
critical point. The chart and both directions of its smoothness are constructed. -/
theorem exists_smooth_morse_chart {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : fderiv ℝ f p = 0)
    (hdet : (PDE.Analysis.hessianMatrix f p).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      p ∈ e.source ∧ e p = 0 ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ (ℝ^n)) p ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      ∀ x ∈ e.source, f x = f p +
        fderiv ℝ (fderiv ℝ f) p (e x) (e x) / 2 := by
  obtain ⟨H, hH⟩ := exists_hessian_continuousLinearEquiv
    (hf.contDiffAt.of_le (by simp)) hdet
  obtain ⟨e, hpSource, hep, hd, hs, ht, hq⟩ :=
    exists_smooth_quadratic_chart hf hp H hH
  refine ⟨e, hpSource, hep, hd, hs, ht, ?_⟩
  intro x hx
  have h := PDE.Analysis.inner_fderiv_gradient_at
    (hf.contDiffAt (x := p) |>.of_le (by simp)) (e x) (e x)
  rw [← hH] at h
  change inner ℝ (H (e x)) (e x) =
    fderiv ℝ (fderiv ℝ f) p (e x) (e x) at h
  simpa only [h] using hq x hx

end PDE.Analysis.StationaryPhase

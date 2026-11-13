/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.AxisymmetricIntegration
public import PDE.CoordinateSystems.Spherical.Frame
import Mathlib.Analysis.InnerProductSpace.Adjoint
import PDE.CoordinateSystems.Spherical.Axisymmetric
import PDE.CoordinateSystems.Spherical.FrameIntegration

/-!
# Quadrant integrals in the compactified radius and the frame Frobenius product

For a scale `s > 0` the compactified radius `β = arctan (r / s)` maps the positive half-line onto
`(0, π / 2)`, with inverse `r = s tan β`, and the radial volume element becomes
`r² dr = s³ (sin² β / cos⁴ β) dβ`. Suppose the weighted values
`sin² β / cos⁴ β · f (point (s tan β) θ φ)` of an integrable function `f` on `ℝ^3` are, for
`β ∈ (0, π / 2)` and `θ ∈ (0, π)`, a continuous profile `G β θ` independent of the azimuth `φ`,
and that `G β (π - θ) = G β θ`. Then `f` agrees off the symmetry axis, a null set, with a
function invariant under the rotations about the axis, and

`∫ f = 4π s³ ∫₀^{π/2} ∫₀^{π/2} G β θ sin θ dθ dβ`.

The spherical frame is an orthonormal basis at every pair of angles, so the inner product of
two vectors is the sum of the products of their frame components. The Frobenius product
`∑ᵢ ∑ⱼ ∂ⱼ Xᵢ ∂ⱼ Yᵢ` of two derivative matrices does not depend on the orthonormal bases chosen
in the domain and in the target, so it equals the Frobenius product of the frame matrices
`⟪e_p, DX e_q⟫` and `⟪e_p, DY e_q⟫`.

## Main results

* `integral_eq_quadrant_of_compactified`.
* `inner_eq_sum_frame`.
* `sum_partialDeriv_mul_partialDeriv_eq_frame`.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Real
open scoped RealInnerProductSpace InnerProduct

/-! ### Integrals in the compactified radius over a quadrant -/

/-- A spherical point of positive radius and polar angle in `(0, π)` lies off the symmetry
axis. -/
private theorem point_notMem_symmetryAxis {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 π) :
    point r θ 0 ∉ symmetryAxis := by
  rw [mem_symmetryAxis_iff]
  rintro ⟨h0, -⟩
  exact (mul_pos hr (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)).ne'
    (by simpa [point, radialFrame] using h0)

/-- For `r > 0` and `s > 0` the compactified radius `arctan (r / s)` lies in `(0, π / 2)`. -/
private theorem arctan_div_mem_Ioo {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    arctan (r / s) ∈ Ioo 0 (π / 2) :=
  ⟨arctan_pos.mpr (div_pos hr hs), arctan_lt_pi_div_two _⟩

/-- If the weighted values `sin² β / cos⁴ β · f (point (s tan β) θ φ)` are `G β θ`, then at a
point of positive radius `r` and polar angle in `(0, π)` the function is
`cos⁴ β / sin² β · G β θ` with `β = arctan (r / s)`, for every azimuth. -/
private theorem apply_point_of_compactified {f : ℝ^3 → ℝ} {s : ℝ} (hs : 0 < s)
    {G : ℝ → ℝ → ℝ}
    (hG : ∀ β ∈ Ioo 0 (π / 2), ∀ θ ∈ Ioo 0 π, ∀ φ : ℝ,
      sin β ^ 2 / cos β ^ 4 * f (point (s * tan β) θ φ) = G β θ)
    {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 π) (φ : ℝ) :
    f (point r θ φ) =
      cos (arctan (r / s)) ^ 4 / sin (arctan (r / s)) ^ 2 * G (arctan (r / s)) θ := by
  have hβ := arctan_div_mem_Ioo hr hs
  have hsin : sin (arctan (r / s)) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi hβ.1 (hβ.2.trans (by linarith [pi_pos]))).ne'
  have hcos : cos (arctan (r / s)) ≠ 0 := (cos_arctan_pos _).ne'
  rw [← hG _ hβ θ hθ φ, tan_arctan, mul_div_cancel₀ _ hs.ne']
  field_simp

/-- If the weighted values `sin² β / cos⁴ β · f (point (s tan β) θ φ)` do not depend on the
azimuth, then `f` set to zero on the symmetry axis is invariant under the rotations about the
axis. -/
private theorem isInvariantUnderAxisRotation_indicator_of_compactified {f : ℝ^3 → ℝ} {s : ℝ}
    (hs : 0 < s) {G : ℝ → ℝ → ℝ}
    (hG : ∀ β ∈ Ioo 0 (π / 2), ∀ θ ∈ Ioo 0 π, ∀ φ : ℝ,
      sin β ^ 2 / cos β ^ 4 * f (point (s * tan β) θ φ) = G β θ) :
    IsInvariantUnderAxisRotation (symmetryAxisᶜ.indicator f) := by
  intro φ x
  have hmem : axisRotation φ x ∈ symmetryAxis ↔ x ∈ symmetryAxis := by simp [symmetryAxis]
  by_cases hx : x ∈ symmetryAxis
  · rw [indicator_of_notMem (notMem_compl_iff.2 (hmem.2 hx)),
      indicator_of_notMem (notMem_compl_iff.2 hx)]
  · have hx0 := ne_zero_of_notMem_symmetryAxis hx
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hθ := polarAngle_mem_Ioo hx
    have hrot : axisRotation φ x = point ‖x‖ (polarAngle x) (φ + azimuthalAngle x) := by
      conv_lhs => rw [← point_norm_polarAngle_azimuthalAngle hx0]
      rw [← axisRotation_point ‖x‖ (polarAngle x) (azimuthalAngle x),
        ← axisRotation_point ‖x‖ (polarAngle x) (φ + azimuthalAngle x), axisRotation_add]
    rw [indicator_of_mem (show axisRotation φ x ∈ symmetryAxisᶜ from fun h ↦ hx (hmem.1 h)),
      indicator_of_mem (show x ∈ symmetryAxisᶜ from hx), hrot,
      apply_point_of_compactified hs hG hr hθ,
      ← apply_point_of_compactified hs hG hr hθ (azimuthalAngle x),
      point_norm_polarAngle_azimuthalAngle hx0]

/-- The integral over `ℝ^3` of an integrable function whose weighted values
`sin² β / cos⁴ β · f (point (s tan β) θ φ)` in the compactified radius `β = arctan (r / s)` are,
for `β ∈ (0, π / 2)` and `θ ∈ (0, π)`, a continuous profile `G β θ` even under `θ ↦ π - θ`:
`∫ f = 4π s³ ∫₀^{π/2} ∫₀^{π/2} G β θ sin θ dθ dβ`. -/
theorem integral_eq_quadrant_of_compactified {f : ℝ^3 → ℝ} (hf : Integrable f) {s : ℝ}
    (hs : 0 < s) {G : ℝ → ℝ → ℝ} (hGc : Continuous (Function.uncurry G))
    (hG : ∀ β ∈ Ioo 0 (Real.pi / 2), ∀ θ ∈ Ioo 0 Real.pi, ∀ φ : ℝ,
      Real.sin β ^ 2 / Real.cos β ^ 4 * f (point (s * Real.tan β) θ φ) = G β θ)
    (hsym : ∀ β θ, G β (Real.pi - θ) = G β θ) :
    ∫ x, f x = 4 * Real.pi * s ^ 3 *
      ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), G β θ * Real.sin θ := by
  have hae : symmetryAxisᶜ.indicator f =ᵐ[volume] f := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_symmetryAxis] with x hx
    exact indicator_of_mem hx f
  have hfold : ∀ β, ∫ θ in (0 : ℝ)..π, G β θ * sin θ =
      2 * ∫ θ in (0 : ℝ)..(π / 2), G β θ * sin θ := by
    intro β
    have hc : Continuous fun θ ↦ G β θ * sin θ :=
      (hGc.comp (continuous_const.prodMk continuous_id)).mul continuous_sin
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (π / 2))
      (hc.intervalIntegrable (π / 2) π), two_mul]
    congr 1
    calc ∫ θ in (π / 2)..π, G β θ * sin θ = ∫ θ in (π / 2)..π, G β (π - θ) * sin (π - θ) := by
          simp only [hsym, sin_pi_sub]
      _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left (fun θ ↦ G β θ * sin θ), sub_self,
            show π - π / 2 = π / 2 by ring]
  have hinner : ∀ r ∈ Ioi (0 : ℝ),
      ∫ θ in (0 : ℝ)..π, symmetryAxisᶜ.indicator f (point r θ 0) * r ^ 2 * sin θ =
        2 * (cos (arctan (r / s)) ^ 4 / sin (arctan (r / s)) ^ 2 * r ^ 2) *
          ∫ θ in (0 : ℝ)..(π / 2), G (arctan (r / s)) θ * sin θ := by
    intro r hr
    calc ∫ θ in (0 : ℝ)..π, symmetryAxisᶜ.indicator f (point r θ 0) * r ^ 2 * sin θ
        = ∫ θ in (0 : ℝ)..π, (cos (arctan (r / s)) ^ 4 / sin (arctan (r / s)) ^ 2 * r ^ 2) *
            (G (arctan (r / s)) θ * sin θ) :=
          intervalIntegral_congr_Ioo pi_pos.le fun θ hθ ↦ by
            rw [indicator_of_mem (point_notMem_symmetryAxis hr hθ),
              apply_point_of_compactified hs hG hr hθ]
            ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, hfold]; ring
  rw [← integral_congr_ae hae,
    integral_volume_of_axisymmetric (isInvariantUnderAxisRotation_indicator_of_compactified hs hG)
      (hf.congr hae.symm),
    setIntegral_congr_fun measurableSet_Ioi hinner, integral_comp_scaled_tan hs,
    setIntegral_congr_fun measurableSet_Ioo
      (g := fun β ↦ 2 * s ^ 3 * ∫ θ in (0 : ℝ)..(π / 2), G β θ * sin θ) ?_,
    integral_const_mul, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo]
  · ring
  · intro β hβ
    have hβ' : arctan (s * tan β / s) = β := by
      rw [mul_div_cancel_left₀ _ hs.ne', arctan_tan (by linarith [hβ.1, pi_pos]) hβ.2]
    have hcos : cos β ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, pi_pos], hβ.2⟩).ne'
    have hsin : sin β ≠ 0 := (sin_pos_of_pos_of_lt_pi hβ.1 (by linarith [hβ.2, pi_pos])).ne'
    simp only [hβ']
    rw [tan_eq_sin_div_cos]
    field_simp

/-! ### Parseval and the Frobenius product in the spherical frame -/

/-- Parseval's identity in the orthonormal spherical frame:
`⟪u, w⟫ = ∑ₖ ⟪e_k, u⟫ ⟪e_k, w⟫`. -/
theorem inner_eq_sum_frame (θ φ : ℝ) (u w : ℝ^3) :
    ⟪u, w⟫ = ∑ k, ⟪frame θ φ k, u⟫ * ⟪frame θ φ k, w⟫ := by
  rw [← (frameBasis θ φ).sum_inner_mul_inner u w]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [frameBasis_apply, real_inner_comm (frame θ φ k) u]

section Frobenius

variable {ι κ E F : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Summing the products of matrix entries `⟪c p, A (b q)⟫ ⟪c p, B (b q)⟫` over the target
basis first gives `∑_q ⟪A (b q), B (b q)⟫`. -/
private theorem sum_sum_inner_mul_inner_eq_sum_inner (A B : E →L[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F) :
    ∑ p, ∑ q, ⟪c p, A (b q)⟫ * ⟪c p, B (b q)⟫ = ∑ q, ⟪A (b q), B (b q)⟫ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← c.sum_inner_mul_inner (A (b q)) (B (b q))]
  exact Finset.sum_congr rfl fun p _ ↦ by rw [real_inner_comm (c p) (A (b q))]

/-- Summing the products of matrix entries `⟪c p, A (b q)⟫ ⟪c p, B (b q)⟫` over the domain
basis first gives `∑_p ⟪A† (c p), B† (c p)⟫`. -/
private theorem sum_sum_inner_mul_inner_eq_sum_inner_adjoint (A B : E →L[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F) :
    ∑ p, ∑ q, ⟪c p, A (b q)⟫ * ⟪c p, B (b q)⟫ = ∑ p, ⟪(A†) (c p), (B†) (c p)⟫ := by
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← b.sum_inner_mul_inner ((A†) (c p)) ((B†) (c p))]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ← real_inner_comm (b q) ((B†) (c p)),
    ContinuousLinearMap.adjoint_inner_left]

/-- The Frobenius product of two operators computed from their matrices in orthonormal bases
does not depend on the bases. -/
private theorem sum_sum_inner_mul_inner_orthonormalBasis (A B : E →L[ℝ] F)
    (b b' : OrthonormalBasis ι ℝ E) (c c' : OrthonormalBasis κ ℝ F) :
    ∑ p, ∑ q, ⟪c p, A (b q)⟫ * ⟪c p, B (b q)⟫ =
      ∑ p, ∑ q, ⟪c' p, A (b' q)⟫ * ⟪c' p, B (b' q)⟫ := by
  rw [sum_sum_inner_mul_inner_eq_sum_inner_adjoint A B b c,
    ← sum_sum_inner_mul_inner_eq_sum_inner_adjoint A B b' c,
    sum_sum_inner_mul_inner_eq_sum_inner A B b' c,
    ← sum_sum_inner_mul_inner_eq_sum_inner A B b' c']

end Frobenius

/-- The Frobenius product `∑ᵢ ∑ⱼ ∂ⱼ Xᵢ ∂ⱼ Yᵢ` at `x` of two fields differentiable there equals
the Frobenius product of their derivative matrices `⟪e_p, DX (x) e_q⟫`, `⟪e_p, DY (x) e_q⟫` in
the spherical frame at any pair of angles. -/
theorem sum_partialDeriv_mul_partialDeriv_eq_frame {X Y : ℝ^3 → ℝ^3} {x : ℝ^3}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) (θ φ : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, PDE.partialDeriv j (fun y ↦ X y i) x *
        PDE.partialDeriv j (fun y ↦ Y y i) x =
      ∑ p : Fin 3, ∑ q : Fin 3, ⟪frame θ φ p, fderiv ℝ X x (frame θ φ q)⟫ *
        ⟪frame θ φ p, fderiv ℝ Y x (frame θ φ q)⟫ := by
  have hc : ∀ Z : ℝ^3 → ℝ^3, DifferentiableAt ℝ Z x → ∀ i j : Fin 3,
      PDE.partialDeriv j (fun y ↦ Z y i) x =
        ⟪EuclideanSpace.basisFun (Fin 3) ℝ i,
          fderiv ℝ Z x (EuclideanSpace.basisFun (Fin 3) ℝ j)⟫ := by
    intro Z hZ i j
    have h : HasFDerivAt (fun y ↦ Z y i)
        ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).comp (fderiv ℝ Z x)) x :=
      (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.comp x hZ.hasFDerivAt
    rw [PDE.partialDeriv, h.fderiv, EuclideanSpace.basisFun_inner,
      EuclideanSpace.basisFun_apply]
    rfl
  simp only [hc X hX, hc Y hY]
  simpa only [frameBasis_apply] using sum_sum_inner_mul_inner_orthonormalBasis (fderiv ℝ X x)
    (fderiv ℝ Y x) (EuclideanSpace.basisFun (Fin 3) ℝ) (frameBasis θ φ)
    (EuclideanSpace.basisFun (Fin 3) ℝ) (frameBasis θ φ)

end PDE.CoordinateSystems.Spherical

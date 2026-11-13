/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantPotential
public import PDE.Fluid.Incompressible.HalfPlane.OriginStrain
public import PDE.FDeriv.PartialDeriv.Within
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension
import PDE.FDeriv.Laplacian.Congruence
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Fluid.Incompressible.HalfPlane.OriginTaylor
import PDE.FDeriv.PartialDeriv.Energy

/-!
# The half-plane stream function of a decaying vorticity

Chen and Hou's profile vorticity is not compactly supported: it decays like `r^{ᾱ₁}` with
`ᾱ₁ ≈ -0.342` (Part I, (Decay) and Section 7.1). For such data the method-of-images
integral `∫ Φ(x - y) W(y) dy` of the odd extension `W` does not converge absolutely, but the
grouped quadrant potential `GreenFunction.quadrantPotential ω` does. We work with the class
`IsDecayingVorticity ω`: `ω` is `C²` on the closed upper half-plane, odd in `x₀` there, and
`|ω(y)| ≤ C (1 + |y|)^(-β)` on the open half-plane for some `β > 0`.

The stream `Ψ = quadrantPotential ω` vanishes on the boundary and is odd in `x₀`
(`GreenFunction.quadrantPotential_of_eq_zero`,
`GreenFunction.quadrantPotential_coordinateReflection_zero`). With the regularity, the Poisson
equation and the growth bound, this makes `Ψ` the half-plane stream function of `ω` in the sense of
the uniqueness class (harmonic difference `o(|x|²)`, odd, zero on the boundary).

## Main definitions

* `IsDecayingVorticity`: `ω` is `C²` on the closed upper half-plane, odd in `x₀` there, and
  `|ω(y)| ≤ C (1 + |y|)^(-β)` on the open upper half-plane for some `β > 0`.

## Main results

* `contDiff_one_quadrantPotential`: `Ψ` is `C¹` on the plane; it is `C²` on the closed upper
  half-plane (`contDiffOn_quadrantPotential`).
* `laplacian_quadrantPotential`: `-ΔΨ = ω` on the open upper half-plane.
* `partialDeriv_quadrantPotential`: the gradient is the grouped Biot-Savart integral
  `∂ⱼΨ(x) = ∫_{ℝ²₊₊} gⱼₛ(x, y) ω(y) dy`, absolutely convergent at every point.
* `tendsto_partialDeriv_partialDeriv_quadrantPotential`: Part I (5.67), `∂₀∂₁Ψ` tends to
  `(4/π) ∫_{ℝ²₊₊} K₁ ω` at the origin from the upper half-plane, so `u_x(0) = -(4/π) ∫ K₁ ω`.
* `hasPrincipalValueAt_partialDeriv_partialDeriv_quadrantPotential`: Part I (3.1)-(3.4), in the
  open half-plane `P.V.∫ k₀ⱼ(x - y) W(y) dy = π (∂ⱼ∂₀Ψ + δ₀ⱼ ω/2)`.
* `IsDecayingVorticity.exists_decomposition_ball`: the cutoff decomposition into a compact `C²`
  source equal to `ω` inside `B(0, R)` and a far density vanishing on the quadrant there.
* `quadrantPotential_isLittleO`: `Ψ = o(|x|²)` on the closed half-plane, from
  `|∇Ψ(x)| ≤ A_ρ/|x| + 12 ε |x| + (10/π) |x| ∫_{|y| ≥ 2|x|} |ω|/|y|²` with `|ω| ≤ ε` beyond `ρ`.

## How it works

We split `ω = χ_R ω + (1 - χ_R) ω` with a radial cutoff `χ_R` equal to one on `B(0, R)`
(`IsDecayingVorticity.exists_decomposition_ball`), with `R` chosen so that the point considered lies
in `B(0, R/2)`. The near part `χ_R ω` extends to a compact `C²` source on the plane
(`PDE.Analysis.exists_contDiff_compact_extension_halfSpace`), whose Green potential is its grouped
quadrant potential (`halfSpaceGreenPotential_eq_quadrantPotential`). The potential of the far part
is the real part of a holomorphic function on `B(0, R/2)`, hence smooth and harmonic there
(`GreenFunction.contDiffOn_quadrantPotential_ball`,
`GreenFunction.laplacian_quadrantPotential_ball`). Regularity, the Poisson equation, the Biot-Savart
integral, the limit of `∂₀∂₁Ψ` at the origin and the principal value follow by adding the two parts.
For the growth bound we split the Biot-Savart integral into the vorticity in a fixed ball, the
vorticity where `|ω| ≤ ε`, and the tail `|y| ≥ 2|x|`; this gives `|∇Ψ(x)| ≤ ε |x|` for large `|x|`,
and a function vanishing on the boundary with gradient `o(|x|)` is `o(|x|²)`
(`isLittleO_sq_of_norm_fderiv_le`). The decomposition is public because the vanishing of the
velocity at the origin is proved from it in a later module.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.4, (Decay), p. 12, and
  Section 7.1, (7.1), p. 122, for the decay of the profile; Section 3, (3.1)-(3.4), p. 27;
  Section 5.6, (5.67), p. 78.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

/-- A vorticity of the decaying class: `C²` on the closed upper half-plane, odd in `x₀` there, and
`|ω(y)| ≤ C (1 + |y|)^(-β)` on the open upper half-plane for some `β > 0`. -/
structure IsDecayingVorticity (ω : ℝ^2 → ℝ) : Prop where
  /-- `ω` is `C²` on the closed upper half-plane. -/
  contDiffOn : ContDiffOn ℝ 2 ω {y | 0 ≤ y 1}
  /-- `ω` is odd in `x₀` on the closed upper half-plane. -/
  odd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y
  /-- The decay `|ω(y)| ≤ C (1 + |y|)^(-β)`, `β > 0`. -/
  decay : ∃ C β : ℝ, 0 < β ∧ ∀ y, 0 < y 1 → |ω y| ≤ C * (1 + ‖y‖) ^ (-β)

/-! ### Compact sources -/

section Compact

variable {F : ℝ^2 → ℝ}

/-- For a continuous compactly supported `F` the Green potential is the convolution
`φ_F(x) = ∫ Γ(x - y) W(y) dy` of the fundamental solution `Γ` with the odd extension `W` of `F`. -/
private theorem integral_fundamentalSolution_eq (hF : Continuous F) (hc : HasCompactSupport F)
    (x : ℝ^2) :
    halfSpaceGreenPotential F x =
      ∫ y, fundamentalSolution 2 (x - y) * oddHalfSpaceExtension F y := by
  rw [halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension hF hc, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_sub_left_eq_self
    (fun t ↦ fundamentalSolution 2 t * oddHalfSpaceExtension F (x - t)) volume x]
  simp only [sub_sub_cancel]

/-- On the open quadrant `ℝ²₊₊` the odd extension of `F` is `F`. -/
private theorem eqOn_oddHalfSpaceExtension_quadrant (F : ℝ^2 → ℝ) :
    EqOn (oddHalfSpaceExtension F) F GreenFunction.quadrant :=
  fun _ hy ↦ oddHalfSpaceExtension_eqOn F hy.2

/-- For a continuous compact source odd in `x₀`, the grouped quadrant integrand of the stream is
integrable. -/
theorem integrableOn_symmetrizedKernel_fundamentalSolution_of_compact (hF : Continuous F)
    (hc : HasCompactSupport F) (hodd : ∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) (x : ℝ^2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (fundamentalSolution 2) x y * F y)
      GreenFunction.quadrant := by
  refine (integrableOn_symmetrizedKernel_mul x (oddHalfSpaceExtension_reflect_zero hodd)
    (oddHalfSpaceExtension_reflect_one F)
    (integrable_fundamentalSolution_mul_oddHalfSpaceExtension hF hc x)).congr_fun
    (fun y hy ↦ ?_) measurableSet_quadrant
  simp only [eqOn_oddHalfSpaceExtension_quadrant F hy]

/-- For a continuous compact source odd in `x₀`, the Green potential is the grouped quadrant
potential. -/
theorem halfSpaceGreenPotential_eq_quadrantPotential (hF : Continuous F)
    (hc : HasCompactSupport F) (hodd : ∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) (x : ℝ^2) :
    halfSpaceGreenPotential F x = quadrantPotential F x := by
  rw [integral_fundamentalSolution_eq hF hc,
    integral_mul_eq_setIntegral_quadrant_symmetrizedKernel x
      (oddHalfSpaceExtension_reflect_zero hodd) (oddHalfSpaceExtension_reflect_one F)
      (integrable_fundamentalSolution_mul_oddHalfSpaceExtension hF hc x)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  rw [eqOn_oddHalfSpaceExtension_quadrant F hy]

/-- For a continuous compact source odd in `x₀`, the grouped velocity integrand is integrable. -/
theorem integrableOn_symmetrizedKernel_gradientKernel_of_compact (hF : Continuous F)
    (hc : HasCompactSupport F) (hodd : ∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) (j : Fin 2) (x : ℝ^2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (gradientKernel j) x y * F y)
      GreenFunction.quadrant := by
  refine (integrableOn_symmetrizedKernel_mul x (oddHalfSpaceExtension_reflect_zero hodd)
    (oddHalfSpaceExtension_reflect_one F)
    (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hF hc j x)).congr_fun
    (fun y hy ↦ ?_) measurableSet_quadrant
  simp only [eqOn_oddHalfSpaceExtension_quadrant F hy]

/-- For a continuous compact source odd in `x₀`, the velocity of the Green potential is the
grouped quadrant integral `∂ⱼφ(x) = ∫_{ℝ²₊₊} gⱼₛ(x, y) F(y) dy`. -/
theorem partialDeriv_halfSpaceGreenPotential_eq_setIntegral (hF : Continuous F)
    (hc : HasCompactSupport F) (hodd : ∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) (j : Fin 2) (x : ℝ^2) :
    (∂[j] (halfSpaceGreenPotential F)) x =
      ∫ y in GreenFunction.quadrant, symmetrizedKernel (gradientKernel j) x y * F y := by
  rw [partialDeriv_halfSpaceGreenPotential_eq_integral hF hc,
    integral_mul_eq_setIntegral_quadrant_symmetrizedKernel x
      (oddHalfSpaceExtension_reflect_zero hodd) (oddHalfSpaceExtension_reflect_one F)
      (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hF hc j x)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  rw [eqOn_oddHalfSpaceExtension_quadrant F hy]

end Compact

/-! ### The cutoff decomposition -/

section Decomposition

/-- The radial cutoff `χ_R(y) = s((4R² - |y|²)/(3R²))`, `s` the smooth transition: one on
`B(0, R)`, zero outside `B(0, 2R)`. -/
private def cutoff (R : ℝ) (y : ℝ^2) : ℝ :=
  Real.smoothTransition ((4 * R ^ 2 - ‖y‖ ^ 2) / (3 * R ^ 2))

/-- The cutoff `χ_R` is smooth. -/
private theorem contDiff_cutoff (R : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff R) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _))

/-- For `R > 0`, `χ_R(y) = 1` when `|y| ≤ R`. -/
private theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {y : ℝ^2} (hy : ‖y‖ ≤ R) : cutoff R y = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg y]

/-- For `R > 0`, `χ_R(y) = 0` when `|y| ≥ 2R`. -/
private theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {y : ℝ^2} (hy : 2 * R ≤ ‖y‖) :
    cutoff R y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  nlinarith

/-- The cutoff is radial, so `χ_R(R₀ y) = χ_R(y)` for the reflection `R₀ : y₀ ↦ -y₀`. -/
private theorem cutoff_reflect (R : ℝ) (y : ℝ^2) : cutoff R (𝐑 0 y) = cutoff R y := by
  simp only [cutoff, PDE.Common.norm_coordinateReflection]

/-- For `R > 0` the cutoff `χ_R` has compact support. -/
private theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^2) (2 * R)) fun y hy ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  exact cutoff_eq_zero hR hy.le

/-- The near part `χ_R ω`. -/
private def nearPart (R : ℝ) (ω : ℝ^2 → ℝ) (y : ℝ^2) : ℝ := cutoff R y * ω y

/-- The far part `(1 - χ_R) ω`. -/
private def farPart (R : ℝ) (ω : ℝ^2 → ℝ) (y : ℝ^2) : ℝ := (1 - cutoff R y) * ω y

variable {ω : ℝ^2 → ℝ}

/-- A decaying vorticity satisfies `|ω(y)| ≤ C (1 + |y|)^(-β)` with `β > 0` on the open quadrant
`ℝ²₊₊`. -/
private theorem decay_closed (hD : IsDecayingVorticity ω) :
    ∃ C β : ℝ, 0 < β ∧ ∀ y ∈ GreenFunction.quadrant, |ω y| ≤ C * (1 + ‖y‖) ^ (-β) := by
  obtain ⟨C, β, hβ, h⟩ := hD.decay
  exact ⟨C, β, hβ, fun y hy ↦ h y hy.2⟩

/-- A decaying vorticity is continuous on the open quadrant `ℝ²₊₊`. -/
private theorem continuousOn_quadrant (hD : IsDecayingVorticity ω) :
    ContinuousOn ω GreenFunction.quadrant :=
  hD.contDiffOn.continuousOn.mono fun _ hy ↦ (le_of_lt hy.2 : (0 : ℝ) ≤ _)

/-- `1/|y|² ≤ ((1 + a)/a)² / (1 + |y|)²` for `|y| ≥ a > 0`. -/
private theorem one_div_sq_le {a : ℝ} (ha : 0 < a) {y : ℝ^2} (hy : a ≤ ‖y‖) :
    1 / ‖y‖ ^ 2 ≤ ((1 + a) / a) ^ 2 / (1 + ‖y‖) ^ 2 := by
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le ha hy
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, div_pow,
    div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : a * (1 + ‖y‖) ≤ (1 + a) * ‖y‖ := by nlinarith
  nlinarith [mul_le_mul this this (by positivity) (by positivity)]

/-- `(1 + |y|)^(-(β + 2)) = (1 + |y|)^(-β) / (1 + |y|)²`. -/
private theorem rpow_neg_add_two {β : ℝ} (y : ℝ^2) :
    (1 + ‖y‖) ^ (-(β + 2)) = (1 + ‖y‖) ^ (-β) / (1 + ‖y‖) ^ 2 := by
  rw [show -(β + 2) = -β + -(2 : ℝ) by ring, Real.rpow_add (by positivity),
    Real.rpow_neg (by positivity) 2, Real.rpow_two, div_eq_mul_inv]

/-- `(1 + |y|)^(-(β + 2))` is integrable on `ℝ²` for `β > 0`. -/
private theorem integrable_one_add_norm_rpow {β : ℝ} (hβ : 0 < β) :
    Integrable (fun y : ℝ^2 ↦ (1 + ‖y‖) ^ (-(β + 2))) := by
  refine integrable_one_add_norm ?_
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  linarith

/-- The far part is bounded by the vorticity: `|(1 - χ_R) ω| ≤ |ω|`. -/
private theorem abs_farPart_le (R : ℝ) (y : ℝ^2) : |farPart R ω y| ≤ |ω y| := by
  have h0 : 0 ≤ cutoff R y := Real.smoothTransition.nonneg _
  have h1 : cutoff R y ≤ 1 := Real.smoothTransition.le_one _
  rw [farPart, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - cutoff R y)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)

/-- The far part is a far density of radius `R`. -/
private theorem isQuadrantFarDensity_farPart (hD : IsDecayingVorticity ω) {R : ℝ} (hR : 0 < R) :
    IsQuadrantFarDensity (farPart R ω) R := by
  have hc : ContinuousOn (farPart R ω) GreenFunction.quadrant :=
    (continuous_const.sub (contDiff_cutoff R (n := 0)).continuous).continuousOn.mul
      (continuousOn_quadrant hD)
  refine ⟨hR, fun y _ hy ↦ by simp [farPart, cutoff_eq_one hR hy.le],
    hc.aestronglyMeasurable measurableSet_quadrant, ?_⟩
  obtain ⟨C, β, hβ, hdec⟩ := decay_closed hD
  have hint := integrable_one_add_norm_rpow hβ
  refine Integrable.mono' (hint.const_mul (C * ((1 + R) / R) ^ 2)).integrableOn
    ((hc.div (continuous_norm.pow 2).continuousOn fun y hy ↦ pow_ne_zero 2
      (norm_ne_zero_iff.mpr (by rintro rfl; simpa using hy.1))).aestronglyMeasurable
        measurableSet_quadrant) ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hdec y hy))
    (Real.rpow_pos_of_pos (by positivity) _)
  rcases lt_or_ge ‖y‖ R with hyR | hyR
  · simp only [farPart, cutoff_eq_one hR hyR.le, sub_self, zero_mul, zero_div, norm_zero]
    positivity
  have hy0 : 0 < ‖y‖ := hR.trans_le hyR
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 2), rpow_neg_add_two]
  calc |farPart R ω y| / ‖y‖ ^ 2 = |farPart R ω y| * (1 / ‖y‖ ^ 2) := by ring
    _ ≤ (C * (1 + ‖y‖) ^ (-β)) * (((1 + R) / R) ^ 2 / (1 + ‖y‖) ^ 2) :=
        mul_le_mul ((abs_farPart_le R y).trans (hdec y hy)) (one_div_sq_le hR hyR)
          (by positivity) (by positivity)
    _ = _ := by ring

/-- The near part `χ_R ω` is `C²` on the closed upper half-plane. -/
private theorem nearPart_contDiffOn (hD : IsDecayingVorticity ω) (R : ℝ) :
    ContDiffOn ℝ 2 (nearPart R ω) {y | 0 ≤ y 1} :=
  (contDiff_cutoff R).contDiffOn.mul hD.contDiffOn

/-- For `R > 0` the near part `χ_R ω` has compact support. -/
private theorem hasCompactSupport_nearPart {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (nearPart R ω) :=
  (hasCompactSupport_cutoff hR).mul_right

/-- The near part `χ_R ω` is odd in `x₀` on the closed upper half-plane. -/
private theorem nearPart_odd (hD : IsDecayingVorticity ω) (R : ℝ) :
    ∀ y, 0 ≤ y 1 → nearPart R ω (𝐑 0 y) = -nearPart R ω y := fun y hy ↦ by
  simp only [nearPart, cutoff_reflect, hD.odd y hy, mul_neg]

/-- **The cutoff decomposition.** For `R > 0` there is a compact `C²` source `F`, equal to
`χ_R ω` on the closed upper half-plane, such that on `B(0, R/2)`
`Ψ_ω = φ_F + Ψ_{(1 - χ_R) ω}` with `φ_F` the Green potential of `F`. -/
private theorem exists_decomposition (hD : IsDecayingVorticity ω) {R : ℝ} (hR : 0 < R) :
    ∃ F : ℝ^2 → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) ∧ EqOn F (nearPart R ω) {y | 0 ≤ y 1} ∧
      ∀ x : ℝ^2, ‖x‖ < R / 2 →
        quadrantPotential ω x =
          halfSpaceGreenPotential F x + quadrantPotential (farPart R ω) x := by
  obtain ⟨F, hF, hFc, hFeq⟩ := PDE.Analysis.exists_contDiff_compact_extension_halfSpace (1 : Fin 2)
    2 (nearPart_contDiffOn hD R) (hasCompactSupport_nearPart hR)
  have hFodd : ∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y := by
    intro y hy
    have hy' : 0 ≤ (𝐑 0 y) 1 := by
      rwa [PDE.Common.coordinateReflection_apply_of_ne 0 1 (by decide)]
    rw [hFeq hy', hFeq hy, nearPart_odd hD R y hy]
  refine ⟨F, hF, hFc, hFodd, hFeq, fun x hx ↦ ?_⟩
  have hfar := isQuadrantFarDensity_farPart hD hR
  have hFQ : EqOn F (nearPart R ω) GreenFunction.quadrant := fun y hy ↦ hFeq (le_of_lt hy.2)
  rw [halfSpaceGreenPotential_eq_quadrantPotential hF.continuous hFc hFodd]
  unfold quadrantPotential
  rw [← integral_add (integrableOn_symmetrizedKernel_fundamentalSolution_of_compact hF.continuous
    hFc hFodd x) (integrableOn_symmetrizedKernel_fundamentalSolution_of_far hfar hx)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  simp only [hFQ hy, nearPart, farPart]
  ring

/-- **The cutoff decomposition of a decaying vorticity.** For `R > 0` there are a compact `C²`
source `F`, odd in `x₀` and equal to `ω` on the closed half-plane inside `B(0, R)`, and a far
density `G` vanishing on the quadrant inside `B(0, R)`, with `F + G = ω` on the quadrant and
`Ψ_ω = φ_F + Ψ_G` on `B(0, R/2)`, `φ_F` the Green potential of `F`. -/
theorem IsDecayingVorticity.exists_decomposition_ball (hD : IsDecayingVorticity ω) {R : ℝ}
    (hR : 0 < R) :
    ∃ F G : ℝ^2 → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) ∧ (∀ y, 0 ≤ y 1 → ‖y‖ < R → F y = ω y) ∧
      IsQuadrantFarDensity G R ∧ (∀ y ∈ GreenFunction.quadrant, F y + G y = ω y) ∧
      ∀ x : ℝ^2, ‖x‖ < R / 2 →
        quadrantPotential ω x = halfSpaceGreenPotential F x + quadrantPotential G x := by
  obtain ⟨F, hF, hFc, hFodd, hFeq, hdec⟩ := exists_decomposition hD hR
  refine ⟨F, farPart R ω, hF, hFc, hFodd, fun y hy hyR ↦ ?_, isQuadrantFarDensity_farPart hD hR,
    fun y hy ↦ ?_, hdec⟩
  · rw [hFeq hy]
    simp [nearPart, cutoff_eq_one hR hyR.le]
  · rw [hFeq (le_of_lt hy.2)]
    simp only [nearPart, farPart]
    ring

end Decomposition

/-! ### The stream function of a decaying vorticity -/

section Stream

variable {ω : ℝ^2 → ℝ}

/-- Second partial derivatives of a sum of functions `C²` at the point. -/
theorem partialDeriv_partialDeriv_add {f g : ℝ^2 → ℝ} {x : ℝ^2} (k l : Fin 2)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (∂[l] (∂[k] (fun y ↦ f y + g y))) x = (∂[l] (∂[k] f)) x + (∂[l] (∂[k] g)) x := by
  have hev : ∂[k] (fun y ↦ f y + g y) =ᶠ[𝓝 x] fun y ↦ (∂[k] f) y + (∂[k] g) y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
    exact PDE.partialDeriv_add (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  rw [PDE.partialDeriv_congr_nhds l hev]
  exact PDE.partialDeriv_add ((PDE.contDiffAt_partialDeriv 1 hf k).differentiableAt one_ne_zero)
    ((PDE.contDiffAt_partialDeriv 1 hg k).differentiableAt one_ne_zero)

variable (hD : IsDecayingVorticity ω)
include hD

/-- Near every point the potential is a compact Green potential plus a smooth far part. -/
private theorem exists_local (x : ℝ^2) :
    ∃ R : ℝ, 0 < R ∧ ‖x‖ < R / 2 ∧ ∃ F : ℝ^2 → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ y, 0 ≤ y 1 → F (𝐑 0 y) = -F y) ∧ EqOn F (nearPart R ω) {y | 0 ≤ y 1} ∧
      (∀ y : ℝ^2, ‖y‖ < R / 2 →
        quadrantPotential ω y = halfSpaceGreenPotential F y + quadrantPotential (farPart R ω) y) ∧
      quadrantPotential ω =ᶠ[𝓝 x]
        fun y ↦ halfSpaceGreenPotential F y + quadrantPotential (farPart R ω) y := by
  have hR : (0 : ℝ) < 2 * ‖x‖ + 2 := by positivity
  have hx : ‖x‖ < (2 * ‖x‖ + 2) / 2 := by linarith
  refine ⟨2 * ‖x‖ + 2, hR, hx, ?_⟩
  obtain ⟨F, hF, hFc, hFodd, hFeq, hdec⟩ := exists_decomposition hD hR
  refine ⟨F, hF, hFc, hFodd, hFeq, hdec, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
  exact hdec y (mem_ball_zero_iff.mp hy)

/-- For `R > 0` the grouped potential of the far part `(1 - χ_R) ω` is `C^n` of every order `n`
at each point of `B(0, R/2)`. -/
private theorem contDiffAt_farPart {R : ℝ} (hR : 0 < R) {x : ℝ^2} (hx : ‖x‖ < R / 2)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (quadrantPotential (farPart R ω)) x :=
  (contDiffOn_quadrantPotential_ball (isQuadrantFarDensity_farPart hD hR)).contDiffAt
    (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx))

/-- The grouped potential of a decaying vorticity is `C¹` on the whole plane. -/
theorem contDiff_one_quadrantPotential : ContDiff ℝ 1 (quadrantPotential ω) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  obtain ⟨R, hR, hx, F, hF, hFc, _, _, -, hev⟩ := exists_local hD x
  exact (((contDiff_one_halfSpaceGreenPotential hF.continuous hFc).contDiffAt).add
    (contDiffAt_farPart hD hR hx)).congr_of_eventuallyEq hev

/-- The grouped potential of a decaying vorticity is `C²` on the closed upper half-plane. -/
theorem contDiffOn_quadrantPotential : ContDiffOn ℝ 2 (quadrantPotential ω) {y | 0 ≤ y 1} := by
  intro x hx
  obtain ⟨R, hR, hxR, F, hF, hFc, _, _, -, hev⟩ := exists_local hD x
  have h1 : ContDiffOn ℝ 2 (halfSpaceGreenPotential F) {y | 0 ≤ y 1} := by
    have := contDiffOn_two_halfSpaceGreenPotential_closure hF hFc
    rwa [HalfSpace.closure_upper_two] at this
  exact ((h1 x hx).add (contDiffAt_farPart hD hR hxR).contDiffWithinAt).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hev) hev.eq_of_nhds

/-- **The Poisson equation**: `-ΔΨ = ω` on the open upper half-plane. -/
theorem laplacian_quadrantPotential {x : ℝ^2} (hx : 0 < x 1) :
    -PDE.laplacian (quadrantPotential ω) x = ω x := by
  obtain ⟨R, hR, hxR, F, hF, hFc, _, hFeq, -, hev⟩ := exists_local hD x
  have hxU : x ∈ HalfSpace.upper 2 := hx
  obtain ⟨hreg, hpois⟩ := halfSpaceGreenPotential_local_poisson hF.continuous hFc hxU
    hF.contDiffAt
  rw [EuclideanLaplacian.laplacian_congr_nhds hev,
    PDE.laplacian_add _ _ x hreg (contDiffAt_farPart hD hR hxR),
    laplacian_quadrantPotential_ball (isQuadrantFarDensity_farPart hD hR) hxR, add_zero, hpois,
    hFeq (le_of_lt hx)]
  simp [nearPart, cutoff_eq_one hR (by linarith : ‖x‖ ≤ R)]

/-- The grouped velocity integrand of a decaying vorticity is integrable at every point. -/
theorem integrableOn_symmetrizedKernel_gradientKernel (j : Fin 2) (x : ℝ^2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (gradientKernel j) x y * ω y)
      GreenFunction.quadrant := by
  obtain ⟨R, hR, hxR, F, hF, hFc, hFodd, hFeq, -, -⟩ := exists_local hD x
  refine ((integrableOn_symmetrizedKernel_gradientKernel_of_compact hF.continuous hFc hFodd j
    x).add (integrableOn_symmetrizedKernel_gradientKernel_of_far
      (isQuadrantFarDensity_farPart hD hR) j hxR)).congr_fun (fun y hy ↦ ?_)
      measurableSet_quadrant
  simp only [Pi.add_apply, hFeq (le_of_lt hy.2), nearPart, farPart]
  ring

/-- The grouped potential integrand of a decaying vorticity is integrable at every point. -/
theorem integrableOn_symmetrizedKernel_fundamentalSolution (x : ℝ^2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (fundamentalSolution 2) x y * ω y)
      GreenFunction.quadrant := by
  obtain ⟨R, hR, hxR, F, hF, hFc, hFodd, hFeq, -, -⟩ := exists_local hD x
  refine ((integrableOn_symmetrizedKernel_fundamentalSolution_of_compact hF.continuous hFc hFodd
    x).add (integrableOn_symmetrizedKernel_fundamentalSolution_of_far
      (isQuadrantFarDensity_farPart hD hR) hxR)).congr_fun (fun y hy ↦ ?_)
      measurableSet_quadrant
  simp only [Pi.add_apply, hFeq (le_of_lt hy.2), nearPart, farPart]
  ring

/-- **The velocity of a decaying vorticity**: `∂ⱼΨ(x) = ∫_{ℝ²₊₊} gⱼₛ(x, y) ω(y) dy` at every
point, an absolutely convergent grouped Biot-Savart integral. -/
theorem partialDeriv_quadrantPotential (j : Fin 2) (x : ℝ^2) :
    (∂[j] (quadrantPotential ω)) x =
      ∫ y in GreenFunction.quadrant, symmetrizedKernel (gradientKernel j) x y * ω y := by
  obtain ⟨R, hR, hxR, F, hF, hFc, hFodd, hFeq, -, hev⟩ := exists_local hD x
  have hfar := isQuadrantFarDensity_farPart hD hR
  rw [PDE.partialDeriv_congr_nhds j hev,
    PDE.partialDeriv_add ((contDiff_one_halfSpaceGreenPotential hF.continuous hFc).differentiable
      one_ne_zero x) ((contDiffAt_farPart hD hR hxR (n := 1)).differentiableAt one_ne_zero),
    partialDeriv_halfSpaceGreenPotential_eq_setIntegral hF.continuous hFc hFodd,
    partialDeriv_quadrantPotential_ball hfar j hxR,
    ← integral_add (integrableOn_symmetrizedKernel_gradientKernel_of_compact hF.continuous hFc
      hFodd j x) (integrableOn_symmetrizedKernel_gradientKernel_of_far hfar j hxR)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  simp only [hFeq (le_of_lt hy.2), nearPart, farPart]
  ring

/-- The strain integrand `K₁ ω` of a decaying vorticity is integrable on the quadrant. -/
theorem integrableOn_hessianKernel_mul_quadrant_of_decay :
    IntegrableOn (fun y ↦ hessianKernel 0 1 y * ω y) GreenFunction.quadrant := by
  obtain ⟨R, hR, hxR, F, hF, hFc, hFodd, hFeq, -, -⟩ := exists_local hD 0
  have hfar := isQuadrantFarDensity_farPart hD hR
  have h2 : IntegrableOn (fun y ↦ 1 / 4 *
      (symmetrizedKernel (hessianKernel 1 0) 0 y * farPart R ω y)) GreenFunction.quadrant :=
    (integrableOn_symmetrizedKernel_hessianKernel_of_far hfar 1 0 hxR).const_mul (1 / 4)
  refine ((integrableOn_hessianKernel_mul_quadrant (hF.of_le (by norm_num)) hFc hFodd).add
    h2).congr_fun (fun y _ ↦ ?_) measurableSet_quadrant
  have hk : symmetrizedKernel (hessianKernel 1 0) 0 y = 4 * hessianKernel 0 1 y := by
    rw [show hessianKernel 1 0 = hessianKernel 0 1 from funext hessianKernel_one_zero,
      symmetrizedKernel_zero_one_origin]
  simp only [Pi.add_apply, hk, hFeq (le_of_lt ‹y ∈ GreenFunction.quadrant›.2), nearPart, farPart]
  ring

/-- **Part I (5.67) for a decaying vorticity**: the mixed derivative of the stream from the upper
half-plane tends to `(4/π) ∫_{ℝ²₊₊} K₁ ω` at the origin, so the strain is
`u_x(0) = -(4/π) ∫_{ℝ²₊₊} K₁ ω`. -/
theorem tendsto_partialDeriv_partialDeriv_quadrantPotential :
    Tendsto (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential ω))) (𝓝[HalfSpace.upper 2] 0)
      (𝓝 (4 / Real.pi * ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y)) := by
  obtain ⟨R, hR, hxR, F, hF, hFc, hFodd, hFeq, hdec, -⟩ := exists_local hD 0
  have hfar := isQuadrantFarDensity_farPart hD hR
  -- the two parts near the origin
  have hev : ∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential ω)) =ᶠ[𝓝[HalfSpace.upper 2] 0]
      fun y ↦ (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential F))) y +
        (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential (farPart R ω)))) y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 (by linarith : 0 < R / 2))] with y hyU hyB
    have hloc : quadrantPotential ω =ᶠ[𝓝 y]
        fun z ↦ halfSpaceGreenPotential F z + quadrantPotential (farPart R ω) z :=
      eventually_of_mem (Metric.isOpen_ball.mem_nhds hyB) fun z hz ↦
        hdec z (mem_ball_zero_iff.mp hz)
    rw [PDE.partialDeriv_congr_nhds 0 (hloc.partialDeriv 1)]
    exact partialDeriv_partialDeriv_add 1 0
      (halfSpaceGreenPotential_local_poisson hF.continuous hFc hyU hF.contDiffAt).1
      (contDiffAt_farPart hD hR (mem_ball_zero_iff.mp hyB))
  have hG := tendsto_secondPartialDeriv_halfSpaceGreenPotential_mixed hF hFc 0
  have hfarC : ContinuousAt (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential (farPart R ω)))) 0 :=
    (PDE.contDiffAt_partialDeriv 0 (PDE.contDiffAt_partialDeriv 1 (contDiffAt_farPart hD hR hxR) 1)
      0).continuousAt
  have hsum := hG.add (hfarC.tendsto.mono_left nhdsWithin_le_nhds)
  have hk (y : ℝ^2) : symmetrizedKernel (hessianKernel 1 0) 0 y = 4 * hessianKernel 0 1 y := by
    rw [show hessianKernel 1 0 = hessianKernel 0 1 from funext hessianKernel_one_zero,
      symmetrizedKernel_zero_one_origin]
  have hIF := integrableOn_hessianKernel_mul_quadrant (hF.of_le (by norm_num)) hFc hFodd
  have hIfar : IntegrableOn (fun y ↦ hessianKernel 0 1 y * farPart R ω y)
      GreenFunction.quadrant :=
    IntegrableOn.congr_fun
      ((integrableOn_symmetrizedKernel_hessianKernel_of_far hfar 1 0 hxR).const_mul (1 / 4))
      (fun y _ ↦ by simp only [hk]; ring) measurableSet_quadrant
  have hval : (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential F))) 0 +
      (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (quadrantPotential (farPart R ω)))) 0 =
      4 / Real.pi * ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y := by
    have h1 := pi_mul_partialDeriv_partialDeriv_zero_origin hF hFc hFodd
    have hsplit : ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * ω y =
        (∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * F y) +
          ∫ y in GreenFunction.quadrant, hessianKernel 0 1 y * farPart R ω y := by
      rw [← integral_add hIF hIfar]
      refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
      simp only [hFeq (le_of_lt hy.2), nearPart, farPart]
      ring
    rw [partialDeriv_partialDeriv_quadrantPotential_ball hfar 1 0 hxR]
    simp only [hk, mul_assoc, integral_const_mul]
    rw [hsplit]
    field_simp
    linarith [h1]
  exact (tendsto_congr' hev).mpr (hval ▸ hsum)

/-- The Hessian kernel against the odd extension of the far part is absolutely integrable near a
point `x` with `|x| < R/2`. -/
private theorem integrable_hessianKernel_mul_oddHalfSpaceExtension_farPart {R : ℝ} (hR : 0 < R)
    (j : Fin 2) {x : ℝ^2} (hxR : ‖x‖ < R / 2) :
    Integrable fun y ↦ hessianKernel 0 j (x - y) * oddHalfSpaceExtension (farPart R ω) y := by
  obtain ⟨C, β, hβ, hdec⟩ := hD.decay
  have hcont : ContinuousOn (farPart R ω) {y | 0 ≤ y 1} :=
    ((continuous_const.sub (contDiff_cutoff R (n := 0)).continuous).continuousOn).mul
      hD.contDiffOn.continuousOn
  have hW : AEStronglyMeasurable (oddHalfSpaceExtension (farPart R ω)) volume := by
    refine .sub ((aestronglyMeasurable_indicator_iff (HalfSpace.measurableSet_upper (n := 2))).mpr
        ((hcont.mono fun y (hy : 0 < y 1) ↦ (le_of_lt hy : (0 : ℝ) ≤ y 1)).aestronglyMeasurable
          (HalfSpace.measurableSet_upper (n := 2))))
      ((aestronglyMeasurable_indicator_iff (HalfSpace.isOpen_lower 2).measurableSet).mpr ?_)
    refine ContinuousOn.aestronglyMeasurable ?_ (HalfSpace.isOpen_lower 2).measurableSet
    refine hcont.comp (HalfSpace.reflectLinearIsometryEquiv 2).continuous.continuousOn
      fun y (hy : y 1 < 0) ↦ ?_
    change 0 ≤ (HalfSpace.reflect 2 y) 1
    rw [reflect_two_eq_coordinateReflection_one, PDE.Common.coordinateReflection_apply_same]
    linarith
  have hint := integrable_one_add_norm_rpow hβ
  have hC : 0 ≤ C := by
    have hy : (0 : ℝ) < (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 := by simp
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hdec _ hy))
      (Real.rpow_pos_of_pos (by positivity) _)
  refine Integrable.mono' (hint.const_mul (2 * C * ((1 + R) / R) ^ 2))
    (((measurable_hessianKernel 0 j).comp (measurable_const.sub measurable_id))
      |>.aestronglyMeasurable.mul hW) (Eventually.of_forall fun y ↦ ?_)
  have hr : ‖HalfSpace.reflect 2 y‖ = ‖y‖ := HalfSpace.norm_reflect (n := 2) y
  rcases lt_or_ge ‖y‖ R with hyR | hyR
  · have h0 : oddHalfSpaceExtension (farPart R ω) y = 0 := by
      simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator, farPart,
        cutoff_eq_one hR hyR.le, cutoff_eq_one hR (hr.trans_lt hyR).le, sub_self, zero_mul]
      split_ifs <;> simp
    rw [h0, mul_zero, norm_zero]
    positivity
  -- the odd extension is bounded by the decay of `ω`
  have hWb : |oddHalfSpaceExtension (farPart R ω) y| ≤ C * (1 + ‖y‖) ^ (-β) := by
    have hfar (z : ℝ^2) (hz : 0 < z 1) : |farPart R ω z| ≤ C * (1 + ‖z‖) ^ (-β) :=
      (abs_farPart_le R z).trans (hdec z hz)
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator]
    split_ifs with h1 h2 h2
    · exact absurd h2 (by have : (0 : ℝ) < y 1 := h1; change ¬ (y 1 < 0); linarith)
    · simpa using hfar y h1
    · simpa [abs_neg, hr] using hfar _ ((HalfSpace.mem_upper_reflect_iff (n := 2) (x := y)).mpr h2)
    · simp only [sub_zero, abs_zero]
      positivity
  have hy0 : 0 < ‖y‖ := hR.trans_le hyR
  have hK : |hessianKernel 0 j (x - y)| ≤ 2 / ‖y‖ ^ 2 := by
    have hxy : ‖y‖ / 2 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le y x, norm_sub_rev y x]
    refine (abs_hessianKernel_le 0 j _).trans ?_
    rw [div_le_div_iff₀ (mul_pos two_pos (pow_pos (by linarith) 2)) (by positivity)]
    nlinarith [mul_le_mul hxy hxy (by positivity) (norm_nonneg _)]
  rw [Real.norm_eq_abs, abs_mul, rpow_neg_add_two]
  calc |hessianKernel 0 j (x - y)| * |oddHalfSpaceExtension (farPart R ω) y|
      ≤ 2 / ‖y‖ ^ 2 * (C * (1 + ‖y‖) ^ (-β)) := by gcongr
    _ = 2 * C * (1 + ‖y‖) ^ (-β) * (1 / ‖y‖ ^ 2) := by ring
    _ ≤ 2 * C * (1 + ‖y‖) ^ (-β) * (((1 + R) / R) ^ 2 / (1 + ‖y‖) ^ 2) := by
      have := one_div_sq_le hR hyR
      gcongr
    _ = 2 * C * ((1 + R) / R) ^ 2 * ((1 + ‖y‖) ^ (-β) / (1 + ‖y‖) ^ 2) := by ring

omit hD in
/-- The odd extension of `f + g` is the sum of the odd extensions of `f` and `g`. -/
private theorem oddHalfSpaceExtension_add (f g : ℝ^2 → ℝ) :
    oddHalfSpaceExtension (fun y ↦ f y + g y) =
      fun y ↦ oddHalfSpaceExtension f y + oddHalfSpaceExtension g y := by
  funext y
  simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator]
  split_ifs <;> ring

/-- **Part I (3.1)-(3.4) for a decaying vorticity**: at every point of the open upper
half-plane the velocity gradient is a principal value of the odd extension `W`,
`P.V.∫ k₀ⱼ(x - y) W(y) dy = π (∂ⱼ∂₀Ψ(x) + δ₀ⱼ ω(x)/2)`; the far field enters through an
absolutely convergent integral. -/
theorem hasPrincipalValueAt_partialDeriv_partialDeriv_quadrantPotential (j : Fin 2) {x : ℝ^2}
    (hx : 0 < x 1) :
    PDE.Analysis.HasPrincipalValueAt univ (fun x y ↦ hessianKernel 0 j (x - y))
      (oddHalfSpaceExtension ω) x
      (Real.pi * ((∂[j] (∂[(0 : Fin 2)] (quadrantPotential ω))) x +
        if (0 : Fin 2) = j then ω x / 2 else 0)) := by
  obtain ⟨R, hR, hxR, F, hF, hFc, hFodd, hFeq, -, hev⟩ := exists_local hD x
  have hfar := isQuadrantFarDensity_farPart hD hR
  have hxU : x ∈ HalfSpace.upper 2 := hx
  have hc := hasPrincipalValueAt_partialDeriv_partialDeriv_zero j (hF.of_le (by norm_num)) hFc
    (continuousAt_oddHalfSpaceExtension_of_mem_upper hF.continuous hxU)
  have hfodd : ∀ y, 0 ≤ y 1 → farPart R ω (𝐑 0 y) = -farPart R ω y := fun y hy ↦ by
    simp only [farPart, cutoff_reflect, hD.odd y hy, mul_neg]
  have hint := integrable_hessianKernel_mul_oddHalfSpaceExtension_farPart hD hR j hxR
  have hfp := hasPrincipalValueAt_of_integrable (K := fun x y ↦ hessianKernel 0 j (x - y)) hint
  have hW : oddHalfSpaceExtension F + oddHalfSpaceExtension (farPart R ω) =
      oddHalfSpaceExtension ω := by
    have h2 : oddHalfSpaceExtension (fun y ↦ F y + farPart R ω y) = oddHalfSpaceExtension ω :=
      oddHalfSpaceExtension_congr fun y hy ↦ by
        simp only [hFeq (le_of_lt (show 0 < y 1 from hy)), nearPart, farPart]
        ring
    rw [← h2, oddHalfSpaceExtension_add]
    rfl
  convert hW ▸ hc.add hfp using 1
  have hfold := integral_mul_eq_setIntegral_quadrant_symmetrizedKernel (k := hessianKernel 0 j) x
    (oddHalfSpaceExtension_reflect_zero hfodd) (oddHalfSpaceExtension_reflect_one _) hint
  have hWx : oddHalfSpaceExtension F x = ω x := by
    rw [oddHalfSpaceExtension_eqOn F hxU, hFeq (le_of_lt hx)]
    simp [nearPart, cutoff_eq_one hR (by linarith : ‖x‖ ≤ R)]
  have hfarQ : ∫ y in GreenFunction.quadrant,
      symmetrizedKernel (hessianKernel 0 j) x y * oddHalfSpaceExtension (farPart R ω) y =
      ∫ y in GreenFunction.quadrant, symmetrizedKernel (hessianKernel 0 j) x y * farPart R ω y :=
    setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ by
      simp only [oddHalfSpaceExtension_eqOn _ (show y ∈ HalfSpace.upper 2 from hy.2)]
  rw [hfold, hfarQ, hWx]
  have hsecond : (∂[j] (∂[(0 : Fin 2)] (quadrantPotential ω))) x =
      (∂[j] (∂[(0 : Fin 2)] (halfSpaceGreenPotential F))) x +
        1 / Real.pi * ∫ y in GreenFunction.quadrant,
          symmetrizedKernel (hessianKernel 0 j) x y * farPart R ω y := by
    rw [PDE.partialDeriv_congr_nhds j (hev.partialDeriv 0),
      partialDeriv_partialDeriv_add 0 j
        (halfSpaceGreenPotential_local_poisson hF.continuous hFc hxU hF.contDiffAt).1
        (contDiffAt_farPart hD hR hxR),
      partialDeriv_partialDeriv_quadrantPotential_ball hfar 0 j hxR]
  rw [hsecond]
  field_simp
  ring

end Stream

/-! ### Growth -/

section Growth

/-- A function `C¹` on the closed upper half-plane, zero on its boundary, whose gradient is
`o(|x|)` in the open half-plane, is `o(|x|²)` on the closed half-plane. -/
theorem isLittleO_sq_of_norm_fderiv_le {ψ : ℝ^2 → ℝ}
    (hψ : ContDiffOn ℝ 1 ψ {x | 0 ≤ x 1}) (hb : ∀ x : ℝ^2, x 1 = 0 → ψ x = 0)
    (hgrad : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ^2, 0 < x 1 → r ≤ ‖x‖ →
      ‖fderiv ℝ ψ x‖ ≤ ε * ‖x‖) :
    ψ =o[cocompact (ℝ^2) ⊓ 𝓟 {x | 0 ≤ x 1}] fun x ↦ ‖x‖ ^ 2 := by
  set A : Set (ℝ^2) := {x | 0 ≤ x 1}
  have hcoord : Continuous fun x : ℝ^2 ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  have hopen : IsOpen {x : ℝ^2 | 0 < x 1} := isOpen_lt continuous_const hcoord
  have hconv : Convex ℝ A :=
    convex_halfSpace_ge (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).toLinearMap.isLinear 0
  have hnhds {z : ℝ^2} (hz : 0 < z 1) : A ∈ 𝓝 z :=
    mem_of_superset (hopen.mem_nhds hz) fun z (hz : 0 < z 1) ↦ (le_of_lt hz : 0 ≤ z 1)
  have hU : UniqueDiffOn ℝ A := uniqueDiffOn_convex hconv
    ⟨EuclideanSpace.single 1 1, mem_interior_iff_mem_nhds.mpr (hnhds (by simp))⟩
  refine Asymptotics.IsLittleO.of_bound fun ε hε ↦ ?_
  obtain ⟨r₀, hr₀, hr⟩ := hgrad (ε / 2) (half_pos hε)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℝ^2) r₀).inter_left
    (isClosed_le continuous_const hcoord)).exists_bound_of_continuousOn
      ((hψ.continuousOn_fderivWithin hU le_rfl).mono inter_subset_left)
  set B' := max B 0
  set R₁ := max r₀ (2 * B' / ε) + 1
  have hev : ∀ᶠ x in cocompact (ℝ^2), R₁ ≤ ‖x‖ := by
    rw [← Metric.cobounded_eq_cocompact]
    exact hasBasis_cobounded_norm.mem_of_mem trivial
  rw [eventually_inf_principal]
  filter_upwards [hev] with x hxR hxA
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x 1 from hxA) with hx0 | hxpos
  · rw [hb x hx0.symm, abs_zero]; positivity
  -- the mean value inequality along the segment from the origin
  have hseg : segment ℝ (0 : ℝ^2) x ⊆ A := hconv.segment_subset (by simp [A]) hxA
  have hbound : ∀ y ∈ segment ℝ (0 : ℝ^2) x, ‖fderivWithin ℝ ψ A y‖ ≤ B' + ε / 2 * ‖x‖ := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ Icc (0 : ℝ) 1, t • x = y := by simpa [segment_eq_image] using hy
    have hnorm : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    by_cases hsmall : ‖t • x‖ ≤ r₀
    · have := hB (t • x) ⟨hseg hy, by rwa [Metric.mem_closedBall, dist_zero_right]⟩
      have : 0 ≤ ε / 2 * ‖x‖ := by positivity
      linarith [le_max_left B 0]
    have htpos : 0 < t := ht.1.lt_of_ne <| by rintro rfl; simp [hr₀.le] at hsmall
    have hint : 0 < (t • x) 1 := by simp only [PiLp.smul_apply, smul_eq_mul]; positivity
    rw [fderivWithin_of_mem_nhds (hnhds hint)]
    have := hr (t • x) hint (not_le.mp hsmall).le
    have : ε / 2 * ‖t • x‖ ≤ ε / 2 * ‖x‖ := by
      rw [hnorm]; gcongr; exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    linarith [le_max_right B 0]
  have hmvt := (convex_segment (0 : ℝ^2) x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := ψ) (f' := fderivWithin ℝ ψ A)
    (fun y hy ↦ ((hψ.differentiableOn (by norm_num) y (hseg hy)).hasFDerivWithinAt).mono hseg)
    hbound (left_mem_segment ℝ 0 x) (right_mem_segment ℝ 0 x)
  rw [hb 0 (by simp), sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
  have hB'x : B' ≤ ε / 2 * ‖x‖ := by
    have := (div_le_iff₀ hε).1 (show 2 * B' / ε ≤ ‖x‖ by linarith [le_max_right r₀ (2 * B' / ε)])
    linarith
  calc |ψ x| ≤ (B' + ε / 2 * ‖x‖) * ‖x‖ := hmvt
    _ ≤ (ε / 2 * ‖x‖ + ε / 2 * ‖x‖) * ‖x‖ := by gcongr
    _ = ε * ‖x‖ ^ 2 := by ring

/-- The grouped velocity kernel is bounded by its four poles:
`|gⱼₛ(x, y)| ≤ (2π)⁻¹ (|x - y|⁻¹ + |x - R₀ y|⁻¹ + |x - R₁ y|⁻¹ + |x + y|⁻¹)`. -/
theorem abs_symmetrizedKernel_gradientKernel_le_sum (j : Fin 2) (x y : ℝ^2) :
    |symmetrizedKernel (gradientKernel j) x y| ≤ 1 / (2 * Real.pi) *
      (‖x - y‖⁻¹ + ‖x - 𝐑 0 y‖⁻¹ + ‖x - 𝐑 1 y‖⁻¹ + ‖x - -y‖⁻¹) := by
  unfold symmetrizedKernel
  have h1 := norm_gradientKernel_le j (x - y)
  have h2 := norm_gradientKernel_le j (x - 𝐑 0 y)
  have h3 := norm_gradientKernel_le j (x - 𝐑 1 y)
  have h4 := norm_gradientKernel_le j (x - -y)
  simp only [Real.rpow_neg_one, Real.norm_eq_abs, sub_neg_eq_add] at h1 h2 h3 h4
  rw [sub_neg_eq_add]
  calc |gradientKernel j (x - y) - gradientKernel j (x - 𝐑 0 y) - gradientKernel j (x - 𝐑 1 y) +
        gradientKernel j (x + y)|
      ≤ |gradientKernel j (x - y)| + |gradientKernel j (x - 𝐑 0 y)| +
          |gradientKernel j (x - 𝐑 1 y)| + |gradientKernel j (x + y)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by linarith

/-- Far from the poles, the grouped velocity kernel decays like `|x|/|y|²`. -/
private theorem abs_symmetrizedKernel_gradientKernel_le_far (j : Fin 2) {x y : ℝ^2} (hy : y ≠ 0)
    (hxy : 2 * ‖x‖ ≤ ‖y‖) :
    |symmetrizedKernel (gradientKernel j) x y| ≤ 10 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hq : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 / 4 := by nlinarith [norm_nonneg x]
  have hmain (k : Fin 2)
      (h : |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) :
      |symmetrizedKernel (gradientKernel j) x y| ≤ 10 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by
    have h1 : |4 / Real.pi * x k * hessianKernel 0 1 y| ≤ 2 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
      calc 4 / Real.pi * |x k| * |hessianKernel 0 1 y| ≤
          4 / Real.pi * ‖x‖ * (1 / (2 * ‖y‖ ^ 2)) := by
            gcongr
            · simpa using PiLp.norm_apply_le (p := 2) x k
            · exact abs_hessianKernel_le 0 1 y
        _ = 2 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by field_simp; ring
    have h2 : 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 ≤ 8 / Real.pi * ‖x‖ / ‖y‖ ^ 2 :=
      calc 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 = 32 / Real.pi * ‖x‖ * ‖x‖ ^ 2 / ‖y‖ ^ 4 := by ring
        _ ≤ 32 / Real.pi * ‖x‖ * (‖y‖ ^ 2 / 4) / ‖y‖ ^ 4 := by gcongr
        _ = 8 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by field_simp; ring
    rw [show 10 / Real.pi * ‖x‖ / ‖y‖ ^ 2 =
      8 / Real.pi * ‖x‖ / ‖y‖ ^ 2 + 2 / Real.pi * ‖x‖ / ‖y‖ ^ 2 by ring]
    linarith [abs_sub_abs_le_abs_sub (symmetrizedKernel (gradientKernel j) x y)
      (4 / Real.pi * x k * hessianKernel 0 1 y)]
  fin_cases j
  · exact hmain 1 (abs_symmetrizedKernel_gradientKernel_zero_sub_le hy hxy)
  · exact hmain 0 (abs_symmetrizedKernel_gradientKernel_one_sub_le hy hxy)

variable {ω : ℝ^2 → ℝ} (hD : IsDecayingVorticity ω)
include hD

/-- The weighted tail `|ω(y)|/|y|²` is integrable on the quadrant outside `B(0, a)`. -/
theorem IsDecayingVorticity.integrableOn_abs_div_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y ↦ |ω y| / ‖y‖ ^ 2) (GreenFunction.quadrant ∩ {y | a ≤ ‖y‖}) := by
  obtain ⟨C, β, hβ, hdec⟩ := decay_closed hD
  have hint := integrable_one_add_norm_rpow hβ
  have hS : MeasurableSet (GreenFunction.quadrant ∩ {y : ℝ^2 | a ≤ ‖y‖}) :=
    measurableSet_quadrant.inter (measurableSet_le measurable_const measurable_norm)
  refine Integrable.mono' (hint.const_mul (C * ((1 + a) / a) ^ 2)).integrableOn
    ((((continuousOn_quadrant hD).mono inter_subset_left).abs.div
      (continuous_norm.pow 2).continuousOn fun y hy ↦ pow_ne_zero 2
        (norm_ne_zero_iff.mpr (by rintro rfl; simpa using hy.1.1))).aestronglyMeasurable hS) ?_
  filter_upwards [ae_restrict_mem hS] with y hy
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le ha hy.2
  rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 2),
    rpow_neg_add_two]
  calc |ω y| / ‖y‖ ^ 2 = |ω y| * (1 / ‖y‖ ^ 2) := by ring
    _ ≤ (C * (1 + ‖y‖) ^ (-β)) * (((1 + a) / a) ^ 2 / (1 + ‖y‖) ^ 2) :=
        mul_le_mul (hdec y hy.1) (one_div_sq_le ha hy.2) (by positivity)
          ((abs_nonneg _).trans (hdec y hy.1))
    _ = C * ((1 + a) / a) ^ 2 * ((1 + ‖y‖) ^ (-β) / (1 + ‖y‖) ^ 2) := by ring

/-- The weighted tail `T(a) = ∫_{ℝ²₊₊ ∩ {|y| ≥ a}} |ω|/|y|²` tends to zero. -/
private theorem tendsto_tail :
    Tendsto (fun a ↦ ∫ y in GreenFunction.quadrant ∩ {y | a ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2) atTop
      (𝓝 0) := by
  have hint := hD.integrableOn_abs_div_sq one_pos
  have hm (a : ℝ) : MeasurableSet {y : ℝ^2 | a ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  have heq : (fun a ↦ ∫ y in GreenFunction.quadrant ∩ {y : ℝ^2 | 1 ≤ ‖y‖},
      {y : ℝ^2 | a ≤ ‖y‖}.indicator (fun y ↦ |ω y| / ‖y‖ ^ 2) y) =ᶠ[atTop]
      fun a ↦ ∫ y in GreenFunction.quadrant ∩ {y | a ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with a ha
    rw [setIntegral_indicator (hm a), inter_assoc,
      inter_eq_right.2 (ofPred_subset_ofPred.2 fun y hy ↦ ha.trans hy :
        {y : ℝ^2 | a ≤ ‖y‖} ⊆ {y | 1 ≤ ‖y‖})]
  refine Tendsto.congr' heq ?_
  simpa using tendsto_integral_filter_of_dominated_convergence (f := fun _ ↦ (0 : ℝ))
    (fun y ↦ ‖|ω y| / ‖y‖ ^ 2‖) (.of_forall fun a ↦ hint.aestronglyMeasurable.indicator (hm a))
    (.of_forall fun a ↦ .of_forall fun y ↦ norm_indicator_le_norm_self _ y) hint.norm
    (.of_forall fun y ↦ tendsto_const_nhds.congr' <| by
      filter_upwards [eventually_gt_atTop ‖y‖] with a ha
      rw [indicator_of_notMem (show y ∉ {y : ℝ^2 | a ≤ ‖y‖} from not_le.mpr ha)])

omit hD in
/-- `∫_{B(0, 2|x|)} |x - e y|⁻¹ dy ≤ 6π |x|` for a linear isometry `e`. -/
theorem setIntegral_ball_norm_sub_comp_le (e : ℝ^2 ≃ₗᵢ[ℝ] ℝ^2) {x : ℝ^2}
    (hx : 0 < ‖x‖) :
    IntegrableOn (fun y ↦ ‖x - e y‖⁻¹) (Metric.ball 0 (2 * ‖x‖)) ∧
      ∫ y in Metric.ball 0 (2 * ‖x‖), ‖x - e y‖⁻¹ ≤ 6 * Real.pi * ‖x‖ := by
  have hmp := e.measurePreserving
  have hemb := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpre : e ⁻¹' Metric.ball 0 (2 * ‖x‖) = Metric.ball 0 (2 * ‖x‖) := by
    ext y
    simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  have hsub : Metric.ball (0 : ℝ^2) (2 * ‖x‖) ⊆ Metric.ball x (3 * ‖x‖) := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ < 3 * ‖x‖ := by linarith
  have hI : IntegrableOn (fun y ↦ ‖x - y‖⁻¹) (Metric.ball 0 (2 * ‖x‖)) :=
    (integrableOn_ball_norm_sub_inv x (3 * ‖x‖)).mono_set hsub
  have hval := hmp.setIntegral_preimage_emb hemb (fun y ↦ ‖x - y‖⁻¹) (Metric.ball 0 (2 * ‖x‖))
  rw [hpre] at hval
  have hint := (hmp.integrableOn_comp_preimage hemb (f := fun y ↦ ‖x - y‖⁻¹)).mpr hI
  rw [hpre] at hint
  refine ⟨hint, ?_⟩
  change ∫ y in Metric.ball 0 (2 * ‖x‖), (fun y ↦ ‖x - y‖⁻¹) (e y) ≤ _
  rw [hval]
  calc ∫ y in Metric.ball 0 (2 * ‖x‖), ‖x - y‖⁻¹ ≤ ∫ y in Metric.ball x (3 * ‖x‖), ‖x - y‖⁻¹ :=
        setIntegral_mono_set (integrableOn_ball_norm_sub_inv x (3 * ‖x‖))
          (Eventually.of_forall fun y ↦ inv_nonneg.mpr (norm_nonneg _))
          (Eventually.of_forall hsub)
    _ = 6 * Real.pi * ‖x‖ := by rw [integral_ball_norm_sub_inv x (by positivity)]; ring

/-- **The velocity estimate behind the growth bound.** For `2ρ ≤ |x|` and `|ω| ≤ ε` on the
quadrant outside `B(0, ρ)`,
`|∂ⱼΨ(x)| ≤ 4/(π|x|) ∫_{ℝ²₊₊ ∩ B̄(0,ρ)} |ω| + 12 ε |x| +
(10/π) |x| ∫_{ℝ²₊₊, |y| ≥ 2|x|} |ω|/|y|²`. -/
private theorem abs_partialDeriv_quadrantPotential_le (j : Fin 2) {x : ℝ^2} {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 ≤ ε) (hρx : 2 * ρ ≤ ‖x‖)
    (hωε : ∀ y ∈ GreenFunction.quadrant, ρ < ‖y‖ → |ω y| ≤ ε) :
    |(∂[j] (quadrantPotential ω)) x| ≤
      4 / (Real.pi * ‖x‖) * (∫ y in GreenFunction.quadrant ∩ Metric.closedBall 0 ρ, |ω y|) +
        12 * ε * ‖x‖ + 10 / Real.pi * ‖x‖ *
          ∫ y in GreenFunction.quadrant ∩ {y | 2 * ‖x‖ ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2 := by
  set r := ‖x‖
  have hr : 0 < r := by linarith
  set Q := GreenFunction.quadrant
  set inv : ℝ^2 → ℝ := fun y ↦ ‖x - y‖⁻¹ + ‖x - 𝐑 0 y‖⁻¹ + ‖x - 𝐑 1 y‖⁻¹ + ‖x - -y‖⁻¹
  have hinv (y : ℝ^2) : 0 ≤ inv y := by positivity
  set b1 : ℝ^2 → ℝ := (Metric.closedBall 0 ρ).indicator fun y ↦ 4 / (Real.pi * r) * |ω y|
  set b2 : ℝ^2 → ℝ := (Metric.ball 0 (2 * r)).indicator fun y ↦ ε * (1 / (2 * Real.pi) * inv y)
  set b3 : ℝ^2 → ℝ := {y : ℝ^2 | 2 * r ≤ ‖y‖}.indicator fun y ↦ 10 / Real.pi * r * (|ω y| / ‖y‖ ^ 2)
  have hmB : MeasurableSet (Metric.closedBall (0 : ℝ^2) ρ) := measurableSet_closedBall
  have hmF : MeasurableSet {y : ℝ^2 | 2 * r ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  -- the four poles
  have hpoles := fun (e : ℝ^2 ≃ₗᵢ[ℝ] ℝ^2) ↦ setIntegral_ball_norm_sub_comp_le e hr
  obtain ⟨i1, v1⟩ := hpoles (LinearIsometryEquiv.refl ℝ (ℝ^2))
  have hR (i : Fin 2) : IntegrableOn (fun y ↦ ‖x - 𝐑 i y‖⁻¹) (Metric.ball 0 (2 * r)) ∧
      ∫ y in Metric.ball 0 (2 * r), ‖x - 𝐑 i y‖⁻¹ ≤ 6 * Real.pi * r :=
    hpoles (PDE.Common.coordinateReflectionLinearIsometryEquiv i)
  obtain ⟨⟨i2, v2⟩, ⟨i3, v3⟩⟩ := And.intro (hR 0) (hR 1)
  obtain ⟨i4, v4⟩ := hpoles (LinearIsometryEquiv.neg ℝ)
  simp only [LinearIsometryEquiv.coe_refl, id_eq, LinearIsometryEquiv.coe_neg] at i1 v1 i4 v4
  have hinv_int : IntegrableOn inv (Metric.ball 0 (2 * r)) := ((i1.add i2).add i3).add i4
  -- integrability of the three bounds on the quadrant
  have hb1 : IntegrableOn b1 Q := (integrableOn_indicator_iff hmB.nullMeasurableSet).2 <|
    (continuousOn_const.mul (hD.contDiffOn.continuousOn.abs.mono inter_subset_right))
      |>.integrableOn_compact ((isCompact_closedBall 0 ρ).inter_right (isClosed_le continuous_const
        (EuclideanSpace.proj (1 : Fin 2)).continuous)) |>.mono_set fun y hy ↦ ⟨hy.1, hy.2.2.le⟩
  have hb2 : IntegrableOn b2 Q :=
    (integrableOn_indicator_iff measurableSet_ball.nullMeasurableSet).2 <|
    IntegrableOn.mono_set ((hinv_int.const_mul _).const_mul ε) inter_subset_left
  have hb3 : IntegrableOn b3 Q := (integrableOn_indicator_iff hmF.nullMeasurableSet).2 <|
    IntegrableOn.mono_set ((hD.integrableOn_abs_div_sq (a := 2 * r) (by positivity)).const_mul _)
      fun y hy ↦ ⟨hy.2, hy.1⟩
  -- the pointwise bound
  have hpt : ∀ y ∈ Q, |symmetrizedKernel (gradientKernel j) x y * ω y| ≤ b1 y + b2 y + b3 y := by
    intro y hy
    have hb1n : 0 ≤ b1 y := indicator_nonneg (fun _ _ ↦ by positivity) y
    have hb2n : 0 ≤ b2 y := indicator_nonneg (fun z _ ↦ by have := hinv z; positivity) y
    have hb3n : 0 ≤ b3 y := indicator_nonneg (fun _ _ ↦ by positivity) y
    rw [abs_mul]
    rcases le_or_gt ‖y‖ ρ with h1 | h1
    · -- near the origin: all four poles are at distance at least `r/2`
      have hfar (z : ℝ^2) (hz : ‖z‖ = ‖y‖) : ‖x - z‖⁻¹ ≤ 2 / r := by
        rw [← inv_div]
        exact inv_anti₀ (by positivity) (by linarith [norm_sub_norm_le x z])
      have hnear : |symmetrizedKernel (gradientKernel j) x y| ≤ 4 / (Real.pi * r) := by
        refine (abs_symmetrizedKernel_gradientKernel_le_sum j x y).trans ?_
        calc 1 / (2 * Real.pi) * (‖x - y‖⁻¹ + ‖x - 𝐑 0 y‖⁻¹ + ‖x - 𝐑 1 y‖⁻¹ + ‖x - -y‖⁻¹)
            ≤ 1 / (2 * Real.pi) * (2 / r + 2 / r + 2 / r + 2 / r) := by
              gcongr
              exacts [hfar y rfl, hfar _ (PDE.Common.norm_coordinateReflection 0 y),
                hfar _ (PDE.Common.norm_coordinateReflection 1 y), hfar _ (norm_neg y)]
          _ = 4 / (Real.pi * r) := by field_simp; ring
      have : b1 y = 4 / (Real.pi * r) * |ω y| :=
        indicator_of_mem (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])) _
      have := mul_le_mul_of_nonneg_right hnear (abs_nonneg (ω y))
      linarith
    rcases lt_or_ge ‖y‖ (2 * r) with h2 | h2
    · -- the middle region: `|ω| ≤ ε` and the four poles
      have : b2 y = ε * (1 / (2 * Real.pi) * inv y) := indicator_of_mem (mem_ball_zero_iff.mpr h2) _
      have := mul_le_mul (abs_symmetrizedKernel_gradientKernel_le_sum j x y) (hωε y hy h1)
        (abs_nonneg _) (by have := hinv y; positivity)
      linarith
    · -- the far region
      have hb3y : b3 y = 10 / Real.pi * r * (|ω y| / ‖y‖ ^ 2) :=
        indicator_of_mem (show y ∈ {y : ℝ^2 | 2 * r ≤ ‖y‖} from h2) _
      calc _ ≤ 10 / Real.pi * r / ‖y‖ ^ 2 * |ω y| := by
            gcongr
            exact abs_symmetrizedKernel_gradientKernel_le_far j (by rintro rfl; simpa using hy.1) h2
        _ = b3 y := by rw [hb3y]; ring
        _ ≤ _ := by linarith
  -- integrate
  have e2 : ∫ y in Q, b2 y ≤ 12 * ε * r := by
    have hball : ∫ y in Metric.ball 0 (2 * r), inv y ≤ 24 * Real.pi * r := by
      simp only [inv]
      rw [integral_add (by exact (i1.add i2).add i3) i4, integral_add (by exact i1.add i2) i3,
        integral_add i1 i2]
      linarith
    rw [setIntegral_indicator measurableSet_ball, integral_const_mul, integral_const_mul]
    calc ε * (1 / (2 * Real.pi) * ∫ y in Q ∩ Metric.ball 0 (2 * r), inv y)
        ≤ ε * (1 / (2 * Real.pi) * (24 * Real.pi * r)) := by
          gcongr
          exact (setIntegral_mono_set hinv_int (.of_forall hinv)
            (.of_forall inter_subset_right)).trans hball
      _ = 12 * ε * r := by field_simp; ring
  rw [partialDeriv_quadrantPotential hD j x]
  calc |∫ y in Q, symmetrizedKernel (gradientKernel j) x y * ω y|
      ≤ ∫ y in Q, (b1 + b2 + b3) y := abs_integral_le_integral_abs.trans <|
        integral_mono_of_nonneg (.of_forall fun y ↦ abs_nonneg _) ((hb1.add hb2).add hb3)
          ((ae_restrict_mem measurableSet_quadrant).mono hpt)
    _ = 4 / (Real.pi * r) * (∫ y in Q ∩ Metric.closedBall 0 ρ, |ω y|) + (∫ y in Q, b2 y) +
        10 / Real.pi * r * ∫ y in Q ∩ {y | 2 * r ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2 := by
      rw [integral_add' (hb1.add hb2) hb3, integral_add' hb1 hb2, setIntegral_indicator hmB,
        setIntegral_indicator hmF, integral_const_mul, integral_const_mul]
    _ ≤ _ := by linarith

/-- **Growth**: the grouped potential of a decaying vorticity is `o(|x|²)` on the closed upper
half-plane. -/
theorem quadrantPotential_isLittleO :
    quadrantPotential ω =o[cocompact (ℝ^2) ⊓ 𝓟 {x | 0 ≤ x 1}] fun x ↦ ‖x‖ ^ 2 := by
  refine isLittleO_sq_of_norm_fderiv_le ((contDiffOn_quadrantPotential hD).of_le (by norm_num))
    (fun x hx ↦ quadrantPotential_of_eq_zero ω hx) fun ε hε ↦ ?_
  obtain ⟨C, β, hβ, hdec⟩ := decay_closed hD
  set δ := ε / 72 with hδ_def
  have hδ : 0 < δ := by positivity
  have hlim : Tendsto (fun t : ℝ ↦ C * (1 + t) ^ (-β)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hβ).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa [Function.comp_def] using h.const_mul C
  obtain ⟨ρ₀, hρ₀⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  set ρ := max ρ₀ 1
  have hρ : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hωε : ∀ y ∈ GreenFunction.quadrant, ρ < ‖y‖ → |ω y| ≤ δ := fun y hy h ↦
    (hdec y hy).trans (le_of_lt (hρ₀ ‖y‖ (by linarith [le_max_left ρ₀ 1])))
  set A := ∫ y in GreenFunction.quadrant ∩ Metric.closedBall 0 ρ, |ω y|
  have hA : 0 ≤ A := setIntegral_nonneg (measurableSet_quadrant.inter measurableSet_closedBall)
    fun y _ ↦ abs_nonneg _
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp ((tendsto_tail hD).eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi * ε / 60)))
  set r₀ := max (max (2 * ρ) (a₀ / 2)) (24 * A / (Real.pi * ε) + 1)
  have hr₀ := le_max_left (max (2 * ρ) (a₀ / 2)) (24 * A / (Real.pi * ε) + 1)
  have hr₀' := le_max_right (max (2 * ρ) (a₀ / 2)) (24 * A / (Real.pi * ε) + 1)
  have hA' : 0 ≤ 24 * A / (Real.pi * ε) := by positivity
  refine ⟨r₀, by linarith, fun x _ hrx ↦ ?_⟩
  have hAx : 24 * A / (Real.pi * ε) ≤ ‖x‖ := by linarith
  have hx1 : 1 ≤ ‖x‖ := by linarith
  have hT := ha₀ (2 * ‖x‖) (by linarith [le_max_right (2 * ρ) (a₀ / 2)])
  have hpart (j : Fin 2) : |(∂[j] (quadrantPotential ω)) x| ≤ ε / 2 * ‖x‖ := by
    have h := abs_partialDeriv_quadrantPotential_le hD j hρ hδ.le
      (by linarith [le_max_left (2 * ρ) (a₀ / 2)]) hωε
    have t1 : 4 / (Real.pi * ‖x‖) * A ≤ ε / 6 * ‖x‖ := by
      rw [div_le_iff₀ (by positivity)] at hAx
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hx1) (by positivity : 0 ≤ Real.pi * ε * ‖x‖)]
    have t3 : 10 / Real.pi * ‖x‖ *
        (∫ y in GreenFunction.quadrant ∩ {y | 2 * ‖x‖ ≤ ‖y‖}, |ω y| / ‖y‖ ^ 2) ≤
          ε / 6 * ‖x‖ :=
      calc _ ≤ 10 / Real.pi * ‖x‖ * (Real.pi * ε / 60) := by gcongr
        _ = ε / 6 * ‖x‖ := by field_simp; ring
    linarith [show 12 * δ * ‖x‖ = ε / 6 * ‖x‖ by rw [hδ_def]; ring]
  refine (PDE.norm_fderiv_le_sum_norm_partialDeriv _ x).trans ?_
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  linarith [hpart 0, hpart 1]

end Growth

end IncompressibleFlow

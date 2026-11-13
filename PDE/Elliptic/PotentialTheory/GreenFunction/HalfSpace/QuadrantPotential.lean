/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.SymmetrizedLogKernel
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantSymmetrization
import PDE.Analysis.Complex.PlanarRealPart
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The grouped quadrant potential

For a density `ω` on the open quadrant `ℝ²₊₊`, the grouped potential

`Ψ(x) = ∫_{ℝ²₊₊} Φₛ(x, y) ω(y) dy`, `Φₛ = symmetrizedKernel Φ`, `Φ = fundamentalSolution 2`,

is the stream function of the density `W` odd in both coordinates that equals `ω` on the
quadrant, with the four images grouped in one integrand. Grouping matters for densities that are
not integrable: `Φₛ(x, y) = O(|x|²/|y|²)`, so `Ψ` converges for `|ω(y)| ≲ (1 + |y|)^(-β)` with
any `β > 0`, while `∫ Φ(x - y) W(y) dy` need not converge.

The densities treated here vanish on the quadrant near the origin, `ω = 0` on
`ℝ²₊₊ ∩ B(0, R)`, with `∫_{ℝ²₊₊} |ω(y)|/|y|² dy < ∞`. On `B(0, R/2)` the potential is the real
part of the holomorphic function `G(z) = ∫ H(z, 𝔠 y) ω(y) dy` of `z = x₀ + i x₁`
(`symmetrizedLogKernel`), so it is smooth and harmonic there, with

`∂ⱼΨ(x) = ∫ gⱼₛ(x, y) ω(y) dy` and `∂ₗ∂ₖΨ(x) = π⁻¹ ∫ kₖₗₛ(x, y) ω(y) dy`,

where `gⱼₛ` and `kₖₗₛ` are the four-image symmetrizations of the gradient and Hessian kernels.

## Main definitions

* `quadrantPotential`: the grouped potential `Ψ`.
* `IsQuadrantFarDensity`: `ω` vanishes on `ℝ²₊₊ ∩ B(0, R)`, is measurable there, and `ω(y)/|y|²`
  is integrable on the quadrant.

## Main results

* `contDiffOn_quadrantPotential_ball`: the grouped potential of a far density is smooth on
  `B(0, R/2)`.
* `laplacian_quadrantPotential_ball`: it is harmonic on `B(0, R/2)`.
* `partialDeriv_quadrantPotential_ball`: `∂ⱼΨ(x) = ∫ gⱼₛ(x, y) ω(y) dy` for `|x| < R/2`.
* `partialDeriv_partialDeriv_quadrantPotential_ball`: `∂ₗ∂ₖΨ(x) = π⁻¹ ∫ kₖₗₛ(x, y) ω(y) dy` for
  `|x| < R/2`.
* `abs_partialDeriv_partialDeriv_quadrantPotential_ball_sub_le`: for `|x| < R/2`,
  `|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(0)| ≤ (104/(9π)) |x|² ∫_{ℝ²₊₊} |ω|/|y|⁴`.
* `quadrantPotential_of_eq_zero`, `quadrantPotential_coordinateReflection_zero`: `Ψ` vanishes on
  the boundary line `x₁ = 0` and is odd in `x₀`.
* `integrableOn_symmetrizedKernel_mul`: if `W` is odd in both coordinates and `k(x - ·) W` is
  integrable, the grouped integrand `kₛ(x, ·) W` is integrable on the quadrant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Complex PotentialTheory PotentialTheory.Planar
open scoped Topology ComplexConjugate
open PDE.Common (coordinateReflection_apply_of_ne)

namespace GreenFunction

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- The grouped quadrant potential `Ψ(x) = ∫_{ℝ²₊₊} Φₛ(x, y) ω(y) dy`, with the four images
of the planar fundamental solution in one integrand. -/
def quadrantPotential (ω : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  ∫ y in quadrant, symmetrizedKernel (fundamentalSolution 2) x y * ω y

/-- A point `y` of the open quadrant has nonzero complex coordinate `𝔠 y`. -/
private theorem cx_ne_zero {y : ℝ^2} (hy : y ∈ quadrant) : 𝔠 y ≠ 0 := by
  rw [← norm_pos_iff, LinearIsometryEquiv.norm_map]
  refine norm_pos_iff.mpr fun h ↦ ?_
  have := hy.1
  rw [h] at this
  simp at this

section FarField

variable {f : ℝ^2 → ℝ} {R : ℝ}

/-- The hypotheses on a far density: it vanishes on the quadrant inside `B(0, R)`, is measurable
on the quadrant, and `f(y)/|y|²` is integrable there. -/
structure IsQuadrantFarDensity (f : ℝ^2 → ℝ) (R : ℝ) : Prop where
  /-- The radius is positive. -/
  pos : 0 < R
  /-- The density vanishes on the quadrant inside `B(0, R)`. -/
  eq_zero : ∀ y ∈ quadrant, ‖y‖ < R → f y = 0
  /-- The density is measurable on the quadrant. -/
  aestronglyMeasurable : AEStronglyMeasurable f (volume.restrict quadrant)
  /-- The weighted density `f(y)/|y|²` is integrable on the quadrant. -/
  integrableOn : IntegrableOn (fun y ↦ f y / ‖y‖ ^ 2) quadrant

/-- For fixed `z`, the kernel `y ↦ H(z, 𝔠 y)` is measurable. -/
private theorem measurable_symmetrizedLogKernel (z : ℂ) :
    Measurable fun y : ℝ^2 ↦ symmetrizedLogKernel z (𝔠 y) := by
  unfold symmetrizedLogKernel
  have hc : Continuous (𝔠) := LinearIsometryEquiv.continuous _
  have hcc : Continuous fun y : ℝ^2 ↦ conj (𝔠 y) := continuous_conj.comp hc
  refine measurable_const.mul ((Complex.measurable_log.comp ?_).sub
    (Complex.measurable_log.comp ?_))
  · exact (measurable_const.sub (measurable_const.div (hc.measurable.pow_const 2)))
  · exact (measurable_const.sub (measurable_const.div (hcc.measurable.pow_const 2)))

/-- For fixed `z`, the derivative kernel `y ↦ H'(z, 𝔠 y)` is measurable. -/
private theorem measurable_symmetrizedLogKernelDeriv (z : ℂ) :
    Measurable fun y : ℝ^2 ↦ symmetrizedLogKernelDeriv z (𝔠 y) := by
  unfold symmetrizedLogKernelDeriv
  have hc : Continuous (𝔠) := LinearIsometryEquiv.continuous _
  have hcc : Continuous fun y : ℝ^2 ↦ conj (𝔠 y) := continuous_conj.comp hc
  exact measurable_const.mul ((measurable_const.div
    ((hc.measurable.pow_const 2).sub measurable_const)).sub
    (measurable_const.div ((hcc.measurable.pow_const 2).sub measurable_const)))

/-- For fixed `z`, the second derivative kernel `y ↦ H''(z, 𝔠 y)` is measurable. -/
private theorem measurable_symmetrizedLogKernelSecondDeriv (z : ℂ) :
    Measurable fun y : ℝ^2 ↦ symmetrizedLogKernelSecondDeriv z (𝔠 y) := by
  unfold symmetrizedLogKernelSecondDeriv
  have hc : Continuous (𝔠) := LinearIsometryEquiv.continuous _
  have hcc : Continuous fun y : ℝ^2 ↦ conj (𝔠 y) := continuous_conj.comp hc
  exact measurable_const.mul
    ((((hc.measurable.pow_const 2).add measurable_const).div
      (((hc.measurable.pow_const 2).sub measurable_const).pow_const 2)).sub
    (((hcc.measurable.pow_const 2).add measurable_const).div
      (((hcc.measurable.pow_const 2).sub measurable_const).pow_const 2)))

/-- A kernel bounded by `c/|w|²` against a far density is integrable on the quadrant. -/
private theorem integrable_kernel_mul (hf : IsQuadrantFarDensity f R) {K : ℂ → ℂ → ℂ} {z : ℂ}
    (hK : Measurable fun y : ℝ^2 ↦ K z (𝔠 y)) {c : ℝ}
    (hb : ∀ w : ℂ, w ≠ 0 → R ≤ ‖w‖ → ‖K z w‖ ≤ c / ‖w‖ ^ 2) :
    Integrable (fun y ↦ K z (𝔠 y) * (f y : ℂ)) (volume.restrict quadrant) := by
  have hmeas : AEStronglyMeasurable (fun y ↦ K z (𝔠 y) * (f y : ℂ))
      (volume.restrict quadrant) :=
    hK.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      hf.aestronglyMeasurable)
  refine Integrable.mono' (hf.integrableOn.norm.const_mul |c|) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  by_cases hfy : f y = 0
  · simp [hfy]
  have hR : R ≤ ‖y‖ := not_lt.1 fun h ↦ hfy (hf.eq_zero y hy h)
  have hb' := hb (𝔠 y) (cx_ne_zero hy) (by rw [LinearIsometryEquiv.norm_map]; exact hR)
  rw [LinearIsometryEquiv.norm_map] at hb'
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr (ne_zero_of_mem_quadrant hy)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 2)]
  calc ‖K z (𝔠 y)‖ * |f y| ≤ c / ‖y‖ ^ 2 * |f y| := by gcongr
    _ ≤ |c| * (|f y| / ‖y‖ ^ 2) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        gcongr
        exact le_abs_self c

/-- Holomorphy under the integral sign for a kernel `K(z, w)` holomorphic in `|z| < |w|`
with derivative `K'` bounded by `c'/|w|²` on `2|z| ≤ |w|`. -/
private theorem hasDerivAt_integral_kernel (hf : IsQuadrantFarDensity f R) {K K' : ℂ → ℂ → ℂ}
    (hK : ∀ z w, ‖z‖ < ‖w‖ → HasDerivAt (fun z ↦ K z w) (K' z w) z)
    (hKm : ∀ z, Measurable fun y : ℝ^2 ↦ K z (𝔠 y))
    (hK'm : ∀ z, Measurable fun y : ℝ^2 ↦ K' z (𝔠 y)) {c c' : ℝ}
    (hb : ∀ z w, w ≠ 0 → 2 * ‖z‖ ≤ ‖w‖ → ‖z‖ < R / 2 → ‖K z w‖ ≤ c / ‖w‖ ^ 2)
    (hb' : ∀ z w, w ≠ 0 → 2 * ‖z‖ ≤ ‖w‖ → ‖z‖ < R / 2 → ‖K' z w‖ ≤ c' / ‖w‖ ^ 2)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R / 2) :
    HasDerivAt (fun z ↦ ∫ y in quadrant, K z (𝔠 y) * (f y : ℂ))
      (∫ y in quadrant, K' z₀ (𝔠 y) * (f y : ℂ)) z₀ := by
  set ε := R / 2 - ‖z₀‖ with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hball : ∀ z ∈ Metric.ball z₀ ε, ‖z‖ < R / 2 := fun z hz ↦ by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    linarith [norm_le_norm_add_norm_sub' z z₀]
  have hfar : ∀ z : ℂ, ‖z‖ < R / 2 → ∀ w : ℂ, R ≤ ‖w‖ → 2 * ‖z‖ ≤ ‖w‖ := fun z hz w hw ↦ by
    linarith
  have hfm : AEStronglyMeasurable (fun y ↦ (f y : ℂ)) (volume.restrict quadrant) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict quadrant)
    (F := fun z y ↦ K z (𝔠 y) * (f y : ℂ)) (F' := fun z y ↦ K' z (𝔠 y) * (f y : ℂ))
    (bound := fun y ↦ |c'| * ‖f y / ‖y‖ ^ 2‖) (Metric.ball_mem_nhds z₀ hεpos) ?_ ?_ ?_ ?_ ?_
    ?_).2
  · exact Eventually.of_forall fun z ↦ (hKm z).aestronglyMeasurable.mul hfm
  · exact integrable_kernel_mul hf (hKm z₀) fun w hw hR ↦ hb z₀ w hw (hfar z₀ hz₀ w hR) hz₀
  · exact (hK'm z₀).aestronglyMeasurable.mul hfm
  · filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy z hz
    by_cases hfy : f y = 0
    · simp [hfy]
    have hR : R ≤ ‖y‖ := not_lt.1 fun h ↦ hfy (hf.eq_zero y hy h)
    have hzb := hball z hz
    have hb'' := hb' z (𝔠 y) (cx_ne_zero hy)
      (hfar z hzb _ (by rw [LinearIsometryEquiv.norm_map]; exact hR)) hzb
    rw [LinearIsometryEquiv.norm_map] at hb''
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr (ne_zero_of_mem_quadrant hy)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 2)]
    calc ‖K' z (𝔠 y)‖ * |f y| ≤ c' / ‖y‖ ^ 2 * |f y| := by gcongr
      _ ≤ |c'| * (|f y| / ‖y‖ ^ 2) := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
          gcongr
          exact le_abs_self c'
  · exact hf.integrableOn.norm.const_mul |c'|
  · filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy z hz
    by_cases hfy : f y = 0
    · simp only [hfy, Complex.ofReal_zero, mul_zero]
      exact hasDerivAt_const z 0
    have hR : R ≤ ‖y‖ := not_lt.1 fun h ↦ hfy (hf.eq_zero y hy h)
    have hzb := hball z hz
    have hlt : ‖z‖ < ‖𝔠 y‖ := by rw [LinearIsometryEquiv.norm_map]; linarith [hf.pos]
    exact (hK z (𝔠 y) hlt).mul_const _

/-- The holomorphic far field `G(z) = ∫_{ℝ²₊₊} H(z, 𝔠 y) f(y) dy`. -/
private def farField (f : ℝ^2 → ℝ) (z : ℂ) : ℂ :=
  ∫ y in quadrant, symmetrizedLogKernel z (𝔠 y) * (f y : ℂ)

/-- Its derivative `G'(z) = ∫ H'(z, 𝔠 y) f(y) dy`. -/
private def farFieldDeriv (f : ℝ^2 → ℝ) (z : ℂ) : ℂ :=
  ∫ y in quadrant, symmetrizedLogKernelDeriv z (𝔠 y) * (f y : ℂ)

/-- Its second derivative `G''(z) = ∫ H''(z, 𝔠 y) f(y) dy`. -/
private def farFieldSecondDeriv (f : ℝ^2 → ℝ) (z : ℂ) : ℂ :=
  ∫ y in quadrant, symmetrizedLogKernelSecondDeriv z (𝔠 y) * (f y : ℂ)

/-- For `w ≠ 0`, `2|z| ≤ |w|` and `|z| < R/2`, `|H(z, w)| ≤ (3/(2π)) (R/2)²/|w|²`. -/
private theorem bound_H (z w : ℂ) (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) (hz : ‖z‖ < R / 2) :
    ‖symmetrizedLogKernel z w‖ ≤ 3 / (2 * Real.pi) * (R / 2) ^ 2 / ‖w‖ ^ 2 := by
  refine (norm_symmetrizedLogKernel_le hw h).trans ?_
  rw [mul_div_assoc]
  gcongr

/-- For `w ≠ 0`, `2|z| ≤ |w|` and `|z| < R/2`, `|H'(z, w)| ≤ (8/(3π)) (R/2)/|w|²`. -/
private theorem bound_H' (z w : ℂ) (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) (hz : ‖z‖ < R / 2) :
    ‖symmetrizedLogKernelDeriv z w‖ ≤ 8 / (3 * Real.pi) * (R / 2) / ‖w‖ ^ 2 := by
  refine (norm_symmetrizedLogKernelDeriv_le hw h).trans ?_
  rw [mul_div_assoc]
  gcongr

/-- For `w ≠ 0` and `2|z| ≤ |w|`, `|H''(z, w)| ≤ 2/|w|²`; the hypothesis `|z| < R/2` is not used. -/
private theorem bound_H'' (z w : ℂ) (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) (_hz : ‖z‖ < R / 2) :
    ‖symmetrizedLogKernelSecondDeriv z w‖ ≤ 2 / ‖w‖ ^ 2 :=
  norm_symmetrizedLogKernelSecondDeriv_le hw h

/-- The far field `G` of a far density is holomorphic on `|z| < R/2`, with derivative `G'`. -/
private theorem hasDerivAt_farField (hf : IsQuadrantFarDensity f R) {z : ℂ} (hz : ‖z‖ < R / 2) :
    HasDerivAt (farField f) (farFieldDeriv f z) z :=
  hasDerivAt_integral_kernel hf (fun _ _ h ↦ hasDerivAt_symmetrizedLogKernel h)
    measurable_symmetrizedLogKernel measurable_symmetrizedLogKernelDeriv bound_H bound_H' hz

/-- The derivative `G'` of the far field is holomorphic on `|z| < R/2`, with derivative `G''`. -/
private theorem hasDerivAt_farFieldDeriv (hf : IsQuadrantFarDensity f R) {z : ℂ}
    (hz : ‖z‖ < R / 2) : HasDerivAt (farFieldDeriv f) (farFieldSecondDeriv f z) z :=
  hasDerivAt_integral_kernel hf (fun _ _ h ↦ hasDerivAt_symmetrizedLogKernelDeriv h)
    measurable_symmetrizedLogKernelDeriv measurable_symmetrizedLogKernelSecondDeriv bound_H'
    bound_H'' hz

/-- If `|z| < R/2` and `R ≤ |w|`, then `2|z| ≤ |w|`. -/
private theorem two_mul_norm_le {z : ℂ} (hz : ‖z‖ < R / 2) {w : ℂ} (hw : R ≤ ‖w‖) :
    2 * ‖z‖ ≤ ‖w‖ := by
  linarith

/-- For `|z| < R/2`, `y ↦ H(z, 𝔠 y) f(y)` is integrable on the quadrant. -/
private theorem integrable_H (hf : IsQuadrantFarDensity f R) {z : ℂ} (hz : ‖z‖ < R / 2) :
    Integrable (fun y ↦ symmetrizedLogKernel z (𝔠 y) * (f y : ℂ)) (volume.restrict quadrant) :=
  integrable_kernel_mul hf (measurable_symmetrizedLogKernel z) fun w hw hR ↦
    bound_H z w hw (two_mul_norm_le hz hR) hz

/-- For `|z| < R/2`, `y ↦ H'(z, 𝔠 y) f(y)` is integrable on the quadrant. -/
private theorem integrable_H' (hf : IsQuadrantFarDensity f R) {z : ℂ} (hz : ‖z‖ < R / 2) :
    Integrable (fun y ↦ symmetrizedLogKernelDeriv z (𝔠 y) * (f y : ℂ))
      (volume.restrict quadrant) :=
  integrable_kernel_mul hf (measurable_symmetrizedLogKernelDeriv z) fun w hw hR ↦
    bound_H' z w hw (two_mul_norm_le hz hR) hz

/-- For `|z| < R/2`, `y ↦ H''(z, 𝔠 y) f(y)` is integrable on the quadrant. -/
private theorem integrable_H'' (hf : IsQuadrantFarDensity f R) {z : ℂ} (hz : ‖z‖ < R / 2) :
    Integrable (fun y ↦ symmetrizedLogKernelSecondDeriv z (𝔠 y) * (f y : ℂ))
      (volume.restrict quadrant) :=
  integrable_kernel_mul hf (measurable_symmetrizedLogKernelSecondDeriv z) fun w hw hR ↦
    bound_H'' z w hw (two_mul_norm_le hz hR) hz

/-- `Re(a r e) = Re(a e) r` for real `r`. -/
private theorem re_mul_ofReal_mul (a e : ℂ) (r : ℝ) : (a * (r : ℂ) * e).re = (a * e).re * r := by
  rw [mul_right_comm, Complex.re_mul_ofReal]

/-- `Re(a r e₁ e₂) = Re(a e₁ e₂) r` for real `r`. -/
private theorem re_mul_ofReal_mul_mul (a e₁ e₂ : ℂ) (r : ℝ) :
    (a * (r : ℂ) * e₁ * e₂).re = (a * e₁ * e₂).re * r := by
  rw [show a * (r : ℂ) * e₁ * e₂ = a * e₁ * e₂ * (r : ℂ) by ring, Complex.re_mul_ofReal]

/-- Where the far density does not vanish, the evaluation point is inside the disc of
holomorphy of the kernel. -/
private theorem norm_lt_of_ne_zero (hf : IsQuadrantFarDensity f R) {x y : ℝ^2}
    (hx : ‖x‖ < R / 2) (hy : y ∈ quadrant) (hfy : f y ≠ 0) : ‖x‖ < ‖y‖ := by
  have hR : R ≤ ‖y‖ := not_lt.1 fun h ↦ hfy (hf.eq_zero y hy h)
  linarith [hf.pos]

/-- `|x| < R/2` gives `|𝔠 x| < R/2`. -/
private theorem norm_cx_lt {x : ℝ^2} (hx : ‖x‖ < R / 2) : ‖𝔠 x‖ < R / 2 := by
  rwa [LinearIsometryEquiv.norm_map]

/-- On `B(0, R/2)` the grouped potential of a far density is the real part of `G`. -/
private theorem quadrantPotential_eq_re_farField (hf : IsQuadrantFarDensity f R) {x : ℝ^2}
    (hx : ‖x‖ < R / 2) : quadrantPotential f x = (farField f (𝔠 x)).re := by
  unfold quadrantPotential farField
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm (integrable_H hf (norm_cx_lt hx))]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  by_cases hfy : f y = 0
  · simp [hfy]
  change _ = (symmetrizedLogKernel (𝔠 x) (𝔠 y) * (f y : ℂ)).re
  rw [Complex.re_mul_ofReal, re_symmetrizedLogKernel (norm_lt_of_ne_zero hf hx hy hfy)]

/-- Near every point of `B(0, R/2)` the grouped potential of a far density agrees with `y ↦ Re G(𝔠
y)`. -/
private theorem eventuallyEq_re_farField (hf : IsQuadrantFarDensity f R) {x : ℝ^2}
    (hx : ‖x‖ < R / 2) : quadrantPotential f =ᶠ[𝓝 x] fun y ↦ (farField f (𝔠 y)).re := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
  exact quadrantPotential_eq_re_farField hf (mem_ball_zero_iff.mp hy)

/-- At every point `y` of `B(0, R/2)` the far field `G` has complex derivative `G'(𝔠 y)` at `𝔠 y`.
-/
private theorem hasDerivAt_farField_ball (hf : IsQuadrantFarDensity f R) :
    ∀ y ∈ Metric.ball (0 : ℝ^2) (R / 2), HasDerivAt (farField f) (farFieldDeriv f (𝔠 y)) (𝔠 y) :=
  fun _ hy ↦ hasDerivAt_farField hf (norm_cx_lt (mem_ball_zero_iff.mp hy))

/-- The grouped potential of a far density is integrable against the quadrant for
`|x| < R/2`. -/
theorem integrableOn_symmetrizedKernel_fundamentalSolution_of_far
    (hf : IsQuadrantFarDensity f R) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (fundamentalSolution 2) x y * f y) quadrant := by
  refine ((integrable_H hf (norm_cx_lt hx)).re).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  by_cases hfy : f y = 0
  · simp [hfy]
  simp only [RCLike.re_to_complex, Complex.re_mul_ofReal]
  rw [re_symmetrizedLogKernel (norm_lt_of_ne_zero hf hx hy hfy)]

/-- The symmetrized velocity kernels against a far density are integrable for `|x| < R/2`. -/
theorem integrableOn_symmetrizedKernel_gradientKernel_of_far (hf : IsQuadrantFarDensity f R)
    (j : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (gradientKernel j) x y * f y) quadrant := by
  refine (((integrable_H' hf (norm_cx_lt hx)).mul_const
    (𝔠 (EuclideanSpace.single j 1))).re).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  by_cases hfy : f y = 0
  · simp [hfy]
  simp only [RCLike.re_to_complex]
  rw [re_mul_ofReal_mul, re_symmetrizedLogKernelDeriv_mul j (norm_lt_of_ne_zero hf hx hy hfy)]

/-- The symmetrized velocity-gradient kernels against a far density are integrable for
`|x| < R/2`. -/
theorem integrableOn_symmetrizedKernel_hessianKernel_of_far (hf : IsQuadrantFarDensity f R)
    (i j : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (hessianKernel i j) x y * f y) quadrant := by
  have h := ((((integrable_H'' hf (norm_cx_lt hx)).mul_const
    (𝔠 (EuclideanSpace.single i 1))).mul_const (𝔠 (EuclideanSpace.single j 1))).re).const_mul
      Real.pi
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  by_cases hfy : f y = 0
  · simp [hfy]
  simp only [RCLike.re_to_complex]
  rw [re_mul_ofReal_mul_mul,
    re_symmetrizedLogKernelSecondDeriv_mul_mul i j (norm_lt_of_ne_zero hf hx hy hfy)]
  field_simp

/-- **Regularity of the far potential**: the grouped potential of a density vanishing on
`ℝ²₊₊ ∩ B(0, R)` is smooth on `B(0, R/2)`. -/
theorem contDiffOn_quadrantPotential_ball (hf : IsQuadrantFarDensity f R) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (quadrantPotential f) (Metric.ball 0 (R / 2)) := by
  have hG : DifferentiableOn ℂ (farField f) (Metric.ball 0 (R / 2)) := fun z hz ↦
    (hasDerivAt_farField hf (mem_ball_zero_iff.mp hz)).differentiableAt.differentiableWithinAt
  have h := PDE.Analysis.contDiffOn_re_comp Metric.isOpen_ball hG (n := n)
  have hpre : (𝔠) ⁻¹' Metric.ball (0 : ℂ) (R / 2) = Metric.ball 0 (R / 2) := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  rw [hpre] at h
  exact h.congr fun x hx ↦ quadrantPotential_eq_re_farField hf (mem_ball_zero_iff.mp hx)

/-- **Velocity of the far potential**: `∂ⱼΨ(x) = ∫ gⱼₛ(x, y) f(y) dy` for `|x| < R/2`. -/
theorem partialDeriv_quadrantPotential_ball (hf : IsQuadrantFarDensity f R) (j : Fin 2)
    {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    (∂[j] (quadrantPotential f)) x =
      ∫ y in quadrant, symmetrizedKernel (gradientKernel j) x y * f y := by
  rw [PDE.partialDeriv_congr_nhds j (eventuallyEq_re_farField hf hx),
    PDE.Analysis.partialDeriv_re_comp j (hasDerivAt_farField hf (norm_cx_lt hx)), farFieldDeriv,
    ← integral_mul_const, ← Complex.reCLM_apply,
    ← Complex.reCLM.integral_comp_comm ((integrable_H' hf (norm_cx_lt hx)).mul_const _)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  by_cases hfy : f y = 0
  · simp [hfy]
  simp only [Complex.reCLM_apply]
  rw [re_mul_ofReal_mul, re_symmetrizedLogKernelDeriv_mul j (norm_lt_of_ne_zero hf hx hy hfy)]

/-- The second derivatives of the far potential as real parts of `G''`. -/
private theorem partialDeriv_partialDeriv_quadrantPotential_eq_re (hf : IsQuadrantFarDensity f R)
    (k l : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    (∂[l] (∂[k] (quadrantPotential f))) x =
      (farFieldSecondDeriv f (𝔠 x) * 𝔠 (EuclideanSpace.single k 1) *
        𝔠 (EuclideanSpace.single l 1)).re := by
  have hev : ∂[k] (quadrantPotential f) =ᶠ[𝓝 x] ∂[k] (fun y ↦ (farField f (𝔠 y)).re) :=
    (eventuallyEq_re_farField hf hx).partialDeriv k
  rw [PDE.partialDeriv_congr_nhds l hev,
    PDE.Analysis.partialDeriv_partialDeriv_re_comp k l Metric.isOpen_ball
      (hasDerivAt_farField_ball hf) (mem_ball_zero_iff.mpr hx)
      (hasDerivAt_farFieldDeriv hf (norm_cx_lt hx))]

/-- **Velocity gradient of the far potential**:
`∂ₗ∂ₖΨ(x) = π⁻¹ ∫ kₖₗₛ(x, y) f(y) dy` for `|x| < R/2`. -/
theorem partialDeriv_partialDeriv_quadrantPotential_ball (hf : IsQuadrantFarDensity f R)
    (k l : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    (∂[l] (∂[k] (quadrantPotential f))) x =
      1 / Real.pi * ∫ y in quadrant, symmetrizedKernel (hessianKernel k l) x y * f y := by
  rw [partialDeriv_partialDeriv_quadrantPotential_eq_re hf k l hx,
    farFieldSecondDeriv, ← integral_mul_const, ← integral_mul_const, ← Complex.reCLM_apply,
    ← Complex.reCLM.integral_comp_comm
      (((integrable_H'' hf (norm_cx_lt hx)).mul_const _).mul_const _),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  by_cases hfy : f y = 0
  · simp [hfy]
  simp only [Complex.reCLM_apply]
  rw [re_mul_ofReal_mul_mul,
    re_symmetrizedLogKernelSecondDeriv_mul_mul k l (norm_lt_of_ne_zero hf hx hy hfy)]
  ring

/-- `f(y)/|y|⁴` is integrable on the quadrant for a far density. -/
theorem IsQuadrantFarDensity.integrableOn_div_pow_four (hf : IsQuadrantFarDensity f R) :
    IntegrableOn (fun y ↦ f y / ‖y‖ ^ 4) quadrant := by
  have hR := hf.pos
  have hm : AEStronglyMeasurable (fun y ↦ f y / ‖y‖ ^ 4) (volume.restrict quadrant) := by
    have hinv : Measurable fun y : ℝ^2 ↦ (‖y‖ ^ 4)⁻¹ := (measurable_norm.pow_const 4).inv
    have h := hf.aestronglyMeasurable.mul hinv.aestronglyMeasurable
    simp only [div_eq_mul_inv]
    exact h
  refine Integrable.mono' (hf.integrableOn.norm.const_mul (1 / R ^ 2)) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
  by_cases hfy : f y = 0
  · simp only [hfy, zero_div, norm_zero]
    positivity
  have hRy : R ≤ ‖y‖ := not_lt.1 fun h ↦ hfy (hf.eq_zero y hy h)
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hRy
  rw [norm_div, norm_div, Real.norm_eq_abs, norm_pow, norm_norm, norm_pow, norm_norm,
    show ‖y‖ ^ 4 = ‖y‖ ^ 2 * ‖y‖ ^ 2 by ring, ← div_div,
    show 1 / R ^ 2 * (|f y| / ‖y‖ ^ 2) = |f y| / ‖y‖ ^ 2 / R ^ 2 by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hR.le hRy 2)

/-- **The far velocity gradient vanishes quadratically at the origin**: for `|x| < R/2`,
`|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(0)| ≤ (104/(9π)) |x|² ∫_{ℝ²₊₊} |f|/|y|⁴`. -/
theorem abs_partialDeriv_partialDeriv_quadrantPotential_ball_sub_le
    (hf : IsQuadrantFarDensity f R) (k l : Fin 2) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    |(∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential f))) 0| ≤
      104 / (9 * Real.pi) * ‖x‖ ^ 2 * ∫ y in quadrant, |f y| / ‖y‖ ^ 4 := by
  have hR := hf.pos
  have h0 : ‖(0 : ℝ^2)‖ < R / 2 := by rw [norm_zero]; linarith
  rw [partialDeriv_partialDeriv_quadrantPotential_eq_re hf k l hx,
    partialDeriv_partialDeriv_quadrantPotential_eq_re hf k l h0, ← Complex.sub_re, ← sub_mul,
    ← sub_mul]
  have he (i : Fin 2) : ‖𝔠 (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one]
  have hsub : farFieldSecondDeriv f (𝔠 x) - farFieldSecondDeriv f (𝔠 0) =
      ∫ y in quadrant, (symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y) -
        symmetrizedLogKernelSecondDeriv 0 (𝔠 y)) * (f y : ℂ) := by
    unfold farFieldSecondDeriv
    rw [← integral_sub (integrable_H'' hf (norm_cx_lt hx)) (integrable_H'' hf (norm_cx_lt h0))]
    refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
    simp only [map_zero]
    ring
  have hint : Integrable (fun y ↦ 104 / (9 * Real.pi) * ‖x‖ ^ 2 * (|f y| / ‖y‖ ^ 4))
      (volume.restrict quadrant) := by
    have := hf.integrableOn_div_pow_four.norm.const_mul (104 / (9 * Real.pi) * ‖x‖ ^ 2)
    refine this.congr (Eventually.of_forall fun y ↦ ?_)
    simp only [norm_div, Real.norm_eq_abs, norm_pow, abs_norm]
  have hbound : ‖farFieldSecondDeriv f (𝔠 x) - farFieldSecondDeriv f (𝔠 0)‖ ≤
      ∫ y in quadrant, 104 / (9 * Real.pi) * ‖x‖ ^ 2 * (|f y| / ‖y‖ ^ 4) := by
    rw [hsub]
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
    by_cases hfy : f y = 0
    · simp only [hfy, Complex.ofReal_zero, mul_zero, norm_zero, abs_zero, zero_div]
      positivity
    have hRy : R ≤ ‖y‖ := not_lt.1 fun h ↦ hfy (hf.eq_zero y hy h)
    have hb := norm_symmetrizedLogKernelSecondDeriv_sub_le (z := 𝔠 x) (cx_ne_zero hy)
      (by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; linarith)
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y) - symmetrizedLogKernelSecondDeriv 0 (𝔠 y)‖ *
          |f y| ≤ 104 / (9 * Real.pi) * (‖x‖ ^ 2 / ‖y‖ ^ 4) * |f y| := by gcongr
      _ = 104 / (9 * Real.pi) * ‖x‖ ^ 2 * (|f y| / ‖y‖ ^ 4) := by ring
  calc |((farFieldSecondDeriv f (𝔠 x) - farFieldSecondDeriv f (𝔠 0)) *
          𝔠 (EuclideanSpace.single k 1) * 𝔠 (EuclideanSpace.single l 1)).re|
      ≤ ‖(farFieldSecondDeriv f (𝔠 x) - farFieldSecondDeriv f (𝔠 0)) *
          𝔠 (EuclideanSpace.single k 1) * 𝔠 (EuclideanSpace.single l 1)‖ := Complex.abs_re_le_norm _
    _ = ‖farFieldSecondDeriv f (𝔠 x) - farFieldSecondDeriv f (𝔠 0)‖ := by
        rw [norm_mul, norm_mul, he, he, mul_one, mul_one]
    _ ≤ _ := hbound.trans (le_of_eq (integral_const_mul _ _))

/-- **Harmonicity of the far potential** on `B(0, R/2)`. -/
theorem laplacian_quadrantPotential_ball (hf : IsQuadrantFarDensity f R) {x : ℝ^2}
    (hx : ‖x‖ < R / 2) : PDE.laplacian (quadrantPotential f) x = 0 := by
  rw [EuclideanLaplacian.laplacian_congr_nhds (eventuallyEq_re_farField hf hx)]
  exact PDE.Analysis.laplacian_re_comp_eq_zero Metric.isOpen_ball (hasDerivAt_farField_ball hf)
    (mem_ball_zero_iff.mpr hx) (hasDerivAt_farFieldDeriv hf (norm_cx_lt hx))

end FarField

section Symmetry

local notation "𝐑" => PDE.Common.coordinateReflection

/-- If `a₀² + a₁² = b₀² + b₁²`, then `|a| = |b|`. -/
private theorem norm_eq_of_sq {a b : ℝ^2} (h : a 0 ^ 2 + a 1 ^ 2 = b 0 ^ 2 + b 1 ^ 2) :
    ‖a‖ = ‖b‖ := by
  have ha := EuclideanSpace.norm_sq_fin_two a
  have hb := EuclideanSpace.norm_sq_fin_two b
  have : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by rw [ha, hb, h]
  exact (sq_eq_sq₀ (norm_nonneg a) (norm_nonneg b)).mp this

/-- `(R₀ y)₀ = -y₀`. -/
private theorem refl_zero_apply (y : ℝ^2) : (𝐑 0 y) 0 = -y 0 :=
  PDE.Common.coordinateReflection_apply_same 0 y

/-- `(R₁ y)₁ = -y₁`. -/
private theorem refl_one_apply (y : ℝ^2) : (𝐑 1 y) 1 = -y 1 :=
  PDE.Common.coordinateReflection_apply_same 1 y

/-- `(R₁ y)₀ = y₀`. -/
private theorem refl_one_apply_zero (y : ℝ^2) : (𝐑 1 y) 0 = y 0 :=
  PDE.Common.coordinateReflection_apply_of_ne 1 0 (by decide) y

/-- On the boundary line the grouped logarithmic kernel vanishes: `Φₛ(x, y) = 0` for
`x₁ = 0`. -/
theorem symmetrizedKernel_fundamentalSolution_of_eq_zero {x : ℝ^2} (hx : x 1 = 0) (y : ℝ^2) :
    symmetrizedKernel (fundamentalSolution 2) x y = 0 := by
  have e1 : ‖x - 𝐑 1 y‖ = ‖x - y‖ := norm_eq_of_sq (by
    simp only [PiLp.sub_apply, refl_one_apply, refl_one_apply_zero, hx]; ring)
  have e2 : ‖x + y‖ = ‖x - 𝐑 0 y‖ := norm_eq_of_sq (by
    simp only [PiLp.sub_apply, PiLp.add_apply, refl_zero_apply, coordinateReflection_apply_of_ne
        (0 : Fin 2) 1 (by decide), hx]; ring)
  simp only [symmetrizedKernel, fundamentalSolution_two, e1, e2]
  ring

/-- The grouped logarithmic kernel is odd under the reflection of the evaluation point in
`x₀`: `Φₛ(R₀ x, y) = -Φₛ(x, y)`. -/
theorem symmetrizedKernel_fundamentalSolution_coordinateReflection_zero (x y : ℝ^2) :
    symmetrizedKernel (fundamentalSolution 2) (𝐑 0 x) y =
      -symmetrizedKernel (fundamentalSolution 2) x y := by
  have e1 : ‖𝐑 0 x - y‖ = ‖x - 𝐑 0 y‖ := norm_eq_of_sq (by
    simp only [PiLp.sub_apply, refl_zero_apply, coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by
        decide)]; ring)
  have e2 : ‖𝐑 0 x - 𝐑 0 y‖ = ‖x - y‖ := norm_eq_of_sq (by
    simp only [PiLp.sub_apply, refl_zero_apply, coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by
        decide)]; ring)
  have e3 : ‖𝐑 0 x - 𝐑 1 y‖ = ‖x + y‖ := norm_eq_of_sq (by
    simp only [PiLp.sub_apply, PiLp.add_apply, refl_zero_apply, coordinateReflection_apply_of_ne
        (0 : Fin 2) 1 (by decide),
      refl_one_apply, refl_one_apply_zero]; ring)
  have e4 : ‖𝐑 0 x + y‖ = ‖x - 𝐑 1 y‖ := norm_eq_of_sq (by
    simp only [PiLp.sub_apply, PiLp.add_apply, refl_zero_apply, coordinateReflection_apply_of_ne
        (0 : Fin 2) 1 (by decide),
      refl_one_apply, refl_one_apply_zero]; ring)
  simp only [symmetrizedKernel, fundamentalSolution_two, e1, e2, e3, e4]
  ring

/-- The grouped potential vanishes on the boundary line. -/
theorem quadrantPotential_of_eq_zero (ω : ℝ^2 → ℝ) {x : ℝ^2} (hx : x 1 = 0) :
    quadrantPotential ω x = 0 := by
  simp [quadrantPotential, symmetrizedKernel_fundamentalSolution_of_eq_zero hx]

/-- The grouped potential is odd in `x₀`. -/
theorem quadrantPotential_coordinateReflection_zero (ω : ℝ^2 → ℝ) (x : ℝ^2) :
    quadrantPotential ω (𝐑 0 x) = -quadrantPotential ω x := by
  simp only [quadrantPotential, symmetrizedKernel_fundamentalSolution_coordinateReflection_zero,
    neg_mul, integral_neg]

/-- **Grouped integrability.** If `W` is odd in both coordinates and `k(x - ·) W` is integrable,
then the grouped integrand `kₛ(x, ·) W` is integrable on the quadrant. -/
theorem integrableOn_symmetrizedKernel_mul {k W : ℝ^2 → ℝ} (x : ℝ^2)
    (hW₀ : ∀ y, W (𝐑 0 y) = -W y) (hW₁ : ∀ y, W (𝐑 1 y) = -W y)
    (hint : Integrable fun y ↦ k (x - y) * W y) :
    IntegrableOn (fun y ↦ symmetrizedKernel k x y * W y) quadrant := by
  have hemb (i : Fin 2) : MeasurableEmbedding (𝐑 i) :=
    (PDE.Common.coordinateReflectionLinearIsometryEquiv i).toMeasurableEquiv.measurableEmbedding
  have hmp (i : Fin 2) := PDE.Common.measurePreserving_coordinateReflection (n := 2) i
  set g := fun y ↦ k (x - y) * W y
  have h0 : Integrable fun y ↦ g (𝐑 0 y) := ((hmp 0).integrable_comp_emb (hemb 0)).mpr hint
  have h1 : Integrable fun y ↦ g (𝐑 1 y) := ((hmp 1).integrable_comp_emb (hemb 1)).mpr hint
  have h01 : Integrable fun y ↦ g (𝐑 0 (𝐑 1 y)) :=
    ((hmp 1).integrable_comp_emb (hemb 1)).mpr h0
  refine (((hint.add h0).add h1).add h01).integrableOn.congr_fun (fun y _ ↦ ?_)
    measurableSet_quadrant
  have hneg : W (-y) = W y := by
    rw [← coordinateReflection_zero_one, hW₀, hW₁, neg_neg]
  simp only [Pi.add_apply, g, symmetrizedKernel, coordinateReflection_zero_one, hW₀, hW₁, hneg,
    sub_neg_eq_add]
  ring

end Symmetry

end GreenFunction

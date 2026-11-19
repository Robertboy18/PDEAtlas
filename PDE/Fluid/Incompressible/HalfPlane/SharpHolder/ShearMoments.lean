/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearKernel
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainMoments
public import PDE.Analysis.SpecialFunctions.Trigonometric.ArctanEnclosure

/-!
# Moments of the shear kernel over rectangles

For a rectangle `[a₀, a₁] × [t₀, t₁]` with `t₀ > 0`, the integral of `K₂(a, t) (α + β a + γ t)`
is the corner sum (`PDE.Analysis.cornerSum`) of
`shearCorner α β γ a t = α arctan (a/t)/2 + β (t/4) log (a² + t²) - γ (a/4) log (a² + t²)`
(`integral_integral_shearDensity_affine`), with `shearInner α β γ` the primitive in `a`. For the
difference kernel `Δ(p, t) = K₂(p + 1, t) - K₂(p - 1, t)` the two shifts give
`integral_integral_shearDifference_affine`. The angular corner sum is a single arctangent when
`a₀ a₁ ≥ 0` (`cornerSum_shearAngle_eq`), and the logarithmic corner sums are differences of
logarithms of ratios (`cornerSum_shearLogT_eq`, `cornerSum_shearLogA_eq`).

## Main definitions

* `shearInner`: the primitive in `a` of `K₂(a, t) (α + β a + γ t)`.
* `shearCorner`: the mixed primitive of `K₂(a, t) (α + β a + γ t)`.

## Main results

* `integral_integral_shearDensity_affine`:
  `∫_{t₀}^{t₁} ∫_{a₀}^{a₁} K₂(a, t) (α + β a + γ t) da dt` is the corner sum of `shearCorner`.
* `integral_integral_shearDifference_affine`: the cell integral of `Δ(p, t) (α + β p + γ t)` is
  the corner sum of the two shifted mixed primitives.
* `cornerSum_shearCorner`: the corner sum of `shearCorner` splits into the angular and the two
  logarithmic sums.
* `cornerSum_shearAngle_eq`: for `a₀ a₁ ≥ 0` the angular corner sum is `(1/2) arctan (N / D)`
  with `N = (a₁ - a₀)(t₁ - t₀)(a₀ a₁ - t₀ t₁)` and
  `D = (t₁² + a₀ a₁)(t₀² + a₀ a₁) + t₀ t₁ (a₁ - a₀)²`.
* `cornerSum_shearLogT_eq`, `cornerSum_shearLogA_eq`: the corner sums of `(t/4) log (a² + t²)`
  and `(a/4) log (a² + t²)` as logarithms of ratios.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis

namespace IncompressibleFlow.SharpHolder

/-! ### Primitives -/

/-- The primitive in `a` of `K₂(a, t) (α + β a + γ t)`. -/
def shearInner (α β γ a t : ℝ) : ℝ :=
  α * (-a / (2 * (a ^ 2 + t ^ 2))) +
    β * (Real.log (a ^ 2 + t ^ 2) / 4 + t ^ 2 / (2 * (a ^ 2 + t ^ 2))) +
    γ * (-(a * t) / (2 * (a ^ 2 + t ^ 2)))

/-- The mixed primitive of `K₂(a, t) (α + β a + γ t)`. -/
def shearCorner (α β γ a t : ℝ) : ℝ :=
  α * (Real.arctan (a / t) / 2) + β * (t / 4 * Real.log (a ^ 2 + t ^ 2)) -
    γ * (a / 4 * Real.log (a ^ 2 + t ^ 2))

/-- For `t ≠ 0`, the derivative in `a` of `shearInner α β γ a t` is `K₂(a, t) (α + β a + γ t)`. -/
theorem hasDerivAt_shearInner (α β γ : ℝ) {a t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun a ↦ shearInner α β γ a t) (shearDensity a t * (α + β * a + γ * t)) a := by
  have hpos : 0 < a ^ 2 + t ^ 2 := by positivity
  have h1 : HasDerivAt (fun a ↦ 2 * (a ^ 2 + t ^ 2)) (2 * (2 * a)) a := by
    simpa using ((hasDerivAt_pow 2 a).add_const (t ^ 2)).const_mul 2
  have h2 : HasDerivAt (fun a ↦ a ^ 2 + t ^ 2) (2 * a) a := by
    simpa using (hasDerivAt_pow 2 a).add_const (t ^ 2)
  have d0 := (hasDerivAt_id' a).neg.div h1 (by positivity)
  have d1 := ((h2.log hpos.ne').div_const 4).add
    ((hasDerivAt_const a (t ^ 2)).div h1 (by positivity))
  have d2 := ((hasDerivAt_id' a).mul_const t).neg.div h1 (by positivity)
  refine ((d0.const_mul α).add (d1.const_mul β) |>.add (d2.const_mul γ)).congr_deriv ?_
  simp only [Pi.neg_apply, shearDensity_eq]
  field_simp
  ring

/-- For `t ≠ 0`, the derivative in `t` of `shearCorner α β γ a t` is `shearInner α β γ a t`. -/
theorem hasDerivAt_shearCorner (α β γ : ℝ) {a t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t ↦ shearCorner α β γ a t) (shearInner α β γ a t) t := by
  have hpos : 0 < a ^ 2 + t ^ 2 := by positivity
  have h2 : HasDerivAt (fun t ↦ a ^ 2 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (a ^ 2)
  have d0 := (hasDerivAt_arctan_const_div a ht).div_const 2
  have d1 := ((hasDerivAt_id' t).div_const 4).mul (h2.log hpos.ne')
  have d2 := (h2.log hpos.ne').const_mul (a / 4)
  refine ((d0.const_mul α).add (d1.const_mul β) |>.sub (d2.const_mul γ)).congr_deriv ?_
  simp only [shearInner]
  field_simp
  ring

/-- For `0 < t₀ ≤ t₁`, `t ↦ shearInner α β γ a t` is continuous on `[t₀, t₁]`. -/
private theorem continuousOn_shearInner (α β γ : ℝ) (a : ℝ) {t₀ t₁ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ t₁) : ContinuousOn (fun t ↦ shearInner α β γ a t) (uIcc t₀ t₁) := by
  have hd : ∀ t ∈ uIcc t₀ t₁, a ^ 2 + t ^ 2 ≠ 0 := fun t h ↦ by
    have := pos_of_mem_uIcc ht₀ ht h; positivity
  have hd2 : ∀ t ∈ uIcc t₀ t₁, 2 * (a ^ 2 + t ^ 2) ≠ 0 := fun t h ↦ by
    have := pos_of_mem_uIcc ht₀ ht h; positivity
  unfold shearInner
  refine ((continuousOn_const.mul ?_).add (continuousOn_const.mul ?_)).add
    (continuousOn_const.mul ?_)
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) hd2
  · refine ContinuousOn.add (ContinuousOn.div_const (ContinuousOn.log (by fun_prop) hd) 4) ?_
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hd2
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) hd2

/-- **The affine moments of `K₂` over a rectangle** above the axis:
`∫_{t₀}^{t₁} ∫_{a₀}^{a₁} K₂(a, t) (α + β a + γ t) da dt` is the corner sum of `shearCorner`. -/
theorem integral_integral_shearDensity_affine (α β γ : ℝ) {a₀ a₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ t₁) :
    ∫ t in t₀..t₁, ∫ a in a₀..a₁, shearDensity a t * (α + β * a + γ * t) =
      cornerSum (shearCorner α β γ) a₀ a₁ t₀ t₁ := by
  refine integral_integral_eq_cornerSum_swap (k₁ := shearInner α β γ)
    (fun t ht' a _ ↦ hasDerivAt_shearInner α β γ (pos_of_mem_uIcc ht₀ ht ht').ne')
    (fun t ht' ↦ ?_) (fun t ht' ↦ hasDerivAt_shearCorner α β γ
      (pos_of_mem_uIcc ht₀ ht ht').ne')
    (fun t ht' ↦ hasDerivAt_shearCorner α β γ (pos_of_mem_uIcc ht₀ ht ht').ne')
    ((continuousOn_shearInner α β γ a₀ ht₀ ht).intervalIntegrable)
    ((continuousOn_shearInner α β γ a₁ ht₀ ht).intervalIntegrable)
  have ht0 := pos_of_mem_uIcc ht₀ ht ht'
  refine ContinuousOn.intervalIntegrable ?_
  simp only [shearDensity_eq]
  exact ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun a _ ↦ by positivity)
    (by fun_prop)

/-- **The cell integral of the difference kernel with an affine weight.** For `t₀ > 0`,
`∫_{t₀}^{t₁} ∫_{p₀}^{p₁} Δ(p, t) (α + β p + γ t)` is the corner sum of
`shearCorner (α - β) β γ (p + 1) t - shearCorner (α + β) β γ (p - 1) t`. -/
theorem integral_integral_shearDifference_affine (α β γ : ℝ) {p₀ p₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ t₁) :
    ∫ t in t₀..t₁, ∫ p in p₀..p₁, shearDifference p t * (α + β * p + γ * t) =
      cornerSum (fun p t ↦ shearCorner (α - β) β γ (p + 1) t -
        shearCorner (α + β) β γ (p - 1) t) p₀ p₁ t₀ t₁ := by
  refine integral_integral_eq_cornerSum_swap
    (k₁ := fun p t ↦ shearInner (α - β) β γ (p + 1) t - shearInner (α + β) β γ (p - 1) t)
    (fun t ht' p _ ↦ ?_) (fun t ht' ↦ ?_) (fun t ht' ↦ ?_) (fun t ht' ↦ ?_) ?_ ?_
  · have ht0 := (pos_of_mem_uIcc ht₀ ht ht').ne'
    have d₁ := (hasDerivAt_shearInner (α - β) β γ (a := p + 1) ht0).comp_add_const p 1
    have d₂ := (hasDerivAt_shearInner (α + β) β γ (a := p - 1) ht0).comp_sub_const p 1
    refine (d₁.sub d₂).congr_deriv ?_
    simp only [shearDifference]
    ring
  · have ht0 := pos_of_mem_uIcc ht₀ ht ht'
    refine ContinuousOn.intervalIntegrable ?_
    simp only [shearDifference, shearDensity_eq]
    refine ContinuousOn.mul (ContinuousOn.sub ?_ ?_) (by fun_prop)
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun u _ ↦ by positivity
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun u _ ↦ by positivity
  · have ht0 := (pos_of_mem_uIcc ht₀ ht ht').ne'
    exact (hasDerivAt_shearCorner _ _ _ ht0).sub (hasDerivAt_shearCorner _ _ _ ht0)
  · have ht0 := (pos_of_mem_uIcc ht₀ ht ht').ne'
    exact (hasDerivAt_shearCorner _ _ _ ht0).sub (hasDerivAt_shearCorner _ _ _ ht0)
  · exact ((continuousOn_shearInner _ _ _ _ ht₀ ht).sub
      (continuousOn_shearInner _ _ _ _ ht₀ ht)).intervalIntegrable
  · exact ((continuousOn_shearInner _ _ _ _ ht₀ ht).sub
      (continuousOn_shearInner _ _ _ _ ht₀ ht)).intervalIntegrable

/-! ### Evaluation of the corner sums -/

/-- The corner sum of `shearCorner` splits into the angular and the two logarithmic sums. -/
theorem cornerSum_shearCorner (α β γ a₀ a₁ t₀ t₁ : ℝ) :
    cornerSum (shearCorner α β γ) a₀ a₁ t₀ t₁ =
      α * cornerSum (fun a t ↦ Real.arctan (a / t) / 2) a₀ a₁ t₀ t₁ +
        β * cornerSum (fun a t ↦ t / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ -
        γ * cornerSum (fun a t ↦ a / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ := by
  simp only [cornerSum, shearCorner]
  ring

/-- **The angular corner sum** is one arctangent when `a₀ a₁ ≥ 0`:
`(1/2) arctan ((a₁ - a₀)(t₁ - t₀)(a₀ a₁ - t₀ t₁) / ((t₁² + a₀ a₁)(t₀² + a₀ a₁) +
t₀ t₁ (a₁ - a₀)²))`. -/
theorem cornerSum_shearAngle_eq {a₀ a₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) (ha : a₀ ≤ a₁)
    (h : 0 ≤ a₀ * a₁) :
    cornerSum (fun a t ↦ Real.arctan (a / t) / 2) a₀ a₁ t₀ t₁ =
      Real.arctan ((a₁ - a₀) * (t₁ - t₀) * (a₀ * a₁ - t₀ * t₁) /
        ((t₁ ^ 2 + a₀ * a₁) * (t₀ ^ 2 + a₀ * a₁) + t₀ * t₁ * (a₁ - a₀) ^ 2)) / 2 := by
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have hP : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + a₀ * a₁ := fun t htp ↦
    add_pos_of_pos_of_nonneg (by positivity) h
  have hG : ∀ t : ℝ, 0 < t → Real.arctan (a₁ / t) - Real.arctan (a₀ / t) =
      Real.arctan (t * (a₁ - a₀) / (t ^ 2 + a₀ * a₁)) := by
    intro t htp
    have hprod : 0 ≤ a₁ / t * (a₀ / t) := by
      rw [div_mul_div_comm, mul_comm a₁ a₀]
      exact div_nonneg h (by positivity)
    rw [arctan_sub_arctan hprod]
    congr 1
    have hn : t * t + a₁ * a₀ ≠ 0 := by
      have := hP t htp
      nlinarith
    rw [div_sub_div_same, div_mul_div_comm, one_add_div (by positivity), div_div_div_eq,
      div_eq_div_iff (mul_ne_zero htp.ne' hn) (hP t htp).ne']
    ring
  have hG0 : ∀ t : ℝ, 0 < t → 0 ≤ t * (a₁ - a₀) / (t ^ 2 + a₀ * a₁) := fun t htp ↦
    div_nonneg (mul_nonneg htp.le (by linarith)) (hP t htp).le
  have h2 := arctan_sub_arctan (mul_nonneg (hG0 t₁ ht₁) (hG0 t₀ ht₀))
  have p1n := (hP t₁ ht₁).ne'
  have p0n := (hP t₀ ht₀).ne'
  have e1 : t₁ * (a₁ - a₀) / (t₁ ^ 2 + a₀ * a₁) - t₀ * (a₁ - a₀) / (t₀ ^ 2 + a₀ * a₁) =
      (a₁ - a₀) * (t₁ - t₀) * (a₀ * a₁ - t₀ * t₁) / ((t₁ ^ 2 + a₀ * a₁) * (t₀ ^ 2 + a₀ * a₁)) := by
    rw [div_sub_div _ _ p1n p0n]
    congr 1
    ring
  have e2 : 1 + t₁ * (a₁ - a₀) / (t₁ ^ 2 + a₀ * a₁) * (t₀ * (a₁ - a₀) / (t₀ ^ 2 + a₀ * a₁)) =
      ((t₁ ^ 2 + a₀ * a₁) * (t₀ ^ 2 + a₀ * a₁) + t₀ * t₁ * (a₁ - a₀) ^ 2) /
        ((t₁ ^ 2 + a₀ * a₁) * (t₀ ^ 2 + a₀ * a₁)) := by
    rw [div_mul_div_comm, one_add_div (mul_ne_zero p1n p0n)]
    congr 1
    ring
  rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero p1n p0n)] at h2
  simp only [cornerSum]
  linear_combination (1 / 2 : ℝ) * hG t₁ ht₁ - (1 / 2 : ℝ) * hG t₀ ht₀ + (1 / 2 : ℝ) * h2

/-- The corner sum of `(t/4) log (a² + t²)`. -/
theorem cornerSum_shearLogT_eq {a₀ a₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    cornerSum (fun a t ↦ t / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ =
      t₁ / 4 * Real.log ((a₁ ^ 2 + t₁ ^ 2) / (a₀ ^ 2 + t₁ ^ 2)) -
        t₀ / 4 * Real.log ((a₁ ^ 2 + t₀ ^ 2) / (a₀ ^ 2 + t₀ ^ 2)) := by
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have q1 : 0 < a₁ ^ 2 + t₁ ^ 2 := by positivity
  have q2 : 0 < a₀ ^ 2 + t₁ ^ 2 := by positivity
  have q3 : 0 < a₁ ^ 2 + t₀ ^ 2 := by positivity
  have q4 : 0 < a₀ ^ 2 + t₀ ^ 2 := by positivity
  rw [cornerSum, Real.log_div q1.ne' q2.ne', Real.log_div q3.ne' q4.ne']
  ring

/-- The corner sum of `(a/4) log (a² + t²)`. -/
theorem cornerSum_shearLogA_eq {a₀ a₁ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    cornerSum (fun a t ↦ a / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ =
      a₁ / 4 * Real.log ((a₁ ^ 2 + t₁ ^ 2) / (a₁ ^ 2 + t₀ ^ 2)) -
        a₀ / 4 * Real.log ((a₀ ^ 2 + t₁ ^ 2) / (a₀ ^ 2 + t₀ ^ 2)) := by
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have q1 : 0 < a₁ ^ 2 + t₁ ^ 2 := by positivity
  have q2 : 0 < a₀ ^ 2 + t₁ ^ 2 := by positivity
  have q3 : 0 < a₁ ^ 2 + t₀ ^ 2 := by positivity
  have q4 : 0 < a₀ ^ 2 + t₀ ^ 2 := by positivity
  rw [cornerSum, Real.log_div q1.ne' q3.ne', Real.log_div q2.ne' q4.ne']
  ring

end IncompressibleFlow.SharpHolder

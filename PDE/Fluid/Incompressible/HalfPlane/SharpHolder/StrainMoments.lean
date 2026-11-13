/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainKernel
public import PDE.Analysis.Integration.Rectangle.MixedPrimitive

/-!
# Moments of the strain kernel over rectangles

For a rectangle `[u₀, u₁] × [z₀, z₁]` in the open upper half-plane, the integral of
`K₁(u, z) (α + β u + γ z)` is the corner sum (`PDE.Analysis.cornerSum`) of
`strainCorner α β γ u z = α (-(1/4) log (u² + z²)) + β (z/2) arctan (u/z) +
  γ ((u/2) arctan (z/u) - z/2)`
(`integral_integral_strainDensity_affine`), with `strainInner α β γ` the intermediate primitive in
`u`. For the difference kernel `-Δ(s₁, s₂) = K₁(s₁ - 1/2, s₂) - K₁(s₁ + 1/2, s₂)` of the
horizontal Hölder estimate of the strain and an affine weight, the two shifted kernels give
`integral_integral_neg_strainDifference_affine`. The logarithmic corner sum is `(1/4) log` of the
cross ratio `((u₀² + z₁²)(u₁² + z₀²)) / ((u₁² + z₁²)(u₀² + z₀²))` (`cornerSum_strainLog_eq`), and
the unit shifts of the arctangent primitives are single arctangents
(`strainShift₁_eq`).

## Main definitions

* `strainInner`: the primitive in `u` of `K₁(u, z) (α + β u + γ z)`.
* `strainCorner`: the mixed primitive of `K₁(u, z) (α + β u + γ z)`.

## Main results

* `integral_integral_strainDensity_affine`:
  `∫_{z₀}^{z₁} ∫_{u₀}^{u₁} K₁(u, z) (α + β u + γ z) du dz` is the corner sum of `strainCorner`.
* `integral_integral_neg_strainDifference_affine`: for `z₀ > 0` the cell integral
  of `-Δ(s₁, s₂) (p₀ + p₁ s₁ + p₂ s₂)` is the corner sum of the two shifted mixed primitives.
* `cornerSum_strainLog_eq`: the corner sum of `-(1/4) log (u² + z²)` is `(1/4) log` of the cross
  ratio.
* `strainShift₁_eq`: for `u ≥ 0`, `z > 0`,
  `(z/2)(arctan ((u + 1)/z) - arctan (u/z)) = (z/2) arctan (z / (z² + u (u + 1)))`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis

namespace IncompressibleFlow.SharpHolder

/-! ### Primitives -/

/-- `d/dx arctan (x/c) = c / (c² + x²)`; for `c = 0` both sides are `0`. -/
theorem hasDerivAt_arctan_div_const {c : ℝ} (x : ℝ) :
    HasDerivAt (fun x ↦ Real.arctan (x / c)) (c / (c ^ 2 + x ^ 2)) x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hasDerivAt_const x (0 : ℝ)
  have h := ((hasDerivAt_id' x).div_const c).arctan
  refine h.congr_deriv ?_
  have : 0 < c ^ 2 + x ^ 2 := by positivity
  field_simp

/-- `d/dx arctan (c/x) = -c / (c² + x²)` for `x ≠ 0`. -/
theorem hasDerivAt_arctan_const_div (c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x ↦ Real.arctan (c / x)) (-c / (c ^ 2 + x ^ 2)) x := by
  have h := ((hasDerivAt_const x c).div (hasDerivAt_id' x) hx).arctan
  simp only [Pi.div_apply] at h
  refine h.congr_deriv ?_
  have : 0 < c ^ 2 + x ^ 2 := by positivity
  field_simp
  ring

/-- The primitive in `u` of `K₁(u, z) (α + β u + γ z)`. -/
def strainInner (α β γ u z : ℝ) : ℝ :=
  α * (-z / (2 * (u ^ 2 + z ^ 2))) + β * ((Real.arctan (u / z) - u * z / (u ^ 2 + z ^ 2)) / 2) +
    γ * (-z ^ 2 / (2 * (u ^ 2 + z ^ 2)))

/-- The mixed primitive of `K₁(u, z) (α + β u + γ z)`. -/
def strainCorner (α β γ u z : ℝ) : ℝ :=
  α * (-Real.log (u ^ 2 + z ^ 2) / 4) + β * (z / 2 * Real.arctan (u / z)) +
    γ * (u / 2 * Real.arctan (z / u) - z / 2)

/-- For `z ≠ 0`, the derivative in `u` of `strainInner α β γ u z` is `K₁(u, z) (α + β u + γ z)`. -/
theorem hasDerivAt_strainInner (α β γ : ℝ) {u z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun u ↦ strainInner α β γ u z) (strainDensity u z * (α + β * u + γ * z)) u := by
  have hpos : 0 < u ^ 2 + z ^ 2 := by positivity
  have h1 : HasDerivAt (fun u ↦ 2 * (u ^ 2 + z ^ 2)) (2 * (2 * u)) u := by
    simpa using ((hasDerivAt_pow 2 u).add_const (z ^ 2)).const_mul 2
  have h2 : HasDerivAt (fun u ↦ u ^ 2 + z ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (z ^ 2)
  have d0 := (hasDerivAt_const u (-z)).div h1 (by positivity)
  have d1 := ((hasDerivAt_arctan_div_const (c := z) u).sub
    (((hasDerivAt_id' u).mul_const z).div h2 hpos.ne')).div_const 2
  have d2 := (hasDerivAt_const u (-z ^ 2)).div h1 (by positivity)
  refine ((d0.const_mul α).add (d1.const_mul β) |>.add (d2.const_mul γ)).congr_deriv ?_
  rw [strainDensity_eq]
  field_simp
  ring

/-- For `z ≠ 0`, the derivative in `z` of `strainCorner α β γ u z` is `strainInner α β γ u z`. At
`u = 0` the arctangent term in `z / u` is the constant `0`. -/
theorem hasDerivAt_strainCorner (α β γ : ℝ) {u z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun z ↦ strainCorner α β γ u z) (strainInner α β γ u z) z := by
  have hpos : 0 < u ^ 2 + z ^ 2 := by positivity
  have h2 : HasDerivAt (fun z ↦ u ^ 2 + z ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add (u ^ 2)
  have d0 := (h2.log hpos.ne').neg.div_const 4
  have d1 := ((hasDerivAt_id' z).div_const 2).mul (hasDerivAt_arctan_const_div u hz)
  have d2 := ((hasDerivAt_arctan_div_const (c := u) z).const_mul (u / 2)).sub
    ((hasDerivAt_id' z).div_const 2)
  refine ((d0.const_mul α).add (d1.const_mul β) |>.add (d2.const_mul γ)).congr_deriv ?_
  simp only [strainInner]
  field_simp
  ring

/-- For `0 < a ≤ b`, every point of `[a, b]` is positive. -/
theorem pos_of_mem_uIcc {a b x : ℝ} (h₀ : 0 < a) (h : a ≤ b) (hx : x ∈ uIcc a b) :
    0 < x := by
  rw [uIcc_of_le h] at hx
  exact h₀.trans_le hx.1

/-- For `0 < z₀ ≤ z₁`, `z ↦ strainInner α β γ u z` is continuous on `[z₀, z₁]`. -/
private theorem continuousOn_strainInner (α β γ : ℝ) (u : ℝ) {z₀ z₁ : ℝ} (hz₀ : 0 < z₀)
    (hz : z₀ ≤ z₁) : ContinuousOn (fun z ↦ strainInner α β γ u z) (uIcc z₀ z₁) := by
  have hz' : ∀ z ∈ uIcc z₀ z₁, z ≠ 0 := fun z h ↦ (pos_of_mem_uIcc hz₀ hz h).ne'
  have hd : ∀ z ∈ uIcc z₀ z₁, u ^ 2 + z ^ 2 ≠ 0 := fun z h ↦ by
    have := hz' z h; positivity
  unfold strainInner
  refine ((continuousOn_const.mul ?_).add (continuousOn_const.mul ?_)).add
    (continuousOn_const.mul ?_)
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun z h ↦ by
      have := hd z h; positivity
  · refine ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) 2
    · exact Real.continuous_arctan.comp_continuousOn (continuousOn_const.div continuousOn_id hz')
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) hd
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun z h ↦ by
      have := hd z h; positivity

/-- **The affine moments of `K₁` over a rectangle** in the open upper half-plane:
`∫_{z₀}^{z₁} ∫_{u₀}^{u₁} K₁(u, z) (α + β u + γ z) du dz` is the corner sum of `strainCorner`. -/
theorem integral_integral_strainDensity_affine (α β γ : ℝ) {u₀ u₁ z₀ z₁ : ℝ}
    (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) :
    ∫ z in z₀..z₁, ∫ u in u₀..u₁, strainDensity u z * (α + β * u + γ * z) =
      cornerSum (strainCorner α β γ) u₀ u₁ z₀ z₁ := by
  refine integral_integral_eq_cornerSum_swap (k₁ := strainInner α β γ)
    (fun z hz' u _ ↦ hasDerivAt_strainInner α β γ (pos_of_mem_uIcc hz₀ hz hz').ne')
    (fun z hz' ↦ ?_) (fun z hz' ↦ hasDerivAt_strainCorner α β γ (pos_of_mem_uIcc hz₀ hz hz').ne')
    (fun z hz' ↦ hasDerivAt_strainCorner α β γ (pos_of_mem_uIcc hz₀ hz hz').ne')
    ((continuousOn_strainInner α β γ u₀ hz₀ hz).intervalIntegrable)
    ((continuousOn_strainInner α β γ u₁ hz₀ hz).intervalIntegrable)
  have hz0 := pos_of_mem_uIcc hz₀ hz hz'
  refine ContinuousOn.intervalIntegrable ?_
  simp only [strainDensity_eq]
  exact ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun u _ ↦ by positivity)
    (by fun_prop)

/-- **The cell integral of the difference kernel with an affine weight.** For `z₀ > 0`,
`∫_{z₀}^{z₁} ∫_{x₀}^{x₁} -Δ(s₁, s₂) (p₀ + p₁ s₁ + p₂ s₂)` is the corner sum of
`strainCorner (p₀ + p₁/2) p₁ p₂ (s₁ - 1/2) z - strainCorner (p₀ - p₁/2) p₁ p₂ (s₁ + 1/2) z`. -/
theorem integral_integral_neg_strainDifference_affine (p₀ p₁ p₂ : ℝ) {x₀ x₁ z₀ z₁ : ℝ}
    (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) :
    ∫ z in z₀..z₁, ∫ s₁ in x₀..x₁, -strainDifference s₁ z * (p₀ + p₁ * s₁ + p₂ * z) =
      cornerSum (fun s₁ z ↦ strainCorner (p₀ + p₁ / 2) p₁ p₂ (s₁ - 1 / 2) z -
        strainCorner (p₀ - p₁ / 2) p₁ p₂ (s₁ + 1 / 2) z) x₀ x₁ z₀ z₁ := by
  refine integral_integral_eq_cornerSum_swap
    (k₁ := fun s₁ z ↦ strainInner (p₀ + p₁ / 2) p₁ p₂ (s₁ - 1 / 2) z -
      strainInner (p₀ - p₁ / 2) p₁ p₂ (s₁ + 1 / 2) z)
    (fun z hz' s₁ _ ↦ ?_) (fun z hz' ↦ ?_) (fun z hz' ↦ ?_) (fun z hz' ↦ ?_) ?_ ?_
  · have hz0 := (pos_of_mem_uIcc hz₀ hz hz').ne'
    have d₁ := (hasDerivAt_strainInner (p₀ + p₁ / 2) p₁ p₂ (u := s₁ - 1 / 2) hz0).comp_sub_const
      s₁ (1 / 2)
    have d₂ := (hasDerivAt_strainInner (p₀ - p₁ / 2) p₁ p₂ (u := s₁ + 1 / 2) hz0).comp_add_const
      s₁ (1 / 2)
    refine (d₁.sub d₂).congr_deriv ?_
    simp only [strainDifference]
    ring
  · have hz0 := pos_of_mem_uIcc hz₀ hz hz'
    refine ContinuousOn.intervalIntegrable ?_
    simp only [strainDifference, strainDensity_eq]
    refine ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.sub ?_ ?_)) (by fun_prop)
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun u _ ↦ by positivity
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun u _ ↦ by positivity
  · have hz0 := (pos_of_mem_uIcc hz₀ hz hz').ne'
    exact (hasDerivAt_strainCorner _ _ _ hz0).sub (hasDerivAt_strainCorner _ _ _ hz0)
  · have hz0 := (pos_of_mem_uIcc hz₀ hz hz').ne'
    exact (hasDerivAt_strainCorner _ _ _ hz0).sub (hasDerivAt_strainCorner _ _ _ hz0)
  · exact ((continuousOn_strainInner _ _ _ _ hz₀ hz).sub
      (continuousOn_strainInner _ _ _ _ hz₀ hz)).intervalIntegrable
  · exact ((continuousOn_strainInner _ _ _ _ hz₀ hz).sub
      (continuousOn_strainInner _ _ _ _ hz₀ hz)).intervalIntegrable

/-! ### Evaluation of the corner sums -/

/-- The corner sum of `-(1/4) log (u² + z²)` is `(1/4) log` of the cross ratio. -/
theorem cornerSum_strainLog_eq {u₀ u₁ z₀ z₁ : ℝ} (h₀ : 0 < u₀) (hu : u₀ ≤ u₁) :
    cornerSum (fun u z ↦ -Real.log (u ^ 2 + z ^ 2) / 4) u₀ u₁ z₀ z₁ =
      Real.log ((u₀ ^ 2 + z₁ ^ 2) * (u₁ ^ 2 + z₀ ^ 2) /
        ((u₁ ^ 2 + z₁ ^ 2) * (u₀ ^ 2 + z₀ ^ 2))) / 4 := by
  have hu1 : 0 < u₁ := h₀.trans_le hu
  have p1 : 0 < u₀ ^ 2 + z₁ ^ 2 := by positivity
  have p2 : 0 < u₁ ^ 2 + z₀ ^ 2 := by positivity
  have p3 : 0 < u₁ ^ 2 + z₁ ^ 2 := by positivity
  have p4 : 0 < u₀ ^ 2 + z₀ ^ 2 := by positivity
  rw [cornerSum, Real.log_div (by positivity) (by positivity), Real.log_mul p1.ne' p2.ne',
    Real.log_mul p3.ne' p4.ne']
  ring

/-- The unit shift `(z/2)(arctan ((u + 1)/z) - arctan (u/z))` of the first-moment primitive is
`(z/2) arctan (z / (z² + u (u + 1)))` for `u ≥ 0`, `z > 0`. -/
theorem strainShift₁_eq {u z : ℝ} (hu : 0 ≤ u) (hz : 0 < z) :
    z / 2 * Real.arctan ((u + 1) / z) - z / 2 * Real.arctan (u / z) =
      z / 2 * Real.arctan (z / (z ^ 2 + u * (u + 1))) := by
  have hlt : (u + 1) / z * (-(u / z)) < 1 := by
    have : (u + 1) / z * (-(u / z)) ≤ 0 := by
      rw [mul_neg]; exact neg_nonpos.2 (by positivity)
    linarith
  rw [← mul_sub, sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add hlt]
  congr 2
  have h1 : 0 < z ^ 2 + u * (u + 1) := by positivity
  rw [show (u + 1) / z + -(u / z) = 1 / z by field_simp; ring,
    show 1 - (u + 1) / z * -(u / z) = (z ^ 2 + u * (u + 1)) / z ^ 2 by field_simp; ring]
  field_simp

end IncompressibleFlow.SharpHolder

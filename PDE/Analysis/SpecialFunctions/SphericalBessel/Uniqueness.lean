/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Solutions of the spherical Bessel equation that are regular at the origin

For two solutions `f`, `g` of `x ^ 2 y'' + 2 x y' + (x ^ 2 - L) y = 0` on `(0, R)`, the
weighted Wronskian `x ^ 2 (f g' - f' g)` is constant. If `x ^ 2 f'` tends to zero at the
origin, then so does `x ^ 2 f`: once `|t ^ 2 f' t| ≤ ε` on `(0, x₁)`, the mean value inequality
on `[x, x₁]` gives `x ^ 2 |f x| ≤ x ^ 2 |f x₁| + ε x₁`. Comparison with the smooth solution `j_l`
then shows that the constant vanishes. Since `j_l` is positive near the origin, a multiple of
`j_l` agrees with `f` to first order at one point, and uniqueness for the linear system
`(y, y')' = (y', -(2/x) y' - (1 - L/x²) y)`, whose coefficients are bounded on compact
subintervals of `(0, R)`, gives `f = c j_l`. The uniqueness statement is proved for the radial
system `(y, y')' = (y', -(2/x) y' - (μ - L/x²) y)` of every real `μ`
(`eqOn_zero_of_radial_ode`); the spherical Bessel equation is the case `μ = 1`.

## Main results

* `hasDerivAt_sq_mul_wronskian`: the weighted Wronskian of two solutions has derivative zero.
* `eq_smul_sphericalBesselJ_of_ode`: a solution on `(0, R)` with `x ^ 2 f' → 0` at the origin
  is a multiple of `j_l`.
* `eq_smul_sphericalBesselJ_of_ode_of_bounded`: the same for solutions with `f'` bounded on
  `(0, R)`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Nat Filter Set
open scoped Topology

/-- The weighted Wronskian `x ^ 2 (f g' - f' g)` of two solutions of the spherical Bessel
equation has derivative zero. -/
theorem hasDerivAt_sq_mul_wronskian {L : ℝ} {f f' f'' g g' g'' : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f (f' x) x) (hf' : HasDerivAt f' (f'' x) x)
    (hg : HasDerivAt g (g' x) x) (hg' : HasDerivAt g' (g'' x) x)
    (hfode : x ^ 2 * f'' x + 2 * x * f' x + (x ^ 2 - L) * f x = 0)
    (hgode : x ^ 2 * g'' x + 2 * x * g' x + (x ^ 2 - L) * g x = 0) :
    HasDerivAt (fun y ↦ y ^ 2 * (f y * g' y - f' y * g y)) 0 x := by
  have h := (hasDerivAt_pow 2 x).mul ((hf.mul hg').sub (hf'.mul hg))
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.sub_apply, Pi.mul_apply]
  linear_combination f x * hgode - g x * hfode

/-- `j_l` is positive on some interval `(0, δ)`. -/
theorem exists_sphericalBesselJ_pos (l : ℕ) :
    ∃ δ > 0, ∀ x ∈ Ioo 0 δ, 0 < sphericalBesselJ l x := by
  have hcont : ContinuousAt (reducedSphericalBesselJ l) 0 :=
    (differentiable_reducedSphericalBesselJ l).continuous.continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (lt_mem_nhds (reducedSphericalBesselJ_zero_pos l)))
  refine ⟨δ, hδ, fun x hx ↦ ?_⟩
  rw [sphericalBesselJ_eq_pow_mul]
  have hg : 0 < reducedSphericalBesselJ l x := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2
  have := hx.1
  positivity

/-- The coefficient field `(h, h') ↦ (h', -(2 / t) h' - (μ - L / t²) h)` of the first-order
system equivalent to the radial equation `t² h'' + 2 t h' + (μ t² - L) h = 0`. -/
def radialSystemField (μ L t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, -(2 / t) * p.2 - (μ - L / t ^ 2) * p.1)

/-- On `[a, ∞)` with `0 < a`, the coefficient field is Lipschitz with a uniform constant. -/
theorem lipschitzWith_radialSystemField {μ L a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    LipschitzWith (Real.toNNReal (1 + 2 / a + (|μ| + |L| / a ^ 2)))
      (radialSystemField μ L t) := by
  have htpos : 0 < t := ha.trans_le ht
  have h₁ : 2 / t ≤ 2 / a := div_le_div_of_nonneg_left (by norm_num) ha ht
  have h₂ : |μ - L / t ^ 2| ≤ |μ| + |L| / a ^ 2 := by
    calc |μ - L / t ^ 2| ≤ |μ| + |L / t ^ 2| := abs_sub _ _
      _ = |μ| + |L| / t ^ 2 := by rw [abs_div, abs_of_pos (by positivity : 0 < t ^ 2)]
      _ ≤ |μ| + |L| / a ^ 2 := by
          gcongr
  have hK : 0 ≤ 1 + 2 / a + (|μ| + |L| / a ^ 2) := by positivity
  rw [lipschitzWith_iff_dist_le_mul, Real.coe_toNNReal _ hK]
  intro p q
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [radialSystemField]
  set d₁ := |p.1 - q.1|
  set d₂ := |p.2 - q.2|
  have hd₁ : d₁ ≤ max d₁ d₂ := le_max_left _ _
  have hd₂ : d₂ ≤ max d₁ d₂ := le_max_right _ _
  have hm : 0 ≤ max d₁ d₂ := (abs_nonneg _).trans hd₁
  have hsecond : |-(2 / t) * p.2 - (μ - L / t ^ 2) * p.1 -
      (-(2 / t) * q.2 - (μ - L / t ^ 2) * q.1)| ≤
        (2 / a + (|μ| + |L| / a ^ 2)) * max d₁ d₂ := by
    calc |-(2 / t) * p.2 - (μ - L / t ^ 2) * p.1 - (-(2 / t) * q.2 - (μ - L / t ^ 2) * q.1)|
        = |-(2 / t) * (p.2 - q.2) - (μ - L / t ^ 2) * (p.1 - q.1)| := by ring_nf
      _ ≤ |-(2 / t) * (p.2 - q.2)| + |(μ - L / t ^ 2) * (p.1 - q.1)| := abs_sub _ _
      _ = (2 / t) * d₂ + |μ - L / t ^ 2| * d₁ := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / t)]
      _ ≤ (2 / a) * max d₁ d₂ + (|μ| + |L| / a ^ 2) * max d₁ d₂ := by
          gcongr
      _ = (2 / a + (|μ| + |L| / a ^ 2)) * max d₁ d₂ := by ring
  apply max_le
  · calc d₂ ≤ max d₁ d₂ := hd₂
      _ ≤ (1 + 2 / a + (|μ| + |L| / a ^ 2)) * max d₁ d₂ :=
          le_mul_of_one_le_left hm (by have : 0 ≤ 2 / a + (|μ| + |L| / a ^ 2) := by positivity
                                       linarith)
  · refine hsecond.trans ?_
    gcongr
    linarith

/-- A solution of the radial equation `r² h'' + 2 r h' + (μ r² - L) h = 0` that vanishes to
first order at an interior point of `(0, R)` vanishes on `(0, R)`. -/
theorem eqOn_zero_of_radial_ode {μ L R x₀ : ℝ} {h h' h'' : ℝ → ℝ}
    (hh : ∀ x ∈ Ioo 0 R, HasDerivAt h (h' x) x)
    (hh' : ∀ x ∈ Ioo 0 R, HasDerivAt h' (h'' x) x)
    (hode : ∀ x ∈ Ioo 0 R, x ^ 2 * h'' x + 2 * x * h' x + (μ * x ^ 2 - L) * h x = 0)
    (hx₀ : x₀ ∈ Ioo 0 R) (h₀ : h x₀ = 0) (h₀' : h' x₀ = 0) :
    ∀ x ∈ Ioo 0 R, h x = 0 := by
  intro x hx
  set a := min x x₀ / 2 with ha
  set b := (max x x₀ + R) / 2 with hb
  have hapos : 0 < a := by
    rw [ha]
    exact half_pos (lt_min hx.1 hx₀.1)
  have hsub : Ioo a b ⊆ Ioo 0 R := by
    intro t ht
    refine ⟨hapos.trans ht.1, ht.2.trans ?_⟩
    rw [hb]
    have := max_lt hx.2 hx₀.2
    linarith
  have hmem (y : ℝ) (hy : y ∈ Ioo 0 R) (hya : min x x₀ ≤ y) (hyb : y ≤ max x x₀) :
      y ∈ Ioo a b := by
    constructor
    · rw [ha]
      have := lt_min hx.1 hx₀.1
      linarith
    · rw [hb]
      have := max_lt hx.2 hx₀.2
      linarith
  set Y : ℝ → ℝ × ℝ := fun t ↦ (h t, h' t)
  have hY : ∀ t ∈ Ioo a b, HasDerivAt Y (radialSystemField μ L t (Y t)) t ∧ Y t ∈ univ := by
    intro t ht
    have ht' := hsub ht
    refine ⟨?_, mem_univ _⟩
    have hd := (hh t ht').prodMk (hh' t ht')
    convert hd using 1
    have htne : t ≠ 0 := ht'.1.ne'
    have := hode t ht'
    simp only [radialSystemField, Y, Prod.mk.injEq, true_and]
    field_simp
    linear_combination -this
  have hZ : ∀ t ∈ Ioo a b, HasDerivAt (fun _ ↦ (0 : ℝ × ℝ))
      (radialSystemField μ L t ((fun _ ↦ (0 : ℝ × ℝ)) t)) t ∧ (0 : ℝ × ℝ) ∈ univ := by
    intro t _
    refine ⟨?_, mem_univ _⟩
    have : radialSystemField μ L t 0 = 0 := by simp [radialSystemField]
    rw [this]
    exact hasDerivAt_const t _
  have hEq := ODE_solution_unique_of_mem_Ioo
    (fun t ht ↦ (lipschitzWith_radialSystemField (μ := μ) (L := L) hapos ht.1.le).lipschitzOnWith
      (s := univ))
    (hmem x₀ hx₀ (min_le_right _ _) (le_max_right _ _)) hY hZ (by simp [Y, h₀, h₀'])
  have := hEq (hmem x hx (min_le_left _ _) (le_max_left _ _))
  simpa [Y] using congrArg Prod.fst this

/-- The coefficient field of the first-order system equivalent to the spherical Bessel
equation, the radial system field with `μ = 1`. -/
def sphericalBesselField (L t : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  radialSystemField 1 L t

/-- On `[a, ∞)` with `0 < a`, the coefficient field is Lipschitz with a uniform constant. -/
theorem lipschitzWith_sphericalBesselField {L a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    LipschitzWith (Real.toNNReal (1 + 2 / a + (1 + |L| / a ^ 2)))
      (sphericalBesselField L t) := by
  have h := lipschitzWith_radialSystemField (μ := 1) (L := L) ha ht
  rw [abs_one] at h
  exact h

/-- A solution of the spherical Bessel equation that vanishes to first order at an interior
point of `(0, R)` vanishes on `(0, R)`. -/
theorem eqOn_zero_of_sphericalBessel_ode {L R x₀ : ℝ} {h h' h'' : ℝ → ℝ}
    (hh : ∀ x ∈ Ioo 0 R, HasDerivAt h (h' x) x)
    (hh' : ∀ x ∈ Ioo 0 R, HasDerivAt h' (h'' x) x)
    (hode : ∀ x ∈ Ioo 0 R, x ^ 2 * h'' x + 2 * x * h' x + (x ^ 2 - L) * h x = 0)
    (hx₀ : x₀ ∈ Ioo 0 R) (h₀ : h x₀ = 0) (h₀' : h' x₀ = 0) :
    ∀ x ∈ Ioo 0 R, h x = 0 :=
  eqOn_zero_of_radial_ode (μ := 1) hh hh' (fun x hx ↦ by rw [one_mul]; exact hode x hx) hx₀ h₀ h₀'

/-- If `f` has derivative `f'` on `(0, R)` and `x ^ 2 f' x → 0` as `x → 0⁺`, then
`x ^ 2 f x → 0`. -/
private theorem tendsto_sq_mul_of_tendsto_sq_mul_deriv {R : ℝ} {f f' : ℝ → ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ Ioo 0 R, HasDerivAt f (f' x) x)
    (hf'₀ : Tendsto (fun x ↦ x ^ 2 * f' x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun x ↦ x ^ 2 * f x) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := ε / (2 * R) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp
    (Metric.tendsto_nhds.mp hf'₀ η hηpos)
  set x₁ := min δ R / 2 with hx₁
  have hm := lt_min hδ hR
  have hx₁pos : 0 < x₁ := half_pos hm
  have hx₁δ : x₁ < δ := by linarith [half_lt_self hm, min_le_left δ R]
  have hx₁R : x₁ < R := by linarith [half_lt_self hm, min_le_right δ R]
  -- The mean value inequality on `[x, x₁]`, where `|f'| ≤ η / x ^ 2`.
  have hbound : ∀ x ∈ Ioo 0 x₁, |x ^ 2 * f x| ≤ x ^ 2 * |f x₁| + η * x₁ := by
    intro x hx
    have hderiv : ∀ t ∈ Icc x x₁, HasDerivWithinAt f (f' t) (Icc x x₁) t := fun t ht ↦
      (hf t ⟨hx.1.trans_le ht.1, ht.2.trans_lt hx₁R⟩).hasDerivWithinAt
    have hxsq : 0 < x ^ 2 := by have := hx.1; positivity
    have hf'le : ∀ t ∈ Ico x x₁, ‖f' t‖ ≤ η / x ^ 2 := by
      intro t ht
      have htpos : 0 < t := hx.1.trans_le ht.1
      have hlt := hsmall ⟨htpos, ht.2.trans hx₁δ⟩
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (sq_nonneg t)] at hlt
      have hxt : x ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hx.1.le ht.1 2
      rw [Real.norm_eq_abs, le_div_iff₀ hxsq]
      nlinarith [abs_nonneg (f' t)]
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hf'le x₁ ⟨hx.2.le, le_rfl⟩
    rw [Real.norm_eq_abs] at hmvt
    have hdiff : x ^ 2 * |f x₁ - f x| ≤ η * x₁ := by
      have hx0 : x ≠ 0 := hx.1.ne'
      calc x ^ 2 * |f x₁ - f x| ≤ x ^ 2 * (η / x ^ 2 * (x₁ - x)) := by gcongr
        _ = η * (x₁ - x) := by field_simp
        _ ≤ η * x₁ := by nlinarith [hx.1]
    have htri : |f x| ≤ |f x₁| + |f x₁ - f x| := by
      calc |f x| = |f x₁ - (f x₁ - f x)| := by rw [sub_sub_cancel]
        _ ≤ |f x₁| + |f x₁ - f x| := abs_sub _ _
    rw [abs_mul, abs_of_pos hxsq]
    nlinarith
  -- Near the origin `x ^ 2 |f x₁| < ε / 2`, and `η x₁ < ε / 2`.
  have hsq : Tendsto (fun x : ℝ ↦ x ^ 2 * |f x₁|) (𝓝[>] 0) (𝓝 0) := by
    have := (((continuous_pow 2).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul_const |f x₁|
    simpa using this
  have hηx₁ : η * x₁ < ε / 2 := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  filter_upwards [Ioo_mem_nhdsGT hx₁pos, Metric.tendsto_nhds.mp hsq (ε / 2) (half_pos hε)]
    with x hx hx'
  rw [Real.dist_eq, sub_zero] at hx' ⊢
  have := hbound x hx
  have := le_abs_self (x ^ 2 * |f x₁|)
  linarith

/-- **Uniqueness of the regular solution**: a solution `f` of the spherical Bessel equation
`x ^ 2 f'' + 2 x f' + (x ^ 2 - l (l + 1)) f = 0` on `(0, R)` with `x ^ 2 f' x → 0` as
`x → 0⁺` is a multiple of `j_l` on `(0, R)`. -/
theorem eq_smul_sphericalBesselJ_of_ode {l : ℕ} {R : ℝ} {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo 0 R, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo 0 R, HasDerivAt f' (f'' x) x)
    (hode : ∀ x ∈ Ioo 0 R,
      x ^ 2 * f'' x + 2 * x * f' x + (x ^ 2 - l * (l + 1)) * f x = 0)
    (hf'₀ : Tendsto (fun x ↦ x ^ 2 * f' x) (𝓝[>] 0) (𝓝 0)) :
    ∃ c, ∀ x ∈ Ioo 0 R, f x = c * sphericalBesselJ l x := by
  rcases le_or_gt R 0 with hR | hR
  · exact ⟨0, fun x hx ↦ absurd (hx.1.trans hx.2) (not_lt.mpr hR)⟩
  have hf₀ := tendsto_sq_mul_of_tendsto_sq_mul_deriv hR hf hf'₀
  set j := sphericalBesselJ l
  set j' := deriv (sphericalBesselJ l)
  set j'' := deriv (deriv (sphericalBesselJ l))
  have hj (x : ℝ) : HasDerivAt j (j' x) x :=
    ((differentiable_sphericalBesselJ l) x).hasDerivAt
  have hj' (x : ℝ) : HasDerivAt j' (j'' x) x := hasDerivAt_deriv_sphericalBesselJ l x
  have hjode (x : ℝ) : x ^ 2 * j'' x + 2 * x * j' x + (x ^ 2 - l * (l + 1)) * j x = 0 :=
    sphericalBesselJ_ode l x
  -- The weighted Wronskian of `f` and `j_l` is constant on `(0, R)`.
  set W : ℝ → ℝ := fun y ↦ y ^ 2 * (f y * j' y - f' y * j y) with hW
  have hWderiv : ∀ x ∈ Ioo 0 R, HasDerivAt W 0 x := fun x hx ↦
    hasDerivAt_sq_mul_wronskian (hf x hx) (hf' x hx) (hj x) (hj' x) (hode x hx) (hjode x)
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx ↦ (hWderiv x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hWderiv x hx).deriv)
  -- The constant is the limit at the origin, which vanishes.
  have hlim : Tendsto W (𝓝[>] 0) (𝓝 0) := by
    have hj₀ : Tendsto j (𝓝[>] 0) (𝓝 (j 0)) :=
      ((differentiable_sphericalBesselJ l).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
    have hj'₀ : Tendsto j' (𝓝[>] 0) (𝓝 (j' 0)) :=
      ((hj' 0).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h := (hf₀.mul hj'₀).sub (hf'₀.mul hj₀)
    rw [zero_mul, zero_mul, sub_zero] at h
    refine h.congr fun y ↦ ?_
    simp only [hW]
    ring
  have hlimC : Tendsto W (𝓝[>] 0) (𝓝 C) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR] with y hy using (hC y hy).symm
  have hC0 : C = 0 := tendsto_nhds_unique hlimC hlim
  -- A point where `j_l` does not vanish.
  obtain ⟨x₀, hx₀, hjx₀⟩ : ∃ x₀ ∈ Ioo 0 R, 0 < j x₀ := by
    obtain ⟨δ, hδ, hpos⟩ := exists_sphericalBesselJ_pos l
    have hm := lt_min hδ hR
    refine ⟨min δ R / 2, ⟨half_pos hm, ?_⟩, hpos _ ⟨half_pos hm, ?_⟩⟩
    · linarith [half_lt_self hm, min_le_right δ R]
    · linarith [half_lt_self hm, min_le_left δ R]
  have hjne : j x₀ ≠ 0 := hjx₀.ne'
  obtain ⟨c, hc⟩ : ∃ c, c = f x₀ / j x₀ := ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  -- The difference `f - c j_l` vanishes to first order at `x₀`.
  have hfx₀ : f x₀ = c * j x₀ := by
    rw [hc]
    field_simp
  have h₁ : f x₀ * j' x₀ - f' x₀ * j x₀ = 0 := by
    have hW₀ := hC x₀ hx₀
    rw [hC0, hW] at hW₀
    exact (mul_eq_zero.mp hW₀).resolve_left (pow_ne_zero 2 hx₀.1.ne')
  have hf'x₀ : f' x₀ = c * j' x₀ := by
    rw [hfx₀] at h₁
    have h₂ : (c * j' x₀ - f' x₀) * j x₀ = 0 := by linear_combination h₁
    linarith [(mul_eq_zero.mp h₂).resolve_right hjne]
  have hzero := eqOn_zero_of_sphericalBessel_ode (L := l * (l + 1)) (R := R)
    (h := fun x ↦ f x - c * j x) (h' := fun x ↦ f' x - c * j' x)
    (h'' := fun x ↦ f'' x - c * j'' x)
    (fun x hx ↦ (hf x hx).sub ((hj x).const_mul c))
    (fun x hx ↦ (hf' x hx).sub ((hj' x).const_mul c))
    (fun x hx ↦ by linear_combination hode x hx - c * hjode x) hx₀
    (by simp only [hfx₀, sub_self]) (by simp only [hf'x₀, sub_self])
  intro x hx
  exact sub_eq_zero.mp (hzero x hx)

/-- A solution of the spherical Bessel equation on `(0, R)` with `f'` bounded is a multiple
of `j_l` on `(0, R)`. -/
theorem eq_smul_sphericalBesselJ_of_ode_of_bounded {l : ℕ} {R : ℝ} {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo 0 R, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo 0 R, HasDerivAt f' (f'' x) x)
    (hode : ∀ x ∈ Ioo 0 R,
      x ^ 2 * f'' x + 2 * x * f' x + (x ^ 2 - l * (l + 1)) * f x = 0)
    {M : ℝ} (hbound : ∀ x ∈ Ioo 0 R, |f' x| ≤ M) :
    ∃ c, ∀ x ∈ Ioo 0 R, f x = c * sphericalBesselJ l x := by
  rcases le_or_gt R 0 with hR | hR
  · exact ⟨0, fun x hx ↦ absurd (hx.1.trans hx.2) (not_lt.mpr hR)⟩
  have hsq : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using this
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖x ^ 2 * f' x‖ ≤ M * ‖x ^ 2‖ := by
    filter_upwards [Ioo_mem_nhdsGT hR] with x hx
    rw [norm_mul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)
  refine eq_smul_sphericalBesselJ_of_ode hf hf' hode (squeeze_zero_norm' hev ?_)
  simpa using hsq.norm.const_mul M

end PDE.Analysis.SpecialFunctions

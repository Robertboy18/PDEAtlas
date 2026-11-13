/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.OriginJets
public import PDE.Analysis.Calculus.Taylor.HalfDisc

/-!
# Quantitative Taylor bounds of jet fields at the wall point

Bounds on the upper half disc `{x₁ > 0, |x| < r}` for jet fields whose third partial derivatives
are at most `M` there, with the second-order jets at the origin taken as limits from the open upper
half-plane.

The axis factors come from horizontal integration from the vertical axis, where the odd
derivatives vanish (`PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le`). These are
the near-origin remainders of the strain modes `f̄_{c_ω}` of a profile (Chen and Hou, Part I,
(4.9)) against their second-order jets, as in the lower-order residual terms of Part I,
Sections 6.4.5 and 6.4.9.

## Main results

* `IsOddJetField.abs_sub_le_of_partialDeriv_three_le`: for `f` odd in `x₀`, `a = lim ∂₀f` and
  `p = lim ∂₀∂₁f`: `|f - a x₀ - p x₀ x₁| ≤ 4 M |x₀| |x|²`, `|∂₁f - p x₀| ≤ 2 M |x₀| |x|`,
  `|∂₀²f|, |∂₁²f| ≤ M |x₀|`, and the remainders of `∂₀f` and of the mixed derivatives.
* `IsOddJetField.abs_strainRange_sub_le`: `|f - x₀ ∂₀f + x₁ ∂₁f - p x₀ x₁| ≤ 10 M |x₀| |x|²`; the
  operator `f ↦ f - x₀ ∂₀f + x₁ ∂₁f` kills the linear term and fixes the mixed one.
* `IsEvenAxisJetField.abs_sub_le_of_partialDeriv_three_le`: for `f` even in `x₀`, zero on the
  axis, and `q = lim ∂₀²f`: `|f - (q/2) x₀²| ≤ 2 M x₀² |x|`, `|∂₀f - q x₀| ≤ 2 M |x₀| |x|`,
  `|∂₁f| ≤ M x₀²`, and the second derivatives.
* `IsEvenAxisJetField.abs_strainRange_sub_le`:
  `|3 f - x₀ ∂₀f + x₁ ∂₁f - (q/2) x₀²| ≤ 9 M x₀² |x|`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2, (4.9), and
  Sections 6.4.5 and 6.4.9.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open Filter Set Metric PDE PDE.Common IncompressibleFlow
open scoped Topology

namespace Boussinesq

set_option linter.missingDocs true

section Taylor

/-- The partial derivatives of `h` minus the quadratic polynomial
`c + α x₀ + β x₁ + γ x₀ x₁ + (δ/2) x₀²`. -/
private theorem partialDeriv_sub_quadratic {h : ℝ^2 → ℝ} {x : ℝ^2} (hh : DifferentiableAt ℝ h x)
    (c α β γ δ : ℝ) (k : Fin 2) :
    (∂[k] fun y ↦ h y - (c + α * y 0 + β * y 1 + γ * (y 0 * y 1) + δ / 2 * (y 0 * y 0))) x =
      (∂[k] h) x - (if k = 0 then α + γ * x 1 + δ * x 0 else β + γ * x 0) := by
  have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
    (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
  simp (disch := fun_prop) only [partialDeriv_add, partialDeriv_sub, partialDeriv_mul,
    partialDeriv_coord, partialDeriv_const]
  fin_cases k
  · simp; ring
  · simp

/-- The quadratic polynomial `c + α x₀ + β x₁ + γ x₀ x₁ + (δ/2) x₀²` is differentiable. -/
private theorem differentiableAt_quadratic (c α β γ δ : ℝ) (x : ℝ^2) :
    DifferentiableAt ℝ
      (fun y : ℝ^2 ↦ c + α * y 0 + β * y 1 + γ * (y 0 * y 1) + δ / 2 * (y 0 * y 0)) x := by
  have dc (i : Fin 2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y i) x :=
    (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt
  fun_prop

/-- The quadratic polynomial tends to its constant term at the origin. -/
private theorem tendsto_quadratic (c α β γ δ : ℝ) :
    Tendsto (fun y : ℝ^2 ↦ c + α * y 0 + β * y 1 + γ * (y 0 * y 1) + δ / 2 * (y 0 * y 0))
      (𝓝[upperHalfPlane] 0) (𝓝 c) := by
  have c0 : Continuous fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have c1 : Continuous fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  have h : Continuous fun y : ℝ^2 ↦
      c + α * y 0 + β * y 1 + γ * (y 0 * y 1) + δ / 2 * (y 0 * y 0) := by fun_prop
  have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := upperHalfPlane))
  simpa using this

/-- Radial integration from the origin for `g - c` with `|∂ⱼg| ≤ M`. -/
private theorem abs_sub_le_of_partialDeriv_le {g : ℝ^2 → ℝ} {r M c : ℝ} (hM : 0 ≤ M)
    (hg : Tendsto g (𝓝[upperHalfPlane] 0) (𝓝 c))
    (hd : ∀ y : ℝ^2, 0 < y 1 → DifferentiableAt ℝ g y)
    (hb : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ j : Fin 2, |(∂[j] g) y| ≤ M)
    {x : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) : |g x - c| ≤ 2 * M * ‖x‖ := by
  have h0 : Tendsto (fun y ↦ g y - c) (𝓝[{z : ℝ^2 | 0 < z 1}] 0) (𝓝 0) := by
    have h := hg.sub_const c
    rw [sub_self] at h
    exact h
  have h := PDE.Analysis.abs_le_mul_pow_succ_of_partialDeriv_le (g := fun y ↦ g y - c) (r := r)
    (m := 0) (fun y hy _ ↦ (hd y hy).sub_const c) h0 hM
    (fun y hy hyr j ↦ by
      rw [partialDeriv_sub (hd y hy) (differentiableAt_const c), partialDeriv_const, sub_zero,
        pow_zero, mul_one]
      exact hb y hy hyr j) hx1 hxr
  simpa using h

/-- Horizontal integration from the vertical axis: a function vanishing on the axis with
`|∂₀g| ≤ M` on the half disc `{x₁ > 0, |x| < r}` is at most `M |x₀|` there. -/
private theorem abs_le_mul_abs_of_axis {g : ℝ^2 → ℝ} {r M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ y : ℝ^2, 0 < y 1 → DifferentiableAt ℝ g y)
    (hax : ∀ y : ℝ^2, y 0 = 0 → 0 < y 1 → ‖y‖ < r → g y = 0)
    (hb : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] g) y| ≤ M) {x : ℝ^2} (hx1 : 0 < x 1)
    (hxr : ‖x‖ < r) : |g x| ≤ M * |x 0| := by
  simpa using PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le (a := 0) (m := 0)
    hM (fun z hz _ ↦ hd z hz) hax (fun z hz hzr ↦ by simpa using hb z hz hzr) hx1 hxr

variable {f : ℝ^2 → ℝ} {r M : ℝ}

/-- **Taylor bounds of an odd jet field at the wall point**: if `f` is an odd jet field of
order `3` whose third partial derivatives are at most `M` on the upper half disc
`{x₁ > 0, |x| < r}`, `a = lim ∂₀f` and `p = lim ∂₀∂₁f` at the origin, then on that half disc
`|f - a x₀ - p x₀x₁| ≤ 4 M |x₀| |x|²`, `|∂₀f - a - p x₁| ≤ 4 M |x|²`,
`|∂₁f - p x₀| ≤ 2 M |x₀| |x|`, `|∂₀∂₀f|, |∂₁∂₁f| ≤ M |x₀|` and `|∂₀∂₁f - p|, |∂₁∂₀f - p| ≤ 2 M |x|`.
-/
theorem IsOddJetField.abs_sub_le_of_partialDeriv_three_le (hf : IsOddJetField 3 f) (hM : 0 ≤ M)
    {a p : ℝ} (ha : Tendsto (∂[0] f) (𝓝[upperHalfPlane] 0) (𝓝 a))
    (hp : Tendsto (∂[0] (∂[1] f)) (𝓝[upperHalfPlane] 0) (𝓝 p))
    (h3 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ j k l : Fin 2, |(∂[j] (∂[l] (∂[k] f))) y| ≤ M)
    {x : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) :
    |f x - a * x 0 - p * (x 0 * x 1)| ≤ 4 * M * |x 0| * ‖x‖ ^ 2 ∧
      |(∂[0] f) x - a - p * x 1| ≤ 4 * M * ‖x‖ ^ 2 ∧
      |(∂[1] f) x - p * x 0| ≤ 2 * M * |x 0| * ‖x‖ ∧
      |(∂[0] (∂[0] f)) x| ≤ M * |x 0| ∧ |(∂[1] (∂[1] f)) x| ≤ M * |x 0| ∧
      |(∂[0] (∂[1] f)) x - p| ≤ 2 * M * ‖x‖ ∧ |(∂[1] (∂[0] f)) x - p| ≤ 2 * M * ‖x‖ := by
  have hU := isOpen_upperHalfPlane
  have hσ : ∀ y ∈ upperHalfPlane, coordinateReflection (0 : Fin 2) y ∈ upperHalfPlane :=
    fun _ hy ↦ coordinateReflection_mem_upperHalfPlane hy
  have hc : ContDiffOn ℝ 3 f upperHalfPlane := hf.smooth.contDiffOn
  have ax : ∀ l : List (Fin 2), l.length ≤ 3 → Even (l.count 0) → ∀ y : ℝ^2, y 0 = 0 →
      0 < y 1 → ‖y‖ < r → iteratedPartialDeriv l f y = 0 := by
    intro l hl he y hy0 hy _
    have h := hf.odd.iteratedPartialDeriv hU hσ l (hc.of_le (by exact_mod_cast hl))
    rw [he.neg_one_pow, mul_one] at h
    exact h.eq_zero_of_apply_eq_zero hy hy0
  have lim : ∀ l : List (Fin 2), l.length ≤ 3 → Even (l.count 0) →
      Tendsto (iteratedPartialDeriv l f) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    fun l hl he ↦ hf.smooth.tendsto_zero_of_parity l hl hf.odd (by rw [he.neg_one_pow]; ring)
  have dif : ∀ l : List (Fin 2), l.length ≤ 2 → ∀ y : ℝ^2, 0 < y 1 →
      DifferentiableAt ℝ (iteratedPartialDeriv l f) y :=
    fun l hl y hy ↦ hf.smooth.differentiableAt l (by omega) hy
  have hcomm : EqOn (∂[1] (∂[0] f)) (∂[0] (∂[1] f)) upperHalfPlane :=
    eqOn_partialDeriv_comm (hc.of_le (by norm_num))
  have hp' : Tendsto (∂[1] (∂[0] f)) (𝓝[upperHalfPlane] 0) (𝓝 p) :=
    hp.congr' (eventuallyEq_nhdsWithin_of_eqOn hcomm.symm)
  have l00 : Tendsto (∂[0] (∂[0] f)) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    lim [0, 0] (by norm_num) (by decide)
  have l11 : Tendsto (∂[1] (∂[1] f)) (𝓝[upperHalfPlane] 0) (𝓝 0) :=
    lim [1, 1] (by norm_num) (by decide)
  -- second derivatives
  have e00 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] (∂[0] f)) y| ≤ M * |y 0| :=
    fun y ↦ abs_le_mul_abs_of_axis hM (dif [0, 0] (by norm_num))
      (ax [0, 0] (by norm_num) (by decide)) (fun z hz hzr ↦ h3 z hz hzr 0 0 0)
  have e11 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] (∂[1] f)) y| ≤ M * |y 0| :=
    fun y ↦ abs_le_mul_abs_of_axis hM (dif [1, 1] (by norm_num))
      (ax [1, 1] (by norm_num) (by decide)) (fun z hz hzr ↦ h3 z hz hzr 0 1 1)
  have r00 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] (∂[0] f)) y| ≤ 2 * M * ‖y‖ := by
    intro y hy hyr
    simpa using abs_sub_le_of_partialDeriv_le hM l00
      (fun z hz ↦ dif [0, 0] (by norm_num) z hz) (fun z hz hzr j ↦ h3 z hz hzr j 0 0) hy hyr
  have r11 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] (∂[1] f)) y| ≤ 2 * M * ‖y‖ := by
    intro y hy hyr
    simpa using abs_sub_le_of_partialDeriv_le hM l11
      (fun z hz ↦ dif [1, 1] (by norm_num) z hz) (fun z hz hzr j ↦ h3 z hz hzr j 1 1) hy hyr
  have r01 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] (∂[1] f)) y - p| ≤ 2 * M * ‖y‖ :=
    fun y hy hyr ↦ abs_sub_le_of_partialDeriv_le hM hp
      (fun z hz ↦ dif [0, 1] (by norm_num) z hz) (fun z hz hzr j ↦ h3 z hz hzr j 1 0) hy hyr
  have r10 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] (∂[0] f)) y - p| ≤ 2 * M * ‖y‖ :=
    fun y hy hyr ↦ abs_sub_le_of_partialDeriv_le hM hp'
      (fun z hz ↦ dif [1, 0] (by norm_num) z hz) (fun z hz hzr j ↦ h3 z hz hzr j 0 1) hy hyr
  -- first derivatives
  have d0 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] f) y - a - p * y 1| ≤ 4 * M * ‖y‖ ^ 2 := by
    intro y hy hyr
    have t := ha.sub (tendsto_quadratic a 0 p 0 0)
    rw [sub_self] at t
    have h := PDE.Analysis.abs_le_mul_pow_succ_of_partialDeriv_le
      (g := fun z ↦ (∂[0] f) z - (a + 0 * z 0 + p * z 1 + 0 * (z 0 * z 1) + 0 / 2 * (z 0 * z 0)))
      (r := r) (C := 2 * M) (m := 1)
      (fun z hz _ ↦ (dif [0] (by norm_num) z hz).sub (differentiableAt_quadratic _ _ _ _ _ z)) t
      (by positivity)
      (fun z hz hzr k ↦ by
        rw [partialDeriv_sub_quadratic (h := ∂[0] f) (dif [0] (by norm_num) z hz)]
        fin_cases k
        · simpa using r00 z hz hzr
        · simpa using r10 z hz hzr) hy hyr
    convert h using 1
    · congr 1; ring
    · ring
  have d1 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] f) y - p * y 0| ≤ 2 * M * |y 0| * ‖y‖ := by
    intro y hy hyr
    have h := PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le
      (g := fun z ↦ (∂[1] f) z - (0 + p * z 0 + 0 * z 1 + 0 * (z 0 * z 1) + 0 / 2 * (z 0 * z 0)))
      (r := r) (A := 2 * M) (a := 0) (m := 1) (by positivity)
      (fun z hz _ ↦ (dif [1] (by norm_num) z hz).sub (differentiableAt_quadratic _ _ _ _ _ z))
      (fun z hz0 hz hzr ↦ by
        have := ax [1] (by norm_num) (by decide) z hz0 hz hzr
        simp only [iteratedPartialDeriv] at this
        simp [hz0, this])
      (fun z hz hzr ↦ by
        rw [partialDeriv_sub_quadratic (h := ∂[1] f) (dif [1] (by norm_num) z hz)]
        simpa using r01 z hz hzr) hy hyr
    convert h using 1
    · congr 1; ring
    · ring
  refine ⟨?_, d0 x hx1 hxr, d1 x hx1 hxr, e00 x hx1 hxr, e11 x hx1 hxr, r01 x hx1 hxr,
    r10 x hx1 hxr⟩
  have h := PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le
    (g := fun z ↦ f z - (0 + a * z 0 + 0 * z 1 + p * (z 0 * z 1) + 0 / 2 * (z 0 * z 0)))
    (r := r) (A := 4 * M) (a := 0) (m := 2) (by positivity)
    (fun z hz _ ↦ (dif [] (by norm_num) z hz).sub (differentiableAt_quadratic _ _ _ _ _ z))
    (fun z hz0 hz hzr ↦ by
      have := ax [] (by norm_num) (by decide) z hz0 hz hzr
      simp only [iteratedPartialDeriv] at this
      simp [hz0, this])
    (fun z hz hzr ↦ by
      rw [partialDeriv_sub_quadratic (h := f) (dif [] (by norm_num) z hz)]
      have h := d0 z hz hzr
      rw [sub_sub] at h
      simpa using h) hx1 hxr
  convert h using 1
  · congr 1; ring
  · ring

/-- **The strain range of an odd jet field at the wall point**: under the hypotheses of
`IsOddJetField.abs_sub_le_of_partialDeriv_three_le`,
`|f - x₀ ∂₀f + x₁ ∂₁f - p x₀ x₁| ≤ 10 M |x₀| |x|²`. -/
theorem IsOddJetField.abs_strainRange_sub_le (hf : IsOddJetField 3 f) (hM : 0 ≤ M) {a p : ℝ}
    (ha : Tendsto (∂[0] f) (𝓝[upperHalfPlane] 0) (𝓝 a))
    (hp : Tendsto (∂[0] (∂[1] f)) (𝓝[upperHalfPlane] 0) (𝓝 p))
    (h3 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ j k l : Fin 2, |(∂[j] (∂[l] (∂[k] f))) y| ≤ M)
    {x : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) :
    |f x - x 0 * (∂[0] f) x + x 1 * (∂[1] f) x - p * (x 0 * x 1)| ≤
      10 * M * |x 0| * ‖x‖ ^ 2 := by
  obtain ⟨h0, h1, h2, -⟩ := hf.abs_sub_le_of_partialDeriv_three_le hM ha hp h3 hx1 hxr
  have hx0 : |x 0| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x 0
  have hx1' : |x 1| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x 1
  have he : f x - x 0 * (∂[0] f) x + x 1 * (∂[1] f) x - p * (x 0 * x 1) =
      (f x - a * x 0 - p * (x 0 * x 1)) - x 0 * ((∂[0] f) x - a - p * x 1) +
        x 1 * ((∂[1] f) x - p * x 0) := by ring
  rw [he]
  have b1 : |x 0| * |(∂[0] f) x - a - p * x 1| ≤ |x 0| * (4 * M * ‖x‖ ^ 2) := by gcongr
  have b2 : |x 1| * |(∂[1] f) x - p * x 0| ≤ ‖x‖ * (2 * M * |x 0| * ‖x‖) := by gcongr
  linarith [abs_add_le (f x - a * x 0 - p * (x 0 * x 1) - x 0 * ((∂[0] f) x - a - p * x 1))
    (x 1 * ((∂[1] f) x - p * x 0)),
    abs_sub (f x - a * x 0 - p * (x 0 * x 1)) (x 0 * ((∂[0] f) x - a - p * x 1)),
    abs_mul (x 0) ((∂[0] f) x - a - p * x 1), abs_mul (x 1) ((∂[1] f) x - p * x 0)]

/-- **Taylor bounds of an even jet field vanishing on the axis at the wall point**: if `f` is an
even jet field of order `3` vanishing on the vertical axis, its third partial derivatives are at
most `M` on the upper half disc `{x₁ > 0, |x| < r}` and `q = lim ∂₀²f` at the origin, then on that
half disc `|f - (q/2) x₀²| ≤ 2 M x₀² |x|`, `|∂₀f - q x₀| ≤ 2 M |x₀| |x|`, `|∂₁f| ≤ M x₀²`,
`|∂₀²f - q| ≤ 2 M |x|` and `|∂₀∂₁f|, |∂₁∂₀f|, |∂₁²f| ≤ M |x₀|`. -/
theorem IsEvenAxisJetField.abs_sub_le_of_partialDeriv_three_le (hf : IsEvenAxisJetField 3 f)
    (hM : 0 ≤ M) {q : ℝ} (hq : Tendsto (∂[0] (∂[0] f)) (𝓝[upperHalfPlane] 0) (𝓝 q))
    (h3 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ j k l : Fin 2, |(∂[j] (∂[l] (∂[k] f))) y| ≤ M)
    {x : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) :
    |f x - q / 2 * x 0 ^ 2| ≤ 2 * M * x 0 ^ 2 * ‖x‖ ∧
      |(∂[0] f) x - q * x 0| ≤ 2 * M * |x 0| * ‖x‖ ∧ |(∂[1] f) x| ≤ M * x 0 ^ 2 ∧
      |(∂[0] (∂[0] f)) x - q| ≤ 2 * M * ‖x‖ ∧ |(∂[0] (∂[1] f)) x| ≤ M * |x 0| ∧
      |(∂[1] (∂[0] f)) x| ≤ M * |x 0| ∧ |(∂[1] (∂[1] f)) x| ≤ M * |x 0| := by
  have hU := isOpen_upperHalfPlane
  have hσ : ∀ y ∈ upperHalfPlane, coordinateReflection (0 : Fin 2) y ∈ upperHalfPlane :=
    fun _ hy ↦ coordinateReflection_mem_upperHalfPlane hy
  have hc : ContDiffOn ℝ 3 f upperHalfPlane := hf.smooth.contDiffOn
  have ax : ∀ l : List (Fin 2), l.length ≤ 3 → Odd (l.count 0) → ∀ y : ℝ^2, y 0 = 0 →
      0 < y 1 → ‖y‖ < r → iteratedPartialDeriv l f y = 0 := by
    intro l hl he y hy0 hy _
    have h := hf.even.iteratedPartialDeriv hU hσ l (hc.of_le (by exact_mod_cast hl))
    rw [he.neg_one_pow, one_mul] at h
    exact h.eq_zero_of_apply_eq_zero hy hy0
  have dif : ∀ l : List (Fin 2), l.length ≤ 2 → ∀ y : ℝ^2, 0 < y 1 →
      DifferentiableAt ℝ (iteratedPartialDeriv l f) y :=
    fun l hl y hy ↦ hf.smooth.differentiableAt l (by omega) hy
  have h1f : IsEvenAxisJetField 2 (∂[1] f) := hf.partialDeriv_one
  have h11f : IsEvenAxisJetField 1 (∂[1] (∂[1] f)) := h1f.partialDeriv_one
  have e01 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] (∂[1] f)) y| ≤ M * |y 0| :=
    fun y ↦ abs_le_mul_abs_of_axis hM (dif [0, 1] (by norm_num))
      (ax [0, 1] (by norm_num) (by decide)) (fun z hz hzr ↦ h3 z hz hzr 0 1 0)
  have e10 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] (∂[0] f)) y| ≤ M * |y 0| :=
    fun y ↦ abs_le_mul_abs_of_axis hM (dif [1, 0] (by norm_num))
      (ax [1, 0] (by norm_num) (by decide)) (fun z hz hzr ↦ h3 z hz hzr 0 0 1)
  have e11 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] (∂[1] f)) y| ≤ M * |y 0| :=
    fun y ↦ abs_le_mul_abs_of_axis hM (dif [1, 1] (by norm_num))
      (fun z hz0 hz _ ↦ h11f.axis z hz hz0) (fun z hz hzr ↦ h3 z hz hzr 0 1 1)
  have r00 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] (∂[0] f)) y - q| ≤ 2 * M * ‖y‖ :=
    fun y hy hyr ↦ abs_sub_le_of_partialDeriv_le hM hq
      (fun z hz ↦ dif [0, 0] (by norm_num) z hz) (fun z hz hzr j ↦ h3 z hz hzr j 0 0) hy hyr
  have d0 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[0] f) y - q * y 0| ≤ 2 * M * |y 0| * ‖y‖ := by
    intro y hy hyr
    have h := PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le
      (g := fun z ↦ (∂[0] f) z - (0 + q * z 0 + 0 * z 1 + 0 * (z 0 * z 1) + 0 / 2 * (z 0 * z 0)))
      (r := r) (A := 2 * M) (a := 0) (m := 1) (by positivity)
      (fun z hz _ ↦ (dif [0] (by norm_num) z hz).sub (differentiableAt_quadratic _ _ _ _ _ z))
      (fun z hz0 hz hzr ↦ by
        have := ax [0] (by norm_num) (by decide) z hz0 hz hzr
        simp only [iteratedPartialDeriv] at this
        simp [hz0, this])
      (fun z hz hzr ↦ by
        rw [partialDeriv_sub_quadratic (h := ∂[0] f) (dif [0] (by norm_num) z hz)]
        simpa using r00 z hz hzr) hy hyr
    convert h using 1
    · congr 1; ring
    · ring
  have d1 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → |(∂[1] f) y| ≤ M * y 0 ^ 2 := by
    intro y hy hyr
    have h := PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le (g := ∂[1] f)
      (a := 1) (m := 0) hM (fun z hz _ ↦ dif [1] (by norm_num) z hz)
      (fun z hz0 hz _ ↦ h1f.axis z hz hz0)
      (fun z hz hzr ↦ by simpa using e01 z hz hzr) hy hyr
    simpa [sq_abs] using h
  refine ⟨?_, d0 x hx1 hxr, d1 x hx1 hxr, r00 x hx1 hxr, e01 x hx1 hxr, e10 x hx1 hxr,
    e11 x hx1 hxr⟩
  have h := PDE.Analysis.abs_le_mul_abs_pow_mul_pow_of_partialDeriv_zero_le
    (g := fun z ↦ f z - (0 + 0 * z 0 + 0 * z 1 + 0 * (z 0 * z 1) + q / 2 * (z 0 * z 0)))
    (r := r) (A := 2 * M) (a := 1) (m := 1) (by positivity)
    (fun z hz _ ↦ (dif [] (by norm_num) z hz).sub (differentiableAt_quadratic _ _ _ _ _ z))
    (fun z hz0 hz _ ↦ by simp [hz0, hf.axis z hz hz0])
    (fun z hz hzr ↦ by
      rw [partialDeriv_sub_quadratic (h := f) (dif [] (by norm_num) z hz)]
      simpa using d0 z hz hzr) hx1 hxr
  convert h using 1
  · congr 1; ring
  · rw [sq_abs]; ring

/-- **The strain range of an even jet field vanishing on the axis**: under the hypotheses of
`IsEvenAxisJetField.abs_sub_le_of_partialDeriv_three_le`,
`|3 f - x₀ ∂₀f + x₁ ∂₁f - (q/2) x₀²| ≤ 9 M x₀² |x|`. -/
theorem IsEvenAxisJetField.abs_strainRange_sub_le (hf : IsEvenAxisJetField 3 f) (hM : 0 ≤ M)
    {q : ℝ} (hq : Tendsto (∂[0] (∂[0] f)) (𝓝[upperHalfPlane] 0) (𝓝 q))
    (h3 : ∀ y : ℝ^2, 0 < y 1 → ‖y‖ < r → ∀ j k l : Fin 2, |(∂[j] (∂[l] (∂[k] f))) y| ≤ M)
    {x : ℝ^2} (hx1 : 0 < x 1) (hxr : ‖x‖ < r) :
    |3 * f x - x 0 * (∂[0] f) x + x 1 * (∂[1] f) x - q / 2 * x 0 ^ 2| ≤
      9 * M * x 0 ^ 2 * ‖x‖ := by
  obtain ⟨h0, h1, h2, -⟩ := hf.abs_sub_le_of_partialDeriv_three_le hM hq h3 hx1 hxr
  have hx1' : |x 1| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x 1
  have he : 3 * f x - x 0 * (∂[0] f) x + x 1 * (∂[1] f) x - q / 2 * x 0 ^ 2 =
      3 * (f x - q / 2 * x 0 ^ 2) - x 0 * ((∂[0] f) x - q * x 0) + x 1 * (∂[1] f) x := by ring
  rw [he]
  have b1 : |x 0| * |(∂[0] f) x - q * x 0| ≤ 2 * M * x 0 ^ 2 * ‖x‖ :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans_eq (by rw [← sq_abs]; ring)
  have b2 : |x 1| * |(∂[1] f) x| ≤ ‖x‖ * (M * x 0 ^ 2) := by gcongr
  linarith [abs_add_le (3 * (f x - q / 2 * x 0 ^ 2) - x 0 * ((∂[0] f) x - q * x 0))
    (x 1 * (∂[1] f) x), abs_sub (3 * (f x - q / 2 * x 0 ^ 2)) (x 0 * ((∂[0] f) x - q * x 0)),
    abs_mul (3 : ℝ) (f x - q / 2 * x 0 ^ 2), abs_mul (x 0) ((∂[0] f) x - q * x 0),
    abs_mul (x 1) ((∂[1] f) x), abs_of_pos (by norm_num : (0 : ℝ) < 3)]

end Taylor

end Boussinesq

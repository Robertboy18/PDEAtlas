/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Increment

/-!
# Integrating the boundary increment decomposition

Translation changes a pair of boundary points into a base point and displacement.
After integrating the base point, the two normal increments have the same energy.
These norm-energy identities hold for functions into any normed additive
commutative group and require no prior finiteness estimate.
-/

@[expose] public section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {f : ℝ^(n + 1) → F}

private theorem measurable_norm_sub_rpow {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {u v : X → F}
    (hu : Continuous u) (hv : Continuous v) (p : ℝ) :
    Measurable (fun x ↦ ENNReal.ofReal (‖u x - v x‖ ^ p)) :=
  ((hu.sub hv).norm.measurable.pow_const p).ennreal_ofReal

/-- The totalized fractional difference integrand vanishes on the diagonal. -/
theorem smoothBoundaryValue_fractional_diagonal (f : ℝ^(n + 1) → F)
    (x : ℝ^n) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (‖x - x‖ ^ (-((n : ℝ) + p - 1))) *
      ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f x‖ ^ p) = 0 := by
  simp [Real.zero_rpow hp.ne']

/-- The real-power kernel and the extended-norm quotient agree everywhere, including
on the diagonal. Positivity of the difference exponent makes both diagonal values zero. -/
theorem smoothBoundaryValue_fractional_kernel_eq (f : ℝ^(n + 1) → F)
    (x y : ℝ^n) {p : ℝ} (hp : 0 < p) (q : ℝ) :
    ENNReal.ofReal (‖x - y‖ ^ (-q)) *
        ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p) =
      ‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ₑ ^ p /
        (ENNReal.ofReal ‖x - y‖) ^ q := by
  by_cases hxy : x = y
  · subst y
    simp [Real.zero_rpow hp.ne', ENNReal.zero_rpow_of_pos hp]
  · rw [← ofReal_norm,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)),
      ENNReal.rpow_neg, div_eq_mul_inv, mul_comm]

/-- The product-measure quotient used by the fractional trace completion is exactly
its iterated real-power kernel integral. No integrability assumption is needed. -/
theorem lintegral_smoothBoundaryValue_enorm_div_eq_pair (hf : Continuous f)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖smoothBoundaryValue f z.1 - smoothBoundaryValue f z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)) =
      ∫⁻ x : ℝ^n, ∫⁻ y : ℝ^n,
        ENNReal.ofReal (‖x - y‖ ^ (-((n : ℝ) + p - 1))) *
          ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p) := by
  have hg := smoothBoundaryValue_continuous hf
  calc
    _ = ∫⁻ z : ℝ^n × ℝ^n,
        ENNReal.ofReal (‖z.1 - z.2‖ ^ (-((n : ℝ) + p - 1))) *
          ENNReal.ofReal (‖smoothBoundaryValue f z.1 - smoothBoundaryValue f z.2‖ ^ p)
        ∂((volume : Measure (ℝ^n)).prod volume) := by
      apply lintegral_congr
      intro z
      exact (smoothBoundaryValue_fractional_kernel_eq f z.1 z.2 hp _).symm
    _ = _ := by
      apply lintegral_prod
      have hkernel : Measurable (fun z : ℝ^n × ℝ^n ↦
          ENNReal.ofReal (‖z.1 - z.2‖ ^ (-((n : ℝ) + p - 1)))) := by fun_prop
      exact (hkernel.mul (measurable_norm_sub_rpow
        (hg.comp continuous_fst) (hg.comp continuous_snd) p)).aemeasurable

/-- The raw boundary pair energy can be integrated over displacement and base point. -/
theorem lintegral_smoothBoundaryValue_pair_eq_shift (hf : Continuous f) (p : ℝ) :
    (∫⁻ x : ℝ^n, ∫⁻ y : ℝ^n,
      ENNReal.ofReal (‖x - y‖ ^ (-((n : ℝ) + p - 1))) *
        ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p)) =
      ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
        ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
          ENNReal.ofReal (‖smoothBoundaryValue f (x + h) - smoothBoundaryValue f x‖ ^ p) := by
  have hg := smoothBoundaryValue_continuous hf
  calc
    _ = ∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n,
        ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
          ENNReal.ofReal (‖smoothBoundaryValue f (x + h) - smoothBoundaryValue f x‖ ^ p) := by
      apply lintegral_congr
      intro x
      have h := lintegral_add_left_eq_self (μ := volume)
        (fun y : ℝ^n ↦
          ENNReal.ofReal (‖x - y‖ ^ (-((n : ℝ) + p - 1))) *
            ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p)) x
      simpa only [← norm_sub_rev (x + _), add_sub_cancel_left,
        norm_sub_rev (smoothBoundaryValue f x)] using h.symm
    _ = _ := by
      apply lintegral_lintegral_swap
      have hkernel : Measurable (fun z : ℝ^n × ℝ^n ↦
          ENNReal.ofReal (‖z.2‖ ^ (-((n : ℝ) + p - 1)))) := by fun_prop
      exact (hkernel.mul (measurable_norm_sub_rpow
        (hg.comp (continuous_fst.add continuous_snd))
        (hg.comp continuous_fst) p)).aemeasurable

/-- At a fixed displacement and height, the boundary increment energy splits into
two equal normal contributions and one tangential contribution. -/
theorem lintegral_smoothBoundaryValue_sub_rpow_le (hf : Continuous f)
    {p : ℝ} (hp : 1 ≤ p) (h : ℝ^n) (t : ℝ) :
    (∫⁻ x : ℝ^n, ENNReal.ofReal
      (‖smoothBoundaryValue f (x + h) - smoothBoundaryValue f x‖ ^ p)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        ((∫⁻ x : ℝ^n, ENNReal.ofReal
            (‖normalSlice f x t - smoothBoundaryValue f x‖ ^ p)) +
          (∫⁻ x : ℝ^n, ENNReal.ofReal
            (‖normalSlice f (x + h) t - normalSlice f x t‖ ^ p)) +
          ∫⁻ x : ℝ^n, ENNReal.ofReal
            (‖normalSlice f x t - smoothBoundaryValue f x‖ ^ p)) := by
  have hg := smoothBoundaryValue_continuous hf
  have ht : Continuous (fun x : ℝ^n ↦ normalSlice f x t) :=
    (normalSlice_product_continuous hf).comp (continuous_id.prodMk continuous_const)
  have hnormal : Measurable (fun x : ℝ^n ↦
      ENNReal.ofReal (‖normalSlice f (x + h) t - smoothBoundaryValue f (x + h)‖ ^ p)) :=
    measurable_norm_sub_rpow (ht.comp (continuous_id.add_const h))
      (hg.comp (continuous_id.add_const h)) p
  have htangential : Measurable (fun x : ℝ^n ↦
      ENNReal.ofReal (‖normalSlice f (x + h) t - normalSlice f x t‖ ^ p)) :=
    measurable_norm_sub_rpow (ht.comp (continuous_id.add_const h)) ht p
  have hsum : Measurable (fun x : ℝ^n ↦
      ENNReal.ofReal (‖normalSlice f (x + h) t - smoothBoundaryValue f (x + h)‖ ^ p) +
        ENNReal.ofReal (‖normalSlice f (x + h) t - normalSlice f x t‖ ^ p)) :=
    hnormal.add htangential
  calc
    _ ≤ ∫⁻ x : ℝ^n, ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        (ENNReal.ofReal (‖normalSlice f (x + h) t - smoothBoundaryValue f (x + h)‖ ^ p) +
          ENNReal.ofReal (‖normalSlice f (x + h) t - normalSlice f x t‖ ^ p) +
          ENNReal.ofReal (‖normalSlice f x t - smoothBoundaryValue f x‖ ^ p)) := by
      apply lintegral_mono
      intro x
      have hbound := ENNReal.ofReal_le_ofReal
        (smoothBoundaryValue_sub_rpow_le_normal_tangential f (x + h) x t hp)
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)] at hbound
      exact hbound
    _ = ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        ((∫⁻ x : ℝ^n, ENNReal.ofReal
            (‖normalSlice f (x + h) t - smoothBoundaryValue f (x + h)‖ ^ p)) +
          (∫⁻ x : ℝ^n, ENNReal.ofReal
            (‖normalSlice f (x + h) t - normalSlice f x t‖ ^ p)) +
          ∫⁻ x : ℝ^n, ENNReal.ofReal
            (‖normalSlice f x t - smoothBoundaryValue f x‖ ^ p)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left hsum, lintegral_add_left hnormal]
    _ = _ := by
      rw [lintegral_add_right_eq_self (μ := volume)
        (fun x : ℝ^n ↦
          ENNReal.ofReal (‖normalSlice f x t - smoothBoundaryValue f x‖ ^ p)) h]

/-- The full pair energy splits into two normal kernel integrals and a tangential
translation integral. The tangential term still depends on the displacement direction. -/
theorem lintegral_smoothBoundaryValue_pair_le_normal_tangential (hf : Continuous f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x : ℝ^n, ∫⁻ y : ℝ^n,
      ENNReal.ofReal (‖x - y‖ ^ (-((n : ℝ) + p - 1))) *
        ENNReal.ofReal (‖smoothBoundaryValue f x - smoothBoundaryValue f y‖ ^ p)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        (2 * (∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n,
            ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
              ENNReal.ofReal (‖normalSlice f x ‖h‖ - smoothBoundaryValue f x‖ ^ p)) +
          ∫⁻ h : ℝ^n, ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1))) *
            ∫⁻ x : ℝ^n, ENNReal.ofReal
              (‖normalSlice f (x + h) ‖h‖ - normalSlice f x ‖h‖‖ ^ p)) := by
  have hg := smoothBoundaryValue_continuous hf
  have hs := normalSlice_product_continuous hf
  let K (h : ℝ^n) := ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + p - 1)))
  let A (h : ℝ^n) := ∫⁻ x : ℝ^n,
    ENNReal.ofReal (‖normalSlice f x ‖h‖ - smoothBoundaryValue f x‖ ^ p)
  let T (h : ℝ^n) := ∫⁻ x : ℝ^n,
    ENNReal.ofReal (‖normalSlice f (x + h) ‖h‖ - normalSlice f x ‖h‖‖ ^ p)
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hnormalJoint := measurable_norm_sub_rpow (X := ℝ^n × ℝ^n)
    (hs.comp (continuous_snd.prodMk continuous_fst.norm)) (hg.comp continuous_snd) p
  have hA : Measurable A := by
    exact hnormalJoint.lintegral_prod_right'
  have hT : Measurable T := by
    have hm := measurable_norm_sub_rpow (X := ℝ^n × ℝ^n)
      (hs.comp ((continuous_snd.add continuous_fst).prodMk continuous_fst.norm))
      (hs.comp (continuous_snd.prodMk continuous_fst.norm)) p
    exact hm.lintegral_prod_right'
  have hnormal :
      (∫⁻ h : ℝ^n, K h * A h) =
        ∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n, K h *
          ENNReal.ofReal (‖normalSlice f x ‖h‖ - smoothBoundaryValue f x‖ ^ p) := by
    calc
      _ = ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n, K h *
          ENNReal.ofReal (‖normalSlice f x ‖h‖ - smoothBoundaryValue f x‖ ^ p) := by
        apply lintegral_congr
        intro h
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = _ := lintegral_lintegral_swap
        ((hK.comp measurable_fst).mul hnormalJoint).aemeasurable
  rw [lintegral_smoothBoundaryValue_pair_eq_shift hf p]
  calc
    _ = ∫⁻ h : ℝ^n, K h *
        ∫⁻ x : ℝ^n, ENNReal.ofReal
          (‖smoothBoundaryValue f (x + h) - smoothBoundaryValue f x‖ ^ p) := by
      apply lintegral_congr
      intro h
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ h : ℝ^n, ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        (K h * A h + K h * T h + K h * A h) := by
      apply lintegral_mono
      intro h
      have hb := mul_le_mul_right
        (lintegral_smoothBoundaryValue_sub_rpow_le hf hp h ‖h‖) (K h)
      simpa only [mul_add, mul_left_comm, mul_assoc] using hb
    _ = ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
        ((∫⁻ h : ℝ^n, K h * A h) + (∫⁻ h : ℝ^n, K h * T h) +
          ∫⁻ h : ℝ^n, K h * A h) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (show Measurable (fun h ↦ K h * A h + K h * T h) from
          (hK.mul hA).add (hK.mul hT)),
        lintegral_add_left (show Measurable (fun h ↦ K h * A h) from hK.mul hA)]
    _ = _ := by
      rw [hnormal]
      dsimp [K, T]
      congr 1
      rw [two_mul]
      ac_rfl

end SobolevSpace.Trace.HalfSpace

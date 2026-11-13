/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import PDE.Analysis.Evolution.Core.Gronwall

/-!
# Data bounds from a Gårding energy inequality

Suppose that for every `t ∈ [a, b]`

`½ ‖w(t)‖² + (θ/2) ∫ₐᵗ ‖u‖² ≤ ½ ‖u₀‖² + (1/(2θ)) ∫ₐᵗ ‖f‖² + γ ∫ₐᵗ ‖w‖²`,

with `θ > 0`, `γ ≥ 0`, `w` continuous on `[a, b]` and `f ∈ L²(a, b)`. Scalar
Grönwall gives `‖w(t)‖² ≤ (‖u₀‖² + θ⁻¹ ∫ₐᵇ ‖f‖²) e^{2γ(t-a)}`, and inserting this
bound back into the inequality gives
`∫ₐᵇ ‖u‖² ≤ θ⁻¹ (1 + 2γ(b-a) e^{2γ(b-a)}) (‖u₀‖² + θ⁻¹ ∫ₐᵇ ‖f‖²)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- The Gårding energy inequality on every prefix `[a, t]` gives
`‖w(t)‖² ≤ (‖u₀‖² + θ⁻¹ ∫ₐᵇ ‖f‖²) e^{2γ(t-a)}`. -/
theorem norm_sq_le_exp_of_garding_energy_bound
    {V H F : Type*} [NormedAddCommGroup V] [NormedAddCommGroup H] [NormedAddCommGroup F]
    {a b theta gamma : ℝ} {u : ℝ → V} {w : ℝ → H} {f : ℝ → F} {uInit : H}
    (hw : ContinuousOn w (Icc a b))
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (htheta : 0 < theta) (hgamma : 0 ≤ gamma) (hab : a ≤ b)
    (henergy : ∀ t ∈ Icc a b,
      (1 / 2 : ℝ) * ‖w t‖ ^ 2 + (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
          (1 / (2 * theta)) * (∫ s in a..t, ‖f s‖ ^ 2) +
          gamma * (∫ s in a..t, ‖w s‖ ^ 2)) :
    ∀ t ∈ Icc a b,
      ‖w t‖ ^ 2 ≤
        (‖uInit‖ ^ 2 + (1 / theta) * (∫ s in a..b, ‖f s‖ ^ 2)) *
          Real.exp ((2 * gamma) * (t - a)) := by
  let e : ℝ → ℝ := fun t ↦ ‖w t‖ ^ 2
  let forcingSq : ℝ → ℝ := fun t ↦ ‖f t‖ ^ 2
  have heContinuous : ContinuousOn e (Set.Icc a b) := hw.norm.pow 2
  have hforcingIntegrable :
      IntervalIntegrable forcingSq volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    change Integrable (fun t ↦ ‖f t‖ ^ 2)
      (volume.restrict (Set.Ioc a b))
    exact hf.integrable_norm_pow (by norm_num)
  have hforcingNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc a b)] forcingSq :=
    Filter.Eventually.of_forall fun t ↦ sq_nonneg ‖f t‖
  have heIntegral : ∀ t ∈ Set.Icc a b,
      e t ≤
        (‖uInit‖ ^ 2 +
          (1 / theta) * (∫ s in a..b, forcingSq s)) +
          (2 * gamma) * ∫ s in a..t, e s := by
    intro t ht
    have huIntegralNonneg :
        0 ≤ ∫ s in a..t, ‖u s‖ ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 fun s _ ↦ sq_nonneg ‖u s‖
    have hforcingMono :
        (∫ s in a..t, forcingSq s) ≤
          ∫ s in a..b, forcingSq s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        hforcingNonneg hforcingIntegrable
    have hscaledForcing :
        (1 / theta) * (∫ s in a..t, forcingSq s) ≤
          (1 / theta) * (∫ s in a..b, forcingSq s) :=
      mul_le_mul_of_nonneg_left hforcingMono (by positivity)
    have hforcingCoefficient :
        2 * (1 / (2 * theta)) = 1 / theta := by
      field_simp
    have hraw := henergy t ht
    have hraw2 :
        e t + theta * (∫ s in a..t, ‖u s‖ ^ 2) ≤
          ‖uInit‖ ^ 2 +
            (1 / theta) * (∫ s in a..t, forcingSq s) +
            (2 * gamma) * (∫ s in a..t, e s) := by
      calc
        e t + theta * (∫ s in a..t, ‖u s‖ ^ 2) =
            2 * ((1 / 2 : ℝ) * ‖w t‖ ^ 2 +
              (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2)) := by
                dsimp [e]
                ring
        _ ≤ 2 * ((1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
              (1 / (2 * theta)) * (∫ s in a..t, ‖f s‖ ^ 2) +
              gamma * (∫ s in a..t, ‖w s‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hraw (by norm_num)
        _ = ‖uInit‖ ^ 2 +
              (1 / theta) * (∫ s in a..t, forcingSq s) +
              (2 * gamma) * (∫ s in a..t, e s) := by
          dsimp [e, forcingSq]
          rw [← hforcingCoefficient]
          ring
    have henergyFullNonneg :
        0 ≤ theta * (∫ s in a..t, ‖u s‖ ^ 2) :=
      mul_nonneg htheta.le huIntegralNonneg
    calc
      e t ≤ e t + theta * (∫ s in a..t, ‖u s‖ ^ 2) :=
        le_add_of_nonneg_right henergyFullNonneg
      _ ≤ ‖uInit‖ ^ 2 +
            (1 / theta) * (∫ s in a..t, forcingSq s) +
            (2 * gamma) * (∫ s in a..t, e s) := hraw2
      _ ≤ (‖uInit‖ ^ 2 +
            (1 / theta) * (∫ s in a..b, forcingSq s)) +
            (2 * gamma) * ∫ s in a..t, e s := by
        gcongr
  exact le_mul_exp_of_le_const_add_mul_intervalIntegral
    heContinuous (mul_nonneg (by norm_num) hgamma) heIntegral

/-- The same prefix inequality gives
`∫ₐᵇ ‖u‖² ≤ θ⁻¹ (1 + 2γ(b-a) e^{2γ(b-a)}) (‖u₀‖² + θ⁻¹ ∫ₐᵇ ‖f‖²)`.
The conclusion does not give integrability of `‖u‖²`: a nonintegrable function
has interval integral `0`. -/
theorem integral_norm_sq_le_of_garding_energy_bound
    {V H F : Type*} [NormedAddCommGroup V] [NormedAddCommGroup H] [NormedAddCommGroup F]
    {a b theta gamma : ℝ} {u : ℝ → V} {w : ℝ → H} {f : ℝ → F} {uInit : H}
    (hw : ContinuousOn w (Icc a b))
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (htheta : 0 < theta) (hgamma : 0 ≤ gamma) (hab : a ≤ b)
    (henergy : ∀ t ∈ Icc a b,
      (1 / 2 : ℝ) * ‖w t‖ ^ 2 + (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
          (1 / (2 * theta)) * (∫ s in a..t, ‖f s‖ ^ 2) +
          gamma * (∫ s in a..t, ‖w s‖ ^ 2)) :
    (∫ s in a..b, ‖u s‖ ^ 2) ≤
      (1 / theta) * (1 + 2 * gamma * (b - a) * Real.exp (2 * gamma * (b - a))) *
        (‖uInit‖ ^ 2 + (1 / theta) * (∫ s in a..b, ‖f s‖ ^ 2)) := by
  let D := ‖uInit‖ ^ 2 + (1 / theta) * (∫ s in a..b, ‖f s‖ ^ 2)
  have hD : 0 ≤ D := add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _))
  have hpivot := norm_sq_le_exp_of_garding_energy_bound hw hf htheta hgamma hab henergy
  have hbound : ∀ t ∈ Icc a b,
      ‖w t‖ ^ 2 ≤ D * Real.exp (2 * gamma * (b - a)) := by
    intro t ht
    exact (hpivot t ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
        (by positivity))) hD)
  have hint :
      (∫ s in a..b, ‖w s‖ ^ 2) ≤ (b - a) * (D * Real.exp (2 * gamma * (b - a))) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab
      ((hw.norm.pow 2).intervalIntegrable_of_Icc hab) intervalIntegrable_const hbound
    simpa only [intervalIntegral.integral_const, smul_eq_mul, Pi.pow_apply] using h
  have hraw := henergy b ⟨hab, le_rfl⟩
  have hforcing : 2 * (1 / (2 * theta)) = 1 / theta := by field_simp
  have hbase : theta * (∫ s in a..b, ‖u s‖ ^ 2) ≤
      D + 2 * gamma * ((b - a) * (D * Real.exp (2 * gamma * (b - a)))) := by
    have hscaled := mul_le_mul_of_nonneg_left hint (show 0 ≤ gamma from hgamma)
    have hfscale := congrArg (fun c ↦ c * (∫ s in a..b, ‖f s‖ ^ 2)) hforcing
    dsimp only [D] at hscaled ⊢
    nlinarith [sq_nonneg ‖w b‖]
  have hdiv := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 1 / theta by positivity)
  calc
    (∫ s in a..b, ‖u s‖ ^ 2) =
        (1 / theta) * (theta * (∫ s in a..b, ‖u s‖ ^ 2)) := by field_simp
    _ ≤ _ := hdiv
    _ = _ := by dsimp only [D]; ring

end PDE.Analysis.Evolution

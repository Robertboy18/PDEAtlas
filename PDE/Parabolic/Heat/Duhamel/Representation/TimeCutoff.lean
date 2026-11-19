/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Representation.CompactSupport
import PDE.FDeriv.Calculus

/-!
# Duhamel representation after a time cutoff

A smooth time cutoff which vanishes at the initial time removes the initial
slice from the Duhamel identity. The resulting source consists of the
original heat residual and the field times the derivative of the cutoff.
All differentiability and support properties of the product are derived.
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory Set
open scoped Interval

namespace HeatEquation

variable {n : ℕ}

/-- A time cutoff vanishing at the initial time expresses the localized field
entirely in terms of its heat residual. The identity includes the
terminal time and only uses relative time derivatives. -/
theorem timeCutoff_eq_integral_heatResidual
    {u D : ℝ → ℝ^n → ℝ} {a b : ℝ} {K : Set (ℝ^n)} {η : ℝ → ℝ}
    (hab : a ≤ b) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (Icc a b ×ˢ univ))
    (hD : ContinuousOn D.uncurry (Icc a b ×ˢ univ))
    (hL : ContinuousOn (fun p : ℝ × ℝ^n ↦ laplacian (u p.1) p.2)
      (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Icc a b, ∀ y,
      HasDerivWithinAt (fun r ↦ u r y) (D s y) (Icc a b) s)
    (hsupport : ∀ s ∈ Icc a b, ∀ y ∉ K, u s y = 0)
    (hspace : ∀ s ∈ Icc a b, ContDiff ℝ 2 (u s))
    (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (x : ℝ^n) :
    η b * u b x =
      ∫ s in a..b, initialValueSolution (fun y ↦
        deriv η s * u s y + η s * (D s y - laplacian (u s) y)) x (b - s) := by
  have hηc : Continuous (fun p : ℝ × ℝ^n ↦ η p.1) :=
    hη.continuous.comp continuous_fst
  have hηd : Continuous (fun p : ℝ × ℝ^n ↦ deriv η p.1) :=
    hη.continuous_deriv_one.comp continuous_fst
  have hproductL : ContinuousOn (fun p : ℝ × ℝ^n ↦
      laplacian (fun y ↦ η p.1 * u p.1 y) p.2) (Icc a b ×ˢ univ) := by
    simp only [PDE.laplacian_const_smul]
    exact hηc.continuousOn.mul hL
  have hproduct := eq_initialValueSolution_add_integral_heatResidual
    (u := fun s y ↦ η s * u s y)
    (D := fun s y ↦ deriv η s * u s y + η s * D s y)
    hab hK (hηc.continuousOn.mul hu)
    ((hηd.continuousOn.mul hu).add (hηc.continuousOn.mul hD)) hproductL
    (fun s hs y ↦ ((hη.differentiable one_ne_zero s).hasDerivAt.hasDerivWithinAt).mul
      (hd s hs y))
    (fun s hs y hy ↦ by rw [hsupport s hs y hy, mul_zero])
    (fun s hs ↦ contDiff_const.mul (hspace s hs)) x
  simpa only [hηa, zero_mul, initialValueSolution_const, zero_add,
    PDE.laplacian_const_smul, mul_sub, add_sub_assoc] using hproduct

end HeatEquation

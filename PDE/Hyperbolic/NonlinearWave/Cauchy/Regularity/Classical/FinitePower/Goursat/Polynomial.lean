/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.ImplicitFunction.IntegralEquation.Smooth
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Rectangle
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.FunctionSpace
import CAS.ExactTactic

/-!
# Polynomial Goursat fixed points

The bounded rectangle operator defines a polynomial fixed-point equation. Its local branch is
available at finite order and smoothly on one common parameter neighborhood.
-/

@[expose] public noncomputable section

section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open scoped unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The two characteristic side lengths and the amplitude. -/
abbrev Parameter := ℝ × ℝ × ℝ

/-- The first normalized coordinate as a continuous scalar field. -/
def firstCoordinate : Rectangle →ᵇ ℝ :=
  mkOfCompact ⟨fun q ↦ (q.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩

/-- The second normalized coordinate as a continuous scalar field. -/
def secondCoordinate : Rectangle →ᵇ ℝ :=
  mkOfCompact ⟨fun q ↦ (q.2 : ℝ), continuous_subtype_val.comp continuous_snd⟩

/-- Restrict both characteristic side lengths and retain the same amplitude. -/
def restrictParameter (p : Parameter) (q : Rectangle) : Parameter :=
  (p.1 * (q.1 : ℝ), p.2.1 * (q.2 : ℝ), p.2.2)

/-- Restriction keeps the parameter inside every centered norm ball. -/
theorem norm_restrictParameter_le (p : Parameter) (q : Rectangle) :
    ‖restrictParameter p q‖ ≤ ‖p‖ := by
  simp only [restrictParameter, Prod.norm_def]
  apply max_le_max
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg q.1.property.1] using q.1.property.2)
  · apply max_le_max _ le_rfl
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg q.2.property.1] using q.2.property.2)

/-- The radial coefficient evaluated throughout a normalized characteristic rectangle. -/
def rectangularCoefficient (c : C(ℝ, ℝ)) (p : Parameter) : Rectangle →ᵇ ℝ :=
  composeCompact c (p.1 • firstCoordinate - p.2.1 • secondCoordinate)

/-- The normalized polynomial Goursat right hand side. -/
def polynomialFixedPoint (c : C(ℝ, ℝ)) (p : Parameter) (w : Rectangle →ᵇ ℝ) :
    Rectangle →ᵇ ℝ :=
  (p.2.2 * p.1) • firstCoordinate + (p.1 * p.2.1) •
    rectangularOperator (rectangularCoefficient c p * w ^ 2)

/-- The coefficient is compatible with characteristic restriction. -/
theorem restrictRectangle_coefficient (c : C(ℝ, ℝ)) (p : Parameter) (q : Rectangle) :
    restrictRectangle q (rectangularCoefficient c p) =
      rectangularCoefficient c (restrictParameter p q) := by
  ext r
  change c (p.1 * ((q.1 : ℝ) * (r.1 : ℝ)) - p.2.1 * ((q.2 : ℝ) * (r.2 : ℝ))) =
    c ((p.1 * (q.1 : ℝ)) * (r.1 : ℝ) - (p.2.1 * (q.2 : ℝ)) * (r.2 : ℝ))
  congr 1
  cas

/-- The entire nonlinear fixed-point equation respects rectangle restriction. -/
theorem restrictRectangle_polynomialFixedPoint (c : C(ℝ, ℝ)) (p : Parameter)
    (q : Rectangle) (w : Rectangle →ᵇ ℝ) :
    restrictRectangle q (polynomialFixedPoint c p w) =
      polynomialFixedPoint c (restrictParameter p q) (restrictRectangle q w) := by
  have hsource : restrictRectangle q (rectangularCoefficient c p * w ^ 2) =
      rectangularCoefficient c (restrictParameter p q) * (restrictRectangle q w) ^ 2 := by
    ext r
    change rectangularCoefficient c p (descend q r) * (w (descend q r)) ^ 2 =
      rectangularCoefficient c (restrictParameter p q) r * (w (descend q r)) ^ 2
    rw [← restrictRectangle_apply, restrictRectangle_coefficient]
  ext r
  change (p.2.2 * p.1) * ((q.1 : ℝ) * (r.1 : ℝ)) + (p.1 * p.2.1) *
      rectangularOperator (rectangularCoefficient c p * w ^ 2) (descend q r) =
    (p.2.2 * (p.1 * (q.1 : ℝ))) * (r.1 : ℝ) + ((p.1 * (q.1 : ℝ)) * (p.2.1 * (q.2 : ℝ))) *
        rectangularOperator
          (rectangularCoefficient c (restrictParameter p q) * (restrictRectangle q w) ^ 2) r
  rw [rectangularOperator_descend, hsource]
  generalize rectangularOperator
    (rectangularCoefficient c (restrictParameter p q) * (restrictRectangle q w) ^ 2) r = J
  cas

/-- The polynomial equation has the same finite regularity as its coefficient. -/
theorem contDiff_polynomialFixedPoint {k : ℕ} {c : ℝ → ℝ} (hc : ContDiff ℝ k c) :
    ContDiff ℝ k (fun z : Parameter × (Rectangle →ᵇ ℝ) ↦
      polynomialFixedPoint ⟨c, hc.continuous⟩ z.1 z.2) := by
  have hcoeff : ContDiff ℝ k (fun z : Parameter × (Rectangle →ᵇ ℝ) ↦
      rectangularCoefficient ⟨c, hc.continuous⟩ z.1) := (contDiff_composeCompact hc).comp
      ((contDiff_fst.fst.smul contDiff_const).sub (contDiff_fst.snd.fst.smul contDiff_const))
  exact (contDiff_fst.snd.snd.mul contDiff_fst.fst).smul contDiff_const |>.add
    ((contDiff_fst.fst.mul contDiff_fst.snd.fst).smul
      (rectangularOperator.contDiff.comp (hcoeff.mul (contDiff_snd.pow 2))))

/-- A smooth coefficient constructs a family of normalized fixed points,
with a uniform ball of uniqueness supplied by the implicit theorem. -/
theorem exists_polynomial_fixed_point {k : ℕ} {c : ℝ → ℝ} (hc : ContDiff ℝ (k + 1) c) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ ∃ ψ : Parameter → (Rectangle →ᵇ ℝ),
      ContDiffOn ℝ (k + 1) ψ (Metric.ball 0 δ) ∧
      (∀ p ∈ Metric.ball 0 δ, ‖ψ p‖ < r) ∧
      (∀ p ∈ Metric.ball 0 δ, ψ p = polynomialFixedPoint ⟨c, hc.continuous⟩ p (ψ p)) ∧
      (∀ p ∈ Metric.ball 0 δ, ∀ w, ‖w‖ < r →
        w = polynomialFixedPoint ⟨c, hc.continuous⟩ p w → ψ p = w) := by
  refine exists_local_fixed_point_of_zero_parameter (contDiff_polynomialFixedPoint hc) fun w ↦ ?_
  simp [polynomialFixedPoint]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology ContDiff unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The same polynomial rectangular operator is smooth to every order. -/
theorem contDiff_infty_polynomialFixedPoint {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun z : Parameter × (Rectangle →ᵇ ℝ) ↦
      polynomialFixedPoint ⟨c, hc.continuous⟩ z.1 z.2) := by
  refine contDiff_infty.mpr fun k ↦ ?_
  exact contDiff_polynomialFixedPoint (hc.of_le (by simp) : ContDiff ℝ k c)

/-- One smooth normalized fixed point has a common ball of uniqueness. -/
theorem exists_smooth_polynomial_fixed_point {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ ∃ ψ : Parameter → (Rectangle →ᵇ ℝ),
      ContDiffOn ℝ ∞ ψ (Metric.ball 0 δ) ∧
      (∀ p ∈ Metric.ball 0 δ, ‖ψ p‖ < r) ∧
      (∀ p ∈ Metric.ball 0 δ, ψ p = polynomialFixedPoint ⟨c, hc.continuous⟩ p (ψ p)) ∧
      (∀ p ∈ Metric.ball 0 δ, ∀ w, ‖w‖ < r →
        w = polynomialFixedPoint ⟨c, hc.continuous⟩ p w → ψ p = w) := by
  apply exists_smooth_local_fixed_point_of_zero_parameter (contDiff_infty_polynomialFixedPoint hc)
  intro w
  simp [polynomialFixedPoint]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

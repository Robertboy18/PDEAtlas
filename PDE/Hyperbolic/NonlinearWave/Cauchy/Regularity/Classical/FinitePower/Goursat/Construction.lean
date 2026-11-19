/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension.FiniteDimensional
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Equation

/-!
# A smooth polynomial Goursat field

The common smooth fixed-point branch descends from a compact rectangle to a smooth field
satisfying the characteristic integral equation.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology ContDiff unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The normalized solutions descend to one field in the physical characteristic variables. -/
theorem exists_smooth_polynomial_goursat_field {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Parameter → ℝ,
      ContDiffOn ℝ ∞ V (Metric.ball 0 δ) ∧
      ∀ p ∈ Metric.ball 0 δ,
        V p = p.2.2 * p.1 + (p.1 * p.2.1) *
          ∫ s : I, ∫ t : I, c (p.1 * (s : ℝ) - p.2.1 * (t : ℝ)) *
            V (p.1 * (s : ℝ), p.2.1 * (t : ℝ), p.2.2) ^ 2 := by
  obtain ⟨δ, r, hδ, _, ψ, hψreg, hψbound, hψeq, hψunique⟩ := exists_smooth_polynomial_fixed_point hc
  have hmem {p : Parameter} (hp : p ∈ Metric.ball 0 δ) (q : Rectangle) :
      restrictParameter p q ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, dist_zero_right] at hp ⊢
    exact (norm_restrictParameter_le p q).trans_lt hp
  have hrestrict {p : Parameter} (hp : p ∈ Metric.ball 0 δ) (q : Rectangle) :
      ψ (restrictParameter p q) = restrictRectangle q (ψ p) := by
    apply hψunique _ (hmem hp q) _ ((norm_restrictRectangle_le q (ψ p)).trans_lt (hψbound p hp))
    calc
      restrictRectangle q (ψ p) =
          restrictRectangle q (polynomialFixedPoint ⟨c, hc.continuous⟩ p (ψ p)) :=
        congrArg (restrictRectangle q) (hψeq p hp)
      _ = _ := restrictRectangle_polynomialFixedPoint _ p q (ψ p)
  let V : Parameter → ℝ := fun p ↦ ψ p (1, 1)
  have hvalue {p : Parameter} (hp : p ∈ Metric.ball 0 δ) (q : Rectangle) :
      V (restrictParameter p q) = ψ p q := by
    dsimp only [V]
    rw [hrestrict hp q, restrictRectangle_apply]
    simp only [descend, mul_one]
  refine ⟨δ, hδ, V, (evalCLM ℝ (1, 1) : (Rectangle →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn
    hψreg, ?_⟩
  intro p hp
  have heq := congrArg (fun w : Rectangle →ᵇ ℝ ↦ w (1, 1)) (hψeq p hp)
  change V p = (p.2.2 * p.1) * 1 + (p.1 * p.2.1) *
    rectangularOperator (rectangularCoefficient ⟨c, hc.continuous⟩ p * ψ p ^ 2) (1, 1) at heq
  rw [mul_one, rectangularOperator_apply] at heq
  simp only [Set.Icc.coe_one, one_mul, descend] at heq
  rw [heq]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [] with t
  change c (p.1 * (s : ℝ) - p.2.1 * (t : ℝ)) * ψ p (s, t) ^ 2 = _
  rw [← hvalue hp (s, t)]
  rfl

/-- The Goursat field can be represented globally with the same smoothness,
while its nonlinear integral equation remains valid on a smaller parameter ball. -/
theorem exists_smooth_polynomial_goursat_equation {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : Parameter → ℝ, ContDiff ℝ ∞ W ∧
      ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
        c (s - t) * W (s, t, p.2.2) ^ 2 := by
  obtain ⟨δ, hδ, V, hV, hVEq⟩ := exists_smooth_polynomial_goursat_field hc
  obtain ⟨W, hW, _, hVW⟩ := hV.exists_contDiff_compactSupport_eventuallyEq_finiteDimensional
      Metric.isOpen_ball (Metric.mem_ball_self hδ)
  obtain ⟨η, hη, hnear⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hVW (Metric.ball_mem_nhds (0 : Parameter) hδ))
  refine ⟨η, hη, W, hW, fun p hp ↦ ?_⟩
  rw [← (hnear hp).1, hVEq p (hnear hp).2]
  have heq : (∫ s : I, ∫ t : I, c (p.1 * (s : ℝ) - p.2.1 * (t : ℝ)) *
      V (p.1 * (s : ℝ), p.2.1 * (t : ℝ), p.2.2) ^ 2) =
      ∫ s : I, ∫ t : I, c (p.1 * (s : ℝ) - p.2.1 * (t : ℝ)) *
        W (p.1 * (s : ℝ), p.2.1 * (t : ℝ), p.2.2) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with s
    apply integral_congr_ae
    filter_upwards [] with t
    have hmem : restrictParameter p (s, t) ∈ Metric.ball 0 η := by
      rw [Metric.mem_ball, dist_zero_right] at hp ⊢
      exact (norm_restrictParameter_le p (s, t)).trans_lt hp
    have hvw : V (p.1 * (s : ℝ), p.2.1 * (t : ℝ), p.2.2) =
        W (p.1 * (s : ℝ), p.2.1 * (t : ℝ), p.2.2) := (hnear hmem).1
    rw [hvw]
  rw [heq]
  exact congrArg (fun z ↦ p.2.2 * p.1 + z)
    (integral_rectangle_eq_normalized (fun s t ↦ c (s - t) * W (s, t, p.2.2) ^ 2) _ _)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

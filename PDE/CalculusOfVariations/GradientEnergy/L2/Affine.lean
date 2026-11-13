/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.Definition
public import PDE.Analysis.Convex.Subdifferential.Translation
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.Affine

/-!
# Signed affine shifts of the ambient gradient energy

Adding `⟪a,p⟫ + b` to a gradient density changes its Dirichlet integral
by exactly `b |Ω|`. The linear gradient term vanishes by integration by
parts. The same identity holds for the extended L² energy, with `+∞`
retained outside H¹₀, and leaves its subdifferential unchanged.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}
  [IsFiniteMeasure (domainMeasure n Ω)]

local notation "μ" => domainMeasure n Ω

/-- The affine gradient contribution is a pure signed volume shift on
the Dirichlet space. Integrability is explicit at this general level. -/
theorem dirichletGradientIntegralEnergy_add_affine
    (a : ℝ^n) (b : ℝ) (u : H¹₀(Ω))
    (hint : Integrable (fun x ↦ L (∇ (u : H¹(Ω)) x)) μ) :
    dirichletGradientIntegralEnergy (fun _ p ↦ L p + ⟪a, p⟫ + b) u =
      dirichletGradientIntegralEnergy (fun _ ↦ L) u + (domainMeasure n Ω).real univ * b := by
  have hi : Integrable (fun x ↦ ⟪a, ∇ (u : H¹(Ω)) x⟫) μ :=
    ((Lp.memLp (∇ (u : H¹(Ω)))).integrable (by norm_num)).const_inner a
  change (∫ x, L (∇ (u : H¹(Ω)) x) + ⟪a, ∇ (u : H¹(Ω)) x⟫ + b ∂μ) =
    (∫ x, L (∇ (u : H¹(Ω)) x) ∂μ) + (domainMeasure n Ω).real univ * b
  rw [integral_add (f := fun x ↦ L (∇ (u : H¹(Ω)) x) + ⟪a, ∇ (u : H¹(Ω)) x⟫)
    (hint.add hi) (integrable_const b), integral_add hint hi,
    show (∫ x, ⟪a, ∇ (u : H¹(Ω)) x⟫ ∂μ) = 0 from
      integral_inner_gradientCLM_eq_zero a u, add_zero, integral_const]
  rfl

/-- The exact affine shift holds throughout L², including competitors
of infinite energy. -/
theorem l2DirichletGradientEnergy_add_affine
    (hint : ∀ u : H¹₀(Ω), Integrable (fun x ↦ L (∇ (u : H¹(Ω)) x)) μ)
    (a : ℝ^n) (b : ℝ) (x : DerivLp n 2 Ω) :
    l2DirichletGradientEnergy (fun p ↦ L p + ⟪a, p⟫ + b) x =
      l2DirichletGradientEnergy L x + ((domainMeasure n Ω).real univ * b : ℝ) := by
  by_cases hx : x ∈ range (baseCoordCLM (n := n) (Ω := Ω))
  · classical
    rw [mem_range] at hx
    rw [l2DirichletGradientEnergy, l2DirichletGradientEnergy, linearImageEnergy,
      linearImageEnergy, Function.extend_def, Function.extend_def]
    simp only [hx, ↓reduceDIte]
    rw [← EReal.coe_add, dirichletGradientIntegralEnergy_add_affine a b _ (hint _)]
  · rw [l2DirichletGradientEnergy_eq_top _ hx, l2DirichletGradientEnergy_eq_top _ hx,
      EReal.top_add_coe]

/-- An affine perturbation of the density leaves the ambient operator
unchanged, without imposing a sign or a normalization at zero. -/
theorem subdifferential_l2DirichletGradientEnergy_add_affine
    (hint : ∀ u : H¹₀(Ω), Integrable (fun x ↦ L (∇ (u : H¹(Ω)) x)) μ)
    (a : ℝ^n) (b : ℝ) (x : DerivLp n 2 Ω) :
    subdifferential (l2DirichletGradientEnergy (fun p ↦ L p + ⟪a, p⟫ + b)) x =
      subdifferential (l2DirichletGradientEnergy L) x := by
  have heq : l2DirichletGradientEnergy (fun p ↦ L p + ⟪a, p⟫ + b) =
      fun x : DerivLp n 2 Ω ↦ l2DirichletGradientEnergy L x +
        ((domainMeasure n Ω).real univ * b : ℝ) :=
    funext (l2DirichletGradientEnergy_add_affine hint a b)
  rw [heq, subdifferential_add_const]

omit [IsFiniteMeasure (domainMeasure n Ω)] in
/-- The energy of the zero field is the domain volume times `L 0`. -/
theorem l2DirichletGradientEnergy_zero (hΩ : IsOpen Ω) (L : ℝ^n → ℝ) :
    l2DirichletGradientEnergy (Ω := Ω) L 0 = ((domainMeasure n Ω).real univ * L 0 : ℝ) := by
  have hzero : dirichletGradientIntegralEnergy (Ω := Ω) (fun _ ↦ L) 0 =
      (domainMeasure n Ω).real univ * L 0 := by
    unfold dirichletGradientIntegralEnergy
    rw [Submodule.coe_zero, map_zero]
    calc
      _ = ∫ _x, L 0 ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero (ℝ^n) 2 μ] with x hx
        exact congrArg L hx
      _ = _ := by rw [integral_const]; rfl
  have hbase := l2DirichletGradientEnergy_base (Ω := Ω) hΩ L 0
  simpa only [map_zero, hzero] using hbase

end PDE.CalculusOfVariations

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalCoefficientEllipticity
public import PDE.Elliptic.Semilinear.SubSupersolution.LocalRange

/-!
# Regularity of solutions enclosed by signed-trace barriers

A reaction that is Lipschitz on the bounded barrier range has an H¹ composition
with the weak solution. The global elliptic estimate then supplies an H³
representative from classical coefficient and graph-boundary data.

This is the first finite Sobolev regularity step. `SubSupersolution.Bootstrap`
iterates higher-order composition in arbitrary dimension, and
`SubSupersolution.Classical` recovers the smooth classical solution.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace

open MeasureTheory Set Boundary BoundaryRegularity
open Boundary.Geometry.SurfaceMeasure
open PDE.Analysis.Variational
open scoped Sobolev ENNReal NNReal

variable {n : ℕ} {Ω : Set ℝ^n}

/-- The integral identity with an almost-everywhere represented nonlinear
load is the distributional equation consumed by elliptic regularity. -/
theorem isWeakShiftedFullDivergenceSolution_of_reaction_eq
    (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (f : ℝ → ℝ) (u : H¹₀(Ω)) (F : DerivLp n 2 Ω)
    (hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦ f (baseCoordCLM u x))
    (hu : ∀ v : H¹₀(Ω), interiorFullDivergenceOperator a b c (u : H¹(Ω)) v =
      ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂domainMeasure n Ω) :
    IsWeakShiftedFullDivergenceSolution a b c 0 F 0 u := by
  apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
    hΩ a b c 0 F 0 u).mp
  intro v
  simp only [shiftedDivergenceForm_apply, generalizedLoad_apply, zero_mul, add_zero,
    Pi.zero_apply, inner_zero_left, Finset.sum_const_zero]
  rw [← interiorFullDivergenceOperator_coe_H10, hu v, inner_base_eq_integral]
  exact integral_congr_ae (hF.symm.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx)

variable {m : ℕ} {D : Set ℝ^(m + 1)}

/-- Classical C² coefficients, a bounded C³ graph domain, and a reaction C¹
only on the bounded barrier range give an H³ zero-boundary solution between
arbitrary ordered H¹ barriers with signed geometric traces. All Sobolev
regularity of the solution and its nonlinear forcing is derived. -/
theorem exists_h3_solution_between_H1_barriers_of_contDiffOn
    (hΩ : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hgraph : HasContDiffGraphBoundary 3 D)
    (a : ℝ^(m + 1) → Fin (m + 1) → Fin (m + 1) → ℝ)
    (b : Fin (m + 1) → ℝ^(m + 1) → ℝ) (c : ℝ^(m + 1) → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 2 (fun x ↦ a x i j) D)
    (hb : ∀ i, ContDiffUpToBoundary 2 (b i) D)
    (hc : ContDiffUpToBoundary 2 c D)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ D, MatrixEllipticLowerBound (a x) alpha)
    (f : ℝ → ℝ) {left right : ℝ} (hf : ContDiffOn ℝ 1 f (Icc left right))
    (lower upper : H¹(D))
    (htraceLower : let := (hgraph.hasC1GraphBoundary (by decide)).c1ExtensionAtlas hΩ hbounded
      ∀ᵐ x ∂surfaceMeasure D, Trace.C1.trace lower x ≤ 0)
    (htraceUpper : let := (hgraph.hasC1GraphBoundary (by decide)).c1ExtensionAtlas hΩ hbounded
      ∀ᵐ x ∂surfaceMeasure D, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂domainMeasure (m + 1) D,
      wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hleft : ∀ᵐ x ∂domainMeasure (m + 1) D, left ≤ wkpBaseCoordinateCLM lower x)
    (hright : ∀ᵐ x ∂domainMeasure (m + 1) D, wkpBaseCoordinateCLM upper x ≤ right)
    (hlower : ∀ v : H¹₀(D), (∀ᵐ x ∂domainMeasure (m + 1) D, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator
        (fun i j ↦ (ha i j).toLp hΩ hbounded ∞)
        (fun i ↦ (hb i).toLp hΩ hbounded ∞) (hc.toLp hΩ hbounded ∞) lower v ≤
          ∫ x, f (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x
            ∂domainMeasure (m + 1) D)
    (hupper : ∀ v : H¹₀(D), (∀ᵐ x ∂domainMeasure (m + 1) D, 0 ≤ baseCoordCLM v x) →
      (∫ x, f (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂domainMeasure (m + 1) D) ≤
        interiorFullDivergenceOperator
          (fun i j ↦ (ha i j).toLp hΩ hbounded ∞)
          (fun i ↦ (hb i).toLp hΩ hbounded ∞) (hc.toLp hΩ hbounded ∞) upper v) :
    ∃ (u : H¹₀(D)) (W : W^{3,2}(D)),
      wkpBaseCoordinateCLM W = baseCoordCLM u ∧
      (∀ᵐ x ∂domainMeasure (m + 1) D,
        wkpBaseCoordinateCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) D,
        baseCoordCLM u x ≤ wkpBaseCoordinateCLM upper x) ∧
      MemLp (fun x ↦ f (baseCoordCLM u x)) 2 (domainMeasure (m + 1) D) ∧
      ∀ v : H¹₀(D), interiorFullDivergenceOperator
        (fun i j ↦ (ha i j).toLp hΩ hbounded ∞)
        (fun i ↦ (hb i).toLp hΩ hbounded ∞) (hc.toLp hΩ hbounded ∞) (u : H¹(D)) v =
          ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂domainMeasure (m + 1) D := by
  let A := fun i j ↦ (ha i j).toLp hΩ hbounded ∞
  let B := fun i ↦ (hb i).toLp hΩ hbounded ∞
  let C := hc.toLp hΩ hbounded ∞
  have hA : IntegratedElliptic (multiplicationCoefficientOperator A) alpha :=
    integratedElliptic_toLp_of_contDiffUpToBoundary hΩ hbounded a ha halpha hElliptic
  have hBC : LowerOrderBounds (multiplicationFirstOrderOperator B)
      (multiplicationZeroOrderOperator C) (∑ i, ‖B i‖) ‖C‖ :=
    lowerOrderBounds_multiplication B C
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (norm_nonneg _)
      (fun i ↦ Finset.single_le_sum (fun j _ ↦ norm_nonneg (B j)) (Finset.mem_univ i))
      le_rfl
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc left right) isCompact_Icc
  obtain ⟨u, hlu, huu, hmem, heq⟩ :=
    exists_weak_solution_between_H1_barriers_of_lipschitzOn
      hΩ hbounded (hgraph.hasC1GraphBoundary (by decide)) A B C hA hBC f hK
      lower upper htraceLower htraceUpper hlr hleft hright hlower hupper
  have hrange : ∀ᵐ x ∂domainMeasure (m + 1) D,
      wkpBaseCoordinateCLM (u : H¹(D)) x ∈ Icc left right := by
    filter_upwards [hleft, hlu, huu, hright] with x hl hlu huu hr
    exact ⟨hl.trans hlu, huu.trans hr⟩
  obtain ⟨F, hF⟩ :=
    exists_h1_composition_of_lipschitzOn hΩ hbounded hK (u : H¹(D)) hrange
  have hweak : IsWeakShiftedFullDivergenceSolution A B C 0 (wkpBaseCoordinateCLM F) 0 u :=
    isWeakShiftedFullDivergenceSolution_of_reaction_eq hΩ A B C f u _ hF heq
  obtain ⟨_, _, hreg⟩ :=
    exists_global_higherOrder_estimate_of_contDiffUpToBoundary
      1 hΩ hbounded hgraph a b c ha hb hc 0 alpha halpha hElliptic
  obtain ⟨W, hW, _⟩ := hreg F u hweak
  exact ⟨u, W, hW, hlu, huu, hmem, heq⟩

end PDE.Elliptic.Semilinear

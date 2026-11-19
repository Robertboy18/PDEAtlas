/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution.Iteration
public import PDE.Elliptic.Variational.Comparison.BoundaryTrace

/-!
# Semilinear Dirichlet solutions between H¹ barriers

On a bounded open C¹ graph domain, ordered H¹ sub- and supersolutions with
signed geometric boundary traces enclose an H¹₀ solution. Trace
truncation and shifted comparison are proved by the Sobolev calculus.
The common L² monotone iteration then solves the original equation.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open Boundary Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure
open PDE.Analysis.Variational
open scoped ENNReal InnerProductSpace NNReal Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
local notation "μ" => domainMeasure (m + 1) Ω

/-- Ordered H¹ barriers with signed geometric traces enclose a zero-boundary weak solution.
The reaction may have any linear growth and a monotone linear shift. -/
theorem exists_weak_solution_between_H1_barriers_of_continuous_of_monotone_shift
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (a : Fin (m + 1) → Fin (m + 1) → DerivLp (m + 1) ∞ Ω)
    (b : Fin (m + 1) → DerivLp (m + 1) ∞ Ω) (c : DerivLp (m + 1) ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (g : ℝ → ℝ) (hg : Continuous g) {A C M : ℝ}
    (hgrowth : ∀ s, ‖g s‖ ≤ A + C * ‖s‖)
    (hmono : Monotone (fun s ↦ g s + M * s))
    (lower upper : H¹(Ω))
    (htraceLower : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace lower x ≤ 0)
    (htraceUpper : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator a b c lower v ≤
        ∫ x, g (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, g (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂μ) ≤
        interiorFullDivergenceOperator a b c upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ wkpBaseCoordinateCLM upper x) ∧
      MemLp (fun x ↦ g (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω), interiorFullDivergenceOperator a b c (u : H¹(Ω)) v =
        ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  let := hgraph.c1ExtensionAtlas hΩ hb
  obtain ⟨P⟩ := exists_inwardPartition hΩ hb (hasC1Boundary_of_local_graph hgraph)
  simp_rw [interiorFullDivergenceOperator_coe_H10]
  apply exists_weak_solution_of_shifted_interval_invariant hΩ.measurableSet hb a b c hA hbc
    g hg hgrowth hmono (wkpBaseCoordinateCLM lower) (wkpBaseCoordinateCLM upper) hlr
  · intro mu hshift _ f hf u hu
    apply AEEqFun.coeFn_le.mp
    apply base_le_ae_of_trace_le_of_shifted_interior_inequality P a b c hA hbc hshift
      lower (u : H¹(Ω))
    · rw [Trace.C1.trace_coe_H10_eq_zero]
      filter_upwards [htraceLower, Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
        («μ» := surfaceMeasure Ω)] with x hx hz
      simpa only [hz, Pi.zero_apply] using hx
    · intro v hv
      rw [interiorFullDivergenceOperator_coe_H10]
      have heq := hu v
      rw [shiftedDivergenceForm_apply, loadFunctional_eq_integral_add_mass g _ _ _ hf] at heq
      exact (add_le_add (hlower v hv) le_rfl).trans_eq heq.symm
  · intro mu hshift _ f hf u hu
    apply AEEqFun.coeFn_le.mp
    apply base_le_ae_of_trace_le_of_shifted_interior_inequality P a b c hA hbc hshift
      (u : H¹(Ω)) upper
    · rw [Trace.C1.trace_coe_H10_eq_zero]
      filter_upwards [htraceUpper, Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
        («μ» := surfaceMeasure Ω)] with x hx hz
      simpa only [hz, Pi.zero_apply] using hx
    · intro v hv
      rw [interiorFullDivergenceOperator_coe_H10]
      have heq := hu v
      rw [shiftedDivergenceForm_apply, loadFunctional_eq_integral_add_mass g _ _ _ hf] at heq
      exact heq.trans_le (add_le_add (hupper v hv) le_rfl)

/-- General H¹ sub- and supersolutions for a globally Lipschitz reaction.
The boundary signs concern the Hausdorff-surface geometric traces. -/
theorem exists_weak_solution_between_H1_barriers_of_lipschitz
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (a : Fin (m + 1) → Fin (m + 1) → DerivLp (m + 1) ∞ Ω)
    (b : Fin (m + 1) → DerivLp (m + 1) ∞ Ω) (c : DerivLp (m + 1) ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (g : ℝ → ℝ) {K : ℝ≥0} (hg : LipschitzWith K g)
    (lower upper : H¹(Ω))
    (htraceLower : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace lower x ≤ 0)
    (htraceUpper : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator a b c lower v ≤
        ∫ x, g (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, g (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂μ) ≤
        interiorFullDivergenceOperator a b c upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ wkpBaseCoordinateCLM upper x) ∧
      MemLp (fun x ↦ g (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω), interiorFullDivergenceOperator a b c (u : H¹(Ω)) v =
        ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  have hgrowth (s : ℝ) : ‖g s‖ ≤ ‖g 0‖ + (K : ℝ) * ‖s‖ := by
    have hdiff : ‖g s - g 0‖ ≤ (K : ℝ) * ‖s‖ := by
      simpa only [sub_zero] using hg.norm_sub_le s 0
    calc
      ‖g s‖ = ‖(g s - g 0) + g 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖g s - g 0‖ + ‖g 0‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖s‖ + ‖g 0‖ := add_le_add hdiff le_rfl
      _ = ‖g 0‖ + (K : ℝ) * ‖s‖ := add_comm _ _
  exact exists_weak_solution_between_H1_barriers_of_continuous_of_monotone_shift
    hΩ hb hgraph a b c hA hbc g hg.continuous hgrowth (monotone_add_mass hg le_rfl)
    lower upper htraceLower htraceUpper hlr hlower hupper

end PDE.Elliptic.Semilinear

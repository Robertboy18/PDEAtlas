/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution.BoundaryTrace

/-!
# Sub- and supersolutions for the semilinear Laplacian

Evans, *Partial Differential Equations*, §9.3, Theorem 1: ordered H¹ weak
barriers with the boundary signs enclose an H¹₀ solution of `-Δu = g(u)`.
The boundary signs use the geometric trace. Both inequalities and
the resulting equation use the integrals of the weak derivatives.

Differentiability and a globally bounded derivative of the reaction suffice;
the smoothness assumed in the reference implies these hypotheses. The domain
is bounded, open, and locally a C¹ graph, with no nonemptiness assumption.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace

open MeasureTheory Set Boundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal NNReal

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
local notation "μ" => domainMeasure (m + 1) Ω

/-- General signed-trace H¹ barriers yield a weak solution of `-Δu = g(u)`.
No zero-trace or boundedness condition is imposed on the barriers. -/
theorem exists_weak_laplacian_solution_between_H1_barriers
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (g : ℝ → ℝ) (hg : Differentiable ℝ g) {C : ℝ}
    (hderiv : ∀ s, |deriv g s| ≤ C)
    (lower upper : H¹(Ω))
    (htraceLower : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace lower x ≤ 0)
    (htraceUpper : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex (m + 1) i) lower x *
        derivCoordCLM i v x ∂μ) ≤
        ∫ x, g (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, g (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂μ) ≤
        ∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex (m + 1) i) upper x *
          derivCoordCLM i v x ∂μ) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ wkpBaseCoordinateCLM upper x) ∧
      MemLp (fun x ↦ g (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω),
        (∑ i, ∫ x, derivCoordCLM i u x * derivCoordCLM i v x ∂μ) =
          ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  classical
  let K : ℝ≥0 := ⟨C, (abs_nonneg _).trans (hderiv 0)⟩
  have hgLip : LipschitzWith K g := lipschitzWith_of_nnnorm_deriv_le hg fun s ↦ by
    exact_mod_cast hderiv s
  let a : Fin (m + 1) → Fin (m + 1) → DerivLp (m + 1) ∞ Ω :=
    fun i j ↦ (memLp_top_const (if i = j then (1 : ℝ) else 0)).toLp
      (fun _ ↦ if i = j then 1 else 0)
  have ha : multiplicationCoefficientOperator a = identityCoefficientOperator := by
    apply multiplicationCoefficientOperator_eq_identity_of_ae
    intro i j
    exact MemLp.coeFn_toLp _
  have hA : IntegratedElliptic (multiplicationCoefficientOperator a) 1 := by
    rw [ha]
    exact integratedElliptic_identity
  have hbc := lowerOrderBounds_multiplication (n := m + 1) (Ω := Ω)
    0 0 (beta := 0) (gamma := 0) le_rfl le_rfl (by simp) (by simp)
  have hform (w : H¹(Ω)) (v : H¹₀(Ω)) :
      interiorFullDivergenceOperator a 0 0 w v =
        ∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex (m + 1) i) w x *
          derivCoordCLM i v x ∂μ := by
    simp only [interiorFullDivergenceOperator, add_apply, ContinuousLinearMap.comp_apply,
      ha, interiorVariableCoeffForm_identity, interiorLowerOrderOperator_apply,
      Pi.zero_apply, Lp.zero_smul, Finset.sum_const_zero, add_zero,
      map_zero]
  have hlower' : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator a 0 0 lower v ≤
        ∫ x, g (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x ∂μ := by
    intro v hv
    rw [hform]
    exact hlower v hv
  have hupper' : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, g (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂μ) ≤
        interiorFullDivergenceOperator a 0 0 upper v := by
    intro v hv
    rw [hform]
    exact hupper v hv
  obtain ⟨u, hlu, huu, hmem, heq⟩ :=
    exists_weak_solution_between_H1_barriers_of_lipschitz hΩ hb hgraph a 0 0 hA hbc g hgLip
      lower upper htraceLower htraceUpper hlr hlower' hupper'
  refine ⟨u, hlu, huu, hmem, fun v ↦ ?_⟩
  simpa only [hform, wkpCoordinateCLM_apply, derivCoordCLM_apply] using heq v

end PDE.Elliptic.Semilinear

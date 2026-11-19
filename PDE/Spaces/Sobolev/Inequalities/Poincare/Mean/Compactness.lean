/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Normed.Operator.Compact.Coercivity
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Centering
import PDE.Spaces.Sobolev.GraphSpace.Norms
import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Compactness and the mean-subtracted Poincaré estimate

The integral-zero Sobolev subspace is closed. On a connected open domain its gradient
is injective, since a function with zero weak gradient is constant almost everywhere.
A compact term in a graph norm estimate can therefore be removed on this subspace.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The Sobolev graph norm is bounded by the base norm plus a dimension multiple of
the vector-valued weak gradient norm. This estimate also holds at exponent infinity. -/
theorem norm_le_base_add_gradient (U : W^{1,p}(Ω)) :
    ‖U‖ ≤ ‖wkpBaseCoordinateCLM U‖ + n * ‖∇ U‖ := by
  apply (ambient_norm_le_base_add_sum_deriv U.val).trans
  apply add_le_add_right
  calc
    ∑ i : Fin n, ‖(U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖
        ≤ ∑ _i : Fin n, ‖∇ U‖ :=
      Finset.sum_le_sum fun i _ ↦ norm_derivCoordinate_le_wkpGradientCLM U i
    _ = n * ‖∇ U‖ := by simp

variable [IsFiniteMeasure (domainMeasure n Ω)]

/-- A compact term controlling the base norm gives Poincaré's estimate after subtracting
the spatial mean. Later domain theorems discharge this compactness hypothesis using Rellich. -/
theorem exists_norm_subtractMean_le_of_compact_estimate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (J : W^{1,p}(Ω) →L[ℝ] F) (hJ : IsCompactOperator J)
    (A B : ℝ≥0) (hbound : ∀ U, ‖U‖ ≤ A * ‖J U‖ + B * ‖∇ U‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(Ω),
      ‖subtractMean U‖ ≤ C * ‖∇ U‖ := by
  let K := (wkpIntegralCLM (n := n) (p := p) (Ω := Ω)).ker
  let : NormedSpace ℝ K := inferInstance
  have hK : IsClosed (K : Set (W^{1,p}(Ω))) :=
    (wkpIntegralCLM (n := n) (p := p) (Ω := Ω)).isClosed_ker
  have : CompleteSpace K := hK.completeSpace_coe
  let G : K →L[ℝ] Lp (ℝ^n) p (domainMeasure n Ω) :=
    wkpGradientCLM.comp K.subtypeL
  have hG : Function.Injective G := by
    intro U V huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eq_zero_of_integral_eq_zero_of_gradient_eq_zero hΩ hconn
    · rw [map_sub, show wkpIntegralCLM U.val = 0 from U.property,
        show wkpIntegralCLM V.val = 0 from V.property, sub_self]
    · rw [map_sub, show ∇ U.val = ∇ V.val from huv, sub_self]
  have hcompact : IsCompactOperator (((A : ℝ) • J).comp K.subtypeL) :=
    (hJ.smul (A : ℝ)).comp_clm K.subtypeL
  have hboundK (U : K) :
      ‖U‖ ≤ ‖(((A : ℝ) • J).comp K.subtypeL) U‖ + B * ‖G U‖ := by
    simpa only [G, ContinuousLinearMap.comp_apply, smul_apply,
      Submodule.subtypeL_apply, norm_smul, Real.norm_of_nonneg A.coe_nonneg,
      Submodule.norm_coe] using hbound U.val
  obtain ⟨C, hC, hest⟩ :=
    @IsCompactOperator.exists_norm_le_of_injective K F (Lp (ℝ^n) p (domainMeasure n Ω))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance _ hcompact G B hboundK hG
  refine ⟨C, hC, fun U ↦ ?_⟩
  have h := hest (⟨subtractMean U, wkpIntegralCLM_subtractMean U⟩ : K)
  change ‖subtractMean U‖ ≤ C * ‖∇ (subtractMean U)‖ at h
  simpa only [wkpGradientCLM_subtractMean] using h

end SobolevSpace.GraphSpace

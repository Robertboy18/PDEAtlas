/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.LpMaps
public import PDE.Parabolic.Regularity.Autonomous.Full.Estimate
public import PDE.Parabolic.Regularity.Autonomous.Higher.EllipticBootstrap
import PDE.Parabolic.Regularity.SpatialH2.WeakResidual

/-!
# Elliptic lifting for the full autonomous equation

At almost every time, the elliptic load is `f - Ru - u'`. Bounds for its
three pivot-valued terms yield an essentially bounded spatial `H²` lift.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The full equation has an `L∞(H²)` lift once its forcing, energy state,
and pivot time derivative are essentially bounded. -/
theorem exists_full_form_spatial_h2_lift
    {t₀ t₁ : ℝ} (hΩ : C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
    (u v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
    (initial : DerivLp n 2 Ω) (F U V : ℝ) (hV : 0 ≤ V)
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen)
      (fun _ ↦ autonomousDivergenceFormOperator A +
        (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.comp R)
      ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).pivotToDual.compLpL
        2 (volume.restrict (Ioc t₀ t₁)) f) u initial)
    (hut : HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen) u
      ((h10L2GelfandTriple hΩ.toC1ExtensionAtlas.isOpen).energyToDual.compLpL
        2 (volume.restrict (Ioc t₀ t₁)) v))
    (hfBound : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ‖f t‖ ≤ F)
    (huBound : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ‖u t‖ ≤ U)
    (hvBound : ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
      ‖baseCoordCLM (n := n) (Ω := Ω) (v t)‖ ≤ V) :
    ∃ U₂ : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁)),
      (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
        lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2)
          (by omega) (U₂ t) = h10SubtypeL (n := n) (Ω := Ω) (u t)) ∧
      MemLp (fun t ↦ U₂ t) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
      ∀ᵐ t ∂volume.restrict (Ioc t₀ t₁), ‖U₂ t‖ ≤
        ‖globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic‖ *
          (F + ‖R‖ * U + V) := by
  let hopen := hΩ.toC1ExtensionAtlas.isOpen
  let T := h10L2GelfandTriple hopen
  let μ := volume.restrict (Ioc t₀ t₁)
  let utH := T.inclusion.compLpL 2 μ v
  have hutBound : ∀ᵐ t ∂μ, ‖utH t‖ ≤ Real.sqrt (V ^ 2) := by
    filter_upwards [T.inclusion.coeFn_compLpL v, hvBound] with t heq hb
    rw [heq, Real.sqrt_sq hV]
    exact hb
  have hutH : HasGelfandWeakTimeDerivativeOn T u (T.pivotToDual.compLpL 2 μ utH) := by
    rw [T.pivotToDual_compLpL_inclusion]
    exact hut
  let rhs := f - R.compLpL 2 μ u
  have hrhs : ∀ᵐ t ∂μ, ‖rhs t‖ ≤ F + ‖R‖ * U := by
    filter_upwards [hfBound, huBound, Lp.coeFn_sub f (R.compLpL 2 μ u),
      R.coeFn_compLpL u] with t hft hut hsub hR
    change ‖(f - R.compLpL 2 μ u) t‖ ≤ _
    rw [hsub, Pi.sub_apply, hR]
    exact (norm_sub_le _ _).trans (add_le_add hft
      ((R.le_opNorm (u t)).trans (mul_le_mul_of_nonneg_left hut (norm_nonneg R))))
  have huPrincipal := hu.sub_pivot_perturbation (autonomousDivergenceFormOperator A) R
  have hresidual := ae_weak_residual_identity_of_integrated_solution hopen A
    rhs utH u initial huPrincipal hutH
  have hlift := exists_spatial_h2_lift t₀ t₁ hΩ A a haRep haC1 rhs utH u
    alpha halpha hElliptic (F + ‖R‖ * U) (V ^ 2) hrhs hutBound hresidual
  obtain ⟨U₂, hU₂, hU₂Top, hU₂Bound⟩ := hlift
  refine ⟨U₂, ?_, hU₂Top, ?_⟩
  · filter_upwards [hU₂] with t ht
    exact ht
  · simpa only [Real.sqrt_sq hV] using hU₂Bound

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

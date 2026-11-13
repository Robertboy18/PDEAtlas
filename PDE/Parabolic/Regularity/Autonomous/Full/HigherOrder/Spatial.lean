/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Bochner
public import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# The higher spatial step for the full parabolic equation

A pivot-valued weak time derivative turns the weak evolution equation into
the elliptic equation `Lu = f - uₜ` at almost every time. The Bochner form of
higher elliptic regularity,
`exists_higherOrder_lp_estimate_of_contDiffUpToBoundary`, then constructs the
next spatial representative.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The pivot weak time derivative identifies the full elliptic residual,
including the drift and potential, almost everywhere in time. -/
theorem ae_full_elliptic_residual
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (f v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (g : DerivLp n 2 Ω)
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u g)
    (hut : HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) v)) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ w : H¹₀(Ω),
      P.form hopen hbounded (u t) w = ⟪f t - v t, baseCoordCLM w⟫_ℝ := by
  let T := h10L2GelfandTriple hopen
  have heq := IsGelfandIntegratedWeakSolution.ae_weak_equation
    (fun _ ↦ aestronglyMeasurable_const) ‖P.form hopen hbounded‖
    (Eventually.of_forall fun _ ↦ le_rfl) hu hut
  filter_upwards [heq, T.pivotToDual.coeFn_compLpL f,
    T.pivotToDual.coeFn_compLpL v] with t ht hft hvt
  intro w
  have h := congrArg (fun ell : StrongDual ℝ (H¹₀(Ω)) ↦ ell w) ht
  rw [hft, hvt] at h
  simp only [add_apply, GelfandTriple.pivotToDual_apply] at h
  change ⟪v t, baseCoordCLM w⟫_ℝ + P.form hopen hbounded (u t) w =
    ⟪f t, baseCoordCLM w⟫_ℝ at h
  rw [inner_sub_left]
  linarith only [h]

/-- Higher regularity of the forcing and the time derivative gives higher
spatial regularity of every original weak solution, with its full estimate. -/
theorem exists_higher_spatial_lift [Fact (0 < n)] (P : SmoothFullCoefficients n Ω) (r : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (r + 2) Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (F V : Lp (W^{r,2}(Ω)) 2 (volume.restrict (Ioc a b)))
        (f v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (g : DerivLp n 2 Ω),
      (∀ᵐ t ∂volume.restrict (Ioc a b), wkpBaseCoordinateCLM (F t) = f t) →
      (∀ᵐ t ∂volume.restrict (Ioc a b), wkpBaseCoordinateCLM (V t) = v t) →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) f) u g →
      HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) v) →
      ∃ U : Lp (W^{(r + 2),2}(Ω)) 2 (volume.restrict (Ioc a b)),
        (∀ᵐ t ∂volume.restrict (Ioc a b), wkpBaseCoordinateCLM (U t) = baseCoordCLM (u t)) ∧
        ‖U‖ ≤ K * (‖F‖ + ‖V‖ + ‖u‖) := by
  obtain ⟨K, hK, hreg⟩ := exists_higherOrder_lp_estimate_of_contDiffUpToBoundary
    (volume.restrict (Ioc a b)) r hopen hbounded hgraph
    P.principal P.drift P.potential (P.principal_smooth (r + 1))
    (P.drift_smooth (r + 1)) (P.potential_smooth (r + 1)) 0 alpha halpha hell
  refine ⟨K, hK, ?_⟩
  intro F V f v u g hF hV hu hut
  have hres := ae_full_elliptic_residual P hopen hbounded f v u g hu hut
  have he : ∀ᵐ t ∂volume.restrict (Ioc a b),
      IsWeakShiftedFullDivergenceSolution
        (fun i j ↦ (P.principal_smooth (r + 1) i j).toLp hopen hbounded ∞)
        (fun i ↦ (P.drift_smooth (r + 1) i).toLp hopen hbounded ∞)
        ((P.potential_smooth (r + 1)).toLp hopen hbounded ∞)
        0 (wkpBaseCoordinateCLM ((F - V) t)) 0 (u t) := by
    filter_upwards [hres, hF, hV, Lp.coeFn_sub F V] with t ht hFt hVt hsub
    apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen _ _ _ _ _ _ _).1
    intro w
    simp only [shiftedDivergenceForm_apply, zero_mul, add_zero,
      generalizedLoad_apply, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero]
    rw [hsub, Pi.sub_apply, map_sub, hFt, hVt]
    exact ht w
  obtain ⟨U, hbase, hnorm⟩ := hreg (F - V) u he
  exact ⟨U, hbase, hnorm.trans (mul_le_mul_of_nonneg_left
    (add_le_add (norm_sub_le F V) le_rfl) hK.le)⟩

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

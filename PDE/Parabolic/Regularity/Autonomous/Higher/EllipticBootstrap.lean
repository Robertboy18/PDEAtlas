/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
import PDE.Parabolic.Regularity.SpatialH2.WeakResidual

/-!
# Elliptic lift for improved parabolic regularity

This is the elliptic step in the symmetric principal-part case of Evans's §7.1.3,
Theorem 5(ii). Evans bounds `‖u_m‖_{H²}` for the Galerkin approximations with the
inequality (54) (step 6 of his proof); we apply the elliptic estimate to the limit, as
in step 3 of his proof of part (i).

At almost every time, the parabolic equation is rewritten as the elliptic
equation `A u = f - uₜ`. The global `H²` solution operator is then applied
pointwise. An `L∞_t L²_x` bound on `f - uₜ` gives an `L∞_t H²_x` lift whose
restriction to `H¹` agrees with the original energy-space trajectory.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), p. 334; §7.1.3,
  steps 3 and 6 of the proof of Theorem 5 (Improved regularity), (49) and (53)-(54), pp. 384-385.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat
namespace AutonomousRegularity

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

attribute [local instance 101] secondCountableTopologyEither_of_left

/-- The order-one restriction of the global `H²` solution operator agrees with a
given weak divergence-form solution. -/
private theorem global_h2_solve_clm_order_one_eq_of_weak_divergence_solution
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (rhs : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (huDivergence :
      IsWeakDivergenceSolution
        (n := n) (Ω := Ω)
        (coefficientBase A) rhs u) :
    lowerOrderCLM
        (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
        (by omega)
        (globalH2SolveCLM hΩ A a haRep haC1
          alpha halpha hElliptic rhs) =
      h10SubtypeL (n := n) (Ω := Ω) u := by
  let coeff := coefficientBase A
  have hueq :=
    eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution
      hΩ A a haRep alpha halpha hElliptic rhs u huDivergence
  exact
    (globalH2SolveCLM_orderOne hΩ A a haRep haC1
      alpha halpha hElliptic rhs).trans
        (congrArg
          (h10SubtypeL (n := n) (Ω := Ω))
          hueq.symm)

/-- A continuous linear image of an essentially bounded right-hand side is
essentially bounded, with the bound controlled by the operator norm. -/
private theorem memLp_top_and_ae_norm_le_of_continuous_linear_map
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : Measure ℝ}
    (solve : X →L[ℝ] Y)
    (rhs : Lp X 2 μ) (U2 : Lp Y 2 μ) (bound : ℝ)
    (hU2Coe : (fun t ↦ U2 t) =ᵐ[μ] fun t ↦ solve (rhs t))
    (hrhsBound : ∀ᵐ t ∂μ, ‖rhs t‖ ≤ bound) :
    MemLp (fun t ↦ U2 t) (⊤ : ℝ≥0∞) μ ∧
      ∀ᵐ t ∂μ, ‖U2 t‖ ≤ ‖solve‖ * bound := by
  have hrhsTop : MemLp (fun t ↦ rhs t) (⊤ : ℝ≥0∞) μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable rhs) bound hrhsBound
  have hU2Top : MemLp (fun t ↦ U2 t) (⊤ : ℝ≥0∞) μ :=
    (hrhsTop.continuousLinearMap_comp solve).ae_eq hU2Coe.symm
  have hU2Bound :
      ∀ᵐ t ∂μ, ‖U2 t‖ ≤ ‖solve‖ * bound := by
    filter_upwards [hU2Coe, hrhsBound] with t hU2t hrhs
    rw [hU2t]
    exact (solve.le_opNorm (rhs t)).trans
      (mul_le_mul_of_nonneg_left hrhs (norm_nonneg solve))
  exact ⟨hU2Top, hU2Bound⟩

/-- Applying the global elliptic solution operator to `f - uₜ` pointwise in time
gives an `L²_t H²` lift whose `H¹` restriction is `u` almost everywhere. If
`‖f‖ ≤ forcingBound` and `‖uₜ‖ ≤ √energyBudget` a.e., the lift is essentially
bounded by `‖S₂‖ (forcingBound + √energyBudget)`. -/
theorem exists_spatial_h2_lift
    (t₀ t₁ : ℝ)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f utH : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (u : Lp
      (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (forcingBound energyBudget : ℝ)
    (hfBound : ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ‖f t‖ ≤ forcingBound)
    (hutHBound : ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ‖utH t‖ ≤ Real.sqrt energyBudget)
    (huEvolution : ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ∀ v : H¹₀(Ω),
        ⟪utH t,
          baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ +
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A))
            ((u : ℝ → H¹₀(Ω)) t) v =
          ⟪f t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ) :
    ∃ h2Lift : Lp (W^{2,2}(Ω)) 2
        (volume.restrict (Set.Ioc t₀ t₁)),
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
          fun t ↦
            h10SubtypeL (n := n) (Ω := Ω)
              ((u : ℝ → H¹₀(Ω)) t)) ∧
      MemLp (fun t ↦ h2Lift t) (⊤ : ℝ≥0∞)
        (volume.restrict (Set.Ioc t₀ t₁)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
        ‖h2Lift t‖ ≤
          ‖globalH2SolveCLM hΩ A a haRep haC1
            alpha halpha hElliptic‖ *
            (forcingBound + Real.sqrt energyBudget) := by
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  let V := H¹₀(Ω)
  let H := DerivLp n 2 Ω
  let _ : MeasurableSpace H := borel H
  let _ : BorelSpace H := ⟨rfl⟩
  let solve2 : H →L[ℝ] W^{2,2}(Ω) := globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic
  let rhs : Lp H 2 μ := f - utH
  let h2Lift : Lp (W^{2,2}(Ω)) 2 μ := solve2.compLpL 2 μ rhs
  have hrhsBound : ∀ᵐ t ∂μ, ‖rhs t‖ ≤ forcingBound + Real.sqrt energyBudget := by
    filter_upwards [hfBound, hutHBound, Lp.coeFn_sub f utH] with t hfB hutB hsub
    rw [show rhs t = f t - utH t from hsub]
    exact (norm_sub_le _ _).trans (add_le_add hfB hutB)
  have hH2LiftCoe : (fun t ↦ h2Lift t) =ᵐ[μ] fun t ↦ solve2 (rhs t) :=
    solve2.coeFn_compLpL rhs
  obtain ⟨hH2LiftTop, hH2LiftBound⟩ := memLp_top_and_ae_norm_le_of_continuous_linear_map
    solve2 rhs h2Lift (forcingBound + Real.sqrt energyBudget) hH2LiftCoe hrhsBound
  refine ⟨h2Lift, ?_, hH2LiftTop, hH2LiftBound⟩
  filter_upwards [hH2LiftCoe, huEvolution, Lp.coeFn_sub f utH] with t hH2LiftT hut hrhsCoe
  rw [hH2LiftT]
  refine global_h2_solve_clm_order_one_eq_of_weak_divergence_solution hΩ A a haRep haC1 alpha
    halpha hElliptic (rhs t) ((u : ℝ → V) t) ?_
  rw [show rhs t = f t - utH t from hrhsCoe]
  exact is_weak_divergence_solution_of_weak_residual_identity hΩ.toC1ExtensionAtlas.isOpen A
    (f t) (utH t) ((u : ℝ → V) t) hut

end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.PairedL2Differentiation.Approximation
public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Compactness.Lp.Ultrafilter
import PDE.Analysis.Evolution.Compactness.PivotWeakDerivative
import PDE.Analysis.Evolution.Galerkin.Measurable.Bounds
import PDE.Analysis.Evolution.Galerkin.Measurable.IntegratedIdentity
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.Evolution.Integrated.WeakLimit
import PDE.Analysis.WeakCompactness

/-!
# Common-subnet compactness for a differentiated Galerkin family

An autonomous Galerkin family and its `L²`-forced differentiated family
converge along one common ultrafilter. Only the
original pivot velocity is compactified. The weak derivative of the
differentiated limit is recovered as the canonical `V*` residual, matching the
conclusion `u'' ∈ L²(0, T; H⁻¹(U))` of Evans §7.1.3, Theorem 5(ii), without imposing an
`L²(H)` bound on the second derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5(ii) and step 7 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
open PDE.Analysis

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Projected equations with a measurable load determine the weak limit equation
for its Bochner class; the choice of representative does not enter the passage. -/
private theorem integrated_solution_toLp_of_projected_weak_limit
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hab : a < b)
    (ell : ℝ → StrongDual ℝ V)
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (u : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)))
    (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
    {l : Filter ℕ} [l.NeBot]
    (huweak : Filter.Tendsto (fun n ↦ toWeakSpace ℝ _ (u n)) l
      (nhds (toWeakSpace ℝ _ uLimit)))
    (hl : l ≤ Filter.atTop) (R : ℝ) (huR : ∀ n, ‖u n‖ ≤ R)
    (project : ℕ → V → V)
    (hproject : ∀ v : V,
      Filter.Tendsto (fun n ↦ project n v) Filter.atTop (nhds v))
    (u₀ : ℕ → H) (uInit : H)
    (hu₀ : Filter.Tendsto u₀ Filter.atTop (nhds uInit))
    (happrox : ∀ n (v : V) (τ : TimeTest a b),
      -(∫ t, inner ℝ (T.inclusion (u n t))
          (T.inclusion (project n v)) * τ.derivToLp t
            ∂(volume.restrict (Set.Ioc a b))) +
          ∫ t, B t (u n t) (project n v) * τ.toLp t
            ∂(volume.restrict (Set.Ioc a b)) =
        (∫ t, ell t (project n v) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b))) +
          inner ℝ (u₀ n) (T.inclusion (project n v)) *
            τ.toFun a) :
    IsGelfandIntegratedWeakSolution T B (hell.toLp ell) uLimit uInit := by
  refine isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit
    T B hBmeas MB hMB hBbound hab (hell.toLp ell) u uLimit huweak hl R huR
    project hproject u₀ uInit hu₀ fun n v τ ↦ ?_
  have hforcing :
      (∫ t, hell.toLp ell t (project n v) * τ.toLp t ∂volume.restrict (Ioc a b)) =
        ∫ t, ell t (project n v) * τ.toLp t ∂volume.restrict (Ioc a b) :=
    integral_congr_ae (hell.coeFn_toLp.mono fun t ht ↦ by simp only [ht])
  exact hforcing ▸ happrox n v τ

/--
Common-subnet compactness for an original autonomous Galerkin family and
its `L²`-forced differentiated family.

Only the original pivot velocity is compactified. The weak derivative of
the differentiated limit is the canonical `V*` residual
`ellDot - B du`, which gives Evans's conclusion `u'' ∈ L²(0, T; H⁻¹(U))`
(§7.1.3, Theorem 5(ii)) in this setting.
-/
theorem IsGelfandIntegratedWeakSolution.exists_of_paired_l2_differentiated_galerkin_families
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : V →L[ℝ] StrongDual ℝ V)
    (ell ellDot : ℝ → StrongDual ℝ V)
    {a b C M MB : ℝ}
    (hab : a < b) (hC : 0 < C) (hMB : 0 ≤ MB)
    (hBbound : ∀ᵐ _t ∂(volume.restrict (Set.Ioc a b)), ‖B‖ ≤ MB)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w)
    (hell : MemLp ell 2 (volume.restrict (Set.Ioc a b)))
    (hellDot : MemLp ellDot 2 (volume.restrict (Set.Ioc a b)))
    (u₀ du₀ : ∀ n, S n)
    (uInit duInit : H)
    (hu₀ : Filter.Tendsto (fun n ↦ T.inclusion (u₀ n : V))
      Filter.atTop (nhds uInit))
    (hdu₀ : Filter.Tendsto (fun n ↦ T.inclusion (du₀ n : V))
      Filter.atTop (nhds duInit))
    (initialPivotBoundSq derivativeInitialPivotBoundSq : ℝ)
    (hInitialPivotBoundSq : 0 ≤ initialPivotBoundSq)
    (hDerivativeInitialPivotBoundSq : 0 ≤ derivativeInitialPivotBoundSq)
    (hu₀Bound : ∀ n,
      ‖T.inclusion (u₀ n : V)‖ ^ 2 ≤ initialPivotBoundSq)
    (hdu₀Bound : ∀ n,
      ‖T.inclusion (du₀ n : V)‖ ^ 2 ≤ derivativeInitialPivotBoundSq)
    (G : ∀ n, AEGelfandGalerkinApproximation T (S n)
      (fun _ ↦ B) ell a b C M (u₀ n))
    (DG : ∀ n, L2DifferentiatedGalerkinApproximation
      T (S n) B ellDot a b (du₀ n))
    (velocityBoundSq : ℝ)
    (hVelocityBoundSq : 0 ≤ velocityBoundSq)
    (hvelocity : ∀ n,
      ‖(G n).pivotDerivativeLp T (S n)‖ ^ 2 ≤ velocityBoundSq)
    (htrajectoryLink : ∀ n,
      T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b))
          ((DG n).ambientTrajectoryLp hab.le) =
        (G n).pivotDerivativeLp T (S n)) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (duH : Lp H 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (ddu : Lp (StrongDual ℝ V) 2
          (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) ell u uInit ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) duH) ∧
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) ellDot du duInit ∧
      HasGelfandWeakTimeDerivativeOn T du ddu ∧
      T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b)) du = duH ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        T.pivotToDual (duH t) + B (u t) = ell t) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ddu t + B (du t) = ellDot t) ∧
      ‖du‖ ^ 2 ≤
        (2 / C) *
          ((1 / 2 : ℝ) * derivativeInitialPivotBoundSq +
            (1 / (2 * C)) * ‖hellDot.toLp ellDot‖ ^ 2) := by
  have hBmeas : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Ioc a b)) := by fun_prop
  classical
  let μ := volume.restrict (Set.Ioc a b)
  have hprojectEnergy : ∀ v : V, Filter.Tendsto
      (fun n ↦ ((P n).energyProjection v : V))
      Filter.atTop (nhds v) :=
    StableTrialProjection.tendsto_energyProjection_of_eventually_approximable
      P hdenseEnergy
  let state : ℕ → Lp V 2 μ :=
    fun n ↦ (G n).ambientTrajectoryLp hab.le
  let velocity : ℕ → Lp H 2 μ :=
    fun n ↦ (G n).pivotDerivativeLp T (S n)
  let derivativeState : ℕ → Lp V 2 μ :=
    fun n ↦ (DG n).ambientTrajectoryLp hab.le
  let stateBoundSq : ℝ :=
    (2 / C) *
      ((1 / 2 : ℝ) * initialPivotBoundSq +
        (M ^ 2 / (2 * C)) * (b - a))
  let derivativeStateBoundSq : ℝ :=
    (2 / C) *
      ((1 / 2 : ℝ) * derivativeInitialPivotBoundSq +
        (1 / (2 * C)) * ‖hellDot.toLp ellDot‖ ^ 2)
  have hStateBoundSq : 0 ≤ stateBoundSq := by dsimp [stateBoundSq]; positivity
  have hDerivativeStateBoundSq : 0 ≤ derivativeStateBoundSq := by
    dsimp [derivativeStateBoundSq]; positivity
  have hstateSq (n : ℕ) : ‖state n‖ ^ 2 ≤ stateBoundSq :=
    ((G n).norm_ambientTrajectoryLp_sq_le hab.le hC).trans <| by
      dsimp [stateBoundSq]; gcongr; exact hu₀Bound n
  have hDerivativeStateSq (n : ℕ) : ‖derivativeState n‖ ^ 2 ≤ derivativeStateBoundSq :=
    ((DG n).norm_ambientTrajectoryLp_sq_le hab.le hC hcoercive hellDot).trans <| by
      dsimp [derivativeStateBoundSq]; gcongr; exact hdu₀Bound n
  obtain ⟨u, duH, U₂, hU₂, huWeak₂, hduHWeak₂, hOriginalWeakDerivative⟩ :=
    exists_hasGelfandWeakTimeDerivativeOn_of_bounded_pivot_derivatives
      T state velocity (isBounded_range_of_norm_sq_le state hStateBoundSq hstateSq)
      (isBounded_range_of_norm_sq_le velocity hVelocityBoundSq hvelocity)
      (fun n ↦ (G n).hasGelfandWeakTimeDerivativeOn_pivotDerivativeLp T (S n) hab.le)
  obtain ⟨du, U, hU₃, hduWeak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
      (U₂ : Filter ℕ) derivativeState
      (isBounded_range_of_norm_sq_le derivativeState hDerivativeStateBoundSq hDerivativeStateSq)
  have hU : (U : Filter ℕ) ≤ Filter.atTop := hU₃.trans hU₂
  have hBv := fun v ↦ hBmeas.apply_continuousLinearMap v
  have hOriginalLp : IsGelfandIntegratedWeakSolution T (fun _ ↦ B) (hell.toLp ell) u uInit :=
    integrated_solution_toLp_of_projected_weak_limit T (fun _ ↦ B) hBv MB hMB hBbound hab ell
      hell state u (huWeak₂.mono_left hU₃) hU (√stateBoundSq)
      (fun n ↦ Real.le_sqrt_of_sq_le (hstateSq n))
      (fun n v ↦ ((P n).energyProjection v : V)) hprojectEnergy
      (fun n ↦ T.inclusion (u₀ n : V)) uInit hu₀
      fun n v τ ↦ (G n).integratedInitialIdentity hab.le hBv MB hBbound
        ((P n).energyProjection v) τ
  have hDerivativeLp :
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B) (hellDot.toLp ellDot) du duInit :=
    integrated_solution_toLp_of_projected_weak_limit T (fun _ ↦ B) hBv MB hMB hBbound hab ellDot
      hellDot derivativeState du hduWeak hU (√derivativeStateBoundSq)
      (fun n ↦ Real.le_sqrt_of_sq_le (hDerivativeStateSq n))
      (fun n v ↦ ((P n).energyProjection v : V)) hprojectEnergy
      (fun n ↦ T.inclusion (du₀ n : V)) duInit hdu₀
      fun n v τ ↦ (DG n).integratedInitialIdentity hab.le hBmeas MB hBbound
        ((P n).energyProjection v) τ
  have hDerivativeWeakDerivative := hDerivativeLp.hasWeakTimeDerivative_residual hBv MB hBbound
  refine ⟨u, duH, du, _, hOriginalLp.congr_forcing_ae hell.coeFn_toLp, hOriginalWeakDerivative,
    hDerivativeLp.congr_forcing_ae hellDot.coeFn_toLp, hDerivativeWeakDerivative,
    compLpL_eq_of_tendsto_weak T.inclusion derivativeState velocity du duH hduWeak
      (hduHWeak₂.mono_left hU₃) htrajectoryLink, ?_, ?_,
    (Real.le_sqrt (norm_nonneg _) hDerivativeStateBoundSq).mp
      (WeakCompactness.norm_le_of_tendsto_of_norm_le hduWeak
        (.of_forall fun n ↦ Real.le_sqrt_of_sq_le (hDerivativeStateSq n)))⟩
  · filter_upwards [hOriginalLp.ae_weak_equation hBv MB hBbound hOriginalWeakDerivative,
      T.pivotToDual.coeFn_compLpL duH, hell.coeFn_toLp] with t ht hduCoe hellCoe
    simpa only [hduCoe, hellCoe] using ht
  · filter_upwards [hDerivativeLp.ae_weak_equation hBv MB hBbound hDerivativeWeakDerivative,
      hellDot.coeFn_toLp] with t ht hellDotCoe
    simpa only [hellDotCoe] using ht

end PDE.Analysis.Evolution

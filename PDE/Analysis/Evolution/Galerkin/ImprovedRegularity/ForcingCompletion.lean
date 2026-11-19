/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.PivotDerivative
public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.Integrated.TimeDependentForm
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import PDE.Analysis.Evolution.Compactness.Lp.PointwiseBounds
import PDE.Analysis.Evolution.Compactness.PivotWeakDerivative
import PDE.Analysis.Evolution.Galerkin.Measurable.Bounds
import PDE.Analysis.Evolution.Galerkin.Measurable.IntegratedIdentity
import PDE.Analysis.Evolution.Integrated.EnergyBounds
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.Evolution.Integrated.WeakLimit
import PDE.Analysis.WeakCompactness

/-!
# Completion of pivot-forced Galerkin solutions

We prove Evans's improved estimate (§7.1.3, Theorem 5(i)) first for regular forcing and
then extend it to arbitrary Bochner `L²(H)` data by completion. The energy estimate enters
the completion only through its hypotheses.

Bounded continuous pivot loads are dense in `L²(H)`. Coercive continuous
dependence gives strong convergence of the states, while weak compactness
preserves the uniformly bounded pivot derivatives. Uniqueness of weak time
derivatives finally identifies the limit with the equation residual.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 5(i). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis

namespace PDE.Analysis.Evolution

/-! ## Completion of pivot-forced solutions -/

section PivotForcingCompletion

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace IsGelfandIntegratedWeakSolution

/-- A pivot-valued weak derivative of an integrated solution is its canonical
residual, by uniqueness of distributional time derivatives. -/
private theorem pivot_derivative_eq_residual
    [CompleteSpace V]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b MB : ℝ}
    (ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (u : Lp V 2 (volume.restrict (Ioc a b)))
    (du : Lp H 2 (volume.restrict (Ioc a b))) {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hsolution : IsGelfandIntegratedWeakSolution T B ell u uInit)
    (hderivative : HasGelfandWeakTimeDerivativeOn T u
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) du)) :
    T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) du =
      gelfandResidualLp B ell u hBmeas MB hBbound :=
  hderivative.eq (hsolution.hasWeakTimeDerivative_residual hBmeas MB hBbound)

/-- Convergent energy projections allow the measurable Galerkin equations to
pass to any bounded weak state limit, independently of velocity compactness. -/
private theorem of_galerkin_weak_limit
    [CompleteSpace V]
    (T : GelfandTriple (V := V) (H := H)) (S : ℕ → Submodule ℝ V)
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdense : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C M MB D : ℝ} (hab : a < b) (hMB : 0 ≤ MB)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (u₀ : ∀ n, S n) (uInit : H)
    (hu₀ : Filter.Tendsto (fun n ↦ T.inclusion (u₀ n : V)) Filter.atTop (nhds uInit))
    (G : ∀ n, AEGelfandGalerkinApproximation T (S n) B ell a b C M (u₀ n))
    (u : Lp V 2 (volume.restrict (Ioc a b))) {l : Filter ℕ} [l.NeBot]
    (hu : Filter.Tendsto
      (fun n ↦ toWeakSpace ℝ _ ((G n).ambientTrajectoryLp hab.le)) l
      (nhds (toWeakSpace ℝ _ u))) (hl : l ≤ Filter.atTop)
    (hbound : ∀ n, ‖(G n).ambientTrajectoryLp hab.le‖ ^ 2 ≤ D) :
    IsGelfandIntegratedWeakSolution T B (hell.toLp ell) u uInit := by
  refine isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit
    T B (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hMB hBbound hab
    (hell.toLp ell) (fun n ↦ (G n).ambientTrajectoryLp hab.le) u hu hl
    (√D) (fun n ↦ Real.le_sqrt_of_sq_le (hbound n))
    (fun n v ↦ ((P n).energyProjection v : V))
    (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P hdense)
    (fun n ↦ T.inclusion (u₀ n : V)) uInit hu₀ fun n v τ ↦ ?_
  have hforcing :
      (∫ t, hell.toLp ell t ((P n).energyProjection v : V) * τ.toLp t
        ∂volume.restrict (Ioc a b)) =
      ∫ t, ell t ((P n).energyProjection v : V) * τ.toLp t ∂volume.restrict (Ioc a b) :=
    integral_congr_ae (hell.coeFn_toLp.mono fun t ht ↦ by simp only [ht])
  exact hforcing ▸ (G n).integratedInitialIdentity hab.le
    (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound ((P n).energyProjection v) τ

/-- Coercive continuous dependence turns convergence of the forcing into a
strong state limit satisfying the limiting equation. -/
private theorem exists_state_limit_of_forcing_tendsto
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b C MB : ℝ}
    (hab : a < b) (hC : 0 < C)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hcoercive : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) (ell : ℕ → Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (ellLimit : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (u : ℕ → Lp V 2 (volume.restrict (Ioc a b)))
    (hellTendsto : Filter.Tendsto ell Filter.atTop (nhds ellLimit))
    (hsolution : ∀ n, IsGelfandIntegratedWeakSolution T B (ell n) (u n) uInit) :
    ∃ uLimit : Lp V 2 (volume.restrict (Ioc a b)),
      Filter.Tendsto u Filter.atTop (nhds uLimit) ∧
      IsGelfandIntegratedWeakSolution T B ellLimit uLimit uInit := by
  have huCauchy : CauchySeq u := Metric.cauchySeq_iff.2 fun ε hε ↦ by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hellTendsto.cauchySeq (C * ε) (mul_pos hC hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [dist_eq_norm]
    calc ‖u m - u n‖ ≤ (1 / C) * ‖ell m - ell n‖ :=
          (hsolution m).norm_sub_le_of_coercive_L2 (fun v ↦ hBmeas.apply_continuousLinearMap v)
            MB hBbound hC hcoercive (hsolution n) hab
      _ < (1 / C) * (C * ε) := by gcongr; simpa only [dist_eq_norm] using hN m hm n hn
      _ = ε := by field_simp
  obtain ⟨uLimit, huTendsto⟩ := cauchySeq_tendsto_of_complete huCauchy
  exact ⟨uLimit, huTendsto, .tendsto_L2 (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound
    hellTendsto huTendsto hsolution⟩

omit [InnerProductSpace ℝ V] in
/-- A varying numerical bound survives strong L² convergence through an
almost-everywhere convergent subsequence. -/
private theorem ae_norm_le_of_tendsto_L2_bound
    {a b : ℝ} {u : ℕ → Lp V 2 (volume.restrict (Ioc a b))}
    {v : Lp V 2 (volume.restrict (Ioc a b))} {radius : ℕ → ℝ} {limitRadius : ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds v))
    (hradius : Filter.Tendsto radius Filter.atTop (nhds limitRadius))
    (hbound : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc a b), ‖u n t‖ ≤ radius n) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), ‖v t‖ ≤ limitRadius := by
  obtain ⟨ns, hns, hpointwise⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  filter_upwards [hpointwise, ae_all_iff.2 fun n ↦ hbound (ns n)] with t ht hboundt
  exact le_of_tendsto_of_tendsto' ((continuous_norm.tendsto _).comp ht)
    (hradius.comp hns.tendsto_atTop) hboundt

/--
Density/completion for pivot-valued forcing while retaining the improved
time derivative.

Bounded continuous `H`-valued loads are approximated strongly in `L²(H)`.
Coercive continuous dependence makes the associated states Cauchy in
`L²(V)`. A continuous quantitative estimate keeps their pivot derivatives
uniformly bounded, so `exists_pivot_derivative_of_tendsto_L2` passes an
`L²(H)` derivative to the completed solution. Uniqueness of weak time
derivatives identifies it with the canonical residual `f - B(·)u`.
-/
theorem exists_of_boundedContinuous_pivot_forcing
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hBmeas : AEStronglyMeasurable B
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H)
    (bound : Lp H 2 (volume.restrict (Set.Ioc a b)) → ℝ)
    (hboundContinuous : Continuous bound)
    (stateBound : Lp H 2 (volume.restrict (Set.Ioc a b)) → ℝ)
    (hstateBoundContinuous : Continuous stateBound)
    (hsolve : ∀ fCont : BoundedContinuousFunction ℝ H,
      ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
          (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
        IsGelfandIntegratedWeakSolution T B
            (fun t ↦ T.pivotToDual (fCont t)) u uInit ∧
        HasGelfandWeakTimeDerivativeOn T u
          (T.pivotToDual.compLpL 2
            (volume.restrict (Set.Ioc a b)) du) ∧
        ‖du‖ ^ 2 ≤
          bound (BoundedContinuousFunction.toLp 2
            (volume.restrict (Set.Ioc a b)) ℝ fCont) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
          ‖u t‖ ≤
            stateBound (BoundedContinuousFunction.toLp 2
              (volume.restrict (Set.Ioc a b)) ℝ fCont))) :
    ∃ (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (du : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T B
          (fun t ↦ T.pivotToDual (f t)) u uInit ∧
      HasGelfandWeakTimeDerivativeOn T u
        (T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) du) ∧
      T.pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc a b)) du =
        gelfandResidualLp B
          (T.pivotToDual.compLpL 2
            (volume.restrict (Set.Ioc a b)) f)
          u (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound ∧
      ‖du‖ ^ 2 ≤ bound f ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖u t‖ ≤ stateBound f) := by
  classical
  let μab := volume.restrict (Set.Ioc a b)
  obtain ⟨fLp, hfLpRange, hfTendsto⟩ := mem_closure_iff_seq_limit.mp
    (BoundedContinuousFunction.toLp_denseRange H μab ℝ (by norm_num) f)
  choose fCont hfCont using hfLpRange
  choose u du hsolution hderivative hduBound hstateBound using fun n ↦ hsolve (fCont n)
  have hforcingAE (n : ℕ) : (fun t ↦ T.pivotToDual (fCont n t)) =ᵐ[μab]
      fun t ↦ T.pivotToDual.compLpL 2 μab (fLp n) t := by
    filter_upwards [BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := μab) (𝕜 := ℝ) (fCont n),
      T.pivotToDual.coeFn_compLpL (fLp n)] with t hcont hcomp
    rw [hcomp, ← hfCont n, hcont]
  obtain ⟨uLimit, huTendsto, hsolutionLimitLp⟩ :=
    exists_state_limit_of_forcing_tendsto T B hab hC hBmeas hBbound hcoercive uInit _ _ u
      (((T.pivotToDual.compLpL 2 μab).continuous.tendsto f).comp hfTendsto)
      fun n ↦ (hsolution n).congr_forcing_ae (hforcingAE n)
  obtain ⟨duLimit, hduLimit, hduLimitBound⟩ :=
    exists_pivot_derivative_of_tendsto_L2 T u uLimit du (fun n ↦ bound (fLp n)) (bound f)
      huTendsto (fun n ↦ hfCont n ▸ hduBound n)
      ((hboundContinuous.tendsto f).comp hfTendsto) hderivative
  exact ⟨uLimit, duLimit, hsolutionLimitLp.congr_forcing_ae (T.pivotToDual.coeFn_compLpL f),
    hduLimit, pivot_derivative_eq_residual T B _ uLimit duLimit
      (fun v ↦ hBmeas.apply_continuousLinearMap v) hBbound hsolutionLimitLp hduLimit,
    hduLimitBound, ae_norm_le_of_tendsto_L2_bound huTendsto
      ((hstateBoundContinuous.tendsto f).comp hfTendsto)
      fun n ↦ by rw [Function.comp_apply, ← hfCont n]; exact hstateBound n⟩

/--
Passage to the measurable Galerkin limit with the improved pivot
derivative retained in the limit.

This strengthens `IsGelfandIntegratedWeakSolution.exists_of_ae_approximations`.
Besides the usual energy bound for the states, it assumes the
dimension-independent `L²(H)` bound obtained by testing with `uₘ'`. A single
ultrafilter is used for both weak limits, so the returned weak solution and
the returned pivot derivative belong to the same limiting trajectory.  The
limit of the Galerkin equations also identifies that pivot derivative with
the canonical residual `ell - B(·)u` in `L²(a,b;V*)`.
-/
theorem exists_of_ae_approximations_with_pivot_derivative_eq_residual
    [CompleteSpace V] [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b C M MB : ℝ} (hab : a < b) (hC : 0 < C)
    (hMB : 0 ≤ MB)
    (hBmeas : AEStronglyMeasurable B
      (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : MemLp ell 2 (volume.restrict (Set.Ioc a b)))
    (u₀ : ∀ n, S n)
    (uInit : H)
    (hu₀ : Filter.Tendsto (fun n ↦ T.inclusion (u₀ n : V))
      Filter.atTop (nhds uInit))
    (initialPivotBoundSq : ℝ)
    (hInitialPivotBoundSq : 0 ≤ initialPivotBoundSq)
    (hu₀Bound : ∀ n,
      ‖T.inclusion (u₀ n : V)‖ ^ 2 ≤ initialPivotBoundSq)
    (G : ∀ n, AEGelfandGalerkinApproximation T (S n) B ell a b C M
      (u₀ n))
    (velocityBoundSq : ℝ)
    (hVelocityBoundSq : 0 ≤ velocityBoundSq)
    (hvelocity : ∀ n,
      ‖(G n).pivotDerivativeLp T (S n)‖ ^ 2 ≤ velocityBoundSq) :
    ∃ (uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)))
        (duHLimit : Lp H 2 (volume.restrict (Set.Ioc a b))),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit ∧
      HasGelfandWeakTimeDerivativeOn T uLimit
        (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
          duHLimit) ∧
      T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) duHLimit =
        gelfandResidualLp B (hell.toLp ell) uLimit
          (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound ∧
      ‖duHLimit‖ ^ 2 ≤ velocityBoundSq ∧
      (∀ stateBound : ℝ,
        (∀ n, ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
          ‖(G n).ambientTrajectoryLp hab.le t‖ ≤ stateBound) →
        ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
          ‖uLimit t‖ ≤ stateBound) := by
  classical
  let state : ℕ → Lp V 2 (volume.restrict (Set.Ioc a b)) :=
    fun n ↦ (G n).ambientTrajectoryLp hab.le
  let D : ℝ := (2 / C) * ((1 / 2 : ℝ) * initialPivotBoundSq + (M ^ 2 / (2 * C)) * (b - a))
  have hstateSq (n : ℕ) : ‖state n‖ ^ 2 ≤ D :=
    ((G n).norm_ambientTrajectoryLp_sq_le hab.le hC).trans
      (by dsimp only [D]; gcongr; exact hu₀Bound n)
  obtain ⟨uLimit, duHLimit, U, hU, huweak, hduHweak, hweakDerivative⟩ :=
    exists_hasGelfandWeakTimeDerivativeOn_of_bounded_pivot_derivatives T state
      (fun n ↦ (G n).pivotDerivativeLp T (S n))
      (isBounded_range_of_norm_sq_le state (by dsimp only [D]; positivity) hstateSq)
      (isBounded_range_of_norm_sq_le _ hVelocityBoundSq hvelocity)
      (fun n ↦ (G n).hasGelfandWeakTimeDerivativeOn_pivotDerivativeLp T (S n) hab.le)
  have hsolutionLp := of_galerkin_weak_limit T S P hdenseEnergy B ell hab hMB
    hBmeas hBbound hell u₀ uInit hu₀ G uLimit huweak hU hstateSq
  refine ⟨uLimit, duHLimit, hsolutionLp.congr_forcing_ae hell.coeFn_toLp, hweakDerivative,
    pivot_derivative_eq_residual T B _ uLimit duHLimit (fun v ↦ hBmeas.apply_continuousLinearMap v)
      hBbound hsolutionLp hweakDerivative, ?_, fun stateBound hstateBound ↦
      ae_norm_le_of_tendsto_weak_Lp (fun _ ↦ stateBound) huweak (.of_forall hstateBound)⟩
  exact (Real.le_sqrt (norm_nonneg _) hVelocityBoundSq).mp
    (WeakCompactness.norm_le_of_tendsto_of_norm_le hduHweak
      (.of_forall fun n ↦ Real.le_sqrt_of_sq_le (hvelocity n)))

end IsGelfandIntegratedWeakSolution

end PivotForcingCompletion

end PDE.Analysis.Evolution

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.ThreeTermEstimate
public import PDE.Analysis.Evolution.Galerkin.Measurable.L2Caratheodory
public import PDE.Analysis.Evolution.Galerkin.Measurable.L2Energy
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.AbsolutelyContinuous
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Bochner classes and uniform estimates of Carathéodory solutions

Let `u` be a Carathéodory solution of the Galerkin system on `S` with a load
`ℓ ∈ L²(a, b; V*)` and a measurable form with `‖B(t)‖ ≤ MB`. The state and the dual derivative
`energyToDual ∘ u'` define classes in `L²(a, b; V)` and `L²(a, b; V*)`, and integration by
parts shows that the second is the Gelfand weak time derivative of the first. Under a Gårding
inequality and a stable trial projection with energy bound `K`,
`‖ι u(t)‖_H + ‖u‖_{L²(V)} + ‖u'‖_{L²(V*)}` is at most a constant depending on `θ`, `γ`,
`b - a`, `MB` and `K` times `‖ι u(a)‖_H + ‖ℓ‖_{L²(V*)}`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution.AffineCaratheodorySolutionOn

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
  [FiniteDimensional ℝ S] [CompleteSpace S]
  {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
  {a b : ℝ} {u₀ : S}

variable (U : AffineCaratheodorySolutionOn
  (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
  (gelfandGalerkinForcing T S ell) a b u₀)

/-- The ambient energy trajectory is square-integrable by absolute continuity
on the compact time interval. -/
theorem gelfandGalerkin_state_memLp (hab : a ≤ b) :
    MemLp (fun t ↦ (U.trajectory t : V)) 2 (volume.restrict (Ioc a b)) := by
  have hu : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  exact (S.subtypeL.continuous.comp_continuousOn hu).memLp_of_subset_isCompact
    isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self

/-- The Galerkin state as an energy-space Bochner class. -/
def gelfandGalerkinStateLp (hab : a ≤ b) : Lp V 2 (volume.restrict (Ioc a b)) :=
  (U.gelfandGalerkin_state_memLp hab).toLp (fun t ↦ (U.trajectory t : V))

/-- The ambient dual derivative is square-integrable. -/
theorem gelfandGalerkin_dual_memLp (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB) :
    MemLp (fun t ↦ T.energyToDual
      (gelfandGalerkinVectorField T S B ell t (U.trajectory t) : V))
      2 (volume.restrict (Ioc a b)) :=
  (T.energyToDual.comp S.subtypeL).comp_memLp'
    (U.gelfandGalerkin_derivative_memLp hab hB hell MB hbound)

/-- The Bochner class of the dual derivative. -/
def gelfandGalerkinDualLp (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB) :
    Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)) :=
  (U.gelfandGalerkin_dual_memLp hab hB hell MB hbound).toLp _

/-- The derivative class is the weak time derivative of the state class. -/
theorem gelfandGalerkin_weakDerivative (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB) :
    HasGelfandWeakTimeDerivativeOn T (U.gelfandGalerkinStateLp hab)
      (U.gelfandGalerkinDualLp hab hB hell MB hbound) := by
  apply HasGelfandWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval T hab
    (S.subtypeL.lipschitzWith.comp_absolutelyContinuousOnInterval U.absolutely_continuous)
    (hU := (U.gelfandGalerkin_state_memLp hab).coeFn_toLp)
    (hG := (U.gelfandGalerkin_dual_memLp hab hB hell MB hbound).coeFn_toLp)
  filter_upwards [U.gelfandGalerkin_derivative_ae] with t ht
  exact S.subtypeL.hasFDerivAt.comp_hasDerivAt t ht

/-- The full three-term estimate, with no dependence on the trial dimension or
mass-inverse norm. The forcing and initial data enter only through their norms. -/
theorem gelfandGalerkin_three_term_bound {K : NNReal} (P : StableTrialProjection T S K)
    (hab : a ≤ b) {theta gamma : ℝ} (htheta : 0 < theta) (hgamma : 0 ≤ gamma)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB)
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      theta * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖T.inclusion (U.trajectory t : V)‖ + ‖U.gelfandGalerkinStateLp hab‖ +
        ‖U.gelfandGalerkinDualLp hab hB hell MB hbound‖ ≤
      gardingThreeTermConstant theta gamma (b - a) MB K *
        (‖T.inclusion (u₀ : V)‖ + ‖hell.toLp ell‖) := by
  have hBae : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound t ⟨ht.1.le, ht.2⟩
  have heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      inner ℝ (T.inclusion
        (gelfandGalerkinVectorField T S B ell t (U.trajectory t) : V)) (T.inclusion v) +
        B t (U.trajectory t : V) v = ell t v :=
    Eventually.of_forall fun t ↦ gelfandGalerkinVectorField_equation T S B ell t (U.trajectory t)
  obtain ⟨hpivot, henergy, hdual⟩ := gelfandGalerkin_garding_three_squared_bounds P hab htheta
    hgamma U.absolutely_continuous U.gelfandGalerkin_derivative_ae
    (U.gelfandGalerkin_derivative_memLp hab hB hell MB hbound) hGarding hell MB hBae heq
  have huNorm : ‖U.gelfandGalerkinStateLp hab‖ ^ 2 =
      ∫ t in a..b, ‖(U.trajectory t : V)‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le hab]
    exact integral_congr_ae ((U.gelfandGalerkin_state_memLp hab).coeFn_toLp.fun_comp
      (fun v ↦ ‖v‖ ^ 2))
  have hgNorm : ‖U.gelfandGalerkinDualLp hab hB hell MB hbound‖ ^ 2 =
      ∫ t in a..b, ‖T.energyToDual
        (gelfandGalerkinVectorField T S B ell t (U.trajectory t) : V)‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le hab]
    exact integral_congr_ae
      ((U.gelfandGalerkin_dual_memLp hab hB hell MB hbound).coeFn_toLp.fun_comp
        (fun v ↦ ‖v‖ ^ 2))
  have hfNorm : ‖hell.toLp ell‖ ^ 2 = ∫ t in a..b, ‖ell t‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (hell.coeFn_toLp.fun_comp (fun v ↦ ‖v‖ ^ 2))
  rw [U.initial_value, ← hfNorm] at hpivot henergy hdual
  rw [← huNorm] at henergy
  rw [← hgNorm] at hdual
  intro t ht
  apply three_term_le_of_garding_squared_bounds htheta hgamma (sub_nonneg.mpr hab)
    (norm_nonneg _) (norm_nonneg _) ?_ henergy hdual
  exact (hpivot t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
      (by positivity))) (by positivity))

end PDE.Analysis.Evolution.AffineCaratheodorySolutionOn

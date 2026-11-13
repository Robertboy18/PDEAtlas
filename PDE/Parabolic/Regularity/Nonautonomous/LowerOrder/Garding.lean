/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.PivotPerturbation
public import PDE.Parabolic.Heat.Variational.MeasurableBounds

/-!
# Gårding existence for time-dependent lower-order perturbations

A uniformly coercive principal form and a bounded energy-to-pivot perturbation
give a Gårding inequality with a shift determined by their bounds. The measurable
Galerkin construction then supplies the full weak solution and a data-independent
energy estimate. The full form need not be symmetric, positive, or coercive.
-/

@[expose] public noncomputable section

open scoped Sobolev
open Filter MeasureTheory Set
open scoped NNReal

namespace PDE.Parabolic.DivergenceFormHeat.LowerOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

/-- Measurable bounded lower-order perturbations of a coercive principal form admit
a unique weak solution. Its `L² H¹₀` bound is fixed before the forcing and initial data.
Coercivity is required only of the principal part; the full Gårding bound is derived. -/
theorem exists_solution_with_state_bound
    {n : ℕ} {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (A : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : ℝ → H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hcoercive : ∀ t ∈ Icc a b, ∀ v, C * ‖v‖ ^ 2 ≤ A t v v)
    (hA : ∀ v, AEStronglyMeasurable (fun t ↦ A t v) (volume.restrict (Ioc a b)))
    (MA : ℝ≥0) (hAbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖A t‖ ≤ MA)
    (hR : ∀ v, AEStronglyMeasurable (fun t ↦ R t v) (volume.restrict (Ioc a b)))
    (MR : ℝ≥0) (hRbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖R t‖ ≤ MR) :
    let T := h10L2GelfandTriple hopen
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (g : H¹₀(Ω)),
      ∃ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
        IsGelfandIntegratedWeakSolution T
          (fun t ↦ A t + T.pivotToDual.comp (R t))
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u (T.inclusion g) ∧
        (∀ v, IsGelfandIntegratedWeakSolution T
          (fun t ↦ A t + T.pivotToDual.comp (R t))
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) v (T.inclusion g) →
            v = u) ∧
        ‖u‖ ≤ K * (‖f‖ + ‖g‖) := by
  let T := h10L2GelfandTriple hopen
  let B := fun t ↦ A t + T.pivotToDual.comp (R t)
  let MB : ℝ≥0 := MA + ‖T.pivotToDual‖₊ * MR
  let gamma := (MR : ℝ) ^ 2 / (2 * C)
  have hgamma : 0 ≤ gamma := by positivity
  have hB (v : H¹₀(Ω)) : AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)) :=
    (hA v).add (T.pivotToDual.continuous.comp_aestronglyMeasurable (hR v))
  have hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB := by
    filter_upwards [hAbound, hRbound] with t hAt hRt
    change ‖A t + T.pivotToDual.comp (R t)‖ ≤ (MA : ℝ) + ‖T.pivotToDual‖ * MR
    exact (norm_add_le (A t) (T.pivotToDual.comp (R t))).trans (add_le_add hAt
      ((ContinuousLinearMap.opNorm_comp_le T.pivotToDual (R t)).trans
        (mul_le_mul_of_nonneg_left hRt (norm_nonneg _))))
  have hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v,
      C / 2 * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hRbound] with t ht hRt
    intro v
    refine (garding_bound_of_coercive_principal T (A t) (R t) hC
      (hcoercive t (Ioc_subset_Icc_self ht)) v).trans ?_
    gcongr
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hRt 2) (by positivity)
  let K := gardingThreeTermConstant (C / 2) gamma (b - a) MB 1
  have hK : 0 ≤ K := by
    dsimp only [K, gardingThreeTermConstant]
    positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro f g
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
  let S := h10L2SpectralTrialSystem hopen hbounded
  have hexists : Nonempty (GardingWeakSolutionOn T B ell (T.inclusion g)
      a b (C / 2) gamma) :=
    @GardingWeakSolutionOn.nonempty_of_ae_garding
      (H¹₀(Ω)) (DerivLp n 2 Ω)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      T S.space S.finiteDimensional S.stabilityConstant
      S.projection S.denseEnergy B a b (C / 2) gamma ell
      hab (half_pos hC) hgamma hB MB hBbound hGarding (T.inclusion g)
  obtain ⟨U⟩ := hexists
  refine ⟨U.state, U.properties.solution, U.properties.unique, ?_⟩
  have h := U.three_term_bound hab.le (half_pos hC) hgamma hB MB hBbound
    a ⟨le_rfl, hab.le⟩
  have hell : ‖ell‖ ≤ ‖f‖ :=
    HeatEquation.Variational.BoundedMeasurableCoefficients.norm_pivotLoadLp_le hopen f
  have hg : ‖T.inclusion g‖ ≤ ‖g‖ := baseCoordCLM_norm_le g
  have hstate : ‖U.state‖ ≤ K * (‖T.inclusion g‖ + ‖ell‖) := by
    change _ ≤ K * (‖T.inclusion g‖ + ‖ell‖) at h
    linarith [norm_nonneg (U.evolution.representative a), norm_nonneg U.derivative]
  have := mul_nonneg hK (by linarith : (0 : ℝ) ≤ ‖f‖ + ‖g‖ - ‖T.inclusion g‖ - ‖ell‖)
  linarith [norm_nonneg f, norm_nonneg g]

end PDE.Parabolic.DivergenceFormHeat.LowerOrder

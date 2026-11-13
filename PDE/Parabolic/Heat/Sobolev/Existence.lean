/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Construction.WeakLimit
public import PDE.Spaces.Sobolev.Evolution.HigherOrder.WholeSpaceContinuity
import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional

/-!
# Whole-space heat evolution with its initial trace

The joint weak limit solves the heat equation with an L² time
derivative. The H²–H¹ factorization supplies a continuous H¹ representative.
Its initial value is identified through the integrated initial identity;
the energy bound holds on the entire closed interval.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- Whole-space heat evolution from arbitrary H¹ data and L²(L²)
forcing, with its weak time derivative and continuous closed-interval H¹ trace. -/
theorem exists_heat_solution
    (hε : 0 < ε) (hab : a < b)
    (F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b))) (q : W^{1,2}(ℝ^n)) :
    ∃ (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
      (v : ℝ → W^{1,2}(ℝ^n)),
      g = (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F ∧
      ε * ‖u‖ ^ 2 ≤ (1 + (1 + ε) * (b - a) * Real.exp (b - a)) *
        (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) ∧
      HasWeakTimeDerivativeOn (Ioo a b)
        (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t) ∧
      ContinuousOn v (Icc a b) ∧
      v =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ lowerOrderCLM (by omega : 1 ≤ 2) (u t)) ∧
      v a = q ∧
      ∀ t ∈ Icc a b, ‖v t‖ ^ 2 ≤
        (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) *
          Real.exp (t - a) := by
  let μ := volume.restrict (Ioc a b)
  let : MeasurableSpace (DerivLp n 2 univ) := borel _
  let : BorelSpace (DerivLp n 2 univ) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (DerivLp n 2 univ)) := borel _
  let : BorelSpace (StrongDual ℝ (DerivLp n 2 univ)) := ⟨rfl⟩
  obtain ⟨u, g, heq, hH2, henergy, hid⟩ := exists_heat_integrated_solution hε hab.le F q
  let P : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  have hPu := P.coeFn_compLpL u
  have hid' (w : DerivLp n 2 univ) (τ : TimeTest a b) :
      -(∫ t, ⟪P.compLpL 2 μ u t, w⟫_ℝ * τ.derivToLp t ∂μ) =
      (∫ t, ⟪g t, w⟫_ℝ * τ.toLp t ∂μ) +
        ⟪wkpBaseCoordinateCLM q, w⟫_ℝ * τ.toFun a := by
    have htime : (∫ t, ⟪P.compLpL 2 μ u t, w⟫_ℝ * τ.derivToLp t ∂μ) =
        ∫ t, ⟪P (u t), w⟫_ℝ * τ.derivToLp t ∂μ := by
      apply integral_congr_ae
      filter_upwards [hPu] with t ht
      rw [ht]
    rw [htime]
    exact hid w τ
  obtain ⟨E, hw, hinit⟩ :=
    exists_continuousPivotEvolutionOn_of_integrated_initial_identity hab
      (P.compLpL 2 μ u) g (wkpBaseCoordinateCLM q) hid'
  have hweak : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ P (u t)) (fun t ↦ g t) := by
    apply hw.pivot_hasWeakTimeDerivativeOn.congr_ae_restrict measurableSet_Ioo
      _ Filter.EventuallyEq.rfl
    exact hPu.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  have hEc : ContinuousOn E.representative (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using E.continuousOn
  have hEu : E.representative =ᵐ[μ] fun t ↦ P (u t) := by
    have h := E.ae_eq_inclusion
    rw [uIcc_of_le hab.le] at h
    exact (h.filter_mono (ae_mono (volume.restrict_mono_set Ioc_subset_Icc_self))).trans hPu
  obtain ⟨v, hv, hvu, hvE⟩ :=
    exists_continuous_hOne_representative_eq_base hab u g hweak E.representative hEc hEu
  refine ⟨u, g, v, heq, hH2, hweak, hv, hvu, ?_, ?_⟩
  · apply wkpBaseCoordinateCLM_injective isOpen_univ
    exact (hvE ⟨le_rfl, hab.le⟩).trans hinit
  · let K := ‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2
    let e (t : ℝ) := K * Real.exp (t - a)
    have he : Continuous e :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_id.sub continuous_const))
    have hae : (fun t ↦ max (‖v t‖ ^ 2) (e t)) =ᵐ[volume.restrict (Icc a b)] e := by
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      filter_upwards [henergy, hvu] with t ht hvt
      apply max_eq_right
      simpa only [hvt] using ht
    have hpoint := Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
      ((hv.norm.pow 2).sup he.continuousOn) he.continuousOn
    intro t ht
    exact max_eq_right_iff.mp (hpoint ht)

end PDE.Parabolic.Heat

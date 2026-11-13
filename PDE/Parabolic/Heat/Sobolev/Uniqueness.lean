/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.WholeSpace
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Core.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Uniqueness for whole-space heat trajectories

An arbitrary H² Bochner state with its L² weak time derivative is
determined by the heat equation and its continuous L² initial trace.
The proof derives absolute continuity and uses the native weak Laplacian
integration-by-parts identity. No energy estimate is a hypothesis.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Laplacian Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- A homogeneous heat trajectory with zero initial datum vanishes, for
every nonnegative diffusivity and every finite interval. For `b ≤ a` the measure on `Ioc a b`
is zero and the trace lives on at most the point `a`. -/
theorem heat_solution_eq_zero
    (hε : 0 ≤ ε)
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u)
    (z : ℝ → DerivLp n 2 univ) (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] fun t ↦ wkpBaseCoordinateCLM (u t))
    (hz0 : z a = 0) :
    u = 0 ∧ g = 0 ∧ EqOn z 0 (Icc a b) := by
  rcases le_or_gt b a with hba | hab
  · have hnull {P : ℝ → Prop} : ∀ᵐ t ∂(volume.restrict (Ioc a b)), P t :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦
        absurd (ht.1.trans_le ht.2) (not_lt.mpr hba)
    refine ⟨Lp.ext hnull, Lp.ext hnull, fun t ht ↦ ?_⟩
    obtain rfl : t = a := le_antisymm (ht.2.trans hba) ht.1
    simpa using hz0
  let μ := volume.restrict (Ioc a b)
  let P : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  have hPu := P.coeFn_compLpL u
  have hwP : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ P.compLpL 2 μ u t) (fun t ↦ g t) :=
    hweak.congr_ae_restrict measurableSet_Ioo
      (hPu.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      Filter.EventuallyEq.rfl
  obtain ⟨w, hwAC, huw, hwd, hw0⟩ :=
    hwP.exists_absolutelyContinuousRepresentative_eq_initial hab z hz
      (hzu.trans hPu.symm)
  have hwu : w =ᵐ[μ] fun t ↦ P (u t) := huw.symm.trans hPu
  have hgA : (g : ℝ → DerivLp n 2 univ) =ᵐ[μ] fun t ↦ A (u t) := by
    rw [heq]
    exact A.coeFn_compLpL u
  have hdiff : ∀ᵐ t ∂μ, deriv (fun s ↦ ‖w s‖ ^ 2) t ≤
      0 * ‖w t‖ ^ 2 + (0 : ℝ) := by
    filter_upwards [hwd, hwu, hgA] with t hdt hwt hgt
    rw [hdt.norm_sq.deriv, hwt, hgt]
    change 2 * ⟪wkpBaseCoordinateCLM (u t), ε • Δ (u t)⟫_ℝ ≤ _
    rw [real_inner_smul_right, inner_base_laplacian_eq_neg_gradient (u t), zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos hε
        (neg_nonpos.mpr (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)))
  have hbound := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le hab.le
    (absolutelyContinuousOnInterval_norm_sq hwAC)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume a b)
    (Filter.Eventually.of_forall fun _ ↦ le_rfl) (le_refl (0 : ℝ)) hdiff
  have hwzero (t : ℝ) (ht : t ∈ Icc a b) : w t = 0 :=
    norm_eq_zero.mp <| sq_eq_zero_iff.mp <| le_antisymm (by
      simpa only [hw0, hz0, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        intervalIntegral.integral_zero, add_zero, zero_mul] using hbound t ht) (sq_nonneg _)
  have hu0 : u = 0 := by
    apply Lp.ext
    filter_upwards [hwu, ae_restrict_mem measurableSet_Ioc,
      Lp.coeFn_zero (W^{2,2}(ℝ^n)) 2 μ] with t ht hti hzero
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    simpa only [hzero, Pi.zero_apply, map_zero, P] using ht.symm.trans
      (hwzero t (Ioc_subset_Icc_self hti))
  refine ⟨hu0, ?_, ?_⟩
  · rw [heq, hu0]
    exact (A.compLpL 2 μ).toLinearMap.map_zero
  · have hzw : z =ᵐ[volume.restrict (Icc a b)] w := by
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact hzu.trans hwu.symm
    exact fun t ht ↦ (Measure.eqOn_Icc_of_ae_eq volume hab.ne hzw hz
      (by simpa only [uIcc_of_le hab.le] using hwAC.continuousOn) ht).trans (hwzero t ht)

/-- Subtraction preserves the heat equation and its weak time
derivative, with the difference of the two forcing terms. -/
theorem heat_solution_sub
    (u v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g h F H : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hwu : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (hwv : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (v t)) (fun t ↦ h t))
    (hequ : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (heqv : h =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) v + H) :
    g - h =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) (u - v) + (F - H) ∧
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM ((u - v) t)) (fun t ↦ (g - h) t) := by
  let μ := volume.restrict (Ioc a b)
  let P : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  have hstate : (fun t ↦ P (u t) - P (v t)) =ᵐ[μ] fun t ↦ P ((u - v) t) := by
    filter_upwards [Lp.coeFn_sub u v] with t ht
    simp only [ht, Pi.sub_apply, map_sub]
  have hvelocity : (fun t ↦ g t - h t) =ᵐ[μ] (fun t ↦ (g - h) t) :=
    (Lp.coeFn_sub g h).symm
  constructor
  · let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
    have hsub : A.compLpL 2 μ (u - v) = A.compLpL 2 μ u - A.compLpL 2 μ v :=
      (A.compLpL 2 μ).toLinearMap.map_sub u v
    rw [hequ, heqv, hsub]
    abel
  · exact (hwu.sub hwv).congr_ae_restrict measurableSet_Ioo
      (hstate.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      (hvelocity.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))

/-- Two arbitrary heat trajectories with the same forcing and initial trace
have equal Bochner states, equal velocities, and equal continuous traces. -/
theorem heat_solution_unique
    (hε : 0 ≤ ε)
    (u v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g h F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hwu : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (hwv : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (v t)) (fun t ↦ h t))
    (hequ : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (heqv : h =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) v + F)
    (z w : ℝ → DerivLp n 2 univ)
    (hz : ContinuousOn z (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] fun t ↦ wkpBaseCoordinateCLM (u t))
    (hwv' : w =ᵐ[volume.restrict (Ioc a b)] fun t ↦ wkpBaseCoordinateCLM (v t))
    (hinit : z a = w a) :
    u = v ∧ g = h ∧ EqOn z w (Icc a b) := by
  let μ := volume.restrict (Ioc a b)
  let P : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  obtain ⟨heq', hweak⟩ := heat_solution_sub u v g h F F hwu hwv hequ heqv
  have heq : g - h = A.compLpL 2 μ (u - v) := by
    simpa only [sub_self, add_zero] using heq'
  have hrep : (fun t ↦ z t - w t) =ᵐ[μ] fun t ↦ P ((u - v) t) := by
    filter_upwards [hzu, hwv', Lp.coeFn_sub u v] with t hzt hwt huv
    simp only [hzt, hwt, huv, Pi.sub_apply, map_sub, P]
  obtain ⟨huv, hgh, hzw⟩ := heat_solution_eq_zero hε (u - v) (g - h)
    hweak heq (fun t ↦ z t - w t) (hz.sub hw) hrep (sub_eq_zero.mpr hinit)
  refine ⟨sub_eq_zero.mp huv, sub_eq_zero.mp hgh, ?_⟩
  intro t ht
  exact sub_eq_zero.mp (hzw ht)

end PDE.Parabolic.Heat

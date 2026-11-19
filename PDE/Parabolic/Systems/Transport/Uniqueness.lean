/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Energy.Integrated
import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# Uniqueness for matrix diffusion trajectories

Subtracting two trajectories gives the same symmetric matrix transport
equation with zero forcing. Its H¹ energy bound forces equality of the
continuous traces. The Sobolev graph inclusions then identify the H³
states, and the equation identifies the H¹ velocities.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ} {ε a b K : ℝ}

/-- Any two trajectories with the same forcing and initial trace
coincide. No estimate for either competitor is a hypothesis. -/
theorem transport_diffusion_unique
    (hε : 0 ≤ ε) (hab : a < b) (hK0 : 0 ≤ K)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (hK : ∀ t ∈ Icc a b, transportDerivativeSum (A t) ≤ K)
    (U V : Fin m → Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (G H F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (heqU : ∀ i, (fun t ↦ G i t) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i t) + F i t +
        vectorTransportH1CLM isOpen_univ (A t)
          (fun j ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U j t)) i)
    (heqV : ∀ i, (fun t ↦ H i t) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (V i t) + F i t +
        vectorTransportH1CLM isOpen_univ (A t)
          (fun j ↦ lowerOrderCLM (by decide : 2 ≤ 3) (V j t)) i)
    (hweakU : ∀ i, HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U i t)) (fun t ↦ G i t))
    (hweakV : ∀ i, HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (V i t)) (fun t ↦ H i t))
    (z w : ℝ → Fin m → W^{1,2}(ℝ^n))
    (hz : ContinuousOn z (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hzu : ∀ i, (fun t ↦ z t i) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U i t))
    (hwv : ∀ i, (fun t ↦ w t i) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (V i t))
    (hinit : z a = w a) :
    U = V ∧ G = H ∧ EqOn z w (Icc a b) := by
  classical
  let μ := volume.restrict (Ioc a b)
  let P : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let Q : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) := lowerOrderCLM (by decide)
  let L : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := higherOrderLaplacianCLM (by decide)
  let dU (i : Fin m) := U i - V i
  let dG (i : Fin m) := G i - H i
  have hstate (i : Fin m) : (fun t ↦ P (U i t) - P (V i t)) =ᵐ[μ]
      fun t ↦ P (dU i t) := by
    filter_upwards [Lp.coeFn_sub (U i) (V i)] with t ht
    simp only [dU, ht, Pi.sub_apply, map_sub]
  have hdweak (i : Fin m) : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ P (dU i t)) (fun t ↦ dG i t) :=
    ((hweakU i).sub (hweakV i)).congr_ae_restrict measurableSet_Ioo
      ((hstate i).filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      ((Lp.coeFn_sub (G i) (H i)).symm.filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
  have hdeq (i : Fin m) : (fun t ↦ dG i t) =ᵐ[μ] fun t ↦
      ε • L (dU i t) + (0 : Lp (W^{1,2}(ℝ^n)) 2 μ) t +
        vectorTransportH1CLM isOpen_univ (A t) (fun j ↦ Q (dU j t)) i := by
    filter_upwards [heqU i, heqV i, Lp.coeFn_sub (G i) (H i),
      ae_all_iff.mpr (fun j ↦ Lp.coeFn_sub (U j) (V j)),
      Lp.coeFn_zero (W^{1,2}(ℝ^n)) 2 μ] with t hUt hVt hGt hdUt hzero
    simp only [dG, dU, hGt, hdUt, Pi.sub_apply, hUt, hVt, hzero, Pi.zero_apply,
      add_zero, map_sub, smul_sub]
    have hpi : (fun j ↦ Q (U j t) - Q (V j t)) =
        (fun j ↦ Q (U j t)) - (fun j ↦ Q (V j t)) := rfl
    rw [hpi, map_sub, Pi.sub_apply]
    change ε • L (U i t) + F i t +
        vectorTransportH1CLM isOpen_univ (A t) (fun j ↦ Q (U j t)) i -
      (ε • L (V i t) + F i t +
        vectorTransportH1CLM isOpen_univ (A t) (fun j ↦ Q (V j t)) i) = _
    abel
  have hdrep (i : Fin m) : (fun t ↦ (z t - w t) i) =ᵐ[μ] fun t ↦ P (dU i t) := by
    filter_upwards [hzu i, hwv i, hstate i] with t hzt hwt ht
    exact (congrArg₂ (· - ·) hzt hwt).trans ht
  obtain ⟨hbound, _⟩ := transport_diffusion_energy_estimates hε hab hK0 A hA hK
    dU dG (fun _ ↦ 0) hdeq hdweak (fun t ↦ z t - w t) (hz.sub hw) hdrep
  have hforcing : (∫ s in a..b, ∑ i : Fin m,
      ‖(0 : Lp (W^{1,2}(ℝ^n)) 2 μ) s‖ ^ 2) = 0 := by
    rw [intervalIntegral.integral_of_le hab.le]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero (W^{1,2}(ℝ^n)) 2 μ] with t ht
    simp only [ht, Pi.zero_apply, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero]
  have hzw : EqOn z w (Icc a b) := by
    intro t ht
    funext i
    have hsum : (∑ j, ‖z t j - w t j‖ ^ 2) ≤ 0 := by
      simpa only [Pi.sub_apply, hinit, sub_self, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, hforcing,
        add_zero, zero_mul] using hbound t ht
    have hi : ‖z t i - w t i‖ ^ 2 ≤ 0 :=
      (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖z t j - w t j‖)
        (Finset.mem_univ i)).trans hsum
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))))
  have hUV : U = V := by
    funext i
    apply Lp.ext
    filter_upwards [hzu i, hwv i, ae_restrict_mem measurableSet_Ioc] with t hut hvt ht
    apply lowerOrderCLM_injective (by decide : 1 ≤ 3) isOpen_univ
    exact hut.symm.trans ((congrFun (hzw (Ioc_subset_Icc_self ht)) i).trans hvt)
  refine ⟨hUV, ?_, hzw⟩
  funext i
  apply Lp.ext
  filter_upwards [heqU i, heqV i] with t hgt hht
  rw [hUV] at hgt
  exact hgt.trans hht.symm

end PDE.Parabolic.Systems

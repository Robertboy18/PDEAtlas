/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Energy.Spatial
public import PDE.Analysis.Evolution.Core.FiniteEnergy

/-!
# Integrated energy of matrix diffusion trajectories

The H¹-valued weak time derivative and the symmetric spatial transport identity
give a closed-time H¹ bound and a diffusion dissipation bound. Their constants
depend on the coefficient derivatives and interval length, not on the positive
diffusivity. The estimate applies to every trajectory satisfying the equation.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

variable {n m : ℕ} {ε a b K : ℝ}

/-- The H¹ energy and integrated ordered-Hessian dissipation of every
solution have a bound uniform in diffusivity. -/
theorem transport_diffusion_energy_estimates
    (hε : 0 ≤ ε) (hab : a < b) (hK0 : 0 ≤ K)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (hK : ∀ t ∈ Icc a b, transportDerivativeSum (A t) ≤ K)
    (U : Fin m → Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (G F : Fin m → Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (heq : ∀ i, (fun t ↦ G i t) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i t) + F i t +
        vectorTransportH1CLM isOpen_univ (A t)
          (fun j ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U j t)) i)
    (hweak : ∀ i, HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U i t)) (fun t ↦ G i t))
    (z : ℝ → Fin m → W^{1,2}(ℝ^n)) (hz : ContinuousOn z (Icc a b))
    (hzu : ∀ i, (fun t ↦ z t i) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U i t)) :
    (∀ t ∈ Icc a b,
      (∑ i, ‖z t i‖ ^ 2) ≤
        ((∑ i, ‖z a i‖ ^ 2) + ∫ s in a..b, ∑ i, ‖F i s‖ ^ 2) *
          Real.exp ((K + 1) * (t - a))) ∧
    (∫ t in a..b, -(2 * ε) *
      ∑ i, ⟪lowerOrderCLM (by decide : 1 ≤ 3) (U i t),
        higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i t)⟫_ℝ) ≤
      (1 + (K + 1) * (b - a) * Real.exp ((K + 1) * (b - a))) *
        ((∑ i, ‖z a i‖ ^ 2) + ∫ s in a..b, ∑ i, ‖F i s‖ ^ 2) := by
  classical
  let μ := volume.restrict (Ioc a b)
  let P : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let L : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := higherOrderLaplacianCLM (by decide)
  let u (i : Fin m) := P.compLpL 2 μ (U i)
  have hPu (i : Fin m) : (fun t ↦ u i t) =ᵐ[μ] fun t ↦ P (U i t) :=
    P.coeFn_compLpL (U i)
  have hw (i : Fin m) : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ u i t) (fun t ↦ G i t) :=
    (hweak i).congr_ae_restrict measurableSet_Ioo
      ((hPu i).symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      Filter.EventuallyEq.rfl
  have hdinner (i : Fin m) :
      IntervalIntegrable (fun t ↦ ⟪P (U i t), L (U i t)⟫_ℝ) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    apply (L2.integrable_inner (𝕜 := ℝ) (P.compLpL 2 μ (U i))
      (L.compLpL 2 μ (U i))).congr
    filter_upwards [P.coeFn_compLpL (U i), L.coeFn_compLpL (U i)] with t ht hLt
    rw [ht, hLt]
  have hd : IntervalIntegrable
      (fun t ↦ -(2 * ε) * ∑ i, ⟪P (U i t), L (U i t)⟫_ℝ) volume a b := by
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (fun i _ ↦ hdinner i)).const_mul (-(2 * ε))
  have hf : IntervalIntegrable (fun t ↦ ∑ i, ‖F i t‖ ^ 2) volume a b := by
    have hi (i : Fin m) : IntervalIntegrable (fun t ↦ ‖F i t‖ ^ 2) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
      exact (Lp.memLp (F i)).integrable_norm_pow (by norm_num)
    convert IntervalIntegrable.sum Finset.univ (fun i _ ↦ hi i) using 1
    ext t
    simp only [Finset.sum_apply]
  apply finite_weak_energy_estimates hab (by linarith : 0 ≤ K + 1) u G hw z hz
    (fun i ↦ (hzu i).trans (hPu i).symm) _ _ hd hf
  · exact Filter.Eventually.of_forall fun t ↦ by
      have hd0 := neg_sum_inner_hOne_laplacian_nonneg (fun i ↦ U i t)
      have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε) hd0
      simpa only [mul_neg, neg_mul, P, L] using h
  · exact Filter.Eventually.of_forall fun t ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · filter_upwards [ae_all_iff.mpr hPu, ae_all_iff.mpr heq,
      ae_restrict_mem measurableSet_Ioc] with t hpt hgt ht
    have hsp := transport_diffusion_spatial_energy_le ε (A t)
      (hA t (Ioc_subset_Icc_self ht)) K (hK t (Ioc_subset_Icc_self ht))
      (fun i ↦ U i t) (fun i ↦ F i t)
    simpa only [hpt, hgt, P, L, neg_mul, sub_eq_add_neg, mul_assoc] using hsp

end PDE.Parabolic.Systems

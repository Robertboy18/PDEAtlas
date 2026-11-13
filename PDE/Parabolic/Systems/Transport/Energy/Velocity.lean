/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Energy.Integrated
import PDE.Analysis.Normed.Operator.FiniteProduct

/-!
# Velocity bounds independent of diffusivity

The equation controls the L² velocity by the diffusion term, forcing,
and matrix transport. For `0 ≤ ε ≤ 1`, the diffusion term is controlled by the
ordered-Hessian dissipation already present in the H¹ energy estimate.
The transport term uses only the coefficient values in L∞.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

variable {n m : ℕ} {ε M : ℝ}

/-- The full diffusion-transport right-hand side has a quadratic L² bound
in terms of its H¹ dissipation, forcing, and H¹ state energy. -/
theorem transport_diffusion_velocity_spatial_le
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hM0 : 0 ≤ M)
    (hM : ‖vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))‖ ≤ M)
    (U : Fin m → W^{3,2}(ℝ^n)) (F : Fin m → W^{1,2}(ℝ^n)) :
    (∑ i, ‖wkpBaseCoordinateCLM
      (ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i) + F i +
        vectorTransportH1CLM isOpen_univ A
          (fun j ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U j)) i)‖ ^ 2) ≤
    3 * ((n : ℝ) * (-(2 * ε) *
      ∑ i, ⟪lowerOrderCLM (by decide : 1 ≤ 3) (U i),
        higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U i)⟫_ℝ) +
      (∑ i, ‖F i‖ ^ 2) +
      (m : ℝ) * M ^ 2 * ∑ i, ‖lowerOrderCLM (by decide : 1 ≤ 3) (U i)‖ ^ 2) := by
  let P : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let L : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := higherOrderLaplacianCLM (by decide)
  let B := vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))
  let v (i : Fin m) := ε • wkpBaseCoordinateCLM (L (U i))
  let f (i : Fin m) := wkpBaseCoordinateCLM (F i)
  let w := B (fun j ↦ P (U j))
  have hthree (i : Fin m) :
      ‖v i + f i + w i‖ ^ 2 ≤ 3 * (‖v i‖ ^ 2 + ‖f i‖ ^ 2 + ‖w i‖ ^ 2) := by
    nlinarith only [mul_self_le_mul_self (norm_nonneg _)
        (norm_add₃_le (a := v i) (b := f i) (c := w i)),
      sq_nonneg (‖v i‖ - ‖f i‖), sq_nonneg (‖f i‖ - ‖w i‖), sq_nonneg (‖w i‖ - ‖v i‖)]
  have hv : (∑ i, ‖v i‖ ^ 2) ≤
      (n : ℝ) * (-(2 * ε) * ∑ i, ⟪P (U i), L (U i)⟫_ℝ) := by
    simpa only [Finset.mul_sum, P, L, v] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
        norm_smul_laplacian_sq_le_hOne_dissipation hε hε1 (U i))
  have hf : (∑ i, ‖f i‖ ^ 2) ≤ ∑ i, ‖F i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ by gcongr; exact wkpBaseCoordinateCLM_norm_le (F i)
  have hw : (∑ i, ‖w i‖ ^ 2) ≤ (m : ℝ) * M ^ 2 * ∑ i, ‖P (U i)‖ ^ 2 := by
    have h := B.sum_norm_sq_apply_le (fun i ↦ P (U i))
    simp only [Fintype.card_fin] at h
    exact h.trans (by gcongr _ * ?_ * _; exact (sq_le_sq₀ (norm_nonneg B) hM0).mpr hM)
  simp only [map_add, map_smul, vectorTransportH1CLM_base, lowerOrderCLM_trans_apply]
  change (∑ i, ‖v i + f i + w i‖ ^ 2) ≤ _
  calc
    _ ≤ ∑ i, 3 * (‖v i‖ ^ 2 + ‖f i‖ ^ 2 + ‖w i‖ ^ 2) := Finset.sum_le_sum fun i _ ↦ hthree i
    _ = 3 * ((∑ i, ‖v i‖ ^ 2) + (∑ i, ‖f i‖ ^ 2) + ∑ i, ‖w i‖ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by gcongr

/-- The time derivative has an L²(L²) estimate whose displayed constant
depends on the interval and coefficient bounds, and is independent of `ε`.
The assumptions concern only the equation and its weak derivative. -/
theorem transport_diffusion_velocity_estimate
    {a b K : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hab : a < b) (hK0 : 0 ≤ K)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (hK : ∀ t ∈ Icc a b, transportDerivativeSum (A t) ≤ K)
    (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Icc a b,
      ‖vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))‖ ≤ M)
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
    (∫ t in a..b, ∑ i, ‖wkpBaseCoordinateCLM (G i t)‖ ^ 2) ≤
      3 * ((n : ℝ) * (1 + (K + 1) * (b - a) * Real.exp ((K + 1) * (b - a))) +
        1 + (m : ℝ) * M ^ 2 * (b - a) * Real.exp ((K + 1) * (b - a))) *
        ((∑ i, ‖z a i‖ ^ 2) + ∫ s in a..b, ∑ i, ‖F i s‖ ^ 2) := by
  classical
  let μ := volume.restrict (Ioc a b)
  let P : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let L : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := higherOrderLaplacianCLM (by decide)
  let e (t : ℝ) := ∑ i, ‖P (U i t)‖ ^ 2
  let d (t : ℝ) := -(2 * ε) * ∑ i, ⟪P (U i t), L (U i t)⟫_ℝ
  let f (t : ℝ) := ∑ i, ‖F i t‖ ^ 2
  let v (t : ℝ) := ∑ i, ‖wkpBaseCoordinateCLM (G i t)‖ ^ 2
  let Q := (∑ i, ‖z a i‖ ^ 2) + ∫ t in a..b, f t
  let R := Real.exp ((K + 1) * (b - a))
  have hs {X : Type} [NormedAddCommGroup X] {u : Fin m → ℝ → X}
      (hu : ∀ i, MemLp (u i) 2 μ) :
      IntervalIntegrable (fun t ↦ ∑ i, ‖u i t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact integrable_finsetSum Finset.univ
      (fun i _ ↦ (hu i).integrable_norm_pow (by norm_num))
  have he : IntervalIntegrable e volume a b :=
    hs (X := W^{1,2}(ℝ^n)) (u := fun i t ↦ P (U i t))
      (fun i ↦ P.comp_memLp (U i))
  have hf : IntervalIntegrable f volume a b :=
    hs (X := W^{1,2}(ℝ^n)) (u := fun i t ↦ F i t) (fun i ↦ Lp.memLp (F i))
  have hv : IntervalIntegrable v volume a b :=
    hs (X := DerivLp n 2 univ) (u := fun i t ↦ wkpBaseCoordinateCLM (G i t))
      (fun i ↦ (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ).comp_memLp
        (G i))
  have hd : IntervalIntegrable d volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    refine (integrable_finsetSum Finset.univ fun i _ ↦ ?_).const_mul _
    refine (L2.integrable_inner (𝕜 := ℝ) (P.compLpL 2 μ (U i)) (L.compLpL 2 μ (U i))).congr ?_
    filter_upwards [P.coeFn_compLpL (U i), L.coeFn_compLpL (U i)] with t ht hLt
    rw [ht, hLt]
  obtain ⟨henergy, hdiss⟩ :=
    transport_diffusion_energy_estimates hε hab hK0 A hA hK U G F heq hweak z hz hzu
  have hQ0 : 0 ≤ Q := add_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (intervalIntegral.integral_nonneg hab.le fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hforcing : (∫ t in a..b, f t) ≤ Q :=
    le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hepoint : ∀ᵐ t ∂μ, e t ≤ Q * R := by
    filter_upwards [ae_all_iff.mpr hzu, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have h := henergy t (Ioc_subset_Icc_self hmem)
    simp only [ht] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_right hmem.2 a) (by linarith))) hQ0)
  have heint : (∫ t in a..b, e t) ≤ (b - a) * (Q * R) := by
    simpa only [← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_const,
      smul_eq_mul] using integral_mono_ae he.1 (integrable_const (Q * R)) hepoint
  have hrhs : IntervalIntegrable
      (fun t ↦ 3 * ((n : ℝ) * d t + f t + (m : ℝ) * M ^ 2 * e t)) volume a b :=
    ((hd.const_mul n).add hf |>.add (he.const_mul ((m : ℝ) * M ^ 2))).const_mul 3
  have hpoint : ∀ᵐ t ∂μ,
      v t ≤ 3 * ((n : ℝ) * d t + f t + (m : ℝ) * M ^ 2 * e t) := by
    filter_upwards [ae_all_iff.mpr heq, ae_restrict_mem measurableSet_Ioc] with t hgt ht
    simpa only [v, hgt, d, e, P, L] using
      transport_diffusion_velocity_spatial_le hε hε1 (A t) hM0
        (hM t (Ioc_subset_Icc_self ht)) (fun i ↦ U i t) (fun i ↦ F i t)
  have hint : (∫ t in a..b, v t) ≤
      3 * ((n : ℝ) * (∫ t in a..b, d t) + (∫ t in a..b, f t) +
        (m : ℝ) * M ^ 2 * ∫ t in a..b, e t) := by
    have h : (∫ t in a..b, v t) ≤
        ∫ t in a..b, 3 * ((n : ℝ) * d t + f t + (m : ℝ) * M ^ 2 * e t) := by
      simpa only [intervalIntegral.integral_of_le hab.le] using
        integral_mono_ae hv.1 hrhs.1 hpoint
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((hd.const_mul n).add hf)
        (he.const_mul ((m : ℝ) * M ^ 2)),
      intervalIntegral.integral_add (hd.const_mul n) hf] using h
  calc
    _ ≤ 3 * ((n : ℝ) * (∫ t in a..b, d t) + (∫ t in a..b, f t) +
        (m : ℝ) * M ^ 2 * ∫ t in a..b, e t) := hint
    _ ≤ 3 * ((n : ℝ) * ((1 + (K + 1) * (b - a) * R) * Q) + Q +
        (m : ℝ) * M ^ 2 * ((b - a) * (Q * R))) := by gcongr
    _ = _ := by dsimp only [Q, R, f]; ring

end PDE.Parabolic.Systems

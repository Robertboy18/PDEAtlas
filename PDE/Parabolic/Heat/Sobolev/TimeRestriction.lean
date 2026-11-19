/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Energy.Estimates
import PDE.Analysis.MeasureTheory.Lp.Restriction.LinearMap

/-!
# Restriction and causal bounds for the heat equation

Restricting Bochner states preserves the equation and weak time
derivative. The H¹ bound at time `t` consequently depends only on forcing
between the initial time and `t`, with no inverse interval-length factor.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n : ℕ} {ε a b c : ℝ}

/-- Restricting the time interval preserves the heat equation and
its weak derivative. -/
theorem heat_solution_restrict_right (hcb : c ≤ b)
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t)) :
    let hμ := volume.restrict_mono_set (Ioc_subset_Ioc_right hcb : Ioc a c ⊆ Ioc a b)
    Lp.restrictionCLMOfLE hμ g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a c)) (Lp.restrictionCLMOfLE hμ u) +
      Lp.restrictionCLMOfLE hμ F ∧
    HasWeakTimeDerivativeOn (Ioo a c)
      (fun t ↦ wkpBaseCoordinateCLM (Lp.restrictionCLMOfLE hμ u t))
      (fun t ↦ Lp.restrictionCLMOfLE hμ g t) := by
  dsimp only
  let hμ := volume.restrict_mono_set (Ioc_subset_Ioc_right hcb : Ioc a c ⊆ Ioc a b)
  let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  constructor
  · rw [heq, map_add]
    congr 1
    exact congrArg (fun L ↦ L u) (A.compLpL_restrictionCLMOfLE hμ).symm
  · have hs : (fun t ↦ wkpBaseCoordinateCLM (u t)) =ᵐ[volume.restrict (Ioc a c)]
        fun t ↦ wkpBaseCoordinateCLM (Lp.restrictionCLMOfLE hμ u t) :=
      (Lp.restrictionCLMOfLE_apply_ae hμ u).symm.fun_comp wkpBaseCoordinateCLM
    exact (hweak.mono (Ioo_subset_Ioo_right hcb)).congr_ae_restrict measurableSet_Ioo
      (hs.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      ((Lp.restrictionCLMOfLE_apply_ae hμ g).symm.filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))

/-- The H¹ norm at a closed-interval time is controlled by past forcing
alone. This is the causal estimate needed for a Volterra fixed point. -/
theorem heat_solution_norm_sq_le_past_forcing
    (hε : 0 < ε)
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (q : W^{1,2}(ℝ^n))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (v : ℝ → W^{1,2}(ℝ^n)) (hv : ContinuousOn v (Icc a b))
    (hvu : v =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u t))
    (hinit : v a = q) :
    ∀ t ∈ Icc a b, ‖v t‖ ^ 2 ≤
      (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..t, ‖F s‖ ^ 2) * Real.exp (t - a) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · simp [hinit]
  let hμ := volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2 : Ioc a t ⊆ Ioc a b)
  let U := Lp.restrictionCLMOfLE hμ u
  let G := Lp.restrictionCLMOfLE hμ g
  let H := Lp.restrictionCLMOfLE hμ F
  obtain ⟨heq', hw'⟩ := heat_solution_restrict_right ht.2 u g F heq hweak
  have hvU : v =ᵐ[volume.restrict (Ioc a t)]
      fun s ↦ lowerOrderCLM (by decide : 1 ≤ 2) (U s) := by
    filter_upwards [hvu.filter_mono (ae_mono hμ),
      Lp.restrictionCLMOfLE_apply_ae hμ u] with s hs hUs
    rw [hs]
    change _ = lowerOrderCLM (by decide : 1 ≤ 2) (Lp.restrictionCLMOfLE hμ u s)
    rw [hUs]
  have hb := (heat_solution_estimates hε hat U G H q heq' hw' v
    (hv.mono (Icc_subset_Icc_right ht.2)) hvU hinit).2 t (right_mem_Icc.mpr hat.le)
  have hF : (∫ s in a..t, ‖H s‖ ^ 2) = ∫ s in a..t, ‖F s‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hat.le, intervalIntegral.integral_of_le hat.le]
    apply integral_congr_ae
    exact (Lp.restrictionCLMOfLE_apply_ae hμ F).fun_comp (fun v ↦ ‖v‖ ^ 2)
  simpa only [hF] using hb

/-- Two solutions with the same initial trace satisfy a causal estimate for
their difference. The right side involves only the difference of forcing. -/
theorem heat_solution_sub_norm_sq_le_past_forcing
    (hε : 0 < ε)
    (u v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g h F H : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hequ : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (heqv : h =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) v + H)
    (hwu : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (hwv : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (v t)) (fun t ↦ h t))
    (z w : ℝ → W^{1,2}(ℝ^n))
    (hz : ContinuousOn z (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u t))
    (hwv' : w =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (v t))
    (hinit : z a = w a) :
    ∀ t ∈ Icc a b, ‖z t - w t‖ ^ 2 ≤
      ((1 + (n : ℝ) / ε) * Real.exp (t - a)) * ∫ s in a..t, ‖(F - H) s‖ ^ 2 := by
  obtain ⟨heq, hweak⟩ := heat_solution_sub u v g h F H hwu hwv hequ heqv
  have hrep : (fun t ↦ z t - w t) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) ((u - v) t) := by
    filter_upwards [hzu, hwv', Lp.coeFn_sub u v] with t hzt hwt huv
    simp only [hzt, hwt, huv, Pi.sub_apply, map_sub]
  have hb := heat_solution_norm_sq_le_past_forcing hε (u - v) (g - h) (F - H) 0
    heq hweak (fun t ↦ z t - w t) (hz.sub hw) hrep (sub_eq_zero.mpr hinit)
  intro t ht
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mul_assoc,
    mul_comm, mul_left_comm] using hb t ht

end PDE.Parabolic.Heat

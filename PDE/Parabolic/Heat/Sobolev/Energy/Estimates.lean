/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Existence
public import PDE.Parabolic.Heat.Sobolev.Uniqueness

/-!
# Estimates for arbitrary heat trajectories

Uniqueness transfers the estimates of the constructed heat solution to every
trajectory in the natural weak class. In particular, the zero-initial response
constant stays bounded as the length of the time interval tends to zero.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- Every heat trajectory satisfies the H² Bochner estimate and the
closed-time H¹ bound. -/
theorem heat_solution_estimates
    (hε : 0 < ε) (hab : a < b)
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (q : W^{1,2}(ℝ^n))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (v : ℝ → W^{1,2}(ℝ^n)) (hv : ContinuousOn v (Icc a b))
    (hvu : v =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      lowerOrderCLM (by omega : 1 ≤ 2) (u t))
    (hinit : v a = q) :
    (ε * ‖u‖ ^ 2 ≤ (1 + (1 + ε) * (b - a) * Real.exp (b - a)) *
      (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2)) ∧
    ∀ t ∈ Icc a b, ‖v t‖ ^ 2 ≤
      (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) *
        Real.exp (t - a) := by
  obtain ⟨u₀, g₀, v₀, heq₀, hH2, hweak₀, hv₀, hvu₀, hinit₀, hbound₀⟩ :=
    exists_heat_solution hε hab F q
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  have hPv : (fun t ↦ P (v t)) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ wkpBaseCoordinateCLM (u t) := by
    filter_upwards [hvu] with t ht
    simp only [ht, P, wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex]
  have hPv₀ : (fun t ↦ P (v₀ t)) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ wkpBaseCoordinateCLM (u₀ t) := by
    filter_upwards [hvu₀] with t ht
    simp only [ht, P, wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex]
  obtain ⟨hu, _, hrep⟩ := heat_solution_unique hε.le u u₀ g g₀ F hweak hweak₀
    heq heq₀ (fun t ↦ P (v t)) (fun t ↦ P (v₀ t))
    (P.continuous.comp_continuousOn hv) (P.continuous.comp_continuousOn hv₀)
    hPv hPv₀ (by rw [hinit, hinit₀])
  refine ⟨hu ▸ hH2, ?_⟩
  intro t ht
  have hvv : v t = v₀ t := wkpBaseCoordinateCLM_injective isOpen_univ (hrep ht)
  rw [hvv]
  exact hbound₀ t ht

/-- A zero-initial heat response is bounded by the L² forcing with a
constant depending on an upper bound for the interval length. This estimate
has no inverse power of the interval length. -/
theorem heat_solution_zero_initial_norm_le
    (hε : 0 < ε) (hab : a < b) {H : ℝ} (hH : b - a ≤ H)
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (v : ℝ → W^{1,2}(ℝ^n)) (hv : ContinuousOn v (Icc a b))
    (hvu : v =ᵐ[volume.restrict (Ioc a b)] fun t ↦
      lowerOrderCLM (by omega : 1 ≤ 2) (u t))
    (hinit : v a = 0) :
    ∀ t ∈ Icc a b,
      ‖v t‖ ≤ Real.sqrt ((1 + (n : ℝ) / ε) * Real.exp H) * ‖F‖ := by
  have hb := (heat_solution_estimates hε hab u g F 0 heq hweak v hv hvu hinit).2
  have hFnorm : (∫ s in a..b, ‖F s‖ ^ 2) = ‖F‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le hab.le]
  have hC : 0 ≤ (1 + (n : ℝ) / ε) * Real.exp H := by positivity
  intro t ht
  have hsmall : Real.exp (t - a) ≤ Real.exp H :=
    Real.exp_le_exp.mpr ((sub_le_sub_right ht.2 a).trans hH)
  have hp : ‖v t‖ ^ 2 ≤ ((1 + (n : ℝ) / ε) * Real.exp H) * ‖F‖ ^ 2 := by
    have he := hb t ht
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add, hFnorm] at he
    have hh := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ (1 + (n : ℝ) / ε) * ‖F‖ ^ 2 by positivity)
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hC]
  exact hp

end PDE.Parabolic.Heat

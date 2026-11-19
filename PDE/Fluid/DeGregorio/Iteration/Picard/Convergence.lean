/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Uniqueness
import CAS.ExactTactic

/-!
# Convergence of frozen transport iterates

Every sequence obtained by solving the frozen equation at each step converges
geometrically to the coupled solution, for every choice of frozen outputs. Coupled
uniqueness then gives a positive-time solution that is unique in its supported H²
class (`exists_hkCurve_local_solution_unique_in_ball`).
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}

/-- Each frozen step reduces its uniform L² distance to the coupled
solution. Iteration gives the geometric error bound for every choice of outputs. -/
theorem IsHkFrozenOutput.dist_iterates_le
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    {L : ℝ} (hL : 0 ≤ L) (hRL : R < L)
    (hsmall : ∀ s ∈ Icc 0 T,
      gronwallBound 0 (5 * (2 * (B : ℝ)))
        ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) s ≤ 1 / 2)
    (f : ℕ → C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    (hstep : ∀ n, ∃ d z : ℝ → ℝ → ℝ,
      IsHkFrozenOutput hT (f n) (f (n + 1)) W₀ w₀ d z) :
    ∀ n, dist (f n) F ≤ Real.sqrt (1 / 2) ^ n * dist (f 0) F := by
  intro n
  induction n with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ n ih =>
    obtain ⟨d, z, hn⟩ := hstep n
    calc
      dist (f (n + 1)) F ≤ Real.sqrt (1 / 2) * dist (f n) F :=
        hn.dist_le_sqrt_half hF hL hRL hsmall
      _ ≤ Real.sqrt (1 / 2) * (Real.sqrt (1 / 2) ^ n * dist (f 0) F) :=
        mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _)
      _ = Real.sqrt (1 / 2) ^ (n + 1) * dist (f 0) F := by
        rw [pow_succ]
        cas

/-- Frozen iterates converge uniformly in L² to the coupled solution,
including both time endpoints. -/
theorem IsHkFrozenOutput.tendsto_iterates
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    {L : ℝ} (hL : 0 ≤ L) (hRL : R < L)
    (hsmall : ∀ s ∈ Icc 0 T,
      gronwallBound 0 (5 * (2 * (B : ℝ)))
        ((2 * (B : ℝ)) * (1 + 2 * L ^ 2)) s ≤ 1 / 2)
    (f : ℕ → C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    (hstep : ∀ n, ∃ d z : ℝ → ℝ → ℝ,
      IsHkFrozenOutput hT (f n) (f (n + 1)) W₀ w₀ d z) :
    Tendsto f atTop (𝓝 F) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) (hF.dist_iterates_le hL hRL hsmall f hstep)
  have hq : Real.sqrt (1 / 2) < 1 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hq).mul_const (dist (f 0) F)

/-- Supported weak H² data generate a positive-time coupled classical solution
which is unique among coupled outputs in the same supported H² class. -/
theorem exists_hkCurve_local_solution_unique_in_ball
    {S : ℝ} (hS : 0 ≤ S) (W₀ : W^{2,2}((Set.univ : Set (ℝ^1))))
    {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0) :
    ∃ (T : ℝ) (hT : 0 < T) (B : NNReal)
      (F : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
            Icc (-(S * Real.exp 2)) (S * Real.exp 2)) B))
      (c w : ℝ → ℝ → ℝ),
      IsHkFrozenOutput hT.le F F W₀ w₀ c w ∧
      IsClassicalSolutionOn 1 ⟨w, hkCurveHilbertVelocity hT.le F⟩ (Ioo 0 T) ∧
      ∀ (G : C(Icc (0 : ℝ) T,
          supportedHkBaseBall 1 2 univ
            (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
              Icc (-(S * Real.exp 2)) (S * Real.exp 2)) B))
        (d z : ℝ → ℝ → ℝ), IsHkFrozenOutput hT.le G G W₀ w₀ d z → G = F := by
  obtain ⟨T, hT, B, F, c, w, hF, hsol⟩ :=
    exists_hkCurve_local_solution hS W₀ hw₀ hW₀ hsupp₀
  exact ⟨T, hT, B, F, c, w, hF, hsol, fun _ _ _ hG ↦ hG.eq_of_self hF⟩

end DeGregorio.Iteration

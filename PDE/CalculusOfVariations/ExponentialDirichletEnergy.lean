/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Dirichlet
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A Dirichlet minimizer with exponential gradient growth

The density `exp (‖z‖²) + (s - 1)²` is convex in the gradient and bounds its squared
norm from below. Its exponential growth is compatible with minimization on `W¹²₀`
when energy is a nonnegative Lebesgue integral, allowed to take the value `∞`.

The zero field has energy twice the domain measure, so every bounded measurable domain
in positive dimension has a finite-energy minimizer. On open domains the boundary
condition is the usual `W¹²₀` condition; on measurable sets it means the supported
smooth-core closure. Neither boundary smoothness nor exponential integrability of all
competitors is required. The potential favors the value one, while the boundary data
are zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal

namespace PDE.CalculusOfVariations

/-- The extended Dirichlet energy with density `exp (‖∇u‖²) + (u - 1)²`.
The integral uses the value and weak gradient of a Sobolev field. It can be infinite. -/
def exponentialGradientEnergy {n : ℕ} {Ω : Set (ℝ^n)}
    (u : W^{1,2}(Ω)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    (Real.exp (‖∇ u x‖ ^ 2) +
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) u x - 1) ^ 2)
    ∂domainMeasure n Ω

/-- Exponential gradient energy attains a finite minimum among zero-boundary `W¹²`
fields on a bounded measurable domain of positive dimension. The zero field supplies
an admissible competitor of energy `2 * |Ω|`. Every field in the supported smooth-core
closure is included in the comparison, even when its energy is infinite. For open
`Ω`, this is minimization over `W¹²₀(Ω)`; no regularity of the boundary is assumed. -/
theorem exists_minimizer_exponentialGradientEnergy_zero_boundary
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ u : W^{1,2}(Ω),
      u ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) ∧
      exponentialGradientEnergy u ≠ ∞ ∧
      ∀ v : W^{1,2}(Ω),
        v ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) →
        exponentialGradientEnergy u ≤ exponentialGradientEnergy v := by
  let F (_x : ℝ^n) (q : ℝ × ℝ^n) : ℝ :=
    Real.exp (‖q.2‖ ^ 2) + (q.1 - 1) ^ 2
  let D (_x : ℝ^n) (q : ℝ × ℝ^n) : ℝ^n :=
    Real.exp (‖q.2‖ ^ 2) • ((2 : ℝ) • q.2)
  have hF : Measurable (Function.uncurry F) := by
    apply Continuous.measurable
    dsimp only [F, Function.uncurry]
    fun_prop
  have hD : Measurable (Function.uncurry D) := by
    apply Continuous.measurable
    dsimp only [D, Function.uncurry]
    fun_prop
  have hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ F x (s, z)) := by
    apply Filter.Eventually.of_forall
    intro x z
    dsimp only [F]
    fun_prop
  have hDcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ D x (s, z)) := by
    apply Filter.Eventually.of_forall
    intro x z
    dsimp only [D]
    exact continuous_const
  have hsq : ConvexOn ℝ univ (fun z : ℝ^n ↦ ‖z‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2
  have hexp : ConvexOn ℝ univ (fun z : ℝ^n ↦ Real.exp (‖z‖ ^ 2)) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (Real.exp_le_exp.mpr (hsq.2 hx hy ha hb hab)).trans
      (convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab)
  have hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ,
      ConvexOn ℝ univ (fun z : ℝ^n ↦ F x (s, z)) :=
    Filter.Eventually.of_forall fun _ s ↦ hexp.add_const ((s - 1) ^ 2)
  have hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      HasFDerivAt (fun y : ℝ^n ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z := by
    apply Filter.Eventually.of_forall
    intro x s z
    have hmap : innerSL ℝ (D x (s, z)) =
        Real.exp (‖z‖ ^ 2) • (2 • innerSL ℝ z) := by
      simp only [D, two_smul]
      apply ContinuousLinearMap.ext
      intro v
      change inner ℝ (Real.exp (‖z‖ ^ 2) • (z + z)) v =
        Real.exp (‖z‖ ^ 2) * (inner ℝ z v + inner ℝ z v)
      rw [real_inner_smul_left, inner_add_left]
    rw [hmap]
    exact ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.exp).add_const ((s - 1) ^ 2)
  have hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      1 * ‖z‖ ^ ((2 : ℝ≥0) : ℝ) - (0 : ℝ) ≤ F x (s, z) := by
    apply Filter.Eventually.of_forall
    intro x s z
    change 1 * ‖z‖ ^ (2 : ℝ) - 0 ≤ Real.exp (‖z‖ ^ 2) + (s - 1) ^ 2
    rw [one_mul, sub_zero, Real.rpow_two]
    linarith [Real.add_one_le_exp (‖z‖ ^ 2), sq_nonneg (s - 1)]
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hΩbounded
  have hzero : exponentialGradientEnergy (n := n) (Ω := Ω) 0 =
      2 * (domainMeasure n Ω) univ := by
    unfold exponentialGradientEnergy
    simp only [map_zero]
    calc
      _ = ∫⁻ _x, (2 : ℝ≥0∞) ∂domainMeasure n Ω := by
        apply lintegral_congr_ae
        filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω),
          Lp.coeFn_zero (ℝ^n) 2 (domainMeasure n Ω)] with x hx hz
        simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at hx hz ⊢
        rw [hx, hz]
        norm_num
      _ = 2 * (domainMeasure n Ω) univ := lintegral_const 2
  have hzero_finite : exponentialGradientEnergy (n := n) (Ω := Ω) 0 ≠ ∞ := by
    rw [hzero]
    exact ENNReal.mul_ne_top (by norm_num) (measure_ne_top (domainMeasure n Ω) univ)
  have hfinite : (∫⁻ x, ENNReal.ofReal (F x
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2)
          ((0 : W^{1,2}(Ω)) + ((0 : W₀^{1,2}(Ω)) :
            W^{1,2}(Ω))) x,
        ∇ ((0 : W^{1,2}(Ω)) + ((0 : W₀^{1,2}(Ω)) :
            W^{1,2}(Ω))) x) + 0) ∂domainMeasure n Ω) ≠ ∞ := by
    simpa only [F, ZeroMemClass.coe_zero, add_zero, exponentialGradientEnergy]
      using hzero_finite
  have hmin := exists_minimizer_mixedWkpLIntegral_prescribed_boundary
    (p := (2 : ℝ≥0)) (F := F) (D := D) (b := fun _ ↦ 0)
    hΩmeas hΩbounded (by norm_num)
  simp only [ENNReal.coe_ofNat] at hmin
  obtain ⟨u, hu, hufinite, humin⟩ :=
    hmin hF hD (measurable_const : Measurable (fun _ : ℝ^n ↦ (0 : ℝ)))
      hFcont hDcont hconvex hderiv (c := 1) zero_lt_one hlower
      (0 : W^{1,2}(Ω)) (0 : W₀^{1,2}(Ω)) hfinite
  refine ⟨u, ?_, ?_, ?_⟩
  · have huzero : u - (0 : W^{1,2}(Ω)) ∈
        wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) := hu
    rw [sub_zero] at huzero
    exact huzero
  · simp only [F, add_zero] at hufinite
    refine cast ?_ hufinite
    rfl
  · intro v hv
    have hvzero : v - (0 : W^{1,2}(Ω)) ∈
        wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) := by
      rw [sub_zero]
      exact hv
    have hle := humin v hvzero
    simp only [F, add_zero] at hle
    refine cast ?_ hle
    rfl

end PDE.CalculusOfVariations

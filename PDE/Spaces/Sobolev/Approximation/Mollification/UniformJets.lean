/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.FiniteJets
import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Uniform jet approximation by the standard mollifier

For a compactly supported `C^m` function `G`, the mollifications `G_j` at the scales `1/(j+1)`
by the standard mollifier eventually approximate every derivative word of length at most `m` to
within any given `η`, uniformly on the whole space; they vanish outside the support radius of `G`
plus two, and they are odd under a coordinate reflection when `G` is (the companion of
`mollify_even_of_radial`).

## Main results

* `eventually_abs_iteratedPartialDeriv_mollify_sub_le`: for every `η > 0`, eventually every
  derivative word of length at most `m` of `G_j` is within `η` of that of `G`, uniformly.
* `mollify_eq_zero_of_lt_norm`: at a scale at most one, the mollification of a function vanishing
  outside the radius `ρ` vanishes outside the radius `ρ + 2`.
* `mollify_odd_of_radial`: mollification by a radial kernel preserves oddness under each
  coordinate reflection.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Mollification by a radial kernel preserves oddness under each coordinate reflection. -/
theorem mollify_odd_of_radial
    (μ : Mollifier n) (w : ℝ → ℝ) (hρ : ∀ x, μ.ρ x = w ‖x‖)
    {ε : ℝ} (hε : 0 < ε) (i : Fin n) {f : ℝ^n → ℝ}
    (hf : PDE.Common.IsOddUnderCoordinateReflection i f) :
    PDE.Common.IsOddUnderCoordinateReflection i (mollify μ ε f) := by
  intro x
  have hscaled : ∀ y, scaled μ ε (PDE.Common.coordinateReflection i y) = scaled μ ε y := by
    intro y
    simp only [scaled_of_pos μ hε, hρ, norm_smul, PDE.Common.norm_coordinateReflection]
  calc
    mollify μ ε f (PDE.Common.coordinateReflection i x) =
        ∫ y, scaled μ ε (PDE.Common.coordinateReflection i y) *
          f (PDE.Common.coordinateReflection i x - PDE.Common.coordinateReflection i y) := by
      simpa only [mollify, convolution_lsmul, smul_eq_mul, PDE.Common.coordinateReflection] using
        (MeasureTheory.integral_comp (PDE.Common.coordinateReflectionLinearIsometryEquiv i)
          (fun y ↦ scaled μ ε y * f (PDE.Common.coordinateReflection i x - y))).symm
    _ = ∫ y, -(scaled μ ε y * f (x - y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hscaled, ← PDE.Common.coordinateReflection_sub, hf, mul_neg]
    _ = -mollify μ ε f x := by
      rw [integral_neg]
      simp only [mollify, convolution_lsmul, smul_eq_mul]

/-- The mollification of a function vanishing outside the radius `ρ` by the standard mollifier at
a scale at most one vanishes outside the radius `ρ + 2`. -/
theorem mollify_eq_zero_of_lt_norm {G : ℝ^n → ℝ} {ρ : ℝ} (hG : ∀ x, ρ < ‖x‖ → G x = 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℝ^n} (hx : ρ + 2 < ‖x‖) :
    mollify (standardMollifier n) ε G x = 0 := by
  by_contra hne
  obtain ⟨y, hy, z, hz, rfl⟩ := support_mollify_subset_closedBall_add_support _ hε
    (tsupport_standardMollifier_subset_closedBall n) G hne
  have hy' : ‖y‖ ≤ ε * 2 := by simpa using hy
  have hz' : ‖z‖ ≤ ρ := by
    by_contra h
    exact hz (hG z (lt_of_not_ge h))
  have := norm_add_le y z
  nlinarith

/-- The derivative words of the mollifications of a compactly supported `C^m` function converge
uniformly: for every `η > 0`, eventually every word of length at most `m` is within `η` of the
corresponding word of the function, at every point. -/
theorem eventually_abs_iteratedPartialDeriv_mollify_sub_le {m : ℕ} {G : ℝ^n → ℝ}
    (hG : ContDiff ℝ m G) (hGc : HasCompactSupport G) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop, ∀ w : List (Fin n), w.length ≤ m → ∀ x : ℝ^n,
      |iteratedPartialDeriv w (mollify (standardMollifier n) (1 / ((j : ℝ) + 1)) G) x -
        iteratedPartialDeriv w G x| ≤ η := by
  set ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hεpos : ∀ j, 0 < ε j := fun j ↦ by positivity
  have hεle : ∀ j, ε j ≤ 1 := fun j ↦ by
    simp only [ε]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hfin : ∀ k : Fin (m + 1), ∀ v : Fin k → Fin n, ∀ᶠ j : ℕ in atTop, ∀ x : ℝ^n,
      |iteratedPartialDeriv (List.ofFn v) (mollify (standardMollifier n) (ε j) G) x -
        iteratedPartialDeriv (List.ofFn v) G x| ≤ η := by
    intro k v
    have hu := iteratedPartialDeriv_mollify_tendstoUniformly
      (standardMollifier n) hG hGc ε hεpos hεle hε0 (List.ofFn v)
      (by simpa using Nat.lt_succ_iff.1 k.2)
    filter_upwards [Metric.tendstoUniformly_iff.1 hu η hη] with j hj x
    have := hj x
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hall : ∀ᶠ j : ℕ in atTop, ∀ k : Fin (m + 1), ∀ v : Fin k → Fin n, ∀ x : ℝ^n,
      |iteratedPartialDeriv (List.ofFn v) (mollify (standardMollifier n) (ε j) G) x -
        iteratedPartialDeriv (List.ofFn v) G x| ≤ η :=
    eventually_all.2 fun k ↦ eventually_all.2 fun v ↦ hfin k v
  filter_upwards [hall] with j hj w hw x
  have := hj ⟨w.length, Nat.lt_succ_of_le hw⟩ w.get x
  simpa only [List.ofFn_get] using this

end SobolevSpace.Approximation

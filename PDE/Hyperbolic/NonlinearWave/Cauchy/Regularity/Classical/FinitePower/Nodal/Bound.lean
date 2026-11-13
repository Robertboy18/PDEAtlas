/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Nodal.Increment
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Integration
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.PowerHolder
import CAS.ExactTactic

/-!
# Uniform bounds for nodal increments

Signed-power increment estimates provide common majorants for passing normalized nodal limits
through an integral.
-/

@[expose] public noncomputable section

section

open Set
open WaveEquation.SmallData.Classical.LocalPower.LowerPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- The coefficient difference and the velocity difference have separate bounds. -/
theorem norm_abs_rpow_mul_sub_le {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (a b c d : ℝ) :
    ‖|a| ^ α * c - |b| ^ α * d‖ ≤ ‖a - b‖ ^ α * ‖c‖ + |b| ^ α * ‖c - d‖ := by
  have hc : ‖|a| ^ α - |b| ^ α‖ ≤ ‖a - b‖ ^ α :=
    (norm_rpow_sub_le_rpow_norm_sub hα hα₁ (abs_nonneg a) (abs_nonneg b)).trans
      (Real.rpow_le_rpow (norm_nonneg _) (by
        simpa only [Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub a b) hα)
  have he : |a| ^ α * c - |b| ^ α * d =
      (|a| ^ α - |b| ^ α) * c + |b| ^ α * (c - d) := by cas
  rw [he]
  calc
    _ ≤ ‖(|a| ^ α - |b| ^ α) * c‖ + ‖|b| ^ α * (c - d)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact add_le_add (mul_le_mul_of_nonneg_right hc (norm_nonneg c)) le_rfl

/-- Linear increments of a field and velocity give a Hölder increment for the source derivative. -/
theorem norm_abs_rpow_mul_increment_le {α M N L L' t : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hL : 0 ≤ L)
    (hL' : 0 ≤ L') (hM : 0 ≤ M) (ht : |t| ≤ 1) {u v : ℝ → ℝ} (hu₀ : |u 0| ≤ M) (hv : ‖v t‖ ≤ N)
    (hu : ‖u t - u 0‖ ≤ L * |t|) (hv' : ‖v t - v 0‖ ≤ L' * |t|) :
    ‖|u t| ^ α * v t - |u 0| ^ α * v 0‖ ≤ (L ^ α * N + M ^ α * L') * |t| ^ α := by
  have hp : (L * |t|) ^ α = L ^ α * |t| ^ α := Real.mul_rpow hL (abs_nonneg _)
  have hb : |t| ≤ |t| ^ α := Real.self_le_rpow_of_le_one (abs_nonneg _) ht hα₁
  calc
    _ ≤ ‖u t - u 0‖ ^ α * ‖v t‖ + |u 0| ^ α * ‖v t - v 0‖ := norm_abs_rpow_mul_sub_le hα hα₁ _ _ _ _
    _ ≤ (L * |t|) ^ α * N + M ^ α * (L' * |t|) := add_le_add
        (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hu hα) hv (norm_nonneg _)
          (Real.rpow_nonneg (mul_nonneg hL (abs_nonneg _)) _))
        (mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) hu₀ hα) hv' (norm_nonneg _)
          (Real.rpow_nonneg hM _))
    _ ≤ (L ^ α * |t| ^ α) * N + M ^ α * (L' * |t| ^ α) := by
      rw [hp]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hL')
          (Real.rpow_nonneg hM _))
    _ = _ := by cas

/-- Symmetric quotients have a fixed majorant on both sides of zero. -/
theorem norm_symmetric_abs_rpow_mul_increment_le {α M N L L' t : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') (hM : 0 ≤ M) (ht : 0 < t) (ht₁ : t ≤ 1) {u v : ℝ → ℝ}
    (hu₀ : |u 0| ≤ M) (hv : ∀ s ∈ ({t, -t} : Set ℝ), ‖v s‖ ≤ N)
    (hu : ∀ s ∈ ({t, -t} : Set ℝ), ‖u s - u 0‖ ≤ L * |s|)
    (hv' : ∀ s ∈ ({t, -t} : Set ℝ), ‖v s - v 0‖ ≤ L' * |s|) :
    ‖(|u t| ^ α * v t + |u (-t)| ^ α * v (-t) - 2 * |u 0| ^ α * v 0) / (2 * t ^ α)‖ ≤
      L ^ α * N + M ^ α * L' := by
  have hp := norm_abs_rpow_mul_increment_le hα hα₁ hL hL' hM
    (by simpa only [abs_of_pos ht] using ht₁) hu₀ (hv t (by simp))
    (hu t (by simp)) (hv' t (by simp))
  have hn := norm_abs_rpow_mul_increment_le hα hα₁ hL hL' hM
    (by simpa only [abs_neg, abs_of_pos ht] using ht₁) hu₀ (hv (-t) (by simp))
    (hu (-t) (by simp)) (hv' (-t) (by simp))
  have he : |u t| ^ α * v t + |u (-t)| ^ α * v (-t) - 2 * |u 0| ^ α * v 0 =
      (|u t| ^ α * v t - |u 0| ^ α * v 0) +
        (|u (-t)| ^ α * v (-t) - |u 0| ^ α * v 0) := by cas
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * t ^ α)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * t ^ α)).mpr
  rw [he]
  calc
    _ ≤ ‖|u t| ^ α * v t - |u 0| ^ α * v 0‖ +
        ‖|u (-t)| ^ α * v (-t) - |u 0| ^ α * v 0‖ := norm_add_le _ _
    _ ≤ (L ^ α * N + M ^ α * L') * |t| ^ α + (L ^ α * N + M ^ α * L') * |-t| ^ α := add_le_add hp hn
    _ = _ := by rw [abs_neg, abs_of_pos ht]; cas

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter MeasureTheory BoundedContinuousFunction
open scoped Topology
open WaveEquation.SmallData.Classical.LocalPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {K : Type} [TopologicalSpace K]

/-- Differentiability in the uniform norm supplies one majorant for the nodal quotients. -/
theorem exists_uniform_nodal_majorant {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) {U V : ℝ → K →ᵇ ℝ}
    (hU : DifferentiableAt ℝ U 0) (hV : DifferentiableAt ℝ V 0) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ z : K, ‖(|U t z| ^ α * V t z + |U (-t) z| ^ α * V (-t) z - 2 *
      (|U 0 z| ^ α * V 0 z)) / (2 * t ^ α)‖ ≤ C := by
  obtain ⟨L, hL, hUL⟩ := hU.hasDerivAt.isBigO_sub.exists_pos
  obtain ⟨L', hL', hVL⟩ := hV.hasDerivAt.isBigO_sub.exists_pos
  refine ⟨L ^ α * (‖V 0‖ + L') + ‖U 0‖ ^ α * L', ?_⟩
  have hboth : ∀ᶠ t : ℝ in 𝓝 0,
      ‖U t - U 0‖ ≤ L * |t| ∧ ‖V t - V 0‖ ≤ L' * |t| := by
    simpa only [sub_zero, Real.norm_eq_abs] using hUL.bound.and hVL.bound
  have hnegT : Tendsto (fun t : ℝ ↦ -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0 : ℝ)
  have hneg := hnegT.eventually hboth
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hboth.filter_mono nhdsWithin_le_nhds,
    hneg.filter_mono nhdsWithin_le_nhds, hsmall.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hp hn ht hpos
  intro z
  have hu (s : ℝ) (hs : s ∈ ({t, -t} : Set ℝ)) :
      ‖U s z - U 0 z‖ ≤ L * |s| := by
    have h := (U s - U 0).norm_coe_le_norm z
    rcases hs with hs | hs
    · subst s
      exact h.trans hp.1
    · simp only [mem_singleton_iff] at hs
      subst s
      exact h.trans hn.1
  have hv (s : ℝ) (hs : s ∈ ({t, -t} : Set ℝ)) :
      ‖V s z - V 0 z‖ ≤ L' * |s| := by
    have h := (V s - V 0).norm_coe_le_norm z
    rcases hs with hs | hs
    · subst s
      exact h.trans hp.2
    · simp only [mem_singleton_iff] at hs
      subst s
      exact h.trans hn.2
  have hvs (s : ℝ) (hs : s ∈ ({t, -t} : Set ℝ)) : ‖V s z‖ ≤ ‖V 0‖ + L' := by
    have hst : |s| ≤ 1 := by
      rcases hs with hs | hs
      · subst s
        exact ht.le
      · simp only [mem_singleton_iff] at hs
        subst s
        simpa only [abs_neg] using ht.le
    calc
      _ ≤ ‖V s z - V 0 z‖ + ‖V 0 z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (V s z - V 0 z) (V 0 z)
      _ ≤ L' * |s| + ‖V 0‖ := add_le_add (hv s hs) ((V 0).norm_coe_le_norm z)
      _ ≤ ‖V 0‖ + L' := by nlinarith
  simpa only [mul_assoc] using norm_symmetric_abs_rpow_mul_increment_le
    (u := fun s ↦ U s z) (v := fun s ↦ V s z) hα hα₁ hL.le hL'.le
    (norm_nonneg (U 0)) hpos (by simpa only [abs_of_pos hpos] using ht.le)
    ((U 0).norm_coe_le_norm z) hvs hu hv

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter BoundedContinuousFunction
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {K : Type} [TopologicalSpace K]

/-- A continuous velocity is uniformly bounded in the nodal quotient on exact zeros. -/
theorem exists_uniform_nodal_majorant_on_zeros {α : ℝ} (hα : 0 < α) {U V : ℝ → K →ᵇ ℝ}
    (hU : DifferentiableAt ℝ U 0) (hV : ContinuousAt V 0) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ z : K, U 0 z = 0 → ‖(|U t z| ^ α * V t z + |U (-t) z| ^ α *
      V (-t) z - 2 * (|U 0 z| ^ α * V 0 z)) / (2 * t ^ α)‖ ≤ C := by
  obtain ⟨L, hL, hUL⟩ := hU.hasDerivAt.isBigO_sub.exists_pos
  let N : ℝ := ‖V 0‖ + 1
  have hVB : ∀ᶠ t : ℝ in 𝓝 0, ‖V t‖ < N :=
    hV.norm.eventually (gt_mem_nhds (by dsimp [N]; linarith))
  have hboth : ∀ᶠ t : ℝ in 𝓝 0,
      ‖U t - U 0‖ ≤ L * |t| ∧ ‖V t‖ < N := by
    simpa only [sub_zero, Real.norm_eq_abs] using hUL.bound.and hVB
  have hnegT : Tendsto (fun t : ℝ ↦ -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0 : ℝ)
  refine ⟨L ^ α * N, ?_⟩
  filter_upwards [hboth.filter_mono nhdsWithin_le_nhds,
    (hnegT.eventually hboth).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hp hn ht
  change 0 < t at ht
  intro z hz
  have hterm (s : ℝ) (hs : ‖U s - U 0‖ ≤ L * |s| ∧ ‖V s‖ < N) :
      ‖|U s z| ^ α * V s z‖ ≤ (L ^ α * N) * |s| ^ α := by
    have hu : |U s z| ≤ L * |s| := by
      simpa only [BoundedContinuousFunction.sub_apply, hz, sub_zero, Real.norm_eq_abs] using
        ((U s - U 0).norm_coe_le_norm z).trans hs.1
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      _ ≤ (L * |s|) ^ α * N := mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) hu hα.le)
        ((V s).norm_coe_le_norm z |>.trans hs.2.le) (norm_nonneg _)
        (Real.rpow_nonneg (mul_nonneg hL.le (abs_nonneg _)) _)
      _ = _ := by rw [Real.mul_rpow hL.le (abs_nonneg _)]; cas
  rw [hz, abs_zero, Real.zero_rpow hα.ne', zero_mul, mul_zero, sub_zero,
    norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * t ^ α)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * t ^ α)).mpr
  calc
    _ ≤ ‖|U t z| ^ α * V t z‖ + ‖|U (-t) z| ^ α * V (-t) z‖ := norm_add_le _ _
    _ ≤ (L ^ α * N) * |t| ^ α + (L ^ α * N) * |-t| ^ α := add_le_add (hterm t hp) (hterm (-t) hn)
    _ = _ := by rw [abs_neg, abs_of_pos ht]; cas

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

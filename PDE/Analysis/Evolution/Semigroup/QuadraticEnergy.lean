/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Work done by continuous forcing in a conservative semigroup

A strongly continuous semigroup preserving a continuous symmetric quadratic form
satisfies the corresponding work identity along its Duhamel curves. The initial
state need not belong to the generator domain.

Fixing a terminal time and propagating every earlier state to that time turns the
mild curve into a differentiable primitive. Preservation of the bilinear form then
identifies its derivative with the work done by the original forcing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Preservation of a symmetric quadratic form also preserves its bilinear pairing. -/
theorem bilinear_eq_of_quadratic_eq (T : StronglyContinuousSemigroup E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (henergy : ∀ t x, B (T t x) (T t x) = B x x)
    (t : NNReal) (x y : E) : B (T t x) (T t y) = B x y := by
  have h := henergy t (x + y)
  have hx := henergy t x
  have hy := henergy t y
  simp only [_root_.map_add, _root_.add_apply] at h
  rw [hsymm (T t y) (T t x), hsymm y x] at h
  linarith

variable [CompleteSpace E]

/-- Propagating a mild state from `s` to a fixed terminal time `t` leaves an
ordinary integral with a fixed terminal lag. Only nonnegative times are used. -/
theorem propagate_mild_eq (T : StronglyContinuousSemigroup E)
    {f : ℝ → E} (hf : Continuous f) (x₀ : E)
    {s t : ℝ} (hs : s ∈ Icc 0 t) :
    T (t - s).toNNReal (T s.toNNReal x₀ + T.duhamel f s) =
      T t.toNNReal x₀ + ∫ r in (0 : ℝ)..s, T (t - r).toNNReal (f r) := by
  rw [_root_.map_add]
  congr 1
  · rw [← T.map_add_apply,
      ← Real.toNNReal_add (sub_nonneg.mpr hs.2) hs.1, sub_add_cancel]
  · rw [duhamel, ← (T (t - s).toNNReal).intervalIntegral_comp_comm
      ((T.continuous_duhamelIntegrand hf s).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.1] at hr
    change T (t - s).toNNReal (T (s - r).toNNReal (f r)) =
      T (t - r).toNNReal (f r)
    rw [← T.map_add_apply,
      ← Real.toNNReal_add (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hr.2)]
    rw [sub_add_sub_cancel]

/-- The change in quadratic energy of a Duhamel curve equals the work of its
continuous forcing. No differentiability of the semigroup orbit is required. -/
theorem quadratic_energy_duhamel (T : StronglyContinuousSemigroup E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (henergy : ∀ t x, B (T t x) (T t x) = B x x)
    {f : ℝ → E} (hf : Continuous f) (x₀ : E) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ T s.toNNReal x₀ + T.duhamel f s
    (1 / 2 : ℝ) * B (z t) (z t) - (1 / 2 : ℝ) * B x₀ x₀ =
      ∫ s in (0 : ℝ)..t, B (z s) (f s) := by
  let z := fun s ↦ T s.toNNReal x₀ + T.duhamel f s
  let g := fun s ↦ T (t - s).toNNReal (f s)
  let w := fun s ↦ T t.toNNReal x₀ + ∫ r in (0 : ℝ)..s, g r
  change (1 / 2 : ℝ) * B (z t) (z t) - (1 / 2 : ℝ) * B x₀ x₀ = _
  have hg : Continuous g := T.continuous_duhamelIntegrand hf t
  have hwderiv (s : ℝ) : HasDerivAt w (g s) s :=
    (intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (μ := volume) 0 s)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt).const_add (T t.toNNReal x₀)
  have hw : Continuous w :=
    continuous_iff_continuousAt.mpr fun s ↦ (hwderiv s).continuousAt
  have hwork : Continuous (fun s ↦ B (w s) (g s)) :=
    (B.continuous.comp hw).clm_apply hg
  have hderiv (s : ℝ) :
      HasDerivAt (fun r ↦ (1 / 2 : ℝ) * B (w r) (w r)) (B (w s) (g s)) s := by
    have hd := (B.hasDerivAt_of_bilinear (fun _ ↦ hwderiv s)
      (fun _ ↦ hwderiv s)).const_mul (1 / 2 : ℝ)
    exact hd.congr_deriv (by rw [hsymm (g s) (w s)]; ring)
  have hprop (s : ℝ) (hs : s ∈ Icc 0 t) :
      w s = T (t - s).toNNReal (z s) := (T.propagate_mild_eq hf x₀ hs).symm
  have hwt : w t = z t := by
    simpa only [sub_self, Real.toNNReal_zero, T.map_zero_apply] using hprop t ⟨ht, le_rfl⟩
  have hwzero : w 0 = T t.toNNReal x₀ := by
    simp only [w, intervalIntegral.integral_same, add_zero]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hderiv s) (hwork.intervalIntegrable (μ := volume) 0 t)
  rw [hwt, hwzero, henergy] at hftc
  rw [← hftc]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  change B (w s) (g s) = B (z s) (f s)
  rw [hprop s hs]
  exact T.bilinear_eq_of_quadratic_eq B hsymm henergy (t - s).toNNReal (z s) (f s)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup

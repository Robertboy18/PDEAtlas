/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.LinearGrowth
import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.FDeriv.Calculus

/-!
# Propagation from one nonnegative compact slice

A nonnegative field has zero Cauchy derivative outside its displacement support.
The fixed-anchor propagation theorem then gives a support radius independent
of a positive lower time cutoff.
-/

@[expose] public noncomputable section

open Filter Set PDE PDE.Common
open scoped Topology

namespace WaveEquation

/-- Nonnegativity supplies the missing compact velocity at time one. Propagation
then gives common support down to every strictly positive time below one. -/
theorem exists_uniform_support_near_initial_of_nonneg {n : ℕ} [Fact (0 < n)] {f : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : Continuous f) (hfO : f =O[𝓝 0] (fun z : ℝ ↦ z))
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hnonneg : ∀ p, 0 < p 0 → 0 ≤ u p)
    (hwave : ∀ t, 0 < t → ∀ x, waveOperator u (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hs : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons 1 x))) :
    ∃ R : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ℝ^n, R < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
  have hpos (x : ℝ^n) (hx : R < ‖x‖) : u (timeSpaceCons 1 x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun y : ℝ^n ↦ u (timeSpaceCons 1 y))
    intro hxmem
    have hnorm : ‖x‖ ≤ R := by simpa using hR hxmem
    exact hx.not_ge hnorm
  have hvel (x : ℝ^n) (hx : R < ‖x‖) : (∂[0] u) (timeSpaceCons 1 x) = 0 := by
    have hmin : IsLocalMin u (timeSpaceCons 1 x) := by
      change ∀ᶠ p in 𝓝 (timeSpaceCons 1 x), u (timeSpaceCons 1 x) ≤ u p
      have htime : ∀ᶠ p : ℝ^(n + 1) in 𝓝 (timeSpaceCons 1 x), 0 < p 0 :=
        (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds (by simp)
      filter_upwards [htime] with p hp
      rw [hpos x hx]
      exact hnonneg p hp
    simp only [partialDeriv, hmin.fderiv_eq_zero, zero_apply]
  refine ⟨R + 2, fun t ht x hx ↦ ?_⟩
  obtain ⟨U, hU, heq⟩ := exists_contDiff_eqOn_forward hu (half_pos ht.1)
  have hlocal (s : ℝ) (hs' : t ≤ s) (y : ℝ^n) : U =ᶠ[𝓝 (timeSpaceCons s y)] u :=
    eventuallyEq_of_eqOn_forward heq
      (by simpa only [timeSpaceCons_zero] using (half_lt_self ht.1).trans_le hs')
  have he := eq_zero_on_Icc_of_cauchySupport_of_isBigO (b := t) (a := 1) (T := 2) (R := R) hf hfO hU
    ⟨ht.2, by norm_num⟩ (fun s hs' y ↦ ?_) (fun y hy ↦ ?_)
    (fun y hy ↦ ?_) t ⟨le_rfl, by linarith [ht.2]⟩ x (by linarith [ht.1])
  · exact (hlocal t le_rfl x).eq_of_nhds.symm.trans he
  · rw [waveOperator_congr_nhds (hlocal s hs'.1 y), (hlocal s hs'.1 y).eq_of_nhds]
    exact hwave s (ht.1.trans_le hs'.1) y
  · exact (hlocal 1 ht.2 y).eq_of_nhds.trans (hpos y hy)
  · rw [partialDeriv_congr_nhds 0 (hlocal 1 ht.2 y)]
    exact hvel y hy

end WaveEquation

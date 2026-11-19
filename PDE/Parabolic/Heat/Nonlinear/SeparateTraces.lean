/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.DirichletBoundaryError

/-!
# Bounded Dirichlet candidates with separate traces

Initial continuity is required only over the open spatial domain. Lateral
continuity is required only at positive times. There is no value or joint limit
condition at the initial/lateral corner. A finite uniform bound on each candidate
cylinder controls integrals at the initial face. Positive-time translations
have the closed-cylinder regularity needed for compact testing.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {T : ℝ}

/-- A bounded classical candidate with separate initial and lateral traces.
The omitted initial/lateral corner carries no continuity or value condition. -/
structure IsBoundedDirichletSquareSolution (Ω : Set (ℝ^n)) (T : ℝ)
    (g : ℝ^n → ℝ) (u : ℝ → ℝ^n → ℝ) : Prop where
  /-- Continuity at the initial face, locally in the open spatial domain. -/
  initial_continuous : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω)
  /-- Continuity at the lateral face, locally in strictly positive time. -/
  lateral_continuous : ContinuousOn u.uncurry (Ioc 0 T ×ˢ closure Ω)
  /-- A uniform finite-cylinder bound excludes singular influx at the omitted corner. -/
  bounded : ∃ B > 0, ∀ t ∈ Icc 0 T, ∀ x ∈ Ω, |u t x| ≤ B
  /-- Joint regularity is needed only inside the cylinder. -/
  smooth : ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω)
  /-- The time derivative satisfies the quadratic heat equation. -/
  equation : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
    deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2
  /-- The lateral trace vanishes at strictly positive interior times. -/
  boundary : ∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u t x = 0
  /-- The initial trace is prescribed only in the open domain. -/
  initial : ∀ x ∈ Ω, u 0 x = g x

variable {g : ℝ^n → ℝ} {u : ℝ → ℝ^n → ℝ}

/-- Translating to strictly positive time avoids every initial/lateral corner. -/
theorem IsBoundedDirichletSquareSolution.shift
    (hu : IsBoundedDirichletSquareSolution Ω T g u)
    {a S : ℝ} (ha : 0 < a) (hS : a + S < T) :
    IsInteriorDirichletSquareSolution Ω S (u a) (fun t x ↦ u (a + t) x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hu.lateral_continuous.comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ by
        refine ⟨?_, hq.2⟩
        change a + q.1 ∈ _
        exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩)
  · exact hu.smooth.comp
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq ↦ ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩)
  · intro t ht x hx
    rw [deriv_comp_const_add (fun r ↦ u r x) a t]
    exact hu.equation (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx
  · intro x hx t ht
    exact hu.boundary x hx (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro x _
    simp

/-- Spatial slices are continuous in the open domain even at time zero. -/
theorem IsBoundedDirichletSquareSolution.continuousOn_slice
    (hu : IsBoundedDirichletSquareSolution Ω T g u)
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContinuousOn (u t) Ω :=
  hu.initial_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hx ↦ ⟨ht, hx⟩)

/-- Boundedness and local initial continuity make every integrable weighted
moment continuous down to zero, without a corner compatibility condition. -/
theorem IsBoundedDirichletSquareSolution.weighted_moment_continuous
    (hu : IsBoundedDirichletSquareSolution Ω T g u) (hΩ : MeasurableSet Ω)
    {w : ℝ^n → ℝ} (hw : IntegrableOn w Ω) :
    ContinuousOn (fun t ↦ ∫ x in Ω, w x * u t x) (Icc 0 T) := by
  obtain ⟨B, _, hB⟩ := hu.bounded
  apply continuousOn_of_dominated (bound := fun x ↦ ‖w x‖ * B)
  · intro t ht
    exact hw.aestronglyMeasurable.mul
      ((hu.continuousOn_slice ht).aestronglyMeasurable hΩ)
  · intro t ht
    filter_upwards [ae_restrict_mem hΩ] with x hx
    simpa only [norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (hB t ht x hx) (norm_nonneg (w x))
  · exact hw.norm.mul_const B
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact continuousOn_const.mul
      (hu.initial_continuous.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht ↦ ⟨ht, hx⟩))

/-- On a positive-time compact strip, a positive Dirichlet weight detects the
boundary layer where the candidate is uniformly small. -/
theorem IsBoundedDirichletSquareSolution.exists_boundary_layer
    (hu : IsBoundedDirichletSquareSolution Ω T g u)
    (hb : Bornology.IsBounded Ω) {w : ℝ^n → ℝ}
    (hw : ContinuousOn w (closure Ω)) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hwzero : ∀ x ∈ frontier Ω, w x = 0)
    {a b η : ℝ} (ha : 0 < a) (hbT : b < T) (hη : 0 < η) :
    ∃ ε > 0, ∀ t ∈ Icc a b, ∀ x ∈ Ω, w x ≤ 2 * ε → |u t x| < η := by
  have hwc : ContinuousOn (fun q : ℝ × ℝ^n ↦ w q.2) (Icc a b ×ˢ closure Ω) :=
    hw.comp continuous_snd.continuousOn (fun _ hq ↦ hq.2)
  have huc : ContinuousOn u.uncurry (Icc a b ×ˢ closure Ω) :=
    hu.lateral_continuous.mono (fun _ hq ↦
      ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans hbT.le⟩, hq.2⟩)
  obtain ⟨ε, hε, hbound⟩ := exists_pos_weight_layer
    (isCompact_Icc.prod hb.isCompact_closure) hwc huc (fun q hq ↦ by
      by_cases hx : q.2 ∈ Ω
      · exact (hwpos q.2 hx).le
      · rw [hwzero q.2 ⟨hq.2, fun h ↦ hx (interior_subset h)⟩])
    (fun q hq hz ↦ by
      have hx : q.2 ∈ frontier Ω := ⟨hq.2, fun h ↦
        (hwpos q.2 (interior_subset h)).ne' hz⟩
      exact hu.boundary q.2 hx q.1 ⟨ha.trans_le hq.1.1, hq.1.2.trans_lt hbT⟩) hη
  exact ⟨ε, hε, fun t ht x hx ↦ hbound (t, x) ⟨ht, subset_closure hx⟩⟩

end HeatEquation.Nonlinear

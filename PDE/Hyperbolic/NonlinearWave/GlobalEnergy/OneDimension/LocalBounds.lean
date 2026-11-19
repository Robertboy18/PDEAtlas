/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.OneDimension.ShortTime
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialCompactness
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SupportPropagation
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Local first-derivative bounds from separately compact wave slices

For a one-dimensional C3 wave with continuous reaction, compact initial velocity
is derived from the PDE and separately compact displacement slices.
Characteristic estimates bound the first jet on an initial slab. Translation and
reflection give a uniform spatial bound near every nonnegative time; reflection
uses only a finite forward band.

These are ingredients for a one-dimensional energy conservation result.
-/

@[expose] public noncomputable section

open PDE PDE.Common Set Filter
open scoped Topology

namespace WaveEquation

/-- Separately compact displacement slices give bounded first derivatives
on a uniform initial time slab in one dimension. Compact initial velocity is obtained from the
PDE. -/
theorem exists_pos_uniform_partialDeriv_bound_of_compact_slices {u : ℝ^2 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiff ℝ 3 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^1, waveOperator u (timeSpaceCons t x) +
      f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x))) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ p : ℝ^2, p 0 ∈ Icc 0 δ → ∀ i : Fin 2, ‖(∂[i] u) p‖ ≤ L := by
  have hg : ContDiff ℝ 2 (fun x : ℝ^1 ↦ u (timeSpaceCons 0 x)) :=
    (hu.of_le (by norm_num)).comp (contDiff_timeSpaceCons_spatial 1 0)
  obtain ⟨G, hG⟩ := hg.continuous.bounded_above_of_compact_support (hs 0 le_rfl)
  have hv : Continuous (fun x : ℝ^1 ↦ (∂[0] u) (timeSpaceCons 0 x)) :=
    (hu.partialDeriv 0 (k := 2) (by norm_num)).continuous.comp
      (contDiff_timeSpaceCons_spatial 1 0 (m := 1)).continuous
  obtain ⟨B₀, hB₀⟩ := hv.bounded_above_of_compact_support
    (hasCompactSupport_initial_velocity_of_compact_slices hf hu hwave hs)
  obtain ⟨B₁, hB₁⟩ := (hg.partialDeriv 0 (k := 1) (by norm_num)).continuous
    |>.bounded_above_of_compact_support ((hs 0 le_rfl).partialDeriv 0)
  have hinitial (p : ℝ^2) (hp : p 0 = 0) :
      timeSpaceCons 0 (spatialPart p) = p := by rw [← hp, timeSpaceCons_spatialPart]
  have hnull (p : ℝ^2) (hp : p 0 = 0) (ε : ℝ) (hε : ε ^ 2 = 1) :
      ‖(∂[0] u) p + ε * (∂[1] u) p‖ ≤ max (B₀ + B₁) 0 := by
    have hspace := partialDeriv_timeSpaceCons_spatial (0 : Fin 1) u 0 (spatialPart p)
      (hu.differentiable (by norm_num)).differentiableAt
    have htbound := hB₀ (spatialPart p)
    have hxbound := hB₁ (spatialPart p)
    rw [hinitial p hp] at htbound hspace
    rw [hspace] at hxbound
    have hεnorm : ‖ε‖ = 1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε, abs_nonneg ε]
    calc
      _ ≤ ‖(∂[0] u) p‖ + ‖ε * (∂[1] u) p‖ := norm_add_le _ _
      _ = ‖(∂[0] u) p‖ + ‖(∂[1] u) p‖ := by rw [norm_mul, hεnorm, one_mul]
      _ ≤ B₀ + B₁ := add_le_add htbound hxbound
      _ ≤ max (B₀ + B₁) 0 := le_max_left _ _
  have hpde (p : ℝ^2) (hp : 0 ≤ p 0) : waveOperator u p + f (u p) = 0 := by
    simpa only [timeSpaceCons_spatialPart] using
      waveOperator_add_eq_zero_of_nonneg hf (hu.of_le (by norm_num)) hwave hp (spatialPart p)
  obtain ⟨δ, hδ, L, hL, hbound⟩ :=
    exists_pos_uniform_partialDeriv_bound_of_semilinearWave (b := 1) (by norm_num)
    (hu.of_le (by norm_num)) hf (le_max_right (B₀ + B₁) 0)
    (fun p hp ↦ by simpa only [hinitial p hp] using hG (spatialPart p)) hnull
    (fun p hp ↦ hpde p hp.1)
  exact ⟨δ, hδ, L, hL, by simpa only [zero_add] using hbound⟩

/-- The initial characteristic bound applies after every nonnegative time slice. -/
theorem exists_pos_uniform_partialDeriv_bound_after_of_compact_slices {u : ℝ^2 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiff ℝ 3 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^1, waveOperator u (timeSpaceCons t x) +
      f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x))) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ p : ℝ^2, p 0 ∈ Icc a (a + δ) → ∀ i : Fin 2, ‖(∂[i] u) p‖ ≤ L := by
  let v : ℝ^2 → ℝ := fun p ↦ u (p + a • EuclideanSpace.single 0 1)
  have hv : ContDiff ℝ 3 v := hu.comp (contDiff_id.add contDiff_const)
  have hshift (t : ℝ) (x : ℝ^1) :
      timeSpaceCons t x + a • EuclideanSpace.single 0 1 = timeSpaceCons (t + a) x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hw (t : ℝ) (ht : 0 < t) (x : ℝ^1) :
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0 := by
    simpa only [v, waveOperator, partialDeriv_comp_add_right, hshift] using
      hwave (t + a) (add_pos_of_pos_of_nonneg ht ha) x
  have hc (t : ℝ) (ht : 0 ≤ t) :
      HasCompactSupport (fun x : ℝ^1 ↦ v (timeSpaceCons t x)) := by
    simpa only [v, hshift] using hs (t + a) (add_nonneg ht ha)
  obtain ⟨δ, hδ, L, hL, hb⟩ := exists_pos_uniform_partialDeriv_bound_of_compact_slices hv hf hw hc
  refine ⟨δ, hδ, L, hL, ?_⟩
  intro p hp i
  have he := hb (p - a • EuclideanSpace.single 0 1)
    (by change p 0 - a * 1 ∈ Icc 0 δ
        constructor <;> linarith [hp.1, hp.2]) i
  simpa only [v, partialDeriv_comp_add_right, sub_add_cancel] using he

/-- One-dimensional characteristics bound the first jet on a neighborhood
of every forward time. Reflection uses only the finite forward band. -/
theorem exists_uniform_partialDeriv_bound_near_of_compact_slices {u : ℝ^2 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiff ℝ 3 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^1, waveOperator u (timeSpaceCons t x) +
      f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x))) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ p : ℝ^2, p 0 ∈ Icc (max 0 (a - δ)) (a + δ) → ∀ i : Fin 2, ‖(∂[i] u) p‖ ≤
      L := by
  obtain ⟨δf, hδf, Lf, hLf, hbf⟩ :=
    exists_pos_uniform_partialDeriv_bound_after_of_compact_slices hu hf hwave hs ha
  by_cases hazero : a = 0
  · subst a
    refine ⟨δf, hδf, Lf, hLf, ?_⟩
    intro p hp i
    exact hbf p ⟨(le_max_left _ _).trans hp.1, hp.2⟩ i
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  let v : ℝ^2 → ℝ := fun p ↦ u (coordinateReflection 0 p)
  have hv : ContDiff ℝ 2 v := hu2.comp
    (coordinateReflectionLinearIsometryEquiv 0).toContinuousLinearEquiv.contDiff
  have hnorm (p : ℝ^2) (i : Fin 2) :
      ‖(∂[i] v) p‖ = ‖(∂[i] u) (coordinateReflection 0 p)‖ := by
    by_cases hi : i = 0
    · subst i
      rw [show (∂[0] v) p = -(∂[0] u) (coordinateReflection 0 p) from
        partialDeriv_comp_coordinateReflection_same 0 u p
          (hu2.differentiable (by norm_num)).differentiableAt, norm_neg]
    · exact congrArg norm (partialDeriv_comp_coordinateReflection_of_ne 0 i hi u p
        (hu2.differentiable (by norm_num)).differentiableAt)
  obtain ⟨G, hG⟩ := (hu.continuous.comp
    (contDiff_timeSpaceCons_spatial 1 a (m := 1)).continuous).bounded_above_of_compact_support
      (hs a ha)
  have hinit (p : ℝ^2) (hp : p 0 = -a) : (coordinateReflection 0 p) 0 = a := by
    simp [hp]
  have hg (p : ℝ^2) (hp : p 0 = -a) : ‖v p‖ ≤ G := by
    have he := hG (spatialPart (coordinateReflection 0 p))
    simp only [Function.comp_apply] at he
    rw [← hinit p hp, timeSpaceCons_spatialPart] at he
    exact he
  have hb (p : ℝ^2) (hp : p 0 = -a) (ε : ℝ) (hε : ε ^ 2 = 1) :
      ‖(∂[0] v) p + ε * (∂[1] v) p‖ ≤ Lf + Lf := by
    have hεnorm : ‖ε‖ = 1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε, abs_nonneg ε]
    have hi (i : Fin 2) : ‖(∂[i] v) p‖ ≤ Lf := by
      rw [hnorm]
      exact hbf _ (by rw [hinit p hp]; exact ⟨le_rfl, by linarith⟩) i
    calc
      _ ≤ ‖(∂[0] v) p‖ + ‖ε * (∂[1] v) p‖ := norm_add_le _ _
      _ = ‖(∂[0] v) p‖ + ‖(∂[1] v) p‖ := by rw [norm_mul, hεnorm, one_mul]
      _ ≤ Lf + Lf := add_le_add (hi 0) (hi 1)
  have hpde (p : ℝ^2) (hp : 0 ≤ p 0) : waveOperator u p + f (u p) = 0 := by
    simpa only [timeSpaceCons_spatialPart] using
      waveOperator_add_eq_zero_of_nonneg hf hu2 hwave hp (spatialPart p)
  have hw (p : ℝ^2) (hp : p 0 ∈ Icc (-a) 0) :
      waveOperator v p + f (v p) = 0 := by
    change waveOperator (fun q ↦ u (coordinateReflection 0 q)) p + _ = 0
    rw [waveOperator_comp_timeReflection hu2]
    exact hpde _ (by simpa using neg_nonneg.mpr hp.2)
  obtain ⟨δb, hδb, Lb, hLb, hbb⟩ :=
    exists_pos_uniform_partialDeriv_bound_of_semilinearWave (b := 0) (by linarith)
      hv hf (add_nonneg hLf hLf) hg hb hw
  refine ⟨min δf δb, lt_min hδf hδb, max Lf Lb, hLf.trans (le_max_left _ _), ?_⟩
  intro p hp i
  by_cases hpa : a ≤ p 0
  · exact (hbf p ⟨hpa, by linarith [hp.2, min_le_left δf δb]⟩ i).trans (le_max_left _ _)
  · have ht : (coordinateReflection 0 p) 0 ∈ Icc (-a) (-a + δb) := by
      have hlo := (le_max_right 0 (a - min δf δb)).trans hp.1
      simp only [coordinateReflection_apply_same]
      constructor <;> linarith [min_le_right δf δb]
    have he := hbb (coordinateReflection 0 p) ht i
    rw [hnorm] at he
    rw [coordinateReflection_involutive 0 p] at he
    exact he.trans (le_max_right Lf Lb)

end WaveEquation

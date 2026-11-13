/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSupport
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Uniqueness
public import PDE.FDeriv.Reflection.Coordinate
import PDE.FDeriv.Calculus

/-!
# Propagating compact slices before differentiating the energy

A locally Lipschitz reaction propagates compact Cauchy support in either time
direction. This transports the locally common support supplied by Baire
category and justifies energy integration under separate compact-slice
hypotheses. Ambient C² regularity is explicit in this module.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Compact Cauchy support propagates at speed one across a finite strip.
Only local Lipschitz regularity of the reaction is used. -/
theorem eq_zero_of_norm_gt_cauchySupport [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {a t R : ℝ}
    (hf : LocallyLipschitz f) (hfzero : f 0 = 0) (hu : ContDiff ℝ 2 u) (hat : a ≤ t)
    (hwave : ∀ s ∈ Ico a t, ∀ y, waveOperator u (timeSpaceCons s y) = -f (u (timeSpaceCons s y)))
    (hpos : ∀ y : ℝ^n, R < ‖y‖ → u (timeSpaceCons a y) = 0)
    (hvel : ∀ y : ℝ^n, R < ‖y‖ → (∂[0] u) (timeSpaceCons a y) = 0) {x : ℝ^n}
    (hx : R + (t - a) < ‖x‖) :
    u (timeSpaceCons t x) = 0 := by
  have hbase (y : ℝ^n) (hy : y ∈ Metric.closedBall x (t - a)) : R < ‖y‖ := by
    have hy' : ‖y - x‖ ≤ t - a := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have hn := norm_le_norm_add_norm_sub y x
    linarith
  exact SmallData.Classical.eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz
    hf hu contDiff_const x (fun s hs y _ ↦ hwave s hs y)
    (fun _ _ _ _ ↦ by simp [waveOperator, hfzero]) (fun y hy ↦ hpos y (hbase y hy))
    (fun y hy ↦ by simpa using hvel y (hbase y hy))
    t ⟨hat, le_rfl⟩ x (by simp)

/-- Time reflection commutes with the wave operator. -/
theorem waveOperator_comp_timeReflection {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (p : ℝ^(n + 1)) :
    waveOperator (fun q ↦ u (coordinateReflection 0 q)) p =
      waveOperator u (coordinateReflection 0 p) := by
  simp only [waveOperator, secondPartialDeriv_comp_coordinateReflection 0 _ u _ hu]

/-- Compact Cauchy support at any time controls the whole finite lifespan slab,
including earlier times. This is a consequence of uniqueness in both time directions. -/
theorem eq_zero_on_Icc_of_cauchySupport [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {b a T R : ℝ}
    (hf : LocallyLipschitz f) (hfzero : f 0 = 0) (hu : ContDiff ℝ 2 u) (ha : a ∈ Icc b T)
    (hwave : ∀ s ∈ Icc b T, ∀ y, waveOperator u (timeSpaceCons s y) = -f (u (timeSpaceCons s y)))
    (hpos : ∀ y : ℝ^n, R < ‖y‖ → u (timeSpaceCons a y) = 0)
    (hvel : ∀ y : ℝ^n, R < ‖y‖ → (∂[0] u) (timeSpaceCons a y) = 0) :
    ∀ t ∈ Icc b T, ∀ x : ℝ^n, R + (T - b) < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  have hreflect (s : ℝ) (y : ℝ^n) :
      coordinateReflection 0 (timeSpaceCons s y) = timeSpaceCons (-s) y := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  intro t ht x hx
  by_cases hat : a ≤ t
  · exact eq_zero_of_norm_gt_cauchySupport hf hfzero hu hat
      (fun s hs y ↦ hwave s ⟨ha.1.trans hs.1, hs.2.le.trans ht.2⟩ y)
      hpos hvel (by linarith [ha.1, ht.2])
  · let v : ℝ^(n + 1) → ℝ := fun p ↦ u (coordinateReflection 0 p)
    have hv : ContDiff ℝ 2 v := hu.comp
      (coordinateReflectionLinearIsometryEquiv 0).toContinuousLinearEquiv.contDiff
    have he := eq_zero_of_norm_gt_cauchySupport (u := v) (a := -a) (t := -t) (R := R)
      hf hfzero hv (by linarith) (fun s hs y ↦ ?_) (fun y hy ↦ ?_)
      (fun y hy ↦ ?_) (x := x) (by linarith [ht.1, ha.2])
    · simpa only [v, hreflect, neg_neg] using he
    · change waveOperator (fun p ↦ u (coordinateReflection 0 p)) (timeSpaceCons s y) = _
      dsimp only [v]
      rw [waveOperator_comp_timeReflection hu, hreflect]
      exact hwave (-s) ⟨by linarith [ht.1, hs.2], by linarith [ha.2, hs.1]⟩ y
    · simpa only [v, hreflect, neg_neg] using hpos y hy
    · change (∂[0] (fun p ↦ u (coordinateReflection 0 p))) (timeSpaceCons (-a) y) = 0
      rw [partialDeriv_comp_coordinateReflection_same 0 u _
        (hu.differentiable (by norm_num)).differentiableAt, hreflect, neg_neg, hvel y hy, neg_zero]

/-- Separate compact spatial slices of a smooth semilinear wave with a locally Lipschitz
reaction give common compact support on every finite forward slab. The reaction at zero is derived
from the PDE on a Baire-good exterior region, not assumed separately. -/
theorem exists_uniform_support_on_Icc_of_compact_slices [Fact (0 < n)] {f : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : LocallyLipschitz f) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 ≤ t → ∀ x, waveOperator u (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, R < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  let I := Ioo (0 : ℝ) (T + 1)
  have hI : IsOpen I := isOpen_Ioo
  let : BaireSpace I := hI.baireSpace
  let : Nonempty I := ⟨⟨(T + 1) / 2, by constructor <;> linarith⟩⟩
  have hc (x : ℝ^n) : Continuous (fun t : I ↦ u (timeSpaceCons t x)) :=
    hu.continuous.comp ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_subtype_val.prodMk continuous_const))
  obtain ⟨a, R, hR⟩ :=
    (dense_locally_uniform_spatial_support hc (fun t ↦ hs t t.property.1.le)).nonempty
  have hR' := (eventually_nhds_subtype_iff I a
    (fun s ↦ ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0)).mp hR
  rw [hI.nhdsWithin_eq a.property] at hR'
  change ∀ᶠ s : ℝ in 𝓝 (a : ℝ), ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0 at hR'
  have hgerm (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) :
      u =ᶠ[𝓝 (timeSpaceCons a x)] fun _ ↦ 0 := by
    have hproj : Tendsto (fun p : ℝ^(n + 1) ↦ p 0) (𝓝 (timeSpaceCons (a : ℝ) x)) (𝓝 (a : ℝ)) :=
      (show Continuous (fun p : ℝ^(n + 1) ↦ p 0) from
        (EuclideanSpace.proj 0).continuous).continuousAt
    have ht : ∀ᶠ p : ℝ^(n + 1) in 𝓝 (timeSpaceCons a x),
        ∀ y : ℝ^n, (R : ℝ) < ‖y‖ → u (timeSpaceCons (p 0) y) = 0 :=
      hproj.eventually (p := fun s ↦ ∀ y : ℝ^n, (R : ℝ) < ‖y‖ → u (timeSpaceCons s y) = 0) hR'
    have hx' : ∀ᶠ p in 𝓝 (timeSpaceCons a x), (R : ℝ) < ‖spatialPart p‖ :=
      ((spatialPartCLM n).continuous.norm.continuousAt).eventually (lt_mem_nhds hx)
    filter_upwards [ht, hx'] with p hp hpx
    simpa only [timeSpaceCons_spatialPart] using hp (spatialPart p) hpx
  have hpos (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) : u (timeSpaceCons a x) = 0 := (hgerm x hx).eq_of_nhds
  have hvel (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) : (∂[0] u) (timeSpaceCons a x) = 0 := by
    rw [PDE.partialDeriv_congr_nhds 0 (hgerm x hx)]
    exact PDE.partialDeriv_const 0
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ (ℝ^n) (R : ℝ)
  have hfzero : f 0 = 0 := by
    have he := hwave a a.property.1.le x
    rw [waveOperator_congr_nhds (hgerm x hx), waveOperator_const, hpos x hx] at he
    exact neg_eq_zero.mp he.symm
  refine ⟨(R : ℝ) + (T + 1), by positivity, fun t ht x hx ↦ ?_⟩
  exact eq_zero_on_Icc_of_cauchySupport hf hfzero hu ⟨a.property.1.le, a.property.2.le⟩
    (fun s hsI y ↦ hwave s hsI.1 y) hpos hvel t ⟨ht.1, by linarith [ht.2]⟩ x
    (by simpa only [sub_zero] using hx)

end WaveEquation

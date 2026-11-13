/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.Pointwise
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.Solution
public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import PDE.FDeriv.Calculus

/-!
# The coordinate PDE and energy correspondence

The constructed Sobolev representatives define classical spacetime fields.
Their observed time derivatives identify the coordinate wave operator.
The displacement and velocity represent the conserved energy evolution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Common WaveEquation
open scoped Sobolev Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

private theorem waveOperator_eq_acceleration_forward {u : ℝ^4 → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (v a : ℝ → ℝ^3 → ℝ)
    (hq : ∀ t > 0, ∀ x, HasDerivAt (fun s ↦ u (timeSpaceCons s x)) (v t x) t)
    (hv : ∀ t > 0, ∀ x, HasDerivAt (fun s ↦ v s x) (a t x) t) {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    waveOperator u (timeSpaceCons t x) =
      a t x - PDE.laplacian (fun y ↦ u (timeSpaceCons t y)) x := by
  have hreg (s : ℝ) (hs : 0 < s) : ContDiffAt ℝ 2 u (timeSpaceCons s x) :=
    hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
      (by simpa using hs))
  have he : (fun s ↦ (∂[0] u) (timeSpaceCons s x)) =ᶠ[𝓝 t] fun s ↦ v s x := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using (hasDerivAt_timeSpaceCons u s x
      ((hreg s hs).differentiableAt (by norm_num))).unique (hq s hs x)
  have hsecond := (hv t ht x).congr_of_eventuallyEq he
  have hp := hasDerivAt_timeSpaceCons (∂[0] u) t x
    ((contDiffAt_partialDeriv 1 (hreg t ht) 0).differentiableAt one_ne_zero)
  rw [waveOperator, ← laplacian_timeSlice_of_contDiffAt u t x (hreg t ht), hp.unique hsecond]

/-- Every H⁵ × H⁴ datum has a forward classical cubic wave representing
the constructed global energy solution. -/
theorem exists_global_classical_cubic (x : W^{5,2}(ℝ^3) × W^{4,2}(ℝ^3)) :
    ∃ u v : C(ℝ^4, ℝ),
      IsClassicalSolution
        (classicalRepresentativeCLM (by norm_num : (3 : ℝ) < 2 * ((5 : ℝ) - 1)) x.1)
        (classicalRepresentativeCLM (by norm_num : (3 : ℝ) < 2 * ((4 : ℝ) - 1)) x.2) u ∧
      (∀ t : ℝ, 0 ≤ t →
        (fun y ↦ u (timeSpaceCons t y)) =ᵐ[volume]
          baseRepresentative (cubicNonlinearity.globalSolution (energyProjectionCLM 4 x) t).1 ∧
        (fun y ↦ v (timeSpaceCons t y)) =ᵐ[volume]
          (cubicNonlinearity.globalSolution (energyProjectionCLM 4 x) t).2 ∧
        ∀ y, HasDerivWithinAt (fun s ↦ u (timeSpaceCons s y))
          (v (timeSpaceCons t y)) (Ici 0) t) := by
  obtain ⟨q, w, a, hq₂, hq₁, hzero, hfield⟩ := exists_global_pointwise_cubic
    (k := 3) (by norm_num) (by norm_num) (by norm_num) x
  let J : ℝ^4 → ℝ × ℝ^3 := fun p ↦ (p 0, spatialPart p)
  have hJ : ContDiff ℝ 2 J := (EuclideanSpace.proj 0).contDiff.prodMk (spatialPartCLM 3).contDiff
  let u : C(ℝ^4, ℝ) := ⟨q ∘ J, q.continuous.comp hJ.continuous⟩
  let v : C(ℝ^4, ℝ) := ⟨w ∘ J, w.continuous.comp hJ.continuous⟩
  have hut (t : ℝ) (y : ℝ^3) : u (timeSpaceCons t y) = q (t, y) := by simp [u, J]
  have hvt (t : ℝ) (y : ℝ^3) : v (timeSpaceCons t y) = w (t, y) := by simp [v, J]
  have hreg : ContDiffOn ℝ 2 u {p | 0 < p 0} := hq₂.comp hJ.contDiffOn (fun p hp ↦ ⟨hp, mem_univ _⟩)
  have hfirst (t : ℝ) (ht : 0 ≤ t) (y : ℝ^3) :
      HasDerivWithinAt (fun s ↦ u (timeSpaceCons s y)) (w (t, y)) (Ici 0) t := by
    simpa only [hut] using ((hfield t ht).2.2.2 y).1
  refine ⟨u, v, ⟨hreg, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hq₁.comp (hJ.of_le (by norm_num)).contDiffOn (fun p hp ↦ ⟨hp, mem_univ _⟩)
  · intro p hp
    have he := waveOperator_eq_acceleration_forward hreg (fun t y ↦ w (t, y)) (fun t y ↦ a (t, y))
      (fun t ht y ↦ (hfirst t ht.le y).hasDerivAt (Ici_mem_nhds ht))
      (fun t ht y ↦ ((hfield t ht.le).2.2.2 y).2.1.hasDerivAt (Ici_mem_nhds ht)) hp (spatialPart p)
    rw [timeSpaceCons_spatialPart] at he
    rw [he]
    simp only [hut]
    have hslice := ((hfield (p 0) hp.le).2.2.1).contDiffAt (x := spatialPart p)
    rw [hslice.coordinate_laplacian_eq_laplacian]
    exact ((hfield (p 0) hp.le).2.2.2 (spatialPart p)).2.2
  · intro y
    rw [hut]
    exact (hzero y).1
  · intro y
    rw [← (hzero y).2]
    exact hfirst 0 le_rfl y
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hut] using (hfield t ht).1
    · simpa only [hvt] using (hfield t ht).2.1
    · intro y
      simpa only [hvt] using hfirst t ht y

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

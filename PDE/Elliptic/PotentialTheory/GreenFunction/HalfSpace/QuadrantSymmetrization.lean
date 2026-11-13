/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BiotSavartKernel

/-!
# Folding planar integrals onto the quadrant

The two coordinate reflections `R₀ y = (-y₀, y₁)` and `R₁ y = (y₀, -y₁)` preserve Lebesgue
measure and the coordinate axes are null, so every integrable `f` satisfies

`∫_{ℝ²} f = ∫_{ℝ²₊₊} (f(y) + f(R₀ y) + f(R₁ y) + f(-y)) dy`

over the open quadrant `ℝ²₊₊ = {y₀ > 0, y₁ > 0}`. For a density `W` odd in both coordinates, as
the odd extension of a vorticity odd in `y₀` is, this gives
`∫ k(x - y) W(y) dy = ∫_{ℝ²₊₊} kₛ(x, y) W(y) dy` with the symmetrized kernel (3.2) of Chen and
Hou I, and for an integrand even in both coordinates the factor `4` of their (5.67).

## Main definitions

* `quadrant`: the open quadrant `ℝ²₊₊ = {y₀ > 0, y₁ > 0}`.

## Main results

* `setIntegral_eq_setIntegral_pos_add_reflect`: for a measurable set `S` invariant under `Rₖ`,
  `∫_S f = ∫_{S ∩ {yₖ > 0}} (f + f ∘ Rₖ)`.
* `setIntegral_eq_setIntegral_inter_quadrant`: for a measurable set `S` invariant under `R₀`
  and `R₁`, `∫_S f = ∫_{S ∩ ℝ²₊₊} (f(y) + f(R₀ y) + f(R₁ y) + f(-y)) dy`.
* `integral_eq_setIntegral_quadrant`: the displayed quadrant fold, for integrable `f`.
* `integral_mul_eq_setIntegral_quadrant_symmetrizedKernel`: if `W` is odd in both coordinates,
  then `∫ k(x - y) W(y) dy = ∫_{ℝ²₊₊} kₛ(x, y) W(y) dy`.
* `integral_eq_four_mul_setIntegral_quadrant`: if `h` is even in both coordinates,
  `∫ h = 4 ∫_{ℝ²₊₊} h`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.2), and
  Section 5.6, (5.67).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace GreenFunction

local notation "𝐑" => PDE.Common.coordinateReflection

/-- The open quadrant `ℝ²₊₊ = {y₀ > 0, y₁ > 0}`. -/
def quadrant : Set (ℝ^2) := {y | 0 < y 0 ∧ 0 < y 1}

/-- The open quadrant `ℝ²₊₊` is measurable. -/
theorem measurableSet_quadrant : MeasurableSet quadrant := by
  have h0 : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have h1 : Measurable fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  exact (measurableSet_lt measurable_const h0).inter (measurableSet_lt measurable_const h1)

/-- Points of the open quadrant are nonzero. -/
theorem ne_zero_of_mem_quadrant {y : ℝ^2} (hy : y ∈ quadrant) : y ≠ 0 := by
  rintro rfl
  have := hy.1
  simp at this

/-- A coordinate reflection preserves Lebesgue measure: `∫_{Rₖ⁻¹ S} g ∘ Rₖ = ∫_S g`. -/
theorem setIntegral_preimage_coordinateReflection (k : Fin 2) (S : Set (ℝ^2)) (g : ℝ^2 → ℝ) :
    ∫ y in 𝐑 k ⁻¹' S, g (𝐑 k y) = ∫ y in S, g y :=
  (PDE.Common.measurePreserving_coordinateReflection k).setIntegral_preimage_emb
    (PDE.Common.coordinateReflectionLinearIsometryEquiv k).toMeasurableEquiv.measurableEmbedding
    g S

/-- The coordinate axes are Lebesgue null. -/
theorem volume_coordinate_eq_zero (k : Fin 2) : volume {y : ℝ^2 | y k = 0} = 0 := by
  have hset : {y : ℝ^2 | y k = 0} =
      ((LinearMap.ker (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).toLinearMap : Submodule ℝ (ℝ^2)) :
        Set (ℝ^2)) := by
    ext y; simp
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : EuclideanSpace.single k (1 : ℝ) ∈
      LinearMap.ker (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).toLinearMap := by
    rw [h]; exact Submodule.mem_top
  simp at hmem

/-- **Half fold.** For a measurable set `S` invariant under the reflection `Rₖ` of the
coordinate `k`, `∫_S f = ∫_{S ∩ {yₖ > 0}} (f + f ∘ Rₖ)`. -/
theorem setIntegral_eq_setIntegral_pos_add_reflect (k : Fin 2) {S : Set (ℝ^2)}
    (hS : MeasurableSet S) (hSinv : ∀ y, 𝐑 k y ∈ S ↔ y ∈ S) {f : ℝ^2 → ℝ}
    (hf : IntegrableOn f S) :
    ∫ y in S, f y = ∫ y in S ∩ {y | 0 < y k}, (f y + f (𝐑 k y)) := by
  have hk : Measurable fun y : ℝ^2 ↦ y k := (EuclideanSpace.proj k).continuous.measurable
  set P := S ∩ {y : ℝ^2 | 0 < y k}
  set N := S ∩ {y : ℝ^2 | y k < 0}
  have hP : MeasurableSet P := hS.inter (measurableSet_lt measurable_const hk)
  have hN : MeasurableSet N := hS.inter (measurableSet_lt hk measurable_const)
  have hcov : S =ᵐ[volume] (P ∪ N : Set (ℝ^2)) := by
    have hnull : volume (S \ (P ∪ N)) = 0 := by
      refine measure_mono_null (fun y hy ↦ ?_) (volume_coordinate_eq_zero k)
      simp only [mem_sdiff, mem_union, mem_inter_iff, mem_ofPred_eq, P, N] at hy
      simp only [mem_ofPred_eq]
      rcases lt_trichotomy (y k) 0 with h | h | h
      · exact absurd (Or.inr ⟨hy.1, h⟩) hy.2
      · exact h
      · exact absurd (Or.inl ⟨hy.1, h⟩) hy.2
    refine (ae_eq_set.mpr ⟨hnull, ?_⟩)
    have : (P ∪ N) \ S = ∅ := by
      ext y; simp only [mem_sdiff, mem_union, mem_inter_iff, P, N, mem_empty_iff_false,
        iff_false, not_and, not_not]
      rintro (h | h) <;> exact h.1
    rw [this, measure_empty]
  have hdisj : Disjoint P N := Set.disjoint_left.mpr fun y hy hy' ↦ by
    have h1 : 0 < y k := hy.2
    have h2 : y k < 0 := hy'.2
    linarith
  have hpre : 𝐑 k ⁻¹' N = P := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hSinv, N, P,
      PDE.Common.coordinateReflection_apply_same, neg_lt_zero]
  have hmp := PDE.Common.measurePreserving_coordinateReflection k
  have hemb : MeasurableEmbedding (𝐑 k) :=
    (PDE.Common.coordinateReflectionLinearIsometryEquiv k).toMeasurableEquiv.measurableEmbedding
  have hNval : ∫ y in N, f y = ∫ y in P, f (𝐑 k y) := by
    rw [← hpre, hmp.setIntegral_preimage_emb hemb f N]
  have hfP : IntegrableOn f P := hf.mono_set inter_subset_left
  have hfN : IntegrableOn f N := hf.mono_set inter_subset_left
  have hfRP : IntegrableOn (fun y ↦ f (𝐑 k y)) P := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hemb).mpr hfN
  rw [setIntegral_congr_set hcov, setIntegral_union hdisj hN hfP hfN, hNval,
    ← integral_add hfP hfRP]

/-- The reflections of the two coordinates commute: `R₀ (R₁ y) = R₁ (R₀ y)`. -/
theorem coordinateReflection_comm (y : ℝ^2) : 𝐑 0 (𝐑 1 y) = 𝐑 1 (𝐑 0 y) := by
  ext k
  fin_cases k <;> simp [PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne]

/-- The two coordinate reflections compose to the point reflection: `R₀ (R₁ y) = -y`. -/
theorem coordinateReflection_zero_one (y : ℝ^2) : 𝐑 0 (𝐑 1 y) = -y := by
  ext k
  fin_cases k <;> simp [PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne]

/-- **Quadrant fold on an invariant set.** If `S` is invariant under both coordinate
reflections, `∫_S f = ∫_{S ∩ ℝ²₊₊} (f(y) + f(R₀ y) + f(R₁ y) + f(-y)) dy`. -/
theorem setIntegral_eq_setIntegral_inter_quadrant {S : Set (ℝ^2)} (hS : MeasurableSet S)
    (hS₀ : ∀ y, 𝐑 0 y ∈ S ↔ y ∈ S) (hS₁ : ∀ y, 𝐑 1 y ∈ S ↔ y ∈ S) {f : ℝ^2 → ℝ}
    (hf : IntegrableOn f S) :
    ∫ y in S, f y = ∫ y in S ∩ quadrant, (f y + f (𝐑 0 y) + f (𝐑 1 y) + f (-y)) := by
  rw [setIntegral_eq_setIntegral_pos_add_reflect 1 hS hS₁ hf]
  have h1m : Measurable fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  have hS' : MeasurableSet (S ∩ {y : ℝ^2 | 0 < y 1}) :=
    hS.inter (measurableSet_lt measurable_const h1m)
  have hinv : ∀ y, 𝐑 0 y ∈ S ∩ {y : ℝ^2 | 0 < y 1} ↔ y ∈ S ∩ {y : ℝ^2 | 0 < y 1} := by
    intro y
    simp only [mem_inter_iff, mem_ofPred_eq, hS₀,
      PDE.Common.coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by decide)]
  have hmp := PDE.Common.measurePreserving_coordinateReflection (n := 2) 1
  have hemb := (PDE.Common.coordinateReflectionLinearIsometryEquiv (n := 2) 1).toMeasurableEquiv
    |>.measurableEmbedding
  have hfR : IntegrableOn (fun y ↦ f (𝐑 1 y)) S := by
    have : 𝐑 1 ⁻¹' S = S := by ext y; exact hS₁ y
    rw [← this]
    exact (hmp.integrableOn_comp_preimage hemb).mpr hf
  have hg : IntegrableOn (fun y ↦ f y + f (𝐑 1 y)) (S ∩ {y : ℝ^2 | 0 < y 1}) :=
    (hf.add hfR).mono_set inter_subset_left
  rw [setIntegral_eq_setIntegral_pos_add_reflect 0 hS' hinv hg]
  have hset : S ∩ {y : ℝ^2 | 0 < y 1} ∩ {y | 0 < y 0} = S ∩ quadrant := by
    ext y; simp only [mem_inter_iff, mem_ofPred_eq, quadrant]; tauto
  rw [hset]
  refine setIntegral_congr_fun (hS.inter measurableSet_quadrant) fun y _ ↦ ?_
  rw [← coordinateReflection_comm, coordinateReflection_zero_one]
  ring

/-- **Quadrant fold.** `∫_{ℝ²} f = ∫_{ℝ²₊₊} (f(y) + f(R₀ y) + f(R₁ y) + f(-y)) dy` for
integrable `f`. -/
theorem integral_eq_setIntegral_quadrant {f : ℝ^2 → ℝ} (hf : Integrable f) :
    ∫ y, f y = ∫ y in quadrant, (f y + f (𝐑 0 y) + f (𝐑 1 y) + f (-y)) := by
  simpa only [Measure.restrict_univ, univ_inter] using
    setIntegral_eq_setIntegral_inter_quadrant MeasurableSet.univ (by simp) (by simp)
      hf.integrableOn

/-- **Odd-odd densities.** If `W` is odd in both coordinates, then
`∫ k(x - y) W(y) dy = ∫_{ℝ²₊₊} kₛ(x, y) W(y) dy`. -/
theorem integral_mul_eq_setIntegral_quadrant_symmetrizedKernel {k W : ℝ^2 → ℝ} (x : ℝ^2)
    (hW₀ : ∀ y, W (𝐑 0 y) = -W y) (hW₁ : ∀ y, W (𝐑 1 y) = -W y)
    (hint : Integrable fun y ↦ k (x - y) * W y) :
    ∫ y, k (x - y) * W y = ∫ y in quadrant, symmetrizedKernel k x y * W y := by
  rw [integral_eq_setIntegral_quadrant hint]
  refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
  have hneg : W (-y) = W y := by
    rw [← coordinateReflection_zero_one, hW₀, hW₁, neg_neg]
  simp only [symmetrizedKernel, hW₀, hW₁, hneg, sub_neg_eq_add]
  ring

/-- **Even-even integrands.** If `h` is even in both coordinates, `∫ h = 4 ∫_{ℝ²₊₊} h`. -/
theorem integral_eq_four_mul_setIntegral_quadrant {h : ℝ^2 → ℝ} (hh : Integrable h)
    (h₀ : ∀ y, h (𝐑 0 y) = h y) (h₁ : ∀ y, h (𝐑 1 y) = h y) :
    ∫ y, h y = 4 * ∫ y in quadrant, h y := by
  rw [integral_eq_setIntegral_quadrant hh, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
  have hneg : h (-y) = h y := by
    rw [← coordinateReflection_zero_one, h₀, h₁]
  simp only [h₀, h₁, hneg]
  ring

end GreenFunction

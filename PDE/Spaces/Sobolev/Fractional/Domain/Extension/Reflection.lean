/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Extension.ReflectionGraph

/-!
# Bounded reflection extension of intrinsic Gagliardo spaces

Even reflection is a bounded linear right inverse to restriction from the whole
space to the upper half-space. For finite `p ≥ 1` its norm is at most `4 ^ (1 / p.toReal)`;
the infinity endpoint is contractive. So restriction to the half-space is surjective.

There is one construction on the Gagliardo graph, from `ReflectionGraph`. The sole order
condition is `0 ≤ n / p.toReal + s`; outside `0 < s < 1` the statements concern the raw
graph, without identifying it with other notions of fractional regularity. The scalar and
quadratic specializations are in `ReflectionQuadratic`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Extension

open SobolevSpace.HalfSpace GagliardoSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_toLp_evenReflection_top_le (hs : 0 ≤ (n : ℝ) / ∞.toReal + s)
    (u : W^{s,∞}(ℝ^n₊; F)) :
    ‖toLp n s Set.univ (evenReflection hs u)‖ ≤ ‖toLp n s ℝ^n₊ u‖ := by
  have he : (toLp n s Set.univ (evenReflection hs u) : ℝ^n → F)
      =ᵐ[volume.restrict Set.univ] (toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n := by
    simpa only [Measure.restrict_univ] using toLp_evenReflection_apply_ae hs u
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  rw [eLpNorm_congr_ae he, Measure.restrict_univ,
    eLpNorm_comp_measurePreserving ((Lp.aestronglyMeasurable _).smul_measure 2)
      (measurePreserving_foldUpper n),
    eLpNorm_smul_measure_of_ne_zero (by norm_num)]
  simp

omit [NormedSpace ℝ F] in
private theorem eLpNorm_top_comp_foldUpper_prod (f : ℝ^n × ℝ^n → F)
    (hf : AEStronglyMeasurable f (gagliardoProductMeasure n ℝ^n₊)) :
    eLpNorm (f ∘ Prod.map (foldUpper n) (foldUpper n)) ∞ (volume.prod volume) =
      eLpNorm f ∞ (gagliardoProductMeasure n ℝ^n₊) := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure 4)
    (measurePreserving_foldUpper_prod n),
    eLpNorm_smul_measure_of_ne_zero (by norm_num)]
  simp

private theorem norm_differenceQuotient_evenReflection_top_le
    (hs : 0 ≤ (n : ℝ) / ∞.toReal + s)
    (u : W^{s,∞}(ℝ^n₊; F)) :
    ‖differenceQuotient n s Set.univ (evenReflection hs u)‖ ≤
      ‖differenceQuotient n s ℝ^n₊ u‖ := by
  have he : (toLp n s Set.univ (evenReflection hs u) : ℝ^n → F)
      =ᵐ[volume.restrict Set.univ] (toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n := by
    simpa only [Measure.restrict_univ] using toLp_evenReflection_apply_ae hs u
  have hdiff := (differenceQuotient_apply_ae (evenReflection hs u)).trans
    (diffQuot_congr_ae he)
  have hsource := aestronglyMeasurable_diffQuot (s := s) (p := ∞)
    (Lp.aestronglyMeasurable (toLp n s ℝ^n₊ u))
  have hfold : AEStronglyMeasurable
      ((toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n) (volume.restrict Set.univ) := by
    simpa only [Measure.restrict_univ] using
      (memLp_comp_foldUpper (Lp.memLp (toLp n s ℝ^n₊ u))).aestronglyMeasurable
  have htarget := aestronglyMeasurable_diffQuot (s := s) (p := ∞) hfold
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  rw [eLpNorm_congr_ae hdiff,
    eLpNorm_congr_ae (differenceQuotient_apply_ae u)]
  simp only [gagliardoProductMeasure, Measure.restrict_univ] at htarget ⊢
  calc
    _ ≤ eLpNorm (diffQuot n s (toLp n s ℝ^n₊ u) (p := ∞) ∘
        Prod.map (foldUpper n) (foldUpper n)) ∞ (volume.prod volume) :=
      eLpNorm_mono_ae htarget (Filter.Eventually.of_forall
        (norm_diffQuot_comp_foldUpper_le hs (toLp n s ℝ^n₊ u)))
    _ = _ := eLpNorm_top_comp_foldUpper_prod _ hsource

private theorem norm_evenReflection_top_le (hs : 0 ≤ (n : ℝ) / ∞.toReal + s)
    (u : W^{s,∞}(ℝ^n₊; F)) :
    ‖evenReflection hs u‖ ≤ ‖u‖ := by
  rw [norm_top, norm_top]
  exact max_le_max (norm_toLp_evenReflection_top_le hs u)
    (norm_differenceQuotient_evenReflection_top_le hs u)

private theorem norm_evenReflection_le_bound (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    ‖evenReflection hs u‖ ≤ (4 : ℝ) ^ (1 / p.toReal) * ‖u‖ := by
  by_cases hp : p = ∞
  · subst p
    simpa using norm_evenReflection_top_le hs u
  · exact norm_evenReflection_le_rpow hp hs u

private theorem comp_foldUpper_congr_ae {E : Type*} {f g : ℝ^n → E}
    (h : f =ᵐ[volume.restrict ℝ^n₊] g) :
    f ∘ foldUpper n =ᵐ[volume] g ∘ foldUpper n :=
  (measurePreserving_foldUpper n).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure h (2 : ℝ≥0∞))

/-- Even reflection is additive on the graph space. -/
@[simp] theorem evenReflection_add (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u v : W^{s,p}(ℝ^n₊; F)) :
    evenReflection hs (u + v) = evenReflection hs u + evenReflection hs v := by
  apply toLp_injective
  rw [map_add]
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have hsource := comp_foldUpper_congr_ae
    (Lp.coeFn_add (toLp n s ℝ^n₊ u) (toLp n s ℝ^n₊ v))
  have htarget := Lp.coeFn_add (toLp n s Set.univ (evenReflection hs u))
    (toLp n s Set.univ (evenReflection hs v))
  simp only [Measure.restrict_univ] at htarget
  have hsum := toLp_evenReflection_apply_ae hs (u + v)
  simp only [map_add] at hsum
  filter_upwards [hsum, toLp_evenReflection_apply_ae hs u,
    toLp_evenReflection_apply_ae hs v, hsource, htarget] with x hsum hu hv hs ht
  exact hsum.trans (hs.trans (by
    simpa only [Function.comp_apply, Pi.add_apply, hu, hv] using ht.symm))

/-- Even reflection commutes with real scalar multiplication. -/
@[simp] theorem evenReflection_smul (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (c : ℝ) (u : W^{s,p}(ℝ^n₊; F)) :
    evenReflection hs (c • u) = c • evenReflection hs u := by
  apply toLp_injective
  rw [map_smul]
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have hsource := comp_foldUpper_congr_ae (Lp.coeFn_smul c (toLp n s ℝ^n₊ u))
  have htarget := Lp.coeFn_smul c (toLp n s Set.univ (evenReflection hs u))
  simp only [Measure.restrict_univ] at htarget
  have hsmul := toLp_evenReflection_apply_ae hs (c • u)
  simp only [map_smul] at hsmul
  filter_upwards [hsmul, toLp_evenReflection_apply_ae hs u, hsource, htarget]
    with x hsmul hu hs ht
  exact hsmul.trans (hs.trans (by
    simpa only [Function.comp_apply, Pi.smul_apply, hu] using ht.symm))

/-- Bounded even reflection from the intrinsic half-space Gagliardo space.
At finite p its norm is at most `4 ^ (1 / p.toReal)`; the infinity endpoint is contractive. -/
def evenReflectionCLM (hs : 0 ≤ (n : ℝ) / p.toReal + s) :
    W^{s,p}(ℝ^n₊; F) →L[ℝ]
      W^{s,p}(ℝ^n; F) :=
  LinearMap.mkContinuous
    { toFun := evenReflection hs
      map_add' := evenReflection_add hs
      map_smul' := evenReflection_smul hs }
    ((4 : ℝ) ^ (1 / p.toReal)) (by
      intro u
      exact norm_evenReflection_le_bound hs u)

/-- The bounded operator acts by the constructed even reflection. -/
theorem evenReflectionCLM_apply (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    evenReflectionCLM hs u = evenReflection hs u :=
  rfl

/-- The bounded operator's representative is even reflection almost everywhere. -/
theorem toLp_evenReflectionCLM_apply_ae (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    (toLp n s Set.univ (evenReflectionCLM hs u) : ℝ^n → F) =ᵐ[volume]
      (toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n :=
  toLp_evenReflection_apply_ae hs u

/-- The operator norm is at most `4 ^ (1 / p.toReal)` at every finite exponent. -/
theorem norm_evenReflectionCLM_le_rpow (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) :
    ‖evenReflectionCLM (F := F) hs‖ ≤ (4 : ℝ) ^ (1 / p.toReal) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (by norm_num) _)
    (norm_evenReflection_le_rpow hp hs)

/-- Restricting the reflected element to the half-space recovers the input. -/
@[simp] theorem restrict_evenReflectionCLM (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    restrictCLM (subset_univ ℝ^n₊) (evenReflectionCLM hs u) = u := by
  apply toLp_injective
  apply Lp.ext
  have hr := toLp_restrictCLM_apply_ae (subset_univ ℝ^n₊) (evenReflection hs u)
  have he := ae_restrict_of_ae (s := ℝ^n₊) (toLp_evenReflection_apply_ae hs u)
  filter_upwards [hr, he, ae_restrict_mem (measurableSet_upper n)] with x hx he hmem
  exact hx.trans (he.trans (congrArg (toLp n s ℝ^n₊ u)
    (foldUpper_of_mem_upper n hmem)))

/-- Even reflection is a bounded linear right inverse to intrinsic restriction. -/
theorem restrictCLM_comp_evenReflectionCLM (hs : 0 ≤ (n : ℝ) / p.toReal + s) :
    (restrictCLM (subset_univ ℝ^n₊)).comp (evenReflectionCLM (F := F) hs) =
      ContinuousLinearMap.id ℝ (W^{s,p}(ℝ^n₊; F)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact restrict_evenReflectionCLM hs u

/-- Every intrinsic half-space element is a restriction of a whole-space element. -/
theorem surjective_restrictCLM_halfSpace (hs : 0 ≤ (n : ℝ) / p.toReal + s) :
    Function.Surjective
      (restrictCLM (n := n) (s := s) (p := p) (F := F) (subset_univ ℝ^n₊)) :=
  fun u ↦ ⟨evenReflectionCLM hs u, restrict_evenReflectionCLM hs u⟩

end SobolevSpace.Fractional.Extension

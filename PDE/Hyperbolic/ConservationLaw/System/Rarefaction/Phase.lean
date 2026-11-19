/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.IntegralCurve
public import PDE.Hyperbolic.ConservationLaw.System.SimpleWave
public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Measure
public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm
import PDE.FDeriv.Calculus

/-!
# The original-parameter phase of a rarefaction

Clipping the similarity coordinate to the two fan speeds and applying the
interval inverse gives a scalar phase in the prescribed curve segment.
It solves the characteristic transport equation away from the two fronts,
which form a null set.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.CharacteristicField

open Filter MeasureTheory Set
open PDE.Common
open scoped Topology

variable {m : ℕ} {flux : ℝ^m → ℝ^m}

/-- The original integral-curve parameter inside the fan, extended by the
endpoint parameters outside its two fronts. -/
def rarefactionPhase (C : CharacteristicField flux) (v : ℝ → ℝ^m)
    (l r a b : ℝ) (p : ℝ^2) : ℝ :=
  C.speedInverse v l r
    (max (C.speed (v a)) (min (C.speed (v b)) (similarityVariable p)))

/-- The phase stays on the whole prescribed unordered parameter segment. -/
theorem rarefactionPhase_mem (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r a b : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b)) (p : ℝ^2) :
    C.rarefactionPhase v l r a b p ∈ uIcc a b := by
  rw [← C.speedInverse_image_Icc hv hgn ha hb hexpands]
  exact mem_image_of_mem _ ⟨le_max_left _ _, max_le hexpands (min_le_left _ _)⟩

/-- At time one the point with spatial coordinate equal to a curve state's
speed recovers that exact parameter, in either parameter orientation. -/
theorem rarefactionPhase_at_speed (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r a b s : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b))
    (hs : s ∈ uIcc a b) :
    C.rarefactionPhase v l r a b !₂[1, C.speed (v s)] = s := by
  have hspeed : C.speed (v s) ∈ Icc (C.speed (v a)) (C.speed (v b)) := by
    rw [← C.speed_image_uIcc hv hgn ha hb hexpands]
    exact mem_image_of_mem _ hs
  change C.speedInverse v l r (max (C.speed (v a)) (min (C.speed (v b)) (C.speed (v s) / 1))) = s
  rw [div_one, min_eq_right hspeed.2, max_eq_right hspeed.1]
  exact C.speedInverse_speed hv hgn (ordConnected_Ioo.uIcc_subset ha hb hs)

/-- The phase is differentiable and solves characteristic transport at
every positive-time point away from the two fronts. -/
theorem differentiableAt_rarefactionPhase_and_transport (C : CharacteristicField flux) {v : ℝ → ℝ^m}
    {l r a b : ℝ} (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b)) {p : ℝ^2}
    (ht : 0 < p 0) (hneA : p 1 ≠ C.speed (v a) * p 0) (hneB : p 1 ≠ C.speed (v b) * p 0) :
    DifferentiableAt ℝ (C.rarefactionPhase v l r a b) p ∧
      (∂[0] (C.rarefactionPhase v l r a b)) p + C.speed (v (C.rarefactionPhase v l r a b p)) *
        (∂[1] (C.rarefactionPhase v l r a b)) p = 0 := by
  have hξ := (differentiableAt_similarityVariable ht.ne').continuousAt
  have hneqA : similarityVariable p ≠ C.speed (v a) := fun h ↦ hneA ((div_eq_iff ht.ne').mp h)
  have hneqB : similarityVariable p ≠ C.speed (v b) := fun h ↦ hneB ((div_eq_iff ht.ne').mp h)
  rcases lt_or_gt_of_ne hneqA with hleft | hleft
  · have heq : C.rarefactionPhase v l r a b =ᶠ[𝓝 p] fun _ ↦ a := by
      filter_upwards [hξ (Iio_mem_nhds hleft)] with q hq
      simp only [rarefactionPhase, min_eq_right (hq.le.trans hexpands),
        max_eq_left hq.le, C.speedInverse_speed hv hgn ha]
    refine ⟨differentiableAt_const a |>.congr_of_eventuallyEq heq, ?_⟩
    rw [partialDeriv_congr_nhds 0 heq, partialDeriv_congr_nhds 1 heq]
    simp
  · rcases lt_or_gt_of_ne hneqB with hright | hright
    · have hmem : similarityVariable p ∈ (C.speed ∘ v) '' Ioo l r := by
        apply image_mono (ordConnected_Ioo.uIcc_subset ha hb)
        rw [C.speed_image_uIcc hv hgn ha hb hexpands]
        exact ⟨hleft.le, hright.le⟩
      have hβ := (C.hasDerivAt_speedInverse hv hgn hmem).differentiableAt
      have heq : C.rarefactionPhase v l r a b =ᶠ[𝓝 p]
          fun q ↦ C.speedInverse v l r (similarityVariable q) := by
        filter_upwards [hξ (Ioo_mem_nhds hleft hright)] with q hq
        simp only [rarefactionPhase, min_eq_right hq.2.le, max_eq_right hq.1.le]
      have hvalue : C.speed (v (C.rarefactionPhase v l r a b p)) =
          similarityVariable p := by
        rw [heq.self_of_nhds]
        exact (C.speedInverse_mem_and_eq hmem).2
      refine ⟨(hβ.comp p (differentiableAt_similarityVariable ht.ne')).congr_of_eventuallyEq heq,
        ?_⟩
      rw [partialDeriv_congr_nhds 0 heq, partialDeriv_congr_nhds 1 heq,
        partialDeriv_comp_real 0 hβ (differentiableAt_similarityVariable ht.ne'),
        partialDeriv_comp_real 1 hβ (differentiableAt_similarityVariable ht.ne'), hvalue]
      calc
        _ = ((∂[0] similarityVariable) p + similarityVariable p * (∂[1] similarityVariable) p) *
              deriv (C.speedInverse v l r) (similarityVariable p) := by ring
        _ = 0 := by rw [similarityVariable_transport p ht.ne', zero_mul]
    · have heq : C.rarefactionPhase v l r a b =ᶠ[𝓝 p] fun _ ↦ b := by
        filter_upwards [hξ (Ioi_mem_nhds hright)] with q hq
        simp only [rarefactionPhase, min_eq_left hq.le, max_eq_right hexpands,
          C.speedInverse_speed hv hgn hb]
      refine ⟨differentiableAt_const b |>.congr_of_eventuallyEq heq, ?_⟩
      rw [partialDeriv_congr_nhds 0 heq, partialDeriv_congr_nhds 1 heq]
      simp

/-- The phase satisfies the scalar characteristic equation almost everywhere
in positive spacetime, by the nullity of the two affine fronts. -/
theorem ae_rarefactionPhase_transport (C : CharacteristicField flux) {v : ℝ → ℝ^m} {l r a b : ℝ}
    (hv : IsIntegralCurveOn v C.vectorField (Ioo l r)) (hgn : C.IsGenuinelyNonlinear)
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) (hexpands : C.speed (v a) ≤ C.speed (v b)) :
    ∀ᵐ p ∂volume.restrict forwardHalfSpace,
      DifferentiableAt ℝ (C.rarefactionPhase v l r a b) p ∧
      (∂[0] (C.rarefactionPhase v l r a b)) p +
        C.speed (v (C.rarefactionPhase v l r a b p)) *
          (∂[1] (C.rarefactionPhase v l r a b)) p = 0 := by
  filter_upwards [ae_restrict_mem forwardHalfSpace.isOpen.measurableSet,
    ae_restrict_of_ae (AffineInterface.ae_ne_interface (C.speed (v a))),
    ae_restrict_of_ae (AffineInterface.ae_ne_interface (C.speed (v b)))] with p hp hpa hpb
  exact C.differentiableAt_rarefactionPhase_and_transport hv hgn ha hb hexpands hp hpa hpb

end PDE.Hyperbolic.ConservationLaw.System.CharacteristicField

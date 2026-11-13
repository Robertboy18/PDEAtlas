/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Lp
import CAS.ExactTactic

/-!
# Weighted square integrability and reflection

A positive lower bound on a weight turns finite weighted energy on a half-space into
unweighted `L²` control. Even and odd reflection then double the squared integral.
We derive integrability before comparing integrals, so a finite value of Lean's totalized
integral is never used in place of finite energy.

The reflection is across any coordinate hyperplane. No trace condition is needed for
`L²`; trace conditions enter only when identifying reflected weak derivatives.
Continuous nonnegative even densities satisfy the same factor-two bound by applying
the square argument to their square roots.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Weighted

private theorem reflection_memLp_and_integral_le
    {n : ℕ} (i : Fin n) (f w : ℝ^n → ℝ) (c sign : ℝ)
    (hc : 0 < c) (hsign : sign ^ 2 = 1)
    (hf : AEStronglyMeasurable f (volume.restrict {x | 0 ≤ x i}))
    (hfloor : ∀ᵐ x ∂(volume.restrict {x : ℝ^n | 0 ≤ x i}), c ≤ w x)
    (hweighted : Integrable (fun x ↦ f x ^ 2 * w x)
      (volume.restrict {x | 0 ≤ x i})) :
    let reflected := fun x : ℝ^n ↦
      if x i < 0 then sign * f (PDE.Common.coordinateReflection i x) else f x
    MemLp reflected 2 volume ∧
      (∫ x, reflected x ^ 2) ≤
        (2 / c) * ∫ x in {x : ℝ^n | 0 ≤ x i}, f x ^ 2 * w x := by
  let H : Set (ℝ^n) := {x | 0 ≤ x i}
  let g : ℝ^n → ℝ := H.indicator f
  let R : ℝ^n → ℝ := fun x ↦
    if x i < 0 then sign * f (PDE.Common.coordinateReflection i x) else f x
  change MemLp R 2 volume ∧
    (∫ x, R x ^ 2) ≤ (2 / c) * ∫ x in H, f x ^ 2 * w x
  have hH : MeasurableSet H :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hpoint : ∀ᵐ x ∂(volume.restrict H),
      f x ^ 2 ≤ c⁻¹ * (f x ^ 2 * w x) := by
    filter_upwards [hfloor] with x hx
    calc
      f x ^ 2 = c⁻¹ * (f x ^ 2 * c) := by cas using hc.ne'
      _ ≤ c⁻¹ * (f x ^ 2 * w x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hx (sq_nonneg _)) (inv_nonneg.mpr hc.le)
  have hsq : Integrable (fun x ↦ f x ^ 2) (volume.restrict H) := by
    apply Integrable.mono' (hweighted.const_mul c⁻¹) (hf.pow 2)
    filter_upwards [hpoint] with x hx
    change ‖f x ^ 2‖ ≤ c⁻¹ * (f x ^ 2 * w x)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))] using hx
  have hbound : (∫ x in H, f x ^ 2) ≤ c⁻¹ * ∫ x in H, f x ^ 2 * w x := by
    simpa only [integral_const_mul] using
      integral_mono_ae hsq (hweighted.const_mul c⁻¹) hpoint
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict hH.nullMeasurableSet).2 ((memLp_two_iff_integrable_sq hf).2 hsq)
  have hreflect := PDE.Common.measurePreserving_coordinateReflection i
  have hgr : MemLp (g ∘ PDE.Common.coordinateReflection i) 2 volume :=
    hg.comp_measurePreserving hreflect
  have haxis : ∀ᵐ x : ℝ^n ∂volume, x i ≠ 0 := by
    rw [ae_iff]
    simpa only [PDE.Common.coordinateHyperplane, mem_ofPred_eq, not_not] using
      HalfSpace.volume_coordinateHyperplane_eq_zero i
  have hrepr : R =ᵐ[volume] fun x ↦
      g x + sign * g (PDE.Common.coordinateReflection i x) := by
    filter_upwards [haxis] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · simp [R, g, H, hx, le_of_lt (neg_pos.mpr hx), not_le.mpr hx]
    · simp [R, g, H, hx.le, not_lt.mpr hx.le, not_le.mpr (neg_lt_zero.mpr hx)]
  have hR : MemLp R 2 volume :=
    (memLp_congr_ae hrepr).2 (hg.add (hgr.const_mul sign))
  have hgSq : Integrable (fun x ↦ g x ^ 2) volume :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hgrSq : Integrable (fun x ↦ g (PDE.Common.coordinateReflection i x) ^ 2) volume :=
    hreflect.integrable_comp_of_integrable hgSq
  have hsquares : (fun x ↦ R x ^ 2) =ᵐ[volume] fun x ↦
      g x ^ 2 + g (PDE.Common.coordinateReflection i x) ^ 2 := by
    filter_upwards [haxis] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · simp [R, g, H, hx, le_of_lt (neg_pos.mpr hx), not_le.mpr hx, mul_pow, hsign]
    · simp [R, g, H, hx.le, not_lt.mpr hx.le, not_le.mpr (neg_lt_zero.mpr hx)]
  have hgIntegral : (∫ x, g x ^ 2) = ∫ x in H, f x ^ 2 := by
    have heq : (fun x ↦ g x ^ 2) = H.indicator (fun x ↦ f x ^ 2) := by
      funext x
      by_cases hx : x ∈ H <;> simp [g, hx]
    rw [heq, integral_indicator hH]
  have hdouble : (∫ x, R x ^ 2) = 2 * ∫ x in H, f x ^ 2 := by
    rw [integral_congr_ae hsquares, integral_add hgSq hgrSq,
      hreflect.integral_comp
        (PDE.Common.coordinateReflectionLinearIsometryEquiv i).toHomeomorph.measurableEmbedding
        (fun x ↦ g x ^ 2),
      hgIntegral]
    ring
  refine ⟨hR, ?_⟩
  rw [hdouble]
  calc
    2 * (∫ x in H, f x ^ 2) ≤ 2 * (c⁻¹ * ∫ x in H, f x ^ 2 * w x) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (2 / c) * ∫ x in H, f x ^ 2 * w x := by ring

/-- Let `f` be almost everywhere strongly measurable on the half-space `{x | 0 ≤ x i}`, let
`c ≤ w` almost everywhere there for some `c > 0`, and let `f ^ 2 * w` be integrable there. Then,
for `sign ^ 2 = 1`, the function equal to `f` on the half-space and to
`sign * f ∘ coordinateReflection i` on `{x | x i < 0}` belongs to `L²(ℝ^n)`. No trace condition
is needed. -/
theorem memLp_reflection_of_integrable_sq_mul
    {n : ℕ} (i : Fin n) (f w : ℝ^n → ℝ) (c sign : ℝ)
    (hc : 0 < c) (hsign : sign ^ 2 = 1)
    (hf : AEStronglyMeasurable f (volume.restrict {x | 0 ≤ x i}))
    (hfloor : ∀ᵐ x ∂(volume.restrict {x : ℝ^n | 0 ≤ x i}), c ≤ w x)
    (hweighted : Integrable (fun x ↦ f x ^ 2 * w x)
      (volume.restrict {x | 0 ≤ x i})) :
    MemLp (fun x : ℝ^n ↦
      if x i < 0 then sign * f (PDE.Common.coordinateReflection i x) else f x) 2 volume :=
  (reflection_memLp_and_integral_le i f w c sign hc hsign hf hfloor hweighted).1

/-- Under the hypotheses of `memLp_reflection_of_integrable_sq_mul`, the integral over `ℝ^n` of
the square of the signed reflection is at most `(2 / c) * ∫ x in {x | 0 ≤ x i}, f x ^ 2 * w x`.
The factor `2` accounts for the two reflected halves. -/
theorem integral_reflection_sq_le_of_integrable_sq_mul
    {n : ℕ} (i : Fin n) (f w : ℝ^n → ℝ) (c sign : ℝ)
    (hc : 0 < c) (hsign : sign ^ 2 = 1)
    (hf : AEStronglyMeasurable f (volume.restrict {x | 0 ≤ x i}))
    (hfloor : ∀ᵐ x ∂(volume.restrict {x : ℝ^n | 0 ≤ x i}), c ≤ w x)
    (hweighted : Integrable (fun x ↦ f x ^ 2 * w x)
      (volume.restrict {x | 0 ≤ x i})) :
    (∫ x : ℝ^n,
      (if x i < 0 then sign * f (PDE.Common.coordinateReflection i x) else f x) ^ 2) ≤
        (2 / c) * ∫ x in {x : ℝ^n | 0 ≤ x i}, f x ^ 2 * w x :=
  (reflection_memLp_and_integral_le i f w c sign hc hsign hf hfloor hweighted).2

end SobolevSpace.Weighted

namespace SobolevSpace.Weighted

open MeasureTheory

/-- If `f` is continuous, nonnegative, even under `coordinateReflection i` and integrable on
`{x | 0 ≤ x i}`, then `f` is integrable on `ℝ^n` and `∫ x, f x ≤ 2 * ∫ x in {x | 0 ≤ x i}, f x`.
The proof applies the signed reflection bound to `√f` with weight `1`. -/
theorem integrable_integral_le_twice_of_nonneg_even
    {n : ℕ} (i : Fin n) {f : ℝ^n → ℝ}
    (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (heven : PDE.Common.IsEvenUnderCoordinateReflection i f)
    (hint : Integrable f (volume.restrict {x : ℝ^n | 0 ≤ x i})) :
    Integrable f volume ∧
      (∫ x, f x) ≤ 2 * ∫ x in {x : ℝ^n | 0 ≤ x i}, f x := by
  let g : ℝ^n → ℝ := fun x ↦ Real.sqrt (f x)
  have hsq (x : ℝ^n) : g x ^ 2 = f x := Real.sq_sqrt (hnonneg x)
  have hweighted : Integrable (fun x ↦ g x ^ 2 * (1 : ℝ))
      (volume.restrict {x : ℝ^n | 0 ≤ x i}) := by
    simpa only [hsq, mul_one] using hint
  have hfloor : ∀ᵐ x : ℝ^n ∂(volume.restrict {x : ℝ^n | 0 ≤ x i}),
      (1 : ℝ) ≤ 1 := Filter.Eventually.of_forall fun _ ↦ le_rfl
  have hrefl (x : ℝ^n) :
      (if x i < 0 then (1 : ℝ) * g (PDE.Common.coordinateReflection i x) else g x) ^
        2 = f x := by
    split_ifs
    · simp only [one_mul, hsq, heven x]
    · exact hsq x
  have hmem := memLp_reflection_of_integrable_sq_mul i g (fun _ ↦ 1) 1 1
    (by norm_num) (by norm_num) hf.sqrt.aestronglyMeasurable hfloor hweighted
  have hbound := integral_reflection_sq_le_of_integrable_sq_mul i g (fun _ ↦ 1) 1 1
    (by norm_num) (by norm_num) hf.sqrt.aestronglyMeasurable hfloor hweighted
  refine ⟨?_, ?_⟩
  · simpa only [hrefl] using hmem.integrable_sq
  · simpa only [hrefl, hsq, mul_one, div_one] using hbound

end SobolevSpace.Weighted

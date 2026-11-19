/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.Algebra

/-!
# The derivative operator of Sobolev composition

A derivative coefficient need not vanish at zero, so it need not belong to Hᵏ
on the whole space. We separate its value at zero from its variable part.
The constant acts by scalar multiplication; the variable part uses the Sobolev
algebra product. This gives a bounded operator with the expected pointwise formula.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Topology

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [NeZero n] {ι : Type*} [DecidableEq ι]

/-- The variable part of a reaction's derivative coefficient; it vanishes at zero. -/
def centeredPartial (f : (ι → ℝ) → ℝ) (i : ι) (a : ι → ℝ) : ℝ :=
  fderiv ℝ f a (Pi.single i 1) - fderiv ℝ f 0 (Pi.single i 1)

/-- Removing the constant coefficient makes composition integrable on the whole space. -/
@[simp] theorem centeredPartial_zero (f : (ι → ℝ) → ℝ) (i : ι) :
    centeredPartial f i 0 = 0 := sub_self _

variable [Fintype ι]

/-- Smooth reactions have smooth centered derivative coefficients. -/
theorem contDiff_centeredPartial {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (centeredPartial f i) :=
  ((hf.fderiv_right (by simp)).clm_apply contDiff_const).sub contDiff_const

/-- The derivative of a finite reaction, acting on Sobolev directions.
The constant coefficient acts directly, while its variable part uses Sobolev multiplication. -/
def finiteCompositionDerivative (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (U : ι → W^{k,2}(ℝ^n)) : (ι → W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n) :=
  ∑ i, ((multiplication hk
    (finiteComposition hk (contDiff_centeredPartial hf i) (centeredPartial_zero f i) U)).comp
      (ContinuousLinearMap.proj i) +
    (fderiv ℝ f 0 (Pi.single i 1)) • (ContinuousLinearMap.proj i))

/-- The Sobolev derivative operator represents the ordinary pointwise derivative. -/
theorem finiteCompositionDerivative_ae (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (U H : ι → W^{k,2}(ℝ^n)) :
    baseRepresentative (finiteCompositionDerivative hk hf U H) =ᵐ[volume]
      (fun x ↦ fderiv ℝ f (fun i ↦ baseRepresentative (U i) x)
        (fun i ↦ baseRepresentative (H i) x)) := by
  let C := fun i ↦ finiteComposition hk (contDiff_centeredPartial hf i)
    (centeredPartial_zero f i) U
  let c := fun i ↦ fderiv ℝ f 0 (Pi.single i 1)
  have hterm (i : ι) : baseRepresentative (multiplication hk (C i) (H i) + c i • H i)
      =ᵐ[volume] (fun x ↦ fderiv ℝ f (fun j ↦ baseRepresentative (U j) x)
        (Pi.single i 1) * baseRepresentative (H i) x) := by
    have ha := baseRepresentative_add_ae (multiplication hk (C i) (H i)) (c i • H i)
    have hs := baseRepresentative_smul_ae (c i) (H i)
    simp only [domainMeasure, Measure.restrict_univ] at ha hs
    filter_upwards [ha, hs, multiplication_ae hk (C i) (H i),
      finiteComposition_ae hk (contDiff_centeredPartial hf i) (centeredPartial_zero f i) U]
      with x ha hs hm hc
    change baseRepresentative (C i) x = _ at hc
    rw [ha, hs, hm, hc]
    simp only [centeredPartial, c, smul_eq_mul]
    ring
  have hsum := baseRepresentative_sum_ae
    (fun i ↦ multiplication hk (C i) (H i) + c i • H i)
  simp only [domainMeasure, Measure.restrict_univ] at hsum
  filter_upwards [hsum, ae_all_iff.mpr hterm] with x hs ht
  simp only [finiteCompositionDerivative, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.proj_apply]
  change baseRepresentative (∑ i, (multiplication hk (C i) (H i) + c i • H i)) x = _
  rw [hs]
  calc
    _ = ∑ i, fderiv ℝ f (fun j ↦ baseRepresentative (U j) x)
        (Pi.single i 1) * baseRepresentative (H i) x :=
      Finset.sum_congr rfl (fun i _ ↦ ht i)
    _ = _ := by
      symm
      have hb (i : ι) : (fun j ↦ if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j
        simp only [Pi.single_apply, eq_comm]
      simpa only [ContinuousLinearMap.coe_coe, hb, smul_eq_mul, mul_comm] using
        (fderiv ℝ f (fun j ↦ baseRepresentative (U j) x)).toLinearMap.pi_apply_eq_sum_univ
          (fun i ↦ baseRepresentative (H i) x)
end SobolevSpace.Composition

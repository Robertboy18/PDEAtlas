/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.AdjointOperator
public import PDE.Hyperbolic.Models.Wave.Strichartz.SpacetimePairing

/-!
# The Gram identity on mixed quotient spaces

The Fourier adjoint and the exterior Newton operator satisfy the Gram
identity on compact tensor sums. Density and continuity extend the identity to
all elements of the mixed dual space. The tensor section lemmas give the measurability,
integrability and representative facts used in that extension.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal

namespace WaveEquation.Strichartz

variable (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
  {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ)

/-- Finite compact Schwartz tensors define a jointly measurable physical function. -/
theorem measurable_compactTensorSchwartzSection :
    Measurable (fun z : ℝ × ℝ^3 ↦ SchwartzMap.compactTensorSchwartzLinearMap a z.1 z.2) := by
  simp only [SchwartzMap.compactTensorSchwartzLinearMap, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.sum_apply, Pi.smul_apply, sum_apply, smul_apply, smul_eq_mul]
  exact (continuous_finsetSum a.support fun z _ ↦
    continuous_const.mul ((z.1.1.continuous.comp continuous_fst).mul
      (z.2.1.continuous.comp continuous_snd))).measurable

/-- Every physical spatial section has compact support. -/
theorem hasCompactSupport_compactTensorSchwartzSection (t : ℝ) :
    HasCompactSupport (SchwartzMap.compactTensorSchwartzLinearMap a t : ℝ^3 → ℝ) := by
  have he : (SchwartzMap.compactTensorSchwartzLinearMap a t : ℝ^3 → ℝ) =
      ∑ z ∈ a.support, fun x ↦ a z • (z.1.1 t • z.2.1 x) := by
    funext x
    simp only [SchwartzMap.compactTensorSchwartzLinearMap, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_apply, Pi.smul_apply, sum_apply, smul_apply]
  rw [he]
  exact HasCompactSupport.finset_sum fun z _ ↦
    (z.2.2.smul_left (f := fun _ ↦ z.1.1 t)).smul_left (f := fun _ ↦ a z)

/-- The finite physical section represents the dense quotient tensor map. -/
theorem compactTensorSchwartzSection_ae_eq :
    ∀ᵐ t, (SchwartzMap.compactTensorSchwartzLinearMap a t : ℝ^3 → ℝ) =ᵐ[volume]
      (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a t : ℝ^3 → ℝ) := by
  filter_upwards [SchwartzMap.compactTensorLpLinearMap_ae_eq
    (4 / 3) (12 / 11) volume volume a] with t ht
  rw [ht]
  exact ((SchwartzMap.compactTensorSchwartzLinearMap a t).coeFn_toLp (12 / 11) volume).symm

/-- The raw mixed norm is finite because it is the norm of the quotient class. -/
theorem memLp_eLpNorm_compactTensorSchwartzSection :
    MemLp (fun t ↦ eLpNorm (SchwartzMap.compactTensorSchwartzLinearMap a t) (12 / 11) volume)
      (4 / 3) volume := by
  let u := SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a
  have he : eLpNorm
      (fun t ↦ eLpNorm (SchwartzMap.compactTensorSchwartzLinearMap a t) (12 / 11) volume)
      (4 / 3) volume = ‖u‖ₑ := by
    rw [Lp.enorm_def, ← eLpNorm_enorm _ (Lp.aestronglyMeasurable u)]
    apply eLpNorm_congr_ae
    filter_upwards [compactTensorSchwartzSection_ae_eq a] with t ht
    exact (eLpNorm_congr_ae ht).trans (Lp.enorm_def (u t)).symm
  change eLpNorm _ _ _ < ∞
  rw [he]
  exact enorm_lt_top

/-- The Fourier energy integral of a compact tensor sum is Bochner integrable. -/
theorem integrable_frequencyEnergyDatum_compactTensor :
    Integrable (fun t ↦ frequencyEnergyDatum
      (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t) := by
  have he (t : ℝ) : frequencyEnergyDatum
      (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t =
      ∑ z ∈ a.support, (a z * z.1.1 t) •
        frequencyEnergyDatum (𝓕 (z.2.1.postcompCLM Complex.ofRealCLM)) t := by
    let L := (frequencyEnergyDatumLinearMap t).comp
      ((SchwartzMap.fourierTransformCLM ℝ).toLinearMap.comp
        (SchwartzMap.postcompCLM Complex.ofRealCLM).toLinearMap)
    change L (SchwartzMap.compactTensorSchwartzLinearMap a t) =
      ∑ z ∈ a.support, (a z * z.1.1 t) • L z.2.1
    simp only [SchwartzMap.compactTensorSchwartzLinearMap, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_smul]
  simp_rw [he]
  exact integrable_finsetSum a.support fun z _ ↦
    integrable_smul_frequencyEnergyDatum _ (continuous_const.mul z.1.1.continuous)
      (z.1.2.mul_left (f := fun _ ↦ a z))

end WaveEquation.Strichartz

namespace WaveEquation.Strichartz

/-- On dense compact tensor classes, the adjoint Gram pairing is the
continuous quotient pairing with the Newton operator. -/
theorem re_inner_energyAdjointOperator_compactTensor
    (a b : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    (inner ℂ
      (energyAdjointOperator
        (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume b))
      (energyAdjointOperator
        (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a))).re =
      (4 * Real.pi)⁻¹ * spacetimePairing
        (spacetimeNewtonOperator
          (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a))
        (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume b) := by
  have hA := energyAdjointOperator_compactTensor a
  have hB := energyAdjointOperator_compactTensor b
  calc
    _ = (inner ℂ (∫ t, frequencyEnergyDatum (𝓕
          ((SchwartzMap.compactTensorSchwartzLinearMap b t).postcompCLM Complex.ofRealCLM)) t)
        (∫ t, frequencyEnergyDatum (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM
            Complex.ofRealCLM)) t)).re := congrArg Complex.re (congrArg₂ (inner ℂ) hB hA)
    _ = (4 * Real.pi)⁻¹ * ∫ t, ∫ x,
        SchwartzMap.compactTensorSchwartzLinearMap b t x * spacetimeNewtonIntegral
          (fun z ↦ SchwartzMap.compactTensorSchwartzLinearMap a z.1 z.2) t x :=
      re_inner_integral_frequencyEnergyDatum_eq _ _
        (measurable_compactTensorSchwartzSection a) (measurable_compactTensorSchwartzSection b)
        (hasCompactSupport_compactTensorSchwartzSection a)
        (hasCompactSupport_compactTensorSchwartzSection b)
        (memLp_eLpNorm_compactTensorSchwartzSection a)
        (memLp_eLpNorm_compactTensorSchwartzSection b)
        (integrable_frequencyEnergyDatum_compactTensor a)
        (integrable_frequencyEnergyDatum_compactTensor b)
    _ = _ := congrArg ((4 * Real.pi)⁻¹ * ·) (spacetimePairing_spacetimeNewtonOperator_eq_of_sections
        (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a)
        (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume b)
        (F := fun z ↦ SchwartzMap.compactTensorSchwartzLinearMap a z.1 z.2)
        (G := fun z ↦ SchwartzMap.compactTensorSchwartzLinearMap b z.1 z.2)
        (measurable_compactTensorSchwartzSection a)
        (compactTensorSchwartzSection_ae_eq a) (compactTensorSchwartzSection_ae_eq b)).symm

/-- The adjoint and Newton operators satisfy the Gram identity on the
entire mixed Lebesgue quotient space, by continuity from compact tensors. -/
theorem re_inner_energyAdjointOperator_eq
    (u v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    (inner ℂ (energyAdjointOperator v) (energyAdjointOperator u)).re =
      (4 * Real.pi)⁻¹ * spacetimePairing (spacetimeNewtonOperator u) v := by
  have hd : DenseRange (SchwartzMap.compactTensorLpLinearMap
      (D := ℝ) (E := ℝ^3) (F := ℝ) (4 / 3) (12 / 11) volume volume) :=
    SchwartzMap.denseRange_compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume
      (by finiteness) (by finiteness)
  have htest (a) (v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
      (inner ℂ (energyAdjointOperator v) (energyAdjointOperator
        (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a))).re =
        (4 * Real.pi)⁻¹ * spacetimePairing (spacetimeNewtonOperator
          (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a)) v := by
    refine hd.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) v
    rintro _ ⟨b, rfl⟩
    exact re_inner_energyAdjointOperator_compactTensor a b
  refine hd.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) u
  rintro _ ⟨a, rfl⟩
  exact htest a v

end WaveEquation.Strichartz

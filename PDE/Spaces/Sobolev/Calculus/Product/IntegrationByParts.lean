/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative
public import PDE.Spaces.Sobolev.Calculus.Product.Operator
import PDE.Analysis.MeasureTheory.Lp.ConstantMultiplier
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# Polarized integration by parts with Sobolev coefficients

For a `W^{1,∞}` coefficient, an `H¹` field, and an `H¹₀` field on an open domain, the weak
Leibniz rule gives

`⟪a ∂ⱼu, v⟫ + ⟪a ∂ⱼv, u⟫ = -⟪(∂ⱼa)u, v⟫`.

On the whole space every `H¹` field belongs to `H¹₀` by density, so the identity needs no
additional boundary or decay hypothesis. The differentiated coefficient is its
Sobolev coordinate. The self-pairing gives weak transport energy as minus half
the divergence pairing. On bounded open domains the actual coordinate functions
belong to `W^{1,∞}`, so dilation has the same dimension factor on completed `H¹₀`.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

namespace MeasureTheory.Lp

private theorem sum_lpSMul_left {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) (a : ι → Lp ℝ ∞ μ) (u : Lp ℝ 2 μ) :
    (∑ i ∈ s, a i) • u = ∑ i ∈ s, a i • u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Lp.smul_add, ih]

end MeasureTheory.Lp

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Polarized integration by parts for a `W^{1,∞}` coefficient, an `H¹` field, and an `H¹₀`
field on an open domain. The coefficient derivative is its Sobolev coordinate. -/
theorem inner_mul_deriv_add_inner_mul_deriv_H10
    (hΩ : IsOpen Ω) (A : W^{1,∞}(Ω)) (i : Fin n)
    (U : H¹(Ω)) (V : H¹₀(Ω)) :
    ⟪((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        (U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i), baseCoordCLM V⟫_ℝ +
      ⟪((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) • derivCoordCLM i V,
        (U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)⟫_ℝ =
      -⟪((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
        (U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1), baseCoordCLM V⟫_ℝ := by
  have hprod := w1TopMultiplierAmbient_mapsIsWkpOn hΩ A U U.property
  have hweak : HasWeakDerivativeOn Ω [i]
      ((((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        (U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ)
      ((((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          (U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) +
        ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
          (U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
    simpa only [singleDerivIndex_toList, w1TopMultiplierAmbient_base,
      w1TopMultiplierAmbient_singleDeriv] using hprod (singleDerivIndex n i)
  have h := weakDerivative_integrationByParts_H10 i _ _ hweak V
  rw [inner_add_left, MeasureTheory.Lp.inner_lpSMul_left, real_inner_comm] at h
  linarith only [h]

/-- Whole-space polarized integration by parts holds for arbitrary `H¹` fields. Their `H¹₀`
membership follows from density, so no additional boundary condition is assumed. -/
theorem inner_mul_deriv_add_inner_mul_deriv_univ
    (A : W^{1,∞}(ℝ^n)) (i : Fin n) (U V : H¹(ℝ^n)) :
    ⟪((A : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1)) •
        (U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i),
      (V : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)⟫_ℝ +
      ⟪((A : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1)) •
        (V : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i),
        (U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)⟫_ℝ =
      -⟪((A : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n i)) •
        (U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1),
        (V : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)⟫_ℝ := by
  simpa only [baseCoordCLM_apply, derivCoordCLM_apply] using
    inner_mul_deriv_add_inner_mul_deriv_H10 isOpen_univ A i U
      ⟨V, DifferenceQuotient.h1Space_mem_H10_univ V⟩

/-- The polarized identity gives the energy pairing directly on completed `H¹₀`. -/
theorem inner_mul_deriv_self_H10 (hΩ : IsOpen Ω) (A : W^{1,∞}(Ω))
    (i : Fin n) (U : H¹₀(Ω)) :
    ⟪((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) • derivCoordCLM i U,
      baseCoordCLM U⟫_ℝ =
      -(1 / 2 : ℝ) *
        ⟪((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
          baseCoordCLM U, baseCoordCLM U⟫_ℝ := by
  have h := inner_mul_deriv_add_inner_mul_deriv_H10 hΩ A i (U : H¹(Ω)) U
  simp only [← baseCoordCLM_apply, ← derivCoordCLM_apply] at h
  linarith only [h]

/-- Weak transport energy is minus half the weak divergence pairing. -/
theorem sum_inner_mul_deriv_self_H10 (hΩ : IsOpen Ω)
    (A : Fin n → W^{1,∞}(Ω)) (U : H¹₀(Ω)) :
    (∑ i, ⟪((A i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
      derivCoordCLM i U, baseCoordCLM U⟫_ℝ) =
      -(1 / 2 : ℝ) *
        ⟪(∑ i, (A i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)) •
          baseCoordCLM U, baseCoordCLM U⟫_ℝ := by
  simp_rw [inner_mul_deriv_self_H10 hΩ]
  rw [← Finset.mul_sum, MeasureTheory.Lp.sum_lpSMul_left, sum_inner]

private theorem coordinate_memLp_top (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (i : Fin n) : MemLp (fun x : ℝ^n ↦ x i) ∞ (domainMeasure n Ω) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  apply memLp_top_of_bound (EuclideanSpace.proj i).continuous.aestronglyMeasurable R
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  exact (PiLp.norm_apply_le x i).trans (hR x hx)

private theorem coordinate_derivatives_memLp (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (i : Fin n) (a : DerivIndex n 1) :
    MemLp (iteratedPartialDeriv a.toList (fun x : ℝ^n ↦ x i)) ∞
      (domainMeasure n Ω) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨j, rfl⟩
  · simpa only [baseIndex_toList, iteratedPartialDeriv] using
      coordinate_memLp_top hΩ hb i
  · simp only [singleDerivIndex_toList, iteratedPartialDeriv, PDE.partialDeriv_coord]
    apply memLp_top_of_bound continuous_const.aestronglyMeasurable 1
    exact .of_forall fun _ ↦ by split_ifs <;> norm_num

/-- A coordinate function is a bounded Sobolev coefficient on a bounded open domain. -/
def coordinateW1Top (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (i : Fin n) :
    W^{1,∞}(Ω) :=
  mkWkpSpaceOnOfContDiffMemLp (fun x : ℝ^n ↦ x i)
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff
    (by exact coordinate_derivatives_memLp hΩ hb i)

/-- The coefficient represents the actual coordinate, rather than a surrogate drift. -/
theorem coordinateW1Top_base_ae (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (i : Fin n) :
    ((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ x i := by
  simpa only [coordinateW1Top, baseIndex_toList, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun x : ℝ^n ↦ x i)
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff
      (coordinate_derivatives_memLp hΩ hb i)
      (baseIndex n 1)

/-- The diagonal weak coordinate derivative is the constant one. -/
theorem coordinateW1Top_deriv_self_ae (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (i : Fin n) :
    ((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω)
      (singleDerivIndex n i) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ 1 := by
  simpa only [coordinateW1Top, singleDerivIndex_toList, iteratedPartialDeriv,
    PDE.partialDeriv_coord, ite_eq_left] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun x : ℝ^n ↦ x i)
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff
      (coordinate_derivatives_memLp hΩ hb i)
      (singleDerivIndex n i)

/-- Dilation retains its exact dimension factor on completed bounded-domain `H¹₀`. -/
theorem sum_inner_coordinate_mul_deriv_self_H10 (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (U : H¹₀(Ω)) :
    (∑ i, ⟪((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω)
      (baseIndex n 1)) • derivCoordCLM i U, baseCoordCLM U⟫_ℝ) =
      -(n : ℝ) / 2 * ‖baseCoordCLM U‖ ^ 2 := by
  have hi (i : Fin n) :
      ⟪((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
        derivCoordCLM i U, baseCoordCLM U⟫_ℝ =
        -(1 / 2 : ℝ) * ‖baseCoordCLM U‖ ^ 2 := by
    rw [inner_mul_deriv_self_H10 hΩ, MeasureTheory.Lp.lpSMul_eq_const_smul
      _ 1 (coordinateW1Top_deriv_self_ae hΩ hb i), one_smul, real_inner_self_eq_norm_sq]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SobolevSpace.GraphSpace

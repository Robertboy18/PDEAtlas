/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedDensity

/-!
# Local energy bounds for Lipschitz first-jet reactions

The Lipschitz bound controls the reaction difference by the natural energy
density, pointwise almost everywhere. Weighted integration by parts then
bounds the energy derivative using only the weight and its first derivatives.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- The square of the full-jet reaction difference is controlled by the
pointwise energy density of the difference, without differentiating f. -/
theorem reaction_sub_sq_le_energyDensity_ae (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∀ᵐ y ∂domainMeasure n univ, ((reaction hf hf0 z - reaction hf hf0 w) y) ^ 2 ≤
      (L : ℝ) ^ 2 * energyDensity (z - w) y := by
  have hjet : (firstJetCLM (z - w) : ℝ^n → ℝ^n × ℝ × ℝ) =ᵐ[domainMeasure n univ]
      fun y ↦ firstJetCLM z y - firstJetCLM w y := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hf.coeFn_compLp hf0 (firstJetCLM z), hf.coeFn_compLp hf0 (firstJetCLM w),
    Lp.coeFn_sub (reaction hf hf0 z) (reaction hf hf0 w),
    firstJet_norm_sq_le_energyDensity_ae (z - w), hjet] with y hz hw hr hd hj
  simp only [Pi.sub_apply] at hr
  rw [hr]
  change reaction hf hf0 z y = _ at hz
  change reaction hf hf0 w y = _ at hw
  rw [hz, hw]
  calc
    (f (firstJetCLM z y) - f (firstJetCLM w y)) ^ 2 =
        ‖f (firstJetCLM z y) - f (firstJetCLM w y)‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ((L : ℝ) * ‖firstJetCLM z y - firstJetCLM w y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hf.norm_sub_le _ _) 2
    _ = (L : ℝ) ^ 2 * ‖firstJetCLM (z - w) y‖ ^ 2 := by rw [hj, mul_pow]
    _ ≤ (L : ℝ) ^ 2 * energyDensity (z - w) y := mul_le_mul_of_nonneg_left hd (sq_nonneg _)

/-- Localizing the quadratic energy differentiates the weight once and
cancels the Laplacian against the spatial derivative of the velocity. -/
theorem weightedEnergyForm_wave (χ : W^{1,∞}(ℝ^n))
    (U : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)) (r : DerivLp n 2 univ) :
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    let z := (lowerOrderCLM (by decide : 1 ≤ 2) U, wkpBaseCoordinateCLM V)
    weightedEnergyForm a z (V, wkpLaplacianCLM U - r) =
      ⟪a • (wkpBaseCoordinateCLM U - r), wkpBaseCoordinateCLM V⟫_ℝ -
        ∑ i : Fin n, ⟪(χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) •
          wkpCoordinateCLM (singleDerivIndex n i) z.1, wkpBaseCoordinateCLM V⟫_ℝ := by
  have h := weighted_wave_pairing χ U V r
  dsimp only at h ⊢
  rw [weightedEnergyForm_apply, Lp.inner_lpSMul_left, real_inner_comm]
  change _ + ⟪_ • wkpBaseCoordinateCLM U, wkpBaseCoordinateCLM V⟫_ℝ + _ = _
  linarith only [h]

/-- The displacement and reaction contribution is bounded by the localized
energy whenever the square of the reaction has the corresponding density bound. -/
theorem weighted_source_pairing_le (a : DerivLp n ∞ univ) (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ a y)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) (r : DerivLp n 2 univ) {K : ℝ}
    (hr : ∀ᵐ y ∂domainMeasure n univ, (r y) ^ 2 ≤ K * energyDensity z y) :
    2 * ⟪a • (wkpBaseCoordinateCLM z.1 - r), z.2⟫_ℝ ≤ (2 + K) * weightedEnergyForm a z z := by
  rw [weighted_pair_eq_integral, weightedEnergyForm_eq_integral,
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono_ae ((integrable_weighted_mul a
    (wkpBaseCoordinateCLM z.1 - r) z.2).const_mul 2)
    ((integrable_weighted_energyDensity a z).const_mul (2 + K))
  filter_upwards [ha, hr, Lp.coeFn_sub (wkpBaseCoordinateCLM z.1) r] with y hy hr hs
  simp only [Pi.sub_apply] at hs
  rw [hs]
  have hu : (wkpBaseCoordinateCLM z.1 y) ^ 2 + (z.2 y) ^ 2 ≤ energyDensity z y := by
    unfold energyDensity
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦
      sq_nonneg (wkpCoordinateCLM (singleDerivIndex n i) z.1 y))]
  have hv : (z.2 y) ^ 2 ≤ energyDensity z y := by
    linarith [sq_nonneg (wkpBaseCoordinateCLM z.1 y)]
  have hyoung := two_mul_le_add_sq (wkpBaseCoordinateCLM z.1 y) (z.2 y)
  have hyoung' := two_mul_le_add_sq (-r y) (z.2 y)
  have hle : 2 * ((wkpBaseCoordinateCLM z.1 y - r y) * z.2 y) ≤
      (2 + K) * energyDensity z y := by nlinarith only [hu, hv, hr, hyoung, hyoung']
  nlinarith only [mul_le_mul_of_nonneg_left hle hy]

/-- A derivative of the weight bounded by rho times the weight contributes
at most rho times the localized energy in each spatial direction. -/
theorem weighted_flux_pairing_le (a b : DerivLp n ∞ univ) (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ a y)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hb : ∀ᵐ y ∂domainMeasure n univ, |b y| ≤ ρ * a y)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) (i : Fin n) :
    -(2 * ⟪b • wkpCoordinateCLM (singleDerivIndex n i) z.1, z.2⟫_ℝ) ≤
      ρ * weightedEnergyForm a z z := by
  rw [weighted_pair_eq_integral, weightedEnergyForm_eq_integral,
    ← integral_const_mul, ← integral_neg, ← integral_const_mul]
  apply integral_mono_ae ((integrable_weighted_mul b
    (wkpCoordinateCLM (singleDerivIndex n i) z.1) z.2).const_mul 2).neg
    ((integrable_weighted_energyDensity a z).const_mul ρ)
  filter_upwards [ha, hb] with y ha hb
  let d := wkpCoordinateCLM (singleDerivIndex n i) z.1 y
  let v := z.2 y
  have hcoord : d ^ 2 + v ^ 2 ≤ energyDensity z y := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
      sq_nonneg (wkpCoordinateCLM (singleDerivIndex n j) z.1 y)) (Finset.mem_univ i)
    unfold energyDensity
    dsimp only [d, v] at *
    linarith [sq_nonneg (wkpBaseCoordinateCLM z.1 y)]
  have hyoung := two_mul_le_add_sq |d| |v|
  simp only [sq_abs] at hyoung
  have habs := neg_le_abs (b y * d * v)
  rw [abs_mul, abs_mul] at habs
  have hbound : -(2 * (b y * d * v)) ≤ |b y| * (d ^ 2 + v ^ 2) := by
    nlinarith only [habs, mul_le_mul_of_nonneg_left hyoung (abs_nonneg (b y))]
  calc
    -(2 * (b y * d * v)) ≤ |b y| * (d ^ 2 + v ^ 2) := hbound
    _ ≤ (ρ * a y) * (d ^ 2 + v ^ 2) :=
      mul_le_mul_of_nonneg_right hb (add_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ (ρ * a y) * energyDensity z y := mul_le_mul_of_nonneg_left hcoord (mul_nonneg hρ ha)
    _ = ρ * (a y * energyDensity z y) := mul_assoc _ _ _

/-- The localized energy derivative is bounded using only the Lipschitz
reaction density bound and the relative first derivatives of the weight. -/
theorem weightedEnergyForm_wave_le (χ : W^{1,∞}(ℝ^n))
    (U : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)) (r : DerivLp n 2 univ)
    {K ρ : ℝ} (hρ : 0 ≤ ρ)
    (ha : ∀ᵐ y ∂domainMeasure n univ,
      0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hd : ∀ i : Fin n, ∀ᵐ y ∂domainMeasure n univ,
      |(χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) y| ≤
        ρ * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hr : ∀ᵐ y ∂domainMeasure n univ, (r y) ^ 2 ≤ K * energyDensity
      (lowerOrderCLM (by decide : 1 ≤ 2) U, wkpBaseCoordinateCLM V) y) :
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    let z := (lowerOrderCLM (by decide : 1 ≤ 2) U, wkpBaseCoordinateCLM V)
    2 * weightedEnergyForm a z (V, wkpLaplacianCLM U - r) ≤
      (2 + K + (n : ℝ) * ρ) * weightedEnergyForm a z z := by
  let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let z := (lowerOrderCLM (by decide : 1 ≤ 2) U, wkpBaseCoordinateCLM V)
  have hs := weighted_source_pairing_le a ha z r hr
  have hf := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ weighted_flux_pairing_le a
      ((χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i)) ha hρ (hd i) z i
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hf
  dsimp only at *
  rw [weightedEnergyForm_wave]
  change 2 * ⟪a • (wkpBaseCoordinateCLM U - r), wkpBaseCoordinateCLM V⟫_ℝ ≤
    (2 + K) * weightedEnergyForm a z z at hs
  dsimp only [a, z] at hs hf
  linarith only [hs, hf]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

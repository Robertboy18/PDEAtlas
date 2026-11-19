/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.UnitaryNormalization
public import PDE.DistributionTheory.TemperedDistribution.Sobolev.Fourier

/-!
# Weak derivatives in angular frequency

For the unitary Fourier transform with kernel `exp (-I ⟪x, ξ⟫)`, each weak
coordinate derivative contributes `I ξᵢ`. Conversely, differentiation of the
transform corresponds to the moment `-I xᵢ` of the input.

The identities hold for any finite coordinate word. Only the input and its
specified derivative need belong to `L²`; no intermediate derivatives or global
`L¹` hypothesis enter. Frequency dilation transports the tempered-distribution
identities from Mathlib's convention and removes their factors of `2π`.
-/

@[expose] public noncomputable section

open FourierTransform MeasureTheory Set PDE PDE.Analysis.Fourier

namespace SobolevSpace

private theorem multiplier_ae_iff_unitaryNormalization {n : ℕ} (α : List (Fin n))
    (z : ℂ) (f g u v : ℝ^n → ℂ)
    (hu : u =ᵐ[volume] fun ξ ↦
      unitaryFourierFactor (ℝ^n) • f ((2 * Real.pi)⁻¹ • ξ))
    (hv : v =ᵐ[volume] fun ξ ↦
      unitaryFourierFactor (ℝ^n) • g ((2 * Real.pi)⁻¹ • ξ)) :
    ((fun ξ ↦ (∏ j : Fin α.length,
        (2 * Real.pi * z) * (ξ (α.get j) : ℂ)) * f ξ) =ᵐ[volume] g) ↔
      (fun ξ ↦ (∏ j : Fin α.length, z * (ξ (α.get j) : ℂ)) * u ξ) =ᵐ[volume] v := by
  have hc : 2 * Real.pi ≠ 0 := by positivity
  have hfactor : unitaryFourierFactor (ℝ^n) ≠ 0 :=
    ne_of_gt unitaryFourierFactor_pos
  have hsymbol (ξ : ℝ^n) :
      (∏ j : Fin α.length,
        (2 * Real.pi * z) * (((2 * Real.pi)⁻¹ • ξ) (α.get j) : ℂ)) =
      ∏ j : Fin α.length, z * (ξ (α.get j) : ℂ) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    have hcancel : (2 * Real.pi : ℂ) * ((2 * Real.pi : ℝ)⁻¹ : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ hc
    calc
      _ = ((2 * Real.pi : ℂ) * ((2 * Real.pi : ℝ)⁻¹ : ℂ)) *
          (z * (ξ (α.get j) : ℂ)) := by
        push_cast
        ac_rfl
      _ = _ := by rw [hcancel, one_mul]
  constructor
  · intro h
    have hcomp := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hc)).ae_eq_comp h
    filter_upwards [hcomp, hu, hv] with ξ hξ huξ hvξ
    rw [huξ, hvξ, mul_smul_comm]
    simpa only [Function.comp_apply, hsymbol] using
      congrArg (unitaryFourierFactor (ℝ^n) • ·) hξ
  · intro h
    have hcomp : (fun ξ ↦ (∏ j : Fin α.length,
          (2 * Real.pi * z) * (((2 * Real.pi)⁻¹ • ξ) (α.get j) : ℂ)) *
        f ((2 * Real.pi)⁻¹ • ξ)) =ᵐ[volume] fun ξ ↦ g ((2 * Real.pi)⁻¹ • ξ) := by
      filter_upwards [h, hu, hv] with ξ hξ huξ hvξ
      rw [huξ, hvξ, mul_smul_comm, ← hsymbol ξ] at hξ
      exact (smul_right_inj hfactor).1 hξ
    have hback := (Measure.quasiMeasurePreserving_smul volume hc).ae_eq_comp hcomp
    filter_upwards [hback] with ξ hξ
    simpa only [Function.comp_apply, smul_smul, inv_mul_cancel₀ hc, one_smul] using hξ

/-- An arbitrary weak derivative has multiplier `∏ j, I ξⱼ` in the unitary
angular-frequency convention. Both representatives are only assumed to be in `L²`. -/
theorem hasComplexWeakDerivativeOn_iff_unitaryFourier {n : ℕ} (α : List (Fin n))
    (u v : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    HasComplexWeakDerivativeOn univ α u v ↔
      (fun ξ ↦ (∏ j : Fin α.length, Complex.I * (ξ (α.get j) : ℂ)) *
        unitaryFourier u ξ) =ᵐ[volume] unitaryFourier v := by
  rw [hasComplexWeakDerivativeOn_iff_fourier]
  exact multiplier_ae_iff_unitaryNormalization α Complex.I _ _ _ _
    (coe_unitaryFourier u) (coe_unitaryFourier v)

/-- Square-integrability of the angular-frequency multiplier is equivalent to the
existence of the specified weak derivative in `L²`. -/
theorem exists_hasComplexWeakDerivativeOn_iff_memLp_unitaryFourier {n : ℕ}
    (α : List (Fin n)) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∃ v : Lp ℂ 2 (volume : Measure (ℝ^n)),
      HasComplexWeakDerivativeOn univ α u v) ↔
      MemLp (fun ξ ↦ (∏ j : Fin α.length, Complex.I * (ξ (α.get j) : ℂ)) *
        unitaryFourier u ξ) 2 volume := by
  constructor
  · rintro ⟨v, hv⟩
    exact (memLp_congr_ae ((hasComplexWeakDerivativeOn_iff_unitaryFourier α u v).1 hv)).2
      (Lp.memLp (unitaryFourier v))
  · intro h
    refine ⟨unitaryFourierInv (h.toLp _),
      (hasComplexWeakDerivativeOn_iff_unitaryFourier α u _).2 ?_⟩
    simpa only [unitaryFourier_unitaryFourierInv] using h.coeFn_toLp.symm

/-- Weak derivatives of the unitary Fourier transform correspond to the moments
`∏ j, -I xⱼ` of the input, with no lower-order moment assumptions. -/
theorem hasComplexWeakDerivativeOn_unitaryFourier_iff {n : ℕ} (α : List (Fin n))
    (u v : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    HasComplexWeakDerivativeOn univ α (unitaryFourier u) v ↔
      (fun x ↦ (∏ j : Fin α.length, -Complex.I * (x (α.get j) : ℂ)) * u x)
        =ᵐ[volume] unitaryFourierInv v := by
  have hnormalized := multiplier_ae_iff_unitaryNormalization α (-Complex.I) _ _ _ _
    (coe_unitaryFourierInv (unitaryFourier u)) (coe_unitaryFourierInv v)
  simp only [mul_neg, unitaryFourierInv_unitaryFourier] at hnormalized
  simpa only [fourier_fourierInv_eq] using
    (hasComplexWeakDerivativeOn_fourier_iff α (𝓕⁻ (unitaryFourier u)) v).trans hnormalized

/-- An arbitrary weak derivative of the unitary Fourier transform has an `L²`
representative exactly when the corresponding moment of the input belongs to `L²`. -/
theorem exists_hasComplexWeakDerivativeOn_unitaryFourier_iff_memLp {n : ℕ}
    (α : List (Fin n)) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∃ v : Lp ℂ 2 (volume : Measure (ℝ^n)),
      HasComplexWeakDerivativeOn univ α (unitaryFourier u) v) ↔
      MemLp (fun x ↦ (∏ j : Fin α.length, -Complex.I * (x (α.get j) : ℂ)) * u x)
        2 volume := by
  constructor
  · rintro ⟨v, hv⟩
    exact (memLp_congr_ae ((hasComplexWeakDerivativeOn_unitaryFourier_iff α u v).1 hv)).2
      (Lp.memLp (unitaryFourierInv v))
  · intro h
    refine ⟨unitaryFourier (h.toLp _),
      (hasComplexWeakDerivativeOn_unitaryFourier_iff α u _).2 ?_⟩
    simpa only [unitaryFourierInv_unitaryFourier] using h.coeFn_toLp.symm

end SobolevSpace

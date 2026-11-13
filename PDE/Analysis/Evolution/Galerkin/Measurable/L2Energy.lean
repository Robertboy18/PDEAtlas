/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.GardingEstimate
public import PDE.Analysis.Evolution.Galerkin.Measurable.Energy
public import PDE.Analysis.Evolution.Galerkin.ProjectedDerivative
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Uniform Gårding estimates for Galerkin derivatives

Let `u : [a, b] → S` be absolutely continuous with `u' ∈ L²`, solving the projected equation
almost everywhere, where `θ ‖w‖² ≤ B(t)(w, w) + γ ‖ι w‖²` with `θ > 0`, `γ ≥ 0`,
`‖B(t)‖ ≤ MB` almost everywhere, and `ℓ ∈ L²(a, b; V*)`. With
`D = ‖ι u(a)‖²_H + θ⁻¹ ∫_a^b ‖ℓ‖²` and `F = θ⁻¹ (1 + 2γ (b - a) e^{2γ (b - a)})`,

`‖ι u(t)‖²_H ≤ D e^{2γ (t - a)}`,  `∫_a^b ‖u‖²_V ≤ F D`,
`∫_a^b ‖u'‖²_{V*} ≤ 2K² (∫_a^b ‖ℓ‖² + MB² F D)`,

where `K` is the energy bound of a stable trial projection onto `S`. The constants do not
depend on the trial space.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gårding energy inequality on every prefix `[a, t]`:
`½ ‖ι u(t)‖² + (θ/2) ∫_a^t ‖u‖²_V ≤ ½ ‖ι u(a)‖² + (1/(2θ)) ∫_a^t ‖ℓ‖² + γ ∫_a^t ‖ι u‖²`. -/
theorem gelfandGalerkin_garding_prefix_energy_bound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (u du : ℝ → S) {a b theta gamma : ℝ} (hab : a ≤ b) (htheta : 0 < theta)
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    (hduMem : MemLp du 2 (volume.restrict (Ioc a b)))
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ w : V,
      theta * ‖w‖ ^ 2 ≤ B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    ∀ t ∈ Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 +
          (theta / 2) * (∫ s in a..t, ‖(u s : V)‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a : V)‖ ^ 2 +
          (1 / (2 * theta)) * (∫ s in a..t, ‖ell s‖ ^ 2) +
          gamma * (∫ s in a..t, ‖T.inclusion (u s : V)‖ ^ 2) := by
  intro t ht
  have hm : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
    volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2)
  have hac := huAC.mono (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
  simpa only [intervalIntegral.integral_of_le ht.1] using
    gelfandGalerkin_garding_energy_bound_of_forcing_memLp T S B ell u du ht.1 htheta
      hac (hdu.filter_mono (ae_mono hm)) (hduMem.mono_measure hm)
      (hGarding.filter_mono (ae_mono hm)) (hell.mono_measure hm)
      (heq.filter_mono (ae_mono hm))

/-- Integrating the projection estimate controls the dual derivative.
Only the energy stability constant appears, so this estimate is uniform in a
stable family of trial spaces. -/
theorem integral_norm_energyToDual_sq_le_of_projected_equation
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u du : ℝ → S} {a b : ℝ} (hab : a ≤ b)
    (hu : MemLp u 2 (volume.restrict (Ioc a b)))
    (hdu : MemLp du 2 (volume.restrict (Ioc a b)))
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    (∫ t in a..b, ‖T.energyToDual (du t : V)‖ ^ 2) ≤
      2 * (K : ℝ) ^ 2 * ((∫ t in a..b, ‖ell t‖ ^ 2) +
        (MB : ℝ) ^ 2 * (∫ t in a..b, ‖(u t : V)‖ ^ 2)) := by
  have hdual := (T.energyToDual.comp S.subtypeL).comp_memLp' hdu
  have hu' := S.subtypeL.comp_memLp' hu
  have hiu : Integrable (fun t ↦ ‖(u t : V)‖ ^ 2) (volume.restrict (Ioc a b)) :=
    hu'.integrable_norm_pow (by norm_num)
  have hif := hell.integrable_norm_pow (by norm_num)
  have hib := (hif.add (hiu.const_mul ((MB : ℝ) ^ 2))).const_mul (2 * (K : ℝ) ^ 2)
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  calc
    _ ≤ ∫ t in Ioc a b,
        2 * (K : ℝ) ^ 2 * (‖ell t‖ ^ 2 + (MB : ℝ) ^ 2 * ‖(u t : V)‖ ^ 2) := by
      apply integral_mono_ae (hdual.integrable_norm_pow (by norm_num)) hib
      filter_upwards [heq, hbound] with t ht hBt
      change ‖T.energyToDual (du t : V)‖ ^ 2 ≤
        2 * (K : ℝ) ^ 2 * (‖ell t‖ ^ 2 + (MB : ℝ) ^ 2 * ‖(u t : V)‖ ^ 2)
      have hn := (P.norm_energyToDual_le_of_projected_equation ht).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_right hBt (norm_nonneg _)) _)
          K.coe_nonneg)
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
      nlinarith [sq_nonneg (‖ell t‖ - (MB : ℝ) * ‖(u t : V)‖),
        mul_nonneg (sq_nonneg (K : ℝ))
          (sq_nonneg (‖ell t‖ - (MB : ℝ) * ‖(u t : V)‖))]
    _ = _ := by
      rw [integral_const_mul, integral_add hif (hiu.const_mul ((MB : ℝ) ^ 2)),
        integral_const_mul]

/-- The three squared estimates of the module docstring: the pointwise pivot bound
`‖ι u(t)‖² ≤ D e^{2γ (t - a)}`, the `L²(V)` bound `F D`, and the `L²(V*)` bound for the
dual derivative. -/
theorem gelfandGalerkin_garding_three_squared_bounds
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u du : ℝ → S} {a b theta gamma : ℝ}
    (hab : a ≤ b) (htheta : 0 < theta) (hgamma : 0 ≤ gamma)
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    (hduMem : MemLp du 2 (volume.restrict (Ioc a b)))
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ w : V,
      theta * ‖w‖ ^ 2 ≤ B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : S,
      inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
        B t (u t : V) (v : V) = ell t (v : V)) :
    let D := ‖T.inclusion (u a : V)‖ ^ 2 + (1 / theta) * (∫ t in a..b, ‖ell t‖ ^ 2)
    let F := (1 / theta) * (1 + 2 * gamma * (b - a) * Real.exp (2 * gamma * (b - a)))
    (∀ t ∈ Icc a b, ‖T.inclusion (u t : V)‖ ^ 2 ≤
      D * Real.exp (2 * gamma * (t - a))) ∧
    (∫ t in a..b, ‖(u t : V)‖ ^ 2) ≤ F * D ∧
    (∫ t in a..b, ‖T.energyToDual (du t : V)‖ ^ 2) ≤
      2 * (K : ℝ) ^ 2 * ((∫ t in a..b, ‖ell t‖ ^ 2) + (MB : ℝ) ^ 2 * (F * D)) := by
  dsimp only
  have huCont : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab] using huAC.continuousOn
  have hw := (T.inclusion.comp S.subtypeL).continuous.comp_continuousOn huCont
  have henergy := gelfandGalerkin_garding_prefix_energy_bound T S B ell u du
    hab htheta huAC hdu hduMem hGarding hell heq
  have hV := integral_norm_sq_le_of_garding_energy_bound hw hell htheta hgamma hab henergy
  refine ⟨norm_sq_le_exp_of_garding_energy_bound hw hell htheta hgamma hab henergy, hV, ?_⟩
  have huMem : MemLp u 2 (volume.restrict (Ioc a b)) :=
    huCont.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  exact (integral_norm_energyToDual_sq_le_of_projected_equation P hab huMem hduMem
    hell MB hbound heq).trans (by gcongr)

end PDE.Analysis.Evolution

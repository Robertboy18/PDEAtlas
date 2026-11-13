/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import PDE.Common.Euclidean

/-!
# Bounded-support Poincaré estimates at every finite exponent

For dimension greater than one, an intermediate Sobolev exponent below the dimension
handles every finite `p ≥ 1`, including the critical and supercritical range. Hölder on
the common bounded support then raises the derivative norm back to `Lᵖ`.
On the real line, the fundamental theorem of calculus supplies the endpoint estimate;
a volume-preserving isometry transports it to one-dimensional Euclidean space.

These are Poincaré's inequality `‖u‖_{L^p(U)} ≤ C ‖Du‖_{L^p(U)}` of Evans, §5.6.1, stated at
the end of Theorem 3 for `u ∈ W^{1,p}_0(U)`, `U` bounded and `1 ≤ p ≤ ∞`. Ours are for `C¹`
functions supported in a fixed bounded set and for finite `p`. The estimate at the
intermediate exponent is Mathlib's Gagliardo–Nirenberg–Sobolev inequality on bounded sets,
`eLpNorm_le_eLpNorm_fderiv_of_le`.

## Main results

* `exists_eLpNorm_le_eLpNorm_fderiv_of_bounded_support`: in dimension at least two, for a
  bounded set `s` and finite `p ≥ 1` some `C` gives `‖u‖_p ≤ C ‖Du‖_p` for every `C¹`
  function `u` supported in `s`.
* `eLpNorm_le_eLpNorm_fderiv_real`, `eLpNorm_le_eLpNorm_fderiv_euclidean_one`: the same on
  `ℝ` and on `ℝ^1`, with `C` the measure of the closure of `s`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, Theorem 3 (Estimates for `W^{1,p}_0`,
  `1 ≤ p < n`), p. 279, and the Poincaré inequality at its end, p. 280.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

open Module Set Function Measure
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- On a common bounded support, the `Lᵖ` norm is controlled by the `Lᵖ` norm of the
Fréchet derivative for every finite `p ≥ 1`. The source has dimension at least two;
no restriction `p < dim E` is imposed. The target can be any finite-dimensional real
normed space. -/
theorem exists_eLpNorm_le_eLpNorm_fderiv_of_bounded_support
    (μ : Measure E) [IsAddHaarMeasure μ]
    (hn : 1 < finrank ℝ E) {s : Set E} (hs : Bornology.IsBounded s)
    {p : NNReal} (hp : 1 ≤ p) :
    ∃ C : NNReal, ∀ u : E → F, ContDiff ℝ 1 u → support u ⊆ s →
      eLpNorm u p μ ≤ C * eLpNorm (fderiv ℝ u) p μ := by
  let n : ℝ := finrank ℝ E
  have hnR : 1 < n := by
    dsimp [n]
    exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn0 : 0 < n := lt_trans zero_lt_one hnR
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hpR
  have hden : 0 < n + p - 1 := by linarith
  let r : NNReal := ⟨n * p / (n + p - 1), by positivity⟩
  have hr : (r : ℝ) = n * p / (n + p - 1) := rfl
  have hr1 : (1 : NNReal) ≤ r := by
    change (1 : ℝ) ≤ n * p / (n + p - 1)
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR.le) (sub_nonneg.mpr hpR)]
  have hrp : r ≤ p := by
    change n * (p : ℝ) / (n + p - 1) ≤ p
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hpR)]
  have hrn : r < (finrank ℝ E : NNReal) := by
    change n * (p : ℝ) / (n + p - 1) < n
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos hn0 (sub_pos.mpr hnR)]
  have hrecip : (r : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := by
    change (r : ℝ)⁻¹ - n⁻¹ ≤ (p : ℝ)⁻¹
    rw [hr, inv_div]
    field_simp
    nlinarith
  let δ : ℝ := 1 / (r : ℝ) - 1 / (p : ℝ)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr1))
      (by exact_mod_cast hrp)
  let M : ℝ≥0∞ := (μ (closure s)) ^ δ
  have hM : M ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hδ hs.isCompact_closure.measure_ne_top
  let C : NNReal := eLpNormLESNormFDerivOfLeConst F μ (closure s) r p * M.toNNReal
  refine ⟨C, ?_⟩
  intro u hu hus
  have hsu : support u ⊆ closure s := hus.trans subset_closure
  have hsdu : support (fderiv ℝ u) ⊆ closure s :=
    (support_fderiv_subset ℝ).trans (closure_mono hus)
  have hdu : AEStronglyMeasurable (fderiv ℝ u) μ :=
    (hu.continuous_fderiv (by norm_num)).aestronglyMeasurable
  have hcompare : eLpNorm (fderiv ℝ u) r μ ≤ eLpNorm (fderiv ℝ u) p μ * M := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := μ.restrict (closure s)) (f := fderiv ℝ u)
      (show (r : ℝ≥0∞) ≤ (p : ℝ≥0∞) by exact_mod_cast hrp) hdu.restrict
    simpa only [eLpNorm_restrict_eq_of_support_subset
        (μ := μ) (f := fderiv ℝ u) hdu hsdu, Measure.restrict_apply_univ,
      ENNReal.coe_toReal, M, δ] using h
  calc
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOfLeConst F μ (closure s) r p *
        eLpNorm (fderiv ℝ u) r μ :=
      eLpNorm_le_eLpNorm_fderiv_of_le μ hu hsu hr1 hrn hrecip hs.closure
    _ ≤ eLpNormLESNormFDerivOfLeConst F μ (closure s) r p *
        (eLpNorm (fderiv ℝ u) p μ * M) := by gcongr
    _ = C * eLpNorm (fderiv ℝ u) p μ := by
      simp only [C, ENNReal.coe_mul, ENNReal.coe_toNNReal hM]
      ac_rfl

end MeasureTheory

open MeasureTheory Set Function
open scoped ENNReal NNReal

namespace MeasureTheory

/-- The one-dimensional Poincaré inequality for every finite exponent `p ≥ 1`.
The constant depends only on the bounded set containing the support. Compact support
is derived, and no finite-dimensional or completeness assumption on the codomain is needed. -/
theorem eLpNorm_le_eLpNorm_fderiv_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ → F} {s : Set ℝ}
    (hu : ContDiff ℝ 1 u) (hsupp : support u ⊆ s)
    {p : ℝ≥0} (hp : 1 ≤ p) (hs : Bornology.IsBounded s) :
    eLpNorm u p volume ≤
      ((volume (closure s)).toNNReal : ℝ≥0∞) * eLpNorm (fderiv ℝ u) p volume := by
  let μs : Measure ℝ := volume.restrict (closure s)
  have husupp : support u ⊆ closure s := hsupp.trans subset_closure
  have htsupp : tsupport u ⊆ closure s :=
    closure_minimal husupp isClosed_closure
  have hdsupp : support (deriv u) ⊆ closure s :=
    support_deriv_subset.trans htsupp
  have hcompact : HasCompactSupport u :=
    HasCompactSupport.of_support_subset_isCompact hs.isCompact_closure husupp
  have hvolume : volume (closure s) ≠ ∞ := hs.closure.measure_lt_top.ne
  have humeas : AEStronglyMeasurable u volume := hu.continuous.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (deriv u) volume :=
    (hu.continuous_deriv le_rfl).aestronglyMeasurable
  have hpoint (x : ℝ) : ‖u x‖ₑ ≤ eLpNorm (deriv u) 1 volume := by
    calc
      ‖u x‖ₑ ≤ ∫⁻ y in Iic x, ‖deriv u y‖ₑ :=
        HasCompactSupport.enorm_le_lintegral_Ici_deriv hu hcompact x
      _ ≤ ∫⁻ y, ‖deriv u y‖ₑ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = eLpNorm (deriv u) 1 volume := (eLpNorm_one_eq_lintegral_enorm hdmeas).symm
  have huLp :
      eLpNorm u p μs ≤
        eLpNorm (deriv u) 1 volume * volume (closure s) ^ (1 / (p : ℝ)) := by
    simpa [μs, one_div, smul_eq_mul] using
      (eLpNorm_le_of_ae_enorm_bound (p := (p : ℝ≥0∞)) (μ := μs)
        humeas.restrict (Filter.Eventually.of_forall hpoint))
  have hdLp :
      eLpNorm (deriv u) 1 μs ≤
        eLpNorm (deriv u) p μs * volume (closure s) ^ (1 - 1 / (p : ℝ)) := by
    have hp' : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
    simpa [μs] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μs) hp' hdmeas.restrict)
  have huRestrict : eLpNorm u p μs = eLpNorm u p volume :=
    eLpNorm_restrict_eq_of_support_subset humeas husupp
  have hdRestrict (q : ℝ≥0∞) :
      eLpNorm (deriv u) q μs = eLpNorm (deriv u) q volume :=
    eLpNorm_restrict_eq_of_support_subset hdmeas hdsupp
  have hpowers :
      volume (closure s) ^ (1 - 1 / (p : ℝ)) *
          volume (closure s) ^ (1 / (p : ℝ)) = volume (closure s) := by
    have hexp : (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) = 1 := sub_add_cancel _ _
    rw [← ENNReal.rpow_add_of_add_pos hvolume (1 - 1 / (p : ℝ)) (1 / (p : ℝ))
      (by rw [hexp]; norm_num), hexp, ENNReal.rpow_one]
  have hderiv :
      eLpNorm (deriv u) p volume = eLpNorm (fderiv ℝ u) p volume :=
    eLpNorm_congr_norm_ae hdmeas
      (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ norm_deriv_eq_norm_fderiv)
  calc
    eLpNorm u p volume = eLpNorm u p μs := huRestrict.symm
    _ ≤ eLpNorm (deriv u) 1 volume * volume (closure s) ^ (1 / (p : ℝ)) := huLp
    _ = eLpNorm (deriv u) 1 μs * volume (closure s) ^ (1 / (p : ℝ)) := by
      rw [hdRestrict]
    _ ≤ (eLpNorm (deriv u) p μs * volume (closure s) ^ (1 - 1 / (p : ℝ))) *
          volume (closure s) ^ (1 / (p : ℝ)) :=
      mul_le_mul_left hdLp _
    _ = volume (closure s) * eLpNorm (fderiv ℝ u) p volume := by
      rw [mul_assoc, hpowers, hdRestrict, hderiv, mul_comm]
    _ = ((volume (closure s)).toNNReal : ℝ≥0∞) *
          eLpNorm (fderiv ℝ u) p volume := by
      rw [ENNReal.coe_toNNReal hvolume]

/-- The one-dimensional Poincaré inequality in Euclidean coordinates for every finite
exponent `p ≥ 1`. The constant is the volume of the closure of the bounded support set.
The change of variables preserves both volume and the operator norm of the derivative. -/
theorem eLpNorm_le_eLpNorm_fderiv_euclidean_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ^1 → F} {s : Set (ℝ^1)}
    (hu : ContDiff ℝ 1 u) (hsupp : support u ⊆ s)
    {p : ℝ≥0} (hp : 1 ≤ p) (hs : Bornology.IsBounded s) :
    eLpNorm u p volume ≤
      ((volume (closure s)).toNNReal : ℝ≥0∞) * eLpNorm (fderiv ℝ u) p volume := by
  let e : ℝ ≃ₗᵢ[ℝ] ℝ^1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  have hs' : Bornology.IsBounded (e ⁻¹' s) :=
    e.isometry.antilipschitzWith.isBounded_preimage hs
  have hsupp' : support (u ∘ e) ⊆ e ⁻¹' s := by
    intro x hx
    exact hsupp hx
  have hvolume : volume (closure (e ⁻¹' s)) = volume (closure s) := by
    change volume (closure (e.toHomeomorph ⁻¹' s)) = volume (closure s)
    rw [← e.toHomeomorph.preimage_closure]
    exact e.measurePreserving.measure_preimage isClosed_closure.measurableSet.nullMeasurableSet
  have huNorm : eLpNorm (u ∘ e) p volume = eLpNorm u p volume :=
    eLpNorm_comp_measurePreserving hu.continuous.aestronglyMeasurable e.measurePreserving
  have hdNorm : eLpNorm (fderiv ℝ (u ∘ e)) p volume =
      eLpNorm (fderiv ℝ u) p volume := by
    calc
      eLpNorm (fderiv ℝ (u ∘ e)) p volume =
          eLpNorm ((fderiv ℝ u) ∘ e) p volume := by
        apply eLpNorm_congr_norm_ae
          ((hu.comp e.contDiff).continuous_fderiv one_ne_zero).aestronglyMeasurable
          ((hu.continuous_fderiv one_ne_zero).comp e.continuous).aestronglyMeasurable
        apply Filter.Eventually.of_forall
        intro x
        change ‖fderiv ℝ (u ∘ e.toContinuousLinearEquiv) x‖ = ‖fderiv ℝ u (e x)‖
        rw [e.toContinuousLinearEquiv.comp_right_fderiv]
        exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e
      _ = eLpNorm (fderiv ℝ u) p volume :=
        eLpNorm_comp_measurePreserving
          (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable e.measurePreserving
  have h := eLpNorm_le_eLpNorm_fderiv_real (hu.comp e.contDiff) hsupp' hp hs'
  rwa [hvolume, huNorm, hdNorm] at h

end MeasureTheory

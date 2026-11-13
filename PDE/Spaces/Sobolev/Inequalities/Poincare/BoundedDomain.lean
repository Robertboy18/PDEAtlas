/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import PDE.Spaces.Sobolev.Calculus.Slicing.Coordinate
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.Spaces.Sobolev.Inequalities.Poincare.Closure
import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global

/-!
# Poincaré inequality on bounded domains

On a bounded set `Ω` every `u ∈ H¹₀(Ω)` satisfies `‖u‖_{L²(Ω)} ≤ C Σᵢ ‖∂ᵢ u‖_{L²(Ω)}`, in every
positive dimension (`exists_poincare_H10`). A containing coordinate slab also gives an explicit
constant equal to its width, using one weak derivative.

This is the case `p = 2` of Poincaré's inequality in Evans §5.6.1, Theorem 3. It gives the
coercivity in the energy estimates for the Dirichlet problem, Evans §6.2.2, Theorem 2.

## How it works

We prove each bound for test functions supported in `Ω` and extend it to `H¹₀(Ω)` by density
(`poincare_Wkp0_of_testFunctions`). For `n > 2` the test-function bound is Mathlib's
Gagliardo–Nirenberg–Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le` at
`p = q = 2`, which on a bounded set allows every `q ≤ p*`; we use it through
`eLpNorm_le_sum_eLpNorm_partialDeriv_of_le`. In dimension two `p = 2` is not below `n`, so we take
`p = 1` and `q = 2` instead and bound the `L¹` norms of the derivatives by their `L²` norms with
Hölder on `Ω`. In dimension one Mathlib's `HasCompactSupport.enorm_le_lintegral_Ici_deriv` bounds
`u` pointwise by `‖u'‖_{L¹}`, and two applications of Hölder give the constant `|Ω|`. The slab bound
applies the same one-dimensional estimate (`eLpNorm_le_measure_mul_eLpNorm_deriv`) on each line in
the direction `eᵢ` and integrates over the other coordinates.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, Theorem 3, pp. 279-280; and §6.2.2, Theorem 2,
  pp. 318-319.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Inequalities

/-- A compact function supported in an interval has an explicit Poincaré bound
given by the length of that interval. -/
theorem eLpNorm_le_measure_mul_eLpNorm_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (hs : tsupport f ⊆ Icc a b) :
    eLpNorm f 2 volume ≤ volume (Icc a b) * eLpNorm (deriv f) 2 volume := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hdcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdNorm (p : ℝ≥0∞) : eLpNorm (deriv f) p volume = eLpNorm (deriv f) p μ :=
    (eLpNorm_restrict_eq_of_support_subset hdcont.aestronglyMeasurable
      ((subset_tsupport _).trans (tsupport_deriv_subset.trans hs))).symm
  have hcompare : eLpNorm (deriv f) 1 volume ≤
      eLpNorm (deriv f) 2 volume * volume (Icc a b) ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := μ) (f := deriv f) (p := 1) (q := 2) (by norm_num)
      hdcont.aestronglyMeasurable
    rw [← hdNorm 1, ← hdNorm 2] at h
    simpa only [μ, Measure.restrict_apply_univ, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, div_one, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using h
  have hpoint (x : ℝ) : ‖f x‖ₑ ≤
      eLpNorm (deriv f) 2 volume * volume (Icc a b) ^ (1 / 2 : ℝ) :=
    (HasCompactSupport.enorm_le_lintegral_Ici_deriv hf hc x).trans <|
      (lintegral_mono' Measure.restrict_le_self le_rfl).trans <|
        (eLpNorm_one_eq_lintegral_enorm hdcont.aestronglyMeasurable).symm.trans_le hcompare
  rw [← eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable
    ((subset_tsupport _).trans hs)]
  have h := eLpNorm_le_of_ae_enorm_bound (p := 2) (μ := μ)
    hf.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hpoint)
  have hsqrt : volume (Icc a b) ^ (1 / 2 : ℝ) *
      volume (Icc a b) ^ (1 / 2 : ℝ) = volume (Icc a b) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  simp only [μ, Measure.restrict_apply_univ, ENNReal.toReal_ofNat,
    show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, smul_eq_mul] at h
  exact h.trans_eq (by rw [mul_assoc, hsqrt, mul_comm])

private theorem eLpNorm_two_sq_eq_lintegral
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf

open Slices

/-- A single coordinate slab controls the entire square integral by the
square integral of that coordinate derivative. -/
theorem lintegral_sq_le_measure_sq_mul_partialDeriv
    {n : ℕ} (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {a b : ℝ}
    (hs : tsupport f ⊆ {x | x i ∈ Icc a b}) :
    (∫⁻ x, ‖f x‖ₑ ^ 2) ≤
      volume (Icc a b) ^ 2 * ∫⁻ x, ‖∂[i] f x‖ₑ ^ 2 := by
  have hline (y : ℝ^n) :
      (∫⁻ t, ‖coordinateSlice i f y t‖ₑ ^ 2) ≤
        volume (Icc a b) ^ 2 *
          ∫⁻ t, ‖coordinateDerivativeInSplit i f (y, t)‖ₑ ^ 2 := by
    have hslice := coordinateSlice_contDiff i hf y
    have hsupp : tsupport (coordinateSlice i f y) ⊆ Icc a b := by
      apply closure_minimal ?_ isClosed_Icc
      intro t ht
      have hx := hs (subset_tsupport f ht)
      change (joinCoordinate i (y, t)) i ∈ Icc a b at hx
      simpa only [joinCoordinate_apply_same] using hx
    have h := pow_le_pow_left'
      (eLpNorm_le_measure_mul_eLpNorm_deriv hslice
        (coordinateSlice_hasCompactSupport i hc y) hsupp) 2
    rw [mul_pow, eLpNorm_two_sq_eq_lintegral hslice.continuous.aestronglyMeasurable,
      eLpNorm_two_sq_eq_lintegral
        (hslice.continuous_deriv le_rfl).aestronglyMeasurable] at h
    simpa only [deriv_coordinateSlice i hf] using h
  have hmp : MeasurePreserving (coordinateMeasurableEquiv i).symm
      ((volume : Measure (ℝ^n)).prod volume) (volume : Measure (ℝ^(n + 1))) := by
    simpa only [Measure.volume_eq_prod] using
      MeasurePreserving.symm (coordinateMeasurableEquiv i)
        (measurePreserving_coordinateMeasurableEquiv i)
  have hcoordinate (g : ℝ^(n + 1) → ℝ≥0∞) :
      (∫⁻ p : ℝ^n × ℝ, g (joinCoordinate i p)
        ∂((volume : Measure (ℝ^n)).prod volume)) = ∫⁻ x, g x := by
    simpa only [coordinateMeasurableEquiv_symm_apply] using
      hmp.lintegral_comp_emb (coordinateMeasurableEquiv i).symm.measurableEmbedding g
  have hfprod : AEMeasurable (fun p : ℝ^n × ℝ ↦ ‖coordinateSlice i f p.1 p.2‖ₑ ^ 2)
      ((volume : Measure (ℝ^n)).prod volume) :=
    ((coordinateSlice_product_continuous i hf.continuous).measurable.enorm.pow_const 2).aemeasurable
  have hdprod : AEMeasurable (fun p : ℝ^n × ℝ ↦ ‖coordinateDerivativeInSplit i f p‖ₑ ^ 2)
      ((volume : Measure (ℝ^n)).prod volume) :=
    ((coordinateDerivativeInSplit_continuous i hf).measurable.enorm.pow_const 2).aemeasurable
  calc ∫⁻ x, ‖f x‖ₑ ^ 2
      = ∫⁻ p : ℝ^n × ℝ, ‖coordinateSlice i f p.1 p.2‖ₑ ^ 2
          ∂((volume : Measure (ℝ^n)).prod volume) := (hcoordinate fun x ↦ ‖f x‖ₑ ^ 2).symm
    _ = ∫⁻ y, ∫⁻ t, ‖coordinateSlice i f y t‖ₑ ^ 2 := lintegral_prod _ hfprod
    _ ≤ ∫⁻ y, volume (Icc a b) ^ 2 * ∫⁻ t, ‖coordinateDerivativeInSplit i f (y, t)‖ₑ ^ 2 :=
      lintegral_mono hline
    _ = volume (Icc a b) ^ 2 * ∫⁻ x, ‖∂[i] f x‖ₑ ^ 2 := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (isCompact_Icc.measure_lt_top).ne),
        ← lintegral_prod _ hdprod, ← hcoordinate fun x ↦ ‖∂[i] f x‖ₑ ^ 2]
      rfl


/-- A coordinate slab gives a Poincaré constant equal to its width. -/
theorem eLpNorm_le_measure_mul_eLpNorm_partialDeriv
    {n : ℕ} (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {a b : ℝ}
    (hs : tsupport f ⊆ {x | x i ∈ Icc a b}) :
    eLpNorm f 2 volume ≤ volume (Icc a b) * eLpNorm (∂[i] f) 2 volume := by
  have hd : Continuous (∂[i] f) := hf.continuous_partialDeriv i
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two]
  rw [mul_pow, eLpNorm_two_sq_eq_lintegral hf.continuous.aestronglyMeasurable,
    eLpNorm_two_sq_eq_lintegral hd.aestronglyMeasurable]
  exact lintegral_sq_le_measure_sq_mul_partialDeriv i hf hc hs

end SobolevSpace.Inequalities

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology NNReal Sobolev

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


/-!
## Poincaré inequality on `H¹₀(Ω)` in every positive dimension
-/

/-- The Sobolev-inequality constant specialized to `p = q = 2`. -/
noncomputable def poincareConst (n : ℕ) (Ω : Set (ℝ^n)) : ℝ≥0 :=
  MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ (MeasureTheory.volume : Measure (ℝ^n)) Ω
    (2 : NNReal) (2 : NNReal)

/-- The two-dimensional constant obtained from `W^{1,1} ↪ L²` followed by Hölder on the
bounded support. -/
noncomputable def poincareConstTwo (Ω : Set (ℝ^2)) : ℝ≥0 :=
  ((MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ
      (MeasureTheory.volume : Measure (ℝ^2)) Ω (1 : NNReal) (2 : NNReal) : ℝ≥0∞) *
    (MeasureTheory.volume Ω) ^ (1 / 2 : ℝ)).toNNReal

/-- In one dimension the fundamental theorem of calculus and two applications of Hölder give
`‖u‖₂ ≤ |Ω| ‖u'‖₂` for compactly supported `u`. -/
noncomputable def poincareConstOne (Ω : Set (ℝ^1)) : ℝ≥0 :=
  (MeasureTheory.volume Ω).toNNReal

private theorem poincare_testFunction (hn : 2 < n)
    (hΩbounded : Bornology.IsBounded Ω) (φΩ : TestFunctionOn n Ω) :
    eLpNorm φΩ.1.toFun 2 volume ≤ (poincareConst n Ω : ℝ≥0∞) *
      ∑ i : Fin n, eLpNorm (∂[i] φΩ.1.toFun) 2 volume := by
  let u : ℝ^n → ℝ := φΩ.1.toFun
  have hu : ContDiff ℝ 1 u := φΩ.1.contDiff.of_le (by simp)
  have hsupp : u.support ⊆ Ω := (subset_tsupport u).trans φΩ.2
  have hn0 : 0 < n := lt_trans (by decide : 0 < 2) hn
  have hp_lt : ((2 : NNReal) : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpq : ((2 : NNReal)⁻¹ : ℝ) - (n : ℝ)⁻¹ ≤ ((2 : NNReal) : ℝ)⁻¹ := by
    exact sub_le_self _ (by positivity)
  simpa [poincareConst, u] using
    (SobolevSpace.Inequalities.eLpNorm_le_sum_eLpNorm_partialDeriv_of_le
      (n := n) (u := u) (s := Ω) hu hsupp (p := (2 : NNReal)) (q := (2 : NNReal))
      (hp := by norm_num) (hp_lt := hp_lt) (hpq := hpq) (hs := hΩbounded))

private theorem poincare_testFunction_two {Ω : Set (ℝ^2)}
    (hΩbounded : Bornology.IsBounded Ω)
    (φΩ : TestFunctionOn 2 Ω) :
    eLpNorm φΩ.1.toFun 2 volume ≤ (poincareConstTwo Ω : ℝ≥0∞) *
      ∑ i : Fin 2, eLpNorm (∂[i] φΩ.1.toFun) 2 volume := by
  let u : ℝ^2 → ℝ := φΩ.1.toFun
  let A : ℝ≥0∞ :=
    eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (ℝ^2)) Ω (1 : NNReal) (2 : NNReal)
  let M : ℝ≥0∞ := volume Ω ^ (1 / 2 : ℝ)
  have hu : ContDiff ℝ 1 u := φΩ.1.contDiff.of_le (by simp)
  have hGNS : eLpNorm u 2 volume ≤ A * ∑ i : Fin 2, eLpNorm (∂[i] u) 1 volume := by
    simpa [A, u] using SobolevSpace.Inequalities.eLpNorm_le_sum_eLpNorm_partialDeriv_of_le
      (n := 2) (u := u) (s := Ω) hu ((subset_tsupport u).trans φΩ.2) (p := (1 : NNReal))
      (q := (2 : NNReal)) (hp := by norm_num) (hp_lt := by norm_num) (hpq := by norm_num)
      (hs := hΩbounded)
  have hderiv (i : Fin 2) : eLpNorm (∂[i] u) 1 volume ≤ M * eLpNorm (∂[i] u) 2 volume := by
    have hd := hu.continuous_partialDeriv i
    have hs : (∂[i] u).support ⊆ Ω :=
      (subset_tsupport _).trans ((PDE.tsupport_partialDeriv_subset i).trans φΩ.2)
    rw [← eLpNorm_restrict_eq_of_support_subset (p := 1) hd.aestronglyMeasurable hs,
      ← eLpNorm_restrict_eq_of_support_subset (p := 2) hd.aestronglyMeasurable hs]
    convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Ω) (p := 1) (q := 2)
      (by norm_num) hd.aestronglyMeasurable using 1
    norm_num [M, mul_comm]
  calc _ ≤ A * ∑ i : Fin 2, eLpNorm (∂[i] u) 1 volume := hGNS
    _ ≤ A * ∑ i : Fin 2, M * eLpNorm (∂[i] u) 2 volume := by gcongr with i; exact hderiv i
    _ = _ := by
      rw [← Finset.mul_sum, ← mul_assoc, poincareConstTwo, ENNReal.coe_toNNReal
        (ENNReal.mul_ne_top (by simp) (by simp [hΩbounded.measure_lt_top.ne]))]

private theorem poincare_testFunction_one {Ω : Set (ℝ^1)}
    (hΩbounded : Bornology.IsBounded Ω)
    (φΩ : TestFunctionOn 1 Ω) :
    eLpNorm φΩ.1.toFun 2 volume ≤ (poincareConstOne Ω : ℝ≥0∞) *
      ∑ i : Fin 1, eLpNorm (∂[i] φΩ.1.toFun) 2 volume := by
  let u : ℝ^1 → ℝ := φΩ.1.toFun
  let d : ℝ^1 → ℝ := ∂[0] u
  let μΩ : Measure (ℝ^1) := domainMeasure 1 Ω
  let M : ℝ≥0∞ := volume Ω ^ (1 / 2 : ℝ)
  have hu : ContDiff ℝ 1 u := φΩ.1.contDiff.of_le (by simp)
  have hdcont : Continuous d := hu.continuous_partialDeriv 0
  have hdsupp : d.support ⊆ Ω :=
    (subset_tsupport d).trans ((PDE.tsupport_partialDeriv_subset 0).trans φΩ.2)
  have he := (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)
  have hpoint (x : ℝ^1) : ‖u x‖ₑ ≤ eLpNorm d 1 volume := by
    let t : ℝ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x
    calc ‖u x‖ₑ = ‖(u ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t‖ₑ := by
          simp only [Function.comp_apply, t]
          rw [(PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm_apply_apply]
      _ ≤ ∫⁻ y in Set.Iic t, ‖deriv (u ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) y‖ₑ :=
        HasCompactSupport.enorm_le_lintegral_Ici_deriv
          (hu.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.contDiff)
          (φΩ.1.hasCompactSupport.comp_homeomorph
            (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph) t
      _ ≤ ∫⁻ y, ‖deriv (u ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) y‖ₑ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = eLpNorm (d ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) 1 volume := by
        simp_rw [PDE.deriv_comp_equivOfUnique_symm u _ (hu.differentiable_one.differentiableAt)]
        simp [eLpNorm_one_eq_lintegral_enorm
          (f := d ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm)
          (hdcont.aestronglyMeasurable.comp_measurePreserving he), d]
      _ = _ := eLpNorm_comp_measurePreserving hdcont.aestronglyMeasurable he
  have hrestrict {f : ℝ^1 → ℝ} (hf : Continuous f) (hs : f.support ⊆ Ω) (p : ℝ≥0∞) :
      eLpNorm f p volume = eLpNorm f p μΩ :=
    (eLpNorm_restrict_eq_of_support_subset hf.aestronglyMeasurable hs).symm
  have hM_sq : M * M = volume Ω := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [poincareConstOne, ENNReal.coe_toNNReal hΩbounded.measure_lt_top.ne, Fin.sum_univ_one]
  change eLpNorm u 2 volume ≤ volume Ω * eLpNorm d 2 volume
  calc eLpNorm u 2 volume = eLpNorm u 2 μΩ :=
        hrestrict hu.continuous ((subset_tsupport u).trans φΩ.2) 2
    _ ≤ eLpNormEssSup u μΩ * M := by
        simpa [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable, M, μΩ, domainMeasure]
          using eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μΩ) (p := 2) (q := ∞) (by simp)
            hu.continuous.aestronglyMeasurable
    _ ≤ eLpNorm d 1 μΩ * M := by
        rw [← hrestrict hdcont hdsupp]
        gcongr
        exact eLpNormEssSup_le_of_ae_enorm_bound (.of_forall hpoint)
    _ ≤ eLpNorm d 2 μΩ * M * M := by
        gcongr
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μΩ) (f := d) (p := 1) (q := 2)
          (by norm_num) hdcont.aestronglyMeasurable using 1
        norm_num [M, μΩ, domainMeasure]
    _ = _ := by rw [mul_assoc, hM_sq, ← hrestrict hdcont hdsupp, mul_comm]

/-- Poincaré inequality on `H¹₀(Ω)` for `n > 2` and bounded `Ω`:
`‖u‖_{L²(Ω)} ≤ poincareConst n Ω * ∑ i, ‖∂ᵢ u‖_{L²(Ω)}`, from the `p = 2` Sobolev inequality. -/
theorem norm_baseCoord_le_poincareConst_mul_sum_derivCoord (hn : 2 < n)
    (hΩbounded : Bornology.IsBounded Ω) :
    ∀ u : H¹₀(Ω),
      ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))‖ ≤
        (poincareConst n Ω : ℝ) *
          ∑ i : Fin n,
            ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
                (singleDerivIndex (n := n) i))‖ := by
  intro u
  apply poincare_Wkp0_of_testFunctions (poincareConst n Ω) ?_ u
  exact poincare_testFunction (n := n) (Ω := Ω) hn hΩbounded

/-- Poincaré inequality on `H¹₀(Ω)` in dimension two.  This is the critical Sobolev case:
`W^{1,1} ↪ L²` controls the function, and bounded support converts the first derivatives from
`L²` to `L¹`. -/
theorem norm_baseCoord_le_poincareConstTwo_mul_sum_derivCoord {Ω : Set (ℝ^2)}
    (hΩbounded : Bornology.IsBounded Ω) :
    ∀ u : H¹₀(Ω),
      ‖(((u : H¹(Ω)) : WkpAmbientOn 2 1 2 Ω) (baseIndex 2 1))‖ ≤
        (poincareConstTwo Ω : ℝ) *
          ∑ i : Fin 2,
            ‖(((u : H¹(Ω)) : WkpAmbientOn 2 1 2 Ω)
                (singleDerivIndex (n := 2) i))‖ := by
  intro u
  apply poincare_Wkp0_of_testFunctions (poincareConstTwo Ω) ?_ u
  exact poincare_testFunction_two hΩbounded

/-- Poincaré inequality on `H¹₀(Ω)` in dimension one, obtained from the fundamental theorem of
calculus and Hölder on the bounded domain. -/
theorem norm_baseCoord_le_poincareConstOne_mul_sum_derivCoord {Ω : Set (ℝ^1)}
    (hΩbounded : Bornology.IsBounded Ω) :
    ∀ u : H¹₀(Ω),
      ‖(((u : H¹(Ω)) : WkpAmbientOn 1 1 2 Ω) (baseIndex 1 1))‖ ≤
        (poincareConstOne Ω : ℝ) *
          ∑ i : Fin 1,
            ‖(((u : H¹(Ω)) : WkpAmbientOn 1 1 2 Ω)
                (singleDerivIndex (n := 1) i))‖ := by
  intro u
  apply poincare_Wkp0_of_testFunctions (poincareConstOne Ω) ?_ u
  exact poincare_testFunction_one hΩbounded

/-- Poincaré inequality on bounded domains in every positive dimension: if `0 < n` and `Ω` is
bounded, there is `C`, depending on `n` and `Ω`, with `‖u‖_{L²(Ω)} ≤ C * ∑ i, ‖∂ᵢ u‖_{L²(Ω)}`
for every `u ∈ H¹₀(Ω)`. -/
theorem exists_poincare_H10 (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0, ∀ u : H¹₀(Ω),
      ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))‖ ≤
        (C : ℝ) *
          ∑ i : Fin n,
            ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
                (singleDerivIndex (n := n) i))‖ := by
  by_cases h1 : n = 1
  · subst n
    exact ⟨poincareConstOne Ω, norm_baseCoord_le_poincareConstOne_mul_sum_derivCoord hΩbounded⟩
  by_cases h2 : n = 2
  · subst n
    exact ⟨poincareConstTwo Ω, norm_baseCoord_le_poincareConstTwo_mul_sum_derivCoord hΩbounded⟩
  have h3 : 2 < n := by omega
  exact ⟨poincareConst n Ω,
    norm_baseCoord_le_poincareConst_mul_sum_derivCoord (n := n) (Ω := Ω) h3 hΩbounded⟩

/-- The width of any containing coordinate slab controls the displacement
by one weak derivative throughout the zero-boundary Sobolev space. -/
theorem norm_baseCoord_le_measure_mul_derivCoord_of_slab
    {n : ℕ} {Ω : Set (ℝ^(n + 1))} (i : Fin (n + 1)) {a b : ℝ}
    (hΩ : Ω ⊆ {x | x i ∈ Icc a b}) (u : H¹₀(Ω)) :
    ‖baseCoordCLM u‖ ≤ (volume (Icc a b)).toReal * ‖derivCoordCLM i u‖ := by
  apply isClosed_property denseRange_testFunctionToH10Linear
    (isClosed_le (by fun_prop) (by fun_prop)) ?_ u
  intro φ
  let U := testFunctionToH10 φ
  change ‖baseCoordCLM U‖ ≤ (volume (Icc a b)).toReal * ‖derivCoordCLM i U‖
  have hbase : eLpNorm φ.1.toFun 2 volume = eLpNorm (baseCoordCLM U) 2
      (domainMeasure (n + 1) Ω) := by
    calc
      _ = eLpNorm φ.1.toFun 2 (domainMeasure (n + 1) Ω) :=
        (eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 2)
          (f := φ.1.toFun) φ.1.contDiff.continuous.aestronglyMeasurable
          ((subset_tsupport _).trans φ.2)).symm
      _ = _ := (eLpNorm_congr_ae (baseCoordCLM_testFunction_apply_ae φ)).symm
  have hderiv : eLpNorm (∂[i] φ.1.toFun) 2 volume = eLpNorm (derivCoordCLM i U) 2
      (domainMeasure (n + 1) Ω) := by
    have hs : Function.support (∂[i] φ.1.toFun) ⊆ Ω :=
      (subset_tsupport _).trans ((PDE.tsupport_partialDeriv_subset i).trans φ.2)
    have hd : Continuous (∂[i] φ.1.toFun) :=
      (φ.1.contDiff.of_le (by simp) : ContDiff ℝ 1 φ.1.toFun).continuous_partialDeriv i
    calc
      _ = eLpNorm (∂[i] φ.1.toFun) 2 (domainMeasure (n + 1) Ω) :=
        (eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 2)
          (f := ∂[i] φ.1.toFun) hd.aestronglyMeasurable hs).symm
      _ = _ := (eLpNorm_congr_ae (derivCoordCLM_testFunction_apply_ae i φ)).symm
  have h := Inequalities.eLpNorm_le_measure_mul_eLpNorm_partialDeriv i
    (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport (φ.2.trans hΩ)
  simp only [← TestFunction.toFun_eq_coe] at h
  rw [hbase, hderiv] at h
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (isCompact_Icc.measure_lt_top).ne (Lp.eLpNorm_ne_top _)) h
  simpa only [Lp.norm_def, ENNReal.toReal_mul] using hreal

end GraphSpace

end SobolevSpace

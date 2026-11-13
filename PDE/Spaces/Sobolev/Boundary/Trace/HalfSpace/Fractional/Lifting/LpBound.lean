/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Regularity
import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral.Lebesgue

/-!
# Function energy of the mollified extension

Mollification contracts each horizontal `Lᵖ` slice. A height multiplier bounded
by `C` and vanishing above `T` therefore gives at most `T Cᵖ` times the boundary
function energy. Applied to the height cutoff, this gives the factor
two for the mollified extension. These estimates include zero-dimensional
boundary data and the endpoint `p = 1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem lintegral_enorm_mollify_rpow_le (μ : Mollifier n)
    {t : ℝ} (ht : 0 < t) (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume) :
    (∫⁻ x, ‖mollifyVector μ t g x‖ₑ ^ p.toReal) ≤ ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hm : AEStronglyMeasurable (mollifyVector μ t g) volume :=
    (mollifyVector_contDiff_of_pos μ ht g
    (hg.locallyIntegrable (Fact.out : 1 ≤ p))).continuous.aestronglyMeasurable
  have hb := ENNReal.rpow_le_rpow
    (MollifyLp.eLpNorm_mollifyVector_le μ ht hp hg) hpr.le
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one] using hb

/-- A bounded height multiplier supported below `T` contributes at most `T Cᵖ`
times the boundary function energy. The nonnegative integral inequality does
not require measurability of the multiplier. -/
theorem lintegral_enorm_height_mul_mollify_rpow_le (μ : Mollifier n)
    (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume)
    {a : ℝ → ℝ} {C T : ℝ≥0} (hC : ∀ t, 0 < t → ‖a t‖ ≤ C)
    (hT : ∀ t, (T : ℝ) ≤ t → a t = 0) :
    (∫⁻ z in ℝ^(n + 1)₊,
      ‖a (splitTangentialNormal z).2 •
        mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1‖ₑ ^
          p.toReal) ≤
      (T : ℝ≥0∞) * (C : ℝ≥0∞) ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  let B := (C : ℝ≥0∞) ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal
  have hs (t : ℝ) (ht : 0 < t) :
      (∫⁻ x, ‖a t • mollifyVector μ t g x‖ₑ ^ p.toReal) ≤
        (Iio (T : ℝ)).indicator (fun _ ↦ B) t := by
    by_cases htT : t < T
    · rw [indicator_of_mem (show t ∈ Iio (T : ℝ) from htT)]
      calc
        _ ≤ ∫⁻ x, ((C : ℝ≥0∞) * ‖mollifyVector μ t g x‖ₑ) ^ p.toReal := by
          apply lintegral_mono
          intro x
          apply ENNReal.rpow_le_rpow _ hpr.le
          rw [enorm_smul]
          exact mul_le_mul' (by exact_mod_cast hC t ht) le_rfl
        _ = (C : ℝ≥0∞) ^ p.toReal *
            ∫⁻ x, ‖mollifyVector μ t g x‖ₑ ^ p.toReal := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
          exact lintegral_const_mul' _ _ (by finiteness)
        _ ≤ B := mul_le_mul' le_rfl (lintegral_enorm_mollify_rpow_le μ ht hp hg)
    · simp [hT t (le_of_not_gt htT), ENNReal.zero_rpow_of_pos hpr]
  calc
    _ = ∫⁻ z, ‖a z.2 • mollifyVector μ z.2 g z.1‖ₑ ^ p.toReal
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure) := by
      rw [← lintegral_joinTangentialNormal_eq_lintegral_upper]
      simp only [split_joinTangentialNormal]
    _ = ∫⁻ z : ℝ × ℝ^n, ‖a z.1 • mollifyVector μ z.1 g z.2‖ₑ ^ p.toReal
        ∂(positiveNormalMeasure.prod volume) := (lintegral_prod_swap _).symm
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, ‖a t • mollifyVector μ t g x‖ₑ ^ p.toReal :=
      lintegral_prod_le _
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (Iio (T : ℝ)).indicator (fun _ ↦ B) t :=
      setLIntegral_mono (measurable_const.indicator measurableSet_Iio) hs
    _ = (T : ℝ≥0∞) * (C : ℝ≥0∞) ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
      rw [lintegral_indicator measurableSet_Iio, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iio]
      have hI : Iio (T : ℝ) ∩ Ioi (0 : ℝ) = Ioo 0 (T : ℝ) := by
        ext t
        exact and_comm
      rw [hI, Real.volume_Ioo]
      simp [B, mul_comm, mul_assoc]

private theorem aestronglyMeasurable_height_mul_mollify (μ : Mollifier n)
    {g : ℝ^n → F} (hg : LocallyIntegrable g volume) {a : ℝ → ℝ} (ha : Measurable a) :
    AEStronglyMeasurable (fun z : ℝ^(n + 1) ↦
      a (splitTangentialNormal z).2 •
        mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1)
      (volume.restrict ℝ^(n + 1)₊) := by
  have hs : Continuous (@splitTangentialNormal n) :=
    tangentialNormalContinuousLinearEquiv.continuous
  have hm : ContinuousOn (fun z : ℝ^(n + 1) ↦
      mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1)
      ℝ^(n + 1)₊ :=
    (contDiffOn_mollifyVector_scale μ hg).continuousOn.comp
      (hs.snd.prodMk hs.fst).continuousOn (fun z hz ↦ by
        rw [upper_eq_preimage_split_snd_Ioi] at hz
        exact ⟨hz.2, mem_univ _⟩)
  exact (ha.comp hs.snd.measurable).aestronglyMeasurable.smul
    (hm.aestronglyMeasurable (HalfSpace.measurableSet_upper (n + 1)))

/-- A measurable height multiplier bounded by `C` and vanishing above `T`
gives the `Lᵖ` bound `T^(1/p) C` for the height-dependent mollification. -/
theorem eLpNorm_height_smul_mollifyVector_le (μ : Mollifier n)
    (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume)
    {a : ℝ → ℝ} (ha : Measurable a) {C T : ℝ≥0}
    (hC : ∀ t, 0 < t → ‖a t‖ ≤ C) (hT : ∀ t, (T : ℝ) ≤ t → a t = 0) :
    eLpNorm (fun z : ℝ^(n + 1) ↦
      a (splitTangentialNormal z).2 •
        mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1)
      p (volume.restrict ℝ^(n + 1)₊) ≤
      (T : ℝ≥0∞) ^ (1 / p.toReal) * C * eLpNorm g p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hmeas := aestronglyMeasurable_height_mul_mollify μ
    (hg.locallyIntegrable (Fact.out : 1 ≤ p)) ha
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hmeas,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable]
  have hb := ENNReal.rpow_le_rpow
    (lintegral_enorm_height_mul_mollify_rpow_le μ hp hg hC hT)
    (one_div_nonneg.mpr hpr.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpr.le),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpr.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpr.ne', ENNReal.rpow_one] at hb
  exact hb

/-- Bounded measurable height multipliers with bounded positive-height support
turn `Lᵖ` boundary data into `Lᵖ` functions on the upper half-space. -/
theorem memLp_height_smul_mollifyVector (μ : Mollifier n)
    (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume)
    {a : ℝ → ℝ} (ha : Measurable a) {C T : ℝ≥0}
    (hC : ∀ t, 0 < t → ‖a t‖ ≤ C) (hT : ∀ t, (T : ℝ) ≤ t → a t = 0) :
    MemLp (fun z : ℝ^(n + 1) ↦
      a (splitTangentialNormal z).2 •
        mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1)
      p (volume.restrict ℝ^(n + 1)₊) := by
  apply lt_of_le_of_lt (eLpNorm_height_smul_mollifyVector_le μ hp hg ha hC hT)
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr ENNReal.toReal_nonneg)
      ENNReal.coe_ne_top) ENNReal.coe_lt_top) hg.eLpNorm_lt_top

/-- The height cutoff costs at most a factor of two in function energy,
in every boundary dimension and for every finite exponent `p ≥ 1`. -/
theorem lintegral_enorm_mollifiedExtension_rpow_le (μ : Mollifier n)
    (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume) :
    (∫⁻ z in ℝ^(n + 1)₊, ‖mollifiedExtension μ g z‖ₑ ^ p.toReal) ≤
      2 * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
  have hC (t : ℝ) (_ : 0 < t) : ‖heightCutoff t‖ ≤ (1 : ℝ≥0) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (heightCutoff_nonneg t), NNReal.coe_one]
      using heightCutoff_le_one t
  have hT (t : ℝ) (ht : (2 : ℝ≥0) ≤ t) : heightCutoff t = 0 :=
    heightCutoff_eq_zero (ht.trans (le_abs_self t))
  simpa only [mollifiedExtension, ENNReal.coe_ofNat, ENNReal.coe_one, ENNReal.one_rpow,
    mul_one] using lintegral_enorm_height_mul_mollify_rpow_le μ hp hg hC hT

/-- The mollified extension has `Lᵖ` norm at most `2^(1/p)` times the boundary norm. -/
theorem eLpNorm_mollifiedExtension_le (μ : Mollifier n)
    (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume) :
    eLpNorm (mollifiedExtension μ g) p (volume.restrict ℝ^(n + 1)₊) ≤
      (2 : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm g p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
    (aestronglyMeasurable_mollifiedExtension μ (hg.locallyIntegrable (Fact.out : 1 ≤ p))),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable]
  have hb := ENNReal.rpow_le_rpow (lintegral_enorm_mollifiedExtension_rpow_le μ hp hg)
    (one_div_nonneg.mpr (ENNReal.toReal_nonneg (a := p)))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _
    (one_div_nonneg.mpr ENNReal.toReal_nonneg)] using hb

/-- The mollified extension of finite-exponent `Lᵖ` boundary data belongs
to `Lᵖ` on the upper half-space. -/
theorem memLp_mollifiedExtension (μ : Mollifier n)
    (hp : p ≠ ∞) {g : ℝ^n → F} (hg : MemLp g p volume) :
    MemLp (mollifiedExtension μ g) p (volume.restrict ℝ^(n + 1)₊) := by
  exact (eLpNorm_mollifiedExtension_le μ hp hg).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      (one_div_nonneg.mpr ENNReal.toReal_nonneg) (by norm_num)) hg.eLpNorm_lt_top)

end SobolevSpace.Trace.HalfSpace

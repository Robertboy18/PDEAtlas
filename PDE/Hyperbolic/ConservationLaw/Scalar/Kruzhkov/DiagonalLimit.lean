/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Translation errors in the spacetime diagonal limit

Strong continuity of translations in `L¹` controls the error made by replacing the second
state in a doubled entropy integral by its value on the diagonal. Averaging the translation
error against a shrinking spacetime mollifier makes it tend to zero.

All integral convergence statements carry integrability hypotheses. They apply to arbitrary
measurable representatives.

The limit is the passage `ε → 0` in (47)-(48) of Evans, §11.4.3, step 3 of the proof of
Theorem 3, where Evans uses the `L¹_loc` convergence of the translated states.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 3, equations (47)-(48).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open PDE.Common SobolevSpace.Approximation
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- The `L¹` translation defect is a continuous function of the spacetime displacement. -/
theorem continuous_integral_norm_translate_sub {f : ℝ^2 → ℝ} (hf : Integrable f volume) :
    Continuous (fun h : ℝ^2 ↦ ∫ x, ‖f (x - h) - f x‖) := by
  let maps : ℝ^2 → C(ℝ^2, ℝ^2) := fun h ↦ ⟨fun x ↦ x - h, continuous_id.sub continuous_const⟩
  have hm (h : ℝ^2) : MeasurePreserving (maps h) volume volume :=
    measurePreserving_sub_right volume h
  let w : Lp ℝ 1 (volume : Measure ℝ^2) := hf.toL1 f
  have hw : (w : ℝ^2 → ℝ) =ᵐ[volume] f := hf.coeFn_toL1
  have hmaps : Continuous maps :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  have hc : Continuous (fun h ↦ Lp.compMeasurePreserving (maps h) (hm h) w) :=
    continuous_const.compMeasurePreservingLp hmaps hm (by norm_num)
  have heq (h : ℝ^2) : ‖Lp.compMeasurePreserving (maps h) (hm h) w - w‖ =
        ∫ x, ‖f (x - h) - f x‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (maps h) (hm h) w) w,
      Lp.coeFn_compMeasurePreserving w (hm h),
      (hm h).quasiMeasurePreserving.ae_eq_comp hw, hw] with x hsub htrans hshift hx
    rw [hsub, Pi.sub_apply, htrans, hshift, hx]
    rfl
  exact ((hc.sub continuous_const).norm).congr heq

/-- Every fixed translation error is integrable, independently of a representative choice. -/
theorem integrable_norm_translate_sub {f : ℝ^2 → ℝ} (hf : Integrable f volume) (h : ℝ^2) :
    Integrable (fun x ↦ ‖f (x - h) - f x‖) volume :=
  ((hf.comp_sub_right h).sub hf).norm

/-- The mollifier-weighted translation error is integrable in the displacement variable. -/
theorem integrable_mollifier_translation_error {f : ℝ^2 → ℝ}
    (hf : Integrable f volume) (μ : Mollifier 2) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun h ↦ scaled μ ε h * (∫ x, ‖f (x - h) - f x‖)) volume :=
  ((scaled_contDiff μ).continuous.mul
    (continuous_integral_norm_translate_sub hf)).integrable_of_hasCompactSupport
      ((scaled_hasCompactSupport μ hε).mul_right)

/-- Averaging the `L¹` translation defect against a shrinking spacetime mollifier gives zero.
This is the diagonal convergence estimate before multiplying by bounded test derivatives. -/
theorem tendsto_mollifier_translation_error {f : ℝ^2 → ℝ} (hf : Integrable f volume)
    (μ : Mollifier 2) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ h, scaled μ (ε n) h * (∫ x, ‖f (x - h) - f x‖)) atTop (𝓝 0) := by
  have hc := (continuous_integral_norm_translate_sub hf).comp continuous_neg
  have h := mollify_tendsto_of_continuous μ hc ε hε hlim (0 : ℝ^2)
  simpa [mollify, convolution] using h

/-- Change from two spacetime points to a point and their displacement. -/
def diagonalChange : (ℝ^2 × ℝ^2) ≃ₜ (ℝ^2 × ℝ^2) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)

/-- The diagonal change of variables preserves product Lebesgue measure. -/
theorem measurePreserving_diagonalChange :
    MeasurePreserving diagonalChange volume volume := by
  rw [Measure.volume_eq_prod]
  convert ((MeasurePreserving.id (volume : Measure ℝ^2)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ^2))).comp
      (measurePreserving_prod_sub volume volume) using 1
  ext1 p
  change (p.1, p.1 - p.2) = (p.1, -(p.2 - p.1))
  simp

/-- An integrable kernel and state give an integrable two-point translation error. -/
theorem integrable_kernel_error {f ρ : ℝ^2 → ℝ}
    (hf : Integrable f volume) (hρ : Integrable ρ volume) :
    Integrable (fun p : ℝ^2 × ℝ^2 ↦ ρ (p.1 - p.2) * ‖f p.2 - f p.1‖) volume := by
  have hfirst := (measurePreserving_sub_prod volume volume).integrable_comp_of_integrable
    (hρ.norm.mul_prod hf.norm)
  have hsecond := measurePreserving_diagonalChange.integrable_comp_of_integrable
    (hf.norm.mul_prod hρ.norm)
  rw [← Measure.volume_eq_prod] at hfirst
  have hmρ := (hρ.aestronglyMeasurable.comp_snd).comp_measurePreserving
    measurePreserving_diagonalChange
  have hmf : AEStronglyMeasurable
      (fun p : ℝ^2 × ℝ^2 ↦ f p.2 - f p.1) volume := by
    rw [Measure.volume_eq_prod]
    exact hf.aestronglyMeasurable.comp_snd.sub hf.aestronglyMeasurable.comp_fst
  refine (hfirst.add hsecond).mono' (hmρ.mul hmf.norm) ?_
  filter_upwards [] with p
  change ‖ρ (p.1 - p.2) * ‖f p.2 - f p.1‖‖ ≤ ‖ρ (p.1 - p.2)‖ * ‖f p.2‖ + ‖f p.1‖ * ‖ρ (p.1 - p.2)‖
  rw [norm_mul, norm_norm]
  calc
    _ ≤ ‖ρ (p.1 - p.2)‖ * (‖f p.2‖ + ‖f p.1‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- Fubini and the diagonal change of variables identify the two-point error with an
average of `L¹` translation errors. -/
theorem integral_kernel_error {f ρ : ℝ^2 → ℝ}
    (hf : Integrable f volume) (hρ : Integrable ρ volume) :
    (∫ p : ℝ^2 × ℝ^2, ρ (p.1 - p.2) * ‖f p.2 - f p.1‖) = ∫ h, ρ h * (∫ x, ‖f (x - h) - f x‖) := by
  have hi := measurePreserving_diagonalChange.integrable_comp_of_integrable
    (integrable_kernel_error hf hρ)
  have heq := measurePreserving_diagonalChange.integral_comp diagonalChange.measurableEmbedding
    (fun p : ℝ^2 × ℝ^2 ↦ ρ (p.1 - p.2) * ‖f p.2 - f p.1‖)
  change Integrable (fun p : ℝ^2 × ℝ^2 ↦
    ρ (p.1 - (p.1 - p.2)) * ‖f (p.1 - p.2) - f p.1‖) volume at hi
  change (∫ p : ℝ^2 × ℝ^2, ρ (p.1 - (p.1 - p.2)) * ‖f (p.1 - p.2) - f p.1‖) = _ at heq
  simp only [sub_sub_cancel] at hi heq
  rw [Measure.volume_eq_prod] at hi
  rw [← heq, Measure.volume_eq_prod, integral_prod_symm _ hi]
  simp only [integral_const_mul]

/-- The two-point spacetime translation error vanishes for shrinking mollifiers. -/
theorem tendsto_integral_kernel_error {f : ℝ^2 → ℝ} (hf : Integrable f volume) (μ : Mollifier 2)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ p : ℝ^2 × ℝ^2,
      scaled μ (ε n) (p.1 - p.2) * ‖f p.2 - f p.1‖) atTop (𝓝 0) := by
  have hi n : Integrable (scaled μ (ε n)) volume :=
    (scaled_contDiff μ).continuous.integrable_of_hasCompactSupport
      (scaled_hasCompactSupport μ (hε n))
  simp_rw [integral_kernel_error hf (hi _)]
  exact tendsto_mollifier_translation_error hf μ hε hlim

/-- Multiplying an integrable density by an integrable diagonal kernel preserves
integrability on the product space. -/
theorem integrable_kernel_left {g ρ : ℝ^2 → ℝ}
    (hg : Integrable g volume) (hρ : Integrable ρ volume) :
    Integrable (fun p : ℝ^2 × ℝ^2 ↦ ρ (p.1 - p.2) * g p.1) volume := by
  have hi := measurePreserving_diagonalChange.integrable_comp_of_integrable (hg.mul_prod hρ)
  simpa [diagonalChange, Function.comp_def, mul_comm] using hi

/-- The mass of the diagonal kernel factors out of a density depending on one point. -/
theorem integral_kernel_left (g ρ : ℝ^2 → ℝ) :
    (∫ p : ℝ^2 × ℝ^2, ρ (p.1 - p.2) * g p.1) = (∫ h, ρ h) * (∫ x, g x) := by
  have h := measurePreserving_diagonalChange.integral_comp
    diagonalChange.measurableEmbedding (fun p : ℝ^2 × ℝ^2 ↦ g p.1 * ρ p.2)
  change (∫ p : ℝ^2 × ℝ^2, g p.1 * ρ (p.1 - p.2)) = ∫ p : ℝ^2 × ℝ^2, g p.1 * ρ p.2 at h
  rw [Measure.volume_eq_prod, integral_prod_mul] at h
  simpa only [mul_comm, Measure.volume_eq_prod] using h

/-- An integrable kernel error controls the difference between the two tested integrals. -/
theorem norm_integral_sub_le_kernel_error {f g ρ : ℝ^2 → ℝ} {F : ℝ^2 × ℝ^2 → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) (hρ : Integrable ρ volume)
    (hmass : ∫ h, ρ h = 1) (hF : Integrable F volume) (C : ℝ)
    (herr : ∀ᵐ p ∂volume, ‖F p - ρ (p.1 - p.2) * g p.1‖ ≤ C * (ρ (p.1 - p.2) * ‖f p.2 - f p.1‖)) :
    ‖(∫ p, F p) - ∫ x, g x‖ ≤ C * ∫ p : ℝ^2 × ℝ^2, ρ (p.1 - p.2) * ‖f p.2 - f p.1‖ := by
  have hi := integrable_kernel_left hg hρ
  have hm : (∫ p : ℝ^2 × ℝ^2, ρ (p.1 - p.2) * g p.1) =
      ∫ x, g x := by rw [integral_kernel_left, hmass, one_mul]
  have hd : Integrable (fun p : ℝ^2 × ℝ^2 ↦ ‖F p - ρ (p.1 - p.2) * g p.1‖)
      volume := (hF.sub hi).norm
  have he : Integrable (fun p : ℝ^2 × ℝ^2 ↦ C * (ρ (p.1 - p.2) * ‖f p.2 - f p.1‖)) volume :=
    (integrable_kernel_error hf hρ).const_mul C
  rw [← hm, ← integral_sub hF hi]
  calc
    _ ≤ ∫ p : ℝ^2 × ℝ^2, ‖F p - ρ (p.1 - p.2) * g p.1‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ^2 × ℝ^2, C * (ρ (p.1 - p.2) * ‖f p.2 - f p.1‖) := integral_mono_ae hd he herr
    _ = _ := integral_const_mul _ _

/-- A kernel error controlled by the translation defect of an `L¹` function vanishes.
Only an eventual bound is needed, so the tests may be restricted to small scales. -/
theorem tendsto_integral_of_kernel_error {f g : ℝ^2 → ℝ} (hf : Integrable f volume)
    (hg : Integrable g volume) (μ : Mollifier 2) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (F : ℕ → ℝ^2 × ℝ^2 → ℝ) (C : ℝ)
    (hF : ∀ᶠ n in atTop, Integrable (F n) volume)
    (herror : ∀ᶠ n in atTop, ∀ᵐ p ∂volume, ‖F n p - scaled μ (ε n) (p.1 - p.2) * g p.1‖ ≤
      C * (scaled μ (ε n) (p.1 - p.2) * ‖f p.2 - f p.1‖)) :
    Tendsto (fun n ↦ ∫ p, F n p) atTop (𝓝 (∫ x, g x)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' (a := fun n ↦ C * ∫ p : ℝ^2 × ℝ^2,
    scaled μ (ε n) (p.1 - p.2) * ‖f p.2 - f p.1‖)
  · filter_upwards [hF, herror] with n hn herr
    exact norm_integral_sub_le_kernel_error hf hg
      ((scaled_contDiff μ).continuous.integrable_of_hasCompactSupport
        (scaled_hasCompactSupport μ (hε n))) (scaled_integral_one μ (hε n)) hn C herr
  · simpa using (tendsto_integral_kernel_error hf μ hε hlim).const_mul C

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

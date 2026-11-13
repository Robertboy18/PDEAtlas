/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.Inequalities.Ladyzhenskaya.Smooth
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Analysis.MeasureTheory.Lp.IntegralPower
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Ladyzhenskaya's inequality on `H¹(ℝ³)`

Every `u ∈ H¹(ℝ³)` lies in `L⁴` with

`‖u‖₄⁴ ≤ ‖u‖₂ ‖∂₀u‖₂ ‖∂₁u‖₂ ‖∂₂u‖₂`.

Smooth compactly supported functions are dense in `H¹(ℝ³)`, so a subsequence of approximants
converges almost everywhere, and Fatou's lemma passes the smooth inequality to the limit; the
right side is continuous in the `H¹` norm. The arithmetic-geometric mean inequality for the
four factors `‖u‖₂², ‖∂₀u‖₂², ‖∂₁u‖₂², ‖∂₂u‖₂²` turns this into the energy form

`‖u‖₄² ≤ ¼ ‖u‖²_{H¹}`, with `‖u‖²_{H¹} = ‖u‖₂² + ‖∇u‖₂²`,

so the inclusion `l4EmbeddingThree : H¹(ℝ³) → L⁴(ℝ³)` has operator norm at most `1/2`. By the
three-term arithmetic-geometric mean inequality the product form also gives
`‖u‖₄⁴ ≤ 3^{-3/2} ‖u‖₂ ‖∇u‖₂³`. For comparison, Hölder's inequality with Talenti's sharp
Sobolev constant gives `‖u‖₄² ≤ (2π)⁻¹ ‖u‖²_{H¹}`, about `0.159` against `1/4` here.

## Main results

* `lintegral_enorm_pow_four_le_H1`, `eLpNorm_four_pow_four_le_H1`: the product form.
* `memLp_four_H1`: `H¹(ℝ³) ⊆ L⁴(ℝ³)`.
* `toReal_eLpNorm_four_pow_four_le_H1`, `toReal_eLpNorm_four_sq_le_H1`,
  `toReal_eLpNorm_four_pow_eight_le_H1`: the real product, energy and gradient forms.
* `l4EmbeddingThree`, `coe_l4EmbeddingThree`, `norm_l4EmbeddingThree_le`: the bounded inclusion
  into `L⁴`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Inequalities

/-- Lower Lebesgue integral of a natural power of the norm as a power of `eLpNorm`. -/
private theorem lintegral_enorm_pow_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ x, ‖f x‖ₑ ^ n ∂μ = eLpNorm f n μ ^ n := by
  rw [← lintegral_ofReal_norm_pow_eq_eLpNorm_pow hf hn]
  refine lintegral_congr fun x ↦ ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The whole-space domain measure is Lebesgue measure. -/
private theorem domainMeasure_univ : domainMeasure 3 (univ : Set (ℝ^3)) = volume := by
  simp [domainMeasure]

/-- The base coordinate of a smooth compactly supported element has the `L²` norm of the
function. -/
private theorem norm_base_mk {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) :
    ‖wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2)
      (Ω := univ) f hf hcs)‖ = (eLpNorm f 2 volume).toReal := by
  have h := norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal (n := 3) (k := 1)
    (p := 2) (Ω := univ) f hf hcs (baseIndex 3 1)
  simpa [baseIndex_toList, iteratedPartialDeriv, domainMeasure_univ] using h

/-- A derivative coordinate of a smooth compactly supported element has the `L²` norm of the
classical partial derivative. -/
private theorem norm_deriv_mk {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (j : Fin 3) :
    ‖wkpCoordinateCLM (singleDerivIndex 3 j) (mkWkpSpaceOnOfContDiff (n := 3) (k := 1)
      (p := 2) (Ω := univ) f hf hcs)‖ = (eLpNorm (fun x ↦ (∂[j] f) x) 2 volume).toReal := by
  have h := norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal (n := 3) (k := 1)
    (p := 2) (Ω := univ) f hf hcs (singleDerivIndex 3 j)
  simpa [singleDerivIndex_toList, iteratedPartialDeriv, domainMeasure_univ] using h

/-- Ladyzhenskaya's inequality for a smooth compactly supported function, in the coordinate
norms of the corresponding `H¹` element. -/
private theorem lintegral_enorm_pow_four_le_mk {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) :
    ∫⁻ x, ‖f x‖ₑ ^ 4 ≤
      ENNReal.ofReal (‖wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (n := 3) (k := 1)
        (p := 2) (Ω := univ) f hf hcs)‖ * ∏ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j)
          (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) f hf hcs)‖) := by
  have h := lintegral_enorm_pow_four_sq_le_of_contDiff (hf.of_le (by exact_mod_cast le_top)) hcs
  have hcont : Continuous f := hf.continuous
  have hdcont (j : Fin 3) : Continuous fun x ↦ (∂[j] f) x := by
    have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
    simpa [partialDeriv] using
      hfd.clm_apply (continuous_const (y := EuclideanSpace.single j (1 : ℝ)))
  have hdcs (j : Fin 3) : HasCompactSupport fun x ↦ (∂[j] f) x := by
    simpa [partialDeriv] using hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j (1 : ℝ))
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖wkpBaseCoordinateCLM
      (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) f hf hcs)‖ ^ 2) := by
    rw [lintegral_enorm_pow_eq hcont.aestronglyMeasurable two_ne_zero, norm_base_mk,
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
    · rfl
    · exact (hcont.memLp_of_hasCompactSupport hcs).eLpNorm_ne_top
  have hd2 (j : Fin 3) : ∫⁻ x, ‖(∂[j] f) x‖ₑ ^ 2 = ENNReal.ofReal (‖wkpCoordinateCLM
      (singleDerivIndex 3 j) (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) f
        hf hcs)‖ ^ 2) := by
    rw [lintegral_enorm_pow_eq (hdcont j).aestronglyMeasurable two_ne_zero, norm_deriv_mk,
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
    · rfl
    · exact ((hdcont j).memLp_of_hasCompactSupport (hdcs j)).eLpNorm_ne_top
  set a := ‖wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2)
    (Ω := univ) f hf hcs)‖
  set b : Fin 3 → ℝ := fun j ↦ ‖wkpCoordinateCLM (singleDerivIndex 3 j)
    (mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) f hf hcs)‖
  have hb (j : Fin 3) : 0 ≤ b j := norm_nonneg _
  rw [h2, Finset.prod_congr rfl fun j _ ↦ hd2 j] at h
  have hrhs : ENNReal.ofReal (a ^ 2) * ∏ j : Fin 3, ENNReal.ofReal (b j ^ 2) =
      ENNReal.ofReal (a * ∏ j : Fin 3, b j) ^ 2 := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun j _ ↦ sq_nonneg (b j),
      ← ENNReal.ofReal_mul (sq_nonneg a), ← ENNReal.ofReal_pow
        (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ ↦ hb j))]
    congr 1
    rw [mul_pow, Finset.prod_pow]
  rw [hrhs] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h

/-- Ladyzhenskaya's inequality on `H¹(ℝ³)`, lower-integral form:
`∫ u⁴ ≤ ‖u‖₂ ‖∂₀u‖₂ ‖∂₁u‖₂ ‖∂₂u‖₂`. -/
theorem lintegral_enorm_pow_four_le_H1 (U : H¹(ℝ^3)) :
    ∫⁻ x, ‖baseRepresentative U x‖ₑ ^ 4 ≤
      ENNReal.ofReal (‖wkpBaseCoordinateCLM U‖ *
        ∏ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) U‖) := by
  obtain ⟨f, hf, hcs, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier 3) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) 1 U
  let V : ℕ → H¹(ℝ^3) := fun m ↦
    mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) (f m) (hf m) (hcs m)
  have hV : Tendsto V atTop (𝓝 U) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  -- The bound converges with the coordinates.
  let c : H¹(ℝ^3) → ℝ := fun W ↦ ‖wkpBaseCoordinateCLM W‖ *
    ∏ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) W‖
  have hc : Continuous c := by
    refine (wkpBaseCoordinateCLM.continuous.norm).mul ?_
    exact continuous_finsetProd _ fun j _ ↦ (wkpCoordinateCLM _).continuous.norm
  have hcV : Tendsto (fun m ↦ ENNReal.ofReal (c (V m))) atTop (𝓝 (ENNReal.ofReal (c U))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hc.tendsto U).comp hV)
  -- A subsequence of the approximants converges almost everywhere.
  have hbase : Tendsto (fun m ↦ wkpBaseCoordinateCLM (V m)) atTop
      (𝓝 (wkpBaseCoordinateCLM U)) := (wkpBaseCoordinateCLM.continuous.tendsto U).comp hV
  have hmeas : TendstoInMeasure (domainMeasure 3 univ)
      (fun m ↦ (wkpBaseCoordinateCLM (V m) : ℝ^3 → ℝ)) atTop
      (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hbase)
  obtain ⟨ns, hnsm, hns⟩ := hmeas.exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂volume, ∀ m, (wkpBaseCoordinateCLM (V m) : ℝ^3 → ℝ) x = f m x := by
    rw [ae_all_iff]
    intro m
    have h := mkWkpSpaceOnOfContDiff_apply_ae (n := 3) (k := 1) (p := 2) (Ω := univ)
      (f m) (hf m) (hcs m) (baseIndex 3 1)
    simp only [baseIndex_toList, iteratedPartialDeriv, domainMeasure_univ] at h
    exact h
  have hns' : ∀ᵐ x ∂volume, Tendsto (fun k ↦ (wkpBaseCoordinateCLM (V (ns k)) : ℝ^3 → ℝ) x)
      atTop (𝓝 ((wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x)) := by
    simpa only [domainMeasure, Measure.restrict_univ] using hns
  have hpt : ∀ᵐ x ∂volume, Tendsto (fun k ↦ ‖f (ns k) x‖ₑ ^ 4) atTop
      (𝓝 (‖baseRepresentative U x‖ₑ ^ 4)) := by
    filter_upwards [hns', hrep] with x hx hxr
    have h := (((ENNReal.continuous_pow 4).comp continuous_enorm).tendsto _).comp hx
    simp only [Function.comp_def, hxr] at h
    exact h
  have hfm (m : ℕ) : AEMeasurable (fun x ↦ ‖f m x‖ₑ ^ 4) volume :=
    ((hf m).continuous.measurable.enorm.pow_const 4).aemeasurable
  calc ∫⁻ x, ‖baseRepresentative U x‖ₑ ^ 4
      = ∫⁻ x, liminf (fun k ↦ ‖f (ns k) x‖ₑ ^ 4) atTop := by
        refine lintegral_congr_ae ?_
        filter_upwards [hpt] with x hx
        exact hx.liminf_eq.symm
    _ ≤ liminf (fun k ↦ ∫⁻ x, ‖f (ns k) x‖ₑ ^ 4) atTop :=
        lintegral_liminf_le' fun k ↦ hfm (ns k)
    _ ≤ liminf (fun k ↦ ENNReal.ofReal (c (V (ns k)))) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k ↦
          lintegral_enorm_pow_four_le_mk (hf (ns k)) (hcs (ns k)))
    _ = ENNReal.ofReal (c U) := (hcV.comp hnsm.tendsto_atTop).liminf_eq

/-- The base representative of an `H¹(ℝ³)` element is strongly measurable for Lebesgue
measure. -/
theorem aestronglyMeasurable_baseRepresentative_H1 (U : H¹(ℝ^3)) :
    AEStronglyMeasurable (baseRepresentative U) volume :=
  (Lp.aestronglyMeasurable (wkpBaseCoordinateCLM U)).mono_measure (by simp [domainMeasure])

/-- **Ladyzhenskaya's inequality** on `H¹(ℝ³)`: `‖u‖₄⁴ ≤ ‖u‖₂ ‖∂₀u‖₂ ‖∂₁u‖₂ ‖∂₂u‖₂`. -/
theorem eLpNorm_four_pow_four_le_H1 (U : H¹(ℝ^3)) :
    eLpNorm (baseRepresentative U) 4 volume ^ 4 ≤
      ENNReal.ofReal (‖wkpBaseCoordinateCLM U‖ *
        ∏ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) U‖) := by
  have h := lintegral_enorm_pow_four_le_H1 U
  rw [lintegral_enorm_pow_eq (aestronglyMeasurable_baseRepresentative_H1 U) four_ne_zero]
    at h
  exact_mod_cast h

/-- `H¹(ℝ³)` is contained in `L⁴(ℝ³)`. -/
theorem memLp_four_H1 (U : H¹(ℝ^3)) : MemLp (baseRepresentative U) 4 volume := by
  have h := (eLpNorm_four_pow_four_le_H1 U).trans_lt ENNReal.ofReal_lt_top
  have hne : eLpNorm (baseRepresentative U) 4 volume ≠ ⊤ := fun htop ↦ by
    rw [htop, ENNReal.top_pow four_ne_zero] at h
    exact lt_irrefl _ h
  exact lt_top_iff_ne_top.mpr hne

/-- Ladyzhenskaya's inequality on `H¹(ℝ³)` with real norms. -/
theorem toReal_eLpNorm_four_pow_four_le_H1 (U : H¹(ℝ^3)) :
    (eLpNorm (baseRepresentative U) 4 volume).toReal ^ 4 ≤
      ‖wkpBaseCoordinateCLM U‖ * ∏ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) U‖ := by
  have hc : 0 ≤ ‖wkpBaseCoordinateCLM U‖ *
      ∏ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) U‖ :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ ↦ norm_nonneg _)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNorm_four_pow_four_le_H1 U)
  rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hc] at h

/-- The squared `H¹(ℝ³)` norm is the squared `L²` norm plus the squared gradient norms. -/
theorem norm_sq_H1_eq (U : H¹(ℝ^3)) :
    ‖U‖ ^ 2 = ‖wkpBaseCoordinateCLM U‖ ^ 2 +
      ∑ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) U‖ ^ 2 :=
  ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (U : WkpAmbientOn 3 1 2 univ)

/-- Energy form of Ladyzhenskaya's inequality on `H¹(ℝ³)`: `‖u‖₄² ≤ ¼ ‖u‖²_{H¹}`. The
arithmetic-geometric mean inequality for `‖u‖₂², ‖∂₀u‖₂², ‖∂₁u‖₂², ‖∂₂u‖₂²` bounds the square
root of the product form. -/
theorem toReal_eLpNorm_four_sq_le_H1 (U : H¹(ℝ^3)) :
    (eLpNorm (baseRepresentative U) 4 volume).toReal ^ 2 ≤ ‖U‖ ^ 2 / 4 := by
  have h := toReal_eLpNorm_four_pow_four_le_H1 U
  rw [Fin.prod_univ_three] at h
  rw [norm_sq_H1_eq, Fin.sum_univ_three]
  set N := (eLpNorm (baseRepresentative U) 4 volume).toReal
  set a := ‖wkpBaseCoordinateCLM U‖
  set b₀ := ‖wkpCoordinateCLM (singleDerivIndex 3 0) U‖
  set b₁ := ‖wkpCoordinateCLM (singleDerivIndex 3 1) U‖
  set b₂ := ‖wkpCoordinateCLM (singleDerivIndex 3 2) U‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb₀ : 0 ≤ b₀ := norm_nonneg _
  have hb₁ : 0 ≤ b₁ := norm_nonneg _
  have hb₂ : 0 ≤ b₂ := norm_nonneg _
  have h₁ : a * b₀ ≤ (a ^ 2 + b₀ ^ 2) / 2 := by nlinarith [sq_nonneg (a - b₀)]
  have h₂ : b₁ * b₂ ≤ (b₁ ^ 2 + b₂ ^ 2) / 2 := by nlinarith [sq_nonneg (b₁ - b₂)]
  have h₃ : a * (b₀ * b₁ * b₂) ≤ ((a * b₀ + b₁ * b₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a * b₀ - b₁ * b₂)]
  have hs : 0 ≤ (a * b₀ + b₁ * b₂) / 2 := by positivity
  have h₄ : (N ^ 2) ^ 2 ≤ ((a ^ 2 + (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2)) / 4) ^ 2 := by
    calc (N ^ 2) ^ 2 = N ^ 4 := by ring
      _ ≤ a * (b₀ * b₁ * b₂) := h
      _ ≤ ((a * b₀ + b₁ * b₂) / 2) ^ 2 := h₃
      _ ≤ ((a ^ 2 + (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2)) / 4) ^ 2 :=
          pow_le_pow_left₀ hs (by linarith) 2
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h₄

/-- Gradient form of Ladyzhenskaya's inequality on `H¹(ℝ³)`:
`27 ‖u‖₄⁸ ≤ ‖u‖₂² ‖∇u‖₂⁶`, that is `‖u‖₄⁴ ≤ 3^{-3/2} ‖u‖₂ ‖∇u‖₂³`, from the product form and
the arithmetic-geometric mean inequality for `‖∂₀u‖₂², ‖∂₁u‖₂², ‖∂₂u‖₂²`. -/
theorem toReal_eLpNorm_four_pow_eight_le_H1 (U : H¹(ℝ^3)) :
    27 * (eLpNorm (baseRepresentative U) 4 volume).toReal ^ 8 ≤
      ‖wkpBaseCoordinateCLM U‖ ^ 2 *
        (∑ j : Fin 3, ‖wkpCoordinateCLM (singleDerivIndex 3 j) U‖ ^ 2) ^ 3 := by
  have h := toReal_eLpNorm_four_pow_four_le_H1 U
  rw [Fin.prod_univ_three] at h
  rw [Fin.sum_univ_three]
  set N := (eLpNorm (baseRepresentative U) 4 volume).toReal
  set a := ‖wkpBaseCoordinateCLM U‖
  set b₀ := ‖wkpCoordinateCLM (singleDerivIndex 3 0) U‖
  set b₁ := ‖wkpCoordinateCLM (singleDerivIndex 3 1) U‖
  set b₂ := ‖wkpCoordinateCLM (singleDerivIndex 3 2) U‖
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have ha : 0 ≤ a := norm_nonneg _
  have hb₀ : 0 ≤ b₀ ^ 2 := sq_nonneg _
  have hb₁ : 0 ≤ b₁ ^ 2 := sq_nonneg _
  have hb₂ : 0 ≤ b₂ ^ 2 := sq_nonneg _
  have hamgm : 27 * (b₀ ^ 2 * b₁ ^ 2 * b₂ ^ 2) ≤ (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) ^ 3 := by
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hb₀ hb₁) hb₂) (sq_nonneg (b₀ ^ 2 - b₁ ^ 2)),
      mul_nonneg (add_nonneg (add_nonneg hb₀ hb₁) hb₂) (sq_nonneg (b₁ ^ 2 - b₂ ^ 2)),
      mul_nonneg (add_nonneg (add_nonneg hb₀ hb₁) hb₂) (sq_nonneg (b₀ ^ 2 - b₂ ^ 2)),
      mul_nonneg hb₀ (sq_nonneg (b₁ ^ 2 - b₂ ^ 2)), mul_nonneg hb₁ (sq_nonneg (b₀ ^ 2 - b₂ ^ 2)),
      mul_nonneg hb₂ (sq_nonneg (b₀ ^ 2 - b₁ ^ 2))]
  have hN4 : 0 ≤ N ^ 4 := by positivity
  calc 27 * N ^ 8 = 27 * (N ^ 4) ^ 2 := by ring
    _ ≤ 27 * (a * (b₀ * b₁ * b₂)) ^ 2 := by gcongr
    _ = a ^ 2 * (27 * (b₀ ^ 2 * b₁ ^ 2 * b₂ ^ 2)) := by ring
    _ ≤ a ^ 2 * (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) ^ 3 := by gcongr

/-- `H¹(ℝ³)` is contained in `L⁴(ℝ³)`, for the whole-space domain measure. -/
theorem memLp_four_domainMeasure_H1 (U : H¹(ℝ^3)) :
    MemLp (baseRepresentative U) 4 (domainMeasure 3 univ) := by
  simpa [domainMeasure] using memLp_four_H1 U

/-- The inclusion `H¹(ℝ³) → L⁴(ℝ³)`, the bounded inclusion of `embeddingCLMOfMemLp`; its
operator norm is at most `1/2` by the energy form of Ladyzhenskaya's inequality
(`norm_l4EmbeddingThree_le`). -/
def l4EmbeddingThree : H¹(ℝ^3) →L[ℝ] DerivLp 3 4 univ :=
  embeddingCLMOfMemLp memLp_four_domainMeasure_H1

/-- The `L⁴` class of `u ∈ H¹(ℝ³)` is represented by the base representative of `u`. -/
@[simp]
theorem coe_l4EmbeddingThree (U : H¹(ℝ^3)) :
    (l4EmbeddingThree U : ℝ^3 → ℝ) = baseRepresentative U :=
  rfl

/-- The norm of the `L⁴` class of `u ∈ H¹(ℝ³)`. -/
theorem norm_l4EmbeddingThree_apply (U : H¹(ℝ^3)) :
    ‖l4EmbeddingThree U‖ = (eLpNorm (baseRepresentative U) 4 volume).toReal := by
  rw [Lp.norm_def, coe_l4EmbeddingThree, domainMeasure_univ]

/-- Energy form of Ladyzhenskaya's inequality: `‖u‖_{L⁴} ≤ ½ ‖u‖_{H¹}` on `ℝ³`. -/
theorem norm_l4EmbeddingThree_apply_le (U : H¹(ℝ^3)) : ‖l4EmbeddingThree U‖ ≤ ‖U‖ / 2 := by
  have h : ‖l4EmbeddingThree U‖ ^ 2 ≤ (‖U‖ / 2) ^ 2 := by
    rw [norm_l4EmbeddingThree_apply, div_pow]
    norm_num
    exact toReal_eLpNorm_four_sq_le_H1 U
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The `L⁴` inclusion of `H¹(ℝ³)` has operator norm at most `1/2`. -/
theorem norm_l4EmbeddingThree_le : ‖l4EmbeddingThree‖ ≤ 1 / 2 :=
  l4EmbeddingThree.opNorm_le_bound (by norm_num) fun U ↦ by
    rw [one_div_mul_eq_div]
    exact norm_l4EmbeddingThree_apply_le U

end SobolevSpace.Inequalities

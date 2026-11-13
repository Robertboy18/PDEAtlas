/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Mollification.Contraction
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Mollification converges in the fractional seminorm

For each fixed displacement, the translation increment converges in `Lᵖ`.
Its error is bounded by twice the original increment norm. The fractional
energy of the original function therefore dominates the errors, so dominated
convergence gives convergence of the whole fractional seminorm.

The proof allows Banach-valued functions, every finite exponent `p ≥ 1`, and
every real order for which the original difference quotient belongs to `Lᵖ`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] [Fact (1 ≤ p)] in
private theorem increment_mollifyVector_sub (μ : Mollifier n) {ε : ℝ}
    {u : ℝ^n → F} (hu : LocallyIntegrable u) (h : ℝ^n) :
    (fun x ↦ (mollifyVector μ ε u (x - h) - u (x - h)) -
      (mollifyVector μ ε u x - u x)) =
    (fun x ↦ mollifyVector μ ε (fun y ↦ u (y - h) - u y) x -
      (u (x - h) - u x)) := by
  funext x
  rw [congrFun (mollifyVector_sub_translate μ hu h) x]
  abel

/-- Positive-scale mollification converges in the whole-space fractional
seminorm for Banach-valued functions and every finite exponent `p ≥ 1`. -/
theorem tendsto_eLpNorm_diffQuot_mollifyVector_sub (μ : Mollifier n) (hp : p ≠ ∞)
    {u : ℝ^n → F} (hu : MemGagliardo n s Set.univ u (p := p)) :
    Tendsto (fun ε : ℝ ↦
      eLpNorm (diffQuot n s (fun x ↦ mollifyVector μ ε u x - u x) (p := p))
        p (gagliardoProductMeasure n Set.univ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have huf : MemLp u p volume := by
    simpa only [Measure.restrict_univ] using hu.1
  have hδ (h : ℝ^n) : MemLp (fun x ↦ u (x - h) - u x) p volume := by
    have hshift : MemLp (fun x ↦ u (x - h)) p volume := by
      simpa only [sub_eq_add_neg, Function.comp_def] using
        huf.comp_measurePreserving (measurePreserving_add_right volume (-h))
    exact hshift.sub huf
  let w (h : ℝ^n) := ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + s * p.toReal)))
  let energy (v : ℝ^n → F) (h : ℝ^n) :=
    w h * eLpNorm (fun x ↦ v (x - h) - v x) p volume ^ p.toReal
  let error (ε : ℝ) := fun x ↦ mollifyVector μ ε u x - u x
  have herr {ε : ℝ} (h : ℝ^n) :
      (fun x ↦ error ε (x - h) - error ε x) =
        (fun x ↦ mollifyVector μ ε (fun y ↦ u (y - h) - u y) x -
          (u (x - h) - u x)) :=
    increment_mollifyVector_sub μ
      (huf.locallyIntegrable (Fact.out : 1 ≤ p)) h
  have hmeas {ε : ℝ} (hε : 0 < ε) : AEStronglyMeasurable (error ε) volume :=
    (mollifyVector_contDiff_of_pos μ hε u (huf.locallyIntegrable (Fact.out : 1 ≤ p))).continuous
      |>.aestronglyMeasurable.sub huf.aestronglyMeasurable
  have henergy {ε : ℝ} (hε : 0 < ε) : AEMeasurable (energy (error ε)) volume :=
    (by fun_prop : Measurable w).aemeasurable.mul
      (aemeasurable_eLpNorm_sub_translate_rpow (hmeas hε) hp0 hp)
  have hbound {ε : ℝ} (hε : 0 < ε) (h : ℝ^n) :
      energy (error ε) h ≤ (2 : ℝ≥0∞) ^ p.toReal * energy u h := by
    change w h * _ ≤ (2 : ℝ≥0∞) ^ p.toReal * (w h * _)
    rw [herr h]
    have hnorm :
        eLpNorm (fun x ↦ mollifyVector μ ε (fun y ↦ u (y - h) - u y) x -
          (u (x - h) - u x)) p volume ≤
          2 * eLpNorm (fun x ↦ u (x - h) - u x) p volume :=
      (eLpNorm_sub_le (Fact.out : 1 ≤ p)).trans <| by
        rw [two_mul]
        exact add_le_add_left (MollifyLp.eLpNorm_mollifyVector_le μ hε hp (hδ h)) _
    calc
      _ ≤ w h * (2 * eLpNorm (fun x ↦ u (x - h) - u x) p volume) ^ p.toReal :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hnorm hr.le) _
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]; ac_rfl
  have hfinite : (∫⁻ h : ℝ^n, (2 : ℝ≥0∞) ^ p.toReal * energy u h) ≠ ∞ := by
    have htwo : (2 : ℝ≥0∞) ^ p.toReal ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hr.le (by norm_num)
    rw [lintegral_const_mul' _ _ htwo]
    apply ENNReal.mul_ne_top htwo
    change (∫⁻ h : ℝ^n, w h *
      eLpNorm (fun x ↦ u (x - h) - u x) p volume ^ p.toReal) ≠ ∞
    rw [← eLpNorm_diffQuot_rpow_eq_lintegral_displacement huf.aestronglyMeasurable hp0 hp]
    exact ENNReal.rpow_ne_top_of_nonneg hr.le hu.2.eLpNorm_lt_top.ne
  have hlimit (h : ℝ^n) :
      Tendsto (fun ε : ℝ ↦ energy (error ε) h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hw := ENNReal.Tendsto.const_mul (a := w h)
      ((tendsto_eLpNorm_mollifyVector_sub μ hp (hδ h)).ennrpow_const p.toReal)
      (Or.inr ENNReal.ofReal_ne_top)
    rw [ENNReal.zero_rpow_of_pos hr, mul_zero] at hw
    refine hw.congr' (eventually_mem_nhdsWithin.mono fun ε hε ↦ ?_)
    change w h * _ = w h * _
    rw [herr h]
  have hint : Tendsto (fun ε : ℝ ↦ ∫⁻ h : ℝ^n, energy (error ε) h)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence'
      (f := fun _ : ℝ^n ↦ (0 : ℝ≥0∞)) (fun h : ℝ^n ↦ (2 : ℝ≥0∞) ^ p.toReal * energy u h)
      (hpos.mono fun ε hε ↦ henergy hε) (hpos.mono fun ε hε ↦ ae_of_all _ (hbound hε))
      hfinite (ae_of_all _ hlimit)
  have hpowers : Tendsto (fun ε : ℝ ↦
      eLpNorm (diffQuot n s (error ε) (p := p)) p
        (gagliardoProductMeasure n Set.univ) ^ p.toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hint.congr' (eventually_mem_nhdsWithin.mono fun ε hε ↦
      (eLpNorm_diffQuot_rpow_eq_lintegral_displacement (hmeas hε) hp0 hp).symm)
  simpa only [ENNReal.rpow_rpow_inv hr.ne', ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)]
    using hpowers.ennrpow_const p.toReal⁻¹

end SobolevSpace.Fractional

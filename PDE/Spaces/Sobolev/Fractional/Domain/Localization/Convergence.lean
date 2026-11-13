/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm.Convergence
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Estimates

/-!
# Convergent families of fractional multipliers

Uniform Lipschitz and supremum bounds give one integrable majorant for a
family of cutoff products. If the cutoffs tend to zero almost everywhere,
their products with a fixed fractional Sobolev function tend to zero in both
the base `Lᵖ` norm and the fractional seminorm.

No boundary regularity or completeness of the target space is used.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞}
  {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {l : Filter ι} [l.IsCountablyGenerated]
  {φ : ι → ℝ^n → ℝ} {L M : ℝ≥0} {u : ℝ^n → F}

/-- Uniformly bounded scalar multipliers that vanish almost everywhere send
a fixed `Lᵖ` function to zero in norm, for every finite positive exponent. -/
theorem tendsto_eLpNorm_smul_zero (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (volume.restrict Ω))
    (hM : ∀ᶠ i in l, ∀ x, ‖φ i x‖ ≤ M)
    (hu : MemLp u p (volume.restrict Ω))
    (hzero : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun i ↦ φ i x) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun x ↦ φ i x • u x) p (volume.restrict Ω))
      l (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  apply tendsto_eLpNorm_zero_of_dominated_convergence hp0 hp
    (fun x ↦ ENNReal.ofReal ((M : ℝ) ^ p.toReal) * ‖u x‖ₑ ^ p.toReal)
    (hmeas.mono fun i hi ↦ hi.smul hu.aestronglyMeasurable)
  · exact hM.mono fun i hi ↦ ae_of_all _ fun x ↦ by
      rw [Pi.smul_apply', enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
      apply mul_le_mul_left
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (norm_nonneg _) (hi x) hr.le)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
        hu.aestronglyMeasurable).1 hu.eLpNorm_lt_top).ne
  · exact hzero.mono fun x hx ↦ by
      simpa only [Pi.smul_apply', zero_smul] using hx.smul_const (u x)

/-- Uniformly bounded Lipschitz multipliers that vanish almost everywhere
send a fixed fractional Sobolev function to zero in its fractional seminorm. -/
theorem tendsto_eLpNorm_diffQuot_smul_zero (hs0 : 0 < s) (hs1 : s < 1)
    (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hL : ∀ᶠ i in l, LipschitzWith L (φ i))
    (hM : ∀ᶠ i in l, ∀ x, ‖φ i x‖ ≤ M)
    (hu : MemGagliardo n s Ω u (p := p))
    (hzero : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun i ↦ φ i x) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (diffQuot n s (fun x ↦ φ i x • u x) (p := p))
      p (gagliardoProductMeasure n Ω)) l (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  let bound (z : ℝ^n × ℝ^n) : ℝ≥0∞ :=
    2 ^ p.toReal *
      (ENNReal.ofReal ((M : ℝ) ^ p.toReal) *
          ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal +
        ENNReal.ofReal ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
          (‖u z.2‖ₑ ^ p.toReal *
            ENNReal.ofReal (cutoffKernel n s (z.1 - z.2) (p := p.toReal))))
  have hbase := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
    hu.1.aestronglyMeasurable).1 hu.1.eLpNorm_lt_top
  have hdiff := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
    hu.2.aestronglyMeasurable).1 hu.2.eLpNorm_lt_top
  have hkernel :
      (∫⁻ z, ‖u z.2‖ₑ ^ p.toReal *
        ENNReal.ofReal (cutoffKernel n s (z.1 - z.2) (p := p.toReal))
        ∂gagliardoProductMeasure n Ω) < ∞ :=
    (lintegral_enorm_rpow_mul_cutoffKernel_le hr.le hu.1.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top hbase (cutoffMass_lt_top hs0 hs1 p.toReal hr))
  have hfinite : (∫⁻ z, bound z ∂gagliardoProductMeasure n Ω) ≠ ∞ := by
    dsimp only [bound]
    rw [lintegral_const_mul' _ _ (by finiteness),
      lintegral_add_left' ((hu.2.aestronglyMeasurable.enorm.pow_const p.toReal).const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top (by finiteness) (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiff.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hkernel.ne⟩)
  apply tendsto_eLpNorm_zero_of_dominated_convergence hp0 hp bound
    (hL.mono fun i hi ↦ aestronglyMeasurable_diffQuot
      (hi.continuous.aestronglyMeasurable.smul hu.1.aestronglyMeasurable))
    ((hL.and hM).mono fun i hi ↦ ae_of_all _ fun z ↦
      enorm_diffQuot_smul_rpow_le hp0 hp (by positivity) hi.1 hi.2 u z.1 z.2)
    hfinite
  have hx := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict Ω) (ν := volume.restrict Ω)).ae hzero
  have hy := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict Ω) (ν := volume.restrict Ω)).ae hzero
  filter_upwards [hx, hy] with z hx hy
  have ht := (hx.smul_const (u z.1)).sub (hy.smul_const (u z.2))
  simpa only [diffQuot, Pi.smul_apply', zero_smul, sub_self, smul_zero] using
    ht.const_smul (‖z.1 - z.2‖ ^ ((n : ℝ) / p.toReal + s))⁻¹

end SobolevSpace.Fractional.Localization

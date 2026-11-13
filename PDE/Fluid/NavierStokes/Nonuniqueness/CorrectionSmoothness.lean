/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.CorrectionRegularity
public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalVelocity
public import PDE.Spaces.Sobolev.Fractional.Integer.ClassicalRepresentation

/-!
# Spatial smoothness of the correction field

Above the threshold radius the ancient correction `U_cor(τ)` lies in vector `Hᵐ` for every `m`
at every `τ ≤ 0`, continuously in `τ` (`exists_correctionLift`). By the Sobolev embedding of
`Hᵐ(ℝ³)` into `Cʳ` for `3 < 2 (m - r)`, the canonical continuous representative
`correctionField D R s τ` is the classical representative of each lift. Hence at every `τ ≤ 0`
the correction field is smooth in space, and it is jointly continuous in `(τ, ξ)` on `τ ≤ 0`.
In physical variables the same holds for `t^{-1/2} U_cor(log t, x / √t)` on `0 < t ≤ 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R s : ℝ}

/-- The Sobolev embedding threshold for a lift of order `m + 1` with `3 < 2m`. -/
theorem three_lt_two_mul_succ_sub_one {m : ℕ} (hm : (3 : ℝ) < 2 * m) :
    ((3 : ℕ) : ℝ) < 2 * (((m + 1 : ℕ) : ℝ) - 1) := by
  push_cast
  linarith

/-- At a time `τ ≤ 0` the correction field is the classical representative of every lift of the
ancient correction. -/
theorem correctionField_eq_classicalRepresentative {m : ℕ} {hm : (3 : ℝ) < 2 * m}
    {V : ℝ → VectorH 3 (m + 1)} (hV : IsCorrectionLift D R s m hm V) {τ : ℝ} (hτ : τ ≤ 0) :
    correctionField D R s τ = fun ξ ↦ WithLp.toLp 2 fun j ↦
      classicalRepresentativeCLM (three_lt_two_mul_succ_sub_one hm) (V τ j) ξ := by
  refine continuousRepresentative_eq ((PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun j ↦ (classicalRepresentativeCLM _ (V τ j)).continuous)) ?_
  have hj : ∀ j : Fin 3, (classicalRepresentativeCLM (three_lt_two_mul_succ_sub_one hm) (V τ j) :
      ℝ^3 → ℝ) =ᵐ[volume]
      baseRepresentative (ancientLift D.dichotomy.η (ancientCorrection D R s) τ j) := by
    intro j
    rw [← hV.2.1 τ hτ]
    exact (classicalRepresentativeCLM_ae _ (V τ j)).trans
      (by rw [show vectorLowerOrderCLM (three_le_succ_of_three_lt_two_mul hm) (V τ) j =
          lowerOrderCLM (three_le_succ_of_three_lt_two_mul hm) (V τ j) from rfl,
        baseRepresentative_lowerOrderCLM])
  filter_upwards [ae_all_iff.mpr hj] with ξ hξ
  exact congrArg (WithLp.toLp 2) (funext hξ)

/-- **Spatial smoothness of the correction field.** Above the threshold radius and for
`s ∈ [0, 1]`, at every `τ ≤ 0` the correction field `ξ ↦ U_cor(τ, ξ)` is smooth. -/
theorem contDiff_correctionField (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {τ : ℝ} (hτ : τ ≤ 0) : ContDiff ℝ (⊤ : ℕ∞) (correctionField D R s τ) := by
  refine contDiff_infty.mpr fun r ↦ ?_
  have hm : (3 : ℝ) < 2 * ((r + 3 : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  obtain ⟨V, hV⟩ := exists_correctionLift hR hs (r + 3) hm
  rw [correctionField_eq_classicalRepresentative hV hτ]
  refine contDiff_piLp' 2 fun j ↦ ?_
  exact contDiff_classicalRepresentativeCLM _ (by push_cast; linarith) (V τ j)

/-- Above the threshold radius and for `s ∈ [0, 1]`, the correction field is jointly continuous in
`(τ, ξ)` on `τ ≤ 0`. -/
theorem continuousOn_correctionField (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun p : ℝ × ℝ^3 ↦ correctionField D R s p.1 p.2) (Iic 0 ×ˢ univ) := by
  have hm : (3 : ℝ) < 2 * ((3 : ℕ) : ℝ) := by norm_num
  have hk := three_lt_two_mul_succ_sub_one hm
  obtain ⟨V, hV⟩ := exists_correctionLift hR hs 3 hm
  -- Extend the lift constantly beyond `0`, to a path continuous on the whole line.
  have hV' : Continuous fun τ : ℝ ↦ V (min τ 0) :=
    hV.1.comp_continuous (continuous_id.min continuous_const) fun τ ↦ min_le_right τ 0
  have hj : ∀ j : Fin 3, Continuous fun p : ℝ × ℝ^3 ↦
      classicalRepresentativeCLM hk (V (min p.1 0) j) p.2 := fun j ↦
    continuous_classicalRepresentativeCLM hk (u := fun τ ↦ V (min τ 0) j)
      ((PiLp.continuous_apply 2 _ j).comp hV')
  have hcont : Continuous fun p : ℝ × ℝ^3 ↦ WithLp.toLp 2 fun j ↦
      classicalRepresentativeCLM hk (V (min p.1 0) j) p.2 :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi hj)
  refine hcont.continuousOn.congr fun p hp ↦ ?_
  have hp0 : min p.1 0 = p.1 := min_eq_left hp.1
  simp only [hp0]
  rw [correctionField_eq_classicalRepresentative hV hp.1]

/-- In physical variables, at every time `0 < t ≤ 1` the correction part
`x ↦ t^{-1/2} U_cor(log t, x / √t)` of the physical velocity is smooth. -/
theorem contDiff_physicalCorrectionField (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ^3 ↦
      (Real.sqrt t)⁻¹ • correctionField D R s (Real.log t) ((Real.sqrt t)⁻¹ • x) :=
  ((contDiff_correctionField hR hs (Real.log_nonpos ht.le ht1)).comp
    (contDiff_const_smul _)).const_smul _

/-- In physical variables the correction part `t^{-1/2} U_cor(log t, x / √t)` of the physical
velocity is jointly continuous on `(0, 1] × ℝ³`. -/
theorem continuousOn_physicalCorrectionField (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun p : ℝ × ℝ^3 ↦
      (Real.sqrt p.1)⁻¹ • correctionField D R s (Real.log p.1) ((Real.sqrt p.1)⁻¹ • p.2))
      (Ioc 0 1 ×ˢ univ) := by
  have hsqrt : ContinuousOn (fun p : ℝ × ℝ^3 ↦ (Real.sqrt p.1)⁻¹) (Ioc 0 1 ×ˢ univ) :=
    (Real.continuous_sqrt.comp continuous_fst).continuousOn.inv₀ fun p hp ↦
      (Real.sqrt_pos.mpr hp.1.1).ne'
  have hlog : ContinuousOn (fun p : ℝ × ℝ^3 ↦ Real.log p.1) (Ioc 0 1 ×ˢ univ) :=
    Real.continuousOn_log.comp continuousOn_fst fun p hp ↦ hp.1.1.ne'
  have hmap : MapsTo (fun p : ℝ × ℝ^3 ↦ (Real.log p.1, (Real.sqrt p.1)⁻¹ • p.2))
      (Ioc 0 1 ×ˢ univ) (Iic 0 ×ˢ univ) := fun p hp ↦
    ⟨Real.log_nonpos hp.1.1.le hp.1.2, mem_univ _⟩
  have hg : ContinuousOn (fun p : ℝ × ℝ^3 ↦ (Real.log p.1, (Real.sqrt p.1)⁻¹ • p.2))
      (Ioc 0 1 ×ˢ univ) :=
    hlog.prodMk (hsqrt.smul continuousOn_snd)
  have hc := (continuousOn_correctionField hR hs).comp hg hmap
  dsimp only [Function.comp_def] at hc
  exact hsqrt.smul hc

end NavierStokes.Nonuniqueness

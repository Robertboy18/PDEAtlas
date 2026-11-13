/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Differentiability
public import PDE.Fluid.Incompressible.LerayProjection.Laplacian
public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCorrection

/-!
# Time differentiability of the correction in physical variables

The physical correction `u_cor(t)` solves the heat Duhamel formula
`u(t) = e^{(t - t₀) Δ} u(t₀) + Π ∫_{t₀}^t e^{(t - r) Δ} g(r) dr` on `(0, 1]` in every vector
`Hᵐ⁺¹` (`physicalCorrection_eq`). The Laplacian generates the heat semigroup on vector `Hᵐ⁺¹`
with domain vector `Hᵐ⁺³` (`hasGeneratorAt_vectorHeatSemigroup`), and both `u_cor` and the
physical forcing `g` lie in every `Hᵐ`, continuously on `(0, 1]`. Duhamel's formula therefore
differentiates in time, and the derivative is the Leray-projected equation of the correction
in physical variables (`hasDerivAt_physicalCorrection`),

`∂ₜ u_cor = Δ u_cor + Π g`,

with no drift term. In particular `t ↦ u_cor(t)` is continuously differentiable on `(0, 1)`
with values in every vector `Hᵐ⁺¹` (`contDiffOn_one_physicalCorrection`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R s : ℝ}

/-! ### Lowering in physical variables -/

/-- Forgetting the top order commutes with the physical map. -/
theorem vectorLower_physicalMap (k : ℕ) (τ : ℝ) (v : VectorH 3 (k + 1)) :
    vectorLower 3 k (physicalMap (k + 1) τ v) = physicalMap k τ (vectorLower 3 k v) := by
  rw [physicalMap_apply, physicalMap_apply, map_smul, vectorLower_vectorDilation]

variable (D R) in
/-- Forgetting the top order of the integrand of order `m + 1` gives the integrand of order `m`
of the lowered path. -/
theorem vectorLower_liftForcing {m : ℕ} (hm : (3 : ℝ) < 2 * m) (V : ℝ → VectorH 3 (m + 2))
    (r : ℝ) :
    vectorLower 3 m (liftForcing D R (m + 1) (three_lt_two_mul_succ hm) V r) =
      liftForcing D R m hm (fun r ↦ vectorLower 3 (m + 1) (V r)) r := by
  rw [liftForcing, liftForcing, map_add, vectorLower_cutoffForcing,
    vectorLower_correctionOperator D R hm]

/-- Forgetting the top order of the physical correction of order `m + 2` gives the physical
correction of order `m + 1`. -/
theorem vectorLower_physicalCorrection_succ (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    vectorLower 3 (m + 1) (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t) =
      physicalCorrection D R s m hm t := by
  rw [physicalCorrection, physicalCorrection, vectorLower_physicalMap,
    vectorLower_correctionLift_succ hR hs hm (Real.log_nonpos ht.le ht1)]

/-- Forgetting the top order of the physical forcing of order `m + 2` gives the physical forcing
of order `m + 1`. -/
theorem vectorLower_physicalForcing_succ (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    vectorLower 3 (m + 1) (physicalForcing D R s (m + 1) (three_lt_two_mul_succ hm) t) =
      physicalForcing D R s m hm t := by
  rw [physicalForcing, physicalForcing, map_smul, vectorLower_physicalMap,
    vectorLower_liftForcing D R (three_lt_two_mul_succ hm)]
  have hτ := Real.log_nonpos ht.le ht1
  simp only [liftForcing]
  rw [vectorLower_correctionLift_succ hR hs (three_lt_two_mul_succ hm) hτ,
    vectorLower_correctionLift_succ hR hs hm hτ]

/-- Above the threshold radius and for `s ∈ [0, 1]` the physical forcing is continuous on
`(0, 1]` in every vector `Hᵐ⁺¹`. -/
theorem continuousOn_physicalForcing (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (hm : (3 : ℝ) < 2 * m) :
    ContinuousOn (physicalForcing D R s m hm) (Ioc 0 1) := by
  have hlog : ContinuousOn Real.log (Ioc 0 1) :=
    Real.continuousOn_log.mono fun t ht ↦ ht.1.ne'
  have hmaps : MapsTo Real.log (Ioc 0 1) (Iic 0) := fun t ht ↦ Real.log_nonpos ht.1.le ht.2
  have hG := continuousOn_liftForcing D R (three_lt_two_mul_succ hm)
    (isCorrectionLift_correctionLift hR hs (m + 1) (three_lt_two_mul_succ hm)).1
  have h := (continuousOn_physicalMap (k := m + 1) subset_rfl hG).comp hlog hmaps
  exact (continuousOn_inv₀.mono fun t ht ↦ ht.1.ne').smul h

/-! ### The time derivative -/

/-- The Duhamel integral from `t₀` to `t₀ + ρ` is the semigroup Duhamel integral of the shifted
forcing, clamped to `[0, b]` for `ρ ≤ b`. -/
theorem intervalIntegral_vectorHeat_eq_duhamel {K : ℕ} (g : ℝ → VectorH 3 K) {t₀ ρ b : ℝ}
    (hρ : ρ ∈ Icc 0 b) :
    ∫ r in t₀..t₀ + ρ, vectorHeat 3 K (t₀ + ρ - r).toNNReal (g r) =
      (vectorHeatSemigroup 3 K).duhamel (fun σ ↦ g (t₀ + max 0 (min σ b))) ρ := by
  have h := intervalIntegral.integral_comp_add_left (a := 0) (b := ρ)
    (fun r ↦ vectorHeat 3 K (t₀ + ρ - r).toNNReal (g r)) t₀
  rw [add_zero] at h
  rw [← h, StronglyContinuousSemigroup.duhamel]
  refine intervalIntegral.integral_congr fun σ hσ ↦ ?_
  rw [uIcc_of_le hρ.1] at hσ
  have hclamp : max 0 (min σ b) = σ := by
    rw [min_eq_left (hσ.2.trans hρ.2), max_eq_right hσ.1]
  simp only [vectorHeatSemigroup_apply, hclamp]
  rw [show t₀ + ρ - (t₀ + σ) = ρ - σ by ring]

/-- Forgetting two orders is lowering twice. -/
theorem vectorLowerOrderCLM_two_eq {k : ℕ} (v : VectorH 3 (k + 2)) :
    vectorLowerOrderCLM (by omega : k ≤ k + 2) v = vectorLower 3 k (vectorLower 3 (k + 1) v) := by
  rw [vectorLower, vectorLower, vectorLowerOrderCLM_trans_apply]

/-- **The equation of the correction in physical variables.** Above the threshold radius and for
`s ∈ [0, 1]`, at every `t ∈ (0, 1)` the physical correction in vector `Hᵐ⁺¹` is differentiable,
with derivative `Δ u_cor(t) + Π g(t)`, the Laplacian of the physical correction in vector `Hᵐ⁺³`
plus the Leray projection of the physical forcing. -/
theorem hasDerivAt_physicalCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (physicalCorrection D R s m hm)
      (vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 2)
          (three_lt_two_mul_succ (three_lt_two_mul_succ hm)) t) +
        leraySobolev 3 (m + 1) (physicalForcing D R s m hm t)) t := by
  have hm₁ := three_lt_two_mul_succ hm
  have hm₂ := three_lt_two_mul_succ hm₁
  have ht0 : 0 < t := ht.1
  set t₀ := t / 2 with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  set b := 1 - t₀ with hbdef
  have hb : 0 < b := by linarith [ht.2]
  set T := vectorHeatSemigroup 3 (m + 1) with hT
  -- lowering two orders in physical variables
  have hlowU : ∀ r, 0 < r → r ≤ 1 → vectorLowerOrderCLM (by omega : m + 1 ≤ m + 1 + 2)
      (physicalCorrection D R s (m + 2) hm₂ r) = physicalCorrection D R s m hm r := by
    intro r hr hr1
    rw [vectorLowerOrderCLM_two_eq, vectorLower_physicalCorrection_succ hR hs hm₁ hr hr1,
      vectorLower_physicalCorrection_succ hR hs hm hr hr1]
  have hlowg : ∀ r, 0 < r → r ≤ 1 → vectorLowerOrderCLM (by omega : m + 1 ≤ m + 1 + 2)
      (physicalForcing D R s (m + 2) hm₂ r) = physicalForcing D R s m hm r := by
    intro r hr hr1
    rw [vectorLowerOrderCLM_two_eq, vectorLower_physicalForcing_succ hR hs hm₁ hr hr1,
      vectorLower_physicalForcing_succ hR hs hm hr hr1]
  -- the clamped time and the forcing paths
  set p : ℝ → ℝ := fun σ ↦ t₀ + max 0 (min σ b) with hp
  have hpc : Continuous p := continuous_const.add (continuous_const.max (continuous_id.min
    continuous_const))
  have hpmem : ∀ σ, p σ ∈ Ioc 0 1 := fun σ ↦ by
    simp only [hp, mem_Ioc]
    exact ⟨by positivity, by linarith [max_le hb.le (min_le_right σ b)]⟩
  set f : ℝ → VectorH 3 (m + 1) := fun σ ↦ physicalForcing D R s m hm (p σ) with hf
  set Af : ℝ → VectorH 3 (m + 1) := fun σ ↦
    vectorLaplacian 3 (m + 1) (physicalForcing D R s (m + 2) hm₂ (p σ)) with hAf
  have hfc : Continuous f :=
    (continuousOn_physicalForcing hR hs m hm).comp_continuous hpc hpmem
  have hAfc : Continuous Af := (vectorLaplacian 3 (m + 1)).continuous.comp
    ((continuousOn_physicalForcing hR hs (m + 2) hm₂).comp_continuous hpc hpmem)
  have hA : ∀ σ, T.HasGeneratorAt (f σ) (Af σ) := fun σ ↦ by
    have h := hasGeneratorAt_vectorHeatSemigroup (n := 3) (k := m + 1)
      (physicalForcing D R s (m + 2) hm₂ (p σ))
    rwa [hlowg _ (hpmem σ).1 (hpmem σ).2] at h
  set x := physicalCorrection D R s m hm t₀ with hx
  set Ax := vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 2) hm₂ t₀) with hAx
  have hgen : T.HasGeneratorAt x Ax := by
    have h := hasGeneratorAt_vectorHeatSemigroup (n := 3) (k := m + 1)
      (physicalCorrection D R s (m + 2) hm₂ t₀)
    rwa [hlowU _ ht₀ (by linarith [ht.2])] at h
  -- the Duhamel formula as a function of the elapsed time
  set F : ℝ → VectorH 3 (m + 1) := fun ρ ↦
    T.realOrbit x ρ + leraySobolev 3 (m + 1) (T.duhamel f ρ) with hF
  have hmild : ∀ ρ ∈ Icc 0 b, physicalCorrection D R s m hm (t₀ + ρ) = F ρ := by
    intro ρ hρ
    rw [physicalCorrection_eq hR hs hm ht₀ (by linarith [hρ.1]) (by linarith [hρ.2]),
      intervalIntegral_vectorHeat_eq_duhamel _ hρ, add_sub_cancel_left]
    rfl
  -- differentiate
  have hρ₁ : t - t₀ ∈ Ioo 0 b := ⟨by linarith, by linarith [ht.2]⟩
  have hd₁ := hgen.hasDerivAt_realOrbit hρ₁.1
  have hd₂ := T.hasDerivAt_duhamel hfc hAfc hρ₁ fun σ _ ↦ hA σ
  have hd₃ := ((leraySobolev 3 (m + 1)).hasFDerivAt.comp_hasDerivAt (t - t₀) hd₂)
  have hdF : HasDerivAt F (T.realOrbit Ax (t - t₀) +
      leraySobolev 3 (m + 1) (T.duhamel Af (t - t₀) + f (t - t₀))) (t - t₀) :=
    hd₁.add hd₃
  have hdu := hdF.comp_sub_const t t₀
  have heq : physicalCorrection D R s m hm =ᶠ[𝓝 t] fun t' ↦ F (t' - t₀) := by
    filter_upwards [Ioo_mem_nhds (by linarith : t₀ < t) ht.2] with t' ht'
    rw [← hmild (t' - t₀) ⟨by linarith [ht'.1], by linarith [ht'.2]⟩, add_sub_cancel]
  refine (hdu.congr_of_eventuallyEq heq).congr_deriv ?_
  -- identify the derivative
  have hpt : p (t - t₀) = t := by
    simp only [hp]
    rw [min_eq_left hρ₁.2.le, max_eq_right hρ₁.1.le]
    ring
  have hft : f (t - t₀) = physicalForcing D R s m hm t := by
    simp only [hf, hpt]
  have hU₂ := physicalCorrection_eq hR hs hm₂ ht₀ (by linarith : t₀ ≤ t) ht.2.le
  have hint : IntervalIntegrable (fun r ↦ vectorHeat 3 (m + 1 + 1 + 1) (t - r).toNNReal
      (physicalForcing D R s (m + 1 + 1) hm₂ r)) volume t₀ t := by
    have hpair : ContinuousOn
        (fun r ↦ ((t - r).toNNReal, physicalForcing D R s (m + 1 + 1) hm₂ r)) (Icc t₀ t) :=
      ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousOn).prodMk
        ((continuousOn_physicalForcing hR hs (m + 1 + 1) hm₂).mono fun r hr ↦
          ⟨ht₀.trans_le hr.1, hr.2.trans ht.2.le⟩)
    have hc := (vectorHeatSemigroup 3 (m + 1 + 1 + 1)).continuous_apply.comp_continuousOn hpair
    simp only [Function.comp_def, vectorHeatSemigroup_apply] at hc
    exact hc.intervalIntegrable_of_Icc (by linarith)
  have hduh : T.duhamel Af (t - t₀) = ∫ r in t₀..t, vectorLaplacian 3 (m + 1)
      (vectorHeat 3 (m + 1 + 1 + 1) (t - r).toNNReal
        (physicalForcing D R s (m + 1 + 1) hm₂ r)) := by
    have h := intervalIntegral_vectorHeat_eq_duhamel (K := m + 1) (t₀ := t₀) (ρ := t - t₀)
      (b := b) (fun r ↦ vectorLaplacian 3 (m + 1) (physicalForcing D R s (m + 1 + 1) hm₂ r))
      ⟨hρ₁.1.le, hρ₁.2.le⟩
    rw [add_sub_cancel] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun r _ ↦ vectorHeat_vectorLaplacian _ _
  have key : vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 1 + 1) hm₂ t) =
      T.realOrbit Ax (t - t₀) + leraySobolev 3 (m + 1) (T.duhamel Af (t - t₀)) := by
    rw [hU₂, map_add, ← vectorHeat_vectorLaplacian, ← leraySobolev_vectorLaplacian,
      ← (vectorLaplacian 3 (m + 1)).intervalIntegral_comp_comm hint, ← hduh]
    rfl
  rw [map_add, ← add_assoc, hft]
  exact congrArg (· + leraySobolev 3 (m + 1) (physicalForcing D R s m hm t)) key.symm

/-- **Time regularity of the physical correction.** Above the threshold radius and for
`s ∈ [0, 1]`, the physical correction is continuously differentiable on `(0, 1)` with values in
every vector `Hᵐ⁺¹`. -/
theorem contDiffOn_one_physicalCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (hm : (3 : ℝ) < 2 * m) :
    ContDiffOn ℝ 1 (physicalCorrection D R s m hm) (Ioo 0 1) := by
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (physicalCorrection D R s m hm)
      (vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 2)
          (three_lt_two_mul_succ (three_lt_two_mul_succ hm)) t) +
        leraySobolev 3 (m + 1) (physicalForcing D R s m hm t)) t :=
    fun t ht ↦ hasDerivAt_physicalCorrection hR hs hm ht
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioc 0 1 := Ioo_subset_Ioc_self
  have hc : ContinuousOn (fun t ↦ vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 2)
      (three_lt_two_mul_succ (three_lt_two_mul_succ hm)) t) +
        leraySobolev 3 (m + 1) (physicalForcing D R s m hm t)) (Ioo 0 1) :=
    ((vectorLaplacian 3 (m + 1)).continuous.comp_continuousOn
      ((continuousOn_physicalCorrection hR hs (m + 2) _).mono hsub)).add
      ((leraySobolev 3 (m + 1)).continuous.comp_continuousOn
        ((continuousOn_physicalForcing hR hs m hm).mono hsub))
  refine contDiffOn_zero.mpr (hc.congr fun t ht ↦ (hd t ht).deriv)

/-- **The time bootstrap.** Above the threshold radius and for `s ∈ [0, 1]`, if at every
order of time regularity `j` the physical forcings are `Cʲ` on `(0, 1)` in every vector `Hᵐ⁺¹`
whenever the physical corrections are, then the physical corrections are `Cʲ` on `(0, 1)` in
every vector `Hᵐ⁺¹` for every `j`: the equation `∂ₜ u = Δ u + Π g` gains one time derivative from
the corrections two orders higher and from the forcing. -/
theorem contDiffOn_physicalCorrection_of_forcing (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hg : ∀ j : ℕ, (∀ (m : ℕ) (hm : (3 : ℝ) < 2 * m),
        ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1)) →
      ∀ (m : ℕ) (hm : (3 : ℝ) < 2 * m), ContDiffOn ℝ j (physicalForcing D R s m hm) (Ioo 0 1)) :
    ∀ (j m : ℕ) (hm : (3 : ℝ) < 2 * m),
      ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1) := by
  intro j
  induction j with
  | zero =>
    intro m hm
    exact contDiffOn_zero.mpr
      ((continuousOn_physicalCorrection hR hs m hm).mono Ioo_subset_Ioc_self)
  | succ j ih =>
    intro m hm
    have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (physicalCorrection D R s m hm)
        (vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 2)
            (three_lt_two_mul_succ (three_lt_two_mul_succ hm)) t) +
          leraySobolev 3 (m + 1) (physicalForcing D R s m hm t)) t :=
      fun t ht ↦ hasDerivAt_physicalCorrection hR hs hm ht
    rw [show ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hc : ContDiffOn ℝ j (fun t ↦ vectorLaplacian 3 (m + 1) (physicalCorrection D R s (m + 2)
        (three_lt_two_mul_succ (three_lt_two_mul_succ hm)) t) +
          leraySobolev 3 (m + 1) (physicalForcing D R s m hm t)) (Ioo 0 1) :=
      ((vectorLaplacian 3 (m + 1)).contDiff.comp_contDiffOn (ih (m + 2) _)).add
        ((leraySobolev 3 (m + 1)).contDiff.comp_contDiffOn (hg j ih m hm))
    exact hc.congr fun t ht ↦ (hd t ht).deriv

end NavierStokes.Nonuniqueness

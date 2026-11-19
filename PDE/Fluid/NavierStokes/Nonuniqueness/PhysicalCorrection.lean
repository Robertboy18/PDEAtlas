/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.CorrectionSmoothness
public import PDE.Parabolic.Heat.WholeSpace.VectorSemigroup

/-!
# The ancient correction in physical variables

The physical correction is `u_cor(t, x) = t^{-1/2} U_cor(log t, x / √t)` for `0 < t ≤ 1`. With
`τ = log t` it is the image of `U_cor(τ)` under `P_τ v = e^{-τ/2} v(e^{-τ/2} ·)`
(`physicalMap`), and as a path in vector `Hᵐ⁺¹` it is `physicalCorrection`, built from the lift
`correctionLift` of the correction to vector `Hᵐ⁺¹`. It is continuous on `(0, 1]` in every
`Hᵐ⁺¹`, since dilations are strongly continuous.

The map `P_τ` turns the free self-similar evolution into the heat evolution,
`P_τ S₀(τ - σ) = e^{(e^τ - e^σ) Δ} P_σ`, and commutes with the Leray projection. With the
substitution `r = log s` in the Duhamel integral, the free forward mild equation of the
correction becomes the heat Duhamel formula in physical variables (`physicalCorrection_eq`):
for `0 < t₀ ≤ t ≤ 1`,

`u_cor(t) = e^{(t - t₀) Δ} u_cor(t₀) + Π ∫_{t₀}^t e^{(t - s) Δ} g(s) ds`,

with the physical forcing `g(s) = s⁻¹ P_{log s} (F(log s) + A(log s) U_cor(log s))`
(`physicalForcing`), which has no drift term.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-! ### The physical change of variables -/

/-- The physical factor `e^{-τ/2}`; at `τ = log t` it is `t^{-1/2}`. -/
def physicalFactor (τ : ℝ) : ℝ :=
  Real.exp (-(τ / 2))

theorem physicalFactor_pos (τ : ℝ) : 0 < physicalFactor τ :=
  Real.exp_pos _

theorem one_le_physicalFactor {τ : ℝ} (hτ : τ ≤ 0) : 1 ≤ physicalFactor τ :=
  Real.one_le_exp_iff.mpr (by linarith)

theorem continuous_physicalFactor : Continuous physicalFactor :=
  Real.continuous_exp.comp (continuous_id.div_const 2).neg

/-- At `τ = log t` the physical factor is `t^{-1/2}`. -/
theorem physicalFactor_log {t : ℝ} (ht : 0 < t) :
    physicalFactor (Real.log t) = (Real.sqrt t)⁻¹ := by
  rw [physicalFactor, Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, Real.rpow_def_of_pos ht]
  ring_nf

/-- The map `P_τ v = e^{-τ/2} v(e^{-τ/2} ·)` from similarity variables at time `τ` to physical
variables at time `e^τ`, on vector `Hᵏ`. -/
def physicalMap (k : ℕ) (τ : ℝ) : VectorH 3 k →L[ℝ] VectorH 3 k :=
  physicalFactor τ • vectorDilation 3 k (physicalFactor τ) (physicalFactor_pos τ).ne'

theorem physicalMap_apply (k : ℕ) (τ : ℝ) (v : VectorH 3 k) :
    physicalMap k τ v =
      physicalFactor τ • vectorDilation 3 k (physicalFactor τ) (physicalFactor_pos τ).ne' v :=
  rfl

/-- In physical variables the free self-similar evolution is the heat evolution:
`P_τ S₀(τ - σ) = e^{(e^τ - e^σ) Δ} P_σ` for `σ ≤ τ`. -/
theorem physicalMap_vectorSelfsimilarHeat {k : ℕ} {σ τ : ℝ} (hστ : σ ≤ τ) (v : VectorH 3 k) :
    physicalMap k τ (vectorSelfsimilarHeat 3 k (τ - σ).toNNReal v) =
      vectorHeat 3 k (Real.exp τ - Real.exp σ).toNNReal (physicalMap k σ v) := by
  have hh : ((τ - σ).toNNReal : ℝ) = τ - σ := Real.coe_toNNReal _ (sub_nonneg.mpr hστ)
  have hfac : physicalFactor τ * selfsimilarFactor (τ - σ).toNNReal = physicalFactor σ := by
    rw [physicalFactor, physicalFactor, selfsimilarFactor, hh, ← Real.exp_add]
    ring_nf
  have htime : parabolicHeatTime (physicalFactor σ) (Real.exp τ - Real.exp σ).toNNReal =
      selfsimilarHeatTime (τ - σ).toNNReal := by
    apply NNReal.coe_injective
    rw [coe_parabolicHeatTime, coe_selfsimilarHeatTime, hh,
      Real.coe_toNNReal _ (sub_nonneg.mpr (Real.exp_le_exp.mpr hστ))]
    have e1 : physicalFactor σ ^ 2 = Real.exp (-σ) := by
      rw [physicalFactor, sq, ← Real.exp_add]
      ring_nf
    rw [e1, mul_sub, ← Real.exp_add, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      show -σ + τ = τ - σ by ring]
  rw [physicalMap_apply, physicalMap_apply, vectorSelfsimilarHeat_eq_vectorDilation, map_smul,
    map_smul, vectorHeat_vectorDilation, htime, smul_smul, ← vectorDilation_mul,
    vectorDilation_congr hfac _ (physicalFactor_pos σ).ne', hfac]

/-- The physical map commutes with the Leray projection. -/
theorem leraySobolev_physicalMap (k : ℕ) (τ : ℝ) (v : VectorH 3 k) :
    leraySobolev 3 k (physicalMap k τ v) = physicalMap k τ (leraySobolev 3 k v) := by
  rw [physicalMap_apply, physicalMap_apply, map_smul, leraySobolev_vectorDilation]

/-- A path continuous on a set of nonpositive times stays continuous in physical variables. -/
theorem continuousOn_physicalMap {k : ℕ} {w : ℝ → VectorH 3 k} {S : Set ℝ} (hS : S ⊆ Iic 0)
    (hw : ContinuousOn w S) : ContinuousOn (fun τ ↦ physicalMap k τ (w τ)) S := by
  let g : ℝ → VectorH 3 k × Ici (1 : ℝ) := fun τ ↦
    (w τ, ⟨max 1 (physicalFactor τ), le_max_left _ _⟩)
  have hg : ContinuousOn g S := hw.prodMk
    (Continuous.subtype_mk (continuous_const.max continuous_physicalFactor) _).continuousOn
  have hd := (continuous_vectorDilation_Ici (n := 3) (k := k) one_pos).comp_continuousOn hg
  refine (continuous_physicalFactor.continuousOn.smul hd).congr fun τ hτ ↦ ?_
  have hmax : max 1 (physicalFactor τ) = physicalFactor τ :=
    max_eq_right (one_le_physicalFactor (hS hτ))
  have h := congrArg (fun L : VectorH 3 k →L[ℝ] VectorH 3 k ↦ physicalFactor τ • L (w τ))
    (vectorDilation_congr (n := 3) (k := k) hmax (one_pos.trans_le (le_max_left _ _)).ne'
      (physicalFactor_pos τ).ne')
  exact h.symm

/-! ### The lifts and the physical correction -/

variable (D : UnstableProfile) (R s : ℝ)

/-- The lift of the ancient correction to vector `Hᵐ⁺¹`, a path with `IsCorrectionLift`
when one exists (above the threshold radius and for `s ∈ [0, 1]`), and zero otherwise. -/
def correctionLift (m : ℕ) (hm : (3 : ℝ) < 2 * m) : ℝ → VectorH 3 (m + 1) := by
  classical
  exact if h : ∃ V, IsCorrectionLift D R s m hm V then h.choose else 0

/-- The physical correction `u_cor(t) = t^{-1/2} U_cor(log t, · / √t)` as a path in vector
`Hᵐ⁺¹`. -/
def physicalCorrection (m : ℕ) (hm : (3 : ℝ) < 2 * m) (t : ℝ) : VectorH 3 (m + 1) :=
  physicalMap (m + 1) (Real.log t) (correctionLift D R s m hm (Real.log t))

/-- The physical forcing `g(t) = t⁻¹ P_{log t} (F(log t) + A(log t) U_cor(log t))` of the
correction in vector `Hᵐ⁺¹`: the integrand of the lift equation of order `m + 2` in physical
variables, with the cutoff forcing and the operator family of order `m + 1` frozen at the
correction. -/
def physicalForcing (m : ℕ) (hm : (3 : ℝ) < 2 * m) (t : ℝ) : VectorH 3 (m + 1) :=
  t⁻¹ • physicalMap (m + 1) (Real.log t) (liftForcing D R (m + 1) (three_lt_two_mul_succ hm)
    (correctionLift D R s (m + 1) (three_lt_two_mul_succ hm)) (Real.log t))

variable {D R s}

/-- Above the threshold radius and for `s ∈ [0, 1]` the chosen lift is a lift. -/
theorem isCorrectionLift_correctionLift (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (hm : (3 : ℝ) < 2 * m) : IsCorrectionLift D R s m hm (correctionLift D R s m hm) := by
  have h := exists_correctionLift hR hs m hm
  unfold correctionLift
  split_ifs
  exact h.choose_spec

/-- Two lifts of the same order agree at nonpositive times. -/
theorem IsCorrectionLift.eqOn {m : ℕ} {hm : (3 : ℝ) < 2 * m} {V W : ℝ → VectorH 3 (m + 1)}
    (hV : IsCorrectionLift D R s m hm V) (hW : IsCorrectionLift D R s m hm W) :
    EqOn V W (Iic 0) := fun τ hτ ↦
  vectorLowerOrderCLM_injective _ isOpen_univ ((hV.2.1 τ hτ).trans (hW.2.1 τ hτ).symm)

/-- Forgetting the top order of the lift of order `m + 2` gives the lift of order `m + 1`. -/
theorem vectorLower_correctionLift_succ (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : (3 : ℝ) < 2 * m) {τ : ℝ} (hτ : τ ≤ 0) :
    vectorLower 3 (m + 1) (correctionLift D R s (m + 1) (three_lt_two_mul_succ hm) τ) =
      correctionLift D R s m hm τ := by
  apply vectorLowerOrderCLM_injective (three_le_succ_of_three_lt_two_mul hm) isOpen_univ
  rw [(isCorrectionLift_correctionLift hR hs m hm).2.1 τ hτ, vectorLower,
    vectorLowerOrderCLM_trans_apply]
  exact (isCorrectionLift_correctionLift hR hs (m + 1) _).2.1 τ hτ

/-- Above the threshold radius and for `s ∈ [0, 1]`, every lift of the correction is
divergence-free at nonpositive times. -/
theorem IsCorrectionLift.leraySobolev_eq (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {m : ℕ} {hm : (3 : ℝ) < 2 * m} {V : ℝ → VectorH 3 (m + 1)}
    (hV : IsCorrectionLift D R s m hm V) {τ : ℝ} (hτ : τ ≤ 0) :
    leraySobolev 3 (m + 1) (V τ) = V τ := by
  apply vectorLowerOrderCLM_injective (three_le_succ_of_three_lt_two_mul hm) isOpen_univ
  rw [vectorLowerOrderCLM_leraySobolev, hV.2.1 τ hτ,
    leraySobolev_ancientLift_ancientCorrection hR hs hτ]

/-- Above the threshold radius and for `s ∈ [0, 1]`, the physical correction is divergence-free
at every time `0 < t ≤ 1`. -/
theorem leraySobolev_physicalCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    leraySobolev 3 (m + 1) (physicalCorrection D R s m hm t) =
      physicalCorrection D R s m hm t := by
  rw [physicalCorrection, leraySobolev_physicalMap,
    (isCorrectionLift_correctionLift hR hs m hm).leraySobolev_eq hR hs
      (Real.log_nonpos ht.le ht1)]

/-- Above the threshold radius and for `s ∈ [0, 1]`, the physical correction is continuous on
`(0, 1]` in every vector `Hᵐ⁺¹`. -/
theorem continuousOn_physicalCorrection (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (hm : (3 : ℝ) < 2 * m) :
    ContinuousOn (physicalCorrection D R s m hm) (Ioc 0 1) := by
  have hlog : ContinuousOn Real.log (Ioc 0 1) :=
    Real.continuousOn_log.mono fun t ht ↦ ht.1.ne'
  have hmaps : MapsTo Real.log (Ioc 0 1) (Iic 0) := fun t ht ↦ Real.log_nonpos ht.1.le ht.2
  have h := (continuousOn_physicalMap (k := m + 1) subset_rfl
    (isCorrectionLift_correctionLift hR hs m hm).1).comp hlog hmaps
  exact h

/-! ### The heat Duhamel formula in physical variables -/

/-- Forgetting the top order of the lift equation of order `m + 2` gives the free mild equation
in vector `Hᵐ⁺¹` with the projected free evolution, which does not gain a derivative. -/
theorem IsCorrectionLift.vectorLower_eq {m : ℕ} {hm : (3 : ℝ) < 2 * m}
    {V : ℝ → VectorH 3 (m + 2)}
    (hV : IsCorrectionLift D R s (m + 1) (three_lt_two_mul_succ hm) V) {σ τ : ℝ} (hστ : σ ≤ τ)
    (hτ : τ ≤ 0) :
    vectorLower 3 (m + 1) (V τ) =
      vectorSelfsimilarHeat 3 (m + 1) (τ - σ).toNNReal (vectorLower 3 (m + 1) (V σ)) +
        ∫ r in σ..τ, leraySobolev 3 (m + 1) (vectorSelfsimilarHeat 3 (m + 1) (τ - r).toNNReal
          (liftForcing D R (m + 1) (three_lt_two_mul_succ hm) V r)) := by
  obtain ⟨hVc, -, hVeq⟩ := hV
  have hsub : Icc σ τ ⊆ Iic 0 := fun r hr ↦ hr.2.trans hτ
  have hGc := continuousOn_liftForcing D R (three_lt_two_mul_succ hm) (hVc.mono hsub)
  have hint := intervalIntegrable_forwardIntegrand_of_continuousOn hστ
    (continuousOn_projectedSelfsimilarHeatGainKernel_apply (n := 3) (k := m + 1))
    (fun r hr _ ↦ norm_projectedSelfsimilarHeatGainKernel_le_selfsimilarForwardGainConstant
      (by norm_num) hr) hGc
  have hI : vectorLower 3 (m + 1) (∫ r in σ..τ, projectedSelfsimilarHeatGainKernel 3 (m + 1)
      (τ - r) (liftForcing D R (m + 1) (three_lt_two_mul_succ hm) V r)) =
      ∫ r in σ..τ, leraySobolev 3 (m + 1) (vectorSelfsimilarHeat 3 (m + 1) (τ - r).toNNReal
        (liftForcing D R (m + 1) (three_lt_two_mul_succ hm) V r)) := by
    rw [← (vectorLower 3 (m + 1)).intervalIntegral_comp_comm hint,
      intervalIntegral.integral_of_le hστ, intervalIntegral.integral_of_le hστ,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun r hr ↦
      vectorLower_projectedSelfsimilarHeatGainKernel (sub_pos.mpr hr.2) _
  rw [hVeq σ τ hστ hτ, map_add, vectorLower_vectorSelfsimilarHeat, hI]

/-- **The heat Duhamel formula of the correction in physical variables.** Above the threshold
radius and for `s ∈ [0, 1]`, for `0 < t₀ ≤ t ≤ 1` the physical correction in vector `Hᵐ⁺¹` solves

`u(t) = e^{(t - t₀) Δ} u(t₀) + Π ∫_{t₀}^t e^{(t - r) Δ} g(r) dr`

with the physical forcing `g` (`physicalForcing`). -/
theorem physicalCorrection_eq (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t₀ t : ℝ} (ht₀ : 0 < t₀) (h : t₀ ≤ t) (ht : t ≤ 1) :
    physicalCorrection D R s m hm t =
      vectorHeat 3 (m + 1) (t - t₀).toNNReal (physicalCorrection D R s m hm t₀) +
        leraySobolev 3 (m + 1) (∫ r in t₀..t,
          vectorHeat 3 (m + 1) (t - r).toNNReal (physicalForcing D R s m hm r)) := by
  have hm' := three_lt_two_mul_succ hm
  have hV := isCorrectionLift_correctionLift hR hs (m + 1) hm'
  have ht0 : 0 < t := ht₀.trans_le h
  have hστ : Real.log t₀ ≤ Real.log t := Real.log_le_log ht₀ h
  have hτ : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht
  have hσ : Real.log t₀ ≤ 0 := hστ.trans hτ
  have hexpτ : Real.exp (Real.log t) = t := Real.exp_log ht0
  have hlow := IsCorrectionLift.vectorLower_eq (hm := hm) hV hστ hτ
  rw [vectorLower_correctionLift_succ hR hs hm hτ,
    vectorLower_correctionLift_succ hR hs hm hσ] at hlow
  have hsub : Icc (Real.log t₀) (Real.log t) ⊆ Iic 0 := fun r hr ↦ hr.2.trans hτ
  have hGc : ContinuousOn (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm'))
      (Icc (Real.log t₀) (Real.log t)) :=
    (continuousOn_liftForcing D R hm' hV.1).mono hsub
  -- The integrand in similarity variables is continuous.
  have hφc : ContinuousOn (fun r ↦ leraySobolev 3 (m + 1)
      (vectorSelfsimilarHeatSemigroup 3 (m + 1) (Real.log t - r).toNNReal
        (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') r)))
      (Icc (Real.log t₀) (Real.log t)) := by
    have hpair : ContinuousOn (fun r ↦ ((Real.log t - r).toNNReal,
        liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') r))
        (Icc (Real.log t₀) (Real.log t)) :=
      ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousOn).prodMk
        hGc
    have h' := (vectorSelfsimilarHeatSemigroup 3 (m + 1)).continuous_apply.comp_continuousOn
      hpair
    exact (leraySobolev 3 (m + 1)).continuous.comp_continuousOn h'
  simp only [vectorSelfsimilarHeatSemigroup_apply] at hφc
  -- The integrand in physical variables is continuous.
  have hψc : ContinuousOn (fun r ↦ vectorHeatSemigroup 3 (m + 1) (t - Real.exp r).toNNReal
      (physicalMap (m + 1) r (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') r)))
      (Icc (Real.log t₀) (Real.log t)) := by
    have hpair : ContinuousOn (fun r ↦ ((t - Real.exp r).toNNReal, physicalMap (m + 1) r
        (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') r)))
        (Icc (Real.log t₀) (Real.log t)) :=
      ((continuous_real_toNNReal.comp
        (continuous_const.sub Real.continuous_exp)).continuousOn).prodMk
        (continuousOn_physicalMap hsub hGc)
    have h' := (vectorHeatSemigroup 3 (m + 1)).continuous_apply.comp_continuousOn hpair
    dsimp only [Function.comp_def] at h'
    exact h'
  simp only [vectorHeatSemigroup_apply] at hψc
  unfold physicalCorrection
  rw [hlow, map_add, physicalMap_vectorSelfsimilarHeat hστ, hexpτ, Real.exp_log ht₀,
    ← (physicalMap (m + 1) (Real.log t)).intervalIntegral_comp_comm
      (hφc.intervalIntegrable_of_Icc hστ)]
  have e1 : (∫ r in Real.log t₀..Real.log t, physicalMap (m + 1) (Real.log t)
      (leraySobolev 3 (m + 1) (vectorSelfsimilarHeat 3 (m + 1) (Real.log t - r).toNNReal
        (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') r)))) =
      ∫ r in Real.log t₀..Real.log t, leraySobolev 3 (m + 1)
        (vectorHeat 3 (m + 1) (t - Real.exp r).toNNReal (physicalMap (m + 1) r
          (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') r))) := by
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le hστ] at hr
    rw [← leraySobolev_physicalMap, physicalMap_vectorSelfsimilarHeat hr.2, hexpτ]
  have e2 : (∫ r in t₀..t, vectorHeat 3 (m + 1) (t - r).toNNReal (physicalForcing D R s m hm r)) =
      ∫ r in t₀..t, r⁻¹ • ((fun u ↦ vectorHeat 3 (m + 1) (t - Real.exp u).toNNReal
        (physicalMap (m + 1) u (liftForcing D R (m + 1) hm'
          (correctionLift D R s (m + 1) hm') u))) ∘ Real.log) r := by
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le h] at hr
    have hr0 : 0 < r := ht₀.trans_le hr.1
    simp only [Function.comp_apply, physicalForcing, map_smul, Real.exp_log hr0]
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun u ↦ vectorHeat 3 (m + 1) (t - Real.exp u).toNNReal
      (physicalMap (m + 1) u (liftForcing D R (m + 1) hm' (correctionLift D R s (m + 1) hm') u)))
    (f := Real.log) (f' := fun r ↦ r⁻¹) (a := t₀) (b := t)
    (Real.continuousOn_log.mono fun r hr ↦ by
      rw [uIcc_of_le h] at hr
      exact (ht₀.trans_le hr.1).ne')
    (fun r hr ↦ Real.hasDerivAt_log (by
      rw [min_eq_left h] at hr
      exact (ht₀.trans hr.1).ne'))
    (fun r hr ↦ by
      rw [min_eq_left h] at hr
      exact inv_nonneg.mpr (ht₀.trans hr.1).le)
  rw [e1, (leraySobolev 3 (m + 1)).intervalIntegral_comp_comm (hψc.intervalIntegrable_of_Icc hστ),
    e2, hsubst]

end NavierStokes.Nonuniqueness

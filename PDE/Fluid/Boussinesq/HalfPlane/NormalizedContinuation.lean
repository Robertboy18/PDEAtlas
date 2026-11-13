/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Normalized
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Inverse
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Calculus

/-!
# The continuation criterion for the normalized rescaled solution

Let the normalized rescaled solution `normalizedSolution k Q J` have the finite life span `T`. Under
the hypotheses of `IsNormalizationSetting.continuationIntegral_normalizedSolution_eq_top` (symmetric
slices, the physical continuation criterion, and `ω_x(0, t_end) = 0` when the interval where
`ω_x(0, t) ≠ 0` ends before the physical life span) its continuation integral is infinite. Changing
variables `σ = τ(t)` gives

```text
∫₀^T (‖∇ũ‖_∞ + ‖∇θ̃‖_∞) dσ = ∫_{J⁺} (‖∇u‖_∞ + C ‖∇θ‖_∞) dt,
```

with `J⁺` the nonnegative times of `J` and `C` the vorticity scale
(`IsNormalizationSetting.continuationIntegral_normalizedSolution`).

## Main results

* `iSup_enorm_fderiv_const_smul_comp_smul`: suprema of dilated gradients.
* `IsNormalizationSetting.continuationIntegral_normalizedSolution`.
* `IsNormalizationSetting.continuationIntegral_normalizedSolution_eq_top`.

## How it works

The change of variables uses `‖∇ũ(σ)‖_∞ = C ‖∇u(t)‖_∞`, `‖∇θ̃(σ)‖_∞ = C² ‖∇θ(t)‖_∞` and
`dσ = C⁻¹ dt`. For the criterion we argue by contradiction. If the rescaled integral were finite,
then `|ũ_x(0, σ)| ≤ ‖∇ũ(σ)‖_∞` and `d/dσ log C_ω = c_ω = c_l(0)/2 + ũ_x(0, σ)` (the dilation rate is
constant) would bound `C_ω` above and below on `[0, T)`, so the physical end time `t_end = ∫₀^T C_ω`
of the interval would be finite. If the end time were less than the physical life span, then
`ω_x(0, t_end) = 0`, while `ω_x(0, t) = ω_x(0, 0)/(C_ω C_l)` stays away from zero. Otherwise the end
time is the physical life span, the physical continuation integral `∫ (‖∇u‖_∞ + ‖∇θ‖_∞)` is
infinite, and `‖∇u‖_∞ + C ‖∇θ‖_∞ ≥ min(1, e^{-K}) (‖∇u‖_∞ + ‖∇θ‖_∞)` makes the rescaled integral
infinite.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory PDE.Analysis IncompressibleFlow
open scoped Topology ENNReal

namespace Boussinesq.HalfPlane

/-- **Suprema of dilated gradients.** For `c ≥ 0` and `L > 0`, the supremum over the upper
half-plane of the gradient of `y ↦ c g(L y)` is `c L` times that of `g`. -/
theorem iSup_enorm_fderiv_const_smul_comp_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ^2 → E} (hg : Differentiable ℝ g) {c L : ℝ} (hc : 0 ≤ c)
    (hL : 0 < L) :
    ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ c • g (L • y)) x‖ₑ =
      ENNReal.ofReal (c * L) * ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ g x‖ₑ := by
  have hpt (x : ℝ^2) : ‖fderiv ℝ (fun y ↦ c • g (L • y)) x‖ₑ =
      ENNReal.ofReal (c * L) * ‖fderiv ℝ g (L • x)‖ₑ := by
    have h1 : HasFDerivAt (fun y : ℝ^2 ↦ L • y) (L • ContinuousLinearMap.id ℝ (ℝ^2)) x :=
      (hasFDerivAt_id x).const_smul L
    have h2 := ((hg (L • x)).hasFDerivAt.comp x h1).const_smul c
    rw [show (fun y ↦ c • g (L • y)) = c • (g ∘ HSMul.hSMul L) from rfl, h2.fderiv]
    have hcomp : (fderiv ℝ g (L • x)).comp (L • ContinuousLinearMap.id ℝ (ℝ^2)) =
        L • fderiv ℝ g (L • x) := by
      ext v
      simp
    rw [hcomp, smul_smul, enorm_smul, Real.enorm_eq_ofReal (mul_nonneg hc hL.le)]
  simp_rw [hpt, ENNReal.mul_iSup]
  exact iSup_upperHalfPlane_smul (fun x ↦ ENNReal.ofReal (c * L) * ‖fderiv ℝ g x‖ₑ) hL

/-- A function continuous on the closed upper half-plane is bounded at its points by its supremum
over the open upper half-plane. -/
theorem enorm_le_iSup_upperHalfPlane {E : Type*} [NormedAddCommGroup E] {F : ℝ^2 → E}
    (hF : Continuous F) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖F x‖ₑ ≤ ⨆ y ∈ upperHalfPlane, ‖F y‖ₑ := by
  have hclosed : IsClosed {y : ℝ^2 | ‖F y‖ₑ ≤ ⨆ z ∈ upperHalfPlane, ‖F z‖ₑ} :=
    isClosed_le (continuous_enorm.comp hF) continuous_const
  have hsub : upperHalfPlane ⊆ {y : ℝ^2 | ‖F y‖ₑ ≤ ⨆ z ∈ upperHalfPlane, ‖F z‖ₑ} :=
    fun y hy ↦ show ‖F y‖ₑ ≤ _ from le_iSup₂_of_le y hy le_rfl
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_upperHalfPlane] at hcl
  exact hcl hx

namespace IsNormalizationSetting

variable {k : ℕ} {Q : VorticityStreamFields} {α : ℝ} {J₀ J : Set ℝ}
  (h : IsNormalizationSetting k Q α J₀ J)
include h

/-- The clock inverts the rescaled time on `J`. -/
theorem physicalTime_rescaledClock {t : ℝ} (ht : t ∈ J) :
    (normalizedRescaling (canonicalOf k Q) J).physicalTime
      (DynamicRescalingData.rescaledClock (physicalVorticityRate (canonicalOf k Q)) t) = t :=
  DynamicRescalingData.physicalTime_ofPhysicalRates_rescaledClock h.isOpen h.ordConnected
    h.zero_mem h.continuousOn_physicalVorticityRate ht

/-- The supremum of the gradient of the rescaled velocity is `C_ω` times that of the physical
velocity at the clock time. -/
theorem iSup_velocity {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) :
    ⨆ x ∈ upperHalfPlane,
        ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity (normalizedSolution k Q J) y σ) x‖ₑ =
      ENNReal.ofReal ((normalizedRescaling (canonicalOf k Q) J).vorticityScale σ) *
        ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity (canonicalOf k Q) y
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ)) x‖ₑ := by
  set D := normalizedRescaling (canonicalOf k Q) J
  have ht := h.subset (physicalTime_mem hσ)
  have hψ := h.classical.regularity.streamFunction_spatial_contDiff ht
  have hC : 0 < D.vorticityScale σ := DynamicRescalingData.physicalVorticityScale_pos _ _
  have hL : 0 < D.spatialScale σ := DynamicRescalingData.physicalSpatialScale_pos _ _
  have hu : Differentiable ℝ
      (fun y ↦ vorticityStreamVelocity (canonicalOf k Q) y (D.physicalTime σ)) :=
    (contDiff_planarStreamVelocity _ hψ).differentiable (by norm_num)
  have hfun : (fun y ↦ vorticityStreamVelocity (normalizedSolution k Q J) y σ) =
      fun y ↦ (D.vorticityScale σ / D.spatialScale σ) •
        (fun z ↦ vorticityStreamVelocity (canonicalOf k Q) z (D.physicalTime σ))
          (D.spatialScale σ • y) := by
    funext y
    exact vorticityStreamVelocity_dynamicallyRescaledFields D _ y σ
      ((hψ.differentiable (by norm_num)) _)
  rw [hfun, iSup_enorm_fderiv_const_smul_comp_smul hu (div_pos hC hL).le hL,
    div_mul_cancel₀ _ hL.ne']

/-- The supremum of the gradient of the rescaled temperature is `C_ω²` times that of the
physical temperature at the clock time. -/
theorem iSup_temperature {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) :
    ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ (normalizedSolution k Q J).temperature y σ) x‖ₑ =
      ENNReal.ofReal ((normalizedRescaling (canonicalOf k Q) J).vorticityScale σ ^ 2) *
        ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ (canonicalOf k Q).temperature y
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ)) x‖ₑ := by
  set D := normalizedRescaling (canonicalOf k Q) J
  have ht := h.subset (physicalTime_mem hσ)
  have hθ := h.classical.regularity.temperature_spatial_contDiff ht
  have hL : 0 < D.spatialScale σ := DynamicRescalingData.physicalSpatialScale_pos _ _
  have hCθ : 0 ≤ D.temperatureScale σ :=
    div_nonneg (sq_nonneg _) hL.le
  have hfun : (fun y ↦ (normalizedSolution k Q J).temperature y σ) =
      fun y ↦ D.temperatureScale σ •
        (fun z ↦ (canonicalOf k Q).temperature z (D.physicalTime σ)) (D.spatialScale σ • y) :=
    rfl
  rw [hfun, iSup_enorm_fderiv_const_smul_comp_smul (hθ.differentiable (by norm_num)) hCθ hL]
  congr 2
  change D.vorticityScale σ ^ 2 / D.spatialScale σ * D.spatialScale σ = _
  field_simp

/-- The nonnegative rescaled times are the rescaled times of the nonnegative times of `J`. -/
theorem lifeSpan_normalizedLifeSpan_eq_image :
    lifeSpan (normalizedLifeSpan k Q J) =
      DynamicRescalingData.rescaledClock (physicalVorticityRate (canonicalOf k Q)) ''
        (J ∩ Ici 0) := by
  have hmono := DynamicRescalingData.strictMonoOn_rescaledClock h.isOpen h.ordConnected h.zero_mem
    h.continuousOn_physicalVorticityRate
  rw [h.lifeSpan_normalizedLifeSpan]
  ext σ
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hσ0⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    rw [mem_Ici, ← hmono.le_iff_le h.zero_mem ht, DynamicRescalingData.rescaledClock_zero]
    exact hσ0
  · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    rw [mem_Ici, ← DynamicRescalingData.rescaledClock_zero
      (physicalVorticityRate (canonicalOf k Q))]
    exact hmono.monotoneOn h.zero_mem ht ht0

/-- **Change of variables in the continuation integral.** The continuation integral of the
normalized rescaled solution over its life span is `∫ (‖∇u‖_∞ + C ‖∇θ‖_∞) dt` over the
nonnegative times of `J`, with the physical vorticity scale `C(t) = exp ∫₀ᵗ b`. -/
theorem continuationIntegral_normalizedSolution :
    continuationIntegral (normalizedSolution k Q J) (normalizedLifeSpan k Q J) =
      ∫⁻ t in J ∩ Ici 0,
        ((⨆ x ∈ upperHalfPlane,
            ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity (canonicalOf k Q) y t) x‖ₑ) +
          ENNReal.ofReal (DynamicRescalingData.physicalVorticityScale
              (physicalVorticityRate (canonicalOf k Q)) t) *
            ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ (canonicalOf k Q).temperature y t) x‖ₑ) := by
  set b := physicalVorticityRate (canonicalOf k Q)
  have hs : MeasurableSet (J ∩ Ici 0) := h.isOpen.measurableSet.inter measurableSet_Ici
  have hderiv : ∀ t ∈ J ∩ Ici 0, HasDerivWithinAt (DynamicRescalingData.rescaledClock b)
      (DynamicRescalingData.physicalVorticityScale b t)⁻¹ (J ∩ Ici 0) t := fun t ht ↦
    (DynamicRescalingData.hasStrictDerivAt_rescaledClock h.isOpen h.ordConnected h.zero_mem
      h.continuousOn_physicalVorticityRate ht.1).hasDerivAt.hasDerivWithinAt
  have hinj : InjOn (DynamicRescalingData.rescaledClock b) (J ∩ Ici 0) :=
    (DynamicRescalingData.strictMonoOn_rescaledClock h.isOpen h.ordConnected h.zero_mem
      h.continuousOn_physicalVorticityRate).injOn.mono inter_subset_left
  rw [continuationIntegral, h.lifeSpan_normalizedLifeSpan_eq_image,
    lintegral_image_eq_lintegral_abs_deriv_mul hs hderiv hinj]
  refine setLIntegral_congr_fun hs fun t ht ↦ ?_
  have hσ : DynamicRescalingData.rescaledClock b t ∈ normalizedTimes k Q J := ⟨t, ht.1, rfl⟩
  have hT := h.physicalTime_rescaledClock ht.1
  have hC : 0 < DynamicRescalingData.physicalVorticityScale b t :=
    DynamicRescalingData.physicalVorticityScale_pos _ _
  have hCs : (normalizedRescaling (canonicalOf k Q) J).vorticityScale
      (DynamicRescalingData.rescaledClock b t) =
        DynamicRescalingData.physicalVorticityScale b t := by
    change DynamicRescalingData.physicalVorticityScale b
      ((normalizedRescaling (canonicalOf k Q) J).physicalTime
        (DynamicRescalingData.rescaledClock b t)) = _
    rw [hT]
  rw [h.iSup_velocity hσ, h.iSup_temperature hσ, hT, hCs, abs_of_pos (inv_pos.2 hC), mul_add,
    ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hC).le,
    ← ENNReal.ofReal_mul (inv_pos.2 hC).le, inv_mul_cancel₀ hC.ne', ENNReal.ofReal_one, one_mul]
  congr 3
  field_simp

/-- The vorticity scale of the normalized rescaling starts at one. -/
theorem vorticityScale_zero : (normalizedRescaling (canonicalOf k Q) J).vorticityScale 0 = 1 := by
  change DynamicRescalingData.physicalVorticityScale _
    ((normalizedRescaling (canonicalOf k Q) J).physicalTime 0) = 1
  rw [show (normalizedRescaling (canonicalOf k Q) J).physicalTime 0 = 0 from
    DynamicRescalingData.physicalTime_ofPhysicalRates_zero h.isOpen h.ordConnected h.zero_mem
      h.continuousOn_physicalVorticityRate, DynamicRescalingData.physicalVorticityScale_zero]

/-- `log C_ω(σ) = ∫₀^σ c_ω` at the rescaled times `σ ≥ 0` of `τ(J)`. -/
theorem log_vorticityScale_eq {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) (hσ0 : 0 ≤ σ) :
    Real.log ((normalizedRescaling (canonicalOf k Q) J).vorticityScale σ) =
      ∫ s in (0 : ℝ)..σ, (normalizedRescaling (canonicalOf k Q) J).vorticityRate s := by
  set D := normalizedRescaling (canonicalOf k Q) J
  have hsub : uIcc 0 σ ⊆ normalizedTimes k Q J := by
    rw [uIcc_of_le hσ0]
    exact h.ordConnected_normalizedTimes.out h.zero_mem_normalizedTimes hσ
  have hd : ∀ s ∈ uIcc 0 σ, HasDerivAt (fun r ↦ Real.log (D.vorticityScale r))
      (D.vorticityRate s) s := by
    intro s hs
    have hpos : D.vorticityScale s ≠ 0 := (DynamicRescalingData.physicalVorticityScale_pos _ _).ne'
    have := ((h.satisfiesDynamicRescalingLawsAt (hsub hs)).vorticityScale_hasDerivAt).log hpos
    convert this using 1
    exact (mul_div_cancel_right₀ _ hpos).symm
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((h.continuousOn_vorticityRate.mono hsub).intervalIntegrable)
  rw [hint, h.vorticityScale_zero, Real.log_one, sub_zero]

/-- **The continuation criterion.** Suppose that the physical slices are in the symmetry class at
the nonnegative times of `J`, that the nonnegative times of `J₀` form the physical life span `T_p`
with the physical continuation criterion, and that the nonnegative times of `J` form the life span
`t_end ≤ T_p` with `ω_x(0, t_end) = 0` when `t_end < T_p`. If the life span of the normalized
rescaled solution is finite, its continuation integral is infinite. -/
theorem continuationIntegral_normalizedSolution_eq_top
    (hsym : ∀ t ∈ J, 0 ≤ t →
      IsReflectionSymmetric (fun x ↦ Q.vorticity x t) (fun x ↦ Q.temperature x t))
    {Tp tEnd : ℝ≥0∞} (hJ₀p : ∀ t, 0 ≤ t → (t ∈ J₀ ↔ ENNReal.ofReal t < Tp))
    (hJp : ∀ t, 0 ≤ t → (t ∈ J ↔ ENNReal.ofReal t < tEnd)) (hle : tEnd ≤ Tp)
    (hend : tEnd < Tp → vorticityXAtOrigin (canonicalOf k Q) tEnd.toReal = 0)
    (hcont : Tp ≠ ⊤ → continuationIntegral (canonicalOf k Q) Tp = ⊤)
    (hT : normalizedLifeSpan k Q J ≠ ⊤) :
    continuationIntegral (normalizedSolution k Q J) (normalizedLifeSpan k Q J) = ⊤ := by
  set D := normalizedRescaling (canonicalOf k Q) J
  set b := physicalVorticityRate (canonicalOf k Q)
  set C := DynamicRescalingData.physicalVorticityScale b
  set τ := DynamicRescalingData.rescaledClock b
  set S := normalizedSolution k Q J
  set T := normalizedLifeSpan k Q J
  by_contra hfin
  set τs := T.toReal
  have hlife : ∀ σ, σ ∈ lifeSpan T ↔ σ ∈ normalizedTimes k Q J ∧ 0 ≤ σ := fun σ ↦ by
    rw [h.lifeSpan_normalizedLifeSpan]
    rfl
  have hlt : ∀ σ ∈ lifeSpan T, σ < τs := fun σ hσ ↦
    (ENNReal.ofReal_lt_iff_lt_toReal hσ.1 hT).1 hσ.2
  have hτmem : ∀ t ∈ J, 0 ≤ t → τ t ∈ lifeSpan T := fun t ht ht0 ↦ by
    rw [h.lifeSpan_normalizedLifeSpan_eq_image]
    exact ⟨t, ⟨ht, ht0⟩, rfl⟩
  have hCτ : ∀ t ∈ J, D.vorticityScale (τ t) = C t := fun t ht ↦ by
    change DynamicRescalingData.physicalVorticityScale b (D.physicalTime (τ t)) = _
    rw [h.physicalTime_rescaledClock ht]
  have hIcc : ∀ σ ∈ lifeSpan T, Icc 0 σ ⊆ normalizedTimes k Q J := fun σ hσ ↦
    h.ordConnected_normalizedTimes.out h.zero_mem_normalizedTimes ((hlife σ).1 hσ).1
  -- the rates on the life span
  set cl₀ := D.spatialRate 0
  have hcl : ∀ σ ∈ lifeSpan T, D.spatialRate σ = cl₀ := fun σ hσ ↦
    h.spatialRate_eq hsym ((hlife σ).1 hσ).1 ((hlife σ).1 hσ).2
  have hcw : ∀ σ ∈ lifeSpan T,
      D.vorticityRate σ = cl₀ / 2 + tangentialVelocityXAtOrigin S σ := fun σ hσ ↦ by
    rw [(h.normalization ((hlife σ).1 hσ).1).vorticity_rate_eq, hcl σ hσ]
  have hux_cont : ContinuousOn (tangentialVelocityXAtOrigin S) (normalizedTimes k Q J) :=
    (h.continuousOn_vorticityRate.sub (h.continuousOn_spatialRate.div_const 2)).congr
      fun σ hσ ↦ by
        simp only [Pi.sub_apply]
        rw [(h.normalization hσ).vorticity_rate_eq]
        ring
  -- the strain is bounded by the supremum of the velocity gradient
  have hux : ∀ σ ∈ normalizedTimes k Q J, ‖tangentialVelocityXAtOrigin S σ‖ₑ ≤
      ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity S y σ) x‖ₑ := by
    intro σ hσ
    have hu : ContDiff ℝ 1 (fun y ↦ vorticityStreamVelocity S y σ) :=
      contDiff_planarStreamVelocity _ (h.regularity.streamFunction_spatial_contDiff hσ)
    refine le_trans ?_ (enorm_le_iSup_upperHalfPlane (hu.continuous_fderiv (by norm_num))
      (x := 0) (by simp))
    have hcomp := ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt).comp 0
      (hu.differentiable (by norm_num) 0).hasFDerivAt
    have heq : tangentialVelocityXAtOrigin S σ =
        (fderiv ℝ (fun y ↦ vorticityStreamVelocity S y σ) 0
          (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) 0 := by
      change fderiv ℝ ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ) ∘
        fun y ↦ vorticityStreamVelocity S y σ) 0 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = _
      rw [hcomp.fderiv]
      rfl
    rw [heq, enorm_le_iff_norm_le]
    exact (PiLp.norm_apply_le _ _).trans
      ((ContinuousLinearMap.le_opNorm _ _).trans_eq (by simp))
  have hmeasT : MeasurableSet (lifeSpan T) :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  -- the integral of the strain is bounded by the continuation integral
  have hint : ∀ σ ∈ lifeSpan T, ∫ s in (0 : ℝ)..σ, |tangentialVelocityXAtOrigin S s| ≤
      (continuationIntegral S T).toReal := by
    intro σ hσ
    rw [intervalIntegral.integral_of_le hσ.1, ← ENNReal.ofReal_le_iff_le_toReal hfin,
      ofReal_integral_eq_lintegral_ofReal
        (((hux_cont.mono (hIcc σ hσ)).abs.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ ↦ abs_nonneg _)]
    refine (lintegral_mono_set (Ioc_subset_Icc_self.trans fun s hs ↦
      (hlife s).2 ⟨hIcc σ hσ hs, hs.1⟩)).trans (setLIntegral_mono' hmeasT fun s hs ↦ ?_)
    rw [← Real.enorm_eq_ofReal_abs]
    exact (hux s ((hlife s).1 hs).1).trans le_self_add
  -- the bound of `log C_ω`
  set K := |cl₀| * τs / 2 + (continuationIntegral S T).toReal with hK
  have hK0 : 0 ≤ K := add_nonneg (by positivity) ENNReal.toReal_nonneg
  have hlog : ∀ σ ∈ lifeSpan T, |Real.log (D.vorticityScale σ)| ≤ K := by
    intro σ hσ
    have hi2 : IntervalIntegrable (fun s ↦ |tangentialVelocityXAtOrigin S s|) volume 0 σ :=
      ((hux_cont.mono (hIcc σ hσ)).abs).intervalIntegrable_of_Icc hσ.1
    rw [h.log_vorticityScale_eq ((hlife σ).1 hσ).1 hσ.1]
    calc |∫ s in (0 : ℝ)..σ, D.vorticityRate s|
        ≤ ∫ s in (0 : ℝ)..σ, |D.vorticityRate s| :=
          intervalIntegral.abs_integral_le_integral_abs hσ.1
      _ ≤ ∫ s in (0 : ℝ)..σ, (|cl₀| / 2 + |tangentialVelocityXAtOrigin S s|) := by
          refine intervalIntegral.integral_mono_on hσ.1
            ((h.continuousOn_vorticityRate.mono (hIcc σ hσ)).abs.intervalIntegrable_of_Icc hσ.1)
            (intervalIntegrable_const.add hi2) fun s hs ↦ ?_
          rw [hcw s ((hlife s).2 ⟨hIcc σ hσ hs, hs.1⟩)]
          exact (abs_add_le _ _).trans_eq (by rw [abs_div, abs_two])
      _ = |cl₀| / 2 * σ + ∫ s in (0 : ℝ)..σ, |tangentialVelocityXAtOrigin S s| := by
          rw [intervalIntegral.integral_add intervalIntegrable_const hi2,
            intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
      _ ≤ K := by linarith [hint σ hσ, mul_le_mul_of_nonneg_left (hlt σ hσ).le (abs_nonneg cl₀)]
  -- bounds of the vorticity scale on the nonnegative times of `J`
  have hCb : ∀ t ∈ J, 0 ≤ t → Real.exp (-K) ≤ C t ∧ C t ≤ Real.exp K := by
    intro t ht ht0
    have hpos : 0 < C t := DynamicRescalingData.physicalVorticityScale_pos _ _
    have hl := hCτ t ht ▸ hlog _ (hτmem t ht ht0)
    rwa [abs_le, Real.le_log_iff_exp_le hpos, Real.log_le_iff_le_exp hpos] at hl
  -- the rescaled time grows at least linearly
  have hτlow : ∀ t ∈ J, 0 ≤ t → t * Real.exp (-K) ≤ τ t := by
    intro t ht ht0
    have hsub : Icc 0 t ⊆ J := h.ordConnected.out h.zero_mem ht
    have hCc : ContinuousOn (fun s ↦ (C s)⁻¹) (Icc 0 t) :=
      ((DynamicRescalingData.continuousOn_physicalVorticityScale h.isOpen h.ordConnected
        h.zero_mem h.continuousOn_physicalVorticityRate).mono hsub).inv₀ fun s _ ↦
          (DynamicRescalingData.physicalVorticityScale_pos _ _).ne'
    have hmono : ∫ _ in (0 : ℝ)..t, Real.exp (-K) ≤ ∫ s in (0 : ℝ)..t, (C s)⁻¹ :=
      intervalIntegral.integral_mono_on ht0 intervalIntegrable_const
        (hCc.intervalIntegrable_of_Icc ht0) fun s hs ↦ by
          rw [Real.exp_neg]
          exact inv_anti₀ (DynamicRescalingData.physicalVorticityScale_pos _ _)
            (hCb s (hsub hs) hs.1).2
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  -- the end time is finite
  have htEnd : tEnd ≤ ENNReal.ofReal (Real.exp K * τs) := by
    by_contra hgt
    have ht₁0 : 0 ≤ Real.exp K * τs := mul_nonneg (Real.exp_pos K).le ENNReal.toReal_nonneg
    have ht₁ := (hJp _ ht₁0).2 (not_le.1 hgt)
    have h1 := hτlow _ ht₁ ht₁0
    rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h1
    linarith [hlt _ (hτmem _ ht₁ ht₁0)]
  have htEnd_ne : tEnd ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top htEnd
  rcases hle.lt_or_eq with hlt' | heq
  · -- the end time is a zero of `ω_x(0)` inside the physical life span
    set te := tEnd.toReal
    have htEnd0 : 0 < tEnd := lt_of_le_of_lt zero_le
      (by simpa using (hJp 0 le_rfl).1 h.zero_mem)
    have hte0 : 0 < te := ENNReal.toReal_pos htEnd0.ne' htEnd_ne
    have hteJ₀ : te ∈ J₀ := (hJ₀p te hte0.le).2 (by rwa [ENNReal.ofReal_toReal htEnd_ne])
    set w := vorticityXAtOrigin (canonicalOf k Q)
    have hT0 : D.physicalTime 0 = 0 :=
      DynamicRescalingData.physicalTime_ofPhysicalRates_zero h.isOpen h.ordConnected h.zero_mem
        h.continuousOn_physicalVorticityRate
    have hL0 : D.spatialScale 0 = 1 := by
      change DynamicRescalingData.physicalSpatialScale _ (D.physicalTime 0) = 1
      rw [hT0, DynamicRescalingData.physicalSpatialScale_zero]
    have hw0 : vorticityXAtOrigin S 0 = w 0 := by
      rw [h.vorticityXAtOrigin_normalizedSolution h.zero_mem_normalizedTimes, h.vorticityScale_zero,
        hL0, hT0, one_mul, one_mul]
    have hw₀ : w 0 ≠ 0 := h.trace_ne_zero 0 h.zero_mem
    -- the spatial scale is `exp(-c_l(0) τ)`
    have hΛ : ∀ t ∈ J, 0 ≤ t → D.spatialScale (τ t) = Real.exp (-(cl₀ * τ t)) := by
      intro t ht ht0
      have hsub : Icc 0 t ⊆ J := h.ordConnected.out h.zero_mem ht
      have ha : ∀ s ∈ uIcc 0 t, physicalSpatialRate (canonicalOf k Q) s = cl₀ * (C s)⁻¹ := by
        intro s hs
        rw [uIcc_of_le ht0] at hs
        have hsJ := hsub hs
        have hcs := hcl _ (hτmem s hsJ hs.1)
        change C (D.physicalTime (τ s)) * physicalSpatialRate (canonicalOf k Q)
          (D.physicalTime (τ s)) = cl₀ at hcs
        rw [h.physicalTime_rescaledClock hsJ] at hcs
        rw [← hcs, mul_comm (C s), mul_assoc,
          mul_inv_cancel₀ (DynamicRescalingData.physicalVorticityScale_pos b s).ne', mul_one]
      change DynamicRescalingData.physicalSpatialScale _ (D.physicalTime (τ t)) = _
      rw [h.physicalTime_rescaledClock ht, DynamicRescalingData.physicalSpatialScale,
        intervalIntegral.integral_congr ha, intervalIntegral.integral_const_mul]
      rfl
    -- the trace stays away from zero
    set m := |w 0| * Real.exp (-K) * Real.exp (-(|cl₀| * τs))
    have hm : 0 < m := by positivity
    have hwlow : ∀ t, 0 ≤ t → t < te → m ≤ |w t| := by
      intro t ht0 htl
      have htJ := (hJp t ht0).2 ((ENNReal.ofReal_lt_iff_lt_toReal ht0 htEnd_ne).2 htl)
      have hσ := hτmem t htJ ht0
      have htr := (h.traces_eq hsym ((hlife _).1 hσ).1 hσ.1).1
      rw [h.vorticityXAtOrigin_normalizedSolution ((hlife _).1 hσ).1, hCτ t htJ, hΛ t htJ ht0,
        h.physicalTime_rescaledClock htJ, hw0] at htr
      have hτb : -(cl₀ * τ t) ≤ |cl₀| * τs := by
        nlinarith [neg_abs_le cl₀, abs_nonneg cl₀, hlt _ hσ, hσ.1]
      have hprod : C t * Real.exp (-(cl₀ * τ t)) ≤ Real.exp K * Real.exp (|cl₀| * τs) :=
        mul_le_mul (hCb t htJ ht0).2 (Real.exp_le_exp.2 hτb) (Real.exp_pos _).le
          (Real.exp_pos _).le
      have hprodpos : 0 < C t * Real.exp (-(cl₀ * τ t)) :=
        mul_pos (DynamicRescalingData.physicalVorticityScale_pos _ _) (Real.exp_pos _)
      calc m = |w 0| / (Real.exp K * Real.exp (|cl₀| * τs)) := by
            simp only [m, Real.exp_neg]
            field_simp
        _ ≤ |w 0| / (C t * Real.exp (-(cl₀ * τ t))) :=
            div_le_div_of_nonneg_left (abs_nonneg _) hprodpos hprod
        _ = |w t| := by
            rw [← htr, abs_mul, abs_of_pos hprodpos, mul_div_cancel_left₀ _ hprodpos.ne']
    have hwc : ContinuousAt w te :=
      (h.regular.continuousOn_vorticityXAtOrigin h.one_le).continuousAt
        (h.isOpen_domain.mem_nhds hteJ₀)
    have hlim : m ≤ |w te| :=
      ge_of_tendsto ((continuous_abs.continuousAt.tendsto.comp hwc.tendsto).mono_left
        nhdsWithin_le_nhds) (by
          filter_upwards [Ioo_mem_nhdsLT hte0] with t ht
          exact hwlow t ht.1.le ht.2)
    rw [hend hlt', abs_zero] at hlim
    linarith
  · -- the end time is the physical life span
    have hTp : Tp ≠ ⊤ := heq ▸ htEnd_ne
    have hset : lifeSpan Tp = J ∩ Ici 0 := by
      ext t
      exact ⟨fun ⟨ht0, htT⟩ ↦ ⟨(hJp t ht0).2 (heq ▸ htT), ht0⟩,
        fun ⟨ht, ht0⟩ ↦ ⟨ht0, heq ▸ (hJp t ht0).1 ht⟩⟩
    apply hfin
    rw [h.continuationIntegral_normalizedSolution]
    refine eq_top_iff.2 ?_
    calc (⊤ : ℝ≥0∞)
      _ = ENNReal.ofReal (Real.exp (-K)) * continuationIntegral (canonicalOf k Q) Tp := by
          rw [hcont hTp, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne']
      _ = ∫⁻ t in J ∩ Ici 0, ENNReal.ofReal (Real.exp (-K)) *
            ((⨆ x ∈ upperHalfPlane,
                ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity (canonicalOf k Q) y t) x‖ₑ) +
              ⨆ x ∈ upperHalfPlane,
                ‖fderiv ℝ (fun y ↦ (canonicalOf k Q).temperature y t) x‖ₑ) := by
          rw [continuationIntegral, hset, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          refine setLIntegral_mono' (h.isOpen.measurableSet.inter measurableSet_Ici)
            fun t ht ↦ ?_
          rw [mul_add]
          exact add_le_add (mul_le_of_le_one_left zero_le
            (ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 hK0))))
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCb t ht.1 ht.2).1) _)

end IsNormalizationSetting

end Boussinesq.HalfPlane

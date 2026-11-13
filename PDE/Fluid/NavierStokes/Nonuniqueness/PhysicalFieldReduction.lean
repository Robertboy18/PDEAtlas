/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCoefficientFields
public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalVelocitySmoothness

/-!
# The coefficient paths through physical coefficient fields

For `t > 0` the linear coefficient path is the transport by the physical cutoff field minus the
transport by the physical profile, and the cutoff forcing path is the projected `L⁴` convection
`-Π(u_cut·∇u_cut + ũ·∇u_cut + u_cut·∇ũ)` of the physical cutoff field `u_cut = -e^{tΔ} w` and the
physical profile `ũ`. So, above the threshold radius and for `s ∈ [0, 1]`, the physical correction
is smooth in time and the physical velocity is smooth on `(0, 1) × ℝ³` as soon as the physical
cutoff field and the physical profile are smooth paths on `(0, 1)` in every `W^{k,∞}` and `W^{k,4}`.

## Main results

* `physicalCoefficient_eq`: the linear coefficient path through the physical fields.
* `physicalCutoffForcing_eq`: the cutoff forcing path through the physical fields.
* `contDiffOn_physicalCoefficient_of_fields`, `contDiffOn_physicalCutoffForcing_of_fields`: both
  paths are smooth on `(0, 1)` when the physical fields are.
* `contDiffOn_physicalCorrection_of_fields`, `contDiffAt_physicalVelocity_of_fields`,
  `physical_time_regularity_of_fields`: the physical correction is `Cʲ` on `(0, 1)` in the vector
  `Hᵐ⁺¹` for all `j` and all `m ≥ 2`, and the physical velocity is smooth on `(0, 1) × ℝ³`.

## How it works

Both identities come from the covariance of the transport and of the `L⁴` convection under the
physical change of variables (`physicalMap_profileConvection`, `physicalMap_lebesgueConvection`) and
from its commutation with the Leray projection (`leraySobolev_physicalMap`). Under the change of
variables at `τ = log t`, the self-similar coefficient and convection become `t` times their
physical counterparts, and the factor `t⁻¹` in the definitions of the physical paths cancels this
`t`. Each physical path is then a fixed bounded linear or bilinear map applied to the physical
fields, so it is smooth wherever the fields are. The last three results follow from
`contDiffOn_physicalCorrection_of_coefficients` and `contDiffAt_physicalVelocity_of_coefficients`,
which take smooth coefficient paths as hypotheses.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R : ℝ}

/-- **The linear coefficient through physical fields.** For `t > 0`, the linear coefficient
path is the projected transport by the physical cutoff field minus the unprojected transport
by the physical profile. -/
theorem physicalCoefficient_eq {m : ℕ} {t : ℝ} (ht : 0 < t) :
    physicalCoefficient D R m t = profileTransport (m + 1) (physicalCutoffSobolev D R (m + 2)
      le_top t) - profileConvection (m + 1) (physicalProfileWkTop D (m + 2) t) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have hexp : Real.exp (Real.log t) = t := Real.exp_log ht
  have hUc : cutoffSobolev D R (m + 1 + 1) le_top (Real.log t) =
      vectorWkpOfContDiff (cutoffFieldFn D R (Real.log t)) (contDiff_cutoffFieldFn D R _)
        (fun j _ ↦ memLp_iteratedFDeriv_cutoffFieldFn D R le_top (Real.log t) j) := rfl
  have hU : D.velocityWkTop (m + 1 + 1) = vectorWkpOfContDiff D.U D.contDiff_U
      (fun j _ ↦ D.memLp_top_iteratedFDeriv j) := rfl
  have hcut := physicalMap_profileConvection (m + 1) (Real.log t)
    (contDiff_cutoffFieldFn D R (Real.log t))
    (fun j _ ↦ memLp_iteratedFDeriv_cutoffFieldFn D R le_top (Real.log t) j) w
  have hprof := physicalMap_profileConvection (m + 1) (Real.log t) D.contDiff_U
    (fun j _ ↦ D.memLp_top_iteratedFDeriv j) w
  rw [hexp, ← hUc] at hcut
  rw [hexp, ← hU] at hprof
  have h₁ : physicalMap (m + 1) (Real.log t) (cutoffCoefficient D R (m + 1) (Real.log t)
      (physicalMap (m + 2) (-Real.log t) w)) =
      t • profileTransport (m + 1) (physicalCutoffSobolev D R (m + 2) le_top t) w := by
    rw [cutoffCoefficient_apply, map_neg, ← leraySobolev_physicalMap, hcut, map_smul,
      ← smul_neg, profileTransport_apply]
    rfl
  have h₂ : physicalMap (m + 1) (Real.log t) ((D.profileCoefficientBounds (m + 1)).transport
      (physicalMap (m + 2) (-Real.log t) w)) =
      t • profileConvection (m + 1) (physicalProfileWkTop D (m + 2) t) w := by
    rw [UnstableProfile.transport_eq_profileConvection, hprof]
    rfl
  change t⁻¹ • physicalMap (m + 1) (Real.log t) ((cutoffCoefficient D R (m + 1) (Real.log t) -
    (D.profileCoefficientBounds (m + 1)).transport) (physicalMap (m + 2) (-Real.log t) w)) = _
  rw [sub_apply, map_sub, h₁, h₂, ← smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
    sub_apply]

/-- **The cutoff forcing through physical fields.** For `t > 0`, the cutoff forcing path is
`-Π(u_cut·∇u_cut + ũ·∇u_cut + u_cut·∇ũ)` with the physical cutoff field `u_cut = -e^{tΔ} w` and
the physical profile `ũ` in `L⁴`-based Sobolev spaces. -/
theorem physicalCutoffForcing_eq {m : ℕ} {t : ℝ} (ht : 0 < t) :
    physicalCutoffForcing D R m t = -leraySobolev 3 (m + 1)
      (lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) +
        lebesgueConvection (m + 1) (physicalProfileWkFour D (m + 1) t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) +
        lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalProfileWkFour D (m + 2) t)) := by
  have hexp : Real.exp (Real.log t) = t := Real.exp_log ht
  set τ := Real.log t with hτ
  have hc := fun j ↦ memLp_iteratedFDeriv_cutoffFieldFn D R le_rfl τ j
  have hu := fun j ↦ D.derivatives_memLp_four j
  have h₁ := physicalMap_lebesgueConvection (m + 1) τ (contDiff_cutoffFieldFn D R τ)
    (contDiff_cutoffFieldFn D R τ) (fun j _ ↦ hc j) (fun j _ ↦ hc j)
  have h₂ := physicalMap_lebesgueConvection (m + 1) τ D.contDiff_U
    (contDiff_cutoffFieldFn D R τ) (fun j _ ↦ hu j) (fun j _ ↦ hc j)
  have h₃ := physicalMap_lebesgueConvection (m + 1) τ (contDiff_cutoffFieldFn D R τ)
    D.contDiff_U (fun j _ ↦ hc j) (fun j _ ↦ hu j)
  rw [hexp] at h₁ h₂ h₃
  have hconv : physicalMap (m + 1) τ (cutoffConvection D R (m + 1) τ) = t •
      (lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) +
        lebesgueConvection (m + 1) (physicalProfileWkFour D (m + 1) t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) +
        lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalProfileWkFour D (m + 2) t)) := by
    have e₁ : physicalMap (m + 1) τ (lebesgueConvection (m + 1)
        (cutoffSobolev D R (m + 1) le_rfl τ) (cutoffSobolev D R (m + 1 + 1) le_rfl τ)) =
        t • lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) := h₁
    have e₂ : physicalMap (m + 1) τ (lebesgueConvection (m + 1) (D.velocityWkFour (m + 1))
        (cutoffSobolev D R (m + 1 + 1) le_rfl τ)) =
        t • lebesgueConvection (m + 1) (physicalProfileWkFour D (m + 1) t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) := h₂
    have e₃ : physicalMap (m + 1) τ (lebesgueConvection (m + 1)
        (cutoffSobolev D R (m + 1) le_rfl τ) (D.velocityWkFour (m + 1 + 1))) =
        t • lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalProfileWkFour D (m + 2) t) := h₃
    rw [smul_add, smul_add]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) ((map_add _ _ _).trans
      (congrArg₂ (· + ·) e₁ e₂)) e₃)
  have hF : cutoffForcing D R (m + 1) τ =
      -leraySobolev 3 (m + 1) (cutoffConvection D R (m + 1) τ) := rfl
  calc physicalCutoffForcing D R m t
      = t⁻¹ • physicalMap (m + 1) τ (cutoffForcing D R (m + 1) τ) := rfl
    _ = t⁻¹ • -leraySobolev 3 (m + 1)
        (physicalMap (m + 1) τ (cutoffConvection D R (m + 1) τ)) := by
      rw [hF, map_neg, leraySobolev_physicalMap]
    _ = _ := by
      have key : ∀ Y : VectorH 3 (m + 1),
          t⁻¹ • -leraySobolev 3 (m + 1) (t • Y) = -leraySobolev 3 (m + 1) Y := fun Y ↦ by
        rw [map_smul, smul_neg, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      rw [hconv]
      exact key _

/-! ### Smoothness of the coefficient paths from smooth physical fields -/

/-- The linear coefficient path is smooth on `(0, 1)` when the physical cutoff field and the
physical profile are smooth paths in every `W^{k,∞}`. -/
theorem contDiffOn_physicalCoefficient_of_fields
    (hcut : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_top) (Ioo 0 1))
    (hprof : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkTop D k) (Ioo 0 1)) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalCoefficient D R m) (Ioo 0 1) := by
  let _ : NormedSpace ℝ (Fin 3 → W^{m + 1 + 1,∞}(ℝ^3)) := Pi.normedSpace
  let _ : NormedSpace ℝ (Fin 3 → W^{m + 1,∞}(ℝ^3)) := Pi.normedSpace
  let _ : NormedSpace ℝ (Fin 3 → Fin 3 → W^{m + 1,∞}(ℝ^3)) := Pi.normedSpace
  have h₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun t ↦ profileTransport (m + 1)
      (physicalCutoffSobolev D R (m + 2) le_top t)) (Ioo 0 1) :=
    (profileTransportCLM (n := 3) (m + 1)).contDiff.comp_contDiffOn (hcut (m + 2))
  have h₂ : ContDiffOn ℝ (⊤ : ℕ∞) (fun t ↦ profileConvection (m + 1)
      (physicalProfileWkTop D (m + 2) t)) (Ioo 0 1) :=
    ((velocityTransportCLM (n := 3) (m + 1)).contDiff.comp_contDiffOn
      ((profileVelocity (n := 3) (m + 1)).contDiff.comp_contDiffOn (hprof (m + 2)))).add
      ((stretchingCLM (n := 3) (m + 1)).contDiff.comp_contDiffOn
        ((profileGradient (n := 3) (m + 1)).contDiff.comp_contDiffOn (hprof (m + 2))))
  exact (h₁.sub h₂).congr fun t ht ↦ physicalCoefficient_eq ht.1

/-- The cutoff forcing path is smooth on `(0, 1)` when the physical cutoff field and the physical
profile are smooth paths in every `W^{k,4}`. -/
theorem contDiffOn_physicalCutoffForcing_of_fields
    (hcut : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_rfl) (Ioo 0 1))
    (hprof : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkFour D k) (Ioo 0 1)) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffForcing D R m) (Ioo 0 1) := by
  let _ : NormedSpace ℝ (Fin 3 → W^{m + 1,4}(ℝ^3)) := Pi.normedSpace
  let _ : NormedSpace ℝ (Fin 3 → W^{m + 1 + 1,4}(ℝ^3)) := Pi.normedSpace
  have hL := (lebesgueConvection (n := 3) (m + 1)).isBoundedBilinearMap.contDiff
    (n := (⊤ : ℕ∞))
  have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun t ↦ -leraySobolev 3 (m + 1)
      (lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) +
        lebesgueConvection (m + 1) (physicalProfileWkFour D (m + 1) t)
          (physicalCutoffSobolev D R (m + 2) le_rfl t) +
        lebesgueConvection (m + 1) (physicalCutoffSobolev D R (m + 1) le_rfl t)
          (physicalProfileWkFour D (m + 2) t))) (Ioo 0 1) :=
    ((leraySobolev 3 (m + 1)).contDiff.comp_contDiffOn
      (((hL.comp_contDiffOn ((hcut (m + 1)).prodMk (hcut (m + 2)))).add
        (hL.comp_contDiffOn ((hprof (m + 1)).prodMk (hcut (m + 2))))).add
        (hL.comp_contDiffOn ((hcut (m + 1)).prodMk (hprof (m + 2)))))).neg
  exact h.congr fun t ht ↦ physicalCutoffForcing_eq ht.1

variable {s : ℝ}

/-- **Time regularity from smooth physical fields.** Above the threshold radius and for
`s ∈ [0, 1]`, if the physical cutoff field `-e^{tΔ} w` and the physical profile
`t^{-1/2} Ũ(x / √t)` are smooth paths on `(0, 1)` in every `W^{k,∞}` and every `W^{k,4}`, then
the physical correction is `Cʲ` on `(0, 1)` in the vector `Hᵐ⁺¹` for every `j` and every `m`
with `3 < 2m`, that is `m ≥ 2`. -/
theorem contDiffOn_physicalCorrection_of_fields (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hcut : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_top) (Ioo 0 1))
    (hcut₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_rfl) (Ioo 0 1))
    (hprof : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkTop D k) (Ioo 0 1))
    (hprof₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkFour D k) (Ioo 0 1)) :
    ∀ (j m : ℕ) (hm : (3 : ℝ) < 2 * m),
      ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1) :=
  contDiffOn_physicalCorrection_of_coefficients hR hs
    (contDiffOn_physicalCutoffForcing_of_fields hcut₄ hprof₄)
    (contDiffOn_physicalCoefficient_of_fields hcut hprof)

/-- **Smoothness of the physical velocity from smooth physical fields.** Under the hypotheses of
`contDiffOn_physicalCorrection_of_fields`, the physical velocity is smooth at every point of
`(0, 1) × ℝ³`. -/
theorem contDiffAt_physicalVelocity_of_fields (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hcut : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_top) (Ioo 0 1))
    (hcut₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_rfl) (Ioo 0 1))
    (hprof : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkTop D k) (Ioo 0 1))
    (hprof₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkFour D k) (Ioo 0 1))
    {z : ℝ^(3 + 1)} (hz : z ∈ IncompressibleFlow.finiteTimeDomain 3 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalVelocity D R s) z :=
  contDiffAt_physicalVelocity_of_coefficients hR hs
    (contDiffOn_physicalCutoffForcing_of_fields hcut₄ hprof₄)
    (contDiffOn_physicalCoefficient_of_fields hcut hprof) hz

/-- **Time regularity in physical variables and joint smoothness, from smooth physical fields.**
Above the threshold radius and for `s ∈ [0, 1]`, if the physical cutoff field `-e^{tΔ} w` and the
physical profile `t^{-1/2} Ũ(x / √t)` are smooth paths on `(0, 1)` in every `W^{k,∞}` and every
`W^{k,4}`, then the physical correction `t^{-1/2} U_cor(log t, x / √t)` is `Cʲ` on `(0, 1)` with
values in the vector `Hᵐ⁺¹` for every `j` and every `m` with `3 < 2m`, that is `m ≥ 2`, and the
physical velocity is smooth at every point of `(0, 1) × ℝ³`. -/
theorem physical_time_regularity_of_fields (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hcut : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_top) (Ioo 0 1))
    (hcut₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffSobolev D R k le_rfl) (Ioo 0 1))
    (hprof : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkTop D k) (Ioo 0 1))
    (hprof₄ : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalProfileWkFour D k) (Ioo 0 1)) :
    (∀ (j m : ℕ) (hm : (3 : ℝ) < 2 * m),
        ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1)) ∧
      ∀ z ∈ IncompressibleFlow.finiteTimeDomain 3 1,
        ContDiffAt ℝ (⊤ : ℕ∞) (physicalVelocity D R s) z :=
  ⟨contDiffOn_physicalCorrection_of_fields hR hs hcut hcut₄ hprof hprof₄,
    fun _ hz ↦ contDiffAt_physicalVelocity_of_fields hR hs hcut hcut₄ hprof hprof₄ hz⟩

end NavierStokes.Nonuniqueness

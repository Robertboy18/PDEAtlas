/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalVelocity
import PDE.Analysis.Calculus.Homogeneous
import PDE.Analysis.MeasureTheory.Lp.Composition.DilationOrbit
import PDE.Analysis.MeasureTheory.Lp.IntermediateExponent
import PDE.Parabolic.Heat.WholeSpace.GaussianFlowHomogeneous
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.LebesgueEmbedding

/-!
# Space-time integrability of the physical velocity

Let `u = ũ + u_cut + u_cor` be the physical velocity of an unstable profile at cutoff radius `R`
(`physicalVelocity`). For `2 ≤ q`, `1 ≤ r` and `3/q + 2/r > 1`, every slice `u(t)`, `0 < t ≤ 1`,
lies in `Lᵠ`, and `t ↦ ‖u(t)‖_{Lᵠ}` lies in `Lʳ((0, 1])` (`physical_memLp_LsLq`); this is the
integrability in Theorem 1 of Hou, Wang and Yang. It rests on the bound

`‖u(t)‖_{Lᵠ} ≤ A t^{3/(2q) - 1/2} + B t^{3/(2q) - 3/(2p)}`,

for `0 < t ≤ 1`, `1 ≤ p ≤ q`, `p < 3` and `2 ≤ q` (`exists_toReal_eLpNorm_velocitySlice_le`), the
bound that Hou, Wang and Yang derive from (2.21), with `p` in the role of their `3 - ε`.

## Main results

* `UnstableProfile.memLp_sub_gaussianFlow_farField`, `profile_add_cutoffField`.
* `exists_eLpNorm_correctionField_le`, `eLpNorm_gaussianFlow_localizedDatum_le`.
* `similarityVelocity`, `memLp_similarityVelocity`, `tendsto_eLpNorm_similarityVelocity_sub`,
  `continuous_toReal_eLpNorm_similarityVelocity`, `exists_toReal_eLpNorm_similarityVelocity_le`.
* `eLpNorm_velocitySlice_physicalVelocity`, `exists_toReal_eLpNorm_velocitySlice_le`.
* `physical_memLp_LsLq`.

## How it works

At a positive time `t`, with `W(τ) = Ũ + U_cut(τ) + U_cor(τ)` the velocity in similarity variables
(`similarityVelocity`), we have `‖u(t)‖_{Lᵠ} = t^{3/(2q) - 1/2} ‖W(log t)‖_{Lᵠ}`
(`eLpNorm_velocitySlice_physicalVelocity`). The far field `u_in = u_loc + w` is homogeneous of
degree `-1`, so `(u_in)_τ = u_in` for the rescaling `f_τ(x) = e^{τ/2} f(e^{τ/2} x)`, and

`Ũ + U_cut(τ) = (Ũ - G₁ * u_in) + G₁ * (u_loc)_τ`

(`profile_add_cutoffField`). The near field `Ũ - G₁ * u_in` lies in `L² ∩ L∞`
(`UnstableProfile.memLp_sub_gaussianFlow_farField`): the profile minus its far field cut off near
the origin is square integrable, and `G₁ * u_in` differs from the same cut-off far field by a field
in `L² ∩ L∞`. Since `u_loc` lies in `Lᵖ` for `p < 3`, Young's inequality gives
`‖G₁ * (u_loc)_τ‖_{Lᵠ} ≤ C e^{(τ/2)(1 - 3/p)} ‖u_loc‖_{Lᵖ}` for `p ≤ q`
(`eLpNorm_gaussianFlow_localizedDatum_le`), and the correction is bounded in `H³ ⊂ L² ∩ L∞`
(`exists_eLpNorm_correctionField_le`); together they give the bound. For `3/q + 2/r > 1` we choose
`p` with `3/p < 3/q + 2/r`, so that both powers lie in `Lʳ((0, 1])` (`memLp_rpow_Ioc`). Each part of
`W(τ)` depends continuously on `τ` in `Lᵠ` for `2 ≤ q ≤ ∞`, so `t ↦ ‖u(t)‖_{Lᵠ}` is continuous at
positive times (`continuousOn_toReal_eLpNorm_velocitySlice_physicalVelocity`), which gives its
measurability.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Theorem 1, p. 1, and Section 2.2,
  (2.21) and the bound after it, p. 15.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis.Evolution PDE.Common
open scoped ENNReal Topology

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The profile minus the time-one heat flow of its far field, `Ũ - G₁ * u_in`, lies in
`L² ∩ L∞`. -/
theorem memLp_sub_gaussianFlow_farField :
    MemLp (D.U - gaussianFlow 1 fun x ↦ ‖x‖⁻¹ • D.A x) 2 volume ∧
      MemLp (D.U - gaussianFlow 1 fun x ↦ ‖x‖⁻¹ • D.A x) ∞ volume := by
  set u : ℝ^3 → ℝ^3 := fun x ↦ ‖x‖⁻¹ • D.A x
  have hA1 : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 D.A x := fun x hx ↦
    (D.A_contDiffAt x hx).of_le (by exact_mod_cast le_top)
  have hχc : HasCompactSupport (unitCutoff (n := 3)) :=
    (PDE.Analysis.standardBump 3).hasCompactSupport
  obtain ⟨h2, htop⟩ := memLp_gaussianFlow_one_sub_cutoff (n := 3) (E := ℝ^3) (by norm_num)
    (by norm_num) D.A_homogeneous hA1 contDiff_unitCutoff.continuous hχc one_pos
    (fun x hx ↦ unitCutoff_of_norm_le_one hx.le)
  have hsplit : D.U - gaussianFlow 1 u =
      (fun ξ ↦ D.U ξ - (1 - unitCutoff ξ) • u ξ) -
        fun x ↦ gaussianFlow 1 u x - (1 - unitCutoff x) • u x := by
    funext x
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right]
  refine ⟨hsplit ▸ D.nearField_memLp.sub h2, ?_⟩
  obtain ⟨M, hM, hu⟩ := PDE.exists_norm_le_mul_inv_norm_of_homogeneous
    (fun x _ hc ↦ D.farField_smul x hc) (fun x hx ↦ (D.contDiffAt_farField hx).continuousAt)
  have hum : AEStronglyMeasurable u volume :=
    PDE.aestronglyMeasurable_of_continuousAt_of_ne (x₀ := 0) fun x hx ↦
      (D.contDiffAt_farField hx).continuousAt
  have hfar : MemLp (fun x ↦ (1 - unitCutoff x) • u x) ∞ volume := by
    refine memLp_top_of_bound ((continuous_const.sub
      contDiff_unitCutoff.continuous).aestronglyMeasurable.smul hum) M
      (ae_of_all _ fun x ↦ ?_)
    rcases le_or_gt ‖x‖ 1 with hx | hx
    · rw [unitCutoff_of_norm_le_one hx, sub_self, zero_smul, norm_zero]
      exact hM
    · have hχ : ‖1 - unitCutoff x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [unitCutoff_nonneg x, unitCutoff_le_one x]
      rw [norm_smul]
      calc
        ‖1 - unitCutoff x‖ * ‖u x‖ ≤ 1 * (M * ‖x‖⁻¹) :=
          mul_le_mul hχ (hu x) (norm_nonneg _) zero_le_one
        _ ≤ M := by
          rw [one_mul]
          exact mul_le_of_le_one_right hM (inv_le_one_of_one_le₀ hx.le)
  obtain ⟨C, hC⟩ := D.bounded_derivatives 0
  have hU : MemLp D.U ∞ volume :=
    memLp_top_of_bound D.contDiff_U.continuous.aestronglyMeasurable C
      (ae_of_all _ fun ξ ↦ by simpa only [norm_iteratedFDeriv_zero] using hC ξ)
  have hG : gaussianFlow 1 u = (fun x ↦ gaussianFlow 1 u x - (1 - unitCutoff x) • u x) +
      fun x ↦ (1 - unitCutoff x) • u x := by
    funext x
    simp only [Pi.add_apply, sub_add_cancel]
  rw [hG]
  exact hU.sub (htop.add hfar)

/-- The localized far field `u_loc` lies in `Lᵖ` for `p < 3`. -/
theorem memLp_localizedDatum {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} (hp : p < 3) :
    MemLp (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) p volume :=
  NavierStokes.Nonuniqueness.memLp_localizedDatum hR (fun x _ hc ↦ D.farField_smul x hc)
    (fun _ hx ↦ D.contDiffAt_farField hx) hp

end UnstableProfile

variable (D : UnstableProfile) (R s : ℝ)

/-- The profile plus the cutoff field in similarity variables:
`Ũ + U_cut(τ) = (Ũ - G₁ * u_in) + G₁ * (u_loc)_τ`, with
`(u_loc)_τ(x) = e^{τ/2} u_loc(e^{τ/2} x)` the rescaled localized datum. -/
theorem profile_add_cutoffField (τ : ℝ) :
    D.U + cutoffField D R τ = (D.U - gaussianFlow 1 fun x ↦ ‖x‖⁻¹ • D.A x) +
      gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
        localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x) := by
  have hA1 : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 D.A x := fun x hx ↦
    (D.A_contDiffAt x hx).of_le (by exact_mod_cast le_top)
  have hloc : (fun x ↦ Real.exp (τ / 2) •
        localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x)) =
      (fun x ↦ ‖x‖⁻¹ • D.A x) - fun x ↦ Real.exp (τ / 2) •
        localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x) := by
    funext x
    have h1 := localizedDatum_add_localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R
      (Real.exp (τ / 2) • x)
    rw [D.farField_smul x (Real.exp_pos _)] at h1
    rw [Pi.sub_apply, eq_sub_iff_add_eq, ← smul_add, h1,
      smul_inv_smul₀ (Real.exp_pos _).ne']
  rw [hloc, gaussianFlow_one_sub
    (integrable_polynomialWeight_smul_norm_inv_smul (n := 3) (by norm_num) D.A_homogeneous hA1)
    (PDE.integrable_polynomialWeight_smul_of_memLp (by norm_num)
      (memLp_dilate (D.memLp_four_localizationRemainder R) τ)), cutoffField_eq_conv]
  abel

/-- The correction field lies in every `Lᵠ`, `2 ≤ q ≤ ∞`, with
`‖U_cor(τ)‖_{Lᵠ} ≤ K ‖U_cor(τ)‖_{H³}` and
`‖U_cor(τ) - U_cor(τ₀)‖_{Lᵠ} ≤ K ‖U_cor(τ) - U_cor(τ₀)‖_{H³}` for one constant `K`. -/
theorem exists_eLpNorm_correctionField_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R s : ℝ) {q : ℝ≥0∞}, 2 ≤ q → ∀ τ τ₀ : ℝ,
      MemLp (correctionField D R s τ) q volume ∧
        eLpNorm (correctionField D R s τ) q volume ≤
          ENNReal.ofReal (K * ‖ancientLift D.dichotomy.η (ancientCorrection D R s) τ‖) ∧
        eLpNorm (correctionField D R s τ - correctionField D R s τ₀) q volume ≤
          ENNReal.ofReal (K * ‖ancientLift D.dichotomy.η (ancientCorrection D R s) τ -
            ancientLift D.dichotomy.η (ancientCorrection D R s) τ₀‖) := by
  obtain ⟨K, hK, hF⟩ :=
    exists_eLpNorm_toLp_baseRepresentative_le_of_dimension_lt (n := 3) (k := 3) (by norm_num)
  refine ⟨K, hK, fun R s q hq τ τ₀ ↦ ?_⟩
  set v := ancientLift D.dichotomy.η (ancientCorrection D R s)
  have hae := correctionField_ae_eq D R s τ
  have hae₀ := correctionField_ae_eq D R s τ₀
  have hj : ∀ᵐ x ∂volume, ∀ j : Fin 3, baseRepresentative ((v τ - v τ₀) j) x =
      baseRepresentative (v τ j) x - baseRepresentative (v τ₀ j) x := by
    refine ae_all_iff.mpr fun j ↦ ?_
    have h := baseRepresentative_sub_ae (v τ j) (v τ₀ j)
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  have hsub : correctionField D R s τ - correctionField D R s τ₀ =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 fun j ↦ baseRepresentative ((v τ - v τ₀) j) x := by
    filter_upwards [hae, hae₀, hj] with x h1 h2 h3
    rw [Pi.sub_apply, h1, h2]
    ext j
    change _ = baseRepresentative ((v τ - v τ₀) j) x
    rw [h3 j]
    rfl
  refine ⟨(hF (v τ) hq).1.ae_eq hae.symm, ?_, ?_⟩
  · rw [eLpNorm_congr_ae hae]
    exact (hF (v τ) hq).2
  · rw [eLpNorm_congr_ae hsub]
    exact (hF (v τ - v τ₀) hq).2

variable {R} in
/-- The time-one heat flow `G₁ * (u_loc)_τ` of the rescaled localized datum lies in every `Lᵠ`,
`2 ≤ q ≤ ∞`. -/
theorem memLp_gaussianFlow_localizedDatum (hR : 0 < R) {q : ℝ≥0∞} (hq : 2 ≤ q) (τ : ℝ) :
    MemLp (gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
      localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x)) q volume :=
  memLp_gaussianFlow one_pos one_le_two hq
    (memLp_dilate (D.memLp_localizedDatum hR (by norm_num)) τ)

variable {R} in
/-- The time-one heat flow `G₁ * (u_loc)_τ` of the rescaled localized datum depends
continuously on `τ` in every `Lᵠ`, `2 ≤ q ≤ ∞`. -/
theorem tendsto_eLpNorm_gaussianFlow_localizedDatum_sub (hR : 0 < R) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (τ₀ : ℝ) :
    Tendsto (fun τ ↦ eLpNorm ((gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
        localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x)) -
      gaussianFlow 1 fun x ↦ Real.exp (τ₀ / 2) •
        localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ₀ / 2) • x)) q volume)
      (𝓝 τ₀) (𝓝 0) := by
  have hloc := D.memLp_localizedDatum hR (p := 2) (by norm_num)
  set H : ℝ → ℝ^3 → ℝ^3 := fun τ ↦ gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
    localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x)
  have hcd (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (H σ) := contDiff_gaussianFlow_one_dilate hloc one_le_two σ
  have h := tendsto_eLpNorm_iteratedFDeriv_gaussianFlow_one_dilate_sub hloc one_le_two
    (by simp) hq 0 τ₀
  refine h.congr fun τ ↦ ?_
  have hd0 (σ : ℝ) : Continuous fun x ↦ iteratedFDeriv ℝ 0 (H σ) x :=
    (hcd σ).continuous_iteratedFDeriv (m := 0) (by simp)
  have hpt (x : ℝ^3) : (iteratedFDeriv ℝ 0 (H τ) - iteratedFDeriv ℝ 0 (H τ₀)) x =
      iteratedFDeriv ℝ 0 (H τ - H τ₀) x := by
    ext m
    simp only [Pi.sub_apply, sub_apply, iteratedFDeriv_zero_apply]
  refine eLpNorm_congr_norm_ae ((hd0 τ).sub (hd0 τ₀)).aestronglyMeasurable
    ((hcd τ).continuous.sub (hcd τ₀).continuous).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [hpt x, norm_iteratedFDeriv_zero]

variable {R} in
/-- The smoothing bound `‖G₁ * (u_loc)_τ‖_{Lᵠ} ≤ C e^{(τ/2)(1 - 3/p)} ‖u_loc‖_{Lᵖ}`,
`1 ≤ p < 3`, `p ≤ q`, with `C` the `L^{q'}` norm of the heat kernel, `1/p + 1/q' = 1 + 1/q`. -/
theorem eLpNorm_gaussianFlow_localizedDatum_le (hR : 0 < R) {p q : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp3 : p < 3) (hpq : p ≤ q) (τ : ℝ) :
    eLpNorm (gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
        localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (τ / 2) • x)) q volume ≤
      eLpNorm (iteratedFDeriv ℝ 0 (HeatEquation.heatKernelSchwartz 3))
          (ENNReal.youngExponent p q) volume *
        (ENNReal.ofReal (Real.exp (τ / 2 * (1 - 3 * p⁻¹.toReal))) *
          eLpNorm (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) p volume) := by
  have hloc := D.memLp_localizedDatum hR hp3
  have h := eLpNorm_iteratedFDeriv_gaussianFlow_one_le hp1 (ENNReal.one_le_youngExponent hpq)
    (ENNReal.inv_add_inv_youngExponent q hp1) (memLp_dilate hloc τ) 0
  rw [eLpNorm_dilate hloc.aestronglyMeasurable τ, finrank_euclideanSpace_fin] at h
  have hcd := contDiff_gaussianFlow_one_dilate hloc hp1 τ
  rw [eLpNorm_congr_norm_ae (hcd.continuous_iteratedFDeriv (m := 0) (by simp)).aestronglyMeasurable
    hcd.continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ norm_iteratedFDeriv_zero)] at h
  exact_mod_cast h

/-! ### The velocity in similarity variables -/

/-- The velocity `W(τ) = Ũ + U_cut(τ) + U_cor(τ)` in similarity variables: at time `t = e^τ`
the physical velocity is `t^{-1/2} W(τ)(x / √t)`. -/
def similarityVelocity (τ : ℝ) : ℝ^3 → ℝ^3 :=
  D.U + cutoffField D R τ + correctionField D R s τ

variable {R} in
/-- The velocity in similarity variables lies in every `Lᵠ`, `2 ≤ q ≤ ∞`. -/
theorem memLp_similarityVelocity (hR : 0 < R) {q : ℝ≥0∞} (hq : 2 ≤ q) (τ : ℝ) :
    MemLp (similarityVelocity D R s τ) q volume := by
  obtain ⟨h2, htop⟩ := D.memLp_sub_gaussianFlow_farField
  obtain ⟨K, -, hK⟩ := exists_eLpNorm_correctionField_le D
  rw [similarityVelocity, profile_add_cutoffField]
  exact ((h2.of_le_exponent_of_memLp_top htop two_ne_zero hq).add
    (memLp_gaussianFlow_localizedDatum D hR hq τ)).add (hK R s hq τ τ).1

variable {R} in
/-- The velocity in similarity variables depends continuously on `τ` in every `Lᵠ`,
`2 ≤ q ≤ ∞`. -/
theorem tendsto_eLpNorm_similarityVelocity_sub (hR : 0 < R) {q : ℝ≥0∞} (hq : 2 ≤ q) (τ₀ : ℝ) :
    Tendsto (fun τ ↦ eLpNorm (similarityVelocity D R s τ - similarityVelocity D R s τ₀) q
      volume) (𝓝 τ₀) (𝓝 0) := by
  obtain ⟨K, -, hK⟩ := exists_eLpNorm_correctionField_le D
  set v := ancientLift D.dichotomy.η (ancientCorrection D R s)
  have hv : Tendsto (fun τ ↦ ENNReal.ofReal (K * ‖v τ - v τ₀‖)) (𝓝 τ₀) (𝓝 0) := by
    have h := tendsto_iff_norm_sub_tendsto_zero.mp (v.continuous.tendsto τ₀)
    simpa using ENNReal.tendsto_ofReal (h.const_mul K)
  have hC : Tendsto (fun τ ↦ eLpNorm (correctionField D R s τ - correctionField D R s τ₀) q
      volume) (𝓝 τ₀) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv (fun _ ↦ zero_le)
      fun τ ↦ (hK R s hq τ τ₀).2.2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_eLpNorm_gaussianFlow_localizedDatum_sub D hR hq τ₀).add hC)
    (fun _ ↦ zero_le) fun τ ↦ ?_
  rw [similarityVelocity, similarityVelocity, profile_add_cutoffField, profile_add_cutoffField]
  refine le_of_eq_of_le (congrArg (eLpNorm · q volume) ?_) (eLpNorm_add_le (one_le_two.trans hq))
  abel

variable {R} in
/-- The `Lᵠ` norm of the velocity in similarity variables depends continuously on `τ`,
`2 ≤ q ≤ ∞`. -/
theorem continuous_toReal_eLpNorm_similarityVelocity (hR : 0 < R) {q : ℝ≥0∞} (hq : 2 ≤ q) :
    Continuous fun τ ↦ (eLpNorm (similarityVelocity D R s τ) q volume).toReal := by
  have : Fact (1 ≤ q) := ⟨one_le_two.trans hq⟩
  have hW (τ : ℝ) := memLp_similarityVelocity D s hR hq τ
  have hnorm : (fun τ ↦ (eLpNorm (similarityVelocity D R s τ) q volume).toReal) =
      fun τ ↦ ‖(hW τ).toLp _‖ := funext fun τ ↦ (Lp.norm_toLp _ _).symm
  rw [hnorm]
  refine continuous_norm.comp (continuous_iff_continuousAt.mpr fun τ₀ ↦ ?_)
  rw [ContinuousAt, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have heq (τ : ℝ) : eLpNorm (⇑((hW τ).toLp _) - ⇑((hW τ₀).toLp _)) q volume =
      eLpNorm (similarityVelocity D R s τ - similarityVelocity D R s τ₀) q volume :=
    eLpNorm_congr_ae ((hW τ).coeFn_toLp.sub (hW τ₀).coeFn_toLp)
  simp_rw [heq]
  exact tendsto_eLpNorm_similarityVelocity_sub D s hR hq τ₀

variable {R} in
/-- On `τ ≤ 0`, for `1 ≤ p < 3`, `p ≤ q` and `2 ≤ q`, the `Lᵠ` norm of the velocity in similarity
variables is at most `A + B e^{(τ/2)(1 - 3/p)}`: the near field `Ũ - G₁ * u_in` and the
correction are bounded, and `G₁ * (u_loc)_τ` obeys the smoothing bound. -/
theorem exists_toReal_eLpNorm_similarityVelocity_le (hR : 0 < R) {p q : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp3 : p < 3) (hpq : p ≤ q) (hq : 2 ≤ q) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ τ ≤ 0,
      (eLpNorm (similarityVelocity D R s τ) q volume).toReal ≤
        A + B * Real.exp (τ / 2 * (1 - 3 * p⁻¹.toReal)) := by
  have hq1 : 1 ≤ q := one_le_two.trans hq
  obtain ⟨h2, htop⟩ := D.memLp_sub_gaussianFlow_farField
  have hV := h2.of_le_exponent_of_memLp_top htop two_ne_zero hq
  obtain ⟨K, hK0, hK⟩ := exists_eLpNorm_correctionField_le D
  have hG : eLpNorm (iteratedFDeriv ℝ 0 (HeatEquation.heatKernelSchwartz 3))
      (ENNReal.youngExponent p q) volume ≠ ∞ :=
    (SchwartzMap.memLp_iteratedFDeriv _ 0 _).eLpNorm_ne_top
  have hloc := D.memLp_localizedDatum hR hp3
  set G := eLpNorm (iteratedFDeriv ℝ 0 (HeatEquation.heatKernelSchwartz 3))
    (ENNReal.youngExponent p q) volume
  set N := eLpNorm (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) p volume
  set a := (eLpNorm (D.U - gaussianFlow 1 fun x ↦ ‖x‖⁻¹ • D.A x) q volume).toReal
  set c := K * ‖ancientCorrection D R s‖
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hc : 0 ≤ c := mul_nonneg hK0 (norm_nonneg _)
  refine ⟨a + c, G.toReal * N.toReal, add_nonneg ha hc,
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, fun τ hτ ↦ ?_⟩
  set e := Real.exp (τ / 2 * (1 - 3 * p⁻¹.toReal))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hv : ‖ancientLift D.dichotomy.η (ancientCorrection D R s) τ‖ ≤
      ‖ancientCorrection D R s‖ := by
    refine (norm_ancientLift_le _ _ τ).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos D.dichotomy.η_pos.le hτ)
  have hVa : eLpNorm (D.U - gaussianFlow 1 fun x ↦ ‖x‖⁻¹ • D.A x) q volume =
      ENNReal.ofReal a := (ENNReal.ofReal_toReal hV.eLpNorm_ne_top).symm
  have hHb : G * (ENNReal.ofReal e * N) = ENNReal.ofReal (G.toReal * N.toReal * e) := by
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hG,
      ENNReal.ofReal_toReal hloc.eLpNorm_ne_top]
    ring
  have hCc : eLpNorm (correctionField D R s τ) q volume ≤ ENNReal.ofReal c :=
    (hK R s hq τ τ).2.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hv hK0))
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [similarityVelocity, profile_add_cutoffField]
  refine (eLpNorm_add_le hq1).trans ((add_le_add (eLpNorm_add_le hq1) le_rfl).trans ?_)
  calc
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal (G.toReal * N.toReal * e) + ENNReal.ofReal c := by
      rw [hVa]
      exact add_le_add (add_le_add le_rfl
        ((eLpNorm_gaussianFlow_localizedDatum_le D hR hp1 hp3 hpq τ).trans hHb.le)) hCc
    _ = ENNReal.ofReal (a + c + G.toReal * N.toReal * e) := by
      rw [← ENNReal.ofReal_add ha (by positivity), ← ENNReal.ofReal_add (by positivity) hc]
      congr 1
      ring

/-! ### Physical variables -/

/-- At a positive time `t` the velocity slice is the rescaling `e^{σ/2} W(log t)(e^{σ/2} x)`,
`σ = -log t`, of the velocity `W` in similarity variables. -/
theorem velocitySlice_physicalVelocity_eq {t : ℝ} (ht : 0 < t) :
    IncompressibleFlow.velocitySlice (physicalVelocity D R s) t = fun x ↦
      Real.exp (-Real.log t / 2) •
        similarityVelocity D R s (Real.log t) (Real.exp (-Real.log t / 2) • x) := by
  have he : Real.exp (-Real.log t / 2) = (Real.sqrt t)⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  funext x
  rw [IncompressibleFlow.velocitySlice, physicalVelocity_timeSpaceCons D R s ht, he]
  rfl

/-- An exponent `p ∈ [1, 3)`, `p ≤ q`, with `3/p < 3/q + 2/r`, for `2 ≤ q`, `1 ≤ r` and
`3/q + 2/r > 1`. -/
private theorem exists_lebesgueExponent {q r : ℝ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hqr : 1 < 3 / q + 2 / r) : ∃ p : ℝ, 1 ≤ p ∧ p ≤ q ∧ p < 3 ∧ 3 / p < 3 / q + 2 / r := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have h3q : 3 / q ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
  have h2r : 2 / r ≤ 2 := by
    rw [div_le_iff₀ hr0]
    linarith
  have h2r0 : 0 < 2 / r := by positivity
  set θ := 1 + 3 / q + 2 / r with hθ
  have hθ0 : 0 < θ := by linarith
  refine ⟨min q (6 / θ), le_min (by linarith) ?_, min_le_left _ _, ?_, ?_⟩
  · rw [le_div_iff₀ hθ0]
    linarith
  · refine (min_le_right _ _).trans_lt ?_
    rw [div_lt_iff₀ hθ0]
    linarith
  · rcases min_choice q (6 / θ) with h | h <;> rw [h]
    · linarith
    · rw [div_div_eq_mul_div, div_lt_iff₀ (by norm_num : (0 : ℝ) < 6)]
      linarith

/-- A power `t ^ a` lies in `Lʳ((0, 1])` when `a r > -1`. -/
theorem memLp_rpow_Ioc {a r : ℝ} (hr : 0 < r) (har : -1 < a * r) :
    MemLp (fun t : ℝ ↦ t ^ a) (ENNReal.ofReal r) (volume.restrict (Ioc 0 1)) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ t ^ a) (volume.restrict (Ioc 0 1)) :=
    (measurable_id.pow_const a).aestronglyMeasurable
  refine (integrable_norm_rpow_iff hmeas (by simpa using hr) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal hr.le]
  refine ((intervalIntegral.intervalIntegrable_rpow' har).1.congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioc)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _), ← Real.rpow_mul ht.1.le]

variable {R} in
/-- At a positive time `t` the `Lᵠ` norm of the velocity slice is
`t^{3/(2q) - 1/2} ‖W(log t)‖_{Lᵠ}`, written as `e^{-(log t)/2 (1 - 3/q)}` times the norm of the
velocity `W` in similarity variables. -/
theorem eLpNorm_velocitySlice_physicalVelocity (hR : 0 < R) {t : ℝ} (ht : 0 < t) (q : ℝ≥0∞) :
    eLpNorm (IncompressibleFlow.velocitySlice (physicalVelocity D R s) t) q volume =
      ENNReal.ofReal (Real.exp (-Real.log t / 2 * (1 - 3 * q⁻¹.toReal))) *
        eLpNorm (similarityVelocity D R s (Real.log t)) q volume := by
  rw [velocitySlice_physicalVelocity_eq D R s ht,
    eLpNorm_dilate (memLp_similarityVelocity D s hR le_rfl _).aestronglyMeasurable,
    finrank_euclideanSpace_fin, Nat.cast_ofNat]

variable {R} in
/-- At positive times the velocity slices lie in every `Lᵠ`, `2 ≤ q ≤ ∞`. -/
theorem memLp_velocitySlice_physicalVelocity (hR : 0 < R) {q : ℝ≥0∞} (hq : 2 ≤ q) {t : ℝ}
    (ht : 0 < t) :
    MemLp (IncompressibleFlow.velocitySlice (physicalVelocity D R s) t) q volume := by
  rw [velocitySlice_physicalVelocity_eq D R s ht]
  exact memLp_dilate (memLp_similarityVelocity D s hR hq _) _

variable {R} in
/-- The `Lᵠ` norm of the velocity slices, `2 ≤ q ≤ ∞`, is continuous at positive times. -/
theorem continuousOn_toReal_eLpNorm_velocitySlice_physicalVelocity (hR : 0 < R) {q : ℝ≥0∞}
    (hq : 2 ≤ q) :
    ContinuousOn (fun t ↦ (eLpNorm (IncompressibleFlow.velocitySlice (physicalVelocity D R s) t)
      q volume).toReal) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi (0 : ℝ)) :=
    Real.continuousOn_log.mono fun t ht ↦ (mem_Ioi.mp ht).ne'
  refine ContinuousOn.congr ?_ fun t ht ↦ by
    rw [eLpNorm_velocitySlice_physicalVelocity D s hR (mem_Ioi.mp ht), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact (Real.continuous_exp.comp_continuousOn
    ((hlog.neg.div_const 2).mul continuousOn_const)).mul
    ((continuous_toReal_eLpNorm_similarityVelocity D s hR hq).comp_continuousOn hlog)

variable {R} in
/-- The bound `‖u(t)‖_{Lᵠ} ≤ A t^{3/(2q) - 1/2} + B t^{3/(2q) - 3/(2p)}` on `0 < t ≤ 1`, for
`1 ≤ p < 3`, `p ≤ q` and `2 ≤ q` (Hou, Wang and Yang, Section 2.2, after (2.21)). -/
theorem exists_toReal_eLpNorm_velocitySlice_le (hR : 0 < R) {p q : ℝ} (hp1 : 1 ≤ p)
    (hp3 : p < 3) (hpq : p ≤ q) (hq : 2 ≤ q) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
      (eLpNorm (IncompressibleFlow.velocitySlice (physicalVelocity D R s) t) (ENNReal.ofReal q)
        volume).toReal ≤ A * t ^ ((3 / q - 1) / 2) + B * t ^ ((3 / q - 3 / p) / 2) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hQ : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal hq
  have hP3 : ENNReal.ofReal p < 3 := by
    rw [← ENNReal.ofReal_ofNat 3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hp3
  have hQinv : (ENNReal.ofReal q)⁻¹.toReal = q⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hq0.le]
  have hPinv : (ENNReal.ofReal p)⁻¹.toReal = p⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le]
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_toReal_eLpNorm_similarityVelocity_le D s hR
    (ENNReal.one_le_ofReal.mpr hp1) hP3 (ENNReal.ofReal_le_ofReal hpq) hQ
  refine ⟨A, B, hA, hB, fun t ht ↦ ?_⟩
  rw [eLpNorm_velocitySlice_physicalVelocity D s hR ht.1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, hQinv]
  have hL : -Real.log t / 2 * (1 - 3 * q⁻¹) = Real.log t * ((3 / q - 1) / 2) := by
    ring
  have hLL : -Real.log t / 2 * (1 - 3 * q⁻¹) + Real.log t / 2 * (1 - 3 * p⁻¹) =
      Real.log t * ((3 / q - 3 / p) / 2) := by
    ring
  calc
    _ ≤ Real.exp (-Real.log t / 2 * (1 - 3 * q⁻¹)) *
        (A + B * Real.exp (Real.log t / 2 * (1 - 3 * (ENNReal.ofReal p)⁻¹.toReal))) :=
      mul_le_mul_of_nonneg_left (hbound _ (Real.log_nonpos ht.1.le ht.2)) (Real.exp_pos _).le
    _ = A * t ^ ((3 / q - 1) / 2) + B * t ^ ((3 / q - 3 / p) / 2) := by
      rw [hPinv, Real.rpow_def_of_pos ht.1, Real.rpow_def_of_pos ht.1, ← hL, ← hLL,
        Real.exp_add]
      ring

variable {R} in
/-- **`LʳLᵠ` integrability of the physical velocity** (Hou, Wang and Yang, Theorem 1). For
`2 ≤ q`, `1 ≤ r` and `3/q + 2/r > 1`, every slice `u(t)`, `0 < t ≤ 1`, lies in `Lᵠ(ℝ³)`, and
`t ↦ ‖u(t)‖_{Lᵠ}` lies in `Lʳ((0, 1])`. With `1 ≤ p ≤ q`, `p < 3` and `3/p < 3/q + 2/r`,
`‖u(t)‖_{Lᵠ} ≤ A t^{3/(2q) - 1/2} + B t^{3/(2q) - 3/(2p)}`, and both powers lie in `Lʳ((0, 1])`
because `3/q + 2/r > 1` and `3/p < 3/q + 2/r`. -/
theorem physical_memLp_LsLq (hR : 0 < R) {q r : ℝ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hqr : 1 < 3 / q + 2 / r) :
    (∀ t ∈ Ioc (0 : ℝ) 1, MemLp (IncompressibleFlow.velocitySlice (physicalVelocity D R s) t)
      (ENNReal.ofReal q) volume) ∧
    MemLp (fun t ↦ (eLpNorm (IncompressibleFlow.velocitySlice (physicalVelocity D R s) t)
      (ENNReal.ofReal q) volume).toReal) (ENNReal.ofReal r) (volume.restrict (Ioc 0 1)) := by
  have hr0 : 0 < r := by linarith
  have hQ : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal hq
  refine ⟨fun t ht ↦ memLp_velocitySlice_physicalVelocity D s hR hQ ht.1, ?_⟩
  obtain ⟨p, hp1, hpq, hp3, hp⟩ := exists_lebesgueExponent hq hr hqr
  obtain ⟨A, B, -, -, hbound⟩ := exists_toReal_eLpNorm_velocitySlice_le D s hR hp1 hp3 hpq hq
  have hkey : (3 / q + 2 / r) * r = 3 / q * r + 2 := by
    field_simp
  have ha : -1 < (3 / q - 1) / 2 * r := by
    have h1 := mul_lt_mul_of_pos_right hqr hr0
    have h2 : (3 / q - 1) / 2 * r = (3 / q * r - r) / 2 := by ring
    rw [h2]
    linarith
  have hb : -1 < (3 / q - 3 / p) / 2 * r := by
    have h1 := mul_lt_mul_of_pos_right hp hr0
    have h2 : (3 / q - 3 / p) / 2 * r = (3 / q * r - 3 / p * r) / 2 := by ring
    rw [h2]
    linarith
  refine (((memLp_rpow_Ioc hr0 ha).const_mul A).add
    ((memLp_rpow_Ioc hr0 hb).const_mul B)).of_le
    (((continuousOn_toReal_eLpNorm_velocitySlice_physicalVelocity D s hR hQ).mono
      fun t ht ↦ ht.1).aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht ↦ ?_))
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (hbound t ht).trans (Real.le_norm_self _)

end NavierStokes.Nonuniqueness

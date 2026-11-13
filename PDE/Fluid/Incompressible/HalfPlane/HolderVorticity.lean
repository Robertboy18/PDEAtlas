/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.DecayingVorticity
public import PDE.Fluid.Incompressible.HalfPlane.VelocityHigherOrder
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoffBounds
import PDE.FDeriv.Laplacian.Congruence

/-!
# The half-plane stream function of a decaying Hölder vorticity

The class `IsHolderVorticity α f`: `f` is continuous on the closed upper half-plane, odd in `x₀`
there, decays like `(1 + |y|)^(-β)` for some `β > 0`, and is `α`-Hölder on the closed upper
half-plane inside every disc, `0 < α < 1`. This is the decaying class of
`IncompressibleFlow.IsDecayingVorticity` with the `C²` hypothesis replaced by local Hölder
continuity, the regularity of the weighted Hölder norms in the energy estimates of Chen and Hou,
Part I, Section 5.4.

For `R > 0` the vorticity splits into the compact near source `nearSource R f`, the even extension
below the wall of `χ_R f` with the radial cutoff `χ_R` (one on `B(0, R)`, zero outside `B(0, 2R)`),
and the far source `farSource R f = (1 - χ_R) f`, which vanishes on `B(0, R)`. The grouped quadrant
potential `Ψ = GreenFunction.quadrantPotential f` is `C²` at every point of the open upper
half-plane (`IsHolderVorticity.contDiffAt_quadrantPotential`) and within the closed one, `C¹` on the
plane (`IsHolderVorticity.contDiff_one_quadrantPotential`), and solves `-ΔΨ = f` in the open upper
half-plane (`IsHolderVorticity.neg_laplacian_quadrantPotential`).

## Main definitions

* `IsHolderVorticity`: `f` is continuous on the closed upper half-plane, odd in `x₀` there,
  decays like `(1 + |y|)^(-β)` for some `β > 0`, and is `α`-Hölder there inside every disc.
* `nearSource`: the even extension below the wall of `χ_R f`.
* `farSource`: the far source `(1 - χ_R) f`, which vanishes on `B(0, R)`.

## Main results

* `exists_abs_radialCutoff_sub_le`: for `0 < α ≤ 1` there is `K` with
  `|χ_δ(y - c) - χ_δ(z - c)| ≤ K δ^(-α) |y - z|^α` for every scale `δ > 0` and center `c`.
* `abs_mul_sub_mul_le`: a cutoff product `g f` with `|g| ≤ 1` is `α`-Hölder with constant `L + K B`.
* `IsHolderVorticity.exists_holder_nearSource`: for `R > 0` the near source is `α`-Hölder on the
  closed upper half-plane.
* `IsHolderVorticity.quadrantPotential_eq`: for `|x| < R/2`, `Ψ` is the Green potential of the
  near source plus the grouped potential of the far source.
* `IsHolderVorticity.contDiffAt_quadrantPotential`: `Ψ` is `C²` at every point of the open upper
  half-plane.
* `IsHolderVorticity.contDiff_one_quadrantPotential`: `Ψ` is `C¹` on the plane.
* `IsHolderVorticity.neg_laplacian_quadrantPotential`: `-ΔΨ = f` in the open upper half-plane.
* `IsHolderVorticity.contDiffOn_quadrantPotential`: `Ψ` is `C²` within the closed upper
  half-plane.

## How it works

At a point `x` we take `R = 2(|x| + 1)`, so that `x` lies in `B(0, R/2)`. There `Ψ` is the Green
potential of the near source plus the grouped potential of the far source
(`IsHolderVorticity.quadrantPotential_eq`); for the near source, which is odd in `x₀`, the two
potentials agree by `halfSpaceGreenPotential_eq_quadrantPotential`. The cutoff bounds
`exists_abs_radialCutoff_sub_le` and `abs_mul_sub_mul_le` make the near source `α`-Hölder on the
closed upper half-plane (`IsHolderVorticity.exists_holder_nearSource`), so its Green potential is
`C²` within the closed half-plane by the Hölder theory of the velocity
(`contDiffOn_succ_succ_halfSpaceGreenPotential` with `k = 0`) and `C¹` on the plane
(`contDiff_one_halfSpaceGreenPotential`). The far potential is smooth and harmonic on `B(0, R/2)`
(`contDiffOn_quadrantPotential_ball`, `laplacian_quadrantPotential_ball`). For the Poisson equation,
`-Δ` of the near potential is the clockwise curl `∂₁u₀ - ∂₀u₁` of its velocity, which is the near
source (`partialDeriv_halfPlaneVelocity_div_curl`), and the near source is `f` at `x`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4, pp. 68-75.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open PDE.Analysis (evenReflection evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

/-- The grouped quadrant potential only reads its density on the open quadrant. -/
theorem GreenFunction.quadrantPotential_congr {f g : ℝ^2 → ℝ}
    (h : Set.EqOn f g GreenFunction.quadrant) : quadrantPotential f = quadrantPotential g := by
  funext x
  unfold quadrantPotential
  refine MeasureTheory.setIntegral_congr_fun GreenFunction.measurableSet_quadrant fun y hy ↦ ?_
  simp only [h hy]

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

/-- A vorticity of the decaying Hölder class: continuous on the closed upper half-plane, odd in
`x₀` there, decaying like `(1 + |y|)^(-β)` for some `β > 0`, and `α`-Hölder on the closed upper
half-plane inside every disc, with `0 < α < 1`. -/
structure IsHolderVorticity (α : ℝ) (f : ℝ^2 → ℝ) : Prop where
  /-- The Hölder exponent is positive. -/
  exponent_pos : 0 < α
  /-- The Hölder exponent is less than one. -/
  exponent_lt_one : α < 1
  /-- `f` is continuous on the closed upper half-plane. -/
  continuousOn : ContinuousOn f {y | 0 ≤ y 1}
  /-- `f` is odd in `x₀` on the closed upper half-plane. -/
  odd : ∀ y, 0 ≤ y 1 → f (𝐑 0 y) = -f y
  /-- The decay `|f(y)| ≤ C (1 + |y|)^(-β)`, `β > 0`. -/
  decay : ∃ C β : ℝ, 0 < β ∧ ∀ y, 0 ≤ y 1 → |f y| ≤ C * (1 + ‖y‖) ^ (-β)
  /-- `f` is `α`-Hölder on the closed upper half-plane inside every disc. -/
  holder : ∀ ρ : ℝ, ∃ L : ℝ, ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖y‖ ≤ ρ → ‖z‖ ≤ ρ →
    |f y - f z| ≤ L * ‖y - z‖ ^ α

/-! ### Cutoffs -/

section Cutoff

/-- The radial cutoff takes values in `[0, 1]`. -/
theorem abs_radialCutoff_le_one (R : ℝ) (y : ℝ^2) : |radialCutoff R y| ≤ 1 := by
  have h := radialCutoff_mem_Icc R y
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The radial cutoff at scale `δ` is the unit cutoff at `δ⁻¹ y`. -/
theorem radialCutoff_eq_radialCutoff_one (δ : ℝ) (y : ℝ^2) :
    radialCutoff δ y = radialCutoff 1 (δ⁻¹ • y) := by
  simp [radialCutoff]

/-- **Hölder bound of the radial cutoff**: for `0 < α ≤ 1` there is `K` with
`|χ_δ(y - c) - χ_δ(z - c)| ≤ K δ^(-α) |y - z|^α` for every scale `δ > 0` and center `c`. -/
theorem exists_abs_radialCutoff_sub_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → ∀ c y z : ℝ^2,
      |radialCutoff δ (y - c) - radialCutoff δ (z - c)| ≤ K * δ ^ (-α) * ‖y - z‖ ^ α := by
  obtain ⟨C, hC⟩ :=
    (contDiff_radialCutoff (n := 2) 1 (k := 1)).lipschitzWith_of_hasCompactSupport
      (radialCutoff_hasCompactSupport one_pos) (by norm_num)
  refine ⟨max (C : ℝ) 1, by positivity, fun δ hδ c y z ↦ ?_⟩
  rw [radialCutoff_eq_radialCutoff_one δ (y - c), radialCutoff_eq_radialCutoff_one δ (z - c)]
  set s := δ⁻¹ * ‖y - z‖ with hs
  have hs0 : 0 ≤ s := by positivity
  have hlip : |radialCutoff 1 (δ⁻¹ • (y - c)) - radialCutoff 1 (δ⁻¹ • (z - c))| ≤ C * s := by
    have := hC.dist_le_mul (δ⁻¹ • (y - c)) (δ⁻¹ • (z - c))
    rw [Real.dist_eq, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)] at this
    exact this
  have hone : |radialCutoff 1 (δ⁻¹ • (y - c)) - radialCutoff 1 (δ⁻¹ • (z - c))| ≤ 1 := by
    have h1 := radialCutoff_mem_Icc (n := 2) 1 (δ⁻¹ • (y - c))
    have h2 := radialCutoff_mem_Icc (n := 2) 1 (δ⁻¹ • (z - c))
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hpow : δ ^ (-α) * ‖y - z‖ ^ α = s ^ α := by
    rw [hs, Real.mul_rpow (inv_nonneg.mpr hδ.le) (norm_nonneg _), Real.inv_rpow hδ.le,
      Real.rpow_neg hδ.le]
  rw [mul_assoc, hpow]
  rcases le_or_gt s 1 with h1 | h1
  · rcases eq_or_lt_of_le hs0 with h0 | h0
    · rw [← h0] at hlip ⊢
      simp only [mul_zero] at hlip
      rw [Real.zero_rpow hα.ne', mul_zero]
      exact hlip
    · have hsa : s ≤ s ^ α := by
        calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
          _ ≤ s ^ α := Real.rpow_le_rpow_of_exponent_ge h0 h1 hα1
      calc _ ≤ (C : ℝ) * s := hlip
        _ ≤ max (C : ℝ) 1 * s ^ α := by
          gcongr
          · exact le_max_left _ _
  · have hsa : 1 ≤ s ^ α := Real.one_le_rpow h1.le hα.le
    calc _ ≤ 1 := hone
      _ ≤ max (C : ℝ) 1 * s ^ α := by
        calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
          _ ≤ max (C : ℝ) 1 * s ^ α := mul_le_mul (le_max_right _ _) hsa zero_le_one
              (by positivity)

/-- **Hölder bound of a cutoff product.** If `|g| ≤ 1`, `g` is `α`-Hölder with constant `K`
and vanishes outside `T`, and `f` is bounded by `B` and `α`-Hölder with constant `L` on
`S ∩ T`, then `g f` is `α`-Hölder on `S` with constant `L + K B`. -/
theorem abs_mul_sub_mul_le {S T : Set (ℝ^2)} {g f : ℝ^2 → ℝ} {K L B α : ℝ} (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hg : ∀ y, |g y| ≤ 1)
    (hgK : ∀ y z, |g y - g z| ≤ K * ‖y - z‖ ^ α) (hgT : ∀ y, y ∉ T → g y = 0)
    (hfB : ∀ y ∈ S, y ∈ T → |f y| ≤ B)
    (hfL : ∀ y ∈ S, ∀ z ∈ S, y ∈ T → z ∈ T → |f y - f z| ≤ L * ‖y - z‖ ^ α)
    {y z : ℝ^2} (hy : y ∈ S) (hz : z ∈ S) :
    |g y * f y - g z * f z| ≤ (L + K * B) * ‖y - z‖ ^ α := by
  have ht : 0 ≤ ‖y - z‖ ^ α := by positivity
  have hgyz := hgK y z
  by_cases hyT : y ∈ T <;> by_cases hzT : z ∈ T
  · have h1 : |g y * (f y - f z)| ≤ L * ‖y - z‖ ^ α := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hg y)).trans (hfL y hy z hz hyT hzT)
    have h2 : |f z * (g y - g z)| ≤ B * (K * ‖y - z‖ ^ α) := by
      rw [abs_mul]
      exact mul_le_mul (hfB z hz hzT) hgyz (abs_nonneg _) hB
    calc |g y * f y - g z * f z| = |g y * (f y - f z) + f z * (g y - g z)| := by ring_nf
      _ ≤ |g y * (f y - f z)| + |f z * (g y - g z)| := abs_add_le _ _
      _ ≤ L * ‖y - z‖ ^ α + B * (K * ‖y - z‖ ^ α) := add_le_add h1 h2
      _ = (L + K * B) * ‖y - z‖ ^ α := by ring
  · have he : g y * f y - g z * f z = f y * (g y - g z) := by rw [hgT z hzT]; ring
    rw [he, abs_mul]
    calc |f y| * |g y - g z| ≤ B * (K * ‖y - z‖ ^ α) :=
          mul_le_mul (hfB y hy hyT) hgyz (abs_nonneg _) hB
      _ ≤ (L + K * B) * ‖y - z‖ ^ α := by nlinarith
  · have he : g y * f y - g z * f z = f z * (g y - g z) := by rw [hgT y hyT]; ring
    rw [he, abs_mul]
    calc |f z| * |g y - g z| ≤ B * (K * ‖y - z‖ ^ α) :=
          mul_le_mul (hfB z hz hzT) hgyz (abs_nonneg _) hB
      _ ≤ (L + K * B) * ‖y - z‖ ^ α := by nlinarith
  · rw [hgT y hyT, hgT z hzT]
    simp only [zero_mul, sub_self, abs_zero]
    positivity

end Cutoff

/-! ### The near and far sources -/

/-- The near source: the even extension below the wall of `χ_R f`, with the radial cutoff `χ_R`
equal to one on `B(0, R)` and to zero outside `B(0, 2R)`. -/
def nearSource (R : ℝ) (f : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  evenReflection fun y ↦ radialCutoff R y * f y

/-- The far source `(1 - χ_R) f`, which vanishes on `B(0, R)`. -/
def farSource (R : ℝ) (f : ℝ^2 → ℝ) (y : ℝ^2) : ℝ :=
  (1 - radialCutoff R y) * f y

variable {α : ℝ} {f : ℝ^2 → ℝ} {R : ℝ}

/-- On the closed upper half-plane the near source is `χ_R f`. -/
theorem nearSource_of_nonneg {y : ℝ^2} (hy : 0 ≤ y 1) :
    nearSource R f y = radialCutoff R y * f y :=
  evenReflection_of_nonneg hy

/-- On the closed upper half-plane inside `B(0, R)` the near source is `f`. -/
theorem nearSource_eq_self (hR : 0 < R) {y : ℝ^2} (hy : 0 ≤ y 1) (hyR : ‖y‖ ≤ R) :
    nearSource R f y = f y := by
  rw [nearSource_of_nonneg hy, radialCutoff_eq_one hR hyR, one_mul]

/-- The near source vanishes on the closed upper half-plane outside `B(0, 2R)`. -/
theorem nearSource_eq_zero (hR : 0 < R) {y : ℝ^2} (hy : 0 ≤ y 1) (hyR : 2 * R ≤ ‖y‖) :
    nearSource R f y = 0 := by
  rw [nearSource_of_nonneg hy, radialCutoff_eq_zero_of_le_norm hR hyR, zero_mul]

/-- The near source of a function continuous on the closed upper half-plane is continuous. -/
theorem continuous_nearSource (hf : ContinuousOn f {y | 0 ≤ y 1}) :
    Continuous (nearSource R f) :=
  continuous_evenReflection
    (((contDiff_radialCutoff (n := 2) R (k := 0)).continuous.continuousOn).mul hf)

/-- The near source is compactly supported. -/
theorem hasCompactSupport_nearSource (hR : 0 < R) : HasCompactSupport (nearSource R f) :=
  hasCompactSupport_evenReflection_of_eq_zero (R := 2 * R) fun _ hy hyR ↦ by
    rw [radialCutoff_eq_zero_of_le_norm hR hyR.le, zero_mul]

/-- The near source of a function odd in `x₀` is odd in `x₀` on the closed upper half-plane. -/
theorem nearSource_odd (hodd : ∀ y, 0 ≤ y 1 → f (𝐑 0 y) = -f y) {y : ℝ^2} (hy : 0 ≤ y 1) :
    nearSource R f (𝐑 0 y) = -nearSource R f y := by
  have hy' : 0 ≤ (𝐑 0 y) 1 := by
    rwa [PDE.Common.coordinateReflection_apply_of_ne 0 1 (by decide)]
  rw [nearSource_of_nonneg hy', nearSource_of_nonneg hy, radialCutoff_even R 0 y, hodd y hy,
    mul_neg]

/-- A function bounded by `C (1 + |y|)^(-β)` is bounded. -/
theorem IsHolderVorticity.exists_bound (hf : IsHolderVorticity α f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, 0 ≤ y 1 → |f y| ≤ B := by
  obtain ⟨C, β, hβ, hdec⟩ := hf.decay
  refine ⟨max C 0, le_max_right _ _, fun y hy ↦ (hdec y hy).trans ?_⟩
  have h1 : (1 + ‖y‖) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)
  have h0 : 0 < (1 + ‖y‖) ^ (-β) := by positivity
  rcases le_total 0 C with hC | hC
  · calc C * (1 + ‖y‖) ^ (-β) ≤ C * 1 := by gcongr
      _ ≤ max C 0 := by simp
  · calc C * (1 + ‖y‖) ^ (-β) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC h0.le
      _ ≤ max C 0 := le_max_right _ _

/-- **The near source is Hölder.** For `R > 0` the near source is `α`-Hölder on the closed upper
half-plane. -/
theorem IsHolderVorticity.exists_holder_nearSource (hf : IsHolderVorticity α f) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |nearSource R f y - nearSource R f z| ≤ M * ‖y - z‖ ^ α := by
  obtain ⟨K, hK, hKb⟩ := exists_abs_radialCutoff_sub_le hf.exponent_pos hf.exponent_lt_one.le
  obtain ⟨B, hB, hfB⟩ := hf.exists_bound
  obtain ⟨L, hL⟩ := hf.holder (2 * R)
  set L' := max L 0
  refine ⟨L' + K * R ^ (-α) * B, by positivity, fun y z hy hz ↦ ?_⟩
  rw [nearSource_of_nonneg hy, nearSource_of_nonneg hz]
  refine abs_mul_sub_mul_le (S := {y | 0 ≤ y 1}) (T := closedBall 0 (2 * R)) (by positivity)
    (le_max_right _ _) hB (abs_radialCutoff_le_one R) (fun a b ↦ ?_) (fun a ha ↦ ?_)
    (fun a ha _ ↦ hfB a ha) (fun a ha b hb haT hbT ↦ ?_) hy hz
  · have := hKb R hR 0 a b
    simpa using this
  · rw [mem_closedBall, dist_zero_right, not_le] at ha
    exact radialCutoff_eq_zero_of_le_norm hR ha.le
  · rw [mem_closedBall, dist_zero_right] at haT hbT
    exact (hL a b ha hb haT hbT).trans (by gcongr; exact le_max_left _ _)

/-- **The far source is a far density.** -/
theorem IsHolderVorticity.isQuadrantFarDensity_farSource (hf : IsHolderVorticity α f)
    (hR : 0 < R) : IsQuadrantFarDensity (farSource R f) R where
  pos := hR
  eq_zero y _ hy := by simp [farSource, radialCutoff_eq_one hR hy.le]
  aestronglyMeasurable :=
    ((((continuous_const.sub (contDiff_radialCutoff (n := 2) R (k := 0)).continuous)).continuousOn
      ).mul (hf.continuousOn.mono fun _ hy ↦ (le_of_lt hy.2 : (0 : ℝ) ≤ _))).aestronglyMeasurable
      measurableSet_quadrant
  integrableOn := by
    obtain ⟨C, β, hβ, hdec⟩ := hf.decay
    have hint : Integrable (fun y : ℝ^2 ↦ (1 + ‖y‖) ^ (-(β + 2))) := by
      refine integrable_one_add_norm ?_
      simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    set K := C * ((1 + R) / R) ^ 2
    have hcont : ContinuousOn (fun y ↦ farSource R f y / ‖y‖ ^ 2) GreenFunction.quadrant :=
      ((((continuous_const.sub (contDiff_radialCutoff (n := 2) R (k := 0)).continuous)).continuousOn
        ).mul (hf.continuousOn.mono fun _ hy ↦ (le_of_lt hy.2 : (0 : ℝ) ≤ _))).div
        (continuous_norm.pow 2).continuousOn
        (fun y hy ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr (by rintro rfl; simpa using hy.1)))
    refine Integrable.mono' (hint.const_mul K).integrableOn
      (hcont.aestronglyMeasurable measurableSet_quadrant) ?_
    filter_upwards [ae_restrict_mem measurableSet_quadrant] with y hy
    have hy1 : 0 ≤ y 1 := le_of_lt hy.2
    have hC : 0 ≤ C := by
      have := (abs_nonneg (f y)).trans (hdec y hy1)
      have hpos : 0 < (1 + ‖y‖) ^ (-β) := by positivity
      exact nonneg_of_mul_nonneg_left this hpos
    by_cases hyR : ‖y‖ < R
    · simp only [farSource, radialCutoff_eq_one hR hyR.le, sub_self, zero_mul, zero_div,
        norm_zero]
      exact mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
    · have hyR' : R ≤ ‖y‖ := le_of_not_gt hyR
      have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hyR'
      have hc := radialCutoff_mem_Icc (n := 2) R y
      have hfar : |farSource R f y| ≤ |f y| := by
        rw [farSource, abs_mul, abs_of_nonneg (by linarith [hc.2] : (0 : ℝ) ≤ 1 - _)]
        exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hc.1])
      have hratio : 1 / ‖y‖ ^ 2 ≤ ((1 + R) / R) ^ 2 / (1 + ‖y‖) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, div_pow,
          div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : R * (1 + ‖y‖) ≤ (1 + R) * ‖y‖ := by nlinarith
        nlinarith [mul_le_mul this this (by positivity) (by positivity)]
      have hpow : (1 + ‖y‖) ^ (-(β + 2)) = (1 + ‖y‖) ^ (-β) / (1 + ‖y‖) ^ 2 := by
        rw [show -(β + 2) = -β + -(2 : ℝ) by ring, Real.rpow_add (by positivity),
          Real.rpow_neg (by positivity) 2, Real.rpow_two, div_eq_mul_inv]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 2), hpow]
      calc |farSource R f y| / ‖y‖ ^ 2 = |farSource R f y| * (1 / ‖y‖ ^ 2) := by ring
        _ ≤ (C * (1 + ‖y‖) ^ (-β)) * (((1 + R) / R) ^ 2 / (1 + ‖y‖) ^ 2) := by
            gcongr
            exact hfar.trans (hdec y hy1)
        _ = K * ((1 + ‖y‖) ^ (-β) / (1 + ‖y‖) ^ 2) := by ring

/-- **The decomposition.** For `R > 0` and `|x| < R/2`, the grouped quadrant potential of `f` is the
Green potential of the near source plus the grouped potential of the far source. -/
theorem IsHolderVorticity.quadrantPotential_eq (hf : IsHolderVorticity α f) (hR : 0 < R)
    {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    quadrantPotential f x =
      halfSpaceGreenPotential (nearSource R f) x + quadrantPotential (farSource R f) x := by
  have hN := continuous_nearSource (R := R) hf.continuousOn
  have hNc := hasCompactSupport_nearSource (f := f) hR
  have hNodd : ∀ y, 0 ≤ y 1 → nearSource R f (𝐑 0 y) = -nearSource R f y :=
    fun y hy ↦ nearSource_odd hf.odd hy
  rw [halfSpaceGreenPotential_eq_quadrantPotential hN hNc hNodd]
  unfold quadrantPotential
  rw [← integral_add (integrableOn_symmetrizedKernel_fundamentalSolution_of_compact hN hNc
    hNodd x) (integrableOn_symmetrizedKernel_fundamentalSolution_of_far
      (hf.isQuadrantFarDensity_farSource hR) hx)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  simp only [nearSource_of_nonneg (le_of_lt hy.2), farSource]
  ring

/-- The decomposition as an equality of germs at a point of `B(0, R/2)`. -/
theorem IsHolderVorticity.quadrantPotential_eventuallyEq (hf : IsHolderVorticity α f)
    (hR : 0 < R) {x : ℝ^2} (hx : ‖x‖ < R / 2) :
    quadrantPotential f =ᶠ[𝓝 x] fun y ↦
      halfSpaceGreenPotential (nearSource R f) y + quadrantPotential (farSource R f) y := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
  exact hf.quadrantPotential_eq hR (mem_ball_zero_iff.mp hy)

/-! ### Regularity -/

/-- The Green potential of a continuous compactly supported source, `α`-Hölder on the closed
upper half-plane with `0 < α < 1`, is `C²` at every point of the open upper half-plane. -/
theorem contDiffAt_halfSpaceGreenPotential_of_holder {P : ℝ^2 → ℝ} (hP : Continuous P)
    (hc : HasCompactSupport P) {M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |P y - P z| ≤ M * ‖y - z‖ ^ α) {x : ℝ^2}
    (hx : 0 < x 1) : ContDiffAt ℝ 2 (halfSpaceGreenPotential P) x := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hR : ∀ y : ℝ^2, 0 ≤ y 1 → r < ‖y‖ → P y = 0 := fun y _ hy ↦ by
    by_contra h
    have := hr (subset_tsupport _ h)
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hM' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 0 P {y | 0 ≤ y 1} y - iteratedFDerivWithin ℝ 0 P {y | 0 ≤ y 1} z‖ ≤
        M * ‖y - z‖ ^ α := by
    intro y z hy hz
    rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hM y z hy hz
  have h := contDiffOn_succ_succ_halfSpaceGreenPotential (k := 0) hα hα1
    (contDiffOn_zero.mpr hP.continuousOn) hR hM'
  have hxU : x ∈ HalfSpace.upper 2 := hx
  have hmem : {y : ℝ^2 | 0 ≤ y 1} ∈ 𝓝 x :=
    mem_of_superset ((HalfSpace.isOpen_upper (n := 2)).mem_nhds hxU)
      fun y (hy : y ∈ HalfSpace.upper 2) ↦ le_of_lt (show 0 < y 1 from hy)
  simpa using h.contDiffAt hmem

variable (hf : IsHolderVorticity α f)
include hf

/-- The Green potential of the near source is `C²` in the open upper half-plane. -/
theorem IsHolderVorticity.contDiffAt_nearSource (hR : 0 < R) {x : ℝ^2} (hx : 0 < x 1) :
    ContDiffAt ℝ 2 (halfSpaceGreenPotential (nearSource R f)) x := by
  obtain ⟨M, -, hM⟩ := hf.exists_holder_nearSource hR
  exact contDiffAt_halfSpaceGreenPotential_of_holder (continuous_nearSource hf.continuousOn)
    (hasCompactSupport_nearSource hR) hf.exponent_pos hf.exponent_lt_one hM hx

/-- The grouped potential of the far source is smooth on `B(0, R/2)`. -/
theorem IsHolderVorticity.contDiffAt_farSource (hR : 0 < R) {x : ℝ^2} (hx : ‖x‖ < R / 2)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (quadrantPotential (farSource R f)) x :=
  (contDiffOn_quadrantPotential_ball (hf.isQuadrantFarDensity_farSource hR)).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx))

/-- **Regularity of the stream**: the grouped quadrant potential of a decaying Hölder vorticity
is `C²` at every point of the open upper half-plane. -/
theorem IsHolderVorticity.contDiffAt_quadrantPotential {x : ℝ^2} (hx : 0 < x 1) :
    ContDiffAt ℝ 2 (quadrantPotential f) x := by
  have hR : 0 < 2 * (‖x‖ + 1) := by positivity
  have hxR : ‖x‖ < 2 * (‖x‖ + 1) / 2 := by linarith
  exact ((hf.contDiffAt_nearSource hR hx).add
    (hf.contDiffAt_farSource hR hxR)).congr_of_eventuallyEq
    (hf.quadrantPotential_eventuallyEq hR hxR)

/-- The grouped quadrant potential of a decaying Hölder vorticity is `C¹` on the plane. -/
theorem IsHolderVorticity.contDiff_one_quadrantPotential :
    ContDiff ℝ 1 (quadrantPotential f) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  have hR : 0 < 2 * (‖x‖ + 1) := by positivity
  have hxR : ‖x‖ < 2 * (‖x‖ + 1) / 2 := by linarith
  exact ((contDiff_one_halfSpaceGreenPotential (continuous_nearSource hf.continuousOn)
    (hasCompactSupport_nearSource hR)).contDiffAt.add
      (hf.contDiffAt_farSource hR hxR)).congr_of_eventuallyEq
    (hf.quadrantPotential_eventuallyEq hR hxR)

/-- **Poisson equation**: `-ΔΨ = f` in the open upper half-plane. -/
theorem IsHolderVorticity.neg_laplacian_quadrantPotential {x : ℝ^2} (hx : 0 < x 1) :
    -PDE.laplacian (quadrantPotential f) x = f x := by
  have hR : 0 < 2 * (‖x‖ + 1) := by positivity
  have hxR : ‖x‖ < 2 * (‖x‖ + 1) / 2 := by linarith
  set R := 2 * (‖x‖ + 1)
  obtain ⟨M, -, hM⟩ := hf.exists_holder_nearSource hR
  have hN := continuous_nearSource (R := R) hf.continuousOn
  have hNc := hasCompactSupport_nearSource (f := f) hR
  have hxU : x ∈ HalfSpace.upper 2 := hx
  obtain ⟨-, hcurl⟩ := partialDeriv_halfPlaneVelocity_div_curl hN hNc hf.exponent_pos
    hf.exponent_lt_one.le hM hxU
  rw [EuclideanLaplacian.laplacian_congr_nhds (hf.quadrantPotential_eventuallyEq hR hxR),
    PDE.laplacian_add _ _ x (hf.contDiffAt_nearSource hR hx) (hf.contDiffAt_farSource hR hxR),
    laplacian_quadrantPotential_ball (hf.isQuadrantFarDensity_farSource hR) hxR, add_zero]
  rw [halfPlaneVelocity_zero, halfPlaneVelocity_one] at hcurl
  have hN0 : nearSource R f x = f x := nearSource_eq_self hR hx.le (by simp [R]; linarith)
  rw [← hN0, ← hcurl]
  simp only [PDE.laplacian, Fin.sum_univ_two, PDE.partialDeriv_neg]
  ring

/-- **The stream function is `C²` within the closed upper half-plane.** For a decaying Hölder
vorticity the grouped quadrant potential is `C²` within `{0 ≤ x₁}`: near a point it is the Green
potential of the compact near source (`C²` within the closed half-plane) plus the smooth far
potential. -/
theorem IsHolderVorticity.contDiffOn_quadrantPotential :
    ContDiffOn ℝ 2 (quadrantPotential f) {y | 0 ≤ y 1} := by
  intro x _
  have hR : 0 < 2 * (‖x‖ + 1) := by positivity
  have hxR : ‖x‖ < 2 * (‖x‖ + 1) / 2 := by linarith
  set R := 2 * (‖x‖ + 1)
  obtain ⟨M, -, hM⟩ := hf.exists_holder_nearSource hR
  have hz : ∀ y : ℝ^2, 0 ≤ y 1 → 2 * R < ‖y‖ → nearSource R f y = 0 := fun y hy hyR ↦
    nearSource_eq_zero hR hy hyR.le
  have hM' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ 0 (nearSource R f) {y | 0 ≤ y 1} y -
        iteratedFDerivWithin ℝ 0 (nearSource R f) {y | 0 ≤ y 1} z‖ ≤ M * ‖y - z‖ ^ α := by
    intro y z hy hz
    rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    exact hM y z hy hz
  have hN : ContDiffOn ℝ 2 (halfSpaceGreenPotential (nearSource R f)) {y | 0 ≤ y 1} := by
    have h := contDiffOn_succ_succ_halfSpaceGreenPotential (k := 0) hf.exponent_pos
      hf.exponent_lt_one (contDiffOn_zero.mpr (continuous_nearSource hf.continuousOn).continuousOn)
      hz hM'
    simpa using h
  have hsum : ContDiffWithinAt ℝ 2 (fun y ↦ halfSpaceGreenPotential (nearSource R f) y +
      quadrantPotential (farSource R f) y) {y | 0 ≤ y 1} x :=
    (hN.contDiffWithinAt ‹_›).add (hf.contDiffAt_farSource hR hxR).contDiffWithinAt
  exact hsum.congr_of_eventuallyEq
    ((hf.quadrantPotential_eventuallyEq hR hxR).filter_mono nhdsWithin_le_nhds)
    (hf.quadrantPotential_eq hR hxR)

end IncompressibleFlow

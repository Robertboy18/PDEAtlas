/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityLipschitz
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BoundedSource
public import PDE.Analysis.Calculus.HalfPlaneHolderDerivative
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarGradientVector
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import PDE.FDeriv.Reflection.Coordinate
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The half-plane velocity of bounded integrable vorticity

The half-plane velocity estimates for compactly supported vorticity extend to vorticity `f` that is
continuous on the closed upper half-plane `H̄ = {x₁ ≥ 0}`, bounded there by `B` and integrable on
the open half-plane `H` with `L = ∫_H |f|`; for the derivative statements `f` is also `α`-Hölder on
`H̄` with constant `M`. The Green potential `φ = halfSpaceGreenPotential f` then converges
absolutely (`GreenFunction.hasIntegrableHalfSpaceGreenPotential_of_bounded`), it is `C¹` on the
plane, and the velocity is its rotated gradient. The velocity is bounded, tangent to the boundary
and, for `0 < α < 1`, Lipschitz on `H̄` with an `α`-Hölder derivative.

## Main results

* `hasFDerivAt_halfSpaceGreenPotential_of_integrable`: the Green potential of bounded integrable
  vorticity is differentiable at every point of the plane, with gradient
  `V(x) = ∫ W(x - z) K(z) dz`, where `W` is the odd extension of `f` and `K` the gradient kernel.
* `halfPlaneVelocity_eq_of_integrable`: the velocity is the rotated gradient field,
  `u(f)(x) = (-V(x)₁, V(x)₀)`.
* `norm_halfPlaneVelocity_le_of_integrable`: `‖u(f)(x)‖ ≤ B + π⁻¹ ∫_{ℝ²₊} |f|` on the plane.
* `halfPlaneVelocity_normal_eq_zero_of_integrable`: the normal velocity vanishes on the boundary.
* `hasFDerivAt_halfPlaneVelocity_of_integrable`: for `α`-Hölder data, `0 < α ≤ 1`, the velocity is
  differentiable in the open half-plane with the principal-value formulas as partial derivatives.
* `abs_partialDeriv_halfPlaneVelocity_sub_le_of_integrable`: for `0 < α < 1`,
  `|∂ᵢuₖ(x) - ∂ᵢuₖ(x')| ≤ 211/(α(1-α)) · M |x - x'|^α` in the open half-plane.
* `dist_fderivWithin_halfPlaneVelocity_le_of_integrable`: for `0 < α < 1` the derivative extends
  `α`-Hölder to the closed half-plane, with constant `844/(α(1-α)) · M`.
* `lipschitzOnWith_halfPlaneVelocity_of_integrable`: for `0 < α < 1` the velocity is Lipschitz on
  the closed half-plane with constant `4((50/α)(1 + B log(2 + M)) + 8B + 10L)`.

## How it works

We cut off the vorticity, `fₙ = ρₙ f` with `ρₙ(y) = clamp(n + 1 - |y|)`, and apply the compactly
supported theory to each `fₙ`. The potentials converge pointwise by dominated convergence, and their
gradients `∫ W(x - z) K(z) dz` converge uniformly by the near and far bound `Bρ + ‖W - Wₙ‖₁/(2πρ)`;
this gives `hasFDerivAt_halfSpaceGreenPotential_of_integrable`. For `α`-Hölder data the gradient
formulas `halfPlaneVelocityGradient` of the cutoffs converge locally uniformly in the open
half-plane, since `f - fₙ` vanishes on the disc of radius `n` and the gradient formula of a
vorticity vanishing near a point is bounded by its mass
(`abs_halfPlaneVelocityGradient_le_of_eq_zero`). So `Du(f)` is given by the principal-value
formulas, and the estimates proved for these formulas apply as they stand
(`abs_partialDeriv_halfPlaneVelocity_le_of_integrable`,
`abs_partialDeriv_halfPlaneVelocity_le_log_of_integrable`). For `0 < α < 1` the derivative extends
`α`-Hölder to the closed half-plane by `PDE.Analysis.hasFDerivWithinAt_closedUpper_of_holder`
(`differentiableOn_halfPlaneVelocity_of_integrable`), and the logarithmic bound on the derivative
makes the velocity Lipschitz on the convex set `H̄`. The bound `B + L/π` is the mass bound of the
gradient kernel applied to the odd extension, and the normal velocity vanishes because the potential
vanishes on the boundary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology Convolution
open GreenFunction PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection halfPlaneFold norm_halfPlaneFold evenReflection_of_nonneg
  evenReflection_evenReflection continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero abs_evenReflection_sub_le)

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The cutoffs -/

/-- The radial cutoff `clamp(n + 1 - |y|)`: one on the disc of radius `n`, zero outside the disc
of radius `n + 1`, `1`-Lipschitz. -/
private def cutoff (n : ℕ) (y : ℝ^2) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - ‖y‖))

/-- The cutoff is nonnegative. -/
private theorem cutoff_nonneg (n : ℕ) (y : ℝ^2) : 0 ≤ cutoff n y := le_max_left _ _

/-- The cutoff is at most one. -/
private theorem cutoff_le_one (n : ℕ) (y : ℝ^2) : cutoff n y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The cutoff is one on the disc of radius `n`. -/
private theorem cutoff_eq_one {n : ℕ} {y : ℝ^2} (hy : ‖y‖ ≤ n) : cutoff n y = 1 := by
  rw [cutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The cutoff vanishes outside the disc of radius `n + 1`. -/
private theorem cutoff_eq_zero {n : ℕ} {y : ℝ^2} (hy : (n : ℝ) + 1 < ‖y‖) : cutoff n y = 0 := by
  rw [cutoff, min_eq_right (by linarith), max_eq_left (by linarith)]

/-- The cutoff is continuous. -/
private theorem continuous_cutoff (n : ℕ) : Continuous (cutoff n) := by
  unfold cutoff; fun_prop

/-- The cutoff is `1`-Lipschitz. -/
private theorem abs_cutoff_sub_le (n : ℕ) (y z : ℝ^2) : |cutoff n y - cutoff n z| ≤ ‖y - z‖ := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (norm_nonneg _) ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero]
  refine max_le (norm_nonneg _) ?_
  rw [show (n : ℝ) + 1 - ‖y‖ - ((n : ℝ) + 1 - ‖z‖) = ‖z‖ - ‖y‖ by ring, abs_sub_comm]
  exact abs_norm_sub_norm_le y z

/-! ### Cut-off vorticity -/

variable {f : ℝ^2 → ℝ} {B M α : ℝ}

/-- The cut-off vorticity `ρₙ f`. -/
private def cut (f : ℝ^2 → ℝ) (n : ℕ) (y : ℝ^2) : ℝ := cutoff n y * f y

/-- `|ρₙ f| ≤ |f|`. -/
private theorem abs_cut_le (n : ℕ) (y : ℝ^2) : |cut f n y| ≤ |f y| := by
  rw [cut, abs_mul, abs_of_nonneg (cutoff_nonneg n y)]
  exact mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one n y)

/-- The cut-off vorticity `ρₙ f` vanishes outside the disc of radius `n + 1`. -/
private theorem cut_eq_zero {n : ℕ} {y : ℝ^2} (hy : (n : ℝ) + 1 < ‖y‖) : cut f n y = 0 := by
  rw [cut, cutoff_eq_zero hy, zero_mul]

/-- The cut-off vorticity `ρₙ f` is `f` on the disc of radius `n`. -/
private theorem cut_eq_self {n : ℕ} {y : ℝ^2} (hy : ‖y‖ ≤ n) : cut f n y = f y := by
  rw [cut, cutoff_eq_one hy, one_mul]

/-- For `f` continuous on `H̄`, the cut-off vorticity `ρₙ f` is continuous on `H̄`. -/
private theorem continuousOn_cut (hf : ContinuousOn f H̄) (n : ℕ) : ContinuousOn (cut f n) H̄ :=
  (continuous_cutoff n).continuousOn.mul hf

/-- The cutoffs are Hölder with the constant `M + B`, uniformly in `n`. -/
private theorem abs_cut_sub_le (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (n : ℕ) {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |cut f n y - cut f n z| ≤ (M + B) * ‖y - z‖ ^ α := by
  have hρ : |cutoff n y - cutoff n z| ≤ ‖y - z‖ ^ α := by
    rcases le_or_gt ‖y - z‖ 1 with h | h
    · refine (abs_cutoff_sub_le n y z).trans ?_
      calc ‖y - z‖ = ‖y - z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖y - z‖ ^ α := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) h hα hα1
    · have h1 : |cutoff n y - cutoff n z| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [cutoff_nonneg n y, cutoff_nonneg n z, cutoff_le_one n y,
          cutoff_le_one n z]
      exact h1.trans (Real.one_le_rpow h.le hα)
  have e : cut f n y - cut f n z = cutoff n y * (f y - f z) + f z * (cutoff n y - cutoff n z) := by
    simp only [cut]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg n y)]
  have h1 : cutoff n y * |f y - f z| ≤ M * ‖y - z‖ ^ α :=
    (mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one n y)).trans (hM y z hy hz)
  have h2 : |f z| * |cutoff n y - cutoff n z| ≤ B * ‖y - z‖ ^ α :=
    mul_le_mul (hB z hz) hρ (abs_nonneg _) ((abs_nonneg _).trans (hB z hz))
  linarith

/-- The odd extension of a function integrable on the open upper half-plane is integrable, with
twice its mass. -/
private theorem integrable_oddHalfSpaceExtension_of_integrableOn {g : ℝ^2 → ℝ}
    (hg : IntegrableOn g (HalfSpace.upper 2)) :
    Integrable (oddHalfSpaceExtension g) ∧
      ∫ y, ‖oddHalfSpaceExtension g y‖ = 2 * ∫ y in HalfSpace.upper 2, ‖g y‖ := by
  have hmp := HalfSpace.measurePreserving_reflect_restrict_lower 2
  have hemb := (HalfSpace.reflectLinearIsometryEquiv 2).toMeasurableEquiv.measurableEmbedding
  have href : IntegrableOn (fun y ↦ g (HalfSpace.reflect 2 y)) (HalfSpace.lower 2) :=
    (hmp.integrable_comp_emb hemb).mpr hg
  have hlow : IntegrableOn (fun y ↦ ‖g (HalfSpace.reflect 2 y)‖) (HalfSpace.lower 2) := href.norm
  refine ⟨(hg.integrable_indicator (HalfSpace.measurableSet_upper 2)).sub
    (href.integrable_indicator (HalfSpace.measurableSet_lower 2)), ?_⟩
  simp_rw [norm_oddHalfSpaceExtension]
  rw [integral_add (IntegrableOn.integrable_indicator hg.norm (HalfSpace.measurableSet_upper 2))
    (hlow.integrable_indicator (HalfSpace.measurableSet_lower 2)),
    integral_indicator (HalfSpace.measurableSet_upper 2),
    integral_indicator (HalfSpace.measurableSet_lower 2),
    hmp.integral_comp hemb (fun y ↦ ‖g y‖)]
  ring

/-- The cutoffs of an integrable function are integrable. -/
private theorem integrableOn_cut {s : Set (ℝ^2)} (hL : IntegrableOn f s) (n : ℕ) :
    IntegrableOn (cut f n) s :=
  hL.bdd_mul (c := 1) (continuous_cutoff n).aestronglyMeasurable.restrict
    (Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg n y)]; exact cutoff_le_one n y)

/-! ### The Green potential and the velocity -/

/-- For a continuous compactly supported source the gradient of the Green potential is the
absolutely convergent vector-kernel integral of its odd extension. -/
private theorem halfSpaceGreenPotentialGradient_eq_integral {g : ℝ^2 → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (x : ℝ^2) :
    halfSpaceGreenPotentialGradient g x =
      ∫ z, oddHalfSpaceExtension g (x - z) • gradientKernelVector z := by
  have hi := integrable_oddHalfSpaceExtension_smul_gradientKernelVector hg hc x
  ext i
  change (gradientKernel i ⋆[ContinuousLinearMap.mul ℝ ℝ] oddHalfSpaceExtension g) x =
    (EuclideanSpace.proj i) (∫ z, oddHalfSpaceExtension g (x - z) • gradientKernelVector z)
  rw [← (EuclideanSpace.proj i).integral_comp_comm hi]
  simp only [convolution, ContinuousLinearMap.mul_apply', EuclideanSpace.coe_proj,
    PiLp.smul_apply, smul_eq_mul, gradientKernelVector_apply, mul_comm]

section Integrable

variable (hf : ContinuousOn f H̄) (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
  (hL : IntegrableOn f (HalfSpace.upper 2))
include hf hB hL

omit hf hB in
/-- The masses of `f - ρₙ f` on the open half-plane tend to zero. -/
private theorem tendsto_integral_cut_sub :
    Tendsto (fun n : ℕ ↦ ∫ y in HalfSpace.upper 2, ‖cut f n y - f y‖) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (HalfSpace.upper 2))
    (F := fun (n : ℕ) y ↦ ‖cut f n y - f y‖) (f := fun _ ↦ (0 : ℝ)) (fun y ↦ 2 * ‖f y‖)
    (fun n ↦ (((continuous_cutoff n).aestronglyMeasurable.restrict.mul
      hL.aestronglyMeasurable).sub hL.aestronglyMeasurable).norm)
    (hL.norm.const_mul 2)
    (fun n ↦ Eventually.of_forall fun y ↦ by
      rw [norm_norm]
      refine (norm_sub_le _ _).trans ?_
      have := abs_cut_le (f := f) n y
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      linarith)
    (Eventually.of_forall fun y ↦ by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
      rw [cut_eq_self (le_trans (Nat.le_ceil _) (by exact_mod_cast hn)), sub_self, norm_zero])
  simpa using h

omit hB hL in
/-- The even extensions of the cutoffs are continuous with compact support and have the odd
extensions of the cutoffs. -/
private theorem cut_data (n : ℕ) :
    Continuous (evenReflection (cut f n)) ∧
      HasCompactSupport (evenReflection (cut f n)) ∧
      oddHalfSpaceExtension (evenReflection (cut f n)) = oddHalfSpaceExtension (cut f n) :=
  ⟨continuous_evenReflection (continuousOn_cut hf n),
    hasCompactSupport_evenReflection_of_eq_zero (R := (n : ℝ) + 1)
      fun _ _ hy ↦ cut_eq_zero hy,
    oddHalfSpaceExtension_congr fun _ hy ↦ evenReflection_of_nonneg (le_of_lt hy)⟩

omit hf hL in
/-- The bound `B` of `|f|` on the closed half-plane is nonnegative. -/
private theorem hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl)

/-- The gradient fields of the cutoffs differ from that of `f` by at most
`Bρ + ‖W(ρₙ f - f)‖₁/(2πρ)`, for every `ρ > 0` and at every point. -/
private theorem norm_field_sub_le (n : ℕ) (y : ℝ^2) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ z, oddHalfSpaceExtension (cut f n) (y - z) • gradientKernelVector z) -
        ∫ z, oddHalfSpaceExtension f (y - z) • gradientKernelVector z‖ ≤
      B * ρ + 2 * (∫ z in HalfSpace.upper 2, ‖cut f n z - f z‖) / (2 * Real.pi * ρ) := by
  have hB0' := hB0 hB
  obtain ⟨hW, -⟩ := integrable_oddHalfSpaceExtension_of_integrableOn hL
  have hWB : ∀ y, ‖oddHalfSpaceExtension f y‖ ≤ B :=
    norm_oddHalfSpaceExtension_le hB0' fun y hy ↦ hB y (le_of_lt hy)
  obtain ⟨hc, hcs, hodd⟩ := cut_data hf n
  have hWn : Integrable (oddHalfSpaceExtension (cut f n)) := by
    rw [← hodd]; exact integrable_oddHalfSpaceExtension hc hcs
  obtain ⟨hWd, hmass⟩ := integrable_oddHalfSpaceExtension_of_integrableOn
    ((integrableOn_cut hL n).sub hL)
  have hWnB : ∀ z, ‖oddHalfSpaceExtension (cut f n) z‖ ≤ B :=
    norm_oddHalfSpaceExtension_le hB0' fun z hz ↦ by
      rw [Real.norm_eq_abs]; exact (abs_cut_le n z).trans (hB z (le_of_lt hz))
  have hi1 : Integrable (fun z ↦ oddHalfSpaceExtension (cut f n) (y - z) •
      gradientKernelVector z) :=
    integrable_smul_gradientKernelVector (hWn.comp_sub_left y) one_pos (M := B)
      (Eventually.of_forall fun z ↦ hWnB _)
  have hi2 : Integrable (fun z ↦ oddHalfSpaceExtension f (y - z) • gradientKernelVector z) :=
    integrable_smul_gradientKernelVector (hW.comp_sub_left y) one_pos (M := B)
      (Eventually.of_forall fun z ↦ hWB _)
  have e : (∫ z, oddHalfSpaceExtension (cut f n) (y - z) • gradientKernelVector z) -
      ∫ z, oddHalfSpaceExtension f (y - z) • gradientKernelVector z =
      ∫ z, oddHalfSpaceExtension (cut f n - f) (y - z) • gradientKernelVector z := by
    rw [← integral_sub hi1 hi2, oddHalfSpaceExtension_sub]
    congr 1; funext z; simp [sub_smul]
  rw [e]
  have hdB : ∀ z, ‖oddHalfSpaceExtension (cut f n - f) (y - z)‖ ≤ B := fun z ↦
    norm_oddHalfSpaceExtension_le hB0' (fun w hw ↦ by
      rw [Real.norm_eq_abs, Pi.sub_apply]
      refine le_trans ?_ (hB w (le_of_lt hw))
      rw [cut, show cutoff n w * f w - f w = -(1 - cutoff n w) * f w by ring, abs_mul,
        abs_neg, abs_of_nonneg (by linarith [cutoff_le_one n w])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [cutoff_nonneg n w])) _
  refine (norm_integral_smul_gradientKernelVector_le_mass (hWd.comp_sub_left y) hρ
    (Eventually.of_forall fun z ↦ hdB z)).trans (le_of_eq ?_)
  rw [integral_sub_left_eq_self (fun z ↦ ‖oddHalfSpaceExtension (cut f n - f) z‖) volume y,
    hmass]
  simp only [Pi.sub_apply]

/-- The gradient fields of the cutoffs converge uniformly on the plane. -/
private theorem tendstoUniformly_field :
    TendstoUniformly
      (fun (n : ℕ) y ↦ ∫ z, oddHalfSpaceExtension (cut f n) (y - z) • gradientKernelVector z)
      (fun y ↦ ∫ z, oddHalfSpaceExtension f (y - z) • gradientKernelVector z) atTop := by
  have hB0' := hB0 hB
  have hm := tendsto_integral_cut_sub hL
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set ρ := ε / (2 * (B + 1)) with hρdef
  have hρ : 0 < ρ := by positivity
  have hlim : Tendsto (fun n : ℕ ↦ 2 * (∫ z in HalfSpace.upper 2, ‖cut f n z - f z‖) /
      (2 * Real.pi * ρ)) atTop (𝓝 0) := by
    simpa using (hm.const_mul 2).div_const (2 * Real.pi * ρ)
  filter_upwards [(tendsto_order.1 hlim).2 (ε / 2) (by positivity)] with n hn
  intro y
  rw [dist_eq_norm, norm_sub_rev]
  have hBρ : B * ρ < ε / 2 :=
    calc B * ρ = ε / 2 * (B / (B + 1)) := by rw [hρdef]; field_simp
      _ < ε / 2 :=
        mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by linarith)).2 (by linarith))
  linarith [norm_field_sub_le hf hB hL n y hρ]

/-- The gradient field of the potential is continuous. -/
private theorem continuous_field :
    Continuous fun x ↦ ∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z := by
  refine (tendstoUniformly_field hf hB hL).continuous (Frequently.of_forall fun n ↦ ?_)
  obtain ⟨hc, hcs, hodd⟩ := cut_data hf n
  have h := continuous_halfSpaceGreenPotentialGradient hc hcs
  simp only [funext (halfSpaceGreenPotentialGradient_eq_integral hc hcs), hodd] at h
  exact h

omit hf in
/-- The Green potentials of the cutoffs converge pointwise. -/
private theorem tendsto_halfSpaceGreenPotential_cut (y : ℝ^2) :
    Tendsto (fun n ↦ halfSpaceGreenPotential (cut f n) y) atTop
      (𝓝 (halfSpaceGreenPotential f y)) := by
  have hGI := hasIntegrableHalfSpaceGreenPotential_of_bounded hL.aestronglyMeasurable
    (fun z hz ↦ hB z (le_of_lt hz)) hL y
  unfold halfSpaceGreenPotential
  refine tendsto_integral_of_dominated_convergence (fun z ↦ ‖halfSpaceGreenFunction z y * f z‖)
    (fun n ↦ ?_) hGI.norm (fun n ↦ Eventually.of_forall fun z ↦ ?_)
    (Eventually.of_forall fun z ↦ ?_)
  · have e : (fun z ↦ halfSpaceGreenFunction z y * cut f n z) =
        fun z ↦ cutoff n z * (halfSpaceGreenFunction z y * f z) := by
      funext z; simp only [cut]; ring
    rw [e]
    exact (continuous_cutoff n).aestronglyMeasurable.restrict.mul hGI.aestronglyMeasurable
  · rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using abs_cut_le n z)
      (norm_nonneg _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
    rw [cut_eq_self (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))]

/-- **The Green potential of bounded integrable vorticity is `C¹`.** For `f` continuous on the
closed half-plane, bounded by `B` there and integrable on the open half-plane, the Green
potential is differentiable at every point of the plane with gradient the absolutely convergent
integral `∫ W(x - z) K(z) dz` of the odd extension `W` against the planar gradient kernel, which
is continuous in `x`. -/
theorem hasFDerivAt_halfSpaceGreenPotential_of_integrable (x : ℝ^2) :
    HasFDerivAt (halfSpaceGreenPotential f)
      (innerSL ℝ (∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z)) x := by
  have hgrad : ∀ (n : ℕ) y, HasFDerivAt (halfSpaceGreenPotential (cut f n))
      (innerSL ℝ (∫ z, oddHalfSpaceExtension (cut f n) (y - z) • gradientKernelVector z)) y := by
    intro n y
    obtain ⟨hc, hcs, hodd⟩ := cut_data hf n
    have h := hasFDerivAt_halfSpaceGreenPotential hc hcs y
    rwa [halfSpaceGreenPotentialGradient_eq_integral hc hcs, hodd,
      halfSpaceGreenPotential_congr fun z hz ↦
        evenReflection_of_nonneg (g := cut f n) (le_of_lt hz)] at h
  have hunif := ((innerSL ℝ : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ).uniformContinuous.comp_tendstoUniformly
    (tendstoUniformly_field hf hB hL)).tendstoUniformlyOn (s := univ)
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hunif (fun n y _ ↦ hgrad n y)
    (fun y _ ↦ tendsto_halfSpaceGreenPotential_cut hB hL y) (mem_univ x)

/-- The partial derivatives of the Green potential are the components of its gradient field. -/
theorem partialDeriv_halfSpaceGreenPotential_of_integrable (i : Fin 2) (x : ℝ^2) :
    (∂[i] (halfSpaceGreenPotential f)) x =
      (∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z) i := by
  change fderiv ℝ (halfSpaceGreenPotential f) x (EuclideanSpace.single i 1) = _
  rw [(hasFDerivAt_halfSpaceGreenPotential_of_integrable hf hB hL x).fderiv]
  simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, starRingEnd_apply,
    star_trivial, one_mul]

/-- The velocity of bounded integrable vorticity is the rotated gradient field:
`u(f)(x) = (-V(x)₁, V(x)₀)` with `V(x) = ∫ W(x - z) K(z) dz`. -/
theorem halfPlaneVelocity_eq_of_integrable (x : ℝ^2) :
    halfPlaneVelocity f x =
      !₂[-(∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z) 1,
        (∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z) 0] := by
  ext k
  fin_cases k <;>
    simp [halfPlaneVelocity, planarStreamVelocity,
      partialDeriv_halfSpaceGreenPotential_of_integrable hf hB hL]

/-- The velocity of bounded integrable vorticity is continuous on the plane. -/
theorem continuous_halfPlaneVelocity_of_integrable : Continuous (halfPlaneVelocity f) := by
  have h := continuous_field hf hB hL
  have he : halfPlaneVelocity f = fun x ↦
      !₂[-(∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z) 1,
        (∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z) 0] :=
    funext (halfPlaneVelocity_eq_of_integrable hf hB hL)
  rw [he]
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k ↦ ?_)
  fin_cases k
  · exact ((PiLp.continuous_apply 2 _ 1).comp h).neg
  · exact (PiLp.continuous_apply 2 _ 0).comp h

/-- **Size of the velocity**: `‖u(f)(x)‖ ≤ B + π⁻¹ ∫_{ℝ²₊} |f|` at every point of the plane. -/
theorem norm_halfPlaneVelocity_le_of_integrable (x : ℝ^2) :
    ‖halfPlaneVelocity f x‖ ≤ B + (∫ y in HalfSpace.upper 2, |f y|) / Real.pi := by
  have hB0' := hB0 hB
  obtain ⟨hW, hmass⟩ := integrable_oddHalfSpaceExtension_of_integrableOn hL
  have hWB : ∀ y, ‖oddHalfSpaceExtension f y‖ ≤ B :=
    norm_oddHalfSpaceExtension_le hB0' fun y hy ↦ hB y (le_of_lt hy)
  have hnorm : ‖halfPlaneVelocity f x‖ =
      ‖∫ z, oddHalfSpaceExtension f (x - z) • gradientKernelVector z‖ := by
    rw [halfPlaneVelocity_eq_of_integrable hf hB hL x, ← sq_eq_sq₀ (norm_nonneg _)
      (norm_nonneg _), EuclideanSpace.norm_sq_fin_two, EuclideanSpace.norm_sq_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [hnorm]
  refine (norm_integral_smul_gradientKernelVector_le_mass (hW.comp_sub_left x) one_pos
    (Eventually.of_forall fun z ↦ hWB _)).trans (le_of_eq ?_)
  rw [integral_sub_left_eq_self (fun z ↦ ‖oddHalfSpaceExtension f z‖) volume x, hmass]
  simp only [Real.norm_eq_abs]
  field_simp

omit hf hB hL in
/-- **Impermeability**: the normal velocity vanishes on the boundary, for every vorticity. The
potential vanishes on the boundary, so its tangential derivative is `0` wherever the potential
is differentiable, and `fderiv` is `0` elsewhere. -/
theorem halfPlaneVelocity_normal_eq_zero_of_integrable {x : ℝ^2} (hx : x 1 = 0) :
    halfPlaneVelocity f x 1 = 0 := by
  have hzero : PDE.Common.VanishesOnCoordinateHyperplane (1 : Fin 2)
      (halfSpaceGreenPotential f) := fun y hy ↦ halfSpaceGreenPotential_boundary f hy
  change (fun y ↦ halfPlaneVelocity f y 1) x = 0
  rw [halfPlaneVelocity_one]
  by_cases hd : DifferentiableAt ℝ (halfSpaceGreenPotential f) x
  · exact hzero.partialDeriv_eq_zero_of_ne (by decide) hx hd
  · simp [PDE.partialDeriv, fderiv_zero_of_not_differentiableAt hd]

end Integrable

/-! ### Gradient formulas of vorticity vanishing near a point -/

/-- A singular-kernel integral of a density vanishing on `B(y, r)` is at most `A ‖F‖₁/r²` over
any set. -/
private theorem abs_setIntegral_mul_le_of_eq_zero {K : ℝ^2 → ℝ} {A : ℝ}
    (hK : IsSingularKernel K A) {F : ℝ^2 → ℝ} (hF : Integrable F) {y : ℝ^2} {r : ℝ}
    (hr : 0 < r) (hz : ∀ z, dist z y < r → F z = 0) (S : Set (ℝ^2)) :
    |∫ z in S, K (y - z) * F z| ≤ A / r ^ 2 * ∫ z, |F z| := by
  have hA := hK.nonneg
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((hF.abs.const_mul (A / r ^ 2)).integrableOn)
    (Eventually.of_forall fun z ↦ ?_)).trans ?_
  · by_cases hzy : dist z y < r
    · rw [hz z hzy, mul_zero, norm_zero]; positivity
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right (hK.abs_le_of_le hr ?_) (abs_nonneg _)
      rw [not_lt, dist_eq_norm, norm_sub_rev] at hzy
      exact hzy
  · exact setIntegral_le_integral (hF.abs.const_mul _)
      (Eventually.of_forall fun z ↦ by positivity) |>.trans (le_of_eq (integral_const_mul _ _))

/-- **Gradient formulas of vorticity vanishing near a point.** If the even extension of `h`
vanishes on `B(y, r)`, `y` in the open half-plane, then the principal values are ordinary
integrals and `|∂ᵢuₖ(h)(y)| ≤ 15/(π r²) ‖E h‖₁` for the gradient formulas. -/
theorem abs_halfPlaneVelocityGradient_le_of_eq_zero {h : ℝ^2 → ℝ} {M α r : ℝ} (hα : 0 < α)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |h y - h z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection h)) {y : ℝ^2} (hy : 0 < y 1) (hr : 0 < r)
    (hz : ∀ z, dist z y < r → evenReflection h z = 0) (i k : Fin 2) :
    |halfPlaneVelocityGradient h i k y| ≤
      15 / (Real.pi * r ^ 2) * ∫ z, |evenReflection h z| := by
  obtain ⟨j, a, b, ha, hb, hrep⟩ := halfPlaneVelocityGradient_eq_combination i k
  have hK := isSingularKernel_hessianKernel 0 j
  have hFM := abs_evenReflection_sub_le hα.le hM
  have hyy : evenReflection h y = 0 := hz y (by simpa using hr)
  have hhy : h y = 0 := by rwa [evenReflection_of_nonneg hy.le] at hyy
  set F := evenReflection h
  have hsing : singularIntegral (hessianKernel 0 j) F y =
      ∫ z in (ball y r)ᶜ, hessianKernel 0 j (y - z) * F z := by
    rw [hK.singularIntegral_eq hα hE hFM y hr, setIntegral_eq_zero_of_forall_eq_zero
      fun z hz' ↦ by rw [hz z hz', hyy, sub_zero, mul_zero], zero_add]
  have h1 := abs_setIntegral_mul_le_of_eq_zero hK hE hr hz (ball y r)ᶜ
  have h2 := abs_setIntegral_mul_le_of_eq_zero hK hE hr hz {z : ℝ^2 | z 1 < 0}
  have hH : |halfPlaneSingularIntegral (hessianKernel 0 j) h y| ≤
      3 * (5 / r ^ 2 * ∫ z, |F z|) := by
    unfold halfPlaneSingularIntegral
    rw [hsing]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_two]
    linarith
  rw [hrep h y, hhy, mul_zero, add_zero, abs_mul]
  have hpi := Real.pi_pos
  have hL0 : 0 ≤ ∫ z, |F z| := integral_nonneg fun z ↦ abs_nonneg _
  calc |a| * |halfPlaneSingularIntegral (hessianKernel 0 j) h y|
      ≤ 1 / Real.pi * (3 * (5 / r ^ 2 * ∫ z, |F z|)) := by gcongr
    _ = 15 / (Real.pi * r ^ 2) * ∫ z, |F z| := by field_simp; ring

/-! ### The derivative of the velocity -/

section Derivative

variable (hf : ContinuousOn f H̄) (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
  (hL : IntegrableOn f (HalfSpace.upper 2)) (hα : 0 < α) (hα1 : α ≤ 1)
  (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
include hf hB hL hα hα1 hM

omit hf hB hL hα hα1 hM in
/-- `(∑ⱼ cⱼ eⱼ*)(eᵢ) = cᵢ`. -/
private theorem sum_smul_proj_apply_single (c : Fin 2 → ℝ) (i : Fin 2) :
    (∑ j : Fin 2, c j • (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ)) (EuclideanSpace.single i 1) =
      c i := by
  fin_cases i <;> simp [Fin.sum_univ_two]

omit hf hB hL hα hα1 hM in
/-- For `g` integrable on the open half-plane with a measurable even extension, the even extension
is integrable on the plane and `∫ |E g| = 2 ∫_{ℝ²₊} |g|`. -/
private theorem integrable_evenReflection_of_integrableOn {g : ℝ^2 → ℝ}
    (hg : IntegrableOn g (HalfSpace.upper 2)) (hgm : AEStronglyMeasurable
      (evenReflection g)) :
    Integrable (evenReflection g) ∧
      ∫ z, |evenReflection g z| = 2 * ∫ z in HalfSpace.upper 2, ‖g z‖ := by
  obtain ⟨hW, hmass⟩ := integrable_oddHalfSpaceExtension_of_integrableOn hg
  have hae := abs_oddHalfSpaceExtension_ae_eq g
  refine ⟨hW.norm.mono' hgm ?_, ?_⟩
  · filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hz]
  · rw [← hmass]
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, hz]

/-- **The derivative of the velocity for bounded integrable Hölder vorticity.** For `f`
continuous on the closed half-plane, bounded by `B`, integrable on the open half-plane and
`α`-Hölder on the closed half-plane (`0 < α ≤ 1`), each velocity component is differentiable at
every point of the open half-plane, with partial derivatives the principal-value formulas
`halfPlaneVelocityGradient`. -/
theorem hasFDerivAt_halfPlaneVelocity_of_integrable (k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    HasFDerivAt (fun y ↦ halfPlaneVelocity f y k)
      (∑ i : Fin 2, halfPlaneVelocityGradient f i k x • (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ))
      x := by
  have hB0' := hB0 hB
  have hx1 : (0 : ℝ) < x 1 := hx
  set r := x 1 / 2 with hrdef
  have hr0 : 0 < r := by positivity
  have hs : ball x r ⊆ HalfSpace.upper 2 := fun y hy ↦ by
    have h1 := EuclideanSpace.abs_apply_le_norm (y - x) 1
    rw [mem_ball, dist_eq_norm] at hy
    rw [PiLp.sub_apply] at h1
    change (0 : ℝ) < y 1
    linarith [neg_abs_le (y 1 - x 1)]
  -- the even extensions of the cutoffs
  have hgM : ∀ (n : ℕ) (y z : ℝ^2), 0 ≤ y 1 → 0 ≤ z 1 →
      |evenReflection (cut f n) y - evenReflection (cut f n) z| ≤
        (M + B) * ‖y - z‖ ^ α := fun n y z hy hz ↦ by
    rw [evenReflection_of_nonneg hy, evenReflection_of_nonneg hz]
    exact abs_cut_sub_le hB hM hα.le hα1 n hy hz
  have hderiv : ∀ (n : ℕ), ∀ y ∈ ball x r, HasFDerivAt (fun y ↦ halfPlaneVelocity (cut f n) y k)
      (∑ i : Fin 2, halfPlaneVelocityGradient (evenReflection (cut f n)) i k y •
        (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ)) y := fun n y hy ↦ by
    have h := hasFDerivAt_halfPlaneVelocity (cut_data hf n).1 (cut_data hf n).2.1 hα hα1
      (fun y z hy hz ↦ hgM n y z hy hz) k (hs hy)
    rwa [halfPlaneVelocity_evenReflection] at h
  -- the velocities converge pointwise
  have hpt : ∀ y, Tendsto (fun n ↦ halfPlaneVelocity (cut f n) y k) atTop
      (𝓝 (halfPlaneVelocity f y k)) := by
    intro y
    have hcut : ∀ n, halfPlaneVelocity (cut f n) y = !₂[
        -(∫ z, oddHalfSpaceExtension (cut f n) (y - z) • gradientKernelVector z) 1,
        (∫ z, oddHalfSpaceExtension (cut f n) (y - z) • gradientKernelVector z) 0] := fun n ↦
      halfPlaneVelocity_eq_of_integrable (continuousOn_cut hf n)
        (fun y hy ↦ (abs_cut_le n y).trans (hB y hy)) (integrableOn_cut hL n) y
    have hV := (tendstoUniformly_field hf hB hL).tendsto_at y
    rw [halfPlaneVelocity_eq_of_integrable hf hB hL y]
    simp only [hcut]
    fin_cases k
    · simpa [Function.comp_def] using
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).tendsto _ |>.comp hV).neg
    · simpa [Function.comp_def] using
        (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).tendsto _ |>.comp hV
  -- the gradient formulas converge uniformly on the ball
  have hE : Integrable (evenReflection f) :=
    (integrable_evenReflection_of_integrableOn hL
      (continuous_evenReflection hf).aestronglyMeasurable).1
  have hgap : ∀ (n : ℕ), 2 * ‖x‖ + 1 ≤ n → ∀ y ∈ ball x r, ∀ i : Fin 2,
      |halfPlaneVelocityGradient (evenReflection (cut f n)) i k y -
        halfPlaneVelocityGradient f i k y| ≤
        15 / Real.pi * (2 * ∫ z in HalfSpace.upper 2, ‖cut f n z - f z‖) := by
    intro n hn y hy i
    have hy1 := hs hy
    obtain ⟨hc, hcs, -⟩ := cut_data hf n
    have hEn := integrable_evenReflection hc hcs
    rw [← halfPlaneVelocityGradient_sub hα (fun y z hy hz ↦ hgM n y z hy hz) hM hEn hE i k hy1]
    have hEh : evenReflection (evenReflection (cut f n) - f) =
        evenReflection (cut f n - f) := by
      funext z
      change evenReflection (evenReflection (cut f n)) z -
          evenReflection f z = evenReflection (cut f n) z -
            evenReflection f z
      rw [evenReflection_evenReflection]
    have hmeas : AEStronglyMeasurable (evenReflection (cut f n - f)) :=
      (continuous_evenReflection
        ((continuousOn_cut hf n).sub hf)).aestronglyMeasurable
    obtain ⟨hEd, hmass⟩ := integrable_evenReflection_of_integrableOn
      ((integrableOn_cut hL n).sub hL) hmeas
    have hzero : ∀ z, dist z y < 1 →
        evenReflection (evenReflection (cut f n) - f) z = 0 := by
      intro z hz
      rw [hEh]
      have hzn : ‖z‖ ≤ n := by
        rw [mem_ball, dist_eq_norm] at hy
        rw [dist_eq_norm] at hz
        have hxr : x 1 ≤ ‖x‖ := (le_abs_self _).trans (EuclideanSpace.abs_apply_le_norm x 1)
        linarith [norm_le_norm_add_norm_sub' z y, norm_le_norm_add_norm_sub' y x]
      change cut f n (halfPlaneFold z) - f (halfPlaneFold z) = 0
      rw [cut_eq_self (by rw [norm_halfPlaneFold]; exact hzn), sub_self]
    have hHM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        |(evenReflection (cut f n) - f) y - (evenReflection (cut f n) - f) z| ≤
          (M + B + M) * ‖y - z‖ ^ α := fun y z hy hz ↦ by
      rw [Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm]
      linarith [abs_sub (evenReflection (cut f n) y - evenReflection (cut f n) z) (f y - f z),
        hgM n y z hy hz, hM y z hy hz]
    have hb := abs_halfPlaneVelocityGradient_le_of_eq_zero hα hHM (hEh ▸ hEd) hy1 one_pos hzero i k
    rw [hEh, hmass] at hb
    simpa using hb
  have hunif : TendstoUniformlyOn
      (fun (n : ℕ) y ↦ ∑ i : Fin 2, halfPlaneVelocityGradient (evenReflection (cut f n))
        i k y • (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ))
      (fun y ↦ ∑ i : Fin 2, halfPlaneVelocityGradient f i k y •
        (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ)) atTop (ball x r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hm := tendsto_integral_cut_sub hL
    have hlim : Tendsto (fun n : ℕ ↦ 2 * (15 / Real.pi *
        (2 * ∫ z in HalfSpace.upper 2, ‖cut f n z - f z‖))) atTop (𝓝 0) := by
      simpa using ((hm.const_mul 2).const_mul (15 / Real.pi)).const_mul 2
    filter_upwards [(tendsto_order.1 hlim).2 ε hε, eventually_ge_atTop ⌈2 * ‖x‖ + 1⌉₊]
      with n hn hN
    intro y hy
    rw [dist_eq_norm]
    refine (ContinuousLinearMap.norm_le_sum_norm_apply_single _).trans_lt (lt_of_le_of_lt ?_ hn)
    have hN' : 2 * ‖x‖ + 1 ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    simp only [sub_apply, sum_smul_proj_apply_single]
    rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [(abs_sub_comm _ _).trans_le (hgap n hN' y hy 0),
      (abs_sub_comm _ _).trans_le (hgap n hN' y hy 1)]
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hunif hderiv (fun y _ ↦ hpt y)
    (mem_ball_self hr0)

/-- The partial derivatives of the velocity are the principal-value formulas. -/
theorem partialDeriv_halfPlaneVelocity_of_integrable (i k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    (∂[i] (fun y ↦ halfPlaneVelocity f y k)) x = halfPlaneVelocityGradient f i k x := by
  change fderiv ℝ (fun y ↦ halfPlaneVelocity f y k) x (EuclideanSpace.single i 1) = _
  rw [(hasFDerivAt_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM k hx).fderiv,
    sum_smul_proj_apply_single (fun j ↦ halfPlaneVelocityGradient f j k x)]

/-- The velocity is differentiable at every point of the open half-plane. -/
theorem differentiableAt_halfPlaneVelocity_of_integrable {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    DifferentiableAt ℝ (halfPlaneVelocity f) x :=
  (differentiableAt_piLp 2).2 fun k ↦
    (hasFDerivAt_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM k hx).differentiableAt

/-- The entries of the derivative of the velocity are the gradient formulas. -/
private theorem fderiv_apply_single {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) (i k : Fin 2) :
    fderiv ℝ (halfPlaneVelocity f) x (EuclideanSpace.single i 1) k =
      halfPlaneVelocityGradient f i k x := by
  have hd := differentiableAt_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM hx
  have h := ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [← partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM i k hx]
  change _ = fderiv ℝ ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ) ∘ halfPlaneVelocity f) x
    (EuclideanSpace.single i 1)
  rw [h]
  rfl

omit hB hα hα1 hM in
/-- The `L¹` norm of the even extension is twice the mass. -/
private theorem integral_abs_evenReflection_of_integrable :
    ∫ z, |evenReflection f z| = 2 * ∫ z in HalfSpace.upper 2, |f z| := by
  have h := (integrable_evenReflection_of_integrableOn hL
    (continuous_evenReflection hf).aestronglyMeasurable).2
  simpa only [Real.norm_eq_abs] using h

/-- **Size of the velocity gradient**: with `L = ∫_{ℝ²₊} |f|`,
`|∂ᵢuₖ(x)| ≤ 50M/α + 8B + 10L` in the open half-plane. -/
theorem abs_partialDeriv_halfPlaneVelocity_le_of_integrable (i k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity f y k)) x| ≤
      50 * M / α + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |f y| := by
  rw [partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM i k hx]
  have h := abs_halfPlaneVelocityGradient_le hα hα1 hM
    (integrable_evenReflection_of_integrableOn hL
      (continuous_evenReflection hf).aestronglyMeasurable).1 hB i k hx
  rw [integral_abs_evenReflection_of_integrable hf hL] at h
  linarith

/-- **Kato-type bound of the velocity gradient**: with `L = ∫_{ℝ²₊} |f|`,
`|∂ᵢuₖ(x)| ≤ (50/α)(1 + B log(2 + M)) + 8B + 10L` in the open half-plane. -/
theorem abs_partialDeriv_halfPlaneVelocity_le_log_of_integrable (i k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity f y k)) x| ≤
      50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |f y| := by
  rw [partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM i k hx]
  have h := abs_halfPlaneVelocityGradient_le_log hα hα1 hM
    (integrable_evenReflection_of_integrableOn hL
      (continuous_evenReflection hf).aestronglyMeasurable).1 hB i k hx
  rw [integral_abs_evenReflection_of_integrable hf hL] at h
  linarith

/-- **Hölder estimate of the velocity gradient**: for `0 < α < 1` and `x, x'` in the open
half-plane, `|∂ᵢuₖ(x) - ∂ᵢuₖ(x')| ≤ 211/(α(1-α)) · M |x - x'|^α`. -/
theorem abs_partialDeriv_halfPlaneVelocity_sub_le_of_integrable (hα1' : α < 1) (i k : Fin 2)
    {x x' : ℝ^2} (hx : x ∈ HalfSpace.upper 2) (hx' : x' ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity f y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity f y k)) x'| ≤
      211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  rw [partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM i k hx,
    partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM i k hx']
  exact abs_halfPlaneVelocityGradient_sub_le hα hα1' hM
    (integrable_evenReflection_of_integrableOn hL
      (continuous_evenReflection hf).aestronglyMeasurable).1 i k hx hx'

/-- The derivative of the velocity is Hölder on the open half-plane with constant
`844/(α(1-α)) · M`. -/
private theorem norm_fderiv_sub_le (hα1' : α < 1) {x x' : ℝ^2} (hx : x ∈ HalfSpace.upper 2)
    (hx' : x' ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (halfPlaneVelocity f) x - fderiv ℝ (halfPlaneVelocity f) x'‖ ≤
      844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  refine (norm_le_sum_abs_apply _).trans ?_
  have h := fun i k ↦ abs_partialDeriv_halfPlaneVelocity_sub_le_of_integrable hf hB hL hα hα1 hM
    hα1' i k hx hx'
  simp only [sub_apply, PiLp.sub_apply,
    fderiv_apply_single hf hB hL hα hα1 hM hx, fderiv_apply_single hf hB hL hα hα1 hM hx',
    ← partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM _ _ hx,
    ← partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM _ _ hx', Fin.sum_univ_two]
  have e : 844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α =
      4 * (211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α) := by ring
  linarith [h 0 0, h 0 1, h 1 0, h 1 1]

/-- **The velocity is differentiable within the closed half-plane** at each of its points, for
`0 < α < 1`. -/
theorem differentiableOn_halfPlaneVelocity_of_integrable (hα1' : α < 1) :
    DifferentiableOn ℝ (halfPlaneVelocity f) H̄ := fun _ hx ↦
  (PDE.Analysis.hasFDerivWithinAt_closedUpper_of_holder hα
    (continuous_halfPlaneVelocity_of_integrable hf hB hL).continuousOn
    (fun _ hy ↦ (differentiableAt_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM
      hy).differentiableWithinAt)
    (fun _ hy _ hy' ↦ norm_fderiv_sub_le hf hB hL hα hα1 hM hα1' hy hy') hx).1
      |>.differentiableWithinAt

/-- **Hölder continuity of the derivative up to the boundary**, for `0 < α < 1`: for `x, x'` in
the closed half-plane, `‖D^H u(x) - D^H u(x')‖ ≤ 844/(α(1-α)) · M |x - x'|^α`. -/
theorem dist_fderivWithin_halfPlaneVelocity_le_of_integrable (hα1' : α < 1) {x x' : ℝ^2}
    (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    dist (fderivWithin ℝ (halfPlaneVelocity f) H̄ x)
        (fderivWithin ℝ (halfPlaneVelocity f) H̄ x') ≤
      844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  rw [dist_eq_norm]
  exact PDE.Analysis.norm_fderivWithin_closedUpper_sub_le_of_holder hα
    (continuous_halfPlaneVelocity_of_integrable hf hB hL).continuousOn
    (fun _ hy ↦ (differentiableAt_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM
      hy).differentiableWithinAt)
    (fun _ hy _ hy' ↦ norm_fderiv_sub_le hf hB hL hα hα1 hM hα1' hy hy') hx hx'

/-- **The velocity is Lipschitz on the closed half-plane**, for `0 < α < 1`, with constant
`4((50/α)(1 + B log(2 + M)) + 8B + 10L)`. -/
theorem lipschitzOnWith_halfPlaneVelocity_of_integrable (hα1' : α < 1) :
    LipschitzOnWith (Real.toNNReal (4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
      10 * ∫ y in HalfSpace.upper 2, |f y|))) (halfPlaneVelocity f) H̄ := by
  set Q := 50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |f y|
  have hcont := (continuous_halfPlaneVelocity_of_integrable hf hB hL).continuousOn (s := H̄)
  have hdH : DifferentiableOn ℝ (halfPlaneVelocity f) (HalfSpace.upper 2) := fun _ hy ↦
    (differentiableAt_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM hy).differentiableWithinAt
  have hC := fun (y : ℝ^2) (hy : y ∈ HalfSpace.upper 2) (y' : ℝ^2)
    (hy' : y' ∈ HalfSpace.upper 2) ↦ norm_fderiv_sub_le hf hB hL hα hα1 hM hα1' hy hy'
  -- interior size of the derivative
  have hsize : ∀ y ∈ HalfSpace.upper 2, ‖fderiv ℝ (halfPlaneVelocity f) y‖ ≤ 4 * Q := by
    intro y hy
    refine (norm_le_sum_abs_apply _).trans ?_
    simp only [fderiv_apply_single hf hB hL hα hα1 hM hy,
      ← partialDeriv_halfPlaneVelocity_of_integrable hf hB hL hα hα1 hM _ _ hy, Fin.sum_univ_two]
    have h := fun i k ↦ abs_partialDeriv_halfPlaneVelocity_le_log_of_integrable hf hB hL hα hα1
      hM i k hy
    linarith [h 0 0, h 0 1, h 1 0, h 1 1]
  -- the size passes to the boundary
  have hsizeH : ∀ x ∈ H̄, ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤ 4 * Q := by
    intro x hx
    have hcl : x ∈ closure (HalfSpace.upper 2) := by rw [HalfSpace.closure_upper_two]; exact hx
    have : (𝓝[HalfSpace.upper 2] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    exact le_of_tendsto
      (PDE.Analysis.hasFDerivWithinAt_closedUpper_of_holder hα hcont hdH hC hx).2.norm
      (by filter_upwards [self_mem_nhdsWithin] with y hy using hsize y hy)
  have hQ : 0 ≤ 4 * Q := (norm_nonneg _).trans (hsizeH 0 (show (0 : ℝ) ≤ (0 : ℝ^2) 1 by simp))
  have hconv : Convex ℝ H̄ :=
    convex_halfSpace_ge (f := fun y : ℝ^2 ↦ y 1) ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩ 0
  refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' ↦ ?_
  rw [Real.coe_toNNReal _ hQ, dist_eq_norm, dist_eq_norm]
  exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy ↦ (PDE.Analysis.hasFDerivWithinAt_closedUpper_of_holder hα hcont hdH hC hy).1)
    hsizeH hx' hx

end Derivative

end IncompressibleFlow

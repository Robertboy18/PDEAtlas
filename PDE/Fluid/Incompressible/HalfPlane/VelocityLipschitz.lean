/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityTangential
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The half-plane velocity field on the closed half-plane

Vector forms of the componentwise first-order estimates of the velocity, for a vorticity given on
the closed upper half-plane `H̄ = {x₁ ≥ 0}`: `f` continuous on `H̄`, vanishing there outside a disc
and `α`-Hölder on `H̄` with constant `M` (`0 < α < 1`), `|f| ≤ B` on `H̄` and `L = ∫_{ℝ²₊} |f|`,
with velocity `u = halfPlaneVelocity f`.

The stream function `φ = halfSpaceGreenPotential f` satisfies `u = (-∂₁^H φ, ∂₀^H φ)` on `H̄` with
derivatives within `H̄` (`PDE.partialDerivWithin`), and its second derivatives within `H̄` are
those of `∓u` (`partialDerivWithin_partialDerivWithin_one_halfSpaceGreenPotential_eq` and its
companion for `∂₀^H φ`).

Here `D^H` is the derivative within `H̄`; at a boundary point where `f` does not vanish the
velocity is not differentiable in the ambient sense.

## Main results

* `differentiableOn_halfPlaneVelocity`: `u` is differentiable within `H̄` at every point of `H̄`.
* `dist_fderivWithin_halfPlaneVelocity_le`: `‖D^H u(x) - D^H u(x')‖ ≤ 844/(α(1-α)) · M |x - x'|^α`.
* `norm_fderivWithin_halfPlaneVelocity_le_holder`: `‖D^H u(x)‖ ≤ 4(50M/α + 8B + 10L)`.
* `norm_fderivWithin_halfPlaneVelocity_le_kato`:
  `‖D^H u(x)‖ ≤ 4((50/α)(1 + B log(2 + M)) + 8B + 10L)`, and its homogeneous form
  `norm_fderivWithin_halfPlaneVelocity_le_kato_homogeneous` (`0 < B`):
  `‖D^H u(x)‖ ≤ 4((50B/α)(1 + log(2 + M/B)) + 8B + 10L)`, which applies to differences.
* `lipschitzOnWith_halfPlaneVelocity`: `u` is Lipschitz on `H̄` with constant
  `4((50/α)(1 + B log(2 + M)) + 8B + 10L)`.
* `halfPlaneVelocity_normal_eq_zero`: the normal velocity vanishes on the boundary, so `u` is
  tangent to `H̄` (the impermeability condition).
* `norm_halfPlaneVelocity_le_of_continuousOn`: `‖u(x)‖ ≤ B + L/π` on the whole plane, and the
  velocity is linear (`halfPlaneVelocity_sub_of_continuousOn`), so every bound applies to
  differences.
* `contDiffOn_succ_halfSpaceGreenPotential`: the stream is one order more regular than the
  velocity within `H̄`.

## How it works

The velocity only depends on `f` in the open half-plane, so we replace `f` by its even reflection,
which is continuous, compactly supported and has the same Hölder constant on `H̄`
(`halfPlaneVelocity_evenReflection`), and apply the componentwise theorems to it. The derivative of
`u` within `H̄` is assembled from those of its two components
(`hasFDerivWithinAt_halfPlaneVelocity`), and its norm is at most the sum of theirs, so the Hölder
constant `422/(α(1-α)) · M` of each component (`norm_fderivWithin_halfPlaneVelocity_sub_le`)
doubles. For the size bounds, the derivative within `H̄` of a component at a boundary point is the
limit of interior derivatives, so the interior bounds `abs_partialDeriv_halfPlaneVelocity_le` and
`abs_partialDeriv_halfPlaneVelocity_le_log` pass to `H̄` with the factor 4
(`norm_fderivWithin_halfPlaneVelocity_le_of_partialDeriv`). The homogeneous Kato form applies the
Kato bound to `B⁻¹ f`, and the Lipschitz bound adds the componentwise bounds
`abs_halfPlaneVelocity_sub_le_mul`. For the stream statements, `φ` is also the potential of the even
reflection and hence `C¹` on the plane (`contDiff_one_halfSpaceGreenPotential`), so its derivative
within `H̄` is the rotated velocity (`fderivWithin_halfSpaceGreenPotential_eq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open GreenFunction PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The linear map with prescribed component functionals. -/
private def assemble (L₀ L₁ : ℝ^2 →L[ℝ] ℝ) : ℝ^2 →L[ℝ] ℝ^2 :=
  L₀.smulRight (EuclideanSpace.single 0 1) + L₁.smulRight (EuclideanSpace.single 1 1)

/-- The `k`-th component of `assemble L₀ L₁` is `Lₖ`. -/
private theorem proj_comp_assemble (L₀ L₁ : ℝ^2 →L[ℝ] ℝ) (k : Fin 2) :
    PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) k ∘L assemble L₀ L₁ = if k = 0 then L₀ else L₁ := by
  ext1 v
  fin_cases k <;> simp [assemble]

/-- `‖assemble L₀ L₁‖ ≤ ‖L₀‖ + ‖L₁‖`. -/
private theorem norm_assemble_le (L₀ L₁ : ℝ^2 →L[ℝ] ℝ) : ‖assemble L₀ L₁‖ ≤ ‖L₀‖ + ‖L₁‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  calc ‖assemble L₀ L₁ v‖ ≤ ‖L₀ v‖ + ‖L₁ v‖ := by
        change ‖L₀ v • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
          L₁ v • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ ≤ _
        refine (norm_add_le _ _).trans ?_
        simp [norm_smul]
    _ ≤ ‖L₀‖ * ‖v‖ + ‖L₁‖ * ‖v‖ := add_le_add (L₀.le_opNorm v) (L₁.le_opNorm v)
    _ = (‖L₀‖ + ‖L₁‖) * ‖v‖ := by ring

variable {f : ℝ^2 → ℝ} {R M α B : ℝ}

/-- The size of the velocity, for data given on the closed half-plane: with `|f| ≤ B` on the
open half-plane, `‖u(f)(x)‖ ≤ B + π⁻¹ ∫_{ℝ²₊} |f|` at every point of the plane. -/
theorem norm_halfPlaneVelocity_le_of_continuousOn (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hB : ∀ y ∈ HalfSpace.upper 2, |f y| ≤ B)
    (x : ℝ^2) :
    ‖halfPlaneVelocity f x‖ ≤ B + (∫ y in HalfSpace.upper 2, |f y|) / Real.pi := by
  have hE := norm_halfPlaneVelocity_le (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR)
    (fun y hy ↦ by rw [evenReflection_of_nonneg (le_of_lt hy)]; exact hB y hy) x
  rwa [halfPlaneVelocity_evenReflection,
    setIntegral_congr_fun (HalfSpace.measurableSet_upper (n := 2))
      (fun y hy ↦ by rw [evenReflection_of_nonneg (le_of_lt hy)])] at hE

/-- **Linearity**, for data given on the closed half-plane. -/
theorem halfPlaneVelocity_sub_of_continuousOn {g : ℝ^2 → ℝ} {R' : ℝ} (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hg : ContinuousOn g H̄)
    (hR' : ∀ y : ℝ^2, 0 ≤ y 1 → R' < ‖y‖ → g y = 0) :
    halfPlaneVelocity (f - g) = halfPlaneVelocity f - halfPlaneVelocity g := by
  have hE : evenReflection (f - g) =
      evenReflection f - evenReflection g := rfl
  rw [← halfPlaneVelocity_evenReflection (f - g), hE,
    ← halfPlaneVelocity_evenReflection f, ← halfPlaneVelocity_evenReflection g]
  funext x
  ext k
  exact halfPlaneVelocity_sub (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR)
    (continuous_evenReflection hg)
    (hasCompactSupport_evenReflection_of_eq_zero hR') x k

/-- **Impermeability.** For `f` continuous on the closed half-plane and vanishing there outside a
disc, the normal velocity vanishes on the boundary. -/
theorem halfPlaneVelocity_normal_eq_zero (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : x 1 = 0) :
    halfPlaneVelocity f x 1 = 0 := by
  rw [← halfPlaneVelocity_evenReflection f]
  change (fun y ↦ halfPlaneVelocity (evenReflection f) y 1) x = 0
  rw [halfPlaneVelocity_one]
  exact partialDeriv_halfSpaceGreenPotential_boundary
    (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR) hx

/-- On the open half-plane the even extension has the same integral of the absolute value as
`f`. -/
private theorem setIntegral_abs_evenReflection (f : ℝ^2 → ℝ) :
    ∫ y in HalfSpace.upper 2, |evenReflection f y| = ∫ y in HalfSpace.upper 2, |f y| :=
  setIntegral_congr_fun (HalfSpace.measurableSet_upper (n := 2))
    fun y hy ↦ by rw [evenReflection_of_nonneg (le_of_lt hy)]

section Holder

variable (hf : ContinuousOn f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
  (hα : 0 < α) (hα1 : α < 1)
  (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
include hf hR hα hα1 hM

omit hα hα1 in
/-- The even extension carries the hypotheses of the componentwise estimates up to the
boundary. -/
private theorem evenData :
    Continuous (evenReflection f) ∧ HasCompactSupport (evenReflection f) ∧
      ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        |evenReflection f y - evenReflection f z| ≤ M * ‖y - z‖ ^ α :=
  ⟨continuous_evenReflection hf,
    hasCompactSupport_evenReflection_of_eq_zero hR, fun y z hy hz ↦ by
      rw [evenReflection_of_nonneg hy, evenReflection_of_nonneg hz]
      exact hM y z hy hz⟩

/-- The vector derivative within the closed half-plane, assembled from the components. -/
private theorem hasFDerivWithinAt_assemble {x : ℝ^2} (hx : 0 ≤ x 1) :
    HasFDerivWithinAt (halfPlaneVelocity f)
      (assemble (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 0) H̄ x)
        (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 1) H̄ x)) H̄ x := by
  obtain ⟨hEc, hEcs, hEM⟩ := evenData hf hR hM
  rw [hasFDerivWithinAt_piLp]
  intro k
  rw [proj_comp_assemble]
  have h := (hasFDerivWithinAt_halfPlaneVelocity hEc hEcs hα hα1 hEM k hx).1
  rw [halfPlaneVelocity_evenReflection] at h
  fin_cases k <;> simpa using h

/-- **The velocity is differentiable within the closed half-plane** at each of its points. -/
theorem differentiableOn_halfPlaneVelocity : DifferentiableOn ℝ (halfPlaneVelocity f) H̄ :=
  fun _ hx ↦ (hasFDerivWithinAt_assemble hf hR hα hα1 hM hx).differentiableWithinAt

/-- At points of `H̄` the derivative within `H̄` of the velocity is assembled from the derivatives
within `H̄` of its two components. -/
private theorem fderivWithin_eq_assemble {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (halfPlaneVelocity f) H̄ x =
      assemble (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 0) H̄ x)
        (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 1) H̄ x) :=
  (hasFDerivWithinAt_assemble hf hR hα hα1 hM hx).fderivWithin (uniqueDiffOn_closedUpper x hx)

/-- **Hölder continuity of the derivative up to the boundary.** For `x, x'` in the closed
half-plane, `‖D^H u(x) - D^H u(x')‖ ≤ 844/(α(1-α)) · M |x - x'|^α`. -/
theorem dist_fderivWithin_halfPlaneVelocity_le {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    dist (fderivWithin ℝ (halfPlaneVelocity f) H̄ x)
        (fderivWithin ℝ (halfPlaneVelocity f) H̄ x') ≤
      844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  obtain ⟨hEc, hEcs, hEM⟩ := evenData hf hR hM
  have hk := fun k : Fin 2 ↦ norm_fderivWithin_halfPlaneVelocity_sub_le hEc hEcs hα hα1 hEM k hx hx'
  simp only [halfPlaneVelocity_evenReflection] at hk
  rw [dist_eq_norm, fderivWithin_eq_assemble hf hR hα hα1 hM hx,
    fderivWithin_eq_assemble hf hR hα hα1 hM hx']
  have hsub : assemble (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 0) H̄ x)
        (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 1) H̄ x) -
      assemble (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 0) H̄ x')
        (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 1) H̄ x') =
      assemble (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 0) H̄ x -
          fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 0) H̄ x')
        (fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 1) H̄ x -
          fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y 1) H̄ x') := by
    ext1 v; ext i; fin_cases i <;> simp [assemble]
  rw [hsub]
  refine (norm_assemble_le _ _).trans ?_
  have := add_le_add (hk 0) (hk 1)
  have e : 844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α =
      422 / (α * (1 - α)) * M * ‖x - x'‖ ^ α + 422 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by ring
  linarith

/-- The derivatives of a velocity component within the closed half-plane are limits of interior
derivatives, so interior bounds of the two partial derivatives bound them. -/
private theorem norm_fderivWithin_apply_le {c : ℝ}
    (hc : ∀ y ∈ HalfSpace.upper 2, ∀ i k : Fin 2,
      |(∂[i] (fun z ↦ halfPlaneVelocity f z k)) y| ≤ c) (k : Fin 2) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (fun y ↦ halfPlaneVelocity f y k) H̄ x‖ ≤ 2 * c := by
  obtain ⟨hEc, hEcs, hEM⟩ := evenData hf hR hM
  have h := (hasFDerivWithinAt_halfPlaneVelocity hEc hEcs hα hα1 hEM k hx).2
  simp only [halfPlaneVelocity_evenReflection] at h
  have hcl : x ∈ closure (HalfSpace.upper 2) := by rw [HalfSpace.closure_upper_two]; exact hx
  have : (𝓝[HalfSpace.upper 2] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  refine le_of_tendsto h.norm ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  refine (ContinuousLinearMap.norm_le_sum_norm_apply_single _).trans ?_
  have h0 := hc y hy 0 k
  have h1 := hc y hy 1 k
  rw [Fin.sum_univ_two]
  change |(∂[(0 : Fin 2)] (fun z ↦ halfPlaneVelocity f z k)) y| +
    |(∂[(1 : Fin 2)] (fun z ↦ halfPlaneVelocity f z k)) y| ≤ 2 * c
  linarith

/-- **Interior bounds give bounds up to the boundary.** If `c` bounds the partial derivatives of
the velocity components at every point of the open half-plane, then `‖D^H u(x)‖ ≤ 4c` at every
point of the closed half-plane. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_of_partialDeriv {c : ℝ}
    (hc : ∀ y ∈ HalfSpace.upper 2, ∀ i k : Fin 2,
      |(∂[i] (fun z ↦ halfPlaneVelocity f z k)) y| ≤ c) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤ 4 * c := by
  rw [fderivWithin_eq_assemble hf hR hα hα1 hM hx]
  refine (norm_assemble_le _ _).trans ?_
  have h0 := norm_fderivWithin_apply_le hf hR hα hα1 hM hc 0 hx
  have h1 := norm_fderivWithin_apply_le hf hR hα hα1 hM hc 1 hx
  linarith

/-- **Size of the derivative up to the boundary.** With `|f| ≤ B` on the closed half-plane and
`L = ∫_{ℝ²₊} |f|`, `‖D^H u(x)‖ ≤ 4(50M/α + 8B + 10L)` at every point of the closed half-plane. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_holder (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤
      4 * (50 * M / α + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |f y|) := by
  obtain ⟨hEc, hEcs, hEM⟩ := evenData hf hR hM
  have hEB : ∀ y, 0 ≤ y 1 → |evenReflection f y| ≤ B := fun y hy ↦ by
    rw [evenReflection_of_nonneg hy]; exact hB y hy
  refine norm_fderivWithin_halfPlaneVelocity_le_of_partialDeriv hf hR hα hα1 hM
    (fun y hy i k ↦ ?_) hx
  have := abs_partialDeriv_halfPlaneVelocity_le hEc hEcs hα hα1.le hEM hEB i k hy
  rwa [halfPlaneVelocity_evenReflection, setIntegral_abs_evenReflection] at this

/-- **Kato-type size of the derivative up to the boundary.** With `|f| ≤ B` on the closed
half-plane and `L = ∫_{ℝ²₊} |f|`, `‖D^H u(x)‖ ≤ 4((50/α)(1 + B log(2 + M)) + 8B + 10L)` at every
point of the closed half-plane. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_kato (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤
      4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
        10 * ∫ y in HalfSpace.upper 2, |f y|) := by
  obtain ⟨hEc, hEcs, hEM⟩ := evenData hf hR hM
  have hEB : ∀ y, 0 ≤ y 1 → |evenReflection f y| ≤ B := fun y hy ↦ by
    rw [evenReflection_of_nonneg hy]; exact hB y hy
  refine norm_fderivWithin_halfPlaneVelocity_le_of_partialDeriv hf hR hα hα1 hM
    (fun y hy i k ↦ ?_) hx
  have := abs_partialDeriv_halfPlaneVelocity_le_log hEc hEcs hα hα1.le hEM hEB i k hy
  rwa [halfPlaneVelocity_evenReflection, setIntegral_abs_evenReflection] at this

/-- **Homogeneous Kato-type size of the derivative up to the boundary.** With `0 < B`,
`|f| ≤ B` on the closed half-plane and `L = ∫_{ℝ²₊} |f|`, at every point of the closed half-plane
`‖D^H u(x)‖ ≤ 4((50B/α)(1 + log(2 + M/B)) + 8B + 10L)`: the bound is homogeneous of degree one
in `(f, M, B, L)`, so it applies to differences; when the data vanish,
`norm_fderivWithin_halfPlaneVelocity_le_holder` with zero constants applies. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_kato_homogeneous
    (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B) (hB0 : 0 < B) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x‖ ≤
      4 * (50 * B / α * (1 + Real.log (2 + M / B)) + 8 * B +
        10 * ∫ y in HalfSpace.upper 2, |f y|) := by
  set g : ℝ^2 → ℝ := B⁻¹ • f with hgdef
  have hfg : f = B • g := by
    funext y; simp only [hgdef, Pi.smul_apply, smul_eq_mul]; field_simp
  have hgc : ContinuousOn g H̄ := hf.const_smul _
  have hgR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0 := fun y hy hyR ↦ by
    simp [hgdef, hR y hy hyR]
  have hBi : 0 < B⁻¹ := inv_pos.mpr hB0
  have hgM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ M / B * ‖y - z‖ ^ α :=
    fun y z hy hz ↦ by
      simp only [hgdef, Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hBi]
      rw [div_eq_inv_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hM y z hy hz) hBi.le
  have hgB : ∀ y, 0 ≤ y 1 → |g y| ≤ 1 := fun y hy ↦ by
    simp only [hgdef, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hBi]
    rw [inv_mul_le_iff₀ hB0, mul_one]; exact hB y hy
  have hgL : ∫ y in HalfSpace.upper 2, |g y| = B⁻¹ * ∫ y in HalfSpace.upper 2, |f y| := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp [hgdef, abs_mul, abs_of_pos hBi]
  have hk := norm_fderivWithin_halfPlaneVelocity_le_kato hgc hgR hα hα1 hgM hgB hx
  have hd := (differentiableOn_halfPlaneVelocity hgc hgR hα hα1 hgM x hx)
  rw [hfg, halfPlaneVelocity_smul, fderivWithin_const_smul (uniqueDiffOn_closedUpper x hx) hd,
    norm_smul, Real.norm_eq_abs, abs_of_pos hB0]
  simp only [hgL, one_mul, mul_one] at hk
  calc B * ‖fderivWithin ℝ (halfPlaneVelocity g) H̄ x‖
      ≤ B * (4 * (50 / α * (1 + Real.log (2 + M / B)) + 8 +
          10 * (B⁻¹ * ∫ y in HalfSpace.upper 2, |f y|))) := by gcongr
    _ = 4 * (50 * B / α * (1 + Real.log (2 + M / B)) + 8 * B +
          10 * ∫ y in HalfSpace.upper 2, |(B • g) y|) := by
        rw [← hfg]
        field_simp

/-- **The velocity is Lipschitz on the closed half-plane.** With `|f| ≤ B` on the closed
half-plane and `L = ∫_{ℝ²₊} |f|`, `u` is Lipschitz on `H̄` with constant
`4((50/α)(1 + B log(2 + M)) + 8B + 10L)`. -/
theorem lipschitzOnWith_halfPlaneVelocity (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B) :
    LipschitzOnWith (Real.toNNReal (4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
      10 * ∫ y in HalfSpace.upper 2, |f y|))) (halfPlaneVelocity f) H̄ := by
  obtain ⟨hEc, hEcs, hEM⟩ := evenData hf hR hM
  have hEB : ∀ y, 0 ≤ y 1 → |evenReflection f y| ≤ B := fun y hy ↦ by
    rw [evenReflection_of_nonneg hy]; exact hB y hy
  have hL := setIntegral_abs_evenReflection f
  refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' ↦ ?_
  have hk := fun k : Fin 2 ↦ abs_halfPlaneVelocity_sub_le_mul hEc hEcs hα hα1 hEM hEB k
    (x := x) (x' := x') hx hx'
  simp only [halfPlaneVelocity_evenReflection, hL] at hk
  set Q := 50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |f y|
  have hQ : 0 ≤ Q := by
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl)
    have hL0 : 0 ≤ ∫ y in HalfSpace.upper 2, |f y| := setIntegral_nonneg
      (HalfSpace.measurableSet_upper (n := 2)) fun y _ ↦ abs_nonneg _
    have hM0 : 0 ≤ M := by
      have h := hM !₂[1, 0] 0 (by simp) (by simp)
      rw [sub_zero, ← Real.sqrt_sq (norm_nonneg _), norm_sq_vec] at h
      norm_num at h
      exact (abs_nonneg _).trans h
    have hlog : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    positivity
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  calc ‖halfPlaneVelocity f x - halfPlaneVelocity f x'‖
      ≤ |halfPlaneVelocity f x 0 - halfPlaneVelocity f x' 0| +
          |halfPlaneVelocity f x 1 - halfPlaneVelocity f x' 1| := by
        rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), EuclideanSpace.norm_sq_fin_two]
        simp only [PiLp.sub_apply]
        nlinarith [abs_nonneg (halfPlaneVelocity f x 0 - halfPlaneVelocity f x' 0),
          abs_nonneg (halfPlaneVelocity f x 1 - halfPlaneVelocity f x' 1),
          sq_abs (halfPlaneVelocity f x 0 - halfPlaneVelocity f x' 0),
          sq_abs (halfPlaneVelocity f x 1 - halfPlaneVelocity f x' 1)]
    _ ≤ 2 * Q * ‖x - x'‖ + 2 * Q * ‖x - x'‖ := add_le_add (hk 0) (hk 1)
    _ = 4 * Q * ‖x - x'‖ := by ring

end Holder


/-! ### The stream function

For data given on the closed half-plane the Green stream `φ = halfSpaceGreenPotential f` is `C¹`
on the plane (it is the potential of the even extension), so its derivatives within `H̄` are its
partial derivatives and `u = (-∂₁^H φ, ∂₀^H φ)` on `H̄`. Consequently the iterated expressions
`∂ⱼ^H ∂ᵢ^H φ` are the expressions `∓∂ⱼ^H uₖ`; these identities say nothing about existence, which
comes from the Hölder or `C¹` theory of the velocity (`differentiableOn_halfPlaneVelocity`,
`hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn`). They connect the velocity interfaces stated
with `PDE.partialDerivWithin` to the velocity theorems. -/

section Stream

variable (hf : ContinuousOn f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
include hf hR

/-- The derivatives within the closed half-plane of the Green stream are its partial
derivatives. -/
theorem partialDerivWithin_halfSpaceGreenPotential_eq (i : Fin 2) {x : ℝ^2} (hx : 0 ≤ x 1) :
    PDE.partialDerivWithin i (halfSpaceGreenPotential f) H̄ x =
      (∂[i] (halfSpaceGreenPotential f)) x := by
  have hφ : halfSpaceGreenPotential f = halfSpaceGreenPotential (evenReflection f) :=
    halfSpaceGreenPotential_congr fun y hy ↦ (evenReflection_of_nonneg (le_of_lt hy)).symm
  rw [hφ]
  exact ((contDiff_one_halfSpaceGreenPotential
    (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR)).differentiable one_ne_zero
    x).partialDerivWithin_eq i (uniqueDiffOn_closedUpper x hx)

/-- On the closed half-plane `u₀ = -∂₁^H φ`. -/
theorem halfPlaneVelocity_zero_eq_neg_partialDerivWithin {x : ℝ^2} (hx : 0 ≤ x 1) :
    halfPlaneVelocity f x 0 = -PDE.partialDerivWithin 1 (halfSpaceGreenPotential f) H̄ x := by
  rw [partialDerivWithin_halfSpaceGreenPotential_eq hf hR 1 hx]
  simp [halfPlaneVelocity]

/-- On the closed half-plane `u₁ = ∂₀^H φ`. -/
theorem halfPlaneVelocity_one_eq_partialDerivWithin {x : ℝ^2} (hx : 0 ≤ x 1) :
    halfPlaneVelocity f x 1 = PDE.partialDerivWithin 0 (halfSpaceGreenPotential f) H̄ x := by
  rw [partialDerivWithin_halfSpaceGreenPotential_eq hf hR 0 hx]
  simp [halfPlaneVelocity]

/-- The iterated derivative expression `∂ⱼ^H ∂₁^H φ` of the Green stream is `-∂ⱼ^H u₀`. -/
theorem partialDerivWithin_partialDerivWithin_one_halfSpaceGreenPotential_eq (j : Fin 2)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    PDE.partialDerivWithin j (PDE.partialDerivWithin 1 (halfSpaceGreenPotential f) H̄) H̄ x =
      -PDE.partialDerivWithin j (fun y ↦ halfPlaneVelocity f y 0) H̄ x := by
  rw [PDE.partialDerivWithin_congr j (g := fun y ↦ -halfPlaneVelocity f y 0)
    (fun y hy ↦ by
      change _ = -halfPlaneVelocity f y 0
      rw [halfPlaneVelocity_zero_eq_neg_partialDerivWithin hf hR hy, neg_neg]) hx]
  simp only [PDE.partialDerivWithin]
  rw [fderivWithin_fun_neg (uniqueDiffOn_closedUpper x hx)]
  rfl

/-- The iterated derivative expression `∂ⱼ^H ∂₀^H φ` of the Green stream is `∂ⱼ^H u₁`. -/
theorem partialDerivWithin_partialDerivWithin_zero_halfSpaceGreenPotential_eq (j : Fin 2)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    PDE.partialDerivWithin j (PDE.partialDerivWithin 0 (halfSpaceGreenPotential f) H̄) H̄ x =
      PDE.partialDerivWithin j (fun y ↦ halfPlaneVelocity f y 1) H̄ x :=
  PDE.partialDerivWithin_congr j
    (fun _ hy ↦ (halfPlaneVelocity_one_eq_partialDerivWithin hf hR hy).symm) hx

omit hf hR in
/-- The derivative within the closed half-plane of a velocity component is the component of the
derivative within it of the velocity, where the velocity is differentiable within it. -/
theorem partialDerivWithin_halfPlaneVelocity_apply (i k : Fin 2) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hd : DifferentiableWithinAt ℝ (halfPlaneVelocity f) H̄ x) :
    PDE.partialDerivWithin i (fun y ↦ halfPlaneVelocity f y k) H̄ x =
      fderivWithin ℝ (halfPlaneVelocity f) H̄ x (EuclideanSpace.single i 1) k := by
  have h : HasFDerivWithinAt (fun y ↦ halfPlaneVelocity f y k)
      (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) k ∘L fderivWithin ℝ (halfPlaneVelocity f) H̄ x) H̄ x :=
    (hasFDerivWithinAt_piLp 2).mp hd.hasFDerivWithinAt k
  rw [h.partialDerivWithin_eq i (uniqueDiffOn_closedUpper x hx)]
  rfl

/-- The rotation `a ↦ (h ↦ a₁h₀ - a₀h₁)`, which takes the velocity to the derivative of the
stream. -/
def streamRotation : ℝ^2 →L[ℝ] (ℝ^2 →L[ℝ] ℝ) :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ) -
    (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ)

/-- On the closed half-plane the derivative within it of the Green stream is the rotated
velocity. -/
theorem fderivWithin_halfSpaceGreenPotential_eq {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (halfSpaceGreenPotential f) H̄ x = streamRotation (halfPlaneVelocity f x) := by
  have hφ : halfSpaceGreenPotential f = halfSpaceGreenPotential (evenReflection f) :=
    halfSpaceGreenPotential_congr fun y hy ↦ (evenReflection_of_nonneg (le_of_lt hy)).symm
  have hd := (contDiff_one_halfSpaceGreenPotential
    (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR)).differentiable one_ne_zero x
  rw [← hφ] at hd
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_closedUpper x hx) hd]
  ext1 v
  have hv : v = v 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      v 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext j; fin_cases j <;> simp
  have h0 : fderiv ℝ (halfSpaceGreenPotential f) x (EuclideanSpace.single 0 1) =
      halfPlaneVelocity f x 1 := by simp [halfPlaneVelocity]; rfl
  have h1 : fderiv ℝ (halfSpaceGreenPotential f) x (EuclideanSpace.single 1 1) =
      -halfPlaneVelocity f x 0 := by simp [halfPlaneVelocity]; rfl
  rw [hv]
  simp only [map_add, map_smul, h0, h1, smul_eq_mul]
  simp [streamRotation]

/-- **The stream is one order more regular than the velocity.** For `f` continuous on the closed
half-plane and vanishing there outside a disc, if the velocity is `C^m` within the closed
half-plane then the Green stream is `C^{m+1}` within it. -/
theorem contDiffOn_succ_halfSpaceGreenPotential {m : ℕ}
    (hu : ContDiffOn ℝ m (halfPlaneVelocity f) H̄) :
    ContDiffOn ℝ (m + 1) (halfSpaceGreenPotential f) H̄ := by
  have hφ : halfSpaceGreenPotential f = halfSpaceGreenPotential (evenReflection f) :=
    halfSpaceGreenPotential_congr fun y hy ↦ (evenReflection_of_nonneg (le_of_lt hy)).symm
  have hC1 : ContDiff ℝ 1 (halfSpaceGreenPotential f) := by
    rw [hφ]
    exact contDiff_one_halfSpaceGreenPotential
      (continuous_evenReflection hf)
      (hasCompactSupport_evenReflection_of_eq_zero hR)
  refine (contDiffOn_succ_iff_fderivWithin uniqueDiffOn_closedUpper).2
    ⟨(hC1.differentiable one_ne_zero).differentiableOn, by simp, ?_⟩
  exact (streamRotation.contDiff.comp_contDiffOn hu).congr fun x hx ↦
    fderivWithin_halfSpaceGreenPotential_eq hf hR hx

end Stream

end IncompressibleFlow

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityBoundary
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.Translation
import PDE.FDeriv.PartialDeriv.Transforms
public import PDE.FDeriv.PartialDeriv.Within
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import Mathlib.Analysis.Calculus.FDeriv.Extend
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Tangential derivatives of the half-plane velocity

The Green potential commutes with translations parallel to the boundary
(`GreenFunction.halfSpaceGreenPotential_comp_add`), hence so does the Biot–Savart velocity
`u(f) = halfPlaneVelocity f` (`halfPlaneVelocity_comp_add`). For continuous compactly supported
vorticity with continuous tangential derivative, the tangential derivative of the velocity is the
velocity of the tangential derivative, `∂₀u(f) = u(∂₀f)`, at every point of the plane
(`hasDerivAt_halfPlaneVelocity_tangential`). For vorticity given on the closed half-plane `H̄`
the tangential derivative within `H̄` takes its place
(`hasDerivAt_halfPlaneVelocity_tangential_of_contDiffOn`).

With `div u = 0` and `∂₁u₀ - ∂₀u₁ = f` this determines the whole derivative,
`Du(f) = divFreeDeriv (u(∂₀f)) f`, where `divFreeDeriv a c` is the derivative of a divergence-free
planar field with tangential derivative `a` and clockwise vorticity `c`: `∂₀u = a`, `∂₁u₀ = c + a₁`,
`∂₁u₁ = -a₀`. For `f` `C¹` within `H̄` and vanishing there outside a disc the formula holds at
interior points (`hasFDerivAt_halfPlaneVelocity_of_contDiffOn`) and within `H̄` at each of its
points (`hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn`). The tangential part
`a ↦ (h ↦ (a₀h₀ + a₁h₁, a₁h₀ - a₀h₁))` preserves norms (`norm_divFreeTangential_apply_apply`) and
the vorticity part `h ↦ (h₁, 0)` has norm at most one; these bounds drive the higher-order estimates
of the velocity.

## Main definitions

* `divFreeDeriv`: the derivative `h ↦ (a₀h₀ + (c + a₁)h₁, a₁h₀ - a₀h₁)` of a divergence-free
  planar field with tangential derivative `a` and clockwise vorticity `c`.
* `divFreeTangential`: its tangential part; `divFreeVorticity` is the vorticity part
  `h ↦ (h₁, 0)`.

## Main results

* `halfPlaneVelocity_comp_add`: for `a₁ = 0`, `u(f(· + a))(x) = u(f)(x + a)`.
* `hasDerivAt_halfPlaneVelocity_tangential`: for continuous compactly supported vorticity with
  continuous tangential derivative, `∂₀u(f) = u(∂₀f)` at every point of the plane.
* `hasDerivAt_halfPlaneVelocity_tangential_of_contDiffOn`: the same with the tangential derivative
  within `H̄`, for `f` `C¹` within `H̄` and vanishing there outside a disc.
* `hasFDerivAt_halfPlaneVelocity_of_contDiffOn`: `Du(f)(x) = divFreeDeriv (u(∂₀f)(x)) (f x)` at
  every point of the open upper half-plane.
* `hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn`: the same formula within `H̄` at each of its
  points.
* `norm_divFreeTangential_apply_apply`: `‖(divFreeTangential a) h‖ = ‖a‖ ‖h‖`.
* `norm_halfPlaneVelocity_le`: with `|f| ≤ B` on the open upper half-plane,
  `‖u(f)(x)‖ ≤ B + π⁻¹ ∫_{ℝ²₊} |f|` at every point of the plane.

## How it works

For the tangential derivative we bound the remainder `f(· + t e₀) - f - t ∂₀f` by `ε |t|` uniformly,
by the mean value theorem and the uniform continuity of `∂₀f`, and it vanishes outside a fixed disc.
By linearity and translation invariance the remainder of the velocity is the velocity of this
remainder, and the size bound `norm_halfPlaneVelocity_le` makes it `O(ε |t|)`. For data on `H̄` we
apply this to the even reflection, which has the same velocity (`halfPlaneVelocity_evenReflection`)
and whose tangential derivative is the even reflection of the tangential derivative within `H̄`
(`hasDerivAt_evenReflection_tangential`). At interior points the velocity is differentiable
(`differentiableAt_halfPlaneVelocity`), its tangential derivative is `u(∂₀f)`, and the divergence
and curl identities (`partialDeriv_halfPlaneVelocity_div_curl`) give the normal derivative. Up to
the boundary we use Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv`, since
`y ↦ divFreeDeriv (u(∂₀f)(y)) (f y)` is continuous on `H̄`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open GreenFunction PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection halfPlaneFold halfPlaneFold_mem evenReflection_of_nonneg
  continuous_evenReflection hasCompactSupport_evenReflection_of_eq_zero)

namespace IncompressibleFlow

/-! ### The derivative of a divergence-free planar field -/

/-- The tangential part of the derivative of a divergence-free planar field: with tangential
derivative `a` and zero vorticity, `h ↦ (a₀h₀ + a₁h₁, a₁h₀ - a₀h₁)`. -/
def divFreeTangential : ℝ^2 →L[ℝ] (ℝ^2 →L[ℝ] ℝ^2) :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight
      ((EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single 0 1) -
        (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single 1 1)) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight
      ((EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single 0 1) +
        (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single 1 1))

/-- The vorticity part `h ↦ (h₁, 0)` of the derivative of a divergence-free planar field. -/
def divFreeVorticity : ℝ^2 →L[ℝ] ℝ^2 :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single 0 1)

/-- The derivative of a divergence-free planar field with tangential derivative `a` and clockwise
vorticity `c`: `h ↦ (a₀h₀ + (c + a₁)h₁, a₁h₀ - a₀h₁)`. -/
def divFreeDeriv (a : ℝ^2) (c : ℝ) : ℝ^2 →L[ℝ] ℝ^2 :=
  divFreeTangential a + c • divFreeVorticity

/-- `(divFreeTangential a) h = (a₀h₀ + a₁h₁, a₁h₀ - a₀h₁)`. -/
theorem divFreeTangential_apply_apply (a h : ℝ^2) :
    divFreeTangential a h = !₂[a 0 * h 0 + a 1 * h 1, a 1 * h 0 - a 0 * h 1] := by
  ext i; fin_cases i
  · simp [divFreeTangential]
  · simp [divFreeTangential]; ring

/-- `divFreeVorticity h = (h₁, 0)`. -/
theorem divFreeVorticity_apply (h : ℝ^2) : divFreeVorticity h = !₂[h 1, 0] := by
  ext i; fin_cases i <;> simp [divFreeVorticity]

/-- `(divFreeDeriv a c) h = (a₀h₀ + (c + a₁)h₁, a₁h₀ - a₀h₁)`. -/
theorem divFreeDeriv_apply (a : ℝ^2) (c : ℝ) (h : ℝ^2) :
    divFreeDeriv a c h = !₂[a 0 * h 0 + (c + a 1) * h 1, a 1 * h 0 - a 0 * h 1] := by
  ext i; fin_cases i <;> simp [divFreeDeriv, divFreeTangential, divFreeVorticity] <;> ring

/-- The tangential column of `divFreeDeriv a c` is `a`. -/
theorem divFreeDeriv_single_zero (a : ℝ^2) (c : ℝ) :
    divFreeDeriv a c (EuclideanSpace.single 0 1) = a := by
  rw [divFreeDeriv_apply]; ext i; fin_cases i <;> simp

/-- The normal column of `divFreeDeriv a c` is `(c + a₁, -a₀)`. -/
theorem divFreeDeriv_single_one (a : ℝ^2) (c : ℝ) :
    divFreeDeriv a c (EuclideanSpace.single 1 1) = !₂[c + a 1, -a 0] := by
  rw [divFreeDeriv_apply]; ext i; fin_cases i <;> simp

/-- The tangential part preserves norms: `‖(divFreeTangential a) h‖ = ‖a‖ ‖h‖`. -/
theorem norm_divFreeTangential_apply_apply (a h : ℝ^2) :
    ‖divFreeTangential a h‖ = ‖a‖ * ‖h‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, EuclideanSpace.norm_sq_fin_two,
      EuclideanSpace.norm_sq_fin_two,
    EuclideanSpace.norm_sq_fin_two, divFreeTangential_apply_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- `‖divFreeTangential a‖ ≤ ‖a‖`. -/
theorem norm_divFreeTangential_apply_le (a : ℝ^2) : ‖divFreeTangential a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun h ↦
    (norm_divFreeTangential_apply_apply a h).le

/-- The map `divFreeTangential` has norm at most one. -/
theorem norm_divFreeTangential_le : ‖divFreeTangential‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a ↦ by
    simpa using norm_divFreeTangential_apply_le a

/-- The map `divFreeVorticity` has norm at most one. -/
theorem norm_divFreeVorticity_le : ‖divFreeVorticity‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h ↦ by
    rw [divFreeVorticity_apply, one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_fin_two, EuclideanSpace.norm_sq_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg (h 0)]

/-- `divFreeDeriv` depends continuously on the tangential derivative and the vorticity. -/
theorem Continuous.divFreeDeriv {X : Type*} [TopologicalSpace X] {a : X → ℝ^2} {c : X → ℝ}
    (ha : Continuous a) (hc : Continuous c) :
    Continuous fun x ↦ IncompressibleFlow.divFreeDeriv (a x) (c x) :=
  (divFreeTangential.continuous.comp ha).add (hc.smul continuous_const)

/-! ### Linearity, size and tangential translations -/

variable {f : ℝ^2 → ℝ}

/-- The velocity is homogeneous in the vorticity. -/
theorem halfPlaneVelocity_smul (c : ℝ) (f : ℝ^2 → ℝ) :
    halfPlaneVelocity (c • f) = c • halfPlaneVelocity f := by
  have hφ : halfSpaceGreenPotential (c • f) = fun x ↦ c • halfSpaceGreenPotential f x := by
    funext x
    simp only [halfSpaceGreenPotential, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      integral_const_mul]
  have h1 : ∀ (i : Fin 2) (x : ℝ^2), (∂[i] (halfSpaceGreenPotential (c • f))) x =
      c * (∂[i] (halfSpaceGreenPotential f)) x := fun i x ↦ by
    rw [hφ, PDE.partialDeriv_const_smul, smul_eq_mul]
  funext x
  ext k
  fin_cases k <;> simp [halfPlaneVelocity, planarStreamVelocity, h1]

/-- **Size of the velocity.** For a continuous compactly supported vorticity with `|f| ≤ B` on
the open upper half-plane, `‖u(f)(x)‖ ≤ B + π⁻¹ ∫_{ℝ²₊} |f|` at every point of the plane. -/
theorem norm_halfPlaneVelocity_le (hf : Continuous f) (hc : HasCompactSupport f) {B : ℝ}
    (hB : ∀ y ∈ HalfSpace.upper 2, |f y| ≤ B) (x : ℝ^2) :
    ‖halfPlaneVelocity f x‖ ≤ B + (∫ y in HalfSpace.upper 2, |f y|) / Real.pi := by
  have hB0 : 0 ≤ B := by
    have := hB !₂[0, 1] (show (0 : ℝ) < (!₂[0, 1] : ℝ^2) 1 by simp)
    exact (abs_nonneg _).trans this
  have h := norm_gradient_halfSpaceGreenPotential_le_mass hf hc hB0
    (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hB y hy) x one_pos
  simp only [Real.norm_eq_abs, mul_one] at h
  rw [halfPlaneVelocity, norm_planarStreamVelocity]
  exact h

/-- The velocity of a continuous compactly supported vorticity is continuous on the plane. -/
private theorem continuous_velocity (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (halfPlaneVelocity f) :=
  (contDiff_planarStreamVelocity (m := 0) _
    (by simpa using contDiff_one_halfSpaceGreenPotential hf hc)).continuous

/-- **Tangential translations commute with the velocity**: for `a₁ = 0` and every vorticity,
`u(f(· + a))(x) = u(f)(x + a)`. -/
theorem halfPlaneVelocity_comp_add {a : ℝ^2} (ha : a 1 = 0) (f : ℝ^2 → ℝ) (x : ℝ^2) :
    halfPlaneVelocity (fun y ↦ f (y + a)) x = halfPlaneVelocity f (x + a) := by
  have hφ : halfSpaceGreenPotential (fun y ↦ f (y + a)) =
      fun y ↦ halfSpaceGreenPotential f (y + a) :=
    funext (halfSpaceGreenPotential_comp_add (n := 2) ha f)
  simp only [halfPlaneVelocity, planarStreamVelocity, hφ, PDE.partialDeriv_comp_add_right]

/-- The integral over the open upper half-plane of a continuous function bounded by `b` and
vanishing outside the disc of radius `ρ` is at most `b` times the area of the disc. -/
private theorem integral_upper_abs_le {g : ℝ^2 → ℝ} (hg : Continuous g) {b ρ : ℝ}
    (hb : ∀ y, |g y| ≤ b) (hρ : ∀ y : ℝ^2, ρ < ‖y‖ → g y = 0) :
    ∫ y in HalfSpace.upper 2, |g y| ≤ b * volume.real (closedBall (0 : ℝ^2) ρ) := by
  have hcs : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall 0 ρ)
    fun y hy ↦ hρ y (by simpa using hy)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
  have hle : ∀ y, |g y| ≤ (closedBall (0 : ℝ^2) ρ).indicator (fun _ ↦ b) y := by
    intro y
    by_cases hy : y ∈ closedBall (0 : ℝ^2) ρ
    · rw [indicator_of_mem hy]; exact hb y
    · rw [indicator_of_notMem hy, hρ y (by simpa using hy), abs_zero]
  have hind : Integrable ((closedBall (0 : ℝ^2) ρ).indicator fun _ ↦ b) :=
    (integrableOn_const (C := b) measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  calc ∫ y in HalfSpace.upper 2, |g y|
      ≤ ∫ y in HalfSpace.upper 2, (closedBall (0 : ℝ^2) ρ).indicator (fun _ ↦ b) y :=
        setIntegral_mono_on (hg.integrable_of_hasCompactSupport hcs).abs.integrableOn
          hind.integrableOn (HalfSpace.measurableSet_upper (n := 2)) fun y _ ↦ hle y
    _ ≤ ∫ y, (closedBall (0 : ℝ^2) ρ).indicator (fun _ ↦ b) y :=
        setIntegral_le_integral hind (Eventually.of_forall fun y ↦ by
          by_cases hy : y ∈ closedBall (0 : ℝ^2) ρ <;> simp [hy, hb0])
    _ = b * volume.real (closedBall (0 : ℝ^2) ρ) := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
          mul_comm]

/-- A function of the line `t ↦ F (y + t e)` differentiable everywhere along the line has, at
`s`, the derivative the line derivative of `F` at `y + s e`. -/
private theorem hasDerivAt_line_of_forall {F g : ℝ^2 → ℝ} {e : ℝ^2}
    (hF : ∀ y, HasDerivAt (fun t : ℝ ↦ F (y + t • e)) (g y) 0) (y : ℝ^2) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ F (y + t • e)) (g (y + s • e)) s := by
  have h1 : HasDerivAt (fun t : ℝ ↦ F (y + s • e + t • e)) (g (y + s • e)) (s - s) := by
    rw [sub_self]; exact hF (y + s • e)
  refine (h1.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  simp only
  rw [add_assoc, ← add_smul, add_sub_cancel]

/-- **Tangential derivatives commute with the velocity.** Let `f` be continuous and compactly
supported and let `g` be continuous with `g(y)` the derivative of `t ↦ f(y + t e₀)` at `t = 0`
for every `y`. Then at every point `x` of the plane, `t ↦ u(f)(x + t e₀)` has derivative
`u(g)(x)` at `t = 0`. -/
theorem hasDerivAt_halfPlaneVelocity_tangential (hf : Continuous f) (hc : HasCompactSupport f)
    {g : ℝ^2 → ℝ} (hg : Continuous g)
    (hfg : ∀ y, HasDerivAt (fun t : ℝ ↦ f (y + t • EuclideanSpace.single 0 1)) (g y) 0)
    (x : ℝ^2) :
    HasDerivAt (fun t : ℝ ↦ halfPlaneVelocity f (x + t • EuclideanSpace.single 0 1))
      (halfPlaneVelocity g x) 0 := by
  set e : ℝ^2 := EuclideanSpace.single 0 1 with he
  have he1 : ∀ t : ℝ, (t • e) 1 = 0 := fun t ↦ by simp [he]
  have hne : ∀ t : ℝ, ‖t • e‖ = |t| := fun t ↦ by simp [he, norm_smul]
  -- `g` vanishes off the support of `f`
  have hgsupp : Function.support g ⊆ tsupport f := fun y hy ↦ by
    by_contra hy'
    have hzero : ∀ᶠ t in 𝓝 (0 : ℝ), f (y + t • e) = 0 :=
      ((by fun_prop : Continuous fun t : ℝ ↦ y + t • e).tendsto' 0 y (by simp)).eventually
        (notMem_tsupport_iff_eventuallyEq.mp hy')
    exact hy ((hfg y).unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero))
  have hgcs : HasCompactSupport g := hc.mono' hgsupp
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hf0 : ∀ y : ℝ^2, R < ‖y‖ → f y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have := hR h; rw [mem_closedBall, dist_zero_right] at this; linarith
  have hg0 : ∀ y : ℝ^2, R < ‖y‖ → g y = 0 := fun y hy ↦ by
    by_contra h
    have := hR (hgsupp h); rw [mem_closedBall, dist_zero_right] at this; linarith
  -- the remainder of the tangential difference quotient
  set h : ℝ → ℝ^2 → ℝ := fun t ↦ ((fun y ↦ f (y + t • e)) - f) - t • g with hhdef
  have hτc : ∀ t : ℝ, Continuous fun y ↦ f (y + t • e) := fun t ↦
    hf.comp (continuous_id.add continuous_const)
  have hτcs : ∀ t : ℝ, HasCompactSupport fun y ↦ f (y + t • e) := fun t ↦
    hc.comp_homeomorph (Homeomorph.addRight (t • e))
  have hhc : ∀ t, Continuous (h t) := fun t ↦ ((hτc t).sub hf).sub (hg.const_smul t)
  have hhcs : ∀ t, HasCompactSupport (h t) := fun t ↦ ((hτcs t).sub hc).sub hgcs.smul_left
  have hrem (t : ℝ) : halfPlaneVelocity f (x + t • e) - halfPlaneVelocity f x -
      t • halfPlaneVelocity g x = halfPlaneVelocity (h t) x := by
    ext k
    have h1 := halfPlaneVelocity_sub ((hτc t).sub hf) ((hτcs t).sub hc) (hg.const_smul t)
      hgcs.smul_left x k
    have h2 := halfPlaneVelocity_sub (hτc t) (hτcs t) hf hc x k
    rw [hhdef]
    simp only at h1 h2 ⊢
    rw [h1, h2, halfPlaneVelocity_smul, ← halfPlaneVelocity_comp_add (he1 t)]
    simp
  -- uniform smallness of the remainder
  have hsmall : ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ y, |h t y| ≤ ε * |t| := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp
      (hgcs.uniformContinuous_of_continuous hg) ε hε
    refine ⟨δ, hδ, fun t ht y ↦ ?_⟩
    have hmv := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ ↦ f (y + s • e) - s * g y) (f' := fun s ↦ g (y + s • e) - g y)
      (C := ε) (x := 0) (y := t)
      (fun s _ ↦ ((hasDerivAt_line_of_forall hfg y s).sub
        ((hasDerivAt_id s).mul_const (g y)) |>.congr_deriv (by simp)).hasDerivWithinAt)
      (fun s hs ↦ by
        have hs' : |s| < δ := by simpa [mem_ball, dist_zero_right] using hs
        have := hδε (show dist (y + s • e) y < δ by
          rw [dist_eq_norm, add_sub_cancel_left, hne]; exact hs')
        rw [Real.dist_eq] at this; rw [Real.norm_eq_abs]; exact this.le)
      (mem_ball_self hδ) (by simpa [mem_ball, dist_zero_right] using ht)
    calc |h t y| = ‖(f (y + t • e) - t * g y) - (f (y + (0 : ℝ) • e) - 0 * g y)‖ := by
          rw [Real.norm_eq_abs]; congr 1; simp only [hhdef, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul, zero_smul, add_zero, zero_mul, sub_zero]; ring
      _ ≤ ε * ‖t - 0‖ := hmv
      _ = ε * |t| := by rw [sub_zero, Real.norm_eq_abs]
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, zero_smul, add_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc0
  set V := volume.real (closedBall (0 : ℝ^2) (R + 1)) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set ε := c / (1 + V / Real.pi) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδh⟩ := hsmall ε hε
  filter_upwards [ball_mem_nhds (0 : ℝ) (lt_min hδ one_pos)] with t ht
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, lt_min_iff] at ht
  rw [hrem t, Real.norm_eq_abs]
  have hB : ∀ y, |h t y| ≤ ε * |t| := hδh t ht.1
  have hsupp (y : ℝ^2) (hy : R + 1 < ‖y‖) : h t y = 0 := by
    have hy' : R < ‖y + t • e‖ := by linarith [norm_le_add_norm_add y (t • e), hne t]
    simp [hhdef, hf0 _ hy', hf0 y (by linarith), hg0 y (by linarith)]
  have hL := integral_upper_abs_le (hhc t) hB hsupp
  refine (norm_halfPlaneVelocity_le (hhc t) (hhcs t) (fun y _ ↦ hB y) x).trans ?_
  have hpi := Real.pi_pos
  calc ε * |t| + (∫ y in HalfSpace.upper 2, |h t y|) / Real.pi
      ≤ ε * |t| + ε * |t| * V / Real.pi := by gcongr
    _ = ε * (1 + V / Real.pi) * |t| := by ring
    _ = c * |t| := by rw [hεdef, div_mul_cancel₀ _ (by positivity)]

/-! ### Vorticity given on the closed half-plane -/

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The derivative within the closed half-plane of a function vanishing on it outside a disc
vanishes there outside the same disc. -/
theorem fderivWithin_eq_zero_of_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ^2 → E} {R : ℝ} (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → F y = 0) {y : ℝ^2}
    (hy : 0 ≤ y 1) (hyR : R < ‖y‖) : fderivWithin ℝ F H̄ y = 0 := by
  have hev : F =ᶠ[𝓝[H̄] y] fun _ ↦ 0 := by
    have hopen : {z : ℝ^2 | R < ‖z‖} ∈ 𝓝 y :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hyR
    filter_upwards [inter_mem_nhdsWithin H̄ hopen] with z hz
    exact hR z hz.1 hz.2
  rw [hev.fderivWithin_eq (hR y hy hyR), fderivWithin_const_apply]

/-- A function `C¹` within the closed half-plane and vanishing there outside a disc is Lipschitz on
the closed half-plane. -/
theorem exists_lipschitz_of_contDiffOn {F : ℝ^2 → ℝ} {R : ℝ} (hF : ContDiffOn ℝ 1 F H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → F y = 0) :
    ∃ C : ℝ, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |F y - F z| ≤ C * ‖y - z‖ ^ (1 : ℝ) := by
  have hK : IsCompact (H̄ ∩ closedBall (0 : ℝ^2) R) :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const (by fun_prop))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((hF.continuousOn_fderivWithin uniqueDiffOn_closedUpper le_rfl).mono inter_subset_left)
  have hbound : ∀ y ∈ H̄, ‖fderivWithin ℝ F H̄ y‖ ≤ max C 0 := by
    intro y hy
    by_cases hyR : ‖y‖ ≤ R
    · exact (hC y ⟨hy, by simpa using hyR⟩).trans (le_max_left _ _)
    · rw [fderivWithin_eq_zero_of_eq_zero hR hy (not_le.mp hyR), norm_zero]
      exact le_max_right _ _
  have hconv : Convex ℝ H̄ :=
    convex_halfSpace_ge (f := fun y : ℝ^2 ↦ y 1) ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩ 0
  refine ⟨max C 0, fun y z hy hz ↦ ?_⟩
  have h := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw ↦ ((hF.differentiableOn one_ne_zero) w hw).hasFDerivWithinAt) hbound hz hy
  rw [Real.rpow_one, ← Real.norm_eq_abs]
  exact h

/-- **Tangential derivative of the even extension.** For `f` differentiable within the closed
half-plane, `t ↦ E(f)(y + t e₀)` has derivative `E(∂₀^{H̄} f)(y)` at `t = 0`, at every point `y`
of the plane. -/
theorem hasDerivAt_evenReflection_tangential (hf : DifferentiableOn ℝ f H̄) (y : ℝ^2) :
    HasDerivAt (fun t : ℝ ↦ evenReflection f (y + t • EuclideanSpace.single 0 1))
      (evenReflection (PDE.partialDerivWithin 0 f H̄) y) 0 := by
  set e : ℝ^2 := EuclideanSpace.single 0 1 with he
  set p : ℝ^2 := halfPlaneFold y with hp
  have hpH : p ∈ H̄ := halfPlaneFold_mem y
  have hline : HasDerivAt (fun t : ℝ ↦ p + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
  have hcomp := ((hf p hpH).hasFDerivWithinAt).comp_hasDerivAt_of_eq (0 : ℝ) hline
    (Eventually.of_forall fun t ↦ show (0 : ℝ) ≤ (p + t • e) 1 by simp [hp, he])
    (by simp)
  have hfold : ∀ t : ℝ, halfPlaneFold (y + t • e) = p + t • e := fun t ↦ by
    ext i; fin_cases i <;> simp [hp, he]
  convert hcomp using 1
  · funext t
    simp only [Function.comp_apply, evenReflection, hfold]
  · rfl

/-- **Tangential derivatives commute with the velocity, data on the closed half-plane.** For `f`
`C¹` within the closed half-plane and vanishing there outside a disc, at every point `x` of the
plane `t ↦ u(f)(x + t e₀)` has derivative `u(∂₀^{H̄} f)(x)` at `t = 0`. -/
theorem hasDerivAt_halfPlaneVelocity_tangential_of_contDiffOn {R : ℝ}
    (hf : ContDiffOn ℝ 1 f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (x : ℝ^2) :
    HasDerivAt (fun t : ℝ ↦ halfPlaneVelocity f (x + t • EuclideanSpace.single 0 1))
      (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄) x) 0 := by
  have hg : ContinuousOn (PDE.partialDerivWithin 0 f H̄) H̄ :=
    (hf.partialDerivWithin (m := 0) 0 uniqueDiffOn_closedUpper (by norm_num)).continuousOn
  have h := hasDerivAt_halfPlaneVelocity_tangential
    (continuous_evenReflection hf.continuousOn)
    (hasCompactSupport_evenReflection_of_eq_zero hR)
    (continuous_evenReflection hg)
    (hasDerivAt_evenReflection_tangential (hf.differentiableOn one_ne_zero)) x
  simpa only [halfPlaneVelocity_evenReflection] using h

/-- For `f` continuous on the closed half-plane and vanishing there outside a disc, the velocity
is continuous on the plane. -/
theorem continuous_halfPlaneVelocity_of_continuousOn {R : ℝ} (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) : Continuous (halfPlaneVelocity f) := by
  rw [← halfPlaneVelocity_evenReflection f]
  exact continuous_velocity (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR)

/-- The partial derivative within the closed half-plane vanishes there outside the disc where the
function vanishes. -/
theorem partialDerivWithin_eq_zero_of_eq_zero {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (i : Fin 2) :
    ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → PDE.partialDerivWithin i f H̄ y = 0 := fun y hy hyR ↦ by
  simp [PDE.partialDerivWithin, fderivWithin_eq_zero_of_eq_zero hR hy hyR]

/-- **The derivative of the velocity at interior points.** For `f` `C¹` within the closed
half-plane and vanishing there outside a disc, at every point of the open upper half-plane
`Du(f)(x) = divFreeDeriv (u(∂₀^{H̄} f)(x)) (f x)`: `∂₀u = u(∂₀f)`, `∂₁u₀ = f + u₁(∂₀f)`,
`∂₁u₁ = -u₀(∂₀f)`. -/
theorem hasFDerivAt_halfPlaneVelocity_of_contDiffOn {R : ℝ} (hf : ContDiffOn ℝ 1 f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    HasFDerivAt (halfPlaneVelocity f)
      (divFreeDeriv (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄) x) (f x)) x := by
  set F := evenReflection f with hFdef
  have hFc : Continuous F := continuous_evenReflection hf.continuousOn
  have hFcs : HasCompactSupport F := hasCompactSupport_evenReflection_of_eq_zero hR
  obtain ⟨C, hC⟩ := exists_lipschitz_of_contDiffOn hf hR
  have hCF : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |F y - F z| ≤ C * ‖y - z‖ ^ (1 : ℝ) :=
    fun y z hy hz ↦ by simpa only [hFdef, evenReflection_of_nonneg hy,
      evenReflection_of_nonneg hz] using hC y z hy hz
  have huF : halfPlaneVelocity F = halfPlaneVelocity f := halfPlaneVelocity_evenReflection f
  have hd := differentiableAt_halfPlaneVelocity hFc hFcs one_pos le_rfl hCF hx
  rw [huF] at hd
  set a := halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄) x with ha
  have htan : fderiv ℝ (halfPlaneVelocity f) x (EuclideanSpace.single 0 1) = a := by
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
        (EuclideanSpace.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).const_add x
    have h2 := (show HasFDerivAt (halfPlaneVelocity f) (fderiv ℝ (halfPlaneVelocity f) x)
        (x + (0 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) by
      simpa using hd.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hline
    exact h2.unique (hasDerivAt_halfPlaneVelocity_tangential_of_contDiffOn hf hR x)
  have hpart (k : Fin 2) : (∂[(0 : Fin 2)] (fun y ↦ halfPlaneVelocity f y k)) x = a k := by
    rw [← huF, ← fderiv_halfPlaneVelocity_apply hFc hFcs one_pos le_rfl hCF hx 0 k, huF, htan]
  obtain ⟨hdiv, hcurl⟩ :=
    partialDeriv_halfPlaneVelocity_div_curl hFc hFcs one_pos le_rfl hCF hx
  rw [huF, hFdef, evenReflection_of_nonneg (le_of_lt hx)] at hcurl
  rw [huF] at hdiv
  have hnormal : fderiv ℝ (halfPlaneVelocity f) x (EuclideanSpace.single 1 1) =
      !₂[f x + a 1, -a 0] := by
    have he : ∀ k : Fin 2, fderiv ℝ (halfPlaneVelocity f) x (EuclideanSpace.single 1 1) k =
        (∂[(1 : Fin 2)] (fun y ↦ halfPlaneVelocity f y k)) x := fun k ↦ by
      rw [← huF, fderiv_halfPlaneVelocity_apply hFc hFcs one_pos le_rfl hCF hx 1 k]
    ext k
    rw [he k]
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [hpart 1]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith [hpart 0]
  refine hd.hasFDerivAt.congr_fderiv ?_
  ext1 v
  have hv : v = v 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      v 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext j; fin_cases j <;> simp
  rw [hv, map_add, map_smul, map_smul, map_add, map_smul, map_smul, htan, hnormal,
    divFreeDeriv_single_zero, divFreeDeriv_single_one]

/-- **The derivative of the velocity up to the boundary.** For `f` `C¹` within the closed
half-plane and vanishing there outside a disc, at every point `x` of the closed half-plane the
velocity is differentiable within it with derivative `divFreeDeriv (u(∂₀^{H̄} f)(x)) (f x)`. -/
theorem hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn {R : ℝ} (hf : ContDiffOn ℝ 1 f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : 0 ≤ x 1) :
    HasFDerivWithinAt (halfPlaneVelocity f)
      (divFreeDeriv (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄) x) (f x)) H̄ x := by
  set g := PDE.partialDerivWithin 0 f H̄ with hgdef
  have hgc : ContinuousOn g H̄ :=
    (hf.partialDerivWithin (m := 0) 0 uniqueDiffOn_closedUpper (by norm_num)).continuousOn
  have hug : Continuous (halfPlaneVelocity g) :=
    continuous_halfPlaneVelocity_of_continuousOn hgc (partialDerivWithin_eq_zero_of_eq_zero hR 0)
  have huf : Continuous (halfPlaneVelocity f) :=
    continuous_halfPlaneVelocity_of_continuousOn hf.continuousOn hR
  have hlim : Tendsto (fun y ↦ divFreeDeriv (halfPlaneVelocity g y) (f y))
      (𝓝[HalfSpace.upper 2] x) (𝓝 (divFreeDeriv (halfPlaneVelocity g x) (f x))) := by
    have hfx : Tendsto f (𝓝[HalfSpace.upper 2] x) (𝓝 (f x)) :=
      ((hf.continuousOn x hx).tendsto).mono_left
        (nhdsWithin_mono x fun y hy ↦ (le_of_lt (show (0 : ℝ) < y 1 from hy)))
    exact ((divFreeTangential.continuous.tendsto _).comp
      ((hug.tendsto x).mono_left nhdsWithin_le_nhds)).add (hfx.smul tendsto_const_nhds)
  have h := hasFDerivWithinAt_closure_of_tendsto_fderiv (f := halfPlaneVelocity f)
    (s := HalfSpace.upper 2) (x := x)
    (fun y hy ↦ (hasFDerivAt_halfPlaneVelocity_of_contDiffOn hf hR hy).differentiableAt
      |>.differentiableWithinAt)
    (HalfSpace.convex_upper (n := 2)) (HalfSpace.isOpen_upper 2) (fun y _ ↦ huf.continuousWithinAt)
    (hlim.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hasFDerivAt_halfPlaneVelocity_of_contDiffOn hf hR hy).fderiv.symm))
  rwa [HalfSpace.closure_upper_two] at h

/-- The derivative within the closed half-plane of the velocity is `divFreeDeriv`. -/
theorem fderivWithin_halfPlaneVelocity_of_contDiffOn {R : ℝ} (hf : ContDiffOn ℝ 1 f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (halfPlaneVelocity f) H̄ x =
      divFreeDeriv (halfPlaneVelocity (PDE.partialDerivWithin 0 f H̄) x) (f x) :=
  (hasFDerivWithinAt_halfPlaneVelocity_of_contDiffOn hf hR hx).fderivWithin
    (uniqueDiffOn_closedUpper x hx)

end IncompressibleFlow

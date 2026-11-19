/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityGradient
public import PDE.Spaces.Holder.Directional
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Hölder estimates of the half-plane velocity gradient

Let `ω` be a continuous compactly supported vorticity with `|ω(y) - ω(z)| ≤ M |y - z|^α` on the
closed upper half-plane, `|ω| ≤ B` there and `L = ∫_{ℝ²₊} |ω|`. The Biot–Savart velocity
`u = halfPlaneVelocity ω` is differentiable in the open upper half-plane `ℝ²₊`
(`differentiableAt_halfPlaneVelocity`) with the principal-value gradient
(`partialDeriv_halfPlaneVelocity`). For `0 < α < 1` the gradient is Hölder; for `0 < α ≤ 1` it is
bounded and satisfies a Kato-type bound.

The Hölder estimate is uniform up to the boundary and depends on `ω` only through `M`. The
low-frequency term `L` in the Kato-type bound cannot be dropped: `ω = ε η(|y|) χ(|y|/R) y₀y₁/|y|²`
with fixed cutoffs has `[ω]_α + sup |ω|` bounded uniformly in `R` while
`u_x(0, 1/2) ≈ -(ε/4) log R`.

## Main results

* `abs_partialDeriv_halfPlaneVelocity_sub_le`:
  `|∂ᵢuₖ(x) - ∂ᵢuₖ(x')| ≤ 211/(α(1-α)) · M |x - x'|^α` for `x, x' ∈ ℝ²₊`.
* `abs_partialDeriv_halfPlaneVelocity_le`: `|∂ᵢuₖ(x)| ≤ 50M/α + 8B + 10L`.
* `abs_partialDeriv_halfPlaneVelocity_le_log`:
  `|∂ᵢuₖ(x)| ≤ (50/α)(1 + B log(2 + M)) + 8B + 10L`, the Kato-type bound.
* `norm_fderiv_halfPlaneVelocity_le`: the derivative of `u` as a linear map is bounded by the
  sum of the four partials, so the same bounds hold for `‖Du(x)‖` with a factor `4`.
* `norm_fderiv_halfPlaneVelocity_sub_le`: `‖Du(x) - Du(x')‖ ≤ 844/(α(1-α)) · M |x - x'|^α`.
* `partialDeriv_halfPlaneVelocity_div_curl`: `∂₀u₀ + ∂₁u₁ = 0` and `∂₁u₀ - ∂₀u₁ = ω`.
* `weightedSeminorm_partialDeriv_halfPlaneVelocity_le`: the seminorm form
  `[∂ᵢuₖ]_{C^α(ℝ²₊)} ≤ 211/(α(1-α)) [ω]_{C^α}`; the `HolderOnWith` form is
  `holderOnWith_partialDeriv_halfPlaneVelocity`.
* `partialDeriv_halfPlaneVelocity_sub`: linearity, so all bounds apply to differences.

## How it works

The partial derivatives of `u` are the principal-value formulas `halfPlaneVelocityGradient`
(`partialDeriv_halfPlaneVelocity`), so the entry bounds are `abs_halfPlaneVelocityGradient_sub_le`,
`abs_halfPlaneVelocityGradient_le` and `abs_halfPlaneVelocityGradient_le_log`, in which the mass of
the even reflection is `2L` (`integral_abs_evenReflection`). The bounds of `Du` as a linear map add
the four entries (`norm_le_sum_abs_apply`). For `norm_fderiv_halfPlaneVelocity_sub_le` we drop the
continuity hypothesis: the Hölder bound makes `ω` continuous on the closed half-plane, and its even
reflection is continuous and has the same velocity (`halfPlaneVelocity_evenReflection`). The
seminorm form applies the pointwise Hölder estimate with `M` the seminorm of `ω` when that is
finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open GreenFunction PotentialTheory.Planar SobolevSpace

namespace IncompressibleFlow

variable {ω : ℝ^2 → ℝ} {M α B : ℝ}

/-- The operator norm of a linear map of the plane is at most the sum of the absolute values of
its four entries `(L eᵢ)ₖ`. -/
theorem norm_le_sum_abs_apply (L : ℝ^2 →L[ℝ] ℝ^2) :
    ‖L‖ ≤ ∑ i : Fin 2, ∑ k : Fin 2, |L (EuclideanSpace.single i 1) k| :=
  L.norm_le_sum_norm_apply_single.trans
    (Finset.sum_le_sum fun _ _ ↦ EuclideanSpace.norm_le_sum_abs _)

section Estimates

variable (hω : Continuous ω) (hc : HasCompactSupport ω)
include hω hc

/-- **Hölder estimate of the velocity gradient up to the boundary.** For a continuous compactly
supported vorticity with `|ω(y) - ω(z)| ≤ M |y - z|^α` on the closed upper half-plane,
`0 < α < 1`, `|∂ᵢuₖ(x) - ∂ᵢuₖ(x')| ≤ 211/(α(1-α)) · M |x - x'|^α` for `x, x'` in the open upper
half-plane. -/
theorem abs_partialDeriv_halfPlaneVelocity_sub_le (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) (i k : Fin 2)
    {x x' : ℝ^2} (hx : x ∈ HalfSpace.upper 2) (hx' : x' ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x'| ≤
      211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  rw [partialDeriv_halfPlaneVelocity hω hc hα hα1.le hM i k hx,
    partialDeriv_halfPlaneVelocity hω hc hα hα1.le hM i k hx']
  exact abs_halfPlaneVelocityGradient_sub_le hα hα1 hM
    (integrable_evenReflection hω hc) i k hx hx'

/-- **Size of the velocity gradient.** With `|ω| ≤ B` on the closed upper half-plane and
`L = ∫_{ℝ²₊} |ω|`, `|∂ᵢuₖ(x)| ≤ 50M/α + 8B + 10L` in the open upper half-plane. -/
theorem abs_partialDeriv_halfPlaneVelocity_le (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) (i k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x| ≤
      50 * M / α + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |ω y| := by
  rw [partialDeriv_halfPlaneVelocity hω hc hα hα1 hM i k hx]
  have h := abs_halfPlaneVelocityGradient_le hα hα1 hM
    (integrable_evenReflection hω hc) hB i k hx
  rw [integral_abs_evenReflection hω hc] at h
  linarith

/-- **Kato-type bound of the velocity gradient.** With `|ω| ≤ B` on the closed upper
half-plane and `L = ∫_{ℝ²₊} |ω|`, `|∂ᵢuₖ(x)| ≤ (50/α)(1 + B log(2 + M)) + 8B + 10L` in the open
upper half-plane. The Hölder constant enters only through the logarithm. -/
theorem abs_partialDeriv_halfPlaneVelocity_le_log (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) (i k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x| ≤
      50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |ω y| := by
  rw [partialDeriv_halfPlaneVelocity hω hc hα hα1 hM i k hx]
  have h := abs_halfPlaneVelocityGradient_le_log hα hα1 hM
    (integrable_evenReflection hω hc) hB i k hx
  rw [integral_abs_evenReflection hω hc] at h
  linarith

/-- The entries of the derivative of the velocity are its partial derivatives. -/
theorem fderiv_halfPlaneVelocity_apply (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) (i k : Fin 2) :
    fderiv ℝ (halfPlaneVelocity ω) x (EuclideanSpace.single i 1) k =
      (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x := by
  have hd := differentiableAt_halfPlaneVelocity hω hc hα hα1 hM hx
  have hcomp : (fun y ↦ halfPlaneVelocity ω y k) =
      (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ) ∘ halfPlaneVelocity ω := rfl
  have h := ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change _ = fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x (EuclideanSpace.single i 1)
  rw [hcomp, h]
  rfl

/-- **The derivative as a linear map.** In the open upper half-plane the operator norm of the
derivative of the velocity is at most the sum of the absolute values of its four partials. -/
theorem norm_fderiv_halfPlaneVelocity_le (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (halfPlaneVelocity ω) x‖ ≤
      ∑ i : Fin 2, ∑ k : Fin 2, |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x| := by
  refine (norm_le_sum_abs_apply _).trans (le_of_eq ?_)
  simp only [fderiv_halfPlaneVelocity_apply hω hc hα hα1 hM hx]

/-- **Kato-type bound of the derivative.** In the open upper half-plane,
`‖Du(x)‖ ≤ 4((50/α)(1 + B log(2 + M)) + 8B + 10L)`. -/
theorem norm_fderiv_halfPlaneVelocity_le_log (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (halfPlaneVelocity ω) x‖ ≤
      4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
        10 * ∫ y in HalfSpace.upper 2, |ω y|) := by
  refine (norm_fderiv_halfPlaneVelocity_le hω hc hα hα1 hM hx).trans ?_
  have h := fun i k ↦ abs_partialDeriv_halfPlaneVelocity_le_log hω hc hα hα1 hM hB i k hx
  simp only [Fin.sum_univ_two]
  linarith [h 0 0, h 0 1, h 1 0, h 1 1]

/-- **Size bound of the derivative.** In the open upper half-plane,
`‖Du(x)‖ ≤ 4(50M/α + 8B + 10L)`. -/
theorem norm_fderiv_halfPlaneVelocity_le_holder (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (halfPlaneVelocity ω) x‖ ≤
      4 * (50 * M / α + 8 * B + 10 * ∫ y in HalfSpace.upper 2, |ω y|) := by
  refine (norm_fderiv_halfPlaneVelocity_le hω hc hα hα1 hM hx).trans ?_
  have h := fun i k ↦ abs_partialDeriv_halfPlaneVelocity_le hω hc hα hα1 hM hB i k hx
  simp only [Fin.sum_univ_two]
  linarith [h 0 0, h 0 1, h 1 0, h 1 1]

/-- `norm_fderiv_halfPlaneVelocity_sub_le` for a continuous vorticity. -/
private theorem norm_fderiv_halfPlaneVelocity_sub_le_of_continuous (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) {x x' : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) (hx' : x' ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (halfPlaneVelocity ω) x - fderiv ℝ (halfPlaneVelocity ω) x'‖ ≤
      844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  refine (norm_le_sum_abs_apply _).trans ?_
  have hentry : ∀ i k : Fin 2, (fderiv ℝ (halfPlaneVelocity ω) x -
      fderiv ℝ (halfPlaneVelocity ω) x') (EuclideanSpace.single i 1) k =
      (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x' := by
    intro i k
    rw [sub_apply, PiLp.sub_apply,
      fderiv_halfPlaneVelocity_apply hω hc hα hα1.le hM hx,
      fderiv_halfPlaneVelocity_apply hω hc hα hα1.le hM hx']
  simp only [hentry, Fin.sum_univ_two]
  have h := fun i k ↦ abs_partialDeriv_halfPlaneVelocity_sub_le hω hc hα hα1 hM i k hx hx'
  have e : 844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α =
      4 * (211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α) := by ring
  linarith [h 0 0, h 0 1, h 1 0, h 1 1]

omit hω in
/-- **Hölder estimate of the derivative as a linear map.** For `0 < α < 1` and `x, x'` in the
open upper half-plane, `‖Du(x) - Du(x')‖ ≤ 844/(α(1-α)) · M |x - x'|^α`. The Hölder bound makes
`ω` continuous on the closed half-plane, and the velocity is unchanged when `ω` is replaced by
its even reflection, which is continuous. -/
theorem norm_fderiv_halfPlaneVelocity_sub_le (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) {x x' : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) (hx' : x' ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (halfPlaneVelocity ω) x - fderiv ℝ (halfPlaneVelocity ω) x'‖ ≤
      844 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  have hcont : ContinuousOn ω {y : ℝ^2 | 0 ≤ y 1} := by
    intro y hy
    have hlim : Tendsto (fun z ↦ M * ‖z - y‖ ^ α) (𝓝[{y : ℝ^2 | 0 ≤ y 1}] y) (𝓝 0) := by
      have h : Tendsto (fun z ↦ M * ‖z - y‖ ^ α) (𝓝 y) (𝓝 (M * ‖y - y‖ ^ α)) :=
        (((continuous_id.sub continuous_const).norm.rpow_const
          fun _ ↦ Or.inr hα.le).tendsto y).const_mul M
      simpa [Real.zero_rpow hα.ne'] using h.mono_left nhdsWithin_le_nhds
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim)
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Real.norm_eq_abs]
    exact hM z y hz hy
  have hME : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |PDE.Analysis.evenReflection ω y - PDE.Analysis.evenReflection ω z| ≤ M * ‖y - z‖ ^ α :=
    fun y z hy hz ↦ by
      rw [PDE.Analysis.evenReflection_of_nonneg hy, PDE.Analysis.evenReflection_of_nonneg hz]
      exact hM y z hy hz
  rw [← halfPlaneVelocity_evenReflection ω]
  exact norm_fderiv_halfPlaneVelocity_sub_le_of_continuous
    (PDE.Analysis.continuous_evenReflection hcont)
    (PDE.Analysis.hasCompactSupport_evenReflection hc) hα hα1 hME hx hx'

omit hω in
/-- **The derivative is Hölder on the open upper half-plane** as a map into linear maps, with
constant `844/(α(1-α)) · M`. -/
theorem holderOnWith_fderiv_halfPlaneVelocity {α M : NNReal} (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ (α : ℝ)) :
    HolderOnWith (Real.toNNReal (844 / (α * (1 - α))) * M) α
      (fderiv ℝ (halfPlaneVelocity ω)) (HalfSpace.upper 2) := by
  intro x hx x' hx'
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  have hpos : 0 ≤ 844 / ((α : ℝ) * (1 - α)) := by
    have : 0 < (α : ℝ) * (1 - α) := mul_pos hα' (by linarith)
    positivity
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hpos]
  exact norm_fderiv_halfPlaneVelocity_sub_le hc hα' hα1' hM hx hx'

/-- **Divergence and vorticity.** In the open upper half-plane the velocity gradient satisfies
`∂₀u₀ + ∂₁u₁ = 0` and `∂₁u₀ - ∂₀u₁ = ω` (clockwise vorticity). -/
theorem partialDeriv_halfPlaneVelocity_div_curl (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    (∂[(0 : Fin 2)] (fun y ↦ halfPlaneVelocity ω y 0)) x +
        (∂[(1 : Fin 2)] (fun y ↦ halfPlaneVelocity ω y 1)) x = 0 ∧
      (∂[(1 : Fin 2)] (fun y ↦ halfPlaneVelocity ω y 0)) x -
        (∂[(0 : Fin 2)] (fun y ↦ halfPlaneVelocity ω y 1)) x = ω x := by
  simp only [partialDeriv_halfPlaneVelocity hω hc hα hα1 hM _ _ hx, halfPlaneVelocityGradient]
  constructor <;> ring

omit hω hc in
/-- A metric Hölder bound `dist (g x) (g y) ≤ K dist(x, y)^γ` on `s` gives
`HolderOnWith K γ g s`. -/
private theorem holderOnWith_of_dist_le {s : Set (ℝ^2)} {g : ℝ^2 → ℝ} {K γ : NNReal}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) ≤ K * dist x y ^ (γ : ℝ)) :
    HolderOnWith K γ g s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.coe_nonneg,
    ENNReal.coe_nnreal_eq K, ← ENNReal.ofReal_mul K.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- **The velocity gradient is Hölder on the open upper half-plane**, in Mathlib's
`HolderOnWith` form: with `[ω]_α ≤ M` on the closed half-plane, every partial `∂ᵢuₖ` is
`α`-Hölder on `ℝ²₊` with constant `211/(α(1-α)) · M`. -/
theorem holderOnWith_partialDeriv_halfPlaneVelocity {α M : NNReal} (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ (α : ℝ)) (i k : Fin 2) :
    HolderOnWith (Real.toNNReal (211 / (α * (1 - α))) * M) α
      (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) (HalfSpace.upper 2) := by
  refine holderOnWith_of_dist_le fun x hx x' hx' ↦ ?_
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ (by
    have : 0 < (α : ℝ) * (1 - α) := mul_pos hα' (by linarith)
    positivity)]
  exact abs_partialDeriv_halfPlaneVelocity_sub_le hω hc hα' hα1' hM i k hx hx'

/-- **The `C^α` estimate of the velocity gradient** in the form
`‖∇u‖_{C^α} ≤ C (‖ω‖_{C^α} + ‖ω‖_{L¹ ∩ L^∞})`: with `C = 211/(α(1-α))`, both the size of
`∂ᵢuₖ` on the open upper half-plane and its `α`-Hölder constant there are at most
`C (M + B + L)`. -/
theorem partialDeriv_halfPlaneVelocity_holder_norm_le (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) (i k : Fin 2) :
    (∀ x ∈ HalfSpace.upper 2, |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x| ≤
      211 / (α * (1 - α)) * (M + B + ∫ y in HalfSpace.upper 2, |ω y|)) ∧
    (∀ x ∈ HalfSpace.upper 2, ∀ x' ∈ HalfSpace.upper 2,
      |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x'| ≤
        211 / (α * (1 - α)) * (M + B + ∫ y in HalfSpace.upper 2, |ω y|) * ‖x - x'‖ ^ α) := by
  have hM0 : 0 ≤ M := by
    have h := hM !₂[1, 0] 0 (by simp) (by simp)
    rw [sub_zero, ← Real.sqrt_sq (norm_nonneg _), norm_sq_vec] at h
    norm_num at h
    exact (abs_nonneg _).trans h
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl)
  have hL0 : 0 ≤ ∫ y in HalfSpace.upper 2, |ω y| :=
    setIntegral_nonneg (HalfSpace.measurableSet_upper (n := 2)) fun y _ ↦ abs_nonneg _
  have h1α : 0 < 1 - α := by linarith
  have hαα : 0 < α * (1 - α) := mul_pos hα h1α
  have hαα1 : α * (1 - α) ≤ 1 / 4 := by nlinarith [sq_nonneg (α - 1 / 2)]
  have hC : 50 / α ≤ 211 / (α * (1 - α)) := by
    rw [div_le_div_iff₀ hα hαα]; nlinarith
  have hC1 : 10 ≤ 211 / (α * (1 - α)) := by
    rw [le_div_iff₀ hαα]; nlinarith
  refine ⟨fun x hx ↦ ?_, fun x hx x' hx' ↦ ?_⟩
  · refine (abs_partialDeriv_halfPlaneVelocity_le hω hc hα hα1.le hM hB i k hx).trans ?_
    have e : 50 * M / α = 50 / α * M := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hC hM0, mul_le_mul_of_nonneg_right hC1 hB0,
      mul_le_mul_of_nonneg_right hC1 hL0]
  · refine (abs_partialDeriv_halfPlaneVelocity_sub_le hω hc hα hα1 hM i k hx hx').trans ?_
    have hδ : 0 ≤ ‖x - x'‖ ^ α := by positivity
    have : M ≤ M + B + ∫ y in HalfSpace.upper 2, |ω y| := by linarith
    gcongr

/-- The partials of the velocity are continuous on the open upper half-plane. -/
theorem continuousOn_partialDeriv_halfPlaneVelocity (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) (i k : Fin 2) :
    ContinuousOn (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) (HalfSpace.upper 2) := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hC : 0 < 211 / (α * (1 - α)) * (|M| + 1) := by
    have : 0 < α * (1 - α) := mul_pos hα (by linarith)
    positivity
  refine ⟨(ε / (211 / (α * (1 - α)) * (|M| + 1))) ^ (1 / α), by positivity, fun y hy hyx ↦ ?_⟩
  have hb := abs_partialDeriv_halfPlaneVelocity_sub_le hω hc hα hα1 hM i k hy hx
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hyx
  have hpow : ‖y - x‖ ^ α < ε / (211 / (α * (1 - α)) * (|M| + 1)) := by
    have := Real.rpow_lt_rpow (norm_nonneg _) hyx hα
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at this
  calc _ ≤ 211 / (α * (1 - α)) * M * ‖y - x‖ ^ α := hb
    _ ≤ 211 / (α * (1 - α)) * (|M| + 1) * ‖y - x‖ ^ α := by
        have : 0 ≤ 211 / (α * (1 - α)) := by
          have : 0 < α * (1 - α) := mul_pos hα (by linarith)
          positivity
        gcongr
        linarith [le_abs_self M]
    _ < 211 / (α * (1 - α)) * (|M| + 1) * (ε / (211 / (α * (1 - α)) * (|M| + 1))) := by
        gcongr
    _ = ε := by field_simp

omit hω hc in
/-- **Linearity of the velocity gradient.** For two continuous compactly supported vorticities,
`α`-Hölder on the closed upper half-plane, the gradient of `u(f - g)` is the difference of the
gradients in the open upper half-plane; the estimates above therefore bound
`∂ᵢuₖ(f) - ∂ᵢuₖ(g)` by the norms of `f - g`. -/
theorem partialDeriv_halfPlaneVelocity_sub {f g : ℝ^2 → ℝ} {Mf Mg : ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (hα : 0 < α)
    (hα1 : α ≤ 1) (hMf : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ Mf * ‖y - z‖ ^ α)
    (hMg : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ Mg * ‖y - z‖ ^ α) (i k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    (∂[i] (fun y ↦ halfPlaneVelocity (f - g) y k)) x =
      (∂[i] (fun y ↦ halfPlaneVelocity f y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity g y k)) x := by
  have hMfg : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |(f - g) y - (f - g) z| ≤ (Mf + Mg) * ‖y - z‖ ^ α := by
    intro y z hy hz
    have e : (f - g) y - (f - g) z = (f y - f z) - (g y - g z) := by simp only [Pi.sub_apply]; ring
    rw [e]
    have := abs_sub (f y - f z) (g y - g z)
    linarith [hMf y z hy hz, hMg y z hy hz]
  rw [partialDeriv_halfPlaneVelocity (hf.sub hg) (hfc.sub hgc) hα hα1 hMfg i k hx,
    partialDeriv_halfPlaneVelocity hf hfc hα hα1 hMf i k hx,
    partialDeriv_halfPlaneVelocity hg hgc hα hα1 hMg i k hx,
    halfPlaneVelocityGradient_sub hα hMf hMg (integrable_evenReflection hf hfc)
      (integrable_evenReflection hg hgc) i k hx]

/-- **The homogeneous Hölder estimate in seminorm form.** With the Hölder seminorm
`[f]_{C^α(D)} = HolderSpace.weightedSeminorm (‖·‖^(-α)) D f`,
`[∂ᵢuₖ]_{C^α(ℝ²₊)} ≤ 211/(α(1-α)) · [ω]_{C^α(closed ℝ²₊)}` for `0 < α < 1`. -/
theorem weightedSeminorm_partialDeriv_halfPlaneVelocity_le (hα : 0 < α) (hα1 : α < 1)
    (i k : Fin 2) :
    HolderSpace.weightedSeminorm (fun h : ℝ^2 ↦ ‖h‖ ^ (-α)) (HalfSpace.upper 2)
        (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) ≤
      ENNReal.ofReal (211 / (α * (1 - α))) *
        HolderSpace.weightedSeminorm (fun h : ℝ^2 ↦ ‖h‖ ^ (-α)) {y : ℝ^2 | 0 ≤ y 1} ω := by
  set S := HolderSpace.weightedSeminorm (fun h : ℝ^2 ↦ ‖h‖ ^ (-α)) {y : ℝ^2 | 0 ≤ y 1} ω
  have hC : 0 < 211 / (α * (1 - α)) := by
    have : 0 < α * (1 - α) := mul_pos hα (by linarith)
    positivity
  rcases eq_or_ne S ⊤ with hS | hS
  · rw [hS, ENNReal.mul_top (by simpa using hC)]
    exact le_top
  -- the Hölder bound with constant `S.toReal`
  have hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ S.toReal * ‖y - z‖ ^ α := by
    intro y z hy hz
    rcases eq_or_ne y z with rfl | hyz
    · simp only [sub_self, abs_zero, norm_zero]
      rw [Real.zero_rpow hα.ne']
      simp
    have hn : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
    have h := HolderSpace.dist_mul_le_weightedSeminorm (g := fun h : ℝ^2 ↦ ‖h‖ ^ (-α))
      (D := {y : ℝ^2 | 0 ≤ y 1}) (f := ω) hS hy hz
    rw [Real.dist_eq, Real.rpow_neg hn.le, ← div_eq_mul_inv,
      div_le_iff₀ (Real.rpow_pos_of_pos hn α)] at h
    exact h
  refine HolderSpace.weightedSeminorm_le_iff.2 fun x hx x' hx' ↦ ?_
  have hb := abs_partialDeriv_halfPlaneVelocity_sub_le hω hc hα hα1 hM i k hx hx'
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_mul (abs_nonneg _)]
  rcases eq_or_ne x x' with rfl | hxx'
  · simp
  have hn : 0 < ‖x - x'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  calc ENNReal.ofReal (|(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x -
        (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x'| * ‖x - x'‖ ^ (-α))
      ≤ ENNReal.ofReal (211 / (α * (1 - α)) * S.toReal) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.rpow_neg hn.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hn α)]
        linarith
    _ = ENNReal.ofReal (211 / (α * (1 - α))) * S := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hS]

end Estimates

end IncompressibleFlow

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BiotSavart
public import PDE.Elliptic.Classical.Harmonic.Reflection
import PDE.FDeriv.Reflection.Coordinate
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Green gradients of product sources and the `C¹` odd reflection

If `u` is `C¹` and vanishes on the hyperplane `{x | x k = 0}`, its odd reflection
`oddReflection k u` (`u` on `{0 ≤ x k}`, `-u ∘ Rₖ` elsewhere) is `C¹`: on the hyperplane the
tangential derivatives of `u` vanish, so the one-sided derivatives `Du(x)` and `-Du(x) ∘ Rₖ`
agree.

In the plane, with `U = oddReflection 1 u`, the odd extension across the boundary of a product
source `∂ⱼu · h` is `∂ⱼU · h` off the boundary line, provided `h ∘ R₁ = h` for `j = 0` and
`h ∘ R₁ = -h` for `j = 1`. If moreover `h` is `C¹`, compactly supported and vanishes on a disc
around the point `x`, the kernel `y ↦ gⱼ(x - y) h(y)` is `C¹` and an integration by parts over the
whole plane moves the derivative onto it:

`∂ᵢ G[∂ⱼu · h](x) = ∫ U(y) (kᵢⱼ(x - y)/π · h(y) - gᵢ(x - y) ∂ⱼh(y)) dy`,

with `gᵢ = gradientKernel i` and `kᵢⱼ = hessianKernel i j`. No boundary term appears: `U` is `C¹`
across the line because `u` vanishes there. This is the integration by parts in the proof of
Chen and Hou I, Section 6.2.3, Proposition 6.6, for the term `∇(-Δ)⁻¹(∇φ† · ∇χ₁)`.

## Main results

* `contDiff_one_oddReflection`: the odd reflection of a `C¹` function vanishing on the hyperplane
  `{x k = 0}` is `C¹`.
* `hasFDerivAt_oddReflection_of_nonneg`: on the closed half-space `{0 ≤ x k}` its derivative is
  `Du(x)`, also on the hyperplane.
* `partialDeriv_oddReflection_of_neg`: on the open negative half-space
  `∂ₖ(oddReflection k u)(x) = ∂ₖu(Rₖ x)` and `∂ⱼ(oddReflection k u)(x) = -∂ⱼu(Rₖ x)` for `j ≠ k`.
* `oddHalfSpaceExtension_partialDeriv_mul_ae_eq`: the odd extension of `∂ⱼu · h` is
  `∂ⱼ(oddReflection 1 u) · h` off the boundary line.
* `partialDeriv_gradientKernel_sub_mul`: `∂ⱼ` of `y ↦ gᵢ(x - y) h(y)` is
  `-(kᵢⱼ(x - y)/π · h(y) - gᵢ(x - y) ∂ⱼh(y))` when `h` vanishes on a disc around `x`.
* `partialDeriv_halfSpaceGreenPotential_partialDeriv_mul`:
  `∂ᵢ G[∂ⱼu · h](x) = ∫ U(y) (kᵢⱼ(x - y)/π · h(y) - gᵢ(x - y) ∂ⱼh(y)) dy`.
* `partialDeriv_halfSpaceGreenPotential_mul`: `∂ᵢ G[u · h](x) = ∫ gᵢ(x - y) U(y) h(y) dy` for `h`
  even in `y₁`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.2.3, Proposition 6.6.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set SobolevSpace PotentialTheory.Planar

local notation "𝐑" => PDE.Common.coordinateReflection

namespace PDE.Common

variable {n : ℕ}

/-- The odd reflection agrees with the function on the closed half-space. -/
theorem oddReflection_of_nonneg (k : Fin n) (g : ℝ^n → ℝ) {x : ℝ^n} (hx : 0 ≤ x k) :
    oddReflection k g x = g x := by
  simp [oddReflection, hx]

/-- The odd reflection is `-g ∘ Rₖ` on the open negative half-space. -/
theorem oddReflection_of_neg (k : Fin n) (g : ℝ^n → ℝ) {x : ℝ^n} (hx : x k < 0) :
    oddReflection k g x = -g (𝐑 k x) := by
  simp [oddReflection, not_le.mpr hx]

/-- Near a point of the open positive half-space the odd reflection is the function itself. -/
theorem oddReflection_eventuallyEq_of_pos (k : Fin n) (g : ℝ^n → ℝ) {x : ℝ^n} (hx : 0 < x k) :
    oddReflection k g =ᶠ[𝓝 x] g := by
  have hc : Continuous fun y : ℝ^n ↦ y k := (EuclideanSpace.proj k).continuous
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  exact oddReflection_of_nonneg k g hy.le

/-- Near a point of the open negative half-space the odd reflection is `-g ∘ Rₖ`. -/
theorem oddReflection_eventuallyEq_of_neg (k : Fin n) (g : ℝ^n → ℝ) {x : ℝ^n} (hx : x k < 0) :
    oddReflection k g =ᶠ[𝓝 x] fun y ↦ -g (𝐑 k y) := by
  have hc : Continuous fun y : ℝ^n ↦ y k := (EuclideanSpace.proj k).continuous
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hx)] with y hy
  exact oddReflection_of_neg k g hy

/-- The coordinate reflection as a continuous linear map. -/
private def reflectionCLM (k : Fin n) : ℝ^n →L[ℝ] ℝ^n :=
  (coordinateReflectionLinearIsometryEquiv k).toContinuousLinearEquiv.toContinuousLinearMap

/-- `reflectionCLM k` acts as the coordinate reflection `𝐑 k`. -/
private theorem reflectionCLM_apply (k : Fin n) (v : ℝ^n) : reflectionCLM k v = 𝐑 k v :=
  rfl

/-- At a point of the hyperplane where `u` vanishes identically on the hyperplane, the
derivative of `u` is odd under the reflection. -/
private theorem fderiv_apply_coordinateReflection {k : Fin n} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) (hx : x k = 0)
    (v : ℝ^n) : fderiv ℝ u x (𝐑 k v) = -fderiv ℝ u x v := by
  set w : ℝ^n := 𝐑 k v + v
  have hw : w k = 0 := by simp [w]
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hcomp : HasDerivAt (fun t : ℝ ↦ u (x + t • w)) (fderiv ℝ u x w) 0 :=
    hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hzero : (fun t : ℝ ↦ u (x + t • w)) = fun _ ↦ 0 := by
    funext t
    exact hb _ (by simp [hx, hw])
  rw [hzero] at hcomp
  have h0 : fderiv ℝ u x w = 0 := hcomp.unique (hasDerivAt_const 0 0)
  have hsum : fderiv ℝ u x (𝐑 k v) + fderiv ℝ u x v = 0 := by
    rw [← map_add]; exact h0
  linarith

/-- On the hyperplane the two one-sided derivatives of the odd reflection agree. -/
private theorem neg_fderiv_comp_reflection {k : Fin n} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) (hx : x k = 0) :
    -(fderiv ℝ u (𝐑 k x)).comp (reflectionCLM k) = fderiv ℝ u x := by
  have hRx : 𝐑 k x = x := (coordinateReflection_eq_self_iff k x).mpr hx
  ext v
  change -(fderiv ℝ u (𝐑 k x) (reflectionCLM k v)) = fderiv ℝ u x v
  rw [reflectionCLM_apply, hRx, fderiv_apply_coordinateReflection hu hb hx v, neg_neg]

/-- The derivative of `-u ∘ Rₖ`. -/
private theorem hasFDerivAt_neg_comp_reflection {k : Fin n} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u (𝐑 k x)) :
    HasFDerivAt (fun y ↦ -u (𝐑 k y)) (-(fderiv ℝ u (𝐑 k x)).comp (reflectionCLM k)) x := by
  have h := hu.hasFDerivAt.comp x (reflectionCLM k).hasFDerivAt
  exact h.neg

/-- A within-derivative on each of two closed sets covering the space is a derivative. -/
private theorem hasFDerivAt_of_isClosed_cover {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {A B : Set E} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : A ∪ B = univ) {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hfA : x ∈ A → HasFDerivWithinAt f f' A x) (hfB : x ∈ B → HasFDerivWithinAt f f' B x) :
    HasFDerivAt f f' x := by
  have h1 : HasFDerivWithinAt f f' A x := by
    by_cases hx : x ∈ A
    · exact hfA hx
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hA.closure_eq])
  have h2 : HasFDerivWithinAt f f' B x := by
    by_cases hx : x ∈ B
    · exact hfB hx
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hB.closure_eq])
  rw [← hasFDerivWithinAt_univ, ← hAB]
  exact h1.union h2

/-- **The odd reflection on the closed half-space.** If `u` is differentiable and vanishes on
the hyperplane `{x k = 0}`, then at every point with `0 ≤ x k` the odd reflection has the
derivative `Du(x)`, including the points of the hyperplane. -/
theorem hasFDerivAt_oddReflection_of_nonneg {k : Fin n} {u : ℝ^n → ℝ}
    (hu : Differentiable ℝ u) (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) {x : ℝ^n}
    (hx : 0 ≤ x k) : HasFDerivAt (oddReflection k u) (fderiv ℝ u x) x := by
  have hc : Continuous fun y : ℝ^n ↦ y k := (EuclideanSpace.proj k).continuous
  refine hasFDerivAt_of_isClosed_cover (A := {y : ℝ^n | 0 ≤ y k}) (B := {y : ℝ^n | y k ≤ 0})
    (isClosed_le continuous_const hc) (isClosed_le hc continuous_const)
    (by ext y; simp [le_total]) (fun _ ↦ ?_) (fun hxB ↦ ?_)
  · exact (hu x).hasFDerivAt.hasFDerivWithinAt.congr
      (fun y hy ↦ oddReflection_of_nonneg k u hy) (oddReflection_of_nonneg k u hx)
  · have hx0 : x k = 0 := le_antisymm hxB hx
    have hRx : 𝐑 k x = x := (coordinateReflection_eq_self_iff k x).mpr hx0
    have h := (hasFDerivAt_neg_comp_reflection (k := k) (x := x) (hu (𝐑 k x))).hasFDerivWithinAt
      (s := {y | y k ≤ 0})
    rw [neg_fderiv_comp_reflection (hu x) hb hx0] at h
    refine h.congr (fun y hy ↦ ?_) ?_
    · rcases (show y k ≤ 0 from hy).lt_or_eq with hlt | heq
      · exact oddReflection_of_neg k u hlt
      · have hRy : 𝐑 k y = y := (coordinateReflection_eq_self_iff k y).mpr heq
        change oddReflection k u y = -u (𝐑 k y)
        rw [oddReflection_of_nonneg k u heq.ge, hRy, hb y heq, neg_zero]
    · rw [oddReflection_of_nonneg k u hx, hRx, hb x hx0, neg_zero]

/-- The odd reflection of a differentiable function vanishing on the hyperplane is
differentiable. -/
theorem differentiable_oddReflection {k : Fin n} {u : ℝ^n → ℝ} (hu : Differentiable ℝ u)
    (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) : Differentiable ℝ (oddReflection k u) := by
  intro x
  rcases le_or_gt 0 (x k) with hx | hx
  · exact (hasFDerivAt_oddReflection_of_nonneg hu hb hx).differentiableAt
  · exact ((hasFDerivAt_neg_comp_reflection (hu (𝐑 k x))).differentiableAt).congr_of_eventuallyEq
      (oddReflection_eventuallyEq_of_neg k u hx)

/-- **The `C¹` odd reflection.** If `u` is `C¹` and vanishes on the hyperplane `{x k = 0}`,
its odd reflection is `C¹` on the whole space. -/
theorem contDiff_one_oddReflection {k : Fin n} {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u)
    (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) : ContDiff ℝ 1 (oddReflection k u) := by
  have hd : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hD : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hc : Continuous fun y : ℝ^n ↦ y k := (EuclideanSpace.proj k).continuous
  refine contDiff_one_iff_hasFDerivAt.mpr
    ⟨fun x ↦ if (fun _ ↦ (0 : ℝ)) x ≤ (fun y : ℝ^n ↦ y k) x then fderiv ℝ u x
      else -(fderiv ℝ u (𝐑 k x)).comp (reflectionCLM k), ?_, fun x ↦ ?_⟩
  · refine Continuous.if_le hD ?_ continuous_const hc fun x hx ↦ ?_
    · exact ((hD.comp (reflectionCLM k).continuous).clm_comp continuous_const).neg
    · exact (neg_fderiv_comp_reflection (hd x) hb hx.symm).symm
  · by_cases hx : 0 ≤ x k
    · simp only [hx, ite_true]
      exact hasFDerivAt_oddReflection_of_nonneg hd hb hx
    · simp only [hx, ite_false]
      exact (hasFDerivAt_neg_comp_reflection (hd (𝐑 k x))).congr_of_eventuallyEq
        (oddReflection_eventuallyEq_of_neg k u (not_le.mp hx))

/-- The partial derivatives of the odd reflection on the closed half-space are those of `u`. -/
theorem partialDeriv_oddReflection_of_nonneg {k : Fin n} {u : ℝ^n → ℝ}
    (hu : Differentiable ℝ u) (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) {x : ℝ^n}
    (hx : 0 ≤ x k) (j : Fin n) : (∂[j] (oddReflection k u)) x = (∂[j] u) x := by
  simp only [PDE.partialDeriv, (hasFDerivAt_oddReflection_of_nonneg hu hb hx).fderiv]

/-- The partial derivatives of the odd reflection on the open negative half-space:
`∂ₖ(oddReflection k u)(x) = ∂ₖu(Rₖ x)` and `∂ⱼ(oddReflection k u)(x) = -∂ⱼu(Rₖ x)` for
`j ≠ k`. -/
theorem partialDeriv_oddReflection_of_neg {k : Fin n} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u (𝐑 k x)) (hx : x k < 0) (j : Fin n) :
    (∂[j] (oddReflection k u)) x =
      if j = k then (∂[j] u) (𝐑 k x) else -(∂[j] u) (𝐑 k x) := by
  have h := (oddReflection_eventuallyEq_of_neg k u hx).fderiv_eq (𝕜 := ℝ)
  have hneg : (∂[j] (fun y ↦ -u (𝐑 k y))) x = -(∂[j] (fun y ↦ u (𝐑 k y))) x := by
    simp only [PDE.partialDeriv]
    rw [show (fun y ↦ -u (𝐑 k y)) = -(fun y ↦ u (𝐑 k y)) from rfl, fderiv_neg]
    rfl
  have hval : (∂[j] (oddReflection k u)) x = (∂[j] (fun y ↦ -u (𝐑 k y))) x := by
    simp only [PDE.partialDeriv, h]
  rw [hval, hneg]
  split_ifs with hj
  · subst hj
    rw [partialDeriv_comp_coordinateReflection_same j u x hu, neg_neg]
  · rw [partialDeriv_comp_coordinateReflection_of_ne k j hj u x hu]

/-- The odd reflection is odd under the reflection it is built from, at every point when the
function vanishes on the hyperplane. -/
theorem oddReflection_coordinateReflection_self (k : Fin n) {u : ℝ^n → ℝ}
    (hb : ∀ y : ℝ^n, y k = 0 → u y = 0) (x : ℝ^n) :
    oddReflection k u (𝐑 k x) = -oddReflection k u x := by
  rcases lt_trichotomy (x k) 0 with hx | hx | hx
  · have hRx : 0 ≤ (𝐑 k x) k := by rw [coordinateReflection_apply_same]; linarith
    rw [oddReflection_of_nonneg k u hRx, oddReflection_of_neg k u hx, neg_neg]
  · have hRx : 𝐑 k x = x := (coordinateReflection_eq_self_iff k x).mpr hx
    rw [hRx, oddReflection_of_nonneg k u hx.ge, hb x hx, neg_zero]
  · have hRx : (𝐑 k x) k < 0 := by rw [coordinateReflection_apply_same]; linarith
    rw [oddReflection_of_neg k u hRx, coordinateReflection_involutive k x,
      oddReflection_of_nonneg k u hx.le]

/-- Two coordinate reflections commute. -/
private theorem coordinateReflection_comm (j k : Fin n) (x : ℝ^n) :
    𝐑 j (𝐑 k x) = 𝐑 k (𝐑 j x) := by
  ext l
  by_cases hj : l = j <;> by_cases hk : l = k
  · subst hj; subst hk; rfl
  · subst hj
    simp [coordinateReflection_apply_of_ne k l hk]
  · subst hk
    simp [coordinateReflection_apply_of_ne j l hj]
  · simp [coordinateReflection_apply_of_ne k l hk, coordinateReflection_apply_of_ne j l hj]

/-- Oddness in a second coordinate `j ≠ k` on the closed half-space `{0 ≤ x k}` passes to the
odd reflection on the whole space. -/
theorem oddReflection_coordinateReflection_of_ne {j k : Fin n} (hjk : j ≠ k) {u : ℝ^n → ℝ}
    (hodd : ∀ y : ℝ^n, 0 ≤ y k → u (𝐑 j y) = -u y) (x : ℝ^n) :
    oddReflection k u (𝐑 j x) = -oddReflection k u x := by
  have hRj : (𝐑 j x) k = x k := coordinateReflection_apply_of_ne j k hjk.symm x
  rcases le_or_gt 0 (x k) with hx | hx
  · rw [oddReflection_of_nonneg k u (hRj ▸ hx), oddReflection_of_nonneg k u hx, hodd x hx]
  · have hRk : 0 ≤ (𝐑 k x) k := by rw [coordinateReflection_apply_same]; linarith
    rw [oddReflection_of_neg k u (hRj ▸ hx), oddReflection_of_neg k u hx,
      coordinateReflection_comm k j, hodd _ hRk]

end PDE.Common

namespace GreenFunction

open PDE.Common

/-- Almost every point of the plane lies off the boundary line. -/
private theorem ae_ne_zero : ∀ᵐ y : ℝ^2, y 1 ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (HalfSpace.volume_boundary (n := 2))] with y hy
  exact hy

/-- The odd extension below the boundary line. -/
private theorem oddHalfSpaceExtension_of_neg (f : ℝ^2 → ℝ) {y : ℝ^2} (hy : y 1 < 0) :
    oddHalfSpaceExtension f y = -f (𝐑 1 y) := by
  have hyl : y ∈ HalfSpace.lower 2 := hy
  have hyu : y ∉ HalfSpace.upper 2 := fun h ↦ by
    have : (0 : ℝ) < y 1 := h
    linarith
  simp [oddHalfSpaceExtension, hyu, hyl, reflect_two_eq_coordinateReflection]

/-- **The odd extension of `∂ⱼu · h`.** If `u` is differentiable and `h ∘ R₁ = σ h` with `σ = 1`
for `j = 0` and `σ = -1` for `j = 1`, the odd extension of `∂ⱼu · h` across the boundary is
`∂ⱼ(oddReflection 1 u) · h` off the boundary line. -/
theorem oddHalfSpaceExtension_partialDeriv_mul_ae_eq (j : Fin 2) {u h : ℝ^2 → ℝ}
    (hu : Differentiable ℝ u) (hpar : ∀ y, h (𝐑 1 y) = (if j = 0 then 1 else -1) * h y) :
    oddHalfSpaceExtension (fun y ↦ (∂[j] u) y * h y) =ᵐ[volume]
      fun y ↦ (∂[j] (oddReflection 1 u)) y * h y := by
  filter_upwards [ae_ne_zero] with y hy
  rcases hy.lt_or_gt with hneg | hpos
  · rw [oddHalfSpaceExtension_of_neg _ hneg, partialDeriv_oddReflection_of_neg (hu _) hneg j,
      hpar y]
    fin_cases j <;> simp
  · rw [oddHalfSpaceExtension_eqOn _ (show y ∈ HalfSpace.upper 2 from hpos)]
    have h := (oddReflection_eventuallyEq_of_pos 1 u hpos).fderiv_eq (𝕜 := ℝ)
    simp only [PDE.partialDeriv, h]

/-- **The odd extension of `u · h`** for `h` even in `y₁`: it is `oddReflection 1 u · h` off the
boundary line. -/
theorem oddHalfSpaceExtension_mul_ae_eq {u h : ℝ^2 → ℝ} (hpar : ∀ y, h (𝐑 1 y) = h y) :
    oddHalfSpaceExtension (fun y ↦ u y * h y) =ᵐ[volume]
      fun y ↦ oddReflection 1 u y * h y := by
  filter_upwards [ae_ne_zero] with y hy
  rcases hy.lt_or_gt with hneg | hpos
  · rw [oddHalfSpaceExtension_of_neg _ hneg, oddReflection_of_neg 1 u hneg, hpar y]
    ring
  · rw [oddHalfSpaceExtension_eqOn _ (show y ∈ HalfSpace.upper 2 from hpos),
      oddReflection_of_nonneg 1 u hpos.le]

/-- The derivative of `y ↦ gᵢ(x - y)` away from the pole: `∂ⱼ` of it is `-kᵢⱼ(x - y)/π`. -/
private theorem partialDeriv_gradientKernel_sub (i j : Fin 2) {x y : ℝ^2} (hxy : x - y ≠ 0) :
    (∂[j] (fun z ↦ gradientKernel i (x - z))) y = -(hessianKernel i j (x - y) / Real.pi) := by
  have hg : DifferentiableAt ℝ (gradientKernel i) (x - y) :=
    (contDiffAt_gradientKernel i hxy (n := 1)).differentiableAt one_ne_zero
  have hcomp : HasFDerivAt (fun z ↦ gradientKernel i (x - z))
      ((fderiv ℝ (gradientKernel i) (x - y)).comp (-ContinuousLinearMap.id ℝ (ℝ^2))) y :=
    hg.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  have h := partialDeriv_gradientKernel j i hxy
  simp only [PDE.partialDeriv] at h
  rw [PDE.partialDeriv, hcomp.fderiv]
  change fderiv ℝ (gradientKernel i) (x - y) (-(EuclideanSpace.single j (1 : ℝ))) = _
  rw [map_neg, h, hessianKernel_comm]

/-- Away from a disc around `x`, the pole of `y ↦ gᵢ(x - y)` is not reached. -/
private theorem sub_ne_zero_of_notMem_ball {x y : ℝ^2} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∉ Metric.ball x ρ) : x - y ≠ 0 := by
  intro h0
  rw [(sub_eq_zero.mp h0).symm] at hy
  exact hy (Metric.mem_ball_self hρ)

/-- The kernel `y ↦ gᵢ(x - y) h(y)` vanishes near every point of the disc where `h` vanishes. -/
private theorem gradientKernel_sub_mul_eventuallyEq_zero (i : Fin 2) {h : ℝ^2 → ℝ} {x y : ℝ^2}
    {ρ : ℝ} (hx : ∀ y ∈ Metric.ball x ρ, h y = 0) (hy : y ∈ Metric.ball x ρ) :
    (fun z ↦ gradientKernel i (x - z) * h z) =ᶠ[𝓝 y] fun _ ↦ 0 := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
  rw [hx z hz, mul_zero]

/-- The kernel `y ↦ gᵢ(x - y) h(y)` is `C¹` when `h` is `C¹` and vanishes on a disc around `x`. -/
theorem contDiff_gradientKernel_sub_mul (i : Fin 2) {h : ℝ^2 → ℝ} (hh : ContDiff ℝ 1 h)
    {x : ℝ^2} {ρ : ℝ} (hρ : 0 < ρ) (hx : ∀ y ∈ Metric.ball x ρ, h y = 0) :
    ContDiff ℝ 1 (fun y ↦ gradientKernel i (x - y) * h y) := by
  refine contDiff_iff_contDiffAt.mpr fun y ↦ ?_
  by_cases hy : y ∈ Metric.ball x ρ
  · exact contDiffAt_const.congr_of_eventuallyEq
      (gradientKernel_sub_mul_eventuallyEq_zero i hx hy)
  · exact ((contDiffAt_gradientKernel i (sub_ne_zero_of_notMem_ball hρ hy)).comp y
      (contDiffAt_const.sub contDiffAt_id)).mul hh.contDiffAt

/-- The partial derivatives of the kernel `y ↦ gᵢ(x - y) h(y)` when `h` vanishes on a disc
around `x`: `∂ⱼ` of it is `-(kᵢⱼ(x - y)/π · h(y) - gᵢ(x - y) ∂ⱼh(y))`. -/
theorem partialDeriv_gradientKernel_sub_mul (i j : Fin 2) {h : ℝ^2 → ℝ}
    (hh : ContDiff ℝ 1 h) {x : ℝ^2} {ρ : ℝ} (hρ : 0 < ρ) (hx : ∀ y ∈ Metric.ball x ρ, h y = 0)
    (y : ℝ^2) :
    (∂[j] (fun z ↦ gradientKernel i (x - z) * h z)) y =
      -(hessianKernel i j (x - y) / Real.pi * h y - gradientKernel i (x - y) * (∂[j] h) y) := by
  by_cases hy : y ∈ Metric.ball x ρ
  · have hh0 : h =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      exact hx z hz
    have h1 : (∂[j] (fun z ↦ gradientKernel i (x - z) * h z)) y = 0 := by
      simp [PDE.partialDeriv, (gradientKernel_sub_mul_eventuallyEq_zero i hx hy).fderiv_eq]
    have h2 : (∂[j] h) y = 0 := by
      simp [PDE.partialDeriv, hh0.fderiv_eq]
    rw [h1, h2, hx y hy]
    ring
  · have hxy := sub_ne_zero_of_notMem_ball hρ hy
    have hg : DifferentiableAt ℝ (fun z ↦ gradientKernel i (x - z)) y :=
      ((contDiffAt_gradientKernel i hxy (n := 1)).differentiableAt one_ne_zero).comp y
        ((differentiableAt_const x).sub differentiableAt_id)
    rw [PDE.partialDeriv_mul hg ((hh.differentiable one_ne_zero) y),
      partialDeriv_gradientKernel_sub i j hxy]
    ring

/-- **Integration by parts for the Green gradient of a product source.** Let `u` be `C¹` with
`u = 0` on the boundary line, and let `h` be `C¹`, compactly supported, with `h ∘ R₁ = σ h`
(`σ = 1` for `j = 0`, `σ = -1` for `j = 1`) and `h = 0` on a disc around `x`. Then, with
`U = oddReflection 1 u`,

`∂ᵢ G[∂ⱼu · h](x) = ∫ U(y) (kᵢⱼ(x - y)/π · h(y) - gᵢ(x - y) ∂ⱼh(y)) dy`. -/
theorem partialDeriv_halfSpaceGreenPotential_partialDeriv_mul (i j : Fin 2) {u h : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 1 u) (hb : ∀ y : ℝ^2, y 1 = 0 → u y = 0) (hh : ContDiff ℝ 1 h)
    (hhc : HasCompactSupport h) (hpar : ∀ y, h (𝐑 1 y) = (if j = 0 then 1 else -1) * h y)
    {x : ℝ^2} {ρ : ℝ} (hρ : 0 < ρ) (hx : ∀ y ∈ Metric.ball x ρ, h y = 0) :
    (∂[i] (halfSpaceGreenPotential fun y ↦ (∂[j] u) y * h y)) x =
      ∫ y, oddReflection 1 u y *
        (hessianKernel i j (x - y) / Real.pi * h y - gradientKernel i (x - y) * (∂[j] h) y) := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hdu : Continuous (∂[j] u) := (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF : Continuous fun y ↦ (∂[j] u) y * h y := hdu.mul hh.continuous
  have hFc : HasCompactSupport fun y ↦ (∂[j] u) y * h y := hhc.mul_left
  set U := oddReflection 1 u with hUdef
  have hU : ContDiff ℝ 1 U := contDiff_one_oddReflection hu hb
  have hUd : Differentiable ℝ U := hU.differentiable one_ne_zero
  set K : ℝ^2 → ℝ := fun y ↦ gradientKernel i (x - y) * h y with hKdef
  have hK : ContDiff ℝ 1 K := contDiff_gradientKernel_sub_mul i hh hρ hx
  have hKc : HasCompactSupport K := hhc.mul_left
  have hKd : Differentiable ℝ K := hK.differentiable one_ne_zero
  have hdK : Continuous fun y ↦ fderiv ℝ K y (EuclideanSpace.single j 1) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdKc : HasCompactSupport fun y ↦ fderiv ℝ K y (EuclideanSpace.single j 1) :=
    hKc.fderiv_apply (𝕜 := ℝ) _
  have hdU : Continuous fun y ↦ fderiv ℝ U y (EuclideanSpace.single j 1) :=
    (hU.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [partialDeriv_halfSpaceGreenPotential_eq_integral hF hFc i x]
  have hae := oddHalfSpaceExtension_partialDeriv_mul_ae_eq j hud hpar
  have h1 : (∫ y, gradientKernel i (x - y) * oddHalfSpaceExtension (fun y ↦ (∂[j] u) y * h y) y)
      = ∫ y, K y * fderiv ℝ U y (EuclideanSpace.single j 1) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hy]
    simp only [hKdef, PDE.partialDeriv]
    ring
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := K) (g := U) (v := EuclideanSpace.single j (1 : ℝ))
    ((hdK.mul hU.continuous).integrable_of_hasCompactSupport hdKc.mul_right)
    ((hK.continuous.mul hdU).integrable_of_hasCompactSupport hKc.mul_right)
    ((hK.continuous.mul hU.continuous).integrable_of_hasCompactSupport hKc.mul_right)
    (fun y _ ↦ hKd y) (fun y _ ↦ hUd y)
  rw [h1, hibp, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  have hKy := partialDeriv_gradientKernel_sub_mul i j hh hρ hx y
  simp only [PDE.partialDeriv] at hKy
  rw [hKdef]
  dsimp only
  rw [hKy]
  simp only [PDE.partialDeriv]
  ring

/-- **The Green gradient of `u · h`** for `h` even in `y₁`: with `U = oddReflection 1 u`,
`∂ᵢ G[u · h](x) = ∫ gᵢ(x - y) U(y) h(y) dy`. -/
theorem partialDeriv_halfSpaceGreenPotential_mul (i : Fin 2) {u h : ℝ^2 → ℝ}
    (huh : Continuous fun y ↦ u y * h y) (hc : HasCompactSupport fun y ↦ u y * h y)
    (hpar : ∀ y, h (𝐑 1 y) = h y) (x : ℝ^2) :
    (∂[i] (halfSpaceGreenPotential fun y ↦ u y * h y)) x =
      ∫ y, gradientKernel i (x - y) * (oddReflection 1 u y * h y) := by
  rw [partialDeriv_halfSpaceGreenPotential_eq_integral huh hc i x]
  refine integral_congr_ae ?_
  filter_upwards [oddHalfSpaceExtension_mul_ae_eq (u := u) hpar] with y hy
  rw [hy]

end GreenFunction

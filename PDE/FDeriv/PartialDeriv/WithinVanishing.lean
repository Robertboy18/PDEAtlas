/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.WithinOperators
public import PDE.Common.Euclidean.CoordinateReflection
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Vanishing to second order within a set

Tools for showing that a field given on a closed set vanishes to second order at a point. On a
set invariant under a coordinate reflection, the partial derivatives within it of even and odd
functions have a parity; at points of the reflection hyperplane the normal derivative of an even
function and the tangential derivatives of an odd function vanish.

## Main results

* `isBigO_sq_of_contDiffOn`: on a convex set with unique derivatives, a function `C²` within the
  set whose value and derivative within the set vanish at a point `p` is `O(‖x - p‖²)` within the
  set at `p`.
* `fderivWithin_eq_zero_of_partialDerivWithin`: on `ℝⁿ` the derivative within a set vanishes when
  all partial derivatives within it do.
* `fderivWithin_apply_eq_zero_of_ray`: the derivative within a set in a direction `v` vanishes at
  `p` if the function vanishes on the ray `p + t v`, `t ≥ 0`, inside the set.
* `partialDerivWithin_coordinateReflection_of_even`: for an even function,
  `∂ⱼf(p) = ±∂ⱼf(Rp)`, with the sign `-` for `j = i`.
* `partialDerivWithin_coordinateReflection_of_odd`: for an odd function,
  `∂ⱼf(p) = ∓∂ⱼf(Rp)`, with the sign `+` for `j = i`.
* `laplacianWithin_coordinateReflection_of_odd`: the Laplacian within such a set of an odd `C²`
  function is odd.
-/

@[expose] public section

noncomputable section

open Filter Set Asymptotics PDE.Common
open scoped Topology

namespace PDE

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {s : Set E} {p : E}

/-- **Second-order vanishing within a convex set**: a function `C²` within a convex set with
unique derivatives whose value and derivative within the set vanish at `p ∈ s` is
`O(‖x - p‖²)` within the set at `p`. -/
theorem isBigO_sq_of_contDiffOn (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s) (hp : p ∈ s)
    (hf : ContDiffOn ℝ 2 f s) (hf0 : f p = 0) (hd : fderivWithin ℝ f s p = 0) :
    f =O[𝓝[s] p] fun x ↦ ‖x - p‖ ^ 2 := by
  set g := fderivWithin ℝ f s
  have hg : ContDiffOn ℝ 1 g s := hf.fderivWithin hu (by norm_num)
  have hfd : DifferentiableOn ℝ f s := hf.differentiableOn (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hg p hp) hs
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhdsWithin_iff.1 ht
  set t₀ := Metric.ball p δ ∩ s
  have ht₀ : Convex ℝ t₀ := (convex_ball p δ).inter hs
  have hpt₀ : p ∈ t₀ := ⟨Metric.mem_ball_self hδ, hp⟩
  -- the derivative is `O(‖y - p‖)` on `t₀`
  have hgt : ∀ y ∈ t₀, ‖g y‖ ≤ K * ‖y - p‖ := fun y hy ↦ by
    have h := hK.norm_sub_le (hδt hy) (hδt hpt₀)
    rwa [show g p = 0 from hd, sub_zero] at h
  refine IsBigO.of_bound K ?_
  filter_upwards [inter_mem_nhdsWithin s (Metric.ball_mem_nhds p hδ), self_mem_nhdsWithin]
    with x hx hxs
  have hxt : x ∈ t₀ := ⟨hx.2, hxs⟩
  set r := ‖x - p‖
  set t' := t₀ ∩ Metric.closedBall p r
  have ht' : Convex ℝ t' := ht₀.inter (convex_closedBall p r)
  have h := ht'.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := f) (f' := g) (C := K * r)
    (fun z hz ↦ ((hfd z hz.1.2).hasFDerivWithinAt).mono
      (inter_subset_left.trans inter_subset_right))
    (fun z hz ↦ (hgt z hz.1).trans (mul_le_mul_of_nonneg_left
      (by simpa [dist_eq_norm] using hz.2) (by positivity)))
    ⟨hpt₀, Metric.mem_closedBall_self (norm_nonneg _)⟩ ⟨hxt, by simp [r, dist_eq_norm]⟩
  rw [hf0, sub_zero] at h
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc ‖f x‖ ≤ K * r * r := h
    _ = K * r ^ 2 := by ring

end Taylor

variable {n : ℕ} {f : ℝ^n → ℝ} {s : Set (ℝ^n)} {p : ℝ^n}

/-- On `ℝⁿ`, the derivative within a set vanishes when all partial derivatives within it do. -/
theorem fderivWithin_eq_zero_of_partialDerivWithin
    (h : ∀ i : Fin n, partialDerivWithin i f s p = 0) : fderivWithin ℝ f s p = 0 := by
  ext v
  have hv := advectiveDerivativeWithin_eq_sum (fun _ ↦ v) f s p
  simp only [advectiveDerivativeWithin, h, mul_zero, Finset.sum_const_zero] at hv
  simpa using hv

/-- **Vanishing along a ray**: if `f` vanishes on the ray `p + t v`, `t ≥ 0`, which lies in `s`,
and `f` is differentiable within `s` at `p`, then the derivative of `f` within `s` at `p` in the
direction `v` vanishes. -/
theorem fderivWithin_apply_eq_zero_of_ray {v : ℝ^n}
    (hray : ∀ t : ℝ, 0 ≤ t → p + t • v ∈ s ∧ f (p + t • v) = 0)
    (hd : DifferentiableWithinAt ℝ f s p) : fderivWithin ℝ f s p v = 0 := by
  set γ : ℝ → ℝ^n := fun t ↦ p + t • v
  have hγ : HasDerivWithinAt γ v (Ici 0) 0 := by
    have h : HasDerivAt γ ((1 : ℝ) • v) 0 := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    rw [one_smul] at h
    exact h.hasDerivWithinAt
  have hmaps : MapsTo γ (Ici 0) s := fun t ht ↦ (hray t ht).1
  have hγ0 : γ 0 = p := by simp [γ]
  have hd' : DifferentiableWithinAt ℝ f s (γ 0) := by rwa [hγ0]
  have hcomp := hd'.hasFDerivWithinAt.comp_hasDerivWithinAt (0 : ℝ) hγ hmaps
  rw [hγ0] at hcomp
  have hzero : HasDerivWithinAt (f ∘ γ) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : ℝ)).congr (fun t ht ↦ (hray t ht).2)
      (by simpa [γ] using (hray 0 le_rfl).2)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hcomp hzero

section Reflection

variable {i : Fin n} (hs : ∀ y ∈ s, coordinateReflection i y ∈ s)
include hs

/-- If `s` is invariant under the reflection `R` in the `i`-th coordinate and `f` is differentiable
within `s` at `R p`, then `f ∘ R` has the derivative `Df(R p) ∘ R` within `s` at `p`. -/
private theorem hasFDerivWithinAt_comp_coordinateReflection
    (hd : DifferentiableWithinAt ℝ f s (coordinateReflection i p)) :
    HasFDerivWithinAt (fun y ↦ f (coordinateReflection i y))
      ((fderivWithin ℝ f s (coordinateReflection i p)).comp
        (coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv.toContinuousLinearMap)
      s p :=
  hd.hasFDerivWithinAt.comp p ((coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv
    |>.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt) (fun y hy ↦ hs y hy)

omit hs in
/-- For a linear form `D` and the reflection `R` in the `i`-th coordinate, `D (R eⱼ)` is `-D eⱼ` for
`j = i` and `D eⱼ` otherwise. -/
private theorem fderivWithin_coordinateReflection_single
    (D : ℝ^n →L[ℝ] ℝ) (j : Fin n) :
    D (coordinateReflection i (EuclideanSpace.single j (1 : ℝ))) =
      (if j = i then -1 else 1) * D (EuclideanSpace.single j (1 : ℝ)) := by
  by_cases hji : j = i
  · subst hji
    have hneg : EuclideanSpace.single j (-1 : ℝ) = -EuclideanSpace.single j (1 : ℝ) := by
      ext k
      by_cases hk : k = j <;> simp [hk]
    rw [coordinateReflection_single_same, hneg, map_neg]
    simp
  · rw [coordinateReflection_single_of_ne i j hji]
    simp [hji]

/-- **Partial derivatives of an even function** within a set invariant under the reflection in
the `i`-th coordinate: `∂ⱼf(p) = ±∂ⱼf(Rp)`, with the sign `-` for `j = i`. -/
theorem partialDerivWithin_coordinateReflection_of_even
    (hpar : ∀ y ∈ s, f (coordinateReflection i y) = f y) (hp : p ∈ s)
    (hu : UniqueDiffWithinAt ℝ s p) (hd : DifferentiableWithinAt ℝ f s (coordinateReflection i p))
    (j : Fin n) :
    partialDerivWithin j f s p =
      (if j = i then -1 else 1) * partialDerivWithin j f s (coordinateReflection i p) := by
  have h := HasFDerivWithinAt.congr' (hasFDerivWithinAt_comp_coordinateReflection hs hd)
    (fun y hy ↦ (hpar y hy).symm) hp
  have key : partialDerivWithin j f s p = fderivWithin ℝ f s (coordinateReflection i p)
      (coordinateReflection i (EuclideanSpace.single j (1 : ℝ))) := by
    rw [show partialDerivWithin j f s p = fderivWithin ℝ f s p (EuclideanSpace.single j 1) from
      rfl, h.fderivWithin hu]
    rfl
  rw [key, fderivWithin_coordinateReflection_single]
  rfl

/-- **Partial derivatives of an odd function** within a set invariant under the reflection in
the `i`-th coordinate: `∂ⱼf(p) = ∓∂ⱼf(Rp)`, with the sign `+` for `j = i`. -/
theorem partialDerivWithin_coordinateReflection_of_odd
    (hpar : ∀ y ∈ s, f (coordinateReflection i y) = -f y) (hp : p ∈ s)
    (hu : UniqueDiffWithinAt ℝ s p) (hd : DifferentiableWithinAt ℝ f s (coordinateReflection i p))
    (j : Fin n) :
    partialDerivWithin j f s p =
      -((if j = i then -1 else 1) * partialDerivWithin j f s (coordinateReflection i p)) := by
  have h := HasFDerivWithinAt.congr' (f₁ := f)
    (hasFDerivWithinAt_comp_coordinateReflection hs hd).neg
    (fun y hy ↦ by
      change f y = -f (coordinateReflection i y)
      rw [hpar y hy, neg_neg]) hp
  have key : partialDerivWithin j f s p = -fderivWithin ℝ f s (coordinateReflection i p)
      (coordinateReflection i (EuclideanSpace.single j (1 : ℝ))) := by
    rw [show partialDerivWithin j f s p = fderivWithin ℝ f s p (EuclideanSpace.single j 1) from
      rfl, h.fderivWithin hu]
    rfl
  rw [key, fderivWithin_coordinateReflection_single]
  rfl

/-- **The Laplacian within a set of an odd function is odd**: for `f` odd under the reflection in
the `i`-th coordinate and `C²` within a reflection-invariant set with unique derivatives,
`Δˢf(Rp) = -Δˢf(p)`. -/
theorem laplacianWithin_coordinateReflection_of_odd
    (hpar : ∀ y ∈ s, f (coordinateReflection i y) = -f y) (hu : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ 2 f s) (hp : p ∈ s) :
    laplacianWithin f s (coordinateReflection i p) = -laplacianWithin f s p := by
  have hRR (y : ℝ^n) : coordinateReflection i (coordinateReflection i y) = y :=
    coordinateReflection_involutive i y
  have hd : DifferentiableOn ℝ f s := hf.differentiableOn (by norm_num)
  have hpar₁ (j : Fin n) (y : ℝ^n) (hy : y ∈ s) :
      partialDerivWithin j f s (coordinateReflection i y) =
        -((if j = i then -1 else 1) * partialDerivWithin j f s y) := by
    have h := partialDerivWithin_coordinateReflection_of_odd hs hpar (hs y hy) (hu _ (hs y hy))
      (by rw [hRR]; exact hd y hy) j
    rwa [hRR] at h
  have hd₁ (j : Fin n) : DifferentiableOn ℝ (partialDerivWithin j f s) s :=
    (hf.partialDerivWithin j hu (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hdR (j : Fin n) : DifferentiableWithinAt ℝ (partialDerivWithin j f s) s
      (coordinateReflection i (coordinateReflection i p)) := by
    rw [hRR]
    exact hd₁ j p hp
  rw [laplacianWithin, laplacianWithin, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j = i
  · have heven : ∀ y ∈ s, partialDerivWithin j f s (coordinateReflection i y) =
        partialDerivWithin j f s y := fun y hy ↦ by
      rw [hpar₁ j y hy, ite_eq_left hj]
      ring
    have h := partialDerivWithin_coordinateReflection_of_even hs heven (hs p hp)
      (hu _ (hs p hp)) (hdR j) j
    rw [hRR, ite_eq_left hj] at h
    rw [h]
    ring
  · have hodd : ∀ y ∈ s, partialDerivWithin j f s (coordinateReflection i y) =
        -partialDerivWithin j f s y := fun y hy ↦ by
      rw [hpar₁ j y hy, ite_eq_right hj, one_mul]
    have h := partialDerivWithin_coordinateReflection_of_odd hs hodd (hs p hp)
      (hu _ (hs p hp)) (hdR j) j
    rw [hRR, ite_eq_right hj, one_mul] at h
    exact h

end Reflection

end PDE

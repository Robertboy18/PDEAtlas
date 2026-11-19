/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Differentiating compactly indexed families in the supremum norm

A continuous family `f : E → F → G` restricted to a compact set `K ⊆ F` in the
second variable defines a map `x ↦ f x (·)` into the supremum-norm space
`K →ᵇ G` of bounded continuous functions.  If `f` is differentiable in `x`
with a derivative `D x y` that is jointly continuous in `(x, y)`, this curried
map is Fréchet differentiable, and its derivative at `x` is the operator
`h ↦ (y ↦ D x y h)`.  The point is uniformity in `y`: joint continuity of `D`
near `{x} × K` with `K` compact gives, via the mean value inequality, a
remainder bound uniform over `y ∈ K`.  We also show that compact
support and joint smoothness on a product pass to slices in either variable.

## Main results

* `BoundedContinuousFunction.compactCurry`: the curried map into `K →ᵇ G`.
* `BoundedContinuousFunction.compactCurryFDeriv`: the pointwise derivative as
  a continuous linear map `E →L[ℝ] (K →ᵇ G)`, bounded by the supremum norm of
  the operator family.
* `BoundedContinuousFunction.hasFDerivAt_compactCurry`: Fréchet
  differentiability of the curried map in the supremum norm.
* `HasCompactSupport.prod_left_slice`, `HasCompactSupport.prod_right_slice`,
  `ContDiff.prod_left_slice`, `ContDiff.prod_right_slice`: slices of compactly
  supported or `Cⁿ` functions on a product.
-/

@[expose] public section

open Asymptotics Function Set TopologicalSpace

noncomputable section

namespace BoundedContinuousFunction

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Curry a continuous family over a compact fiber into the supremum-norm space. -/
def compactCurry (K : Compacts F) (f : E → F → G)
    (hf : Continuous f.uncurry) (x : E) : K →ᵇ G :=
  mkOfCompact
    { toFun := fun y ↦ f x y
      continuous_toFun := hf.comp (continuous_const.prodMk continuous_subtype_val) }

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- Evaluating the curried family at `y ∈ K` recovers `f x y`. -/
@[simp]
theorem compactCurry_apply (K : Compacts F) (f : E → F → G)
    (hf : Continuous f.uncurry) (x : E) (y : K) :
    compactCurry K f hf x y = f x y :=
  rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- Joint continuity over a compact fiber is continuity in the supremum norm. -/
theorem continuous_compactCurry (K : Compacts F) (f : E → F → G)
    (hf : Continuous f.uncurry) :
    Continuous (compactCurry K f hf) := by
  apply (ContinuousMap.isometryEquivBoundedOfCompact K G).continuous.comp
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- A continuous operator-valued family restricted to a compact fiber. -/
def compactCurryOperator (K : Compacts F) (D : E → F → E →L[ℝ] G)
    (hD : Continuous D.uncurry) (x : E) : K →ᵇ (E →L[ℝ] G) :=
  mkOfCompact
    { toFun := fun y ↦ D x y
      continuous_toFun := hD.comp (continuous_const.prodMk continuous_subtype_val) }

/-- Apply a continuous operator-valued family on a compact fiber to one vector. -/
def compactCurryOperatorApply (K : Compacts F) (D : E → F → E →L[ℝ] G)
    (hD : Continuous D.uncurry) (x h : E) : K →ᵇ G :=
  mkOfCompact
    { toFun := fun y ↦ D x y h
      continuous_toFun :=
        (hD.comp (continuous_const.prodMk continuous_subtype_val)).clm_apply continuous_const }

omit [NormedSpace ℝ F] in
/-- Evaluating the applied operator family at `y ∈ K` gives `D x y h`. -/
@[simp]
theorem compactCurryOperatorApply_apply
    (K : Compacts F) (D : E → F → E →L[ℝ] G)
    (hD : Continuous D.uncurry) (x h : E) (y : K) :
    compactCurryOperatorApply K D hD x h y = D x y h :=
  rfl

/-- The pointwise derivative of a compactly indexed family, as a map into the supremum-norm
space. -/
def compactCurryFDeriv (K : Compacts F) (D : E → F → E →L[ℝ] G)
    (hD : Continuous D.uncurry) (x : E) : E →L[ℝ] K →ᵇ G :=
  LinearMap.mkContinuous
    { toFun := compactCurryOperatorApply K D hD x
      map_add' := fun h h' ↦ by
        ext y
        change D x y (h + h') = D x y h + D x y h'
        exact map_add (D x y) h h'
      map_smul' := fun c h ↦ by
        ext y
        change D x y (c • h) = c • D x y h
        exact map_smul (D x y) c h }
    ‖compactCurryOperator K D hD x‖ fun h ↦ by
      change ‖compactCurryOperatorApply K D hD x h‖ ≤
        ‖compactCurryOperator K D hD x‖ * ‖h‖
      refine (BoundedContinuousFunction.norm_le
        (f := compactCurryOperatorApply K D hD x h)
        (C := ‖compactCurryOperator K D hD x‖ * ‖h‖)
        (mul_nonneg (norm_nonneg (compactCurryOperator K D hD x)) (norm_nonneg h))).2 ?_
      intro y
      exact (D x y).le_opNorm h |>.trans
        (mul_le_mul_of_nonneg_right
          ((compactCurryOperator K D hD x).norm_coe_le_norm y) (norm_nonneg h))

omit [NormedSpace ℝ F] in
/-- The candidate derivative applied to `h` and evaluated at `y ∈ K` is
`D x y h`. -/
@[simp]
theorem compactCurryFDeriv_apply (K : Compacts F) (D : E → F → E →L[ℝ] G)
    (hD : Continuous D.uncurry) (x h : E) (y : K) :
    compactCurryFDeriv K D hD x h y = D x y h :=
  rfl

omit [NormedSpace ℝ F] in
/-- Differentiability near the parameter, at every point of the compact fiber,
gives differentiation in the supremum norm when the derivative is jointly continuous. -/
theorem hasFDerivAt_compactCurry_of_eventually
    (K : Compacts F) (f : E → F → G) (D : E → F → E →L[ℝ] G)
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (x : E)
    (hderiv : ∀ᶠ z in nhds x, ∀ y : K, HasFDerivAt (fun w ↦ f w y) (D z y) z) :
    HasFDerivAt (compactCurry K f hf) (compactCurryFDeriv K D hD x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.2
  intro ε hε
  obtain ⟨v, hv, hclose⟩ :=
    K.2.mem_uniformity_of_prod
      (s := (univ : Set E)) (k := (K : Set F)) (f := D)
      hD.continuousOn (mem_univ x) (Metric.dist_mem_uniformity hε)
  have hv' : v ∈ nhds x := by simpa using hv
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hv' hderiv)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  rw [norm_le (mul_nonneg hε.le (norm_nonneg h))]
  intro y
  change ‖f (x + h) y - f x y - D x y h‖ ≤ ε * ‖h‖
  have hx : x ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball] using hδ
  have hxh : x + h ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hbound : ∀ z ∈ Metric.ball x δ, ‖D z y - D x y‖ ≤ ε := by
    intro z hz
    have hzv : z ∈ v := (hδv hz).1
    have hyK : (y : F) ∈ K := y.2
    have hdist : dist (D z y) (D x y) < ε := hclose z hzv y hyK
    simpa [dist_eq_norm] using hdist.le
  have hmvt :=
    (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := fun z ↦ f z y) (f' := fun z ↦ D z y) (φ := D x y)
      (fun z hz ↦ ((hδv hz).2 y).hasFDerivWithinAt) hbound hx hxh
  simpa only [add_sub_cancel_left] using hmvt

omit [NormedSpace ℝ F] in
/-- A jointly differentiable family over a compact fiber differentiates in the supremum norm,
provided that its parameter derivative is jointly continuous. -/
theorem hasFDerivAt_compactCurry
    (K : Compacts F) (f : E → F → G) (D : E → F → E →L[ℝ] G)
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (hderiv : ∀ x y, HasFDerivAt (fun z ↦ f z y) (D x y) x)
    (x : E) :
    HasFDerivAt (compactCurry K f hf) (compactCurryFDeriv K D hD x) x :=
  hasFDerivAt_compactCurry_of_eventually K f D hf hD x
    (Filter.Eventually.of_forall fun z y ↦ hderiv z y)

end BoundedContinuousFunction

namespace HasCompactSupport

/-- Compact support of a function on a product passes to a slice in the first
variable. -/
theorem prod_left_slice
    {α β M : Type*} [TopologicalSpace α] [R1Space α]
    [TopologicalSpace β] [Zero M]
    {f : α × β → M} (hf : HasCompactSupport f) (y : β) :
    HasCompactSupport (fun x ↦ f (x, y)) := by
  let K : Set α := Prod.fst '' tsupport f
  have hK : IsCompact K := hf.isCompact.image continuous_fst
  refine HasCompactSupport.intro hK ?_
  intro x hx
  by_contra hxy
  have hs : (x, y) ∈ Function.support f := by
    simpa [Function.support] using hxy
  exact hx ⟨(x, y), subset_closure hs, rfl⟩

/-- Compact support of a function on a product passes to a slice in the second
variable. -/
theorem prod_right_slice
    {α β M : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [R1Space β] [Zero M]
    {f : α × β → M} (hf : HasCompactSupport f) (x : α) :
    HasCompactSupport (fun y ↦ f (x, y)) := by
  let K : Set β := Prod.snd '' tsupport f
  have hK : IsCompact K := hf.isCompact.image continuous_snd
  refine HasCompactSupport.intro hK ?_
  intro y hy
  by_contra hxy
  have hs : (x, y) ∈ Function.support f := by
    simpa [Function.support] using hxy
  exact hy ⟨(x, y), subset_closure hs, rfl⟩

end HasCompactSupport

variable {𝕜 E F G : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Joint smoothness on a product passes to a slice in the first variable. -/
theorem ContDiff.prod_left_slice {n : ℕ∞} {f : E × F → G}
    (hf : ContDiff 𝕜 n f) (y : F) :
    ContDiff 𝕜 n (fun x ↦ f (x, y)) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

/-- Joint smoothness on a product passes to a slice in the second variable. -/
theorem ContDiff.prod_right_slice {n : ℕ∞} {f : E × F → G}
    (hf : ContDiff 𝕜 n f) (x : E) :
    ContDiff 𝕜 n (fun y ↦ f (x, y)) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local inversion of a family near the identity

If `Φ(0, ·)` is the identity near `x`, the map `(t, y) ↦ (t, Φ(t, y))` has an
invertible triangular derivative at `(0, x)`. The inverse function theorem therefore
constructs a spatial inverse depending jointly `C²` on the parameter and position.
All identities and regularity conclusions are local; the family need not be globally
injective or have a global smooth extension. The spatial space may be any real Banach space.
-/

@[expose] public noncomputable section

open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Φ : ℝ → E → E} {x : E}

/-- The triangular linear equivalence with identity diagonal and parameter derivative
in its lower left block. It is the derivative of `(t,y) ↦ (t,Φ(t,y))` when `Φ(0,·)`
is locally the identity. -/
def parameterMapDerivative (Φ : ℝ → E → E) (x : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).skewProd (ContinuousLinearEquiv.refl ℝ E)
    ((fderiv ℝ (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x)).comp
      (ContinuousLinearMap.inl ℝ ℝ E))

/-- Local identity of the spatial map makes the derivative of the augmented map
invertible. No restriction is placed on the parameter derivative. -/
theorem hasFDerivAt_parameterMap
    (hΦ : DifferentiableAt ℝ (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    HasFDerivAt (fun p : ℝ × E ↦ (p.1, Φ p.1 p.2))
      (parameterMapDerivative Φ x : (ℝ × E) →L[ℝ] (ℝ × E)) (0, x) := by
  have hspace (v : E) :
      fderiv ℝ (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x) (0, v) = v := by
    have h := hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (0 : ℝ) x)
    have heq := congrArg (fun A ↦ A v) h.fderiv
    change fderiv ℝ (Φ 0) x v =
      fderiv ℝ (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x) (0, v) at heq
    rw [hΦ₀.fderiv_eq] at heq
    simpa using heq.symm
  have hD :
      (ContinuousLinearMap.fst ℝ ℝ E).prod
        (fderiv ℝ (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x)) =
      (parameterMapDerivative Φ x : (ℝ × E) →L[ℝ] (ℝ × E)) := by
    apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · rfl
    change fderiv ℝ (fun q : ℝ × E ↦ Φ q.1 q.2) (0, x) p =
      p.2 + fderiv ℝ (fun q : ℝ × E ↦ Φ q.1 q.2) (0, x) (p.1, 0)
    rw [← hspace p.2, ← map_add]
    simp only [Prod.mk_add_mk, zero_add, add_zero]
  rw [← hD]
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := (0, x))).prodMk hΦ.hasFDerivAt

variable [CompleteSpace E]

/-- The spatial part of Mathlib's local inverse of `(t,y) ↦ (t,Φ(t,y))`.
Its values away from the inverse neighborhood carry no asserted regularity or inverse law. -/
def localSpatialInverse
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) (t : ℝ) (y : E) : E :=
  ((contDiffAt_fst.prodMk hΦ).localInverse
    (hasFDerivAt_parameterMap (hΦ.differentiableAt (by norm_num)) hΦ₀)
    (by norm_num) (t, y)).2

/-- The local spatial inverse fixes the base point at parameter zero. -/
theorem localSpatialInverse_zero_apply
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    localSpatialInverse hΦ hΦ₀ 0 x = x := by
  have h := (contDiffAt_fst.prodMk hΦ).localInverse_apply_image
    (hasFDerivAt_parameterMap (hΦ.differentiableAt (by norm_num)) hΦ₀) (by norm_num)
  simpa only [hΦ₀.eq_of_nhds, id_eq, localSpatialInverse] using congrArg Prod.snd h

/-- A jointly `C²` family near the identity has a jointly `C²` local spatial inverse. -/
theorem contDiffAt_localSpatialInverse
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    ContDiffAt ℝ 2 (fun p : ℝ × E ↦ localSpatialInverse hΦ hΦ₀ p.1 p.2) (0, x) := by
  have h := ((contDiffAt_fst.prodMk hΦ).to_localInverse
    (hasFDerivAt_parameterMap (hΦ.differentiableAt (by norm_num)) hΦ₀) (by norm_num)).snd
  simpa only [hΦ₀.eq_of_nhds, id_eq, localSpatialInverse] using h

/-- The local inverse undoes the spatial transformation jointly near `(0,x)`. -/
theorem localSpatialInverse_left_inverse
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    ∀ᶠ p : ℝ × E in 𝓝 (0, x), localSpatialInverse hΦ hΦ₀ p.1 (Φ p.1 p.2) = p.2 := by
  have h := ((contDiffAt_fst.prodMk hΦ).hasStrictFDerivAt'
    (hasFDerivAt_parameterMap (hΦ.differentiableAt (by norm_num)) hΦ₀)
    (by norm_num)).eventually_left_inverse
  filter_upwards [h] with p hp
  exact congrArg Prod.snd hp

/-- The spatial transformation undoes its local inverse jointly near `(0,x)`.
The first coordinate of the augmented inverse is forced to equal the parameter. -/
theorem localSpatialInverse_right_inverse
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    ∀ᶠ p : ℝ × E in 𝓝 (0, x), Φ p.1 (localSpatialInverse hΦ hΦ₀ p.1 p.2) = p.2 := by
  have h := ((contDiffAt_fst.prodMk hΦ).hasStrictFDerivAt'
    (hasFDerivAt_parameterMap (hΦ.differentiableAt (by norm_num)) hΦ₀)
    (by norm_num)).eventually_right_inverse
  simp only [hΦ₀.eq_of_nhds, id_eq] at h
  filter_upwards [h] with p hp
  have hfst := congrArg Prod.fst hp
  have hsnd := congrArg Prod.snd hp
  change Φ _ (localSpatialInverse hΦ hΦ₀ p.1 p.2) = p.2 at hsnd
  rw [hfst] at hsnd
  exact hsnd

/-- At parameter zero the local spatial inverse is itself the identity near `x`. -/
theorem localSpatialInverse_zero
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    localSpatialInverse hΦ hΦ₀ 0 =ᶠ[𝓝 x] id := by
  filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
    (localSpatialInverse_left_inverse hΦ hΦ₀), hΦ₀] with y hy hbase
  simpa only [hbase, id_eq] using hy

end PDE.Analysis

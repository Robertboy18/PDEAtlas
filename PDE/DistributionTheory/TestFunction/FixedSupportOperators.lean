/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import PDE.FDeriv.PartialDeriv

/-!
# Local multipliers and coordinate derivatives on supported tests

A coefficient of finite regularity near a fixed compact acts continuously on tests supported
there. Smooth separation localizes the coefficient before applying Mathlib's multiplier map.
The coefficient may be singular outside that compact.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter TopologicalSpace
open scoped Distributions Topology ContDiff

namespace ContDiffMapSupportedIn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : Compacts E}

/-- Finite regularity near a closed compact admits a globally regular representative agreeing
on a neighborhood of that compact. No extension of the coefficient across its singular set
is required. -/
theorem exists_contDiff_eq_nhdsSet (m : ℕ) (W : E → ℝ)
    (hW : ∀ x ∈ K, ContDiffAt ℝ (m : WithTop ℕ∞) W x) :
    ∃ G : E → ℝ, ContDiff ℝ (m : WithTop ℕ∞) G ∧
      ∀ᶠ x in 𝓝ˢ (K : Set E), G x = W x := by
  let U := {x : E | ContDiffAt ℝ (m : WithTop ℕ∞) W x}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun x hx ↦
    (show ContDiffAt ℝ (m : WithTop ℕ∞) W x from hx).eventually (by simp)
  obtain ⟨θ, hθ0, hθ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ E) hU.isClosed_compl K.isCompact.isClosed
    (Set.disjoint_left.mpr fun x hx hxK ↦ hx (hW x hxK)) (n := (m : ℕ∞))
  have hθ : ContDiff ℝ (m : WithTop ℕ∞) θ := contMDiff_iff_contDiff.mp θ.contMDiff
  refine ⟨fun x ↦ θ x * W x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hθ.contDiffAt.mul hx
    · have hz := hθ0.filter_mono (nhds_le_nhdsSet hx)
      have heq : (fun y ↦ θ y * W y) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
        filter_upwards [hz] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [hθ1] with x hx
    simp [hx]

/-- Multiplication by a coefficient that is Cᵐ near the fixed support, as a continuous linear
operator on Cᵐ supported tests. -/
def localMultiplierCLM (m : ℕ) (W : E → ℝ)
    (hW : ∀ x ∈ K, ContDiffAt ℝ (m : WithTop ℕ∞) W x) :
    𝓓^{(m : ℕ∞)}_{K}(E, ℝ) →L[ℝ] 𝓓^{(m : ℕ∞)}_{K}(E, ℝ) :=
  bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
    (exists_contDiff_eq_nhdsSet m W hW).choose_spec.1

/-- The local multiplier is pointwise multiplication by the original coefficient. -/
theorem localMultiplierCLM_apply (m : ℕ) (W : E → ℝ)
    (hW : ∀ x ∈ K, ContDiffAt ℝ (m : WithTop ℕ∞) W x)
    (f : 𝓓^{(m : ℕ∞)}_{K}(E, ℝ)) :
    ⇑(localMultiplierCLM m W hW f) = fun x ↦ W x * f x := by
  ext x
  change f x * (exists_contDiff_eq_nhdsSet m W hW).choose x = W x * f x
  by_cases hx : x ∈ K
  · rw [(exists_contDiff_eq_nhdsSet m W hW).choose_spec.2.self_of_nhdsSet x hx]
    exact mul_comm _ _
  · rw [f.zero_on_compl hx]
    simp

section CoordinateDerivatives

variable {d : ℕ} {K' : Compacts (ℝ^d)}

/-- Coordinate differentiation on supported tests, with the same regularity convention as
Mathlib's `fderivCLM`: it represents the derivative when `k + 1 ≤ n`. -/
def partialDerivCLM (n k : ℕ∞) (i : Fin d) :
    𝓓^{n}_{K'}(ℝ^d, ℝ) →L[ℝ] 𝓓^{k}_{K'}(ℝ^d, ℝ) :=
  (postcompCLM (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))).comp
    (fderivCLM ℝ n k)

/-- The supported coordinate operator recovers the coordinate partial derivative. -/
theorem partialDerivCLM_apply (n k : ℕ∞) (i : Fin d)
    (hk : k + 1 ≤ n) (f : 𝓓^{n}_{K'}(ℝ^d, ℝ)) :
    ⇑(partialDerivCLM n k i f) = (∂[i] ⇑f) := by
  change (fun x ↦ (fderivCLM ℝ n k f x) (EuclideanSpace.single i 1)) = _
  rw [fderivCLM_apply_of_le ℝ f hk]
  rfl

/-- A word of coordinate derivatives as a continuous linear map between fixed-support
spaces. It computes the iterated partial derivative when `k + indices.length ≤ n`. -/
def iteratedPartialDerivCLM (n k : ℕ∞) (indices : List (Fin d)) :
    𝓓^{n}_{K'}(ℝ^d, ℝ) →L[ℝ] 𝓓^{k}_{K'}(ℝ^d, ℝ) :=
  match indices with
  | [] => monoCLM ℝ
  | i :: rest => (partialDerivCLM (k + 1) k i).comp
      (iteratedPartialDerivCLM n (k + 1) rest)

/-- A supported coordinate word recovers the literal iterated partial derivative. -/
theorem iteratedPartialDerivCLM_apply (n k : ℕ∞) (indices : List (Fin d))
    (hk : k + indices.length ≤ n) (f : 𝓓^{n}_{K'}(ℝ^d, ℝ)) :
    ⇑(iteratedPartialDerivCLM n k indices f) = iteratedPartialDeriv indices f := by
  induction indices generalizing k with
  | nil =>
      have hkn : k ≤ n := by simpa using hk
      simp [iteratedPartialDerivCLM, monoCLM_apply, hkn, iteratedPartialDeriv]
  | cons i rest ih =>
      have hr : k + 1 + rest.length ≤ n := by
        simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
          add_comm 1 (rest.length : ℕ∞)] using hk
      change ⇑(partialDerivCLM (k + 1) k i
        (iteratedPartialDerivCLM n (k + 1) rest f)) = _
      rw [partialDerivCLM_apply _ _ _ le_rfl, ih _ hr]
      rfl

end CoordinateDerivatives

end ContDiffMapSupportedIn

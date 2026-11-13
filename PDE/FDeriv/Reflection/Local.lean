/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Reflection.Coordinate
public import PDE.FDeriv.PartialDeriv.OpenSet
import PDE.FDeriv.Calculus

/-!
# Reflection parity on an invariant open set

Let `σᵢ` be the reflection in the coordinate hyperplane `{xᵢ = 0}` and `U` an open set with
`σᵢ U ⊆ U`, such as a half-space bounded by a hyperplane orthogonal to that one. A function with
`f ∘ σᵢ = ε f` on `U` has `(∂ᵢ f) ∘ σᵢ = -ε ∂ᵢ f` and `(∂ⱼ f) ∘ σᵢ = ε ∂ⱼ f` on `U` (`j ≠ i`),
so the parity of an iterated derivative is that of `f` times `(-1)` per derivative in the
reflected coordinate. Odd functions vanish at the fixed points of `σᵢ` in `U`, and the limit of an
odd function at a point approached by fixed points in `U` is zero. A function vanishing on the
part of the hyperplane in `U` has vanishing tangential derivatives there. These are the parity
facts for fields that are symmetric only on a half-space.

## Main results

* `PDE.Common.IsReflectionEigenfunctionOn`: `f ∘ σᵢ = ε f` on `U`, the reflection eigenfunctions;
  `IsReflectionEigenfunctionOn.mono` restricts them to subsets.
* `IsReflectionEigenfunctionOn.partialDeriv_same`, `IsReflectionEigenfunctionOn.partialDeriv_of_ne`.
* `IsReflectionEigenfunctionOn.iteratedPartialDeriv`: the parity of an iterated derivative.
* `IsReflectionEigenfunctionOn.eq_zero_of_apply_eq_zero`,
  `IsReflectionEigenfunctionOn.eq_zero_of_tendsto`.
* `partialDeriv_eq_zero_of_eqOn_hyperplane`, `iteratedPartialDeriv_replicate_eq_zero`,
  `eq_zero_of_tendsto_of_eqOn_hyperplane`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Common

variable {n : ℕ}

/-- `f` is a reflection eigenfunction with eigenvalue `ε` on `U`: `f ∘ σᵢ = ε f` at every point
of `U`. Even functions have `ε = 1`, odd ones `ε = -1`. -/
def IsReflectionEigenfunctionOn (U : Set (ℝ^n)) (i : Fin n) (ε : ℝ) (f : ℝ^n → ℝ) : Prop :=
  ∀ x ∈ U, f (coordinateReflection i x) = ε * f x

namespace IsReflectionEigenfunctionOn

variable {i : Fin n} {ε : ℝ} {U : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- The eigenfunction condition is inherited by subsets. -/
theorem mono {V : Set (ℝ^n)} (h : IsReflectionEigenfunctionOn U i ε f) (hVU : V ⊆ U) :
    IsReflectionEigenfunctionOn V i ε f :=
  fun x hx ↦ h x (hVU hx)

/-- On an open set `U` where `f ∘ σᵢ = ε f`, the two functions agree near every point of `U`. -/
private theorem comp_eventuallyEq (h : IsReflectionEigenfunctionOn U i ε f) (hU : IsOpen U)
    {x : ℝ^n} (hx : x ∈ U) : (fun y ↦ f (coordinateReflection i y)) =ᶠ[𝓝 x] fun y ↦ ε * f y := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact h y hy

/-- The derivative in the reflected coordinate reverses the parity. -/
theorem partialDeriv_same (h : IsReflectionEigenfunctionOn U i ε f) (hU : IsOpen U)
    (hσ : ∀ x ∈ U, coordinateReflection i x ∈ U) (hf : DifferentiableOn ℝ f U) :
    IsReflectionEigenfunctionOn U i (-ε) (∂[i] f) := by
  intro x hx
  have hchain := partialDeriv_comp_coordinateReflection_same i f x
    ((hf _ (hσ x hx)).differentiableAt (hU.mem_nhds (hσ x hx)))
  rw [partialDeriv_congr_nhds i (h.comp_eventuallyEq hU hx)] at hchain
  have hsmul : (∂[i] (fun y ↦ ε * f y)) x = ε * (∂[i] f) x := by
    have := partialDeriv_const_smul (i := i) (f := f) (x := x) ε
    simpa [smul_eq_mul] using this
  rw [hsmul] at hchain
  linarith

/-- A derivative in another coordinate keeps the parity. -/
theorem partialDeriv_of_ne (h : IsReflectionEigenfunctionOn U i ε f) (hU : IsOpen U)
    (hσ : ∀ x ∈ U, coordinateReflection i x ∈ U) (hf : DifferentiableOn ℝ f U) {j : Fin n}
    (hji : j ≠ i) : IsReflectionEigenfunctionOn U i ε (∂[j] f) := by
  intro x hx
  have hchain := partialDeriv_comp_coordinateReflection_of_ne i j hji f x
    ((hf _ (hσ x hx)).differentiableAt (hU.mem_nhds (hσ x hx)))
  rw [partialDeriv_congr_nhds j (h.comp_eventuallyEq hU hx)] at hchain
  have hsmul : (∂[j] (fun y ↦ ε * f y)) x = ε * (∂[j] f) x := by
    have := partialDeriv_const_smul (i := j) (f := f) (x := x) ε
    simpa [smul_eq_mul] using this
  rw [hsmul] at hchain
  exact hchain.symm

/-- The parity of an iterated derivative is that of the function times `(-1)` per derivative in
the reflected coordinate. -/
theorem iteratedPartialDeriv (h : IsReflectionEigenfunctionOn U i ε f) (hU : IsOpen U)
    (hσ : ∀ x ∈ U, coordinateReflection i x ∈ U) (indices : List (Fin n))
    (hf : ContDiffOn ℝ indices.length f U) :
    IsReflectionEigenfunctionOn U i (ε * (-1) ^ indices.count i)
      (PDE.iteratedPartialDeriv indices f) := by
  induction indices with
  | nil => simpa [PDE.iteratedPartialDeriv] using h
  | cons j rest ih =>
    have hrest : ContDiffOn ℝ rest.length f U := hf.of_le (by simp)
    have hdiff : DifferentiableOn ℝ (PDE.iteratedPartialDeriv rest f) U :=
      (contDiffOn_iteratedPartialDeriv hU rest (m := 1) (by simpa using hf)).differentiableOn
        (by norm_num)
    change IsReflectionEigenfunctionOn U i _ (∂[j] (PDE.iteratedPartialDeriv rest f))
    by_cases hji : j = i
    · subst hji
      have := (ih hrest).partialDeriv_same hU hσ hdiff
      simpa [List.count_cons, pow_succ, mul_neg, mul_comm, mul_left_comm] using this
    · have := (ih hrest).partialDeriv_of_ne hU hσ hdiff hji
      simpa [List.count_cons, hji] using this

/-- An odd function vanishes at the fixed points of the reflection. -/
theorem eq_zero_of_apply_eq_zero (h : IsReflectionEigenfunctionOn U i (-1) f) {x : ℝ^n} (hx : x ∈ U)
    (hxi : x i = 0) : f x = 0 := by
  have hfix : coordinateReflection i x = x :=
    (coordinateReflection_eq_self_iff i x).2 (by simpa [coordinateHyperplane] using hxi)
  have := h x hx
  rw [hfix] at this
  linarith

/-- The limit of an odd function at a point approached by fixed points of the reflection in `U` is
zero. -/
theorem eq_zero_of_tendsto (h : IsReflectionEigenfunctionOn U i (-1) f) {p : ℝ^n} {L : ℝ}
    (hne : (𝓝[U ∩ {x | x i = 0}] p).NeBot) (ht : Tendsto f (𝓝[U] p) (𝓝 L)) : L = 0 := by
  have ht' : Tendsto f (𝓝[U ∩ {x | x i = 0}] p) (𝓝 L) :=
    ht.mono_left (nhdsWithin_mono _ inter_subset_left)
  have hzero : Tendsto f (𝓝[U ∩ {x | x i = 0}] p) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (h.eq_zero_of_apply_eq_zero hx.1 hx.2).symm
  exact tendsto_nhds_unique ht' hzero

end IsReflectionEigenfunctionOn

/-- A function vanishing on the part of the hyperplane `{xᵢ = 0}` in an open set `U` has
vanishing tangential derivatives there. -/
theorem partialDeriv_eq_zero_of_eqOn_hyperplane {i j : Fin n} (hji : j ≠ i) {U : Set (ℝ^n)}
    (hU : IsOpen U) {f : ℝ^n → ℝ} (hf : ∀ x ∈ U, x i = 0 → f x = 0) {x : ℝ^n} (hx : x ∈ U)
    (hxi : x i = 0) (hdiff : DifferentiableAt ℝ f x) : (∂[j] f) x = 0 := by
  rw [partialDeriv_eq_deriv_coordinateLine j x hdiff]
  have hline : f ∘ coordinateLine j x =ᶠ[𝓝 (x j)] fun _ ↦ 0 := by
    have hcont : Continuous (coordinateLine j x) := by
      unfold coordinateLine
      fun_prop
    have hmem : coordinateLine j x (x j) ∈ U := by rw [coordinateLine_self]; exact hx
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hmem)] with s hs
    refine hf _ hs ?_
    rw [show coordinateLine j x s i = x i by simp [coordinateLine, Ne.symm hji]]
    exact hxi
  rw [hline.deriv_eq]
  simp

/-- Iterated tangential derivatives of a `C^k` function vanishing on the part of the hyperplane in
`U` vanish there. -/
theorem iteratedPartialDeriv_replicate_eq_zero {i j : Fin n} (hji : j ≠ i) {U : Set (ℝ^n)}
    (hU : IsOpen U) {f : ℝ^n → ℝ} {k : ℕ} (hf : ContDiffOn ℝ k f U)
    (hzero : ∀ x ∈ U, x i = 0 → f x = 0) :
    ∀ x ∈ U, x i = 0 → PDE.iteratedPartialDeriv (List.replicate k j) f x = 0 := by
  induction k with
  | zero => simpa [PDE.iteratedPartialDeriv] using hzero
  | succ k ih =>
    intro x hx hxi
    have hk : ContDiffOn ℝ k f U := hf.of_le (by norm_cast; omega)
    have hdiff : DifferentiableOn ℝ (PDE.iteratedPartialDeriv (List.replicate k j) f) U :=
      (contDiffOn_iteratedPartialDeriv hU (List.replicate k j) (m := 1)
        (by simpa using hf)).differentiableOn (by norm_num)
    rw [List.replicate_succ]
    exact partialDeriv_eq_zero_of_eqOn_hyperplane hji hU (ih hk) hx hxi
      ((hdiff x hx).differentiableAt (hU.mem_nhds hx))

/-- The limit of a function vanishing on the part of the hyperplane in `U`, at a point approached
by such points, is zero. -/
theorem eq_zero_of_tendsto_of_eqOn_hyperplane {i : Fin n} {U : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ∀ x ∈ U, x i = 0 → f x = 0) {p : ℝ^n} {L : ℝ} (hne : (𝓝[U ∩ {x | x i = 0}] p).NeBot)
    (ht : Tendsto f (𝓝[U] p) (𝓝 L)) : L = 0 := by
  have ht' : Tendsto f (𝓝[U ∩ {x | x i = 0}] p) (𝓝 L) :=
    ht.mono_left (nhdsWithin_mono _ inter_subset_left)
  have hzero : Tendsto f (𝓝[U ∩ {x | x i = 0}] p) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hf x hx.1 hx.2).symm
  exact tendsto_nhds_unique ht' hzero

end PDE.Common

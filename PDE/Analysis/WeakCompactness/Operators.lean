/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Strongly convergent self-adjoint regularizers and weak limits

Let `Qᵢ` be self-adjoint operators on a real Hilbert space converging strongly to the
identity. If `uᵢ ⇀ u` weakly with `‖uᵢ‖ ≤ R`, then `Qᵢ uᵢ ⇀ u`. Moving `Qᵢ` to the test
vector reduces the claim to pairing a strongly convergent sequence of functionals with a
bounded weakly convergent sequence. Joint weak compactness then passes a regularized graph
relation `B yᵢ = Qᵢ xᵢ` and a regularized linear equation `zᵢ = Qᵢ (A yᵢ) + Qᵢ f` to the
limit.

Two auxiliary facts: squared norm bounds pass to weak limits, and if `yᵢ` is bounded and
`B yᵢ` converges in norm, the limit lies in the range of `B`.
-/

@[expose] public section

namespace PDE.Analysis.WeakCompactness

open Filter
open scoped InnerProductSpace Topology

/-- Squared norm bounds pass to weak limits in a real normed space. -/
theorem norm_sq_le_of_tendsto_of_norm_sq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → E} {uLimit : E} {C : ℝ}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l
      (𝓝 (toWeakSpace ℝ E uLimit)))
    (hbound : ∀ᶠ i in l, ‖u i‖ ^ 2 ≤ C) :
    ‖uLimit‖ ^ 2 ≤ C := by
  obtain ⟨i, hi⟩ := hbound.exists
  have hC : 0 ≤ C := (sq_nonneg ‖u i‖).trans hi
  have hsqrt : ∀ᶠ i in l, ‖u i‖ ≤ Real.sqrt C :=
    hbound.mono fun i hi ↦ (Real.le_sqrt (norm_nonneg _) hC).mpr hi
  have hlim := norm_le_of_tendsto_of_norm_le hu hsqrt
  exact (Real.le_sqrt (norm_nonneg _) hC).mp hlim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι}

/-- If `yᵢ` is bounded in a real Hilbert space and `B yᵢ → x` in norm, then `x = B v` for
some `v`. The range of `B` need not be closed. -/
theorem exists_preimage_of_isBounded_range_of_tendsto
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [l.NeBot]
    (B : H →L[ℝ] X) (y : ι → H)
    (hy : Bornology.IsBounded (Set.range y)) {x : X}
    (hstrong : Tendsto (fun i ↦ B (y i)) l (𝓝 x)) :
    ∃ v : H, B v = x := by
  obtain ⟨v, W, hW, hv⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter l y hy
  have hweak : Tendsto (fun i ↦ toWeakSpace ℝ X (B (y i))) W
      (𝓝 (toWeakSpace ℝ X (B v))) :=
    (WeakSpace.map B).continuous.continuousAt.tendsto.comp hv
  have hstrongW : Tendsto (fun i ↦ toWeakSpace ℝ X (B (y i))) W
      (𝓝 (toWeakSpace ℝ X x)) :=
    (toWeakSpaceCLM ℝ X).continuous.continuousAt.tendsto.comp (hstrong.mono_left hW)
  exact ⟨v, (toWeakSpace ℝ X).injective (tendsto_nhds_unique hweak hstrongW)⟩

/-- If self-adjoint operators `Qᵢ` converge strongly to the identity and `uᵢ ⇀ u` weakly
with `‖uᵢ‖ ≤ R`, then `Qᵢ uᵢ ⇀ u` weakly. -/
theorem tendsto_selfAdjoint_apply
    (Q : ι → H →L[ℝ] H)
    (hQ : ∀ x, Tendsto (fun i ↦ Q i x) l (𝓝 x))
    (hself : ∀ i x y, ⟪Q i x, y⟫_ℝ = ⟪x, Q i y⟫_ℝ)
    {u : ι → H} {uLimit : H}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l
      (𝓝 (toWeakSpace ℝ H uLimit)))
    (R : ℝ) (hR : ∀ i, ‖u i‖ ≤ R) :
    Tendsto (fun i ↦ toWeakSpace ℝ H (Q i (u i))) l
      (𝓝 (toWeakSpace ℝ H uLimit)) := by
  have hinj : Function.Injective (topDualPairing ℝ H).flip := by
    intro x y h
    apply ext_inner_left ℝ
    intro v
    exact DFunLike.congr_fun h (innerSL ℝ v)
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro φ
  let v := (InnerProductSpace.toDual ℝ H).symm φ
  have hp := tendsto_dual_apply_of_tendsto_strong_weak
    ((innerSL ℝ).continuous.continuousAt.tendsto.comp (hQ v)) hu R hR
  change Tendsto (fun i ↦ φ (Q i (u i))) l (𝓝 (φ uLimit))
  simpa only [Function.comp_apply, innerSL_apply_apply, hself, v,
    InnerProductSpace.toDual_symm_apply] using hp

/-- Let `x`, `y`, `z` be bounded families in real Hilbert spaces `X`, `Y`, `Z` with
`B (y i) = QX i (x i)` and `z i = QZ i (A (y i)) + QZ i f`, where `QX i` and `QZ i` are
self-adjoint and converge strongly to the identity. Along some ultrafilter refining `l` the
three families converge weakly, and their limits satisfy `B yLimit = xLimit` and
`zLimit = A yLimit + f`. -/
theorem exists_weak_limit_regularized_graph
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    [l.NeBot]
    (QX : ι → X →L[ℝ] X) (QZ : ι → Z →L[ℝ] Z)
    (hQX : ∀ x, Tendsto (fun i ↦ QX i x) l (𝓝 x))
    (hQZ : ∀ z, Tendsto (fun i ↦ QZ i z) l (𝓝 z))
    (hselfX : ∀ i x y, ⟪QX i x, y⟫_ℝ = ⟪x, QX i y⟫_ℝ)
    (hselfZ : ∀ i x y, ⟪QZ i x, y⟫_ℝ = ⟪x, QZ i y⟫_ℝ)
    (B : Y →L[ℝ] X) (A : Y →L[ℝ] Z)
    (x : ι → X) (y : ι → Y) (z : ι → Z) (f : Z)
    (hx : Bornology.IsBounded (Set.range x))
    (hy : Bornology.IsBounded (Set.range y))
    (hz : Bornology.IsBounded (Set.range z))
    (hxy : ∀ i, B (y i) = QX i (x i))
    (hzAf : ∀ i, z i = QZ i (A (y i)) + QZ i f) :
    ∃ (xLimit : X) (yLimit : Y) (zLimit : Z) (U : Ultrafilter ι),
      (U : Filter ι) ≤ l ∧
      Tendsto (fun i ↦ toWeakSpace ℝ X (x i)) U (𝓝 (toWeakSpace ℝ X xLimit)) ∧
      Tendsto (fun i ↦ toWeakSpace ℝ Y (y i)) U (𝓝 (toWeakSpace ℝ Y yLimit)) ∧
      Tendsto (fun i ↦ toWeakSpace ℝ Z (z i)) U (𝓝 (toWeakSpace ℝ Z zLimit)) ∧
      B yLimit = xLimit ∧ zLimit = A yLimit + f := by
  obtain ⟨xLimit, U₁, hU₁, hx₁⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter l x hx
  obtain ⟨yLimit, U₂, hU₂, hy₂⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₁ : Filter ι) y hy
  obtain ⟨zLimit, U, hU, hzweak⟩ :=
    exists_ultrafilter_tendsto_weak_of_isBounded_range_filter (U₂ : Filter ι) z hz
  have hUl := hU.trans (hU₂.trans hU₁)
  have hxweak := hx₁.mono_left (hU.trans hU₂)
  have hyweak := hy₂.mono_left hU
  obtain ⟨R, hR⟩ := hx.exists_norm_le
  have hQx := tendsto_selfAdjoint_apply QX (fun x ↦ (hQX x).mono_left hUl)
    hselfX hxweak R (fun i ↦ hR _ (Set.mem_range_self i))
  have hBy : Tendsto (fun i ↦ toWeakSpace ℝ X (B (y i))) U
      (𝓝 (toWeakSpace ℝ X (B yLimit))) :=
    (WeakSpace.map B).continuous.continuousAt.tendsto.comp hyweak
  have hBlim : B yLimit = xLimit := by
    apply (toWeakSpace ℝ X).injective
    apply tendsto_nhds_unique hBy
    simpa only [hxy] using hQx
  have hAy : Tendsto (fun i ↦ toWeakSpace ℝ Z (A (y i))) U
      (𝓝 (toWeakSpace ℝ Z (A yLimit))) :=
    (WeakSpace.map A).continuous.continuousAt.tendsto.comp hyweak
  obtain ⟨S, hS⟩ := hy.exists_norm_le
  have hQAy := tendsto_selfAdjoint_apply QZ (fun z ↦ (hQZ z).mono_left hUl)
    hselfZ hAy (‖A‖ * S) (fun i ↦ (A.le_opNorm (y i)).trans
      (mul_le_mul_of_nonneg_left (hS _ (Set.mem_range_self i)) (norm_nonneg _)))
  have hQf : Tendsto (fun i ↦ toWeakSpace ℝ Z (QZ i f)) U
      (𝓝 (toWeakSpace ℝ Z f)) :=
    (toWeakSpaceCLM ℝ Z).continuous.continuousAt.tendsto.comp ((hQZ f).mono_left hUl)
  have hright : Tendsto (fun i ↦ toWeakSpace ℝ Z (z i)) U
      (𝓝 (toWeakSpace ℝ Z (A yLimit + f))) := by
    simpa only [hzAf, map_add] using hQAy.add hQf
  exact ⟨xLimit, yLimit, zLimit, U, hUl, hxweak, hyweak, hzweak, hBlim,
    (toWeakSpace ℝ Z).injective (tendsto_nhds_unique hzweak hright)⟩

end PDE.Analysis.WeakCompactness

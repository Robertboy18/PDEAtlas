/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Weak compactness in reflexive spaces

A norm-bounded set in a reflexive real or complex normed space has weakly compact
weak closure. Reflexivity is the surjectivity of Mathlib's canonical map into the
continuous double dual, and the proof combines Banach–Alaoglu with Mathlib's embedding
of `WeakSpace` into the weak-star double dual. Real Hilbert spaces are reflexive by the
Fréchet–Riesz representation theorem. Evans, Appendix D.4, Theorem 3, states the sequential
form for reflexive Banach spaces and uses it in the Galerkin existence proof of §7.1.2.

## Main results

* `WeakCompactness.isCompact_closure_of_isBounded_of_reflexive`: bounded sets of a
  reflexive space are weakly relatively compact.
* `inclusionInDoubleDual_surjective`: a real Hilbert space is reflexive.
* `WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter`: a bounded
  family in a real Hilbert space converges weakly along an ultrafilter refining any
  nontrivial filter.
* `WeakCompactness.norm_le_of_tendsto_of_norm_le`: the norm is weakly lower
  semicontinuous.
* `WeakCompactness.tendsto_strong_of_norm`: the Radon–Riesz property of real inner
  product spaces.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.3, Theorem 2, p. 722 (Riesz representation),
  Appendix D.4, Theorem 3, and the lower semicontinuity of the norm, p. 723, and §7.1.2, step 1
  of the proof of Theorem 3, (27), p. 378. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set

namespace PDE.Analysis

/-- Surjectivity of the canonical double-dual map is unchanged when the domain
has the weak topology and the codomain has the weak-star topology. -/
theorem inclusionInDoubleDualWeak_surjective_of_surjective
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak 𝕜 E) := by
  intro F
  obtain ⟨x, hx⟩ := h (WeakDual.toStrongDual F)
  refine ⟨toWeakSpace 𝕜 E x, ?_⟩
  apply WeakDual.toStrongDual.injective
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun G : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ G f) hx

/-- In a reflexive real or complex normed space, the weak closure of a
norm-bounded set is weakly compact. Reflexivity is the surjectivity of the
canonical map into the continuous double dual. -/
theorem WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (S : Set (WeakSpace 𝕜 E))
    (hS : Bornology.IsBounded ((toWeakSpace 𝕜 E) ⁻¹' S)) :
    IsCompact (closure S) := by
  apply NormedSpace.isCompact_closure_of_isBounded 𝕜 E S hS
  intro F _
  exact inclusionInDoubleDualWeak_surjective_of_surjective hreflexive F

/-- In a reflexive real or complex normed space, a norm-bounded family has a weakly
convergent ultrafilter refinement of any prescribed nontrivial filter. -/
theorem WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter_of_reflexive
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (u : ι → E) (hu : Bornology.IsBounded (Set.range u)) :
    ∃ (w : WeakSpace 𝕜 E) (U : Ultrafilter ι),
      (U : Filter ι) ≤ l ∧
      Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) U (nhds w) := by
  let weakSeq : ι → WeakSpace 𝕜 E := fun i ↦ toWeakSpace 𝕜 E (u i)
  let S : Set (WeakSpace 𝕜 E) := Set.range weakSeq
  have hpre : (toWeakSpace 𝕜 E) ⁻¹' S = Set.range u := by
    ext x
    simp [S, weakSeq]
  have hbounded : Bornology.IsBounded ((toWeakSpace 𝕜 E) ⁻¹' S) := by
    rwa [hpre]
  have hcompact := WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
    hreflexive S hbounded
  have hmap : Filter.map weakSeq l ≤ Filter.principal (closure S) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Filter.Eventually.of_forall fun i ↦ subset_closure ⟨i, rfl⟩
  obtain ⟨w, _, hw⟩ := hcompact.exists_mapClusterPt hmap
  obtain ⟨U, hU, htendsto⟩ := mapClusterPt_iff_ultrafilter.mp hw
  exact ⟨w, U, hU, htendsto⟩


section NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- If `uᵢ ⇀ w` weakly, then `ℓ uᵢ → ℓ w` for every continuous linear functional `ℓ`. -/
theorem WeakCompactness.tendsto_evaluation
    {ι : Type*} {l : Filter ι} {u : ι → WeakSpace ℝ H} {w : WeakSpace ℝ H}
    (hu : Filter.Tendsto u l (nhds w)) (ell : StrongDual ℝ H) :
    Filter.Tendsto (fun i ↦ ell ((toWeakSpace ℝ H).symm (u i))) l
      (nhds (ell ((toWeakSpace ℝ H).symm w))) := by
  change Filter.Tendsto
    (((WeakBilin.eval (topDualPairing ℝ H).flip ell) :
      WeakSpace ℝ H → ℝ) ∘ u) l
    (nhds (WeakBilin.eval (topDualPairing ℝ H).flip ell w))
  exact
    (WeakBilin.eval (topDualPairing ℝ H).flip ell).continuous.continuousAt.tendsto.comp hu

/-- If `ℓᵢ → ℓ` in operator norm and `wᵢ ⇀ w` weakly with `‖wᵢ‖ ≤ R`, then
`ℓᵢ wᵢ → ℓ w`. -/
theorem WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
    {ι : Type*} {l : Filter ι}
    {ell : ι → StrongDual ℝ H} {ellLimit : StrongDual ℝ H}
    (hell : Tendsto ell l (nhds ellLimit))
    {w : ι → H} {wLimit : H}
    (hw : Tendsto (fun i ↦ toWeakSpace ℝ H (w i)) l
      (nhds (toWeakSpace ℝ H wLimit)))
    (R : ℝ) (hwR : ∀ i, ‖w i‖ ≤ R) :
    Tendsto (fun i ↦ ell i (w i)) l (nhds (ellLimit wLimit)) := by
  have herror :
      Tendsto (fun i ↦ (ell i - ellLimit) (w i)) l (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun i ↦ R * ‖ell i - ellLimit‖)
    · intro i
      calc
        ‖(ell i - ellLimit) (w i)‖ ≤
            ‖ell i - ellLimit‖ * ‖w i‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖ell i - ellLimit‖ * R :=
          mul_le_mul_of_nonneg_left (hwR i) (norm_nonneg _)
        _ = R * ‖ell i - ellLimit‖ := mul_comm _ _
    · have hzero :
          Tendsto (fun i ↦ ‖ell i - ellLimit‖) l (nhds 0) := by
        have hconst :
            Tendsto (fun _ : ι ↦ ellLimit) l (nhds ellLimit) :=
          tendsto_const_nhds
        simpa using (hell.sub hconst).norm
      simpa using hzero.const_mul R
  have hfixed :
      Tendsto (fun i ↦ ellLimit (w i)) l
        (nhds (ellLimit wLimit)) := by
    simpa using WeakCompactness.tendsto_evaluation hw ellLimit
  have hsum := herror.add hfixed
  convert hsum using 1
  · funext i
    simp
  · simp


/-- Weak lower semicontinuity of the norm in a real normed space: if `uᵢ ⇀ w` weakly and
eventually `‖uᵢ‖ ≤ C`, then `‖w‖ ≤ C`. The proof tests against a norming functional at
`w` given by Hahn–Banach. -/
theorem WeakCompactness.norm_le_of_tendsto_of_norm_le
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → WeakSpace ℝ H} {w : WeakSpace ℝ H} {C : ℝ}
    (hu : Filter.Tendsto u l (nhds w))
    (hbound : ∀ᶠ i in l, ‖(toWeakSpace ℝ H).symm (u i)‖ ≤ C) :
    ‖(toWeakSpace ℝ H).symm w‖ ≤ C := by
  obtain ⟨ell, hnorm, hell⟩ := exists_dual_vector'' ℝ ((toWeakSpace ℝ H).symm w)
  have hvalue : ∀ᶠ i in l, ell ((toWeakSpace ℝ H).symm (u i)) ≤ C := by
    filter_upwards [hbound] with i hi
    calc
      ell ((toWeakSpace ℝ H).symm (u i)) ≤
          ‖ell ((toWeakSpace ℝ H).symm (u i))‖ := le_abs_self _
      _ ≤ ‖(toWeakSpace ℝ H).symm (u i)‖ := by
        simpa only [one_mul] using ell.le_of_opNorm_le hnorm ((toWeakSpace ℝ H).symm (u i))
      _ ≤ C := hi
  simpa [hell] using le_of_tendsto (WeakCompactness.tendsto_evaluation hu ell) hvalue

end NormedSpace

/-- In a real inner product space, if `xᵢ → x₀` in norm and `yᵢ ⇀ y₀` weakly with
`‖yᵢ‖ ≤ R`, then `⟪yᵢ - v, xᵢ - z⟫ → ⟪y₀ - v, x₀ - z⟫` for all fixed `v` and `z`. -/
theorem WeakCompactness.tendsto_inner_sub_of_tendsto_strong_weak
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} {l : Filter ι} {x y : ι → H} {x₀ y₀ : H}
    (hx : Tendsto x l (nhds x₀))
    (hy : Tendsto (fun i ↦ toWeakSpace ℝ H (y i)) l (nhds (toWeakSpace ℝ H y₀)))
    (R : ℝ) (hR : ∀ i, ‖y i‖ ≤ R) (z v : H) :
    Tendsto (fun i ↦ inner ℝ (y i - v) (x i - z)) l
      (nhds (inner ℝ (y₀ - v) (x₀ - z))) := by
  have hpair := WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
    ((innerSL ℝ).continuous.tendsto (x₀ - z) |>.comp (hx.sub_const z)) hy R hR
  have hfixed : Tendsto (fun i ↦ inner ℝ (x i - z) v) l
      (nhds (inner ℝ (x₀ - z) v)) :=
    (hx.sub_const z).inner tendsto_const_nhds
  have hp : Tendsto (fun i ↦ inner ℝ (x i - z) (y i - v)) l
      (nhds (inner ℝ (x₀ - z) (y₀ - v))) := by
    simpa only [Function.comp_apply, innerSL_apply_apply, ← inner_sub_right]
      using hpair.sub hfixed
  simpa only [real_inner_comm] using hp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The canonical map from a real Hilbert space into its continuous double
dual is surjective.  This is the reflexivity of Hilbert spaces, proved by
pulling a double-dual functional back along the Riesz isometry. -/
theorem inclusionInDoubleDual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro F
  let e := InnerProductSpace.toDual ℝ H
  let h : StrongDual ℝ H := F.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let x : H := e.symm h
  refine ⟨x, ContinuousLinearMap.ext (fun f ↦ ?_)⟩
  let y : H := e.symm f
  have hfy : e y = f := e.apply_symm_apply f
  change f x = F f
  rw [← hfy]
  change inner ℝ y x = F (e y)
  rw [real_inner_comm]
  rw [show x = e.symm h from rfl, InnerProductSpace.toDual_symm_apply]
  rfl

/-- The weak closure of a norm-bounded set in a real Hilbert space is weakly
compact.  Here `S` is expressed in `WeakSpace ℝ H`; its inverse image under
`toWeakSpace` is the same underlying set equipped with the norm topology. -/
theorem WeakCompactness.isCompact_closure_of_isBounded
    (S : Set (WeakSpace ℝ H))
    (hS : Bornology.IsBounded ((toWeakSpace ℝ H) ⁻¹' S)) :
    IsCompact (closure S) := by
  exact WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
    inclusionInDoubleDual_surjective S hS

/-- A weakly closed, norm-bounded subset of a real Hilbert space is weakly
compact. -/
theorem WeakCompactness.isCompact_of_isClosed_of_isBounded
    {S : Set (WeakSpace ℝ H)}
    (hclosed : IsClosed S)
    (hbounded : Bornology.IsBounded ((toWeakSpace ℝ H) ⁻¹' S)) :
    IsCompact S := by
  rw [← hclosed.closure_eq]
  exact WeakCompactness.isCompact_closure_of_isBounded S hbounded

/-- A norm-bounded family indexed by a nontrivial filter has a weakly
convergent ultrafilter refinement. -/
theorem WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (u : ι → H) (hu : Bornology.IsBounded (Set.range u)) :
    ∃ (w : WeakSpace ℝ H) (U : Ultrafilter ι),
      (U : Filter ι) ≤ l ∧
      Filter.Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) U (nhds w) := by
  exact WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter_of_reflexive
    inclusionInDoubleDual_surjective l u hu

/--
A norm-bounded family in a real Hilbert space `H` converges weakly to some `uLimit : H`
along an ultrafilter refining the prescribed filter. This is
`exists_ultrafilter_tendsto_of_isBounded_range_filter` with the limit written as an element
of `H` instead of `WeakSpace ℝ H`, so that refinements in several spaces can be chained.
-/
theorem WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (u : ι → H) (hu : Bornology.IsBounded (Set.range u)) :
    ∃ (uLimit : H) (U : Ultrafilter ι),
      (U : Filter ι) ≤ l ∧
      Filter.Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) U
        (nhds (toWeakSpace ℝ H uLimit)) := by
  obtain ⟨w, U, hU, huWeak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      l u hu
  exact ⟨(toWeakSpace ℝ H).symm w, U, hU, by simpa using huWeak⟩

omit [CompleteSpace H] in
/-- A nonnegative weighted sum of two squared norms is weakly lower semicontinuous: if
`uᵢ ⇀ u` and `vᵢ ⇀ v` weakly in real inner product spaces, `a, b ≥ 0`, and eventually
`a ‖uᵢ‖² + b ‖vᵢ‖² ≤ C`, then `a ‖u‖² + b ‖v‖² ≤ C`. -/
theorem WeakCompactness.weighted_norm_sq_add_le_of_tendsto_weak
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → H} {uLimit : H} {v : ι → K} {vLimit : K}
    {a b C : ℝ}
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l
      (nhds (toWeakSpace ℝ H uLimit)))
    (hv : Filter.Tendsto (fun i ↦ toWeakSpace ℝ K (v i)) l
      (nhds (toWeakSpace ℝ K vLimit)))
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ᶠ i in l, a * ‖u i‖ ^ 2 + b * ‖v i‖ ^ 2 ≤ C) :
    a * ‖uLimit‖ ^ 2 + b * ‖vLimit‖ ^ 2 ≤ C := by
  let energyLimit := a * ‖uLimit‖ ^ 2 + b * ‖vLimit‖ ^ 2
  have huInner : Filter.Tendsto (fun i ↦ inner ℝ uLimit (u i)) l
      (nhds (inner ℝ uLimit uLimit)) := by
    simpa only [LinearEquiv.symm_apply_apply, innerSL_apply_apply] using
      WeakCompactness.tendsto_evaluation hu (innerSL ℝ uLimit)
  have hvInner : Filter.Tendsto (fun i ↦ inner ℝ vLimit (v i)) l
      (nhds (inner ℝ vLimit vLimit)) := by
    simpa only [LinearEquiv.symm_apply_apply, innerSL_apply_apply] using
      WeakCompactness.tendsto_evaluation hv (innerSL ℝ vLimit)
  have henergy : Filter.Tendsto
      (fun i ↦ a * inner ℝ uLimit (u i) + b * inner ℝ vLimit (v i)) l
      (nhds energyLimit) := by
    simpa only [energyLimit, real_inner_self_eq_norm_sq] using
      (huInner.const_mul a).add (hvInner.const_mul b)
  have henergyBound : ∀ᶠ i in l,
      a * inner ℝ uLimit (u i) + b * inner ℝ vLimit (v i) ≤
        (energyLimit + C) / 2 := by
    filter_upwards [hbound] with i hi
    have huCauchy : inner ℝ uLimit (u i) ≤ ‖uLimit‖ * ‖u i‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have hvCauchy : inner ℝ vLimit (v i) ≤ ‖vLimit‖ * ‖v i‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have huYoung : 2 * (a * inner ℝ uLimit (u i)) ≤
        a * ‖uLimit‖ ^ 2 + a * ‖u i‖ ^ 2 := by
      have hinner := mul_le_mul_of_nonneg_left huCauchy ha
      have hsquare := mul_le_mul_of_nonneg_left
        (two_mul_le_add_sq ‖uLimit‖ ‖u i‖) ha
      calc
        2 * (a * inner ℝ uLimit (u i)) ≤
            2 * (a * (‖uLimit‖ * ‖u i‖)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = a * (2 * (‖uLimit‖ * ‖u i‖)) := by ring
        _ ≤ a * (‖uLimit‖ ^ 2 + ‖u i‖ ^ 2) := by
          simpa only [mul_assoc] using hsquare
        _ = a * ‖uLimit‖ ^ 2 + a * ‖u i‖ ^ 2 := by ring
    have hvYoung : 2 * (b * inner ℝ vLimit (v i)) ≤
        b * ‖vLimit‖ ^ 2 + b * ‖v i‖ ^ 2 := by
      have hinner := mul_le_mul_of_nonneg_left hvCauchy hb
      have hsquare := mul_le_mul_of_nonneg_left
        (two_mul_le_add_sq ‖vLimit‖ ‖v i‖) hb
      calc
        2 * (b * inner ℝ vLimit (v i)) ≤
            2 * (b * (‖vLimit‖ * ‖v i‖)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = b * (2 * (‖vLimit‖ * ‖v i‖)) := by ring
        _ ≤ b * (‖vLimit‖ ^ 2 + ‖v i‖ ^ 2) := by
          simpa only [mul_assoc] using hsquare
        _ = b * ‖vLimit‖ ^ 2 + b * ‖v i‖ ^ 2 := by ring
    dsimp only [energyLimit]
    linarith
  have hlimit := le_of_tendsto henergy henergyBound
  dsimp only [energyLimit] at hlimit ⊢
  linarith

omit [CompleteSpace H] in
/-- The case `a = b = 1` of `weighted_norm_sq_add_le_of_tendsto_weak`. -/
theorem WeakCompactness.norm_sq_add_norm_sq_le_of_tendsto_weak
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → H} {uLimit : H} {v : ι → K} {vLimit : K}
    {C : ℝ}
    (hu : Filter.Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l
      (nhds (toWeakSpace ℝ H uLimit)))
    (hv : Filter.Tendsto (fun i ↦ toWeakSpace ℝ K (v i)) l
      (nhds (toWeakSpace ℝ K vLimit)))
    (hbound : ∀ᶠ i in l, ‖u i‖ ^ 2 + ‖v i‖ ^ 2 ≤ C) :
    ‖uLimit‖ ^ 2 + ‖vLimit‖ ^ 2 ≤ C := by
  simpa only [one_mul] using
    WeakCompactness.weighted_norm_sq_add_le_of_tendsto_weak
      hu hv (a := 1) (b := 1) (by positivity) (by positivity)
        (by simpa only [one_mul] using hbound)

omit [CompleteSpace H] in
/-- Radon–Riesz property: in a real inner product space, weak convergence together with
convergence of norms implies norm convergence. -/
theorem WeakCompactness.tendsto_strong_of_norm
    {ι : Type*} {l : Filter ι} {u : ι → WeakSpace ℝ H} {w : WeakSpace ℝ H}
    (hu : Filter.Tendsto u l (nhds w))
    (hnorm : Filter.Tendsto
      (fun i ↦ ‖(toWeakSpace ℝ H).symm (u i)‖) l
      (nhds ‖(toWeakSpace ℝ H).symm w‖)) :
    Filter.Tendsto (fun i ↦ (toWeakSpace ℝ H).symm (u i)) l
      (nhds ((toWeakSpace ℝ H).symm w)) := by
  let x : ι → H := fun i ↦ (toWeakSpace ℝ H).symm (u i)
  let y : H := (toWeakSpace ℝ H).symm w
  have hinner : Filter.Tendsto (fun i ↦ inner ℝ (x i) y) l
      (nhds (inner ℝ y y)) := by
    simpa [x, y, real_inner_comm] using
      WeakCompactness.tendsto_evaluation hu (innerSL ℝ y)
  have hsq : Filter.Tendsto (fun i ↦ ‖x i - y‖ ^ 2) l (nhds 0) := by
    have hnormSq : Filter.Tendsto (fun i ↦ ‖x i‖ ^ 2) l (nhds (‖y‖ ^ 2)) := by
      simpa only [x, y] using hnorm.pow 2
    have hformula := (hnormSq.sub (hinner.const_mul 2)).add_const (‖y‖ ^ 2)
    convert hformula using 1
    · funext i
      exact norm_sub_sq_real (x i) y
    · rw [real_inner_self_eq_norm_sq]
      ring_nf
  have hnormSub : Filter.Tendsto (fun i ↦ ‖x i - y‖) l (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    convert hsqrt using 1
    · funext i
      exact (Real.sqrt_sq (norm_nonneg (x i - y))).symm
    · simp
  have hsub : Filter.Tendsto (fun i ↦ x i - y) l (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormSub
  simpa only [x, y, sub_add_cancel, zero_add] using hsub.add_const y

end PDE.Analysis

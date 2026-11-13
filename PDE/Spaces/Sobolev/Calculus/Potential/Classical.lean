/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Potential.Convex
public import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# Classical potentials in Sobolev spaces

A continuously varying classical gradient gives a `C¹` potential. On every
relatively compact open subdomain, the classical-to-weak construction
then produces a Sobolev element whose vector-valued weak gradient is the
prescribed field. The subdomain need not have a regular boundary.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace

open GraphSpace

variable {n : ℕ} {Ω V : Set (ℝ^n)} {f : ℝ^n → ℝ} {g : ℝ^n → ℝ^n}

/-- A continuous prescribed classical gradient gives first-order continuous
differentiability on the open domain. -/
theorem contDiffOn_one_of_hasGradientAt
    (hΩ : IsOpen Ω) (hg : ContinuousOn g Ω)
    (hf : ∀ x ∈ Ω, HasGradientAt f (g x) x) :
    ContDiffOn ℝ 1 f Ω := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) hΩ.uniqueDiffOn).mpr
  refine ⟨by simp, fun x ↦ InnerProductSpace.toDual ℝ (ℝ^n) (g x), ?_, ?_⟩
  · exact contDiffOn_zero.mpr
      ((InnerProductSpace.toDual ℝ (ℝ^n)).continuous.comp_continuousOn hg)
  · exact fun x hx ↦ (hf x hx).hasFDerivAt.hasFDerivWithinAt

/-- A classical potential on a neighborhood of a compact closure gives a
Sobolev graph with the same values and gradient at every exponent. -/
theorem exists_wkpSpaceOn_of_hasGradientAt
    (hΩ : IsOpen Ω) (hg : ContinuousOn g Ω)
    (hf : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ u : W^{1,p}(V),
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n V] f ∧
      (∇ u : ℝ^n → ℝ^n) =ᵐ[domainMeasure n V] g := by
  have h := contDiffUpToBoundary_of_contDiffOn hΩ
    (contDiffOn_one_of_hasGradientAt hΩ hg hf) hcompact hVΩ
  have hb := hcompact.isBounded.subset subset_closure
  let u := h.toWkpSpaceOn hV hb p
  refine ⟨u, h.toWkpSpaceOn_base_ae hV hb p, ?_⟩
  have hrows : ∀ᵐ x ∂domainMeasure n V, ∀ i : Fin n,
      (u : WkpAmbientOn n 1 p V) (singleDerivIndex n i) x =
        (∂[i] f) x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [h.toWkpSpaceOn_apply_ae hV hb p (singleDerivIndex n i)] with x hx
    simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hx
  filter_upwards [wkpGradientCLM_apply_ae u, hrows,
    ae_restrict_mem hV.measurableSet] with x hx hrow hxV
  ext i
  rw [hx i, hrow i, ← PDE.gradient_apply_eq_partialDeriv,
    (hf x (hVΩ (subset_closure hxV))).gradient]

/-- Closed differentiable fields on an open convex neighborhood are weak
gradients on every relatively compact open subdomain. -/
theorem exists_wkpSpaceOn_gradient_eq_of_partialDeriv_comm
    (hΩ : IsOpen Ω) (hconvex : Convex ℝ Ω) (hg : DifferentiableOn ℝ g Ω)
    (hcomm : ∀ x ∈ Ω, ∀ i j : Fin n,
      (∂[i] (fun y ↦ g y j)) x = (∂[j] (fun y ↦ g y i)) x)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ u : W^{1,p}(V),
      (∇ u : ℝ^n → ℝ^n) =ᵐ[domainMeasure n V] g := by
  obtain ⟨f, hf⟩ :=
    EuclideanSpace.exists_potential_of_partialDeriv_comm hconvex hΩ hg hcomm
  obtain ⟨u, _, hu⟩ :=
    exists_wkpSpaceOn_of_hasGradientAt hΩ hg.continuousOn hf hV hcompact hVΩ p
  exact ⟨u, hu⟩

end SobolevSpace

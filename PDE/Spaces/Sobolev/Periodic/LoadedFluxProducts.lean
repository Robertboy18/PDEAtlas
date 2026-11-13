/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.FluxProducts
public import PDE.Spaces.Sobolev.Periodic.RescaledConvergence

/-!
# Vanishing corrector pairings for fluxes with a fixed divergence

The loaded weak divergence equation permits compactly localized canonical
H¹ tests. Its cutoff product rule bounds the gradient pairing using only the value
coordinate, the L² load, and the flux norm. Consequently a uniformly bounded flux of
fixed divergence has vanishing weighted pairing with the rescaled gradient of any
periodic Sobolev potential. The potential and its strong value limit come from the
periodic Sobolev construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev Distributions

namespace SobolevSpace.Periodic

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The canonical coordinate divergence equation is the vector weak pairing. -/
theorem inner_gradient_eq_of_weakDivergenceFunctional
    (q : Lp (ℝ^n) 2 (domainMeasure n Ω)) (f : GraphSpace.DerivLp n 2 Ω)
    (hq : GraphSpace.weakDivergenceFunctional
      (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp q) f = 0) (u : H¹₀(Ω)) :
    ⟪q, GraphSpace.gradientCLM u⟫_ℝ = ⟪f, GraphSpace.baseCoordCLM u⟫_ℝ := by
  have h := DFunLike.congr_fun hq u
  rw [GraphSpace.weakDivergenceFunctional_apply, zero_apply,
    sub_eq_zero] at h
  have hQ := Lp.euclideanTuple_coordinates q
  rw [← hQ]
  change ⟪Lp.euclideanTuple (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp q),
    Lp.euclideanTuple (fun i ↦ GraphSpace.derivCoordCLM i u)⟫_ℝ = _
  rw [Lp.inner_euclideanTuple]
  exact h

/-- The loaded weak divergence equation transfers the derivative from a compactly
localized H¹ test to its cutoff, with the expected load term. -/
theorem inner_weighted_wkpGradient_eq (hΩo : IsOpen Ω)
    (q : Lp (ℝ^n) 2 (domainMeasure n Ω)) (f : GraphSpace.DerivLp n 2 Ω)
    (hq : GraphSpace.weakDivergenceFunctional
      (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp q) f = 0)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ Ω) (u : H¹(Ω)) :
    ⟪q, GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.wkpGradientCLM u⟫_ℝ =
      ⟪f, GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.wkpBaseCoordinateCLM u⟫_ℝ -
      ⟪q, Lp.euclideanTuple (fun i ↦ GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i •
        GraphSpace.wkpBaseCoordinateCLM u)⟫_ℝ := by
  let U := GraphSpace.cutoffH1ToH10 hΩo κ hκ u
  have hb : GraphSpace.baseCoordCLM U =
      GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.wkpBaseCoordinateCLM u := by
    change GraphSpace.cutoffLpAt (p := 2) (Ω := Ω) κ (GraphSpace.baseIndex n 1)
      (u : GraphSpace.WkpAmbientOn n 1 2 Ω) = _
    simp only [GraphSpace.cutoffLpAt, GraphSpace.firstOrderRows_baseIndex,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply, GraphSpace.mulLpLeft_apply]
    rfl
  have hd (i : Fin n) : GraphSpace.derivCoordCLM i U =
      GraphSpace.testFunctionLpTop (Ω := Ω) κ •
        GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex n i) u +
      GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i •
        GraphSpace.wkpBaseCoordinateCLM u := by
    change GraphSpace.cutoffLpAt (p := 2) (Ω := Ω) κ (GraphSpace.singleDerivIndex n i)
      (u : GraphSpace.WkpAmbientOn n 1 2 Ω) = _
    simp only [GraphSpace.cutoffLpAt, GraphSpace.firstOrderRows_singleDerivIndex,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      PiLp.proj_apply, GraphSpace.cutoffDerivativeLp_apply]
    rfl
  have hg : GraphSpace.gradientCLM U =
      GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.wkpGradientCLM u +
        Lp.euclideanTuple (fun i ↦ GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i •
          GraphSpace.wkpBaseCoordinateCLM u) := by
    change Lp.euclideanTuple (fun i ↦ GraphSpace.derivCoordCLM i U) =
      GraphSpace.testFunctionLpTop (Ω := Ω) κ •
        Lp.euclideanTuple (fun i ↦
          GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex n i) u) + _
    rw [← Lp.euclideanTuple_lpSMul, ← map_add]
    congr 1
    funext i
    exact hd i
  have he := inner_gradient_eq_of_weakDivergenceFunctional q f hq U
  rw [hg, hb, inner_add_right] at he
  exact eq_sub_of_add_eq he

/-- A uniformly bounded flux with fixed L² divergence has vanishing weighted
pairing with gradients of H¹ fields whose values tend strongly to zero. -/
theorem tendsto_inner_weighted_wkpGradient_eq_zero (hΩo : IsOpen Ω)
    {ι : Type*} {l : Filter ι} (q : ι → Lp (ℝ^n) 2 (domainMeasure n Ω))
    (f : GraphSpace.DerivLp n 2 Ω)
    (hq : ∀ j, GraphSpace.weakDivergenceFunctional
      (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp (q j)) f = 0)
    (R : ℝ) (hR : ∀ j, ‖q j‖ ≤ R) (u : ι → H¹(Ω))
    (hu : Tendsto (fun j ↦ GraphSpace.wkpBaseCoordinateCLM (u j)) l (𝓝 0))
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ Ω) :
    Tendsto (fun j ↦ ⟪q j, GraphSpace.testFunctionLpTop (Ω := Ω) κ •
      GraphSpace.wkpGradientCLM (u j)⟫_ℝ) l (𝓝 0) := by
  let L : GraphSpace.DerivLp n 2 Ω →L[ℝ] GraphSpace.DerivLp n 2 Ω :=
    GraphSpace.mulLpLeft (GraphSpace.testFunctionLpTop (Ω := Ω) κ)
  let M : GraphSpace.DerivLp n 2 Ω →L[ℝ] Lp (ℝ^n) 2 (domainMeasure n Ω) :=
    Lp.euclideanTuple.comp (ContinuousLinearMap.pi fun i ↦
      GraphSpace.mulLpLeft (GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i))
  have hL : Tendsto (fun j ↦ ⟪f, L (GraphSpace.wkpBaseCoordinateCLM (u j))⟫_ℝ) l (𝓝 0) := by
    simpa only [map_zero, Function.comp_def, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply] using (((innerSL ℝ f).comp L).continuous.tendsto 0).comp hu
  have hM : Tendsto (fun j ↦ M (GraphSpace.wkpBaseCoordinateCLM (u j))) l (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using (M.continuous.tendsto 0).comp hu
  have hpair : Tendsto (fun j ↦ ⟪q j, M (GraphSpace.wkpBaseCoordinateCLM (u j))⟫_ℝ)
      l (𝓝 0) := by
    apply squeeze_zero_norm (fun j ↦
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hR j) (norm_nonneg _)))
    simpa only [norm_zero, mul_zero] using hM.norm.const_mul R
  have he (j : ι) :
      ⟪q j, GraphSpace.testFunctionLpTop (Ω := Ω) κ •
        GraphSpace.wkpGradientCLM (u j)⟫_ℝ =
      ⟪f, L (GraphSpace.wkpBaseCoordinateCLM (u j))⟫_ℝ -
        ⟪q j, M (GraphSpace.wkpBaseCoordinateCLM (u j))⟫_ℝ :=
    inner_weighted_wkpGradient_eq hΩo (q j) f (hq j) κ hκ (u j)
  simp_rw [he]
  simpa only [sub_zero] using hL.sub hpair

/-- In particular, the exact rescaled gradient of any periodic Sobolev potential
has zero limiting pairing with a uniformly bounded flux of fixed L² divergence. -/
theorem tendsto_inner_rescale_gradient_of_weakDivergence
    (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    {ι : Type*} {l : Filter ι} (q : ι → Lp (ℝ^n) 2 (domainMeasure n Ω))
    (f : GraphSpace.DerivLp n 2 Ω)
    (hq : ∀ j, GraphSpace.weakDivergenceFunctional
      (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp (q j)) f = 0)
    (R : ℝ) (hR : ∀ j, ‖q j‖ ≤ R)
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (w : h1Space n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ Ω) :
    Tendsto (fun j ↦ ⟪q j, GraphSpace.testFunctionLpTop (Ω := Ω) κ •
      rescaleLp hΩ (ε j) (hε j) (hε1 j) (gradientCLM n w)⟫_ℝ) l (𝓝 0) := by
  simpa only [gradient_scaledPotential] using tendsto_inner_weighted_wkpGradient_eq_zero
    hΩo q f hq R hR
    (fun j ↦ scaledPotential hΩ hΩo.measurableSet w (ε j) (hε j) (hε1 j))
    (tendsto_base_scaledPotential hΩ w ε hε hε1 hΩo.measurableSet ht) κ hκ

end SobolevSpace.Periodic

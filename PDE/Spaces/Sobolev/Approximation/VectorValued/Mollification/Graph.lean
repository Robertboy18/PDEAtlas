/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.WeakDerivatives
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Topology
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Whole-space mollification in the Banach-valued Sobolev graph

Every derivative coordinate is convolved by the same scalar mollifier. Commutation with
weak derivatives places the resulting family in the closed Sobolev graph. For finite
`p ≥ 1`, the Banach-valued `Lp` approximate identity gives convergence in every
coordinate, hence in the finite `PiLp` graph topology.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Positive-scale mollification preserves Banach-valued `Lp` membership for finite
`p ≥ 1`, without a measurable-space structure in the public codomain interface. -/
theorem memLp_mollifyVector (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    {f : ℝ^n → F} (hf : MemLp f p volume) :
    MemLp (mollifyVector μ ε f) p volume := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  exact (MollifyLp.eLpNorm_mollifyVector_le μ hε hp hf).trans_lt hf.eLpNorm_lt_top

/-- The Sobolev bundle obtained by convolving every derivative coordinate with one mollifier. -/
def mollify (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (U : W^{k,p}((⊤ : Opens ℝ^n); F)) : W^{k,p}((⊤ : Opens ℝ^n); F) :=
  ofWeakDerivatives (fun a ↦ mollifyVector μ ε (U.val a))
    (fun a ↦ by
      simpa [domainMeasure] using memLp_mollifyVector μ hε hp
        (by simpa [domainMeasure] using Lp.memLp (U.val a)))
    (fun a ↦ (U.property a).mollifyVector μ hε)

/-- Every mollified graph coordinate has the expected convolved representative. -/
theorem mollify_apply_ae (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (U : W^{k,p}((⊤ : Opens ℝ^n); F)) (a : DerivIndex n k) :
    ((mollify μ hε hp U).val a : ℝ^n → F) =ᵐ[volume]
      mollifyVector μ ε (U.val a) := by
  simpa only [mollify, domainMeasure, Opens.coe_top, Measure.restrict_univ] using
    ofWeakDerivatives_apply_ae (Ω := ⊤) (p := p)
      (fun a ↦ mollifyVector μ ε (U.val a)) _ _ a

/-- The mollified bundle has a globally smooth base representative. -/
theorem mollify_has_smooth_representative (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (hp : p ≠ ∞) (U : W^{k,p}((⊤ : Opens ℝ^n); F)) :
    ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ((mollify μ hε hp U).val (baseIndex n k) : ℝ^n → F) =ᵐ[volume] f := by
  refine ⟨mollifyVector μ ε (U.val (baseIndex n k)), ?_,
    mollify_apply_ae μ hε hp U (baseIndex n k)⟩
  apply mollifyVector_contDiff_of_pos μ hε
  exact locallyIntegrableOn_univ.mp (U.property (baseIndex n k)).locallyIntegrable_f

/-- Positive scales tending to zero approximate every whole-space Banach-valued Sobolev
bundle in its full graph norm, at every finite exponent `p ≥ 1`. -/
theorem mollify_tendsto (μ : Mollifier n) (hp : p ≠ ∞)
    (U : W^{k,p}((⊤ : Opens ℝ^n); F)) (ε : ℕ → ℝ) (hε : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m ↦ mollify μ (hε m) hp U) atTop (𝓝 U) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  apply tendsto_subtype_rng.mpr
  apply ((PiLp.homeomorph p (fun _ : DerivIndex n k ↦
    Lp F p (domainMeasure n (⊤ : Opens ℝ^n)))).symm.continuous.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro a
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (U.val a)).mpr
  have h := mollifyVector_converges_Lp μ p hp ε hε hε0
    (show MemLp (U.val a : ℝ^n → F) p volume by
      simpa [domainMeasure] using Lp.memLp (U.val a))
  apply h.congr'
  filter_upwards [] with m
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
  apply eLpNorm_congr_ae
  filter_upwards [mollify_apply_ae μ (hε m) hp U a] with x hx
  exact congrArg (· - U.val a x) hx.symm

end SobolevSpace.VectorValued

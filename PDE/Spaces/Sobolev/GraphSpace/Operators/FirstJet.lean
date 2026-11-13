/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# Values and weak gradients as one Lp field

The first jet of a scalar Sobolev function is the pair `(u, ∇u)`. Bundling it as
a continuous linear map into `Lᵖ` lets an integral density depend on both entries
without repeatedly choosing representatives. For a finite system, the same construction
records the first jet of every component, so the density may couple them freely.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)
local notation "G" => wkpGradientCLM (n := n) (p := p) (Ω := Ω)

/-- The value and weak gradient together, with the product norm on `ℝ × ℝⁿ`.
This is a bounded linear map at every Sobolev exponent, including infinity. -/
def wkpFirstJetCLM : W^{1,p}(Ω) →L[ℝ] Lp (ℝ × ℝ^n) p μ :=
  ((ContinuousLinearMap.inl ℝ ℝ (ℝ^n)).compLpL p μ).comp B +
    ((ContinuousLinearMap.inr ℝ ℝ (ℝ^n)).compLpL p μ).comp G

/-- The bundled first jet agrees almost everywhere with the value-gradient pair. -/
theorem wkpFirstJetCLM_apply_ae (u : W^{1,p}(Ω)) :
    wkpFirstJetCLM u =ᵐ[μ] fun x ↦ (B u x, ∇ u x) := by
  let L := ContinuousLinearMap.inl ℝ ℝ (ℝ^n)
  let R := ContinuousLinearMap.inr ℝ ℝ (ℝ^n)
  change ((L.compLpL p μ) (B u) + (R.compLpL p μ) (G u)) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_add ((L.compLpL p μ) (B u)) ((R.compLpL p μ) (G u)),
    L.coeFn_compLpL (B u), R.coeFn_compLpL (G u)] with x ha hL hR
  simp only [ha, Pi.add_apply, hL, hR, L, R, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first jets of a finite family, viewed as a single `Lᵖ` field. The state
uses the maximum norm across components and can feed a coupled integral density. -/
def vectorWkpFirstJetCLM : (ι → W^{1,p}(Ω)) →L[ℝ] Lp (ι → ℝ × ℝ^n) p μ :=
  ∑ i : ι,
    ((ContinuousLinearMap.single ℝ (fun _ : ι ↦ ℝ × ℝ^n) i).compLpL p μ).comp
      (wkpFirstJetCLM.comp (ContinuousLinearMap.proj i))

/-- All component value-gradient pairs represent the finite first jet on one
common set of full measure. This includes an empty family. -/
theorem vectorWkpFirstJetCLM_apply_ae (u : ι → W^{1,p}(Ω)) :
    vectorWkpFirstJetCLM u =ᵐ[μ] fun x i ↦ (B (u i) x, ∇ (u i) x) := by
  let L (i : ι) := ContinuousLinearMap.single ℝ (fun _ : ι ↦ ℝ × ℝ^n) i
  let f (i : ι) := wkpFirstJetCLM (u i)
  have hcomp : ∀ᵐ x ∂μ, ∀ i : ι, (L i).compLpL p μ (f i) x = L i (f i x) :=
    ae_all_iff.2 fun i ↦ (L i).coeFn_compLpL (f i)
  have hjet : ∀ᵐ x ∂μ, ∀ i : ι, f i x = (B (u i) x, G (u i) x) :=
    ae_all_iff.2 fun i ↦ wkpFirstJetCLM_apply_ae (u i)
  have hsum : vectorWkpFirstJetCLM u = ∑ i : ι, (L i).compLpL p μ (f i) := by
    simp only [vectorWkpFirstJetCLM, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, L, f]
  rw [hsum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ (L i).compLpL p μ (f i)), hcomp, hjet] with x hs hc hj
  rw [hs]
  simp only [hc, hj, L, ContinuousLinearMap.single_apply]
  exact Finset.univ_sum_single _

end SobolevSpace.GraphSpace

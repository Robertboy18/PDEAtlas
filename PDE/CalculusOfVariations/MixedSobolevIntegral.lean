/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.MixedIntegralEnergy
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# Mixed convergence of finite-power Sobolev energies

For a bounded family in `W¹ᵖ`, weak Sobolev convergence gives weak convergence
of the gradients. If the values also converge strongly in `Lᵖ`, the mixed
integral theorem passes every eventual upper energy bound to the limit.
Convexity is required only in the gradient variable.

The density is evaluated on the base-coordinate and gradient maps. On open sets these
are the usual weak Sobolev coordinates. For arbitrary sets the statement
concerns LeanPDE's weak-derivative graph space. No boundedness or boundary
regularity of the domain is required for this convergence statement.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal Topology

namespace PDE.CalculusOfVariations

/-- Finite-power convex-gradient energies respect weak Sobolev convergence
with strong convergence of the values. Weak convergence and a norm bound
for the gradients follow from the bounded Sobolev family. The density and
derivative growth bounds give integrability and continuity through the
mixed integral theorem. -/
theorem integral_le_of_tendsto_weak_wkp_of_tendsto_base
    {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_one : 1 < p) (hp_top : p ≠ ∞)
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → ℝ × ℝ^n → ℝ^n}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D))
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, Continuous (F x))
    (hDcont : ∀ᵐ x ∂domainMeasure n Ω, Continuous (D x))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ,
      ConvexOn ℝ univ (fun g : ℝ^n ↦ F x (s, g)))
    (hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (g : ℝ^n),
      HasFDerivAt (fun z : ℝ^n ↦ F x (s, z)) (innerSL ℝ (D x (s, g))) g)
    {a b : ℝ^n → ℝ} {C L : ℝ}
    (ha : Integrable a (domainMeasure n Ω)) (hb : MemLp b q (domainMeasure n Ω))
    (hFgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ z,
      |F x z| ≤ a x + C * ‖z‖ ^ p.toReal)
    (hDgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ z,
      ‖D x z‖ ≤ b x + L * ‖z‖ ^ (p.toReal - 1))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,p}(Ω)} {uLimit : W^{1,p}(Ω)}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ (W^{1,p}(Ω)) (u i)) l
      (𝓝 (toWeakSpace ℝ (W^{1,p}(Ω)) uLimit)))
    (hbase : Tendsto (fun i ↦
      wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (u i)) l
      (𝓝 (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) uLimit)))
    (R : ℝ) (huR : ∀ i, ‖u i‖ ≤ R)
    {c : ℝ} (hbound : ∀ᶠ i in l,
      (∫ x, F x
        (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (u i) x,
          ∇ (u i) x) ∂domainMeasure n Ω) ≤ c) :
    (∫ x, F x
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) uLimit x,
        ∇ uLimit x) ∂domainMeasure n Ω) ≤ c := by
  let G : W^{1,p}(Ω) →L[ℝ] Lp (ℝ^n) p (domainMeasure n Ω) :=
    wkpGradientCLM (n := n) (Ω := Ω)
  have hg : Tendsto (fun i ↦ toWeakSpace ℝ (Lp (ℝ^n) p (domainMeasure n Ω))
      (G (u i))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) p (domainMeasure n Ω)) (G uLimit))) :=
    (WeakSpace.map G).continuous.continuousAt.tendsto.comp hu
  have hgR (i : ι) : ‖G (u i)‖ ≤ ‖G‖ * R :=
    (G.le_opNorm (u i)).trans (mul_le_mul_of_nonneg_left (huR i) (norm_nonneg G))
  exact integral_le_of_tendsto_strong_weak_of_convex_gradient
    hp_one hp_top hF hD hFcont hDcont hconvex hderiv ha hb hFgrowth hDgrowth
    hbase hg (‖G‖ * R) hgR hbound

end PDE.CalculusOfVariations

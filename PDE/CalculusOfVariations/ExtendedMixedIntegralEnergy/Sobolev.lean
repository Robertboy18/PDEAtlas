/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ConvexLowerSemicontinuity
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.ValueL1
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
import PDE.Analysis.Operator.CompactConvergence

/-!
# Weak Sobolev lower semicontinuity without upper growth

On a C¹ extension domain, Rellich compactness turns weak `W¹ᵖ` sequential
convergence into strong `L¹` convergence of the values, in every positive dimension.
Uniform boundedness supplies the Sobolev norm bound. The gradients converge weakly
through the continuous linear gradient map. The mixed integral theorem permits a
different exponent for the values, so `L¹` convergence suffices.

The density is convex in the gradient variable and continuous in the value for each gradient,
almost everywhere; it need not be differentiable. No upper growth
bound, integrability of the energy, or continuity of the induced functional is assumed.
Lowering the exponent preserves the original values almost everywhere, so the final
energy uses the original Sobolev representatives. The theorem assumes a bounded
open set with local C¹ graph boundary and builds the boundary atlas in the proof. The result
is a form of Evans, §8.2.2, Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal Topology

namespace PDE.CalculusOfVariations

/-- An extended mixed energy is sequentially lower semicontinuous under weak
`W¹ᵖ` convergence on a bounded open set with C¹ graph boundary in every positive
dimension, for every finite `p > 1`. Strong `L¹` convergence of the values and
norm boundedness both follow from weak convergence.

Subtracting the measurable lower bound gives a nonnegative Lebesgue integral, possibly
infinite. An integrable lower bound makes this a finite shift of the original energy.
No boundary values are prescribed in this convergence statement. -/
theorem lintegral_le_liminf_of_tendsto_weak_wkp_of_c1Domain
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ F x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ,
      ConvexOn ℝ univ (fun z : ℝ^n ↦ F x (s, z)))
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ × ℝ^n, b x ≤ F x z)
    {u : ℕ → W^{1,p}(Ω)}
    {uLimit : W^{1,p}(Ω)}
    (hu : Tendsto
      (fun j ↦ toWeakSpace ℝ (W^{1,p}(Ω)) (u j)) atTop
      (𝓝 (toWeakSpace ℝ (W^{1,p}(Ω)) uLimit))) :
    (∫⁻ x, ENNReal.ofReal (F x
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) uLimit x,
        ∇ uLimit x) - b x) ∂domainMeasure n Ω) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (F x
        (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) (u j) x,
          ∇ (u j) x) - b x) ∂domainMeasure n Ω) atTop := by
  obtain ⟨atlas, _, _⟩ :=
    (Boundary.hasContDiffGraphBoundary_one_iff.mpr hgraph).exists_c1ExtensionAtlas
      le_rfl hopen hbounded
  let := atlas
  let q := ENNReal.conjExponent (p : ℝ≥0∞)
  have : ENNReal.HolderConjugate (p : ℝ≥0∞) q := inferInstance
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q (p : ℝ≥0∞)⟩
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  have hq_top : q ≠ ∞ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q (p : ℝ≥0∞)).mpr hpE).ne
  let W := W^{1,p}(Ω)
  let B : W →L[ℝ] Lp ℝ 1 (domainMeasure n Ω) := RellichKondrachov.valueL1CLM
  let G : W →L[ℝ] Lp (ℝ^n) p (domainMeasure n Ω) := wkpGradientCLM
  have hbase : Tendsto (fun j ↦ B (u j)) atTop (𝓝 (B uLimit)) :=
    PDE.Analysis.tendsto_compactOperator_of_tendsto_weak B
      RellichKondrachov.valueL1CLM_isCompactOperator_of_c1Domain hu
  have hgradient : Tendsto
      (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) p (domainMeasure n Ω)) (G (u j))) atTop
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) p (domainMeasure n Ω)) (G uLimit))) :=
    (WeakSpace.map G).continuous.continuousAt.tendsto.comp hu
  have henergy (v : W) :
      (∫⁻ x, ENNReal.ofReal (F x (B v x, G v x) - b x) ∂domainMeasure n Ω) =
        ∫⁻ x, ENNReal.ofReal (F x
          (wkpBaseCoordinateCLM v x, G v x) - b x) ∂domainMeasure n Ω := by
    apply lintegral_congr_ae
    filter_upwards [RellichKondrachov.valueL1CLM_apply_ae v] with x hx
    rw [show B v x = wkpBaseCoordinateCLM v x from hx]
  -- strong convergence of the values gives almost-everywhere convergence along subsequences
  simpa only [henergy] using
    le_liminf_of_tendsto_Lp_of_forall_subseq_ae
      (J := fun j ↦ ∫⁻ x, ENNReal.ofReal (F x (B (u j) x, G (u j) x) - b x)
        ∂domainMeasure n Ω) hbase fun φ hφ hae ↦
      lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient hq_top
        hF hb hFcont hconvex hlower
        (fun j ↦ (Lp.stronglyMeasurable (B (u (φ j)))).measurable)
        (Lp.stronglyMeasurable (B uLimit)).measurable hae (hgradient.comp hφ)

end PDE.CalculusOfVariations

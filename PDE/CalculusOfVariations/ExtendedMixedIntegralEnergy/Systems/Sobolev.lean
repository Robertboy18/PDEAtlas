/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ConvexLowerSemicontinuity
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.VectorValues
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
import PDE.Analysis.WeakSequentialBoundedness

/-!
# Weak lower semicontinuity for coupled Sobolev systems

Strong L1 convergence of the Euclidean values and weak convergence of the
full Frobenius gradient feed the generic mixed integral theorem. Finite
product compactness and automatic weak boundedness supply both convergence
and norm bounds. The value and gradient dependence may couple all components.

The density is continuous in the value and convex in the gradient matrix; it need not be
differentiable. The lower semicontinuity step is
`lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient`, applied along
subsequences whose values converge almost everywhere.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Sobolev

namespace PDE.CalculusOfVariations

/-- A coupled extended energy, continuous in the value and convex in the full gradient matrix,
is weakly sequentially lower semicontinuous on the finite Sobolev product, on a bounded open
set with C¹ graph boundary. No derivative of the density, no upper growth bound and no finite
energy is assumed. -/
theorem lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_c1Domain
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(m * n),
      Continuous (fun s : ℝ^m ↦ F x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ F x (s, z)))
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n), b x ≤ F x z)
    {u : ℕ → Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
    {uLimit : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
    (hu : Tendsto
      (fun j ↦ toWeakSpace ℝ (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) (u j)) atTop
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) uLimit))) :
    (∫⁻ x, ENNReal.ofReal (F x
      (vectorWkpValueCLM (n := n) (m := m) (p := (p : ℝ≥0∞)) uLimit x,
        ∇ uLimit x) - b x) ∂domainMeasure n Ω) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (F x
        (vectorWkpValueCLM (n := n) (m := m) (p := (p : ℝ≥0∞)) (u j) x,
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
  let W := Fin m → W^{1,(p : ℝ≥0∞)}(Ω)
  let B : W →L[ℝ] Lp (ℝ^m) 1 (domainMeasure n Ω) := RellichKondrachov.vectorValueL1CLM
  let G : W →L[ℝ] Lp (ℝ^(m * n)) p (domainMeasure n Ω) := vectorWkpGradientCLM
  have hbase : Tendsto (fun j ↦ B (u j)) atTop (𝓝 (B uLimit)) :=
    RellichKondrachov.tendsto_vectorValueL1CLM_of_tendsto_weak hu
  have hgradient : Tendsto
      (fun j ↦ toWeakSpace ℝ (Lp (ℝ^(m * n)) p (domainMeasure n Ω)) (G (u j))) atTop
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^(m * n)) p (domainMeasure n Ω)) (G uLimit))) :=
    (WeakSpace.map G).continuous.continuousAt.tendsto.comp hu
  have henergy (v : W) :
      (∫⁻ x, ENNReal.ofReal (F x (B v x, G v x) - b x) ∂domainMeasure n Ω) =
        ∫⁻ x, ENNReal.ofReal (F x
          (vectorWkpValueCLM v x, G v x) - b x) ∂domainMeasure n Ω := by
    apply lintegral_congr_ae
    filter_upwards [RellichKondrachov.vectorValueL1CLM_apply_ae v] with x hx
    rw [show B v x = vectorWkpValueCLM v x from hx]
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

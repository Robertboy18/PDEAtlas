/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Sobolev
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ClassicalDensity
public import PDE.Analysis.MeasureTheory.Integral.LowerBounded

/-!
# Weak lower semicontinuity for a classical Lagrangian

This is the sequential lower semicontinuity theorem of Evans, §8.2.2,
Theorem 1. Write the Lagrangian as `L ((x, s), z)`, with spatial point `x`,
value `s`, and gradient `z`. Continuous differentiability on the open domain
suffices; the Lagrangian need not be regular outside it.

The Lagrangian is classically differentiable; `∇ u` is the weak gradient of
the Sobolev field, evaluated through its chosen `Lp` representative.

Convexity is required only in `z`. A constant lower bound makes `L - c`
nonnegative, so its Lebesgue integral retains infinite values. On the bounded
domain this shifts the usual energy by the finite constant `c |Ω|`. No upper
growth bound or boundary condition is assumed.

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

/-- A `C¹` Lagrangian bounded below and convex only in the gradient has a
sequentially weakly lower semicontinuous extended energy on `W¹ᵖ(Ω)`,
for every finite `p > 1` and every positive dimension. The domain is bounded,
open, and locally has C¹ graph boundary. All Sobolev functions are allowed.

The displayed nonnegative integral is the original energy minus the fixed
finite constant `c |Ω|`; it may equal infinity. The density is assumed `C¹`
only for spatial points in `Ω`. Its gradient derivative and the required norm bounds are derived
inside the proof. -/
theorem lintegral_le_liminf_of_tendsto_weak_wkp_of_contDiffOn
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {L : (ℝ^n × ℝ) × ℝ^n → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ, ConvexOn ℝ univ (fun z : ℝ^n ↦ L ((x, s), z)))
    {c : ℝ} (hlower : ∀ x ∈ Ω, ∀ (s : ℝ) (z : ℝ^n), c ≤ L ((x, s), z))
    {u : ℕ → W^{1,p}(Ω)}
    {uLimit : W^{1,p}(Ω)}
    (hu : Tendsto
      (fun j ↦ toWeakSpace ℝ (W^{1,p}(Ω)) (u j)) atTop
      (𝓝 (toWeakSpace ℝ (W^{1,p}(Ω)) uLimit))) :
    (∫⁻ x, ENNReal.ofReal (L
      ((x, wkpBaseCoordinateCLM uLimit x), ∇ uLimit x) - c)
      ∂domainMeasure n Ω) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (L
        ((x, wkpBaseCoordinateCLM (u j) x), ∇ (u j) x) - c)
        ∂domainMeasure n Ω) atTop := by
  obtain ⟨F, D, hFmeas, hDmeas, hFeq, hFcont, hDcont, hFD⟩ :=
    exists_measurable_gradient_representatives_of_contDiffOn hopen hL
  have hmem : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hopen.measurableSet
  have hvalue : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ F x (s, z)) := hmem.mono fun x hx ↦ hFcont x hx
  have hsupport : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ D x (s, z)) := hmem.mono fun x hx ↦ hDcont x hx
  have hconv : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ,
      ConvexOn ℝ univ (fun z : ℝ^n ↦ F x (s, z)) := by
    filter_upwards [hmem] with x hx
    simpa only [hFeq x hx] using hconvex x hx
  have hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      HasFDerivAt (fun y : ℝ^n ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z :=
    hmem.mono fun x hx ↦ hFD x hx
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : ℝ × ℝ^n, c ≤ F x v := by
    filter_upwards [hmem] with x hx
    rintro ⟨s, z⟩
    rw [hFeq x hx]
    exact hlower x hx s z
  have henergy (v : W^{1,p}(Ω)) :
      (∫⁻ x, ENNReal.ofReal
        (F x (wkpBaseCoordinateCLM v x, ∇ v x) - c) ∂domainMeasure n Ω) =
        ∫⁻ x, ENNReal.ofReal
          (L ((x, wkpBaseCoordinateCLM v x), ∇ v x) - c)
          ∂domainMeasure n Ω := by
    apply lintegral_congr_ae
    filter_upwards [hmem] with x hx
    rw [hFeq x hx]
  simpa only [henergy] using
    lintegral_le_liminf_of_tendsto_weak_wkp_of_c1Domain hopen hbounded hgraph hp
      hFmeas hDmeas measurable_const hvalue hsupport hconv hderiv hlow hu

/-- The original signed energy, defined by its positive and negative parts,
is weakly lower semicontinuous. A constant lower bound makes its negative
part finite; positive infinite energies are allowed on both sides. -/
theorem integral_le_liminf_of_tendsto_weak_wkp_of_contDiffOn
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {L : (ℝ^n × ℝ) × ℝ^n → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ, ConvexOn ℝ univ (fun z : ℝ^n ↦ L ((x, s), z)))
    {c : ℝ} (hlower : ∀ x ∈ Ω, ∀ (s : ℝ) (z : ℝ^n), c ≤ L ((x, s), z))
    {u : ℕ → W^{1,p}(Ω)}
    {uLimit : W^{1,p}(Ω)}
    (hu : Tendsto
      (fun j ↦ toWeakSpace ℝ (W^{1,p}(Ω)) (u j)) atTop
      (𝓝 (toWeakSpace ℝ (W^{1,p}(Ω)) uLimit))) :
    PDE.Analysis.lowerBoundedIntegral (domainMeasure n Ω)
      (fun x ↦ L ((x, wkpBaseCoordinateCLM uLimit x), ∇ uLimit x)) ≤
      liminf (fun j ↦ PDE.Analysis.lowerBoundedIntegral (domainMeasure n Ω)
        (fun x ↦ L ((x, wkpBaseCoordinateCLM (u j) x), ∇ (u j) x)))
        atTop := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hmem : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hopen.measurableSet
  have hmeas (v : W^{1,p}(Ω)) :
      AEStronglyMeasurable
        (fun x ↦ L ((x, wkpBaseCoordinateCLM v x), ∇ v x))
        (domainMeasure n Ω) :=
    aestronglyMeasurable_classicalDensity hopen.measurableSet hL.continuousOn
      (Lp.aestronglyMeasurable _).aemeasurable
      (Lp.aestronglyMeasurable _).aemeasurable hmem
  have hlow (v : W^{1,p}(Ω)) :
      ∀ᵐ x ∂domainMeasure n Ω,
        -(-c) ≤ L ((x, wkpBaseCoordinateCLM v x), ∇ v x) :=
    hmem.mono fun x hx ↦ by simpa only [neg_neg] using hlower x hx _ _
  apply PDE.Analysis.lowerBoundedIntegral_le_liminf (hmeas uLimit)
    (fun j ↦ hmeas (u j)) (integrable_const (-c)) (hlow uLimit) (fun j ↦ hlow (u j))
  simpa only [sub_eq_add_neg] using
    lintegral_le_liminf_of_tendsto_weak_wkp_of_contDiffOn
      hopen hbounded hgraph hp hL hconvex hlower hu

end PDE.CalculusOfVariations

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Polyconvexity.Determinant.Classical
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.DirectMethod

/-!
# Minimizers of determinant energies in affine Sobolev classes

The graph coercivity bound controls the Euclidean coordinates of the full
gradient. Together with determinant lower semicontinuity this supplies the two
inputs to the common affine direct method. The exponent is any finite real
`q > n`; neither an integer exponent nor a finite-energy boundary lift is needed.

This is the affine-class step in Evans, §8.2.4(b), Theorem 9. All matrix norms
below are explicitly the Frobenius norm through `Matrix.euclideanEquiv`,
independently of the ambient matrix norm.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Theorem 9.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Matrix.Norms.Elementwise Sobolev

namespace PDE.CalculusOfVariations

/-- Graph coercivity and independent matrix–determinant convexity give a
minimizer of the shifted determinant energy in every affine zero-trace class.
The bound need not hold away from the determinant graph. -/
theorem exists_minimizer_determinantWkpLIntegral_prescribed_boundary
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : (n : ℝ) < q)
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun R : Matrix (Fin n) (Fin n) ℝ × ℝ ↦ F ((x, s), R)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ),
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ F ((x, s), (P, P.det)))
    (g : Fin n → W^{1,ENNReal.ofReal q}(Ω)) :
    ∃ u : Fin n → W^{1,ENNReal.ofReal q}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω)) ∧
      ∀ v : Fin n → W^{1,ENNReal.ofReal q}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn
          (n := n) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω)) →
        vectorWkpLIntegral (determinantDensity F) (fun _ ↦ β) u ≤
          vectorWkpLIntegral (determinantDensity F) (fun _ ↦ β) v := by
  have hn : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (show 0 < n from Fact.out))
  have hq1 : 1 < q := hn.trans_lt hq
  have hq0 : 0 ≤ q := zero_le_one.trans hq1.le
  have hp : 1 < q.toNNReal := by
    exact_mod_cast (show (1 : ℝ) < (q.toNNReal : ℝ) by
      simpa only [Real.coe_toNNReal q hq0] using hq1)
  let : Fact (1 ≤ (q.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp.le⟩
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^n) (z : ℝ^(n * n)),
      α * ‖z‖ ^ (q.toNNReal : ℝ) - β ≤ determinantDensity F x (s, z) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    intro s z
    simpa only [determinantDensity, ContinuousLinearEquiv.apply_symm_apply,
      Real.coe_toNNReal q hq0] using
      hcoercive x hx s (Matrix.euclideanEquiv.symm z)
  have hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ F ((x, s), (P, P.det)) := by
    intro x hx s P
    have h := hcoercive x hx s P
    have hnonneg := mul_nonneg hα.le
      (Real.rpow_nonneg (norm_nonneg (Matrix.euclideanEquiv P)) q)
    linarith
  have hclosed : IsSeqClosed (toWeakSpace ℝ
      (Fin n → W^{1,(q.toNNReal : ℝ≥0∞)}(Ω)) '' univ) := by
    rw [image_univ_of_surjective (toWeakSpace ℝ _).surjective]
    exact isClosed_univ.isSeqClosed
  obtain ⟨u, _, hu, hmin⟩ :=
    exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_weak_lsc
      hbounded hp hα hlow
      (fun hu ↦ vectorWkpLIntegral_le_liminf_of_contDiffOn_convex_determinant
        hopen hbounded hgraph hq hF hconvex hlower hu) hclosed g (mem_univ _)
  exact ⟨u, hu, fun v hv ↦ hmin v (mem_univ _) hv⟩

/-- The original signed determinant energy attains its minimum in every affine
zero-trace class. The shift `β` may have either sign, and the minimum may be
positive infinity. All competitors in the class are included. -/
theorem exists_minimizer_determinantWkpIntegral_prescribed_boundary
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : (n : ℝ) < q)
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun R : Matrix (Fin n) (Fin n) ℝ × ℝ ↦ F ((x, s), R)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ),
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ F ((x, s), (P, P.det)))
    (g : Fin n → W^{1,ENNReal.ofReal q}(Ω)) :
    ∃ u : Fin n → W^{1,ENNReal.ofReal q}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω)) ∧
      ∀ v : Fin n → W^{1,ENNReal.ofReal q}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn
          (n := n) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω)) →
        vectorWkpIntegral (determinantDensity F) u ≤
          vectorWkpIntegral (determinantDensity F) v := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ F ((x, s), (P, P.det)) := by
    intro x hx s P
    have h := hcoercive x hx s P
    have hnonneg := mul_nonneg hα.le
      (Real.rpow_nonneg (norm_nonneg (Matrix.euclideanEquiv P)) q)
    linarith
  obtain ⟨u, hu, hmin⟩ :=
    exists_minimizer_determinantWkpLIntegral_prescribed_boundary
      hopen hbounded hgraph hq hF hconvex hα hcoercive g
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  rw [vectorWkpIntegral_determinantDensity_eq_lIntegral_sub
    hopen.measurableSet hF.continuousOn hlower u,
    vectorWkpIntegral_determinantDensity_eq_lIntegral_sub
      hopen.measurableSet hF.continuousOn hlower v]
  exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmin v hv)) le_rfl

end PDE.CalculusOfVariations

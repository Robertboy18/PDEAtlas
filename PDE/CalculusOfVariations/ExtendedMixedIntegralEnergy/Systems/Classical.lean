/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Dirichlet
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ClassicalDensity

/-!
# Classical coupled matrix energies

A C1 density convex in the full gradient matrix and coercive in its Frobenius
norm attains a minimum in each affine zero-boundary Sobolev class. The matrix
variable is transported isometrically to Euclidean coordinates for the Hilbert
supporting-field argument. All value and gradient entries may remain coupled. This is the
affine-class form of Evans, §8.2.4(a), Theorem 5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(a), Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Matrix.Norms.Frobenius Sobolev

namespace PDE.CalculusOfVariations

/-- Evaluation of a continuous matrix density on the Sobolev value
and full matrix gradient is a.e. strongly measurable. -/
theorem aestronglyMeasurable_matrixWkpDensity
    {m n : ℕ} {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {L : (ℝ^n × ℝ^m) × Matrix (Fin m) (Fin n) ℝ → ℝ}
    (hL : ContinuousOn L ((Ω ×ˢ univ) ×ˢ univ))
    (u : Fin m → W^{1,p}(Ω)) :
    AEStronglyMeasurable (fun x ↦ L ((x, vectorWkpValueCLM u x),
      Matrix.euclideanEquiv.symm (∇ u x))) (domainMeasure n Ω) := by
  have hL' : ContinuousOn
      (fun t : (ℝ^n × ℝ^m) × ℝ^(m * n) ↦ L (t.1, Matrix.euclideanEquiv.symm t.2))
      ((Ω ×ˢ univ) ×ˢ univ) :=
    hL.comp (continuous_fst.prodMk
      (Matrix.euclideanEquiv.symm.continuous.comp continuous_snd)).continuousOn
      (fun _ ht ↦ ⟨ht.1, mem_univ _⟩)
  exact aestronglyMeasurable_classicalDensity hΩ hL'
    (Lp.aestronglyMeasurable _).aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
    (ae_restrict_mem hΩ)

/-- For every Sobolev system, the original signed matrix energy is exactly
the shifted nonnegative energy minus `β |Ω|`. The shift remains valid at
infinite energy and requires only a lower bound and finite domain volume. -/
theorem vectorWkpIntegral_eq_lIntegral_sub_of_continuousOn
    {m n : ℕ} {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {L : (ℝ^n × ℝ^m) × Matrix (Fin m) (Fin n) ℝ → ℝ}
    (hL : ContinuousOn L ((Ω ×ˢ univ) ×ˢ univ))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ L ((x, s), P))
    (u : Fin m → W^{1,p}(Ω)) :
    vectorWkpIntegral (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) u =
      (vectorWkpLIntegral (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2))
        (fun _ ↦ β) u : EReal) -
        ((β * (domainMeasure n Ω).real univ : ℝ) : EReal) := by
  apply PDE.Analysis.lowerBoundedIntegral_eq_lintegral_add_const_sub
    (aestronglyMeasurable_matrixWkpDensity hΩ hL u)
  filter_upwards [ae_restrict_mem hΩ] with x hx
  exact hlower x hx _ _

/-- A C¹ density convex in the full Euclidean gradient has a weakly lower
semicontinuous shifted Sobolev energy. Only a constant lower bound is needed;
coercivity is reserved for the subsequent minimization argument. -/
theorem vectorWkpLIntegral_le_liminf_of_contDiffOn_convex
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {L : (ℝ^n × ℝ^m) × ℝ^(m * n) → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ L ((x, s), z)))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s z, -β ≤ L ((x, s), z))
    {u : ℕ → Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
    {U : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
    (hu : Tendsto (fun j ↦ toWeakSpace ℝ _ (u j)) atTop (𝓝 (toWeakSpace ℝ _ U))) :
    vectorWkpLIntegral (fun x z ↦ L ((x, z.1), z.2)) (fun _ ↦ β) U ≤
      liminf (fun j ↦ vectorWkpLIntegral (fun x z ↦ L ((x, z.1), z.2))
        (fun _ ↦ β) (u j)) atTop := by
  obtain ⟨F, D, hF, hD, hFeq, hFcont, hDcont, hFD⟩ :=
    exists_measurable_gradient_representatives_of_contDiffOn hopen hL
  have hmem : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hopen.measurableSet
  have hconv : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ F x (s, z)) := by
    filter_upwards [hmem] with x hx
    simpa only [hFeq x hx] using hconvex x hx
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n), -β ≤ F x z := by
    filter_upwards [hmem] with x hx
    intro z
    rw [hFeq x hx]
    exact hlower x hx z.1 z.2
  have henergy (v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
      vectorWkpLIntegral F (fun _ ↦ β) v =
        vectorWkpLIntegral (fun x z ↦ L ((x, z.1), z.2)) (fun _ ↦ β) v := by
    apply lintegral_congr_ae
    filter_upwards [hmem] with x hx
    rw [hFeq x hx]
  have h : vectorWkpLIntegral F (fun _ ↦ β) U ≤
      liminf (fun j ↦ vectorWkpLIntegral F (fun _ ↦ β) (u j)) atTop := by
    simpa only [vectorWkpLIntegral, sub_neg_eq_add] using
      lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_c1Domain
        hopen hbounded hgraph hp hF hD (measurable_const (a := -β))
        (hmem.mono fun x hx ↦ hFcont x hx) (hmem.mono fun x hx ↦ hDcont x hx)
        hconv (hmem.mono fun x hx ↦ hFD x hx) hlow hu
  simpa only [henergy] using h

/-- A classical, fully coupled matrix density has an extended-energy minimizer
in every prescribed affine Sobolev class. The dimension of the target is any
natural number, including zero. The domain is bounded, open, and has C1 graph
boundary. No upper growth or finite-energy competitor is assumed. -/
theorem exists_minimizer_matrixWkpLIntegral_prescribed_boundary
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {L : (ℝ^n × ℝ^m) × Matrix (Fin m) (Fin n) ℝ → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun P : Matrix (Fin m) (Fin n) ℝ ↦ L ((x, s), P)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^m) (P : Matrix (Fin m) (Fin n) ℝ),
      α * ‖P‖ ^ (p : ℝ) - β ≤ L ((x, s), P))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) ∧
      ∀ v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
        vectorWkpLIntegral (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2))
          (fun _ ↦ β) u ≤
        vectorWkpLIntegral (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2))
          (fun _ ↦ β) v := by
  have hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ L ((x, s), P) := by
    intro x hx s P
    have h := hcoercive x hx s P
    have hnonneg := mul_nonneg hα.le (Real.rpow_nonneg (norm_nonneg P) (p : ℝ))
    linarith
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      α * ‖z‖ ^ (p : ℝ) - β ≤ L ((x, s), Matrix.euclideanEquiv.symm z) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    intro s z
    have hn : ‖Matrix.euclideanEquiv.symm z‖ = ‖z‖ := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (Matrix.norm_euclideanEquiv (Matrix.euclideanEquiv.symm z)).symm
    simpa only [hn] using hcoercive x hx s (Matrix.euclideanEquiv.symm z)
  have hclosed : IsSeqClosed (toWeakSpace ℝ
      (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) '' univ) := by
    rw [image_univ_of_surjective (toWeakSpace ℝ _).surjective]
    exact isClosed_univ.isSeqClosed
  have hL' : ContDiffOn ℝ 1
      (fun t : (ℝ^n × ℝ^m) × ℝ^(m * n) ↦ L (t.1, Matrix.euclideanEquiv.symm t.2))
      ((Ω ×ˢ univ) ×ˢ univ) :=
    hL.comp (contDiff_fst.prodMk
      (Matrix.euclideanEquiv.symm.contDiff.comp contDiff_snd)).contDiffOn
      (fun _ ht ↦ ⟨ht.1, mem_univ _⟩)
  have hconv' : ∀ x ∈ Ω, ∀ s : ℝ^m, ConvexOn ℝ univ
      (fun z : ℝ^(m * n) ↦ L ((x, s), Matrix.euclideanEquiv.symm z)) := by
    intro x hx s
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ t r ht hr htr
    change L ((x, s), Matrix.euclideanEquiv.symm (t • a + r • b)) ≤
      t • L ((x, s), Matrix.euclideanEquiv.symm a) +
        r • L ((x, s), Matrix.euclideanEquiv.symm b)
    rw [map_add, map_smul, map_smul]
    exact (hconvex x hx s).2 (mem_univ _) (mem_univ _) ht hr htr
  obtain ⟨u, _, hu, hmin⟩ :=
    exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_weak_lsc
      hbounded hp hα hlow
      (fun h ↦ vectorWkpLIntegral_le_liminf_of_contDiffOn_convex
        hopen hbounded hgraph hp hL' hconv'
        (fun x hx s z ↦ hlower x hx s (Matrix.euclideanEquiv.symm z)) h) hclosed g (mem_univ _)
  exact ⟨u, hu, fun v hv ↦ hmin v (mem_univ _) hv⟩

end PDE.CalculusOfVariations

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Polyconvexity.Determinant.Density
public import PDE.CalculusOfVariations.Polyconvexity.Determinant.LowerSemicontinuity

/-!
# Weak lower semicontinuity of classical determinant energies

A density `F(P,r,z,x)` convex jointly in `(P,r)` is evaluated at `r = det P`.
It need only be C¹ on the full open spatial cylinder, and bounded below on the
determinant graph. For a weakly convergent W¹ᑫ sequence, `q > n`, the
original signed extended energy is lower semicontinuous.

The proof constructs the measurable supporting field from the classical
density. Strong L¹ convergence of the values, weak convergence of the joint
gradient–determinant lift, and the resulting bounds supply the analytic
hypotheses. No upper growth bound or finite energy is assumed.

This is the determinant-dependent case of Evans, §8.2.4(b), Theorem 8, where
the polyconvex density has the form (51) with the convexity (52), on a domain
with C¹ graph boundary that need not be connected.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Theorem 8.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Matrix.Norms.Elementwise Sobolev

namespace PDE.CalculusOfVariations

/-- The nonnegative shift of the determinant energy is weakly
sequentially lower semicontinuous for finite real `q > n`. The signed shift
is arbitrary, and its lower bound is required only on the determinant graph. -/
theorem vectorWkpLIntegral_le_liminf_of_contDiffOn_convex_determinant
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : (n : ℝ) < q)
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun R : Matrix (Fin n) (Fin n) ℝ × ℝ ↦ F ((x, s), R)))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ F ((x, s), (P, P.det)))
    {u : ℕ → Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin n → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) U))) :
    vectorWkpLIntegral (determinantDensity F) (fun _ ↦ β) U ≤
      liminf (fun k ↦ vectorWkpLIntegral (determinantDensity F) (fun _ ↦ β) (u k))
        atTop := by
  have hn : 0 < n := Fact.out
  let : Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) :=
    ⟨(ENNReal.one_lt_ofReal_div_nat hn hq).le⟩
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let e := Matrix.euclideanScalarEquiv (m := n) (n := n)
  let L : (ℝ^n × ℝ^n) × ℝ^(n * n + 1) → ℝ := fun t ↦ F (t.1, e.symm t.2)
  have hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ) :=
    hF.comp (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)).contDiffOn
      (fun _ ht ↦ ⟨ht.1, mem_univ _⟩)
  obtain ⟨G, D, hG, hD, hGeq, hGcont, hDcont, hGD⟩ :=
    exists_measurable_gradient_representatives_of_contDiffOn hopen hL
  have hmem : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hopen.measurableSet
  have hconv : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun z : ℝ^(n * n + 1) ↦ G x (s, z)) := by
    filter_upwards [hmem] with x hx
    intro s
    simp_rw [hGeq x hx]
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ t r ht hr htr
    change F ((x, s), e.symm (t • a + r • b)) ≤
      t • F ((x, s), e.symm a) + r • F ((x, s), e.symm b)
    rw [map_add, map_smul, map_smul]
    exact (hconvex x hx s).2 (mem_univ _) (mem_univ _) ht hr htr
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ),
      -β ≤ G x (s, Matrix.euclideanScalarEquiv (P, P.det)) := by
    filter_upwards [hmem] with x hx
    intro s P
    rw [hGeq x hx]
    simpa only [L, e, ContinuousLinearEquiv.symm_apply_apply] using hlower x hx s P
  let W := Fin n → W^{1,ENNReal.ofReal q}(Ω)
  have henergy (v : W) :
      (∫⁻ x, ENNReal.ofReal (G x (vectorWkpValueCLM v x,
        Matrix.euclideanScalarEquiv
          (Matrix.euclideanEquiv.symm (∇ v x),
            (Matrix.euclideanEquiv.symm (∇ v x)).det)) - (-β))
        ∂domainMeasure n Ω) =
      vectorWkpLIntegral (determinantDensity F) (fun _ ↦ β) v := by
    apply lintegral_congr_ae
    filter_upwards [hmem] with x hx
    rw [hGeq x hx]
    simp only [L, e, ContinuousLinearEquiv.symm_apply_apply, sub_neg_eq_add,
      determinantDensity]
  simp_rw [← henergy]
  convert lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_convex_determinant
      (Ω := ⟨Ω, hopen⟩) hbounded hgraph hq hG hD (measurable_const (a := -β))
      (hmem.mono fun x hx ↦ hGcont x hx) (hmem.mono fun x hx ↦ hDcont x hx)
      hconv (hmem.mono fun x hx ↦ hGD x hx) hlow hu using 1

/-- The signed determinant energy is weakly sequentially lower
semicontinuous for every positive dimension and finite real `q > n`.
The lower bound is required only at `(P, det P)`, and the energy may be `+∞`. -/
theorem vectorWkpIntegral_le_liminf_of_contDiffOn_convex_determinant
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : (n : ℝ) < q)
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun R : Matrix (Fin n) (Fin n) ℝ × ℝ ↦ F ((x, s), R)))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ F ((x, s), (P, P.det)))
    {u : ℕ → Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin n → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) U))) :
    vectorWkpIntegral (determinantDensity F) U ≤
      liminf (fun k ↦ vectorWkpIntegral (determinantDensity F) (u k)) atTop := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hmem : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hopen.measurableSet
  have hbound (v : Fin n → W^{1,ENNReal.ofReal q}(Ω)) :
      ∀ᵐ x ∂domainMeasure n Ω, -β ≤
      determinantDensity F x (vectorWkpValueCLM v x, ∇ v x) :=
    hmem.mono fun x hx ↦ hlower x hx _ _
  exact PDE.Analysis.lowerBoundedIntegral_le_liminf
    (aestronglyMeasurable_determinantDensity hopen.measurableSet hF.continuousOn U)
    (fun k ↦ aestronglyMeasurable_determinantDensity
      hopen.measurableSet hF.continuousOn (u k))
    (integrable_const β) (hbound U) (fun k ↦ hbound (u k))
    (vectorWkpLIntegral_le_liminf_of_contDiffOn_convex_determinant
      hopen hbounded hgraph hq hF hconvex hlower hu)

end PDE.CalculusOfVariations

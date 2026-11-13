/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.ConvexIntegral
public import PDE.Analysis.Calculus.StrongConvex
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ClassicalDensity
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace
public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent

/-!
# Uniqueness of finite-energy scalar minimizers

The original signed integral uses the scalar value, weak gradient,
and geometric trace. Joint convexity, strict for different gradients, gives
uniqueness in a prescribed trace class. One minimizer must have finite energy;
when every admissible energy is infinite, every admissible function minimizes.

This is the finite-energy midpoint argument of Evans, §8.2.2, Theorem 3, for jointly convex
value-dependent densities. Evans's own case, a value-independent density with a uniform
convexity bound, is `eq_of_isMinOn_wkpIntegral_of_hessian_lower_bound`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal

namespace PDE.CalculusOfVariations

/-- Two finite-energy scalar minimizers with the same geometric trace
coincide under joint convexity that is strict for different gradients. Values
may enter the density, and the finite exponent need only be at least one. -/
theorem eq_of_isMinOn_wkpIntegral
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 ≤ q)
    {L : (ℝ^(d + 1) × ℝ) × ℝ^(d + 1) → ℝ}
    (hL : ContinuousOn L ((Ω ×ˢ univ) ×ˢ univ))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ L ((x, s), P))
    (hconvex : ∀ x ∈ Ω, ConvexOn ℝ univ
      (fun z : ℝ × ℝ^(d + 1) ↦ L ((x, z.1), z.2)))
    (hstrict : ∀ x ∈ Ω, ∀ z w : ℝ × ℝ^(d + 1), z.2 ≠ w.2 →
      L ((x, (2 : ℝ)⁻¹ * z.1 + (2 : ℝ)⁻¹ * w.1),
        (2 : ℝ)⁻¹ • z.2 + (2 : ℝ)⁻¹ • w.2) <
      (L ((x, z.1), z.2) + L ((x, w.1), w.2)) / 2) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp ℝ (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      let A := {u : W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.traceLp q u = γ}
      let I := fun u : W^{1,ENNReal.ofReal q}(Ω) ↦
        PDE.Analysis.lowerBoundedIntegral (domainMeasure (d + 1) Ω)
          (fun x ↦ L ((x, wkpBaseCoordinateCLM u x), ∇ u x))
      ∀ u v, u ∈ A → v ∈ A → IsMinOn I A u → IsMinOn I A v → I u ≠ ⊤ → u = v := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  intro γ A I u v hu hv hminu hminv hfinite
  have hA : Convex ℝ A :=
    (convex_singleton γ).linear_preimage (Trace.C1.traceLp q).toLinearMap
  have hg : ∇ u = ∇ v := by
    apply PDE.Analysis.lp_eq_of_isMinOn_lowerBoundedIntegral
      (μ := domainMeasure (d + 1) Ω) (p := ENNReal.ofReal q)
      (wkpBaseCoordinateCLM (n := d + 1) (m := 1)
        (p := ENNReal.ofReal q) (Ω := Ω)).toLinearMap
      (wkpGradientCLM (n := d + 1) (p := ENNReal.ofReal q) (Ω := Ω)).toLinearMap
      (L := fun x z ↦ L ((x, z.1), z.2)) (b := fun _ ↦ β) hA _ (integrable_const β)
      _ _ _ hu hv hminu hminv hfinite
    · intro w _
      exact aestronglyMeasurable_classicalDensity hopen.measurableSet hL
        (Lp.aestronglyMeasurable _).aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
        (ae_restrict_mem hopen.measurableSet)
    · intro w _
      filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
      exact hlower x hx _ _
    · exact (ae_restrict_mem hopen.measurableSet).mono fun x hx ↦ hconvex x hx
    · filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
      intro z w hne
      exact hstrict x hx z w hne
  have hp : 1 ≤ q.toNNReal := by
    exact_mod_cast (show (1 : ℝ) ≤ (q.toNNReal : ℝ) by
      simpa only [Real.coe_toNNReal q (le_trans zero_le_one hq)] using hq)
  have : Fact (1 ≤ (q.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  apply eq_of_sub_mem_Wkp0_of_wkpGradientCLM_eq (Nat.succ_pos d) hbounded hp _ hg
  apply (Trace.C1.traceLp_eq_zero_iff_mem_Wkp0 q (u - v)).mp
  rw [map_sub, show Trace.C1.traceLp q u = γ from hu,
    show Trace.C1.traceLp q v = γ from hv, sub_self]

/-- Finite-energy form of Evans §8.2.2, Theorem 3. The original scalar energy
has at most one minimizer when a value-independent C2 density has a uniform
positive gradient Hessian bound. -/
theorem eq_of_isMinOn_wkpIntegral_of_hessian_lower_bound
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 ≤ q)
    {F : ℝ^(d + 1) × ℝ^(d + 1) → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ω ×ˢ univ))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ P, -β ≤ F (x, P))
    {θ : ℝ} (hθ : 0 < θ)
    (hHessian : ∀ x ∈ Ω, ∀ P Q : ℝ^(d + 1),
      θ * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun R ↦ F (x, R))) P Q Q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp ℝ (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      let A := {u : W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.traceLp q u = γ}
      let I := fun u : W^{1,ENNReal.ofReal q}(Ω) ↦
        PDE.Analysis.lowerBoundedIntegral (domainMeasure (d + 1) Ω)
          (fun x ↦ F (x, ∇ u x))
      ∀ u v, u ∈ A → v ∈ A → IsMinOn I A u → IsMinOn I A v → I u ≠ ⊤ → u = v := by
  have hs (x : ℝ^(d + 1)) (hx : x ∈ Ω) :
      StrictConvexOn ℝ univ (fun P : ℝ^(d + 1) ↦ F (x, P)) :=
    (PDE.Analysis.strongConvexOn_slice_of_hessian_lower_bound hF hx
      (hHessian x hx)).strictConvexOn hθ
  apply eq_of_isMinOn_wkpIntegral hopen hbounded hgraph hq
    (L := fun t ↦ F (t.1.1, t.2))
    (hF.continuousOn.comp (continuous_fst.fst.prodMk continuous_snd).continuousOn
      (fun _ ht ↦ ⟨ht.1.1, mem_univ _⟩))
    (fun x hx _ P ↦ hlower x hx P)
  · intro x hx
    refine ⟨convex_univ, fun z _ w _ a b ha hb hab ↦ ?_⟩
    exact (hs x hx).convexOn.2 (mem_univ z.2) (mem_univ w.2) ha hb hab
  · intro x hx z w hne
    simpa only [smul_eq_mul, div_eq_mul_inv, add_mul, mul_comm (2 : ℝ)⁻¹] using
      (hs x hx).2 (mem_univ z.2) (mem_univ w.2) hne
        (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num)

end PDE.CalculusOfVariations

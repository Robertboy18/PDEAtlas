/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.ConvexIntegral
public import PDE.Analysis.Calculus.StrongConvex
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Existence

/-!
# Uniqueness of finite-energy minimizers for coupled systems

Joint convexity in the value and full gradient matrix, strict at midpoints
with different matrices, determines a minimizer in its geometric trace class.
The energy is the original signed integral. Only one minimizing energy must
be finite; neither quadratic gradient integrability nor upper growth is used.

This is the midpoint argument of Evans, §8.2.4(a), Theorem 6, which assumes a density
independent of the value and uniformly convex in the gradient matrix; that case is
`eq_of_isMinOn_matrixWkpIntegral_of_hessian_lower_bound`. When every admissible energy is
infinite, every admissible map is a minimizer.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(a), Theorem 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Matrix.Norms.Frobenius Sobolev

namespace PDE.CalculusOfVariations

/-- Finite minimizers of a jointly convex matrix density in a prescribed
geometric trace class coincide if convexity is strict whenever the matrices
differ. Values may enter and couple with the matrix. The domain need not be
connected or nonempty, and the target may have dimension zero. -/
theorem eq_of_isMinOn_matrixWkpIntegral
    {m d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 ≤ q)
    {L : (ℝ^(d + 1) × ℝ^m) × Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ}
    (hL : ContinuousOn L ((Ω ×ˢ univ) ×ˢ univ))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ L ((x, s), P))
    (hconvex : ∀ x ∈ Ω, ConvexOn ℝ univ
      (fun z : ℝ^m × Matrix (Fin m) (Fin (d + 1)) ℝ ↦ L ((x, z.1), z.2)))
    (hstrict : ∀ x ∈ Ω, ∀ z w : ℝ^m × Matrix (Fin m) (Fin (d + 1)) ℝ,
      z.2 ≠ w.2 →
        L ((x, (2 : ℝ)⁻¹ • z.1 + (2 : ℝ)⁻¹ • w.1),
          (2 : ℝ)⁻¹ • z.2 + (2 : ℝ)⁻¹ • w.2) <
        (L ((x, z.1), z.2) + L ((x, w.1), w.2)) / 2) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp (ℝ^m) (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      let A := {u : Fin m → W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.vectorTraceLp q u = γ}
      let I := vectorWkpIntegral
        (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2))
      ∀ u v, u ∈ A → v ∈ A → IsMinOn I A u → IsMinOn I A v → I u ≠ ⊤ → u = v := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  intro γ A I u v hu hv hminu hminv hfinite
  have hA : Convex ℝ A :=
    (convex_singleton γ).linear_preimage (Trace.C1.vectorTraceLp q).toLinearMap
  have hg : ∇ u = ∇ v := by
    apply PDE.Analysis.lp_eq_of_isMinOn_lowerBoundedIntegral
      (μ := domainMeasure (d + 1) Ω) (p := ENNReal.ofReal q)
      (vectorWkpValueCLM (m := m) (n := d + 1)
        (p := ENNReal.ofReal q) (Ω := Ω)).toLinearMap
      (vectorWkpGradientCLM (m := m) (n := d + 1)
        (p := ENNReal.ofReal q) (Ω := Ω)).toLinearMap
      (L := fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) (b := fun _ ↦ β) hA
      (fun w _ ↦ aestronglyMeasurable_matrixWkpDensity
        (m := m) (n := d + 1) (p := ENNReal.ofReal q) (Ω := Ω) (L := L)
        hopen.measurableSet hL w)
      (integrable_const β) _ _ _ hu hv hminu hminv hfinite
    · intro w _
      filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
      exact hlower x hx _ _
    · filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
      refine ⟨convex_univ, ?_⟩
      intro z _ w _ a b ha hb hab
      change L ((x, a • z.1 + b • w.1),
        Matrix.euclideanEquiv.symm (a • z.2 + b • w.2)) ≤ _
      rw [map_add, map_smul, map_smul]
      exact (hconvex x hx).2 (mem_univ (z.1, Matrix.euclideanEquiv.symm z.2))
        (mem_univ (w.1, Matrix.euclideanEquiv.symm w.2)) ha hb hab
    · filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
      intro z w hne
      have hn : Matrix.euclideanEquiv.symm z.2 ≠ Matrix.euclideanEquiv.symm w.2 :=
        Matrix.euclideanEquiv.symm.injective.ne hne
      change L ((x, (2 : ℝ)⁻¹ • z.1 + (2 : ℝ)⁻¹ • w.1),
        Matrix.euclideanEquiv.symm ((2 : ℝ)⁻¹ • z.2 + (2 : ℝ)⁻¹ • w.2)) < _
      rw [map_add, map_smul, map_smul]
      exact hstrict x hx (z.1, Matrix.euclideanEquiv.symm z.2)
        (w.1, Matrix.euclideanEquiv.symm w.2) hn
  have hp : 1 ≤ q.toNNReal := by
    exact_mod_cast (show (1 : ℝ) ≤ (q.toNNReal : ℝ) by
      simpa only [Real.coe_toNNReal q (le_trans zero_le_one hq)] using hq)
  have : Fact (1 ≤ (q.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  exact eq_of_sub_mem_Wkp0_of_vectorWkpGradientCLM_eq (Nat.succ_pos d) hbounded hp
    ((Trace.C1.vectorTraceLp_eq_iff_sub_mem_Wkp0 q u v).mp (hu.trans hv.symm)) hg

/-- A finite-energy competitor upgrades existence for a coercive coupled
matrix density to existence of exactly one minimizer. Only that competitor
must have finite energy; other admissible energies may be infinite. -/
theorem existsUnique_minimizer_matrixWkpIntegral_of_finite_competitor
    {m d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 < q)
    {L : (ℝ^(d + 1) × ℝ^m) × Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ConvexOn ℝ univ
      (fun z : ℝ^m × Matrix (Fin m) (Fin (d + 1)) ℝ ↦ L ((x, z.1), z.2)))
    (hstrict : ∀ x ∈ Ω, ∀ z w : ℝ^m × Matrix (Fin m) (Fin (d + 1)) ℝ,
      z.2 ≠ w.2 →
        L ((x, (2 : ℝ)⁻¹ • z.1 + (2 : ℝ)⁻¹ • w.1),
          (2 : ℝ)⁻¹ • z.2 + (2 : ℝ)⁻¹ • w.2) <
        (L ((x, z.1), z.2) + L ((x, w.1), w.2)) / 2)
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^m) (P : Matrix (Fin m) (Fin (d + 1)) ℝ),
      α * ‖P‖ ^ q - β ≤ L ((x, s), P)) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp (ℝ^m) (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      let A := {u : Fin m → W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.vectorTraceLp q u = γ}
      let I := vectorWkpIntegral
        (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2))
      (∃ w ∈ A, I w ≠ ⊤) →
        ∃! u : Fin m → W^{1,ENNReal.ofReal q}(Ω),
          u ∈ A ∧ IsMinOn I A u := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  intro γ A I ⟨w, hw, hfinite⟩
  have hslice : ∀ x ∈ Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun P : Matrix (Fin m) (Fin (d + 1)) ℝ ↦ L ((x, s), P)) := by
    intro x hx s
    refine ⟨convex_univ, fun P _ Q _ a b ha hb hab ↦ ?_⟩
    simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] using
      (hconvex x hx).2 (mem_univ (s, P)) (mem_univ (s, Q)) ha hb hab
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_matrixWkpIntegral_of_nonempty_trace
    hopen hbounded hgraph hq hL hslice hα hcoercive γ ⟨w, hw⟩
  have hu_finite : I u ≠ ⊤ := ne_top_of_le_ne_top hfinite (hmin w hw)
  have hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ L ((x, s), P) := by
    intro x hx s P
    have hc := hcoercive x hx s P
    have hn := mul_nonneg hα.le (Real.rpow_nonneg (norm_nonneg P) q)
    linarith
  refine ⟨u, ⟨hu, hmin⟩, fun v hv ↦ ?_⟩
  exact (eq_of_isMinOn_matrixWkpIntegral hopen hbounded hgraph hq.le hL.continuousOn
    hlower hconvex hstrict γ u v hu hv.1 hmin hv.2 hu_finite).symm

/-- Finite-energy form of Evans §8.2.4(a), Theorem 6: a value-independent C2
density with a positive Hessian bound on every full matrix direction has at
most one minimizer in each geometric trace class. The matrix norm is
Frobenius. Coercive densities satisfy the common lower bound used here. -/
theorem eq_of_isMinOn_matrixWkpIntegral_of_hessian_lower_bound
    {m d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 ≤ q)
    {F : ℝ^(d + 1) × Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ω ×ˢ univ))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ P, -β ≤ F (x, P))
    {θ : ℝ} (hθ : 0 < θ)
    (hHessian : ∀ x ∈ Ω, ∀ P Q : Matrix (Fin m) (Fin (d + 1)) ℝ,
      θ * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun R ↦ F (x, R))) P Q Q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp (ℝ^m) (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      let A := {u : Fin m → W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.vectorTraceLp q u = γ}
      let I := vectorWkpIntegral (fun x z ↦ F (x, Matrix.euclideanEquiv.symm z.2))
      ∀ u v, u ∈ A → v ∈ A → IsMinOn I A u → IsMinOn I A v → I u ≠ ⊤ → u = v := by
  have hs (x : ℝ^(d + 1)) (hx : x ∈ Ω) :
      StrictConvexOn ℝ univ (fun P : Matrix (Fin m) (Fin (d + 1)) ℝ ↦ F (x, P)) :=
    (PDE.Analysis.strongConvexOn_slice_of_hessian_lower_bound hF hx
      (hHessian x hx)).strictConvexOn hθ
  apply eq_of_isMinOn_matrixWkpIntegral hopen hbounded hgraph hq
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

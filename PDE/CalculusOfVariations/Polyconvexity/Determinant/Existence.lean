/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Polyconvexity.Determinant.Dirichlet
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteProduct

/-!
# Polyconvex minimizers with prescribed geometric trace

A nonempty trace class and graph coercivity suffice for existence of a minimizer
of the original signed determinant energy. The class uses the trace on
the boundary with Hausdorff surface measure. Its affine description, weak
compactness, and determinant lower semicontinuity are all derived.

This gives the determinant-dependent polyconvex theorem in Evans, §8.2.4(b),
Theorem 9. The minimum is allowed to be infinite, as in the all-infinite case of
the direct-method proof. A finite competitor separately gives integrability and
an ordinary real integral at the minimizer. Positive dimensions are written `d + 1`;
thus `d = 0` includes one-dimensional domains. Neither connectedness nor
nonemptiness of the domain is required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Theorem 9.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.CalculusOfVariations

/-- A C1 polyconvex determinant density with Frobenius power coercivity has
a signed extended-energy minimizer in every nonempty prescribed trace class.
The exponent is any finite real number above the domain dimension, the lower
shift has either sign, and no finite-energy competitor is assumed. -/
theorem exists_minimizer_determinantWkpIntegral_of_nonempty_trace
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : ((d + 1 : ℕ) : ℝ) < q)
    {F : (ℝ^(d + 1) × ℝ^(d + 1)) ×
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^(d + 1),
      ConvexOn ℝ univ (fun R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ × ℝ ↦
        F ((x, s), R)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^(d + 1))
      (P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ F ((x, s), (P, P.det))) :
    let hq1 : 1 < q :=
      (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : ℝ^(d + 1) → ℝ^(d + 1),
      let A := {u : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω) |
        (Trace.C1.vectorTraceLp q u : ℝ^(d + 1) → ℝ^(d + 1)) =ᵐ[surfaceMeasure Ω] γ}
      A.Nonempty → ∃ u ∈ A, IsMinOn (vectorWkpIntegral (determinantDensity F)) A u := by
  have hq1 : 1 < q :=
    (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  let : Fact (0 < d + 1) := ⟨Nat.succ_pos d⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  dsimp only
  intro γ ⟨g, hg⟩
  let A := {v : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω) |
    (Trace.C1.vectorTraceLp q v : ℝ^(d + 1) → ℝ^(d + 1)) =ᵐ[surfaceMeasure Ω] γ}
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_determinantWkpIntegral_prescribed_boundary
    hopen hbounded hgraph hq hF hconvex hα hcoercive g
  have hclass (v : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω)) :
      v ∈ A ↔ ∀ i, v i - g i ∈ wkp0SubmoduleOn
        (n := d + 1) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω) :=
    Trace.C1.vectorTraceLp_ae_eq_iff_sub_mem_Wkp0_of_ae_eq q g hg v
  exact ⟨u, (hclass u).mpr hu, fun v hv ↦ hmin v ((hclass v).mp hv)⟩

/-- A single finite-energy admissible map gives a minimizer whose original
density is integrable. Its signed extended energy is its ordinary real integral,
and it still minimizes against the entire trace class, including infinite-energy
competitors. -/
theorem exists_minimizer_determinantWkpIntegral_of_finite_competitor
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : ((d + 1 : ℕ) : ℝ) < q)
    {F : (ℝ^(d + 1) × ℝ^(d + 1)) ×
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^(d + 1),
      ConvexOn ℝ univ (fun R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ × ℝ ↦
        F ((x, s), R)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^(d + 1))
      (P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ F ((x, s), (P, P.det))) :
    let hq1 : 1 < q :=
      (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : ℝ^(d + 1) → ℝ^(d + 1),
      let A := {u : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω) |
        (Trace.C1.vectorTraceLp q u : ℝ^(d + 1) → ℝ^(d + 1)) =ᵐ[surfaceMeasure Ω] γ}
      let I := vectorWkpIntegral (determinantDensity F)
      (∃ w ∈ A, I w ≠ ⊤) →
        ∃ u ∈ A, IsMinOn I A u ∧ I u ≠ ⊤ ∧
          Integrable (fun x ↦ determinantDensity F x
            (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure (d + 1) Ω) ∧
          I u = ((∫ x, determinantDensity F x
            (vectorWkpValueCLM u x, ∇ u x)
              ∂domainMeasure (d + 1) Ω : ℝ) : EReal) := by
  have hq1 : 1 < q :=
    (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  dsimp only
  intro γ ⟨w, hw, hfinite⟩
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_determinantWkpIntegral_of_nonempty_trace
    hopen hbounded hgraph hq hF hconvex hα hcoercive γ ⟨w, hw⟩
  have hfiniteu : vectorWkpIntegral (determinantDensity F) u ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (hmin hw)
  have hlower : ∀ᵐ x ∂domainMeasure (d + 1) Ω, -β ≤
      determinantDensity F x (vectorWkpValueCLM u x, ∇ u x) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    have h := hcoercive x hx (vectorWkpValueCLM u x)
      (Matrix.euclideanEquiv.symm (∇ u x))
    have hnonneg := mul_nonneg hα.le
      (Real.rpow_nonneg (norm_nonneg (∇ u x)) q)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    change -β ≤ F ((x, vectorWkpValueCLM u x),
      (Matrix.euclideanEquiv.symm (∇ u x),
        (Matrix.euclideanEquiv.symm (∇ u x)).det))
    linarith
  have hint := (PDE.Analysis.integrable_iff_lowerBoundedIntegral_ne_top
    (aestronglyMeasurable_determinantDensity hopen.measurableSet hF.continuousOn u)
    (integrable_const β) hlower).mpr hfiniteu
  exact ⟨u, hu, hmin, hfiniteu, hint, vectorWkpIntegral_eq_integral hint⟩

end PDE.CalculusOfVariations

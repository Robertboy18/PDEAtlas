/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Determinant.Dirichlet
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteProduct

/-!
# Prescribed-trace minimizers with determinant one

A convex gradient energy has a minimizer among maps with prescribed trace and determinant one.
This is Evans, §8.4.4(b), Theorem 7, which is stated for maps of three variables and `q > 3`.
Here the statement holds in every positive dimension, for each finite real exponent above that
dimension, on a bounded open domain with C¹ graph boundary, and with a signed lower shift. The
admissible class need only be nonempty; its minimum may be infinite.

The trace is the Hausdorff-measure trace and the determinant uses the
original weak derivative coordinates. We reduce the trace class to the affine class of
`exists_minimizer_matrixWkpIntegral_prescribed_boundary_det_eq_one` with
`Trace.C1.vectorTraceLp_ae_eq_iff_sub_mem_Wkp0_of_ae_eq`. Empty or disconnected domains need
no exceptions.

## Main results

* `exists_minimizer_matrixWkpIntegral_of_nonempty_trace_det_eq_one`: a minimizer of the signed
  extended energy on every nonempty admissible class.
* `exists_minimizer_matrixWkpIntegral_det_eq_one_of_finite_competitor`: if one admissible map
  has finite energy, the minimizer has an integrable density and its energy is the ordinary
  integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.4(b), Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.CalculusOfVariations

/-- A C¹ gradient density convex in the full matrix and coercive in its
Frobenius norm attains its original signed energy on every nonempty geometric
trace class with determinant one. Constants precede the uniform coercivity
bound, and no finite admissible energy is required. -/
theorem exists_minimizer_matrixWkpIntegral_of_nonempty_trace_det_eq_one
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : ((d + 1 : ℕ) : ℝ) < q)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ × ℝ^(d + 1) → ℝ}
    (hL : ContDiffOn ℝ 1 L (univ ×ˢ Ω))
    (hconvex : ∀ x ∈ Ω,
      ConvexOn ℝ univ (fun P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ↦ L (P, x)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ L (P, x)) :
    let hq1 : 1 < q :=
      (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : ℝ^(d + 1) → ℝ^(d + 1),
      let A := {u : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω) |
        (Trace.C1.vectorTraceLp q u : ℝ^(d + 1) → ℝ^(d + 1)) =ᵐ[surfaceMeasure Ω] γ ∧
        ∀ᵐ x ∂domainMeasure (d + 1) Ω,
          (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex (d + 1) j) (u i) x).det = 1}
      A.Nonempty → ∃ u ∈ A, IsMinOn
        (vectorWkpIntegral (fun x z ↦ L (Matrix.euclideanEquiv.symm z.2, x))) A u := by
  have hq1 : 1 < q :=
    (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  let : Fact (0 < d + 1) := ⟨Nat.succ_pos d⟩
  dsimp only
  intro γ ⟨g, hg⟩
  have hL' : ContDiffOn ℝ 1
      (fun t : (ℝ^(d + 1) × ℝ^(d + 1)) × Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ↦
        L (t.2, t.1.1)) ((Ω ×ˢ univ) ×ˢ univ) :=
    hL.comp (contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst)).contDiffOn
      (fun _ ht ↦ ⟨mem_univ _, ht.1.1⟩)
  obtain ⟨u, hdet, hu, hmin⟩ :=
    exists_minimizer_matrixWkpIntegral_prescribed_boundary_det_eq_one
      hopen hbounded hgraph hq hL' (fun x hx _ ↦ hconvex x hx) hα
      (fun x hx _ P ↦ hcoercive x hx P) g hg.2
  have hclass (v : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω)) :=
    Trace.C1.vectorTraceLp_ae_eq_iff_sub_mem_Wkp0_of_ae_eq q g hg.1 v
  exact ⟨u, ⟨(hclass u).mpr hu, hdet⟩,
    fun v hv ↦ hmin v hv.2 ((hclass v).mp hv.1)⟩

/-- If one admissible map has finite energy, the determinant-constrained
minimizer has an integrable density and its signed energy equals the ordinary
real integral. It still minimizes over the whole admissible class. -/
theorem exists_minimizer_matrixWkpIntegral_det_eq_one_of_finite_competitor
    {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : ((d + 1 : ℕ) : ℝ) < q)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ × ℝ^(d + 1) → ℝ}
    (hL : ContDiffOn ℝ 1 L (univ ×ˢ Ω))
    (hconvex : ∀ x ∈ Ω,
      ConvexOn ℝ univ (fun P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ↦ L (P, x)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ L (P, x)) :
    let hq1 : 1 < q :=
      (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : ℝ^(d + 1) → ℝ^(d + 1),
      let A := {u : Fin (d + 1) → W^{1,ENNReal.ofReal q}(Ω) |
        (Trace.C1.vectorTraceLp q u : ℝ^(d + 1) → ℝ^(d + 1)) =ᵐ[surfaceMeasure Ω] γ ∧
        ∀ᵐ x ∂domainMeasure (d + 1) Ω,
          (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex (d + 1) j) (u i) x).det = 1}
      let I := vectorWkpIntegral (fun x z ↦ L (Matrix.euclideanEquiv.symm z.2, x))
      (∃ w ∈ A, I w ≠ ⊤) →
        ∃ u ∈ A, IsMinOn I A u ∧ I u ≠ ⊤ ∧
          Integrable (fun x ↦ L (Matrix.euclideanEquiv.symm (∇ u x), x))
            (domainMeasure (d + 1) Ω) ∧
          I u = ((∫ x, L (Matrix.euclideanEquiv.symm (∇ u x), x)
            ∂domainMeasure (d + 1) Ω : ℝ) : EReal) := by
  have hq1 : 1 < q :=
    (show (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_pos d).trans_lt hq
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq1.le⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  dsimp only
  intro γ ⟨w, hw, hwfinite⟩
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_matrixWkpIntegral_of_nonempty_trace_det_eq_one
    hopen hbounded hgraph hq hL hconvex hα hcoercive γ ⟨w, hw⟩
  have hfinite : vectorWkpIntegral (fun x z ↦ L (Matrix.euclideanEquiv.symm z.2, x)) u ≠ ⊤ :=
    ne_top_of_le_ne_top hwfinite (hmin hw)
  have hL' : ContDiffOn ℝ 1
      (fun t : (ℝ^(d + 1) × ℝ^(d + 1)) × Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ↦
        L (t.2, t.1.1)) ((Ω ×ˢ univ) ×ˢ univ) :=
    hL.comp (contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst)).contDiffOn
      (fun _ ht ↦ ⟨mem_univ _, ht.1.1⟩)
  have hlower : ∀ᵐ x ∂domainMeasure (d + 1) Ω,
      -β ≤ L (Matrix.euclideanEquiv.symm (∇ u x), x) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    have h := hcoercive x hx (Matrix.euclideanEquiv.symm (∇ u x))
    have hnonneg := mul_nonneg hα.le
      (Real.rpow_nonneg (norm_nonneg (∇ u x)) q)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    linarith
  have hint := (PDE.Analysis.integrable_iff_lowerBoundedIntegral_ne_top
    (aestronglyMeasurable_matrixWkpDensity hopen.measurableSet hL'.continuousOn u)
    (integrable_const β) hlower).mpr hfinite
  exact ⟨u, hu, hmin, hfinite, hint, vectorWkpIntegral_eq_integral hint⟩

end PDE.CalculusOfVariations

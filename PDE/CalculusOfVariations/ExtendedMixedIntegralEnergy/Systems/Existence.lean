/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Classical
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteProduct

/-!
# Existence of minimizers for coupled variational systems

Evans, §8.2.4(a), Theorem 5: a density convex
in the full gradient matrix and coercive in its Frobenius norm attains its
extended minimum in a nonempty prescribed-trace class. The domain is bounded and
open with C1 graph boundary; the target dimension and the density's coupling are
arbitrary.

The nonnegative integral of `L + β` retains infinite energies. On the bounded
domain it differs from the lower-bounded energy by the finite constant `β |Ω|`.
The direct method includes the case where every admissible energy is infinite.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(a), Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Matrix.Norms.Frobenius Sobolev

namespace PDE.CalculusOfVariations

/-- A coupled matrix energy attains its extended minimum in every nonempty
geometric trace class. The C1 atlas and the exponent instances are constructed
from the displayed assumptions; neither a finite-energy competitor nor upper
growth is required. The finite target dimension may be zero. -/
theorem exists_minimizer_matrixWkpLIntegral_of_nonempty_trace
    {m d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 < q)
    {L : (ℝ^(d + 1) × ℝ^m) × Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun P : Matrix (Fin m) (Fin (d + 1)) ℝ ↦ L ((x, s), P)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^m) (P : Matrix (Fin m) (Fin (d + 1)) ℝ),
      α * ‖P‖ ^ q - β ≤ L ((x, s), P)) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp (ℝ^m) (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      {u : Fin m → W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.vectorTraceLp q u = γ}.Nonempty →
      ∃ u : Fin m → W^{1,ENNReal.ofReal q}(Ω),
        Trace.C1.vectorTraceLp q u = γ ∧
        ∀ v : Fin m → W^{1,ENNReal.ofReal q}(Ω),
          Trace.C1.vectorTraceLp q v = γ →
          vectorWkpLIntegral
            (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) (fun _ ↦ β) u ≤
          vectorWkpLIntegral
            (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) (fun _ ↦ β) v := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  have : Fact (0 < d + 1) := ⟨Nat.succ_pos _⟩
  intro γ hγ
  obtain ⟨g, hg⟩ := hγ
  have hp : 1 < q.toNNReal := by
    exact_mod_cast (show (1 : ℝ) < (q.toNNReal : ℝ) by
      simpa only [Real.coe_toNNReal q (le_trans zero_le_one hq.le)] using hq)
  have : Fact (1 ≤ (q.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp.le⟩
  have hlower : ∀ x ∈ Ω, ∀ (s : ℝ^m) (P : Matrix (Fin m) (Fin (d + 1)) ℝ),
      α * ‖P‖ ^ (q.toNNReal : ℝ) - β ≤ L ((x, s), P) := by
    simpa only [Real.coe_toNNReal q (le_trans zero_le_one hq.le)] using hcoercive
  obtain ⟨u, hu, hmin⟩ :=
    exists_minimizer_matrixWkpLIntegral_prescribed_boundary
      hopen hbounded hgraph hp hL hconvex hα hlower g
  have hclass (v : Fin m → W^{1,ENNReal.ofReal q}(Ω)) :=
    Trace.C1.vectorTraceLp_eq_iff_sub_mem_Wkp0_of_trace q g hg v
  exact ⟨u, (hclass u).mpr hu, fun v hv ↦ hmin v ((hclass v).mp hv)⟩

/-- Evans §8.2.4(a), Theorem 5, for the original signed energy: a fully
coupled gradient-matrix density attains its extended minimum on each nonempty
prescribed-trace class. The energy is the difference of its positive
and negative part integrals. Coercivity and finite volume make the negative
part finite; no upper growth or finite-energy competitor is required. The
case where every admissible energy is positive infinity is included. -/
theorem exists_minimizer_matrixWkpIntegral_of_nonempty_trace
    {m d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} (hq : 1 < q)
    {L : (ℝ^(d + 1) × ℝ^m) × Matrix (Fin m) (Fin (d + 1)) ℝ → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun P : Matrix (Fin m) (Fin (d + 1)) ℝ ↦ L ((x, s), P)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^m) (P : Matrix (Fin m) (Fin (d + 1)) ℝ),
      α * ‖P‖ ^ q - β ≤ L ((x, s), P)) :
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω :=
      hgraph.c1ExtensionAtlas hopen hbounded
    ∀ γ : Lp (ℝ^m) (ENNReal.ofReal q) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω),
      {u : Fin m → W^{1,ENNReal.ofReal q}(Ω) |
        Trace.C1.vectorTraceLp q u = γ}.Nonempty →
      ∃ u : Fin m → W^{1,ENNReal.ofReal q}(Ω),
        Trace.C1.vectorTraceLp q u = γ ∧
        ∀ v : Fin m → W^{1,ENNReal.ofReal q}(Ω),
          Trace.C1.vectorTraceLp q v = γ →
          vectorWkpIntegral
            (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) u ≤
          vectorWkpIntegral
            (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) v := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω :=
    hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  intro γ hγ
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_matrixWkpLIntegral_of_nonempty_trace
    hopen hbounded hgraph hq hL hconvex hα hcoercive γ hγ
  have hlower : ∀ x ∈ Ω, ∀ (s : ℝ^m) (P : Matrix (Fin m) (Fin (d + 1)) ℝ),
      -β ≤ L ((x, s), P) := by
    intro x hx s P
    have hnonneg := mul_nonneg hα.le (Real.rpow_nonneg (norm_nonneg P) q)
    exact (by linarith : -β ≤ α * ‖P‖ ^ q - β).trans (hcoercive x hx s P)
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  rw [vectorWkpIntegral_eq_lIntegral_sub_of_continuousOn
      hopen.measurableSet hL.continuousOn hlower u,
    vectorWkpIntegral_eq_lIntegral_sub_of_continuousOn
      hopen.measurableSet hL.continuousOn hlower v]
  exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmin v hv)) le_rfl

end PDE.CalculusOfVariations

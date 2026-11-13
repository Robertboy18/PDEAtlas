/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.FiniteExponent
import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.OneDimensionalCritical
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Embedding
import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.ExponentRestriction

/-!
# Poincaré's inequality after subtracting the mean

On a bounded connected open C1 domain, the `Lᵖ` norm of a Sobolev function minus its
spatial average is bounded by its weak gradient norm, for every `1 ≤ p ≤ ∞`.
This is Poincaré's inequality, Evans §5.8.1, Theorem 1.
Rellich compactness supplies the finite-exponent estimate, as in Evans's proof. The
one-dimensional critical embedding and finite-exponent Morrey embedding supply the remaining
endpoint cases.

The final theorems, `exists_norm_base_subtractMean_le_of_c1GraphBoundary` and
`exists_poincare_mean_of_c1GraphBoundary`, build their extension atlas from the local C1 graph
condition. Neither an extension estimate nor compactness is a hypothesis of those theorems.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.1, Theorem 1, p. 290.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

private theorem exists_norm_base_subtractMean_le_of_bounded_embedding
    {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [IsFiniteMeasure (domainMeasure n Ω)] (hqp : q ≤ p)
    (L : W^{1,q}(Ω) →L[ℝ] ((ℝ^n) →ᵇ ℝ))
    (hL : ∀ U, (fun x ↦ L U x) =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM U)
    (hP : ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,q}(Ω),
      ‖subtractMean U‖ ≤ C * ‖∇ U‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(Ω),
      ‖wkpBaseCoordinateCLM (subtractMean U)‖ ≤ C * ‖∇ U‖ := by
  obtain ⟨C, hC, hP⟩ := hP
  let R := ((domainMeasure n Ω) univ ^ (1 / q.toReal - 1 / p.toReal)).toReal
  let M : ℝ := measureUnivNNReal (domainMeasure n Ω) ^ p.toReal⁻¹
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  have hM : 0 ≤ M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  refine ⟨M * (‖L‖ * C * R) + 1, by positivity, fun U ↦ ?_⟩
  let V := lowerExponentOfFiniteMeasureCLM hqp U
  have hagree : (fun x ↦ L (subtractMean V) x) =ᵐ[domainMeasure n Ω]
      wkpBaseCoordinateCLM (subtractMean U) :=
    (hL (subtractMean V)).trans (subtractMean_lowerExponent_base_ae hqp U)
  have hgrad : ‖∇ V‖ ≤ R * ‖∇ U‖ :=
    norm_lowerExponent_gradient_le hqp U
  have hbound : ∀ᵐ x ∂domainMeasure n Ω,
      ‖wkpBaseCoordinateCLM (subtractMean U) x‖ ≤
        (‖L‖ * C * R) * ‖∇ U‖ := by
    filter_upwards [hagree] with x hx
    rw [← hx]
    calc
      ‖L (subtractMean V) x‖ ≤ ‖L (subtractMean V)‖ :=
        (L (subtractMean V)).norm_coe_le_norm x
      _ ≤ ‖L‖ * ‖subtractMean V‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (C * ‖∇ V‖) :=
        mul_le_mul_of_nonneg_left (hP V) (norm_nonneg L)
      _ ≤ ‖L‖ * (C * (R * ‖∇ U‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgrad hC.le) (norm_nonneg L)
      _ = _ := by ring
  calc
    ‖wkpBaseCoordinateCLM (subtractMean U)‖
        ≤ M * ((‖L‖ * C * R) * ‖∇ U‖) :=
      Lp.norm_le_of_ae_bound (by positivity) hbound
    _ ≤ (M * (‖L‖ * C * R) + 1) * ‖∇ U‖ := by
      nlinarith [norm_nonneg (∇ U)]

/-- On a one-dimensional connected C1 extension domain, mean-subtracted Poincaré holds
at every exponent, including one and infinity. The critical `W¹¹` embedding supplies the
uniform bound after the `L¹` Poincaré estimate. -/
theorem exists_norm_base_subtractMean_le_oneDimension
    {Ω : Set (ℝ^1)} [Boundary.C1ExtensionAtlas 1 Ω]
    (hconn : IsConnected Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(Ω),
      ‖wkpBaseCoordinateCLM (subtractMean U)‖ ≤ C * ‖∇ U‖ := by
  apply exists_norm_base_subtractMean_le_of_bounded_embedding (Fact.out : 1 ≤ p)
    (CriticalOneDimensional.criticalEmbedding.comp
      (Extension.C1.extensionCLM (n := 1) (p := 1) (Ω := Ω)))
  · exact CriticalOneDimensional.criticalEmbeddingOn_ae
  · exact exists_norm_subtractMean_le_one_of_c1Domain hconn

/-- On a connected C1 extension domain of dimension at least two, the infinity endpoint
follows from a finite exponent above the dimension and the Morrey embedding. -/
theorem exists_norm_base_subtractMean_le_top_of_c1Domain
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} [Boundary.C1ExtensionAtlas n Ω]
    (hn : 2 ≤ n) (hconn : IsConnected Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,∞}(Ω),
      ‖wkpBaseCoordinateCLM (subtractMean U)‖ ≤ C * ‖∇ U‖ := by
  let q : ℝ := n + 1
  have hq : (n : ℝ) < q := by dsimp [q]; linarith
  have hq1 : 1 < q := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Fact.out : 0 < n)
    dsimp [q]
    linarith
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨(ENNReal.one_lt_ofReal.mpr hq1).le⟩
  let L := HolderSpace.C0GammaOn.toBoundedContinuousFunctionCLM.comp
    ((finiteMorreyEmbedding (Fact.out : 0 < n) hq
      (Real.HolderConjugate.conjExponent hq1)).comp
        (Extension.C1.extensionCLM (n := n) (p := ENNReal.ofReal q) (Ω := Ω)))
  apply exists_norm_base_subtractMean_le_of_bounded_embedding
    (p := ∞) (q := ENNReal.ofReal q) le_top L
  · exact finiteMorreyEmbeddingOn_ae hq (Real.HolderConjugate.conjExponent hq1)
  · have : Fact (1 ≤ q.toNNReal) := ⟨by simpa using hq1.le⟩
    convert!
      exists_norm_subtractMean_le_finite_of_c1Domain (p := q.toNNReal) hn hconn
      using 1

/-- Every connected C1 extension domain satisfies mean-subtracted Poincaré for arbitrary
Sobolev elements at every exponent `1 ≤ p ≤ ∞`. -/
theorem exists_norm_base_subtractMean_le_of_c1Domain
    {n : ℕ} [hn : Fact (0 < n)] {Ω : Set (ℝ^n)} [Boundary.C1ExtensionAtlas n Ω]
    (hconn : IsConnected Ω) {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(Ω),
      ‖wkpBaseCoordinateCLM (subtractMean U)‖ ≤ C * ‖∇ U‖ := by
  by_cases hn1 : n = 1
  · subst n
    exact exists_norm_base_subtractMean_le_oneDimension hconn
  have hn2 : 2 ≤ n := by have := hn.out; omega
  by_cases hptop : p = ∞
  · subst p
    exact exists_norm_base_subtractMean_le_top_of_c1Domain hn2 hconn
  lift p to ℝ≥0 using hptop
  have : Fact (1 ≤ p) := ⟨by exact_mod_cast hp.out⟩
  obtain ⟨C, hC, hP⟩ := exists_norm_subtractMean_le_finite_of_c1Domain (p := p) hn2 hconn
  refine ⟨C, hC, fun U ↦ ?_⟩
  exact (wkpBaseCoordinateCLM_norm_le _).trans (hP U)

/-- Evans §5.8.1, Theorem 1: if `Ω ⊆ ℝ^(n+1)` is open, bounded and connected with C1 graph
boundary and `1 ≤ p ≤ ∞`, there is `C > 0` such that the base coordinate of `u - (u)_Ω` has
norm at most `C * ‖∇ u‖` for every `u ∈ W^{1,p}(Ω)`. The extension atlas used in the proof is
built from the graph boundary hypothesis. -/
theorem exists_norm_base_subtractMean_le_of_c1GraphBoundary
    {n : ℕ} {Ω : Set (ℝ^(n + 1))}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    let := hgraph.c1ExtensionAtlas hΩ hbounded
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(Ω),
      ‖wkpBaseCoordinateCLM (subtractMean U)‖ ≤ C * ‖∇ U‖ := by
  let := hgraph.c1ExtensionAtlas hΩ hbounded
  exact exists_norm_base_subtractMean_le_of_c1Domain hconn

/-- Poincaré's inequality with the integral average written out: if `Ω ⊆ ℝ^(n+1)` is open,
bounded and connected with C1 graph boundary and `1 ≤ p ≤ ∞`, there is `C > 0` with
`‖u - ⨍_Ω u‖_{Lᵖ(Ω)} ≤ C * ‖∇ u‖` for every `u ∈ W^{1,p}(Ω)`. The statement mentions no atlas
or finite-measure instance. -/
theorem exists_poincare_mean_of_c1GraphBoundary
    {n : ℕ} {Ω : Set (ℝ^(n + 1))}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(Ω),
      (eLpNorm (fun x ↦ wkpBaseCoordinateCLM U x -
        ⨍ y, wkpBaseCoordinateCLM U y ∂domainMeasure (n + 1) Ω)
          p (domainMeasure (n + 1) Ω)).toReal ≤ C * ‖∇ U‖ := by
  let := hgraph.c1ExtensionAtlas hΩ hbounded
  obtain ⟨C, hC, hP⟩ := exists_norm_base_subtractMean_le_of_c1Domain (p := p) hconn
  refine ⟨C, hC, fun U ↦ ?_⟩
  rw [← eLpNorm_congr_ae (subtractMean_base_ae U), ← Lp.norm_def]
  exact hP U

end SobolevSpace.GraphSpace

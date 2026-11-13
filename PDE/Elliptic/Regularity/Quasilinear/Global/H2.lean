/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.GeometricAtlas
public import PDE.Elliptic.Monotone.Estimates.Dirichlet
public import PDE.Elliptic.Regularity.Quasilinear.Interior.LocalRegularity
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.Constant
import PDE.Spaces.Sobolev.Localization.Assembly.Partition

/-!
# Global H² regularity for a strongly monotone Lipschitz flux

Local interior and boundary representatives are summed using the
finite partition of unity. The resulting `H²` field has the same
almost-everywhere base representative as the original `H¹₀` solution.
The boundary proof recovers the normal derivative from the nonlinear
flux; no differentiability of the flux or regularity of the solution is
assumed.

The geometric endpoint takes bounded C² graph boundary data. All
positive dimensions, including one, and the empty open set are allowed.
This supplies the regularity implication used for the gradient-energy
subdifferential in Evans, *Partial Differential Equations*, §9.6.3.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A weak Dirichlet solution for a centered strongly monotone
Lipschitz flux and an `L²` load has a global `H²` representative. -/
theorem exists_H2_of_centered_monotone_weakEquation
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : ℝ^n → ℝ^n) (hzero : A 0 = 0) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : H¹₀(Ω))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
    (∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x)) →
    (∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
    ∃ W : W^{2,2}(Ω),
      (baseRepresentative W =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ)) ∧
      ‖W‖ ≤ M * ‖f‖ := by
  classical
  let P := hΩ.toC1ExtensionAtlas
  obtain ⟨M₀, hM₀, hlocal₀⟩ := exists_H2_interiorCutoff_of_monotone_weakEquation P
    A hzero hθ hmono hLip P.interiorCutoff P.interiorCutoff_support
  choose M hM hlocal using fun i ↦ exists_H2_physicalChartCutoff_of_monotone_weakEquation
    P i (hΩ.chart_contDiff_two i) (hΩ.chart_symm_contDiff_two i)
    A hzero hθ hmono hLip (P.boundaryCutoff i) (P.boundaryCutoff_support i)
  let K := M₀ + ∑ i, M i
  have hK : 0 ≤ K := add_nonneg hM₀ (Finset.sum_nonneg fun i _ ↦ hM i)
  obtain ⟨M₁, hM₁, henergy⟩ := exists_H10_norm_bound_of_gradient_coercivity
    (Fact.out : 0 < n) hΩ.bounded hθ
  refine ⟨K * (M₁ + 1), mul_nonneg hK (add_nonneg hM₁.le zero_le_one), ?_⟩
  intro u q f hq hweak
  have hcoercive : ∀ᵐ x ∂domainMeasure n Ω,
      θ * ‖∇ (u : H¹(Ω)) x‖ ^ 2 ≤ ⟪Lp.euclideanTuple q x, ∇ (u : H¹(Ω)) x⟫ := by
    filter_upwards [hq, gradientCLM_apply_ae u, Lp.euclideanTuple_apply_ae q]
      with x hx hd hQ
    have hd' : WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x) = ∇ (u : H¹(Ω)) x := by
      apply PiLp.ext
      intro i
      exact (hd i).symm
    have hQ' : WithLp.toLp 2 (fun i ↦ q i x) = Lp.euclideanTuple q x := by
      apply PiLp.ext
      intro i
      exact (hQ i).symm
    rw [hd', hQ'] at hx
    simpa only [hzero, sub_zero, hx, pow_two, mul_assoc] using hmono (∇ (u : H¹(Ω)) x) 0
  have hu : ‖u‖ ≤ M₁ * ‖f‖ := henergy u q f hcoercive (hweak u)
  obtain ⟨W₀, hW₀, hW₀norm⟩ := hlocal₀ u q f hq hweak
  choose W hW hWnorm using fun i ↦ hlocal i u q f hq hweak
  refine ⟨partitionAssembly W₀ W,
    partitionAssembly_base_ae P (baseCoordCLM u) W₀ W hW₀ hW, ?_⟩
  calc
    _ ≤ ‖W₀‖ + ∑ i, ‖W i‖ := norm_partitionAssembly_le W₀ W
    _ ≤ M₀ * (‖u‖ + ‖f‖) + ∑ i, M i * (‖u‖ + ‖f‖) :=
      add_le_add hW₀norm (Finset.sum_le_sum fun i _ ↦ hWnorm i)
    _ = K * (‖u‖ + ‖f‖) := by rw [← Finset.sum_mul]; exact (add_mul _ _ _).symm
    _ ≤ K * (M₁ * ‖f‖ + ‖f‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hu le_rfl) hK
    _ = _ := by ring

/-- A constant part of the flux vanishes against zero-boundary tests.
Thus global regularity holds for arbitrary strongly monotone Lipschitz
fluxes, including gradients of densities with a nonzero affine part. -/
theorem exists_H2_of_monotone_weakEquation
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : ℝ^n → ℝ^n) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : H¹₀(Ω))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
    (∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x)) →
    (∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
    ∃ W : W^{2,2}(Ω),
      (baseRepresentative W =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ)) ∧
      ‖W‖ ≤ M * ‖f‖ := by
  have hLip' : LipschitzWith C (fun z ↦ A z - A 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [dist_sub_right] using hLip.dist_le_mul z w
  obtain ⟨M, hM, hcentered⟩ := exists_H2_of_centered_monotone_weakEquation hΩ
    (fun z ↦ A z - A 0) (sub_self _) hθ (fun z w ↦ by simpa using hmono z w) hLip'
  refine ⟨M, hM, ?_⟩
  intro u q f hq hweak
  let := isFiniteMeasure_domainMeasure_of_isBounded hΩ.bounded
  let c : Fin n → DerivLp n 2 Ω := fun i ↦
    (wkpConstant (n := n) (p := 2) (Ω := Ω) (A 0 i)).val (baseIndex n 1)
  have hc (i : Fin n) : (c i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ A 0 i :=
    wkpConstant_base_ae _
  apply hcentered u (fun i ↦ q i - c i) f
  · have hcoords := ae_all_iff.mpr fun i ↦ (Lp.coeFn_sub (q i) (c i)).and (hc i)
    filter_upwards [hq, hcoords] with x hx hy
    apply PiLp.ext
    intro i
    have hqi := congrArg (fun z : ℝ^n ↦ z i) hx
    change A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) i = q i x at hqi
    change A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) i - A 0 i =
      (q i - c i) x
    rw [(hy i).1]
    change _ = q i x - c i x
    rw [hqi, (hy i).2]
  · intro v
    have hci (i : Fin n) : ⟪c i, derivCoordCLM i v⟫ = 0 :=
      inner_constant_derivCoordCLM_eq_zero (A 0 i) (c i) (hc i) i v
    simpa only [inner_sub_left, hci, sub_zero] using hweak v

/-- C² graph boundary data suffice for global nonlinear `H²` regularity;
the operational atlas is constructed from the geometry. -/
theorem exists_H2_of_monotone_weakEquation_of_graphBoundary
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : SobolevSpace.Boundary.HasContDiffGraphBoundary 2 Ω)
    (A : ℝ^n → ℝ^n) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : H¹₀(Ω))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
    (∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x)) →
    (∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
    ∃ W : W^{2,2}(Ω),
      (baseRepresentative W =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ)) ∧
      ‖W‖ ≤ M * ‖f‖ :=
  exists_H2_of_monotone_weakEquation (hgraph.c2BoundaryAtlas le_rfl hopen hbounded)
    A hθ hmono hLip

end PDE.Elliptic.Regularity.Quasilinear

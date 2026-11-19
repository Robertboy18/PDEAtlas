/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.GradientReaction.Existence
public import PDE.Elliptic.Regularity.Global.Poisson

/-!
# Zero-boundary `H²` solutions of a Lipschitz gradient reaction

For every positive dimension and bounded open `C²` domain, the threshold
`μ ≥ 1 + K²` gives a unique weak solution of `-Δu + b(Du) + μu = 0`.
Its `L²` Poisson load is `-b(Du)-μu`. Global regularity supplies an `H²`
representative of that same `H¹₀` field, including all first weak derivatives.

The endpoint proves both the `L²` equation and its almost-everywhere form with the
diagonal second derivatives. The threshold precedes the domain and reaction
data and imposes no restriction on `b(0)`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.GradientReaction

open MeasureTheory BoundaryRegularity
open scoped ENNReal NNReal Sobolev Laplacian

variable {n : ℕ} {Ω : Set (ℝ^n)} {K : ℝ≥0} {b : ℝ^n → ℝ}

/-- An equality of strong loads gives the original equation almost everywhere. -/
theorem ae_equation_of_load_eq_zero
    (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b) (μ : ℝ)
    (u : H¹₀(Ω)) (U : W^{2,2}(Ω))
    (h : -(Δ U) + reaction hbounded hb u + μ • baseCoordCLM u = 0) :
    ∀ᵐ x ∂domainMeasure n Ω,
      -(∑ i : Fin n, (U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i i) x) +
        b (∇ (u : H¹(Ω)) x) + μ * baseCoordCLM u x = 0 := by
  have hz :
      ((-(Δ U) + reaction hbounded hb u + μ • baseCoordCLM u :
        DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] 0 := by
    rw [h]
    exact Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)
  filter_upwards
    [hz, Lp.coeFn_add (-(Δ U) + reaction hbounded hb u) (μ • baseCoordCLM u),
      Lp.coeFn_add (-(Δ U)) (reaction hbounded hb u),
      Lp.coeFn_neg (Δ U), wkpLaplacianCLM_coeFn U,
      reaction_coeFn hbounded hb u, Lp.coeFn_smul μ (baseCoordCLM u)] with
    x hx hadd hsum hneg hlap hb hsmul
  change (Δ U : DerivLp n 2 Ω) x = _ at hlap
  simpa only [hadd, Pi.add_apply, hsum, hneg, Pi.neg_apply, hlap, hb, hsmul,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hx

/-- Any weak solution on a bounded `C²` domain has an `H²` representative of the
same `H¹₀` field, with the exact strong load and almost-everywhere equation. -/
theorem exists_h2_of_isWeakSolution [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hb : LipschitzWith K b) (μ : ℝ) (u : H¹₀(Ω))
    (hu : IsWeakSolution b μ u) :
    ∃ U : W^{2,2}(Ω),
      wkpBaseCoordinateCLM U = baseCoordCLM u ∧
      lowerOrderCLM (k := 1) (m := 2) (by omega) U = (u : H¹(Ω)) ∧
      -(Δ U) + reaction hbounded hb u + μ • baseCoordCLM u = 0 ∧
      (∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
        ∇ (u : H¹(Ω)) x i =
          (U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by norm_num) i) x) ∧
      ∀ᵐ x ∂domainMeasure n Ω,
        -(∑ i : Fin n, (U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i i) x) +
          b (∇ (u : H¹(Ω)) x) + μ * baseCoordCLM u x = 0 := by
  have hop := (weakOperator_eq_zero_iff hbounded hb μ u).2 hu
  obtain ⟨U, hbase, hload⟩ := (dirichletForm_eq_load_iff_h2 hopen hbounded hgraph u _).1
    (dirichletForm_eq_load_of_weakOperator_eq_zero hbounded hb μ u hop)
  have hfirst := lowerOrder_eq_h10SubtypeL_of_base_eq hopen U u hbase
  have hstrong : -(Δ U) + reaction hbounded hb u + μ • baseCoordCLM u = 0 := by
    rw [hload]
    abel
  refine ⟨U, hbase, hfirst, hstrong, ?_, ae_equation_of_load_eq_zero hbounded hb μ u U hstrong⟩
  have hgrad := wkpGradientCLM_apply_ae (lowerOrderCLM (k := 1) (m := 2) (by omega) U)
  have heq : ∇ (lowerOrderCLM (k := 1) (m := 2) (by omega) U) = ∇ (u : H¹(Ω)) := by
    rw [hfirst]
  rw [heq] at hgrad
  simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex] using hgrad

/-- Every positive dimension and every globally Lipschitz gradient reaction admit a unique
zero-boundary `H²` solution once `μ ≥ 1+K²`. No weak solution or regularity
of the solution is assumed. -/
theorem existsUnique_h2_solution (n : ℕ) (hn : 0 < n) (K : ℝ≥0)
    (μ : ℝ) (hμ : 1 + (K : ℝ) ^ 2 ≤ μ)
    (Ω : Set (ℝ^n)) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (b : ℝ^n → ℝ) (hb : LipschitzWith K b) :
    ∃! u : H¹₀(Ω), IsWeakSolution b μ u ∧
      ∃ U : W^{2,2}(Ω),
        wkpBaseCoordinateCLM U = baseCoordCLM u ∧
        lowerOrderCLM (k := 1) (m := 2) (by omega) U = (u : H¹(Ω)) ∧
        -(Δ U) + reaction hbounded hb u + μ • baseCoordCLM u = 0 ∧
        (∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
          ∇ (u : H¹(Ω)) x i =
            (U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by norm_num) i) x) ∧
        ∀ᵐ x ∂domainMeasure n Ω,
          -(∑ i : Fin n, (U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i i) x) +
            b (∇ (u : H¹(Ω)) x) + μ * baseCoordCLM u x = 0 := by
  let : Fact (0 < n) := ⟨hn⟩
  obtain ⟨u, hu, huniq⟩ := existsUnique_weakSolution μ hμ hbounded hb
  have hweak := (weakOperator_eq_zero_iff hbounded hb μ u).1 hu
  exact ⟨u, ⟨hweak, exists_h2_of_isWeakSolution hopen hbounded hgraph hb μ u hweak⟩,
    fun v hv ↦ huniq v ((weakOperator_eq_zero_iff hbounded hb μ v).2 hv.1)⟩

end SobolevSpace.GraphSpace.GradientReaction

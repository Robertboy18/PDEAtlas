/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.LowerSemicontinuity
public import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.Lift
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.VectorValues

/-!
# Lower semicontinuity for convex matrix–determinant densities

Strong L¹ convergence of the values and weak L^(q/n) convergence of
the joint gradient–determinant lift feed the mixed convex integral theorem.
The lower bound is imposed only on the determinant graph. It need not
hold when the scalar coordinate varies independently of the matrix.

No growth bound or finite energy is assumed. The result includes every
positive dimension and every finite real exponent above that dimension.
It is the measurable-density form of Evans, §8.2.4(b), Theorem 8, whose proof
combines the weak convergence (54) of the determinants with the convexity (52).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Lemma (Weak continuity of determinants)
  and Theorem 8.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace PDE.CalculusOfVariations

/-- Lower semicontinuity of a shifted integral convex in the joint independent
matrix and determinant variables, with a lower bound only on their graph. -/
theorem lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_convex_determinant
    {n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)}
    (hbounded : Bornology.IsBounded (Ω : Set (ℝ^n)))
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set (ℝ^n)))
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (n : ℝ))] (hq : (n : ℝ) < q)
    {F : ℝ^n → ℝ^n × ℝ^(n * n + 1) → ℝ}
    {D : ℝ^n → ℝ^n × ℝ^(n * n + 1) → ℝ^(n * n + 1)} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(n * n + 1),
      Continuous (fun s : ℝ^n ↦ F x (s, z)))
    (hDcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(n * n + 1),
      Continuous (fun s : ℝ^n ↦ D x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun z : ℝ^(n * n + 1) ↦ F x (s, z)))
    (hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^n) (z : ℝ^(n * n + 1)),
      HasFDerivAt (fun y : ℝ^(n * n + 1) ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ),
      b x ≤ F x (s, Matrix.euclideanScalarEquiv (P, P.det)))
    {u : ℕ → Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin n → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) U))) :
    (∫⁻ x, ENNReal.ofReal (F x (vectorWkpValueCLM U x,
        Matrix.euclideanScalarEquiv
          (Matrix.euclideanEquiv.symm (∇ U x),
            (Matrix.euclideanEquiv.symm (∇ U x)).det)) - b x)
      ∂domainMeasure n Ω) ≤
      liminf (fun k ↦ ∫⁻ x, ENNReal.ofReal (F x (vectorWkpValueCLM (u k) x,
        Matrix.euclideanScalarEquiv
          (Matrix.euclideanEquiv.symm (∇ (u k) x),
            (Matrix.euclideanEquiv.symm (∇ (u k) x)).det)) - b x)
        ∂domainMeasure n Ω) atTop := by
  have hn : 0 < n := Fact.out
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  obtain ⟨atlas, _, _⟩ :=
    (Boundary.hasContDiffGraphBoundary_one_iff.mpr hgraph).exists_c1ExtensionAtlas
      le_rfl Ω.isOpen hbounded
  let := atlas
  let r := ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)
  let s := ENNReal.conjExponent r
  have : ENNReal.HolderConjugate r s := inferInstance
  have : Fact (1 ≤ s) := ⟨ENNReal.HolderConjugate.one_le s r⟩
  have hs_top : s ≠ ∞ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt s r).mpr
      (ENNReal.one_lt_ofReal_div_nat hn hq)).ne
  let W := Fin n → W^{1,ENNReal.ofReal q}(Ω)
  let B : W →L[ℝ] Lp (ℝ^n) 1 (domainMeasure n Ω) := RellichKondrachov.vectorValueL1CLM
  let G : W → Lp (ℝ^(n * n + 1)) r (domainMeasure n Ω) := wkpJacobianDetLift hn
  have hbase : Tendsto (fun k ↦ B (u k)) atTop (𝓝 (B U)) :=
    RellichKondrachov.tendsto_vectorValueL1CLM_of_tendsto_weak hu
  have hgradient : Tendsto (fun k ↦ toWeakSpace ℝ
      (Lp (ℝ^(n * n + 1)) r (domainMeasure n Ω)) (G (u k))) atTop
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^(n * n + 1)) r (domainMeasure n Ω)) (G U))) :=
    tendsto_weak_wkpJacobianDetLift_of_c1GraphBoundary hbounded hgraph hq hu
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (PDE.Analysis.isBounded_range_of_tendsto_weak hgradient)
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, b x ≤ F x (B U x, G U x) := by
    filter_upwards [coeFn_wkpJacobianDetLift hn U, hlower] with x hx hb
    change b x ≤ F x (B U x, wkpJacobianDetLift hn U x)
    rw [hx]
    exact hb _ _
  have henergy (v : W) :
      (∫⁻ x, ENNReal.ofReal (F x (B v x, G v x) - b x) ∂domainMeasure n Ω) =
        ∫⁻ x, ENNReal.ofReal (F x (vectorWkpValueCLM v x,
          Matrix.euclideanScalarEquiv
            (Matrix.euclideanEquiv.symm (∇ v x),
              (Matrix.euclideanEquiv.symm (∇ v x)).det)) - b x)
          ∂domainMeasure n Ω := by
    apply lintegral_congr_ae
    filter_upwards [RellichKondrachov.vectorValueL1CLM_apply_ae v,
      coeFn_wkpJacobianDetLift hn v] with x hx hg
    rw [show B v x = vectorWkpValueCLM v x from hx,
      show G v x = _ from hg]
  simpa only [henergy] using
    lintegral_le_liminf_of_tendsto_strong_weak_of_convex_gradient hs_top
      hF hD hb hFcont hDcont hconvex hderiv hbase hgradient hlow R
      (fun k ↦ hR _ (mem_range_self k))

end PDE.CalculusOfVariations

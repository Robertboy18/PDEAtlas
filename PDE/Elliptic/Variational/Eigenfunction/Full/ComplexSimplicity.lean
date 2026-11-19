/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.Full.Simplicity
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Complex

/-!
# Complex geometric simplicity of the principal eigenvalue

At a real eigenvalue the complex weak equation splits into two real
weak eigen-equations. Real geometric simplicity then identifies every
derivative coordinate of the complex graph with the corresponding complex
multiple of the positive eigenfunction.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The complex eigenspace at a positive eigenfunction is its complex span,
expressed using the recombination of real Sobolev graphs. The
identity holds for the full graph, including every weak derivative. -/
theorem eq_complexOfRealGraphs_of_nonneg_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    {r : ℝ} (hr : 0 < r) (u : H¹₀(Ω))
    (hu : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM u x)
    (hune : baseCoordCLM u ≠ 0)
    (hueq : ∀ w : H¹₀(Ω),
      P.form hopen hbounded u w = r * ⟪baseCoordCLM u, baseCoordCLM w⟫_ℝ)
    (U : ComplexWkSpaceOn n 1 Ω)
    (hUr : U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUi : U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUeq : ∀ v : H¹₀(Ω), P.complexForm hopen hbounded U v =
      (r : ℂ) * ∫ x, U.1 (baseIndex n 1) x *
        (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) :
    ∃ c : ℂ, U = complexOfRealGraphs ((c.re • u).1) ((c.im • u).1) := by
  have hre (v : H¹₀(Ω)) :
      P.form hopen hbounded ⟨U.re, hUr⟩ v =
        r * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ := by
    simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      (P.parts_of_complexForm_eq hopen hbounded U hUr hUi (r : ℂ) v (hUeq v)).1
  have him (v : H¹₀(Ω)) :
      P.form hopen hbounded ⟨U.im, hUi⟩ v =
        r * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ := by
    simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      (P.parts_of_complexForm_eq hopen hbounded U hUr hUi (r : ℂ) v (hUeq v)).2
  obtain ⟨a, ha⟩ := P.eq_smul_of_nonneg_eigenfunction hopen hbounded hconn hgraph
    halpha hell hc hr hu hune hueq hre
  obtain ⟨b, hb⟩ := P.eq_smul_of_nonneg_eigenfunction hopen hbounded hconn hgraph
    halpha hell hc hr hu hune hueq him
  refine ⟨⟨a, b⟩, ?_⟩
  apply Subtype.ext
  apply PiLp.ext
  intro i
  have hra : Complex.reCLM.compLpL 2 (domainMeasure n Ω) (U.1 i) = (a • u).1.1 i :=
    congrArg (fun v : H¹₀(Ω) ↦ v.1.1 i) ha
  have hib : Complex.imCLM.compLpL 2 (domainMeasure n Ω) (U.1 i) = (b • u).1.1 i :=
    congrArg (fun v : H¹₀(Ω) ↦ v.1.1 i) hb
  apply Lp.ext
  have hreal := Complex.reCLM.coeFn_compLpL (U.1 i)
  have himag := Complex.imCLM.coeFn_compLpL (U.1 i)
  rw [hra] at hreal
  rw [hib] at himag
  filter_upwards [hreal, himag, coeFn_complexLp ((a • u).1.1 i) ((b • u).1.1 i)]
    with x hx hy hz
  change U.1 i x = complexLp ((a • u).1.1 i) ((b • u).1.1 i) x
  rw [hz]
  apply Complex.ext
  · simpa using hx.symm
  · simpa using hy.symm

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

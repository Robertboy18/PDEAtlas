/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution.Bootstrap
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
import PDE.Elliptic.Regularity.Global.SmoothBoundary
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.ClassicalBoundary
import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary

/-!
# Classical solutions between subsolutions and supersolutions

A bounded weak solution bootstraps through all Sobolev orders on a smooth
bounded graph domain. Morrey reconstruction gives one representative smooth on
the closure. The trace kernel gives its pointwise zero boundary values, and
the full variational operator identifies its classical equation.

Only the geometry, coefficients, and reaction are assumed smooth. The reaction
need be smooth only near the bounded interval containing the barriers. The
dimension is any positive integer, and the principal matrix need not be
symmetric. Drift and potential terms are retained.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace
open MeasureTheory Set Boundary BoundaryRegularity
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- A bounded weak semilinear solution has a smooth representative satisfying
the full classical equation and vanishing on the entire frontier. The smooth
coefficient package stores only raw coefficient functions and their regularity. -/
theorem exists_classicalRepresentative_of_bounded_semilinear_solution
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, HasContDiffGraphBoundary k Ω)
    (P : SmoothFullCoefficients n Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    {f : ℝ → ℝ} {left right : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hinterval : Icc left right ⊆ s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (u : H¹₀(Ω))
    (hrange : ∀ᵐ x ∂domainMeasure n Ω, baseCoordCLM u x ∈ Icc left right)
    (hu : ∀ v : H¹₀(Ω), P.form hopen hbounded u v =
      ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂domainMeasure n Ω) :
    ∃ z : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      z =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ) ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧
      (∀ x ∈ Ω, z x ∈ Icc left right) ∧
      ∀ x ∈ Ω, P.classicalLoad z x = f (z x) := by
  have hall := exists_allOrderSobolevRepresentatives_of_bounded_semilinear_solution
    hopen hbounded hgraph P.principal P.drift P.potential
    P.principal_smooth P.drift_smooth P.potential_smooth halpha hell hs hinterval hf
    u hrange (fun v ↦ by
      rw [interiorFullDivergenceOperator_coe_H10]
      exact hu v)
  obtain ⟨atlas, _, _⟩ := (hgraph 2).exists_c2BoundaryAtlas (by norm_num) hopen hbounded
  obtain ⟨z, hz, hzae⟩ := exists_smoothRepresentativeOnClosure_of_all_orders
    hopen (baseCoordCLM u) hall (hasClassicalRepresentativesOnClosure atlas)
  have hzcont : ContinuousOn z Ω := hz.continuousOn.mono subset_closure
  have hzrange : ∀ x ∈ Ω, z x ∈ Icc left right := by
    have hlo : (fun x ↦ max left (z x)) =ᵐ[domainMeasure n Ω] z := by
      filter_upwards [hzae, hrange] with x hx hr
      exact max_eq_right (hx ▸ hr.1)
    have hhi : (fun x ↦ min right (z x)) =ᵐ[domainMeasure n Ω] z := by
      filter_upwards [hzae, hrange] with x hx hr
      exact min_eq_right (hx ▸ hr.2)
    have hlo' := Measure.eqOn_open_of_ae_eq hlo hopen (continuousOn_const.sup hzcont) hzcont
    have hhi' := Measure.eqOn_open_of_ae_eq hhi hopen (continuousOn_const.inf hzcont) hzcont
    exact fun x hx ↦ ⟨max_eq_right_iff.mp (hlo' hx), min_eq_right_iff.mp (hhi' hx)⟩
  have hzboundary : ∀ x ∈ frontier Ω, z x = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
    have htrace (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : ENNReal.ofReal 2 = p)
        (U : W^{1,p}(Ω))
        (hU : U ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p)
          (Ω := Ω)).toSubmodule)
        (hUz : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] z) :
        ∀ x ∈ frontier Ω, z x = 0 := by
      subst p
      exact (Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
        hopen hbounded ((hgraph 1).hasC1GraphBoundary le_rfl) 2
        U hz.continuousOn hUz).mp hU
    exact htrace 2 (ENNReal.ofReal_ofNat 2) u.val u.property hzae.symm
  have hz2 : ContDiffUpToBoundary 2 z Ω := by
    let : C1ExtensionAtlas n Ω := atlas.toC1ExtensionAtlas
    have hn : 0 < n := Fact.out
    let : Fact (1 ≤ (((2 * n : ℕ) : NNReal) : ℝ≥0∞)) :=
      ⟨by exact_mod_cast (by omega : 1 ≤ 2 * n)⟩
    obtain ⟨W, hW⟩ := hall (2 + n + 1)
    obtain ⟨jet, hjet⟩ := exists_supercriticalSobolevJet atlas 2 W
    obtain ⟨w, hw, _, hwae⟩ := exists_contDiffUpToBoundary_representative_of_dimension_lt
      (by exact_mod_cast (by omega : 1 < 2 * n))
      (by exact_mod_cast (by omega : n < 2 * n)) (by rfl : 2 + 1 ≤ 2 + 1) jet
    exact hw.congr hopen (Measure.eqOn_open_of_ae_eq
      (hzae.trans (hwae.trans (hjet.trans hW)).symm) hopen hzcont hw.contDiffOn.continuousOn)
  obtain ⟨F, hF⟩ := Composition.exists_hk_composition_on_domain_of_contDiffOn
    (by decide : 0 < 1) hopen hbounded (hgraph 1) hs hinterval hf u.val hrange
  let A : DerivLp n 2 Ω := (P.classicalLoad_regular hopen hbounded hz2).toLp hopen hbounded 2
  have hbase : wkpBaseCoordinateCLM (hz2.toWkpSpaceOn hopen hbounded 2) = baseCoordCLM u :=
    Lp.ext ((hz2.toWkpSpaceOn_base_ae hopen hbounded 2).trans hzae)
  have hload : A = wkpBaseCoordinateCLM F := by
    apply (h10L2GelfandTriple hopen).pivotToDual_injective
    ext v
    change ⟪A, baseCoordCLM v⟫_ℝ = ⟪wkpBaseCoordinateCLM F, baseCoordCLM v⟫_ℝ
    have hform := P.form_eq_load hopen hbounded 0
      (hz2.toWkpSpaceOn hopen hbounded 2) u v hbase
    rw [P.load_toWkpSpaceOn hopen hbounded hz2,
      ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] at hform
    rw [← hform, hu v, inner_base_eq_integral]
    exact integral_congr_ae (hF.symm.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx)
  have heq : P.classicalLoad z =ᵐ[domainMeasure n Ω] fun x ↦ f (z x) := by
    have hA := (P.classicalLoad_regular hopen hbounded hz2).toLp_coeFn hopen hbounded 2
    change (A : ℝ^n → ℝ) =ᵐ[_] _ at hA
    rw [hload] at hA
    filter_upwards [hA, hF, hzae] with x ha hf hz
    exact ha.symm.trans (hf.trans (congrArg f hz.symm))
  refine ⟨z, hz, hzae, hzboundary, hzrange, ?_⟩
  exact Measure.eqOn_open_of_ae_eq heq hopen
    (P.classicalLoad_regular hopen hbounded hz2).contDiffOn.continuousOn
    (hf.continuousOn.comp hzcont fun x hx ↦ hinterval (hzrange x hx))

variable {m : ℕ} {D : Set ℝ^(m + 1)}

/-- Smooth geometry and coefficients, and a reaction smooth near the bounded
barrier range, give a classical zero-boundary solution between ordered H¹
subsolutions and supersolutions with signed traces. No regularity of a sought
solution is assumed. The result holds in every positive spatial dimension. -/
theorem exists_classical_solution_between_H1_barriers_of_contDiffOn
    (hopen : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hgraph : ∀ k : ℕ, HasContDiffGraphBoundary k D)
    (a : ℝ^(m + 1) → Fin (m + 1) → Fin (m + 1) → ℝ)
    (b : Fin (m + 1) → ℝ^(m + 1) → ℝ) (c : ℝ^(m + 1) → ℝ)
    (ha : ∀ k i j, ContDiffUpToBoundary k (fun x ↦ a x i j) D)
    (hb : ∀ k i, ContDiffUpToBoundary k (b i) D)
    (hc : ∀ k, ContDiffUpToBoundary k c D)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ D, MatrixEllipticLowerBound (a x) alpha)
    (f : ℝ → ℝ) {left right : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hinterval : Icc left right ⊆ s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (lower upper : H¹(D))
    (htraceLower :
      let := ((hgraph 3).hasC1GraphBoundary (by decide)).c1ExtensionAtlas hopen hbounded
      ∀ᵐ x ∂surfaceMeasure D, Trace.C1.trace lower x ≤ 0)
    (htraceUpper :
      let := ((hgraph 3).hasC1GraphBoundary (by decide)).c1ExtensionAtlas hopen hbounded
      ∀ᵐ x ∂surfaceMeasure D, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂domainMeasure (m + 1) D,
      wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hleft : ∀ᵐ x ∂domainMeasure (m + 1) D, left ≤ wkpBaseCoordinateCLM lower x)
    (hright : ∀ᵐ x ∂domainMeasure (m + 1) D, wkpBaseCoordinateCLM upper x ≤ right)
    (hlower : ∀ v : H¹₀(D), (∀ᵐ x ∂domainMeasure (m + 1) D, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator
        (fun i j ↦ (ha 0 i j).toLp hopen hbounded ∞)
        (fun i ↦ (hb 0 i).toLp hopen hbounded ∞) ((hc 0).toLp hopen hbounded ∞) lower v ≤
          ∫ x, f (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x
            ∂domainMeasure (m + 1) D)
    (hupper : ∀ v : H¹₀(D), (∀ᵐ x ∂domainMeasure (m + 1) D, 0 ≤ baseCoordCLM v x) →
      (∫ x, f (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x
        ∂domainMeasure (m + 1) D) ≤
          interiorFullDivergenceOperator
            (fun i j ↦ (ha 0 i j).toLp hopen hbounded ∞)
            (fun i ↦ (hb 0 i).toLp hopen hbounded ∞)
            ((hc 0).toLp hopen hbounded ∞) upper v) :
    ∃ (u : H¹₀(D)) (z : ℝ^(m + 1) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) z (closure D) ∧
      z =ᵐ[domainMeasure (m + 1) D] (baseCoordCLM u : ℝ^(m + 1) → ℝ) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) D, wkpBaseCoordinateCLM lower x ≤ z x) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) D, z x ≤ wkpBaseCoordinateCLM upper x) ∧
      (∀ x ∈ frontier D, z x = 0) ∧
      (∀ x ∈ D, z x ∈ Icc left right) ∧
      ∀ x ∈ D,
        -(∑ i, ∑ j, (∂[i] (fun y ↦ a y i j * (∂[j] z) y)) x) +
          (∑ i, b i x * (∂[i] z) x) + c x * z x = f (z x) := by
  have hf1 : ContDiffOn ℝ 1 f (Icc left right) := (hf.of_le (by simp)).mono hinterval
  obtain ⟨u, _, _, hlu, huu, _, hu⟩ :=
    exists_h3_solution_between_H1_barriers_of_contDiffOn hopen hbounded (hgraph 3)
      a b c (ha 2) (hb 2) (hc 2) halpha hell f hf1 lower upper
      htraceLower htraceUpper hlr hleft hright
      (by simpa only [ContDiffUpToBoundary.toLp] using hlower)
      (by simpa only [ContDiffUpToBoundary.toLp] using hupper)
  let P : SmoothFullCoefficients (m + 1) D := ⟨a, b, c, ha, hb, hc⟩
  have hrange : ∀ᵐ x ∂domainMeasure (m + 1) D, baseCoordCLM u x ∈ Icc left right := by
    filter_upwards [hleft, hlu, huu, hright] with x hl hlu huu hr
    exact ⟨hl.trans hlu, huu.trans hr⟩
  have huP (v : H¹₀(D)) : P.form hopen hbounded u v =
      ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂domainMeasure (m + 1) D := by
    have heq := hu v
    rw [interiorFullDivergenceOperator_coe_H10] at heq
    simpa only [P, SmoothFullCoefficients.form, fullDivergenceForm_apply,
      multiplicationFirstOrderOperator_apply, multiplicationZeroOrderOperator_apply,
      mulLpLeft_apply, ContDiffUpToBoundary.toLp] using heq
  obtain ⟨z, hz, hzae, hboundary, hzrange, heq⟩ :=
    exists_classicalRepresentative_of_bounded_semilinear_solution
      hopen hbounded hgraph P halpha hell hs hinterval hf u hrange huP
  exact ⟨u, z, hz, hzae, hlu.mp (hzae.mono fun x hz hx ↦ hz ▸ hx),
    huu.mp (hzae.mono fun x hz hx ↦ hz ▸ hx), hboundary, hzrange, heq⟩

end PDE.Elliptic.Semilinear

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Higher
public import PDE.Elliptic.Regularity.Boundary.GeometricAtlas
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
import PDE.Spaces.Sobolev.Extension.C1.Classical

/-!
# Improved parabolic regularity from classical boundary data

We prove both parts of Evans's §7.1.3, Theorem 5 (Improved regularity), for a bounded open
domain with a `C²` graph boundary and symmetric principal coefficients that are `C¹` up to
the boundary. The drift and potential need only be continuous up to the boundary; Evans
assumes a smooth boundary and, in (45), smooth coefficients independent of `t`. The boundary
atlas and the coefficient extensions are built in the proofs, so neither is a hypothesis.

## Main results

* `exists_improved_regularity_of_contDiffUpToBoundary`: Theorem 5(i).
* `exists_higher_regularity_of_contDiffUpToBoundary`: Theorem 5(ii).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, (45), p. 381, and Theorem 5 (Improved regularity),
  (46)-(47), p. 382.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

private theorem exists_classical_principal_realization
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (alpha : ℝ)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ (_ : C2BoundaryAtlas n Ω) (aext : ℝ^n → Fin n → Fin n → ℝ),
      (∀ i j, (wkpBaseCoordinateCLM ((ha i j).toWkpSpaceOn hopen hbounded ∞) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦ aext x i j) ∧
      (∀ i j, ContDiff ℝ 1 (fun x ↦ aext x i j)) ∧
      (∀ x ∈ Ω, ∀ i j, aext x i j = aext x j i) ∧
      (∀ x ∈ Ω, MatrixEllipticLowerBound (aext x) alpha) := by
  classical
  have hatlas := hgraph.exists_c2BoundaryAtlas le_rfl hopen hbounded
  obtain ⟨atlas, _, _⟩ := hatlas
  have hC1 := hgraph.hasC1GraphBoundary (by norm_num)
  choose g hg _ hga using fun i j ↦
    (ha i j).exists_contDiff_one_extension hopen hbounded hC1
  let aext : ℝ^n → Fin n → Fin n → ℝ := fun x i j ↦ g i j x
  have heq (x : ℝ^n) (hx : x ∈ Ω) : aext x = a x := by
    funext i j
    exact hga i j hx
  refine ⟨atlas, aext, ?_, hg, ?_, ?_⟩
  · intro i j
    filter_upwards [(ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞,
      ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact hx.trans (hga i j hxΩ).symm
  · intro x hx i j
    rw [heq x hx]
    exact haSymm x hx i j
  · intro x hx
    rw [heq x hx]
    exact hElliptic x hx

/-- Every weak solution of the full classical autonomous equation has the
first improved estimate. The hypotheses are only the boundary geometry and
classical coefficients, and the constant is chosen before the solution data. -/
theorem exists_improved_regularity_of_contDiffUpToBoundary
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (hb : ∀ i, ContDiffUpToBoundary 0 (b i) Ω)
    (hc : ContDiffUpToBoundary 0 c Ω)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (g : H¹₀(Ω))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
          (fun _ ↦ fullDivergenceForm
            (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hopen hbounded ∞))
            (fun i ↦ mulLpLeft ((hb i).toLp hopen hbounded ∞))
            (mulLpLeft (hc.toLp hopen hbounded ∞)))
          ((h10L2GelfandTriple hopen).pivotToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ∃ (ut : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (U₂ : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
          ((h10L2GelfandTriple hopen).pivotToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) ut) ∧
        (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
          lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2) (by omega) (U₂ t) =
            h10SubtypeL (n := n) (Ω := Ω) (u t)) ∧
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
        (eLpNormEssSup (fun t ↦ u t) (volume.restrict (Ioc t₀ t₁))).toReal +
          ‖U₂‖ + ‖ut‖ ≤ K * (‖g‖ + ‖f‖) := by
  let A : Fin n → Fin n → W^{1,∞}(Ω) :=
    fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
  let R := lowerOrderOperator (fun i ↦ mulLpLeft ((hb i).toLp hopen hbounded ∞))
    (mulLpLeft (hc.toLp hopen hbounded ∞))
  have hreal := exists_classical_principal_realization hopen hbounded hgraph a ha
    haSymm alpha hElliptic
  obtain ⟨atlas, aext, hrep, hext, hsymm, hell⟩ := hreal
  have hcoeff : coefficientBase A = fun i j ↦ (ha i j).toLp hopen hbounded ∞ := by
    funext i j
    exact (ha i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
  have hform : fullDivergenceForm
      (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hopen hbounded ∞))
      (fun i ↦ mulLpLeft ((hb i).toLp hopen hbounded ∞))
      (mulLpLeft (hc.toLp hopen hbounded ∞)) =
      autonomousDivergenceFormOperator A +
        (h10L2GelfandTriple hopen).pivotToDual.comp R := by
    rw [fullDivergenceForm_eq_principal_add_pivot_comp hopen]
    simp only [autonomousDivergenceFormOperator, hcoeff, R]
  have hreg := exists_full_form_improved_regularity ht atlas A aext hrep hext
    hsymm alpha halpha hell R
  obtain ⟨K, hK, hreg⟩ := hreg
  refine ⟨K, hK, ?_⟩
  intro f g u hu
  rw [hform] at hu
  exact hreg f g u hu

/-- With an `H² ∩ H¹₀` initial datum and forcing with an `L²` weak time
derivative, every weak solution has both time derivatives and the full
second improved sum estimate for the classical autonomous operator. -/
theorem exists_higher_regularity_of_contDiffUpToBoundary
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (hb : ∀ i, ContDiffUpToBoundary 0 (b i) Ω)
    (hc : ContDiffUpToBoundary 0 c Ω)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f df : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc t₀ t₁)))
        (g : H¹₀(Ω)) (G : W^{2,2}(Ω))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
      lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2)
        (by omega) G = h10SubtypeL (n := n) (Ω := Ω) g →
      HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Ioc t₀ t₁)) df) →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ fullDivergenceForm
            (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hopen hbounded ∞))
            (fun i ↦ mulLpLeft ((hb i).toLp hopen hbounded ∞))
            (mulLpLeft (hc.toLp hopen hbounded ∞)))
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc t₀ t₁)) f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ∃ (v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc t₀ t₁)))
        (dv : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc t₀ t₁)))
        (U₂ : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc t₀ t₁))),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
          ((h10L2GelfandTriple hopen).energyToDual.compLpL
            2 (volume.restrict (Ioc t₀ t₁)) v) ∧
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen)
          v dv ∧
        (∀ᵐ t ∂volume.restrict (Ioc t₀ t₁),
          lowerOrderCLM (n := n) (Ω := Ω) (p := 2) (k := 1) (m := 2)
            (by omega) (U₂ t) = h10SubtypeL (n := n) (Ω := Ω) (u t)) ∧
        MemLp (fun t ↦ U₂ t) ∞ (volume.restrict (Ioc t₀ t₁)) ∧
        MemLp (fun t ↦ baseCoordCLM (n := n) (Ω := Ω) (v t)) ∞
          (volume.restrict (Ioc t₀ t₁)) ∧
        (eLpNormEssSup (fun t ↦ U₂ t) (volume.restrict (Ioc t₀ t₁))).toReal +
          (eLpNormEssSup (fun t ↦ baseCoordCLM (n := n) (Ω := Ω) (v t))
            (volume.restrict (Ioc t₀ t₁))).toReal + ‖v‖ + ‖dv‖ ≤
          K * (‖G‖ + Real.sqrt (‖f‖ ^ 2 + ‖df‖ ^ 2)) := by
  let A : Fin n → Fin n → W^{1,∞}(Ω) :=
    fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
  let R := lowerOrderOperator (fun i ↦ mulLpLeft ((hb i).toLp hopen hbounded ∞))
    (mulLpLeft (hc.toLp hopen hbounded ∞))
  have hreal := exists_classical_principal_realization hopen hbounded hgraph a ha
    haSymm alpha hElliptic
  obtain ⟨atlas, aext, hrep, hext, hsymm, hell⟩ := hreal
  have hcoeff : coefficientBase A = fun i j ↦ (ha i j).toLp hopen hbounded ∞ := by
    funext i j
    exact (ha i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
  have hform : fullDivergenceForm
      (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hopen hbounded ∞))
      (fun i ↦ mulLpLeft ((hb i).toLp hopen hbounded ∞))
      (mulLpLeft (hc.toLp hopen hbounded ∞)) =
      autonomousDivergenceFormOperator A +
        (h10L2GelfandTriple hopen).pivotToDual.comp R := by
    rw [fullDivergenceForm_eq_principal_add_pivot_comp hopen]
    simp only [autonomousDivergenceFormOperator, hcoeff, R]
  have hreg := exists_full_form_higher_regularity ht atlas A aext hrep hext
    hsymm alpha halpha hell R
  obtain ⟨K, hK, hreg⟩ := hreg
  refine ⟨K, hK, ?_⟩
  intro f df g G u hG hf hu
  rw [hform] at hu
  exact hreg f df g G u hG hf hu

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

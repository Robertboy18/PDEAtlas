/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Uniqueness
public import PDE.Examples.CalculusOfVariations.Systems.SignedEnergy

/-!
# Unique minimizers of a coupled value and matrix energy

The density `‖P‖² + trace(P)² - 2 + (s₀ + P₀₁)²` couples diagonal gradient
entries and also couples a value with an off-diagonal entry. Its zero-trace
class has exactly one signed-energy minimizer.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.CalculusOfVariations
open scoped ENNReal NNReal Matrix.Norms.Frobenius Sobolev

namespace PDE.Examples.VariationalSystems

/-- A value component coupled to an off-diagonal derivative. -/
def valueMatrixCoupling : ℝ^2 × Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ where
  toFun z := z.1 0 + z.2 0 1
  map_add' _ _ := by simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply,
    Matrix.add_apply]; abel
  map_smul' a z := by
    change a * z.1 0 + a * z.2 0 1 = a * (z.1 0 + z.2 0 1)
    exact (mul_add _ _ _).symm

/-- The coupled matrix density from `SignedEnergy`, plus a value-gradient coupling. -/
def valueCoupledDensity (t : (ℝ^2 × ℝ^2) × Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  coupledDensity t + valueMatrixCoupling (t.1.2, t.2) ^ 2

/-- The coupled value-gradient density is continuously differentiable. -/
theorem valueCoupledDensity_contDiff : ContDiff ℝ 1 valueCoupledDensity :=
  coupledDensity_contDiff.add
    ((valueMatrixCoupling.toContinuousLinearMap.contDiff.comp
      (contDiff_fst.snd.prodMk contDiff_snd)).pow 2)

/-- The square of the mixed linear coordinate is jointly convex. -/
theorem valueMatrixCoupling_sq_convex :
    ConvexOn ℝ univ (fun z ↦ valueMatrixCoupling z ^ 2) := by
  simpa only [Function.comp_def, preimage_univ] using
    (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 from ⟨1, rfl⟩)).comp_linearMap
      valueMatrixCoupling

/-- The value-dependent density is convex in the value and entire matrix together. -/
theorem valueCoupledDensity_convex (x : ℝ^2) :
    ConvexOn ℝ univ (fun z : ℝ^2 × Matrix (Fin 2) (Fin 2) ℝ ↦
      valueCoupledDensity ((x, z.1), z.2)) := by
  have hbase : ConvexOn ℝ univ (fun z : ℝ^2 × Matrix (Fin 2) (Fin 2) ℝ ↦
      coupledDensity ((x, z.1), z.2)) := by
    refine ⟨convex_univ, fun z _ w _ a b ha hb hab ↦ ?_⟩
    exact (coupledDensity_convex x 0).2 (mem_univ z.2) (mem_univ w.2) ha hb hab
  exact hbase.add valueMatrixCoupling_sq_convex

/-- The density is strictly midpoint convex in `(s, P)` along pairs with distinct matrices. -/
theorem valueCoupledDensity_strict_midpoint (x : ℝ^2)
    (z w : ℝ^2 × Matrix (Fin 2) (Fin 2) ℝ) (hne : z.2 ≠ w.2) :
    valueCoupledDensity ((x, (2 : ℝ)⁻¹ • z.1 + (2 : ℝ)⁻¹ • w.1),
      (2 : ℝ)⁻¹ • z.2 + (2 : ℝ)⁻¹ • w.2) <
      (valueCoupledDensity ((x, z.1), z.2) +
        valueCoupledDensity ((x, w.1), w.2)) / 2 := by
  have hn : StrongConvexOn univ 2 (fun P : ℝ^(2 * 2) ↦ ‖P‖ ^ 2) := by
    rw [strongConvexOn_iff_convex]
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul, sub_self] using
      (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set (ℝ^(2 * 2)))))
  have hnorm := (hn.strictConvexOn (by norm_num)).2
    (mem_univ (Matrix.euclideanEquiv z.2)) (mem_univ (Matrix.euclideanEquiv w.2))
    (Matrix.euclideanEquiv.injective.ne hne)
    (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num)
  have ht : ConvexOn ℝ univ
      (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ Matrix.trace P ^ 2) := by
    simpa only [Function.comp_def, preimage_univ, Matrix.traceLinearMap_apply] using
      (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 from ⟨1, rfl⟩)).comp_linearMap
        (Matrix.traceLinearMap (Fin 2) ℝ ℝ)
  have htrace := ht.2 (mem_univ z.2) (mem_univ w.2)
    (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num)
  have hv := valueMatrixCoupling_sq_convex.2 (mem_univ z) (mem_univ w)
    (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num)
  change valueMatrixCoupling
    ((2 : ℝ)⁻¹ • z.1 + (2 : ℝ)⁻¹ • w.1,
      (2 : ℝ)⁻¹ • z.2 + (2 : ℝ)⁻¹ • w.2) ^ 2 ≤ _ at hv
  simp only [valueCoupledDensity, coupledDensity, map_add, map_smul]
  simp only [smul_eq_mul] at hnorm htrace hv
  linarith

/-- The signed energy of `valueCoupledDensity` has exactly one minimizer among maps with
zero trace. -/
theorem valueCoupled_zero_trace_unique_minimizer {Ω : Set (ℝ^2)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) :
    letI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
    letI : Boundary.C1ExtensionAtlas 2 Ω := hgraph.c1ExtensionAtlas hopen hbounded
    let A := {u : Fin 2 → W^{1,ENNReal.ofReal 2}(Ω) |
      Trace.C1.vectorTraceLp 2 u = 0}
    let I := vectorWkpIntegral
      (fun x z ↦ valueCoupledDensity ((x, z.1), Matrix.euclideanEquiv.symm z.2))
    ∃! u, u ∈ A ∧ IsMinOn I A u := by
  let : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  let : Boundary.C1ExtensionAtlas 2 Ω := hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  refine existsUnique_minimizer_matrixWkpIntegral_of_finite_competitor
    hopen hbounded hgraph (by norm_num : (1 : ℝ) < 2)
    valueCoupledDensity_contDiff.contDiffOn
    (fun x _ ↦ valueCoupledDensity_convex x)
    (fun x _ z w ↦ valueCoupledDensity_strict_midpoint x z w)
    (β := 2) (by norm_num : (0 : ℝ) < 1) ?_ 0 ?_
  · intro x _ s P
    simp only [valueCoupledDensity, coupledDensity, Matrix.norm_euclideanEquiv,
      one_mul, Real.rpow_two]
    linarith [sq_nonneg (Matrix.trace P), sq_nonneg (valueMatrixCoupling (s, P))]
  · refine ⟨0, map_zero _, ?_⟩
    have hi : Integrable
        (fun x ↦ valueCoupledDensity
          ((x, vectorWkpValueCLM (0 : Fin 2 → W^{1,ENNReal.ofReal 2}(Ω)) x),
            Matrix.euclideanEquiv.symm (∇
              (0 : Fin 2 → W^{1,ENNReal.ofReal 2}(Ω)) x)))
        (domainMeasure 2 Ω) := by
      apply (integrable_const (-2 : ℝ)).congr
      filter_upwards [Lp.coeFn_zero (ℝ^2) (ENNReal.ofReal 2) (domainMeasure 2 Ω),
        Lp.coeFn_zero (ℝ^(2 * 2)) (ENNReal.ofReal 2) (domainMeasure 2 Ω)] with x hv hg
      simp only [map_zero, hv, hg, Pi.zero_apply, valueCoupledDensity, coupledDensity,
        norm_zero, zero_pow (by decide : 2 ≠ 0), Matrix.trace_zero, zero_add, zero_sub,
        valueMatrixCoupling]
      norm_num
    rw [vectorWkpIntegral_eq_integral hi]
    exact EReal.coe_ne_top _

end PDE.Examples.VariationalSystems

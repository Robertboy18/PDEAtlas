/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.TestedTraces
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Spaces
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianTest

/-!
# Energy-space identities from compact spatial tests

Whole-space density and the weak Green identity identify the vector equations
of a finite-speed trajectory from its compact spatial tests.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open PDE SobolevSpace SobolevSpace.GraphSpace
open scoped Topology ENNReal Sobolev Laplacian InnerProductSpace
open scoped SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Compact smooth spatial pairings determine a whole-space L² class. -/
theorem eq_of_inner_testFunction_eq {a b : DerivLp 3 2 univ}
    (h : ∀ φ : TestFunctionOn 3 univ, ⟪a, (energyTriple 3).inclusion (testFunctionToH1 φ)⟫_ℝ = ⟪b,
      (energyTriple 3).inclusion (testFunctionToH1 φ)⟫_ℝ) :
    a = b := by
  let test : TestFunctionOn 3 univ → DerivLp 3 2 univ := fun φ ↦ baseCoordCLM (testFunctionToH10 φ)
  have hd : DenseRange test :=
    (baseCoordCLM_denseRange isOpen_univ).comp denseRange_testFunctionToH10Linear
      (baseCoordCLM (n := 3) (Ω := univ)).continuous
  apply ext_inner_right ℝ
  exact congr_fun (hd.equalizer (continuous_const.inner continuous_id)
    (continuous_const.inner continuous_id) (funext h))

/-- Compact smooth tests determine a continuous functional on the full
whole-space H¹ space. -/
theorem dual_eq_of_testFunction_eq {a b : StrongDual ℝ H¹(ℝ^3)}
    (h : ∀ φ : TestFunctionOn 3 univ, a (testFunctionToH1 φ) = b (testFunctionToH1 φ)) :
    a = b := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  obtain ⟨f, hf, hc, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier 3) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) 1 v
  rw [← tendsto_iff_norm_sub_tendsto_zero] at hlim
  let φ (j : ℕ) : TestFunctionOn 3 univ := ⟨⟨f j, hf j, hc j, subset_univ _⟩, subset_univ _⟩
  have hlim' : Tendsto (fun j ↦ testFunctionToH1 (φ j)) atTop (𝓝 v) := hlim
  exact (isClosed_eq a.continuous b.continuous).mem_of_tendsto hlim'
    (Eventually.of_forall fun j ↦ h (φ j))

/-- An almost-everywhere representative computes the L² pairing with a
compact spatial test. -/
theorem inner_testFunction_eq_integral_of_ae {v : DerivLp 3 2 univ} {f : ℝ^3 → ℝ}
    (hv : (v : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] f) (φ : TestFunctionOn 3 univ) :
    ⟪v, (energyTriple 3).inclusion (testFunctionToH1 φ)⟫_ℝ = ∫ x : ℝ^3, f x * φ.1.toFun x := by
  change ⟪v, baseCoordCLM (testFunctionToH10 φ)⟫_ℝ = _
  rw [inner_base_testFunction_eq_integral]
  have he : (∫ x : ℝ^3, (v : ℝ^3 → ℝ) x * φ.1.toFun x ∂domainMeasure 3 univ) =
      ∫ x : ℝ^3, f x * φ.1.toFun x ∂domainMeasure 3 univ :=
    integral_congr_ae (hv.fun_mul (Eventually.of_forall fun _ ↦ rfl))
  simpa only [domainMeasure, Measure.restrict_univ] using he

/-- The weak spatial energy operator tested against a compact smooth function
is the negative integral against its ordinary Laplacian. -/
theorem gradientForm_testFunction_eq_integral_of_ae {q : H¹(ℝ^3)} {f : ℝ^3 → ℝ}
    (hq : ((energyTriple 3).inclusion q : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] f)
    (φ : TestFunctionOn 3 univ) :
    gradientForm 3 q (testFunctionToH1 φ) = -(∫ x : ℝ^3, f x * laplacian φ.1.toFun x) := by
  rw [gradientForm_apply]
  change (∑ i : Fin 3, ⟪q.val (singleDerivIndex 3 i), derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ) = _
  rw [sum_inner_deriv_test_eq_neg_integral_laplacian]
  congr 1
  have he : (∫ x, baseRepresentative q x * laplacian φ.1.toFun x ∂domainMeasure 3 univ) =
      ∫ x, f x * laplacian φ.1.toFun x ∂domainMeasure 3 univ :=
    integral_congr_ae (hq.fun_mul (Eventually.of_forall fun _ ↦ rfl))
  simpa only [domainMeasure, Measure.restrict_univ] using he

/-- Continuous energy representatives of a C¹ trajectory satisfying the
positive-time tested equation satisfy both vector integral equations. The
acceleration takes values in the full H¹ dual and the force is the
negative signed power. -/
theorem energy_integral_primitives_of_signedPower_tested_equation {r b L S : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) (hS : 0 ≤ S) (hSL : S < L) {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (hwave : ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 L,
      HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
      ((∫ x : ℝ^3, u (t, x) * laplacian φ x) - ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t)
    {q : ℝ → H¹(ℝ^3)} {v F : ℝ → DerivLp 3 2 univ} (hq : Continuous q) (hv : Continuous v)
    (hF : Continuous F)
    (hqae : ∀ t ∈ Icc 0 S, ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun
      x ↦ u (t, x))
    (hvae : ∀ t ∈ Icc 0 S, (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun x ↦
      fderiv ℝ u (t, x) (1, 0))
    (hFae : ∀ t ∈ Icc 0 S, (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun x ↦
      -Real.signedPower r (u (t, x))) :
    ∀ t ∈ Icc 0 S,
      (∫ s in 0..t, v s) = (energyTriple 3).inclusion (q t) -
        (energyTriple 3).inclusion (q 0) ∧
      (∫ s in 0..t, (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s)) =
        (energyTriple 3).pivotToDual (v t) - (energyTriple 3).pivotToDual (v 0) := by
  have hzero : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
  have hvel (x : ℝ^3) : HasDerivAt (fun t ↦ u (t, x))
      (fderiv ℝ u (0, x) (1, 0)) 0 := by
    have hO : IsOpen {p : ℝ × ℝ^3 | -b < p.1 ∧ p.1 < L} :=
      (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
    exact ((hu.contDiffAt (hO.mem_nhds ⟨by linarith, hS.trans_lt hSL⟩)).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
  have hscalar (φ : TestFunctionOn 3 univ) :=
    integral_primitives_of_signedPower_tested_equation hr hb hS hSL hu
      (fun _ ↦ rfl) hvel (φ.1.contDiff.of_le (by norm_num)) φ.1.hasCompactSupport
      (hwave φ.1.toFun (φ.1.contDiff.of_le (by norm_num)) φ.1.hasCompactSupport)
  simp only [← TestFunction.toFun_eq_coe] at hscalar
  have hpairq (s : ℝ) (hs : s ∈ Icc 0 S) (φ : TestFunctionOn 3 univ) :=
    inner_testFunction_eq_integral_of_ae (hqae s hs) φ
  have hpairv (s : ℝ) (hs : s ∈ Icc 0 S) (φ : TestFunctionOn 3 univ) :=
    inner_testFunction_eq_integral_of_ae (hvae s hs) φ
  have hacc : Continuous (fun s ↦ (energyTriple 3).pivotToDual (F s) - gradientForm 3 (q s)) :=
    ((energyTriple 3).pivotToDual.continuous.comp hF).sub ((gradientForm 3).continuous.comp hq)
  intro t ht
  have hmem (s : ℝ) (hs : s ∈ uIcc 0 t) : s ∈ Icc 0 S := by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  constructor
  · refine eq_of_inner_testFunction_eq fun φ ↦ ?_
    have hcomm : ⟪(∫ s in 0..t, v s), (energyTriple 3).inclusion (testFunctionToH1 φ)⟫_ℝ =
          ∫ s in 0..t, ⟪v s, (energyTriple 3).inclusion (testFunctionToH1 φ)⟫_ℝ := by
      calc
        _ = ⟪(energyTriple 3).inclusion (testFunctionToH1 φ), ∫ s in 0..t, v s⟫_ℝ :=
          real_inner_comm _ _
        _ = ∫ s in 0..t, ⟪(energyTriple 3).inclusion (testFunctionToH1 φ), v s⟫_ℝ :=
          ((innerSL ℝ ((energyTriple 3).inclusion (testFunctionToH1 φ))).intervalIntegral_comp_comm
            (hv.intervalIntegrable 0 t)).symm
        _ = _ := intervalIntegral.integral_congr fun s _ ↦ real_inner_comm _ _
    rw [hcomm, inner_sub_left, hpairq t ht, hpairq 0 hzero, ← (hscalar φ).2.2.1 t ht]
    exact intervalIntegral.integral_congr fun s hs ↦ hpairv s (hmem s hs) φ
  · refine dual_eq_of_testFunction_eq fun φ ↦ ?_
    rw [ContinuousLinearMap.intervalIntegral_apply (hacc.intervalIntegrable 0 t)]
    simp only [sub_apply, PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply]
    rw [hpairv t ht, hpairv 0 hzero, ← (hscalar φ).2.2.2 t ht]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    have hfpair := inner_testFunction_eq_integral_of_ae (hFae s (hmem s hs)) φ
    simp only [neg_mul, integral_neg] at hfpair
    rw [hfpair, gradientForm_testFunction_eq_integral_of_ae (hqae s (hmem s hs)) φ]
    abel

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

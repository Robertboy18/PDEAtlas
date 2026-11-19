/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Reflexivity
public import PDE.Analysis.WeakCompactness.Identification
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import PDE.Common.Euclidean

/-!
# Weak `Lᵖ` convergence from smooth test integrals

For `1 < p < ∞`, a bounded family of real `Lᵖ` functions on an open Euclidean
set converges weakly when all its compactly supported smooth test integrals
converge to those of the proposed limit. Reflexivity supplies compactness;
the fundamental lemma for distributions separates the cluster points.

The convergence holds along the original filter, and the open set is arbitrary.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Distributions

namespace MeasureTheory.Lp

variable {n : ℕ} (Ω : Opens (ℝ^n))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μΩ" => Measure.restrict
  (volume : Measure (ℝ^n)) (Ω : Set (ℝ^n))

/-- Integration against a smooth test function is a continuous linear functional on
`Lᵖ`. The construction uses the Hölder pairing with its conjugate exponent. -/
def testFunctionPairing (φ : 𝓓(Ω, ℝ)) : StrongDual ℝ (Lp ℝ p μΩ) :=
  letI : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μΩ p (ENNReal.conjExponent p)).flip
    ((φ.continuous.memLp_of_hasCompactSupport (μ := μΩ)
      (p := ENNReal.conjExponent p) φ.hasCompactSupport).toLp φ)

/-- The dual functional is the ordinary integral of the representatives. -/
theorem testFunctionPairing_apply (φ : 𝓓(Ω, ℝ)) (f : Lp ℝ p μΩ) :
    testFunctionPairing Ω φ f = ∫ x, f x * φ x ∂μΩ := by
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  unfold testFunctionPairing
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (φ.continuous.memLp_of_hasCompactSupport (μ := μΩ)
      (p := ENNReal.conjExponent p) φ.hasCompactSupport)] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

/-- Smooth tests supported inside the open set separate its `Lᵖ` elements. -/
theorem injective_testFunctionPairing :
    Function.Injective (fun f : Lp ℝ p μΩ ↦ fun φ : 𝓓(Ω, ℝ) ↦
      testFunctionPairing Ω φ f) := by
  intro f g hfg
  have hzero (φ : 𝓓(Ω, ℝ)) : ∫ x, (f - g) x * φ x ∂μΩ = 0 := by
    rw [← testFunctionPairing_apply, map_sub, sub_eq_zero]
    exact congrFun hfg φ
  have hlocal : LocallyIntegrableOn (fun x ↦ (f - g) x) Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (f - g)).locallyIntegrable (Fact.out : 1 ≤ p))
  have hae := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    (fun ψ hψ hcs hs ↦ by
      let φ : 𝓓(Ω, ℝ) :=
        ⟨ψ, hψ, hcs, hs⟩
      have hrestrict : (∫ x in (Ω : Set (ℝ^n)),
          ψ x * (f - g) x) = ∫ x, ψ x * (f - g) x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hxs ↦ hx (hs hxs))
        rw [hz, zero_mul]
      have hφ := hzero φ
      change (∫ x in (Ω : Set (ℝ^n)), (f - g) x * ψ x) = 0 at hφ
      simpa only [smul_eq_mul, ← hrestrict, mul_comm] using hφ)
  apply sub_eq_zero.mp
  apply Lp.ext
  filter_upwards [ae_restrict_iff' Ω.isOpen.measurableSet |>.mpr hae,
    Lp.coeFn_zero (E := ℝ) (p := p) (μ := μΩ)] with x hx hz
  exact hx.trans hz.symm

/-- A bounded family in reflexive `Lᵖ` converges weakly if all its smooth test integrals
converge. This retains the original filter, in particular the whole original sequence. -/
theorem tendsto_weak_of_test_integrals
    (hp : 1 < p) (hp_top : p ≠ ∞)
    {ι : Type*} {l : Filter ι} (f : ι → Lp ℝ p μΩ) (g : Lp ℝ p μΩ)
    (hbounded : Bornology.IsBounded (range f))
    (htest : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i ↦ ∫ x, f i x * φ x ∂μΩ) l (𝓝 (∫ x, g x * φ x ∂μΩ))) :
    Tendsto (fun i ↦ toWeakSpace ℝ (Lp ℝ p μΩ) (f i)) l
      (𝓝 (toWeakSpace ℝ (Lp ℝ p μΩ) g)) := by
  apply PDE.Analysis.WeakCompactness.tendsto_of_separating_functionals_of_reflexive
    (surjective_inclusionInDoubleDual hp hp_top) (testFunctionPairing Ω)
    (injective_testFunctionPairing Ω) f g hbounded
  intro φ
  simpa only [testFunctionPairing_apply] using htest φ

end MeasureTheory.Lp

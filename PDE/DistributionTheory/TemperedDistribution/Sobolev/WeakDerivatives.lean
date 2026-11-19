/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Complex
public import PDE.DistributionTheory.TemperedDistribution.IteratedDerivative
public import PDE.DistributionTheory.Schwartz.PartialDerivative
import PDE.Analysis.Distribution.Schwartz.Density
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Weak derivatives as tempered derivatives

An `L²` function and its proposed derivative define tempered distributions. Their
distributional derivative identity is exactly the usual weak identity against compact
smooth tests. Compact cutoffs are dense in Schwartz space, so passing to tempered
distributions imposes no extra condition at infinity.

Only the function and the specified derivative must belong to `L²`. In particular,
the theorem does not assume square-integrability of the intermediate derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace LineDeriv PDE
open scoped SchwartzMap Distributions

namespace SobolevSpace

/-- The arbitrary-order `L²` weak derivative is the corresponding tempered derivative.
The distribution pairing is complex-linear, with no conjugation of the test function. -/
theorem hasComplexWeakDerivativeOn_iff_temperedDerivative {n : ℕ}
    (α : List (Fin n)) (u v : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    HasComplexWeakDerivativeOn univ α u v ↔
      ∂^{fun j : Fin α.length ↦ EuclideanSpace.single (α.get j) (1 : ℝ)}
        (u : 𝓢'(ℝ^n, ℂ)) = (v : 𝓢'(ℝ^n, ℂ)) := by
  let m := fun j : Fin α.length ↦ EuclideanSpace.single (α.get j) (1 : ℝ)
  have hu : MemLp (u : ℝ^n → ℂ) 2 (domainMeasure n univ) := by
    simpa [domainMeasure] using Lp.memLp u
  have hv : MemLp (v : ℝ^n → ℂ) 2 (domainMeasure n univ) := by
    simpa [domainMeasure] using Lp.memLp v
  have hsign : (-1 : ℂ) ^ α.length * (-1 : ℂ) ^ α.length = 1 := by
    rw [← mul_pow]
    simp
  constructor
  · intro h
    have hcompact : Set.EqOn
        (fun φ : 𝓢(ℝ^n, ℂ) ↦ (∂^{m} (u : 𝓢'(ℝ^n, ℂ))) φ)
        (v : 𝓢'(ℝ^n, ℂ))
        {φ : 𝓢(ℝ^n, ℂ) | HasCompactSupport (φ : ℝ^n → ℂ)} := by
      intro φ hφ
      let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℂ) :=
        ⟨φ, φ.smooth ⊤, hφ, subset_univ _⟩
      have hp : (u : 𝓢'(ℝ^n, ℂ)) (∂^{m} φ) =
          (-1 : ℂ) ^ α.length * (v : 𝓢'(ℝ^n, ℂ)) φ := by
        rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
        have hd := SchwartzMap.coe_iteratedLineDerivOp α φ
        change ⇑(∂^{m} φ) = iteratedPartialDeriv α (φ : ℝ^n → ℂ) at hd
        simp_rw [hd]
        simpa [ψ, domainMeasure, smul_eq_mul, mul_comm] using
          h.integral_identity_complex hu hv ψ (subset_univ _)
      change (∂^{m} (u : 𝓢'(ℝ^n, ℂ))) φ = (v : 𝓢'(ℝ^n, ℂ)) φ
      rw [TemperedDistribution.iteratedLineDerivOp_apply_apply, hp]
      change (-1 : ℂ) ^ α.length *
        ((-1 : ℂ) ^ α.length * (v : 𝓢'(ℝ^n, ℂ)) φ) = _
      rw [← mul_assoc, hsign, one_mul]
    have heq := Continuous.ext_on SchwartzMap.dense_hasCompactSupport
      (∂^{m} (u : 𝓢'(ℝ^n, ℂ))).continuous (v : 𝓢'(ℝ^n, ℂ)).continuous hcompact
    ext φ
    exact congrFun heq φ
  · intro h
    apply (hasComplexWeakDerivativeOn_iff_integral_identity hu hv).2
    intro φ _
    let ψ : 𝓢(ℝ^n, ℂ) :=
      (φ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) (by simp)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp φ.contDiff)
    have hd : ⇑(∂^{m} ψ) = fun x ↦ ((iteratedPartialDeriv α φ.toFun x : ℝ) : ℂ) := by
      rw [SchwartzMap.coe_iteratedLineDerivOp]
      exact iteratedPartialDeriv_ofReal α φ.toFun
    have heq := congrArg (fun T : 𝓢'(ℝ^n, ℂ) ↦ T ψ) h
    rw [TemperedDistribution.iteratedLineDerivOp_apply_apply,
      Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at heq
    have heq' := congrArg (fun z : ℂ ↦ (-1 : ℂ) ^ α.length * z) heq
    simp only [smul_eq_mul, ← mul_assoc, hsign, one_mul] at heq'
    simp_rw [show (fun j : Fin α.length ↦ EuclideanSpace.single (α.get j) (1 : ℝ)) = m
      from rfl, hd] at heq'
    simpa [ψ, domainMeasure, mul_comm] using heq'

end SobolevSpace

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.PartialDeriv.Support
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Coordinate derivatives of Euclidean test functions

Mathlib's `𝓓^{k}(U, F)` bundles differentiability, compact support, and support inside the open
set `U`, and its calculus is `fderivCLM` and the derivative along a fixed vector. The weak
formulations in this library integrate the coordinate derivative `∂ᵢφ` against coefficients.
The lemmas below connect these coordinates to test functions:
`∂ᵢφ` is continuous (`continuous_partialDeriv`), compactly supported, integrable, and zero
off `tsupport φ`, and `integrable_partialDeriv_smul` pairs it with any `LocallyIntegrableOn`
coefficient. That last lemma is vector-valued so that scalar and system conservation laws share
one statement.

The one construction, `mulLeft`, multiplies `φ` by a coefficient `a` that is `C¹` only on
`tsupport φ` (hypothesis `ha`). This is the most that
`integrable_mul_partialDeriv_of_contDiffAt` can use, since its `g` is `C¹` on `U` and
unknown outside.
-/

@[expose] public section

open PDE (partialDeriv)

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace TestFunction

variable {n : ℕ} {U : Opens (ℝ^n)}

/-- Multiply a `C¹` test function by a scalar coefficient that is `C¹` on its
topological support.

No regularity is required away from the support: there the product is locally
zero. The product has support in the same open set as the original test
function. -/
def mulLeft
    (a : ℝ^n → ℝ) (φ : 𝓓^{1}(U, ℝ))
    (ha : ∀ x ∈ tsupport (φ : ℝ^n → ℝ), ContDiffAt ℝ 1 a x) :
    𝓓^{1}(U, ℝ) where
  toFun x := a x * φ x
  contDiff' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (φ : ℝ^n → ℝ)
    · exact (ha x hx).mul φ.contDiff.contDiffAt
    · have hφ :
          (φ : ℝ^n → ℝ) =ᶠ[𝓝 x] (0 : ℝ^n → ℝ) :=
        (notMem_tsupport_iff_eventuallyEq).1 hx
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hφ] with y hy
      have hφy : φ y = (0 : ℝ) := by
        simpa using hy
      simp [hφy]
  hasCompactSupport' := by
    simpa [Pi.mul_def] using φ.hasCompactSupport.mul_left (f := a)
  tsupport_subset' :=
    (tsupport_mul_subset_right : tsupport (fun x ↦ a x * φ x) ⊆ tsupport φ).trans
      φ.tsupport_subset

/-- Pointwise formula for the product test function: `(a · φ)(x) = a x * φ x`. -/
@[simp]
theorem mulLeft_apply
    (a : ℝ^n → ℝ) (φ : 𝓓^{1}(U, ℝ))
    (ha : ∀ x ∈ tsupport (φ : ℝ^n → ℝ), ContDiffAt ℝ 1 a x)
    (x : ℝ^n) :
    mulLeft a φ ha x = a x * φ x :=
  rfl

/-- Product rule for a support-local coefficient multiplied by a test
function. -/
theorem partialDeriv_mulLeft
    (a : ℝ^n → ℝ) (φ : 𝓓^{1}(U, ℝ))
    (ha : ∀ x ∈ tsupport (φ : ℝ^n → ℝ), ContDiffAt ℝ 1 a x)
    {x : ℝ^n} (i : Fin n) (hax : DifferentiableAt ℝ a x) :
    (∂[i] (mulLeft a φ ha : ℝ^n → ℝ)) x =
      a x * (∂[i] (φ : ℝ^n → ℝ)) x +
        φ x * (∂[i] a) x := by
  have hφx : DifferentiableAt ℝ (φ : ℝ^n → ℝ) x :=
    φ.contDiff.differentiable_one x
  simpa [mulLeft, mul_comm, add_comm] using
    (PDE.partialDeriv_mul (i := i) hax hφx)

/-- A coordinate derivative of a `C¹` test function is continuous. -/
theorem continuous_partialDeriv (φ : 𝓓^{1}(U, ℝ)) (i : Fin n) :
    Continuous (fun x : ℝ^n ↦ (∂[i] ⇑φ) x) := by
  have hcontinuous :
      Continuous fun p : ℝ^n × ℝ^n ↦
        (fderiv ℝ φ p.1 : ℝ^n →L[ℝ] ℝ) p.2 :=
    φ.contDiff.continuous_fderiv_apply (hn := by norm_num)
  exact hcontinuous.comp (continuous_id.prodMk continuous_const)

/-- A coordinate derivative of a `C¹` test function has compact support. -/
theorem hasCompactSupport_partialDeriv (φ : 𝓓^{1}(U, ℝ)) (i : Fin n) :
    HasCompactSupport (fun x : ℝ^n ↦ (∂[i] ⇑φ) x) :=
  φ.hasCompactSupport.partialDeriv i

/-- A coordinate derivative of a `C¹` test function is integrable. -/
theorem integrable_partialDeriv (φ : 𝓓^{1}(U, ℝ)) (i : Fin n) :
    Integrable (fun x : ℝ^n ↦ (∂[i] ⇑φ) x) volume :=
  (φ.continuous_partialDeriv i).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_partialDeriv i)

/-- A coordinate derivative vanishes outside the topological support of the test function. -/
theorem partialDeriv_eq_zero_of_notMem_tsupport
    (φ : 𝓓^{1}(U, ℝ)) {x : ℝ^n}
    (hx : x ∉ tsupport (φ : ℝ^n → ℝ)) (i : Fin n) :
    (∂[i] ⇑φ) x = 0 :=
  PDE.partialDeriv_eq_zero_of_notMem_tsupport i hx

/-- A coordinate derivative vanishes outside the open support domain of the test function. -/
theorem partialDeriv_eq_zero_of_notMem
    (φ : 𝓓^{1}(U, ℝ)) {x : ℝ^n} (hx : x ∉ U) (i : Fin n) :
    (∂[i] ⇑φ) x = 0 :=
  φ.partialDeriv_eq_zero_of_notMem_tsupport
    (fun hxSupport ↦ hx (φ.tsupport_subset hxSupport)) i

/-- Multiplying a locally integrable coefficient by a coordinate derivative of a test function
produces a globally integrable function. -/
theorem integrable_partialDeriv_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓^{1}(U, ℝ)) {g : ℝ^n → E}
    (hg : LocallyIntegrableOn g U volume) (i : Fin n) :
    Integrable (fun x : ℝ^n ↦ (∂[i] ⇑φ) x • g x) volume := by
  have hgSupport : IntegrableOn g (tsupport (φ : ℝ^n → ℝ)) volume :=
    hg.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport
  have hIntegrableOn :
      IntegrableOn
        (fun x : ℝ^n ↦ (∂[i] ⇑φ) x • g x)
        (tsupport (φ : ℝ^n → ℝ)) volume :=
    hgSupport.continuousOn_smul
      (φ.continuous_partialDeriv i).continuousOn φ.hasCompactSupport
  apply
    (integrableOn_iff_integrable_of_support_subset
      (s := tsupport (φ : ℝ^n → ℝ)) ?_).mp hIntegrableOn
  intro x hx
  by_contra hxSupport
  exact hx (by simp [φ.partialDeriv_eq_zero_of_notMem_tsupport hxSupport i])

/-- Scalar form of `integrable_partialDeriv_smul`, with the coefficient written first. -/
theorem integrable_mul_partialDeriv
    (φ : 𝓓^{1}(U, ℝ)) {g : ℝ^n → ℝ}
    (hg : LocallyIntegrableOn g U volume) (i : Fin n) :
    Integrable (fun x : ℝ^n ↦ g x * (∂[i] ⇑φ) x) volume := by
  simpa [smul_eq_mul, mul_comm] using φ.integrable_partialDeriv_smul hg i

/-- Multiplying the derivative of a support-locally `C¹` coefficient by a
test function produces a globally integrable function. -/
theorem integrable_mul_partialDeriv_of_contDiffAt
    (φ : 𝓓^{1}(U, ℝ)) {g : ℝ^n → ℝ}
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (i : Fin n) :
    Integrable (fun x : ℝ^n ↦ φ x * (∂[i] g) x) volume := by
  let gφ : 𝓓^{1}(U, ℝ) :=
    mulLeft g φ fun x hx ↦ hg x (φ.tsupport_subset hx)
  have hgContinuous : ContinuousOn g U := by
    intro x hx
    exact (hg x hx).continuousAt.continuousWithinAt
  have hgLocal : LocallyIntegrableOn g U volume :=
    hgContinuous.locallyIntegrableOn U.isOpen.measurableSet
  have hproduct (x : ℝ^n) :
      (∂[i] (gφ : ℝ^n → ℝ)) x =
        g x * (∂[i] (φ : ℝ^n → ℝ)) x +
          φ x * (∂[i] g) x := by
    by_cases hx : x ∈ U
    · simpa [gφ] using
        partialDeriv_mulLeft g φ
          (fun y hy ↦ hg y (φ.tsupport_subset hy)) i
          (hg x hx).differentiableAt_one
    · have hφ : φ x = 0 := φ.zero_on_compl hx
      have hφDeriv :
          (∂[i] (φ : ℝ^n → ℝ)) x = 0 :=
        φ.partialDeriv_eq_zero_of_notMem hx i
      have hgφDeriv :
          (∂[i] (gφ : ℝ^n → ℝ)) x = 0 :=
        gφ.partialDeriv_eq_zero_of_notMem hx i
      simp [hgφDeriv, hφ, hφDeriv]
  have hsub :
      Integrable
        (fun x : ℝ^n ↦
          (∂[i] (gφ : ℝ^n → ℝ)) x -
            g x * (∂[i] (φ : ℝ^n → ℝ)) x)
        volume :=
    (gφ.integrable_partialDeriv i).sub
      (φ.integrable_mul_partialDeriv hgLocal i)
  apply hsub.congr
  filter_upwards with x
  rw [hproduct x]
  ring

end TestFunction

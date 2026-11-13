/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.FDeriv.Operators
public import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.Calculus

/-!
# Coordinate integration by parts for test functions

For a compactly supported `C¹` scalar function `f` and a map `g : ℝ^n → E` into a real
normed space that is `C¹` at every point of `tsupport f`,

`∫ f · ∂ᵢg = -∫ (∂ᵢf) · g`,

with no boundary term because `f` vanishes outside a compact set. This is the integration by
parts formula of Evans, Appendix C.2, Theorem 2, without its boundary term; it is also formula
(1) of §5.2.1, which motivates the definition of weak derivatives there. Mathlib proves it for
Fréchet derivatives in an arbitrary direction
(`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`); here it is specialized to the
coordinate directions `eᵢ` and to the `partialDeriv` and `laplacian` notation used throughout
LeanPDE. Iterating once gives the formal self-adjointness of the Laplacian, which is Green's
formula (iii) of Appendix C.2, Theorem 3, without boundary terms.
The vector-valued statement is kept so that scalar conservation laws and finite-dimensional
systems share one weak formulation. The vector-valued formula uses Mathlib's Bochner integral,
which is defined to be zero when the codomain is not complete.

## Main results

* `PDE.Analysis.integral_smul_partialDeriv_eq_neg_of_contDiffAt` (from
  `Integration.CompactByParts`): coordinate integration by parts with coefficient regularity
  only at points of the test factor's support.
* `integral_smul_secondPartialDeriv_eq`: `∫ f • ∂ᵢ²g = ∫ (∂ᵢ²f) • g` near the test support.
* `integral_mul_laplacian_eq_of_contDiffAt`: `∫ f Δg = ∫ (Δf) g` when `f` has compact support
  and `g` is `C²` near the support of `f`; `integral_mul_laplacian_eq` is the global case.
* `TestFunction.laplacianCLM_apply_eq_laplacian`: Mathlib's bundled Laplacian on test
  functions agrees pointwise with the coordinate Laplacian.
* `TestFunction.integral_partialDeriv_eq_zero`: `∫ ∂ᵢφ = 0` for a `C¹` test function.

The `TestFunction` namespace also records that the Laplacian of a test function is smooth (or
continuous, for `C²`), compactly supported inside the support of `φ`, and integrable.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.2, Theorems 2 and 3, p. 712; §5.2.1, (1)-(3),
  p. 256.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

noncomputable section

open Function MeasureTheory Set
open scoped Distributions

namespace PDE.DistributionTheory

open PDE.Analysis

variable {n : ℕ} {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate derivative of a compactly supported `C¹` scalar field on Euclidean space is
integrable. -/
theorem integrable_partialDeriv_of_hasCompactSupport
    {F : ℝ^n → ℝ} (i : Fin n)
    (hF : ContDiff ℝ 1 F) (hcompact : HasCompactSupport F) :
    Integrable (∂[i] F) := by
  have hcont : Continuous (fun x ↦ fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ))) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact hcont.integrable_of_hasCompactSupport
    (hcompact.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ)))

/-- The integral of a coordinate derivative of a compactly supported `C¹` scalar field on
Euclidean space vanishes: integrate by parts against the constant test function `1`. -/
theorem integral_partialDeriv_eq_zero_of_hasCompactSupport
    {F : ℝ^n → ℝ} (i : Fin n)
    (hF : ContDiff ℝ 1 F) (hcompact : HasCompactSupport F) :
    ∫ x, (∂[i] F) x = 0 := by
  have h := integral_mul_partialDeriv_eq_neg (f := F) (g := fun _ : ℝ^n ↦ (1 : ℝ)) i
    hF contDiff_const hcompact
  have hzero : (0 : ℝ) = -∫ x : ℝ^n, (∂[i] F) x ∂volume := by
    simpa [partialDeriv] using h
  linarith

/-- Two coordinate integrations by parts for a vector coefficient that is `C²`
only near the support of the compact test. -/
theorem integral_smul_secondPartialDeriv_eq
    {f : ℝ^n → ℝ} {g : ℝ^n → E} (i : Fin n)
    (hf : ContDiff ℝ 2 f) (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 2 g x)
    (hcompact : HasCompactSupport f) :
    (∫ x, f x • (∂[i] (∂[i] g)) x) =
      ∫ x, (∂[i] (∂[i] f)) x • g x := by
  have hfirst := integral_smul_partialDeriv_eq_neg_of_contDiffAt i (hf.of_le (by norm_num))
    (fun x hx ↦ contDiffAt_partialDeriv 1 (hg x hx) i) hcompact
  have hsubset : tsupport (∂[i] f) ⊆ tsupport f :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := f) (EuclideanSpace.single i (1 : ℝ))
  rw [hfirst, integral_smul_partialDeriv_eq_neg_of_contDiffAt i
    (contDiff_partialDeriv_of_succ (m := 1) hf)
    (fun x hx ↦ (hg x (hsubset hx)).of_le (by norm_num))
    (hcompact.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))), neg_neg]

/-- The Laplacian is formally self-adjoint against a compact `C²` test, with
regularity of the other factor only near the support of that test. -/
theorem integral_mul_laplacian_eq_of_contDiffAt
    {f u : ℝ^n → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hu : ∀ x ∈ tsupport f, ContDiffAt ℝ 2 u x) :
    (∫ x, f x * laplacian u x) = ∫ x, laplacian f x * u x := by
  have hleft (i : Fin n) :
      Integrable (fun x ↦ f x * (∂[i] (∂[i] u)) x) := by
    apply hc.integrable_of_continuousOn_tsupport
    · intro x hx
      exact (hf.continuous.continuousAt.mul
        (contDiffAt_partialDeriv 0
          (contDiffAt_partialDeriv 1 (hu x hx) i) i).continuousAt).continuousWithinAt
    · intro x hx
      simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hright (i : Fin n) :
      Integrable (fun x ↦ (∂[i] (∂[i] f)) x * u x) := by
    apply hc.integrable_of_continuousOn_tsupport
    · intro x hx
      exact ((contDiffAt_partialDeriv 0
        (contDiffAt_partialDeriv 1 hf.contDiffAt i) i).continuousAt.mul
          (hu x hx).continuousAt).continuousWithinAt
    · intro x hx
      have hz : (∂[i] (∂[i] f)) x = 0 := by
        change (∂[i] (fun y ↦ (∂[i] f) y)) x = 0
        simpa [partialDeriv] using partialDeriv_second_congr_nhds i
          (notMem_tsupport_iff_eventuallyEq.mp hx)
      rw [hz, zero_mul]
  simp only [laplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hleft i),
    integral_finsetSum Finset.univ (fun i _ ↦ hright i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_smul_secondPartialDeriv_eq i hf hu hc

/-- The Laplacian is formally self-adjoint when one factor is compactly
supported. -/
theorem integral_mul_laplacian_eq
    {f : ℝ^n → ℝ} (g : ℝ^n → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hcompact : HasCompactSupport f) :
    (∫ x : ℝ^n, f x * laplacian g x) =
      ∫ x : ℝ^n, laplacian f x * g x :=
  integral_mul_laplacian_eq_of_contDiffAt hf hcompact fun _ _ ↦ hg.contDiffAt

end PDE.DistributionTheory

namespace TestFunction

variable {n : ℕ} {U : TopologicalSpace.Opens (ℝ^n)}

/-- The Laplacian of a smooth test function is smooth. -/
theorem contDiff_laplacian (φ : 𝓓(U, ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (laplacian (φ : ℝ^n → ℝ)) := by
  unfold laplacian
  apply ContDiff.sum
  intro i _hi
  exact PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv φ.contDiff)

/-- The total coordinate Laplacian of a test function is supported in the
support of the original function. -/
theorem support_laplacian_subset {k : ℕ∞} (φ : 𝓓^{k}(U, ℝ)) :
    Function.support (laplacian (φ : ℝ^n → ℝ)) ⊆
      tsupport (φ : ℝ^n → ℝ) := by
  intro x hx
  by_contra hxtsupport
  have hzero :
      (φ : ℝ^n → ℝ) =ᶠ[nhds x] (0 : ℝ^n → ℝ) :=
    (notMem_tsupport_iff_eventuallyEq).mp hxtsupport
  have hlaplacian : laplacian (φ : ℝ^n → ℝ) x = 0 := by
    unfold laplacian
    apply Finset.sum_eq_zero
    intro i _hi
    have hsecond := PDE.partialDeriv_second_congr_nhds (n := n) i hzero
    simpa [partialDeriv] using hsecond
  exact hx hlaplacian

/-- The total coordinate Laplacian of a test function has compact support. -/
theorem hasCompactSupport_laplacian {k : ℕ∞}
    (φ : 𝓓^{k}(U, ℝ)) :
    HasCompactSupport (laplacian (φ : ℝ^n → ℝ)) :=
  HasCompactSupport.of_support_subset_isCompact
    φ.hasCompactSupport φ.support_laplacian_subset

/-- The Laplacian of a `C²` test function is continuous. -/
theorem continuous_laplacian_two (φ : 𝓓^{2}(U, ℝ)) :
    Continuous (laplacian (φ : ℝ^n → ℝ)) := by
  unfold laplacian
  apply continuous_finsetSum
  intro i _hi
  have hpartial : ContDiff ℝ 1 (fun x ↦ (∂[i] ⇑φ) x) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) φ.contDiff
  exact (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hpartial).continuous

/-- The Laplacian of a `C²` test function is integrable. -/
theorem integrable_laplacian_two (φ : 𝓓^{2}(U, ℝ)) :
    Integrable (laplacian (φ : ℝ^n → ℝ)) volume :=
  φ.continuous_laplacian_two.integrable_of_hasCompactSupport
    φ.hasCompactSupport_laplacian

/-- The Laplacian of a smooth test function is integrable. -/
theorem integrable_laplacian (φ : 𝓓(U, ℝ)) :
    Integrable (laplacian (φ : ℝ^n → ℝ)) volume :=
  φ.contDiff_laplacian.continuous.integrable_of_hasCompactSupport
    φ.hasCompactSupport_laplacian

/-- Mathlib's bundled test-function Laplacian agrees pointwise with the
classical Euclidean Laplacian used by LeanPDE. -/
@[simp]
theorem laplacianCLM_apply_eq_laplacian
    (φ : 𝓓(U, ℝ)) (x : ℝ^n) :
    LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓(U, ℝ) φ x =
      laplacian (φ : ℝ^n → ℝ) x := by
  rw [LineDeriv.laplacianCLM_eq_sum
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  simp only [_root_.sum_apply]
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _hi
  let firstDerivative : 𝓓(U, ℝ) :=
    TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ
  have hfirst :
      (firstDerivative : ℝ^n → ℝ) =
        (∂[i] (φ : ℝ^n → ℝ)) := by
    funext y
    rw [show firstDerivative y =
        (TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ : 𝓓(U, ℝ)) y by rfl]
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  change
    (TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) firstDerivative : 𝓓(U, ℝ)) x =
      (∂[i] (∂[i] (φ : ℝ^n → ℝ))) x
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [(firstDerivative.contDiff.differentiable
    (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  change
    fderiv ℝ (firstDerivative : ℝ^n → ℝ) x
        (EuclideanSpace.single i (1 : ℝ)) =
      (∂[i] (∂[i] (φ : ℝ^n → ℝ))) x
  rw [hfirst]
  rfl

/-- Every coordinate derivative of a compactly supported test function has
zero integral. -/
theorem integral_partialDeriv_eq_zero
    (φ : 𝓓^{1}(U, ℝ)) (i : Fin n) :
    (∫ x : ℝ^n, (∂[i] (φ : ℝ^n → ℝ)) x ∂volume) = 0 :=
  PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport i
    φ.contDiff φ.hasCompactSupport

end TestFunction

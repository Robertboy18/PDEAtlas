/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Linearization
public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileExhaustion
import PDE.Analysis.Integration.CompactByPartsCoordinates
import PDE.FDeriv.PartialDeriv.Smooth
import PDE.Spaces.Sobolev.Calculus.IsolatedPoint
import PDE.Spaces.Sobolev.Approximation.Mollification.FiniteRegularityTesting
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# The weak profile density of a field smooth off the origin

For a continuous field `U` on `ℝ³` that is `C²` and divergence free away from the origin, with
locally integrable first partials and diagonal second partials, the integral of the weak profile
density against a smooth compactly supported field is the pairing of the stationary operator
`-½(U + ξ·∇U) + (U·∇)U - ΔU` with the field
(`integral_weakProfileDensity_eq_integral_inner_stationaryVelocityOperator`). This identifies the
weak residual of a numerically computed candidate, which is smooth only off the origin.

## Main results

* `integral_weakProfileDensity_eq_integral_inner_stationaryVelocityOperator`: the identity above.
* `integral_inner_profileAdjoint_eq_integral_inner_stationaryVelocityLinearization`: the same
  identity for the linearization at `B`. For `B` that is `C¹` and `V` that is `C²`, both divergence
  free off the origin, pairing `V` with `profileAdjoint B φ` gives the pairing of
  `-½(V + ξ·∇V) + (B·∇)V + (V·∇)B - ΔV` with `φ`; the right side is integrable
  (`integrable_inner_stationaryVelocityLinearization`).
* `integral_inner_gradient_eq_zero`: `∫ ∇P·φ = 0` for a divergence-free test field `φ` and a locally
  integrable `P` whose locally integrable classical partials are its weak derivatives.

## How it works

Both identities are proved one component at a time, by moving every derivative from the test field
onto the field. The single point where the field may fail to be smooth does not obstruct this: a
function that is `C¹` off a point with locally integrable classical partials has them as weak
derivatives (`SobolevSpace.hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_zero`), which gives
the integration by parts `integral_mul_partialDeriv_eq_neg_of_contDiffAt`. Applied twice it moves
the Laplacian (`integral_mul_partialDeriv_partialDeriv_eq`), and with the weight `xⱼ` it gives the
dilation term `∫ f xⱼ ∂ⱼψ = -∫ (∂ⱼ f) xⱼ ψ - ∫ f ψ` (`integral_mul_coord_mul_partialDeriv_eq`). In
the convection terms the transporting field is divergence free off the origin, so
`sum_integral_mul_mul_partialDeriv_eq` moves the derivative without leaving a divergence term. The
pressure identity is one integration by parts against the weak derivatives of `P`, after which the
divergence of `φ` vanishes pointwise.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open MeasureTheory.LocallyIntegrable (integrable_mul_right_of_hasCompactSupport)
open scoped RealInnerProductSpace

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- Integration by parts against a smooth compactly supported function for a function that is
`C¹` off the origin with a locally integrable partial derivative. -/
theorem integral_mul_partialDeriv_eq_neg_of_contDiffAt {f ψ : ℝ^3 → ℝ}
    (hf : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 f x) (hfi : LocallyIntegrable f volume) (j : Fin 3)
    (hfj : LocallyIntegrable (PDE.partialDeriv j f) volume) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, f x * PDE.partialDeriv j ψ x = -∫ x, PDE.partialDeriv j f x * ψ x := by
  have hw := hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_zero (n := 2) hf
    (hfi.locallyIntegrableOn univ) j (hfj.locallyIntegrableOn univ)
  have h := hw.integral_identity_of_contDiff (m := 1) isOpen_univ (hψ.of_le (by simp)) hψc
    (subset_univ _) (by simp)
  simpa [domainMeasure, iteratedPartialDeriv] using h


/-- At a point where a field is `C²`, a component of its coordinate Laplacian is the sum of the
diagonal second partials of the component. -/
theorem laplacian_apply_of_contDiffAt {U : ℝ^3 → ℝ^3} {x : ℝ^3} (hU : ContDiffAt ℝ 2 U x)
    (i : Fin 3) :
    PDE.laplacian U x i =
      ∑ j, PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ U y i)) x := by
  unfold PDE.laplacian
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hD : DifferentiableAt ℝ (PDE.partialDeriv j U) x :=
    (PDE.contDiffAt_partialDeriv 1 (by norm_num; exact hU) j).differentiableAt (by simp)
  rw [PDE.partialDeriv_apply j i hD]
  refine PDE.partialDeriv_congr_nhds j ?_
  filter_upwards [hU.eventually (by simp)] with y hy
  exact PDE.partialDeriv_apply j i (hy.differentiableAt (by simp))


variable {U φ : ℝ^3 → ℝ^3}


/-- Integration by parts of the dilation term: `∫ f xⱼ ∂ⱼψ = -∫ (∂ⱼ f) xⱼ ψ - ∫ f ψ`, for a
continuous `f` that is `C¹` off the origin with a locally integrable partial derivative. -/
theorem integral_mul_coord_mul_partialDeriv_eq {f ψ : ℝ^3 → ℝ} (hfc : Continuous f)
    (hf : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 f x) (j : Fin 3)
    (hfj : LocallyIntegrable (PDE.partialDeriv j f) volume) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, f x * x j * PDE.partialDeriv j ψ x =
      -(∫ x, PDE.partialDeriv j f x * (x j * ψ x)) - ∫ x, f x * ψ x := by
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^3 ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).contDiff
  have h := integral_mul_partialDeriv_eq_neg_of_contDiffAt hf hfc.locallyIntegrable j hfj
    (hcoord.mul hψ) hψc.mul_left
  have hpd (x : ℝ^3) : PDE.partialDeriv j (fun y ↦ y j * ψ y) x =
      ψ x + x j * PDE.partialDeriv j ψ x := by
    rw [PDE.partialDeriv_mul (hcoord.differentiable (by simp) x) (hψ.differentiable (by simp) x),
      PDE.partialDeriv_coord]
    simp
  simp only [hpd, mul_add] at h
  have i1 : Integrable (fun x ↦ f x * ψ x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right hfc hψ.continuous hψc
  have i2 : Integrable (fun x ↦ f x * (x j * PDE.partialDeriv j ψ x)) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right hfc
      (hcoord.continuous.mul (hψ.partialDeriv j (k := 0)).continuous)
      (hψc.partialDeriv j).mul_left
  rw [integral_add i1 i2] at h
  simp only [mul_assoc]
  linarith

/-- Integration by parts twice: `∫ f ∂ⱼ∂ⱼψ = ∫ (∂ⱼ∂ⱼ f) ψ`, for a continuous `f` that is `C²` off
the origin with locally integrable `∂ⱼ f` and `∂ⱼ∂ⱼ f`. -/
theorem integral_mul_partialDeriv_partialDeriv_eq {f ψ : ℝ^3 → ℝ} (hfc : Continuous f)
    (hf : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 f x) (j : Fin 3)
    (hfj : LocallyIntegrable (PDE.partialDeriv j f) volume)
    (hfjj : LocallyIntegrable (PDE.partialDeriv j (PDE.partialDeriv j f)) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, f x * PDE.partialDeriv j (PDE.partialDeriv j ψ) x =
      ∫ x, PDE.partialDeriv j (PDE.partialDeriv j f) x * ψ x := by
  have h1 := integral_mul_partialDeriv_eq_neg_of_contDiffAt
    (fun x hx ↦ (hf x hx).of_le (by simp)) hfc.locallyIntegrable j hfj
    (hψ.partialDeriv j (k := (⊤ : ℕ∞))) (hψc.partialDeriv j)
  have h2 := integral_mul_partialDeriv_eq_neg_of_contDiffAt (f := PDE.partialDeriv j f)
    (fun x hx ↦ PDE.contDiffAt_partialDeriv 1 (by norm_num; exact hf x hx) j) hfj j hfjj hψ hψc
  rw [h1, h2, neg_neg]

/-- Integration by parts of a transport term: `∑ⱼ ∫ g Aⱼ ∂ⱼψ = -∫ (∑ⱼ Aⱼ ∂ⱼ g) ψ`, for a continuous
field `A` that is `C¹` and divergence free off the origin and a continuous `g` that is `C¹` off
the origin, with locally integrable partial derivatives. -/
theorem sum_integral_mul_mul_partialDeriv_eq {A : ℝ^3 → ℝ^3} {g ψ : ℝ^3 → ℝ}
    (hAc : Continuous A) (hA : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 A x)
    (hAdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence A x = 0)
    (hAD : ∀ j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ A x j)) volume)
    (hgc : Continuous g) (hg : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 g x)
    (hgD : ∀ j, LocallyIntegrable (PDE.partialDeriv j g) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∑ j, ∫ x, g x * A x j * PDE.partialDeriv j ψ x =
      -∫ x, (∑ j, A x j * PDE.partialDeriv j g x) * ψ x := by
  have hAc' (k : Fin 3) : Continuous (fun x ↦ A x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hAc
  have hAk (k : Fin 3) : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 (fun y ↦ A y k) x := fun x hx ↦
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).contDiff.contDiffAt.comp x (hA x hx)
  have hprod (j : Fin 3) : LocallyIntegrable
      (PDE.partialDeriv j (fun y ↦ A y j * g y)) volume := by
    refine (((hAD j).mul_continuous hgc).add ((hgD j).continuous_mul (hAc' j))).congr ?_
    filter_upwards [volume.ae_ne (0 : ℝ^3)] with x hx
    rw [Pi.add_apply, PDE.partialDeriv_mul ((hAk j x hx).differentiableAt (by simp))
      ((hg x hx).differentiableAt (by simp))]
  have h (j : Fin 3) := integral_mul_partialDeriv_eq_neg_of_contDiffAt
    (f := fun y ↦ A y j * g y) (fun x hx ↦ (hAk j x hx).mul (hg x hx))
    ((hAc' j).mul hgc).locallyIntegrable j (hprod j) hψ hψc
  have hint (j : Fin 3) := integrable_mul_right_of_hasCompactSupport (hprod j) hψ.continuous hψc
  have h' (j : Fin 3) : ∫ x, g x * A x j * PDE.partialDeriv j ψ x =
      -∫ x, PDE.partialDeriv j (fun y ↦ A y j * g y) x * ψ x := by
    rw [← h j]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  simp only [h']
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ ↦ hint j]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ^3)] with x hx
  have hsum : ∑ j, PDE.partialDeriv j (fun y ↦ A y j * g y) x =
      ∑ j, A x j * PDE.partialDeriv j g x := by
    simp only [PDE.partialDeriv_mul ((hAk _ x hx).differentiableAt (by simp))
      ((hg x hx).differentiableAt (by simp)), Finset.sum_add_distrib]
    have hd := hAdiv x hx
    rw [PDE.divergence_eq_sum] at hd
    rw [← Finset.sum_mul, hd, zero_mul, zero_add]
  rw [← Finset.sum_mul, hsum]

/-- One component of the weak profile identity. -/
private theorem integral_component_eq (hc : Continuous U)
    (hU : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 U x)
    (hdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence U x = 0)
    (hD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ U x i)) volume)
    (hH : ∀ i j, LocallyIntegrable
      (PDE.partialDeriv j (PDE.partialDeriv j (fun x ↦ U x i))) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (i : Fin 3) :
    (∫ x, U x i * φ x i) +
        (1 / 2 : ℝ) * (∑ j, ∫ x, U x i * x j * PDE.partialDeriv j (fun y ↦ φ y i) x) -
        (∑ j, ∫ x, U x i * U x j * PDE.partialDeriv j (fun y ↦ φ y i) x) -
        (∫ x, U x i * PDE.laplacian (fun y ↦ φ y i) x) =
      ∫ x, stationaryVelocityOperator U x i * φ x i ∧
      Integrable (fun x ↦ stationaryVelocityOperator U x i * φ x i) volume := by
  have hUc (k : Fin 3) : Continuous (fun x ↦ U x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hc
  have hUk (k : Fin 3) : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 (fun y ↦ U y k) x := fun x hx ↦
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).contDiff.contDiffAt.comp x (hU x hx)
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ
  have hφic : HasCompactSupport (fun y ↦ φ y i) := hφc.comp_left (g := fun v : ℝ^3 ↦ v i) rfl
  have hdφ (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    hφi.partialDeriv j (k := (⊤ : ℕ∞))
  have hdφc (j : Fin 3) : HasCompactSupport (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    hφic.partialDeriv j
  have hcoord (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^3 ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).contDiff
  have hI1 (j : Fin 3) := integral_mul_coord_mul_partialDeriv_eq (hUc i)
    (fun x hx ↦ (hUk i x hx).of_le (by simp)) j (hD i j) hφi hφic
  have hI2 := sum_integral_mul_mul_partialDeriv_eq hc (fun x hx ↦ (hU x hx).of_le (by simp))
    hdiv (fun j ↦ hD j j) (hUc i) (fun x hx ↦ (hUk i x hx).of_le (by simp)) (hD i) hφi hφic
  have hI3 (j : Fin 3) := integral_mul_partialDeriv_partialDeriv_eq (hUc i) (hUk i) j (hD i j)
    (hH i j) hφi hφic
  -- the Laplacian of the test component
  have hlap : ∫ x, U x i * PDE.laplacian (fun y ↦ φ y i) x =
      ∑ j, ∫ x, U x i * PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ φ y i)) x := by
    rw [← integral_finsetSum _ fun j _ ↦
      PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hUc i)
        ((hdφ j).partialDeriv j (k := 0)).continuous ((hdφc j).partialDeriv j)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [PDE.laplacian, Finset.mul_sum]
  -- the stationary operator, split
  have hsv : (fun x ↦ stationaryVelocityOperator U x i * φ x i) =ᵐ[volume] fun x ↦
      -(1 / 2 : ℝ) * (U x i * φ x i) -
        (1 / 2 : ℝ) * (∑ j, PDE.partialDeriv j (fun y ↦ U y i) x * (x j * φ x i)) +
        (∑ j, U x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i -
        (∑ j, PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ U y i)) x * φ x i) := by
    filter_upwards [volume.ae_ne (0 : ℝ^3)] with x hx
    have hd : DifferentiableAt ℝ U x := (hU x hx).differentiableAt (by simp)
    simp only [stationaryVelocityOperator, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, PDE.advectiveDerivative, PDE.Analysis.fderiv_apply_component hd,
      laplacian_apply_of_contDiffAt (hU x hx), Fin.sum_univ_three]
    ring
  have i1 : Integrable (fun x ↦ U x i * φ x i) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hUc i) hφi.continuous hφic
  have i2 (j : Fin 3) : Integrable
      (fun x ↦ PDE.partialDeriv j (fun y ↦ U y i) x * (x j * φ x i)) volume :=
    integrable_mul_right_of_hasCompactSupport (hD i j) ((hcoord j).continuous.mul hφi.continuous)
        hφic.mul_left
  have i3 : Integrable (fun x ↦ (∑ j, U x j * PDE.partialDeriv j (fun y ↦ U y i) x) *
      φ x i) volume := integrable_mul_right_of_hasCompactSupport
    (locallyIntegrable_finsetSum _ fun j _ ↦ (hD i j).continuous_mul (hUc j)) hφi.continuous hφic
  have i4 (j : Fin 3) : Integrable
      (fun x ↦ PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ U y i)) x * φ x i) volume :=
    integrable_mul_right_of_hasCompactSupport (hH i j) hφi.continuous hφic
  have s2 := integrable_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) ↦ i2 j
  have s4 := integrable_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) ↦ i4 j
  have iA := (i1.const_mul (-(1 / 2 : ℝ))).sub (s2.const_mul (1 / 2 : ℝ))
  refine ⟨?_, ((iA.add i3).sub s4).congr hsv.symm⟩
  rw [integral_congr_ae hsv, integral_sub, integral_add, integral_sub, integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun j _ ↦ i2 j, integral_finsetSum _ fun j _ ↦ i4 j,
    hlap, hI2]
  · simp only [hI1, hI3, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exacts [i1.const_mul _, s2.const_mul _, iA, i3, iA.add i3, s4]


/-- **Weak profile density of a field smooth off the origin.** Let `U` be continuous on `ℝ³`,
`C²` and divergence free off the origin, with locally integrable first partials and diagonal
second partials. Then the integral of the weak profile density of `U` against a smooth compactly
supported field is the pairing of the stationary operator `-½(U + ξ·∇U) + (U·∇)U - ΔU` with the
field. -/
theorem integral_weakProfileDensity_eq_integral_inner_stationaryVelocityOperator
    (hc : Continuous U) (hU : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 U x)
    (hdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence U x = 0)
    (hD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ U x i)) volume)
    (hH : ∀ i j, LocallyIntegrable
      (PDE.partialDeriv j (PDE.partialDeriv j (fun x ↦ U x i))) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, weakProfileDensity U φ x = ∫ x, ⟪stationaryVelocityOperator U x, φ x⟫ := by
  have hcomp (i : Fin 3) := integral_component_eq hc hU hdiv hD hH hφ hφc i
  have hUc (k : Fin 3) : Continuous (fun x ↦ U x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hc
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ
  have hφic (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i) :=
    hφc.comp_left (g := fun v : ℝ^3 ↦ v i) rfl
  have hcoord (j : Fin 3) : Continuous (fun y : ℝ^3 ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous
  have hd (i j : Fin 3) : Continuous (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    ((hφi i).partialDeriv j (k := 0)).continuous
  have hdc (i j : Fin 3) : HasCompactSupport (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    (hφic i).partialDeriv j
  have i1 (i : Fin 3) : Integrable (fun x ↦ U x i * φ x i) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hUc i) (hφi i).continuous (hφic i)
  have i2 (i j : Fin 3) : Integrable
      (fun x ↦ U x i * x j * PDE.partialDeriv j (fun y ↦ φ y i) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hUc i).mul (hcoord j)) (hd i j)
      (hdc i j)
  have i3 (i j : Fin 3) : Integrable
      (fun x ↦ U x i * U x j * PDE.partialDeriv j (fun y ↦ φ y i) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hUc i).mul (hUc j)) (hd i j)
      (hdc i j)
  have i4 (i : Fin 3) : Integrable (fun x ↦ U x i * PDE.laplacian (fun y ↦ φ y i) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hUc i)
      ((hφi i).of_le (by simp) : ContDiff ℝ 2 _).continuous_coordinate_laplacian
      (hφic i).coordinate_laplacian
  have s1 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i1 i
  have s2 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦
    integrable_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) ↦ i2 i j
  have s3 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦
    integrable_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) ↦ i3 i j
  have s4 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i4 i
  have hsum : ∫ x, ⟪stationaryVelocityOperator U x, φ x⟫ =
      ∑ i, ∫ x, stationaryVelocityOperator U x i * φ x i := by
    rw [← integral_finsetSum _ fun i _ ↦ (hcomp i).2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  simp only [weakProfileDensity_eq_sum U (hφ.of_le (by simp))]
  rw [integral_sub, integral_sub, integral_add, integral_const_mul,
    integral_finsetSum _ fun i _ ↦ i1 i, integral_finsetSum _ fun i _ ↦ i4 i,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ i2 i j,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ i3 i j, hsum,
    ← Finset.sum_congr rfl fun i _ ↦ (hcomp i).1]
  · simp only [fun i ↦ integral_finsetSum _ fun j (_ : j ∈ Finset.univ) ↦ i2 i j,
      fun i ↦ integral_finsetSum _ fun j (_ : j ∈ Finset.univ) ↦ i3 i j,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  exacts [s1, s2.const_mul _, s1.add (s2.const_mul _), s3, (s1.add (s2.const_mul _)).sub s3, s4]


/-- One component of the weak linearized identity. -/
private theorem integral_linear_component_eq {B V : ℝ^3 → ℝ^3} (hBc : Continuous B)
    (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x i)) volume)
    (hVc : Continuous V) (hV : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 V x)
    (hVdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence V x = 0)
    (hVD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ V x i)) volume)
    (hVH : ∀ i j, LocallyIntegrable
      (PDE.partialDeriv j (PDE.partialDeriv j (fun x ↦ V x i))) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (m : Fin 3) :
    (∫ x, V x m * φ x m) +
        (1 / 2 : ℝ) * (∑ i, ∫ x, V x m * x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
        (∑ i, ∫ x, V x m * PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ φ y m)) x) -
        (∑ i, ∫ x, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
        (∑ i, ∫ x, V x m * B x i * PDE.partialDeriv i (fun y ↦ φ y m) x) =
      ∫ x, stationaryVelocityLinearization B V x m * φ x m ∧
      Integrable (fun x ↦ stationaryVelocityLinearization B V x m * φ x m) volume := by
  have hVc' (k : Fin 3) : Continuous (fun x ↦ V x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hVc
  have hBc' (k : Fin 3) : Continuous (fun x ↦ B x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hBc
  have hVk (k : Fin 3) : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 (fun y ↦ V y k) x := fun x hx ↦
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).contDiff.contDiffAt.comp x (hV x hx)
  have hBk (k : Fin 3) : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 (fun y ↦ B y k) x := fun x hx ↦
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).contDiff.contDiffAt.comp x (hB x hx)
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y m) :=
    (EuclideanSpace.proj m : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ
  have hφic : HasCompactSupport (fun y ↦ φ y m) := hφc.comp_left (g := fun v : ℝ^3 ↦ v m) rfl
  have hcoord (j : Fin 3) : Continuous (fun y : ℝ^3 ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous
  have hI1 (i : Fin 3) := integral_mul_coord_mul_partialDeriv_eq (hVc' m)
    (fun x hx ↦ (hVk m x hx).of_le (by simp)) i (hVD m i) hφi hφic
  have hI3 (i : Fin 3) := integral_mul_partialDeriv_partialDeriv_eq (hVc' m) (hVk m) i (hVD m i)
    (hVH m i) hφi hφic
  have hIc := sum_integral_mul_mul_partialDeriv_eq hVc (fun x hx ↦ (hV x hx).of_le (by simp))
    hVdiv (fun j ↦ hVD j j) (hBc' m) (hBk m) (hBD m) hφi hφic
  have hId := sum_integral_mul_mul_partialDeriv_eq hBc hB hBdiv (fun j ↦ hBD j j) (hVc' m)
    (fun x hx ↦ (hVk m x hx).of_le (by simp)) (hVD m) hφi hφic
  -- the linearized operator, split
  have hsv : (fun x ↦ stationaryVelocityLinearization B V x m * φ x m) =ᵐ[volume] fun x ↦
      -(1 / 2 : ℝ) * (V x m * φ x m) -
        (1 / 2 : ℝ) * (∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * (x i * φ x m)) +
        (∑ i, B x i * PDE.partialDeriv i (fun y ↦ V y m) x) * φ x m +
        (∑ i, V x i * PDE.partialDeriv i (fun y ↦ B y m) x) * φ x m -
        (∑ i, PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ V y m)) x * φ x m) := by
    filter_upwards [volume.ae_ne (0 : ℝ^3)] with x hx
    have hdV : DifferentiableAt ℝ V x := (hV x hx).differentiableAt (by simp)
    have hdB : DifferentiableAt ℝ B x := (hB x hx).differentiableAt (by simp)
    simp only [stationaryVelocityLinearization, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, PDE.advectiveDerivative,
      PDE.Analysis.fderiv_apply_component hdV, PDE.Analysis.fderiv_apply_component hdB,
      laplacian_apply_of_contDiffAt (hV x hx), Fin.sum_univ_three]
    ring
  have i1 : Integrable (fun x ↦ V x m * φ x m) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hVc' m) hφi.continuous hφic
  have i2 (i : Fin 3) : Integrable
      (fun x ↦ PDE.partialDeriv i (fun y ↦ V y m) x * (x i * φ x m)) volume :=
    integrable_mul_right_of_hasCompactSupport (hVD m i) ((hcoord i).mul hφi.continuous)
        hφic.mul_left
  have i3 : Integrable (fun x ↦ (∑ i, B x i * PDE.partialDeriv i (fun y ↦ V y m) x) *
      φ x m) volume := integrable_mul_right_of_hasCompactSupport
    (locallyIntegrable_finsetSum _ fun i _ ↦ (hVD m i).continuous_mul (hBc' i)) hφi.continuous hφic
  have i4 : Integrable (fun x ↦ (∑ i, V x i * PDE.partialDeriv i (fun y ↦ B y m) x) *
      φ x m) volume := integrable_mul_right_of_hasCompactSupport
    (locallyIntegrable_finsetSum _ fun i _ ↦ (hBD m i).continuous_mul (hVc' i)) hφi.continuous hφic
  have i5 (i : Fin 3) : Integrable
      (fun x ↦ PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ V y m)) x * φ x m) volume :=
    integrable_mul_right_of_hasCompactSupport (hVH m i) hφi.continuous hφic
  have s2 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i2 i
  have s5 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i5 i
  have iA := (i1.const_mul (-(1 / 2 : ℝ))).sub (s2.const_mul (1 / 2 : ℝ))
  refine ⟨?_, (((iA.add i3).add i4).sub s5).congr hsv.symm⟩
  rw [integral_congr_ae hsv, integral_sub, integral_add, integral_add, integral_sub,
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ ↦ i2 i,
    integral_finsetSum _ fun i _ ↦ i5 i, hIc, hId]
  · simp only [hI1, hI3, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exacts [i1.const_mul _, s2.const_mul _, iA, i3, iA.add i3, i4, (iA.add i3).add i4, s5]

/-- **Weak linearized identity for fields smooth off the origin.** Let `B` be continuous, `C¹`
and divergence free off the origin, and `V` continuous, `C²` and divergence free off the origin,
with locally integrable first partials of both and diagonal second partials of `V`. Then the
pairing of `V` with the adjoint `profileAdjoint B φ` of the linearization at `B`, for a smooth
compactly supported `φ`, is the pairing of the linearized operator
`-½(V + ξ·∇V) + (B·∇)V + (V·∇)B - ΔV` with `φ`. -/
theorem integral_inner_profileAdjoint_eq_integral_inner_stationaryVelocityLinearization
    {B V : ℝ^3 → ℝ^3} (hBc : Continuous B) (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x i)) volume)
    (hVc : Continuous V) (hV : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 V x)
    (hVdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence V x = 0)
    (hVD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ V x i)) volume)
    (hVH : ∀ i j, LocallyIntegrable
      (PDE.partialDeriv j (PDE.partialDeriv j (fun x ↦ V x i))) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, ⟪V x, profileAdjoint B φ x⟫ = ∫ x, ⟪stationaryVelocityLinearization B V x, φ x⟫ := by
  have hcomp (m : Fin 3) := integral_linear_component_eq hBc hB hBdiv hBD hVc hV hVdiv hVD hVH
    hφ hφc m
  have hVc' (k : Fin 3) : Continuous (fun x ↦ V x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hVc
  have hBc' (k : Fin 3) : Continuous (fun x ↦ B x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hBc
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ
  have hφic (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i) :=
    hφc.comp_left (g := fun v : ℝ^3 ↦ v i) rfl
  have hcoord (j : Fin 3) : Continuous (fun y : ℝ^3 ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous
  have hd (i j : Fin 3) : Continuous (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    ((hφi i).partialDeriv j (k := 0)).continuous
  have hdc (i j : Fin 3) : HasCompactSupport (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    (hφic i).partialDeriv j
  have hdd (i j : Fin 3) : Continuous
      (PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ φ y i))) :=
    (((hφi i).partialDeriv j (k := (⊤ : ℕ∞))).partialDeriv j (k := 0)).continuous
  have hddc (i j : Fin 3) : HasCompactSupport
      (PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ φ y i))) :=
    ((hφic i).partialDeriv j).partialDeriv j
  have i1 (m : Fin 3) : Integrable (fun x ↦ V x m * φ x m) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hVc' m) (hφi m).continuous (hφic m)
  have i2 (m i : Fin 3) : Integrable
      (fun x ↦ V x m * x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hVc' m).mul (hcoord i)) (hd m i)
      (hdc m i)
  have i3 (m i : Fin 3) : Integrable
      (fun x ↦ V x m * PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ φ y m)) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hVc' m) (hdd m i) (hddc m i)
  have i4 (m i : Fin 3) : Integrable
      (fun x ↦ B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hBc' m).mul (hVc' i)) (hd m i)
      (hdc m i)
  have i5 (m i : Fin 3) : Integrable
      (fun x ↦ V x m * B x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hVc' m).mul (hBc' i)) (hd m i)
      (hdc m i)
  have hsum : ∫ x, ⟪stationaryVelocityLinearization B V x, φ x⟫ =
      ∑ m, ∫ x, stationaryVelocityLinearization B V x m * φ x m := by
    rw [← integral_finsetSum _ fun m _ ↦ (hcomp m).2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hpt : (fun x ↦ ⟪V x, profileAdjoint B φ x⟫) = fun x ↦ ∑ m, (V x m * φ x m +
      (1 / 2 : ℝ) * (∑ i, V x m * x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
      (∑ i, V x m * PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ φ y m)) x) -
      (∑ i, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
      (∑ i, V x m * B x i * PDE.partialDeriv i (fun y ↦ φ y m) x)) := by
    funext x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, profileAdjoint_apply hφ]
    simp only [Fin.sum_univ_three]
    ring
  have s2 (m : Fin 3) := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i2 m i
  have s3 (m : Fin 3) := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i3 m i
  have s4 (m : Fin 3) := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i4 m i
  have s5 (m : Fin 3) := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i5 m i
  have iA (m : Fin 3) := (i1 m).add ((s2 m).const_mul (1 / 2 : ℝ))
  rw [hpt, integral_finsetSum, hsum]
  · refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← (hcomp m).1, integral_sub, integral_sub, integral_sub, integral_add, integral_const_mul,
      integral_finsetSum _ fun i _ ↦ i2 m i, integral_finsetSum _ fun i _ ↦ i3 m i,
      integral_finsetSum _ fun i _ ↦ i4 m i, integral_finsetSum _ fun i _ ↦ i5 m i]
    exacts [i1 m, (s2 m).const_mul _, iA m, s3 m, (iA m).sub (s3 m), s4 m,
      ((iA m).sub (s3 m)).sub (s4 m), s5 m]
  · exact fun m _ ↦ (((iA m).sub (s3 m)).sub (s4 m)).sub (s5 m)


/-- Under the hypotheses of
`integral_inner_profileAdjoint_eq_integral_inner_stationaryVelocityLinearization`, the pairing of
the linearized operator with a smooth compactly supported field is integrable. -/
theorem integrable_inner_stationaryVelocityLinearization {B V : ℝ^3 → ℝ^3}
    (hBc : Continuous B) (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x i)) volume)
    (hVc : Continuous V) (hV : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 V x)
    (hVdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence V x = 0)
    (hVD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ V x i)) volume)
    (hVH : ∀ i j, LocallyIntegrable
      (PDE.partialDeriv j (PDE.partialDeriv j (fun x ↦ V x i))) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ ⟪stationaryVelocityLinearization B V x, φ x⟫) volume := by
  refine (integrable_finsetSum Finset.univ fun m _ ↦ (integral_linear_component_eq hBc hB hBdiv
    hBD hVc hV hVdiv hVD hVH hφ hφc m).2).congr (Eventually.of_forall fun x ↦ ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- A pressure with locally integrable classical partials that are its weak derivatives pairs
to zero with the gradient against a divergence-free test field: `∫ ∇P·φ = 0`. -/
theorem integral_inner_gradient_eq_zero {P : ℝ^3 → ℝ} (hP : LocallyIntegrable P volume)
    (hPw : ∀ i, HasWeakDerivativeOn univ [i] P (PDE.partialDeriv i P))
    (hPi : ∀ i, LocallyIntegrable (PDE.partialDeriv i P) volume)
    (hφ : IsSolenoidalTestField φ) : ∫ x, ⟪gradient P x, φ x⟫ = 0 := by
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ.1
  have hφic (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i) :=
    hφ.2.1.comp_left (g := fun v : ℝ^3 ↦ v i) rfl
  have hibp (i : Fin 3) : ∫ x, P x * PDE.partialDeriv i (fun y ↦ φ y i) x =
      -∫ x, PDE.partialDeriv i P x * φ x i := by
    have h := (hPw i).integral_identity_of_contDiff (m := 1) isOpen_univ
      ((hφi i).of_le (by simp)) (hφic i) (subset_univ _) (by simp)
    simpa [domainMeasure, iteratedPartialDeriv] using h
  have hint (i : Fin 3) := integrable_mul_right_of_hasCompactSupport (hPi i) (hφi i).continuous
      (hφic i)
  have hint' (i : Fin 3) := integrable_mul_right_of_hasCompactSupport hP ((hφi i).partialDeriv i
      (k := 0)).continuous
    ((hφic i).partialDeriv i)
  have hpt (x : ℝ^3) : ⟪gradient P x, φ x⟫ = ∑ i, PDE.partialDeriv i P x * φ x i := by
    rw [PiLp.inner_apply]
    simp only [PDE.gradient_apply_eq_partialDeriv, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hdiv : ∫ x, ∑ i, P x * PDE.partialDeriv i (fun y ↦ φ y i) x = 0 := by
    refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans (integral_zero _ ℝ)
    rw [← Finset.mul_sum]
    change P x * PDE.divergence φ x = 0
    rw [hφ.2.2 x, mul_zero]
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  rw [integral_finsetSum _ fun i _ ↦ hint' i] at hdiv
  simp only [hibp, Finset.sum_neg_distrib] at hdiv
  linarith

end NavierStokes.Nonuniqueness

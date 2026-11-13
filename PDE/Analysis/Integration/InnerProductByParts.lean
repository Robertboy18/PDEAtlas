/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.CompactByParts
public import PDE.FDeriv.Operators
import PDE.Analysis.Integration.CompactPairing
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Integration by parts and the vector Dirichlet energy

The coordinate Laplacian acts on a vector field componentwise. Pairing it with
the field and integrating gives the negative sum of the squared coordinate
derivatives. A compactly supported field has no boundary term, in any spatial
dimension and for values in any real inner product space.

The same coordinate argument moves the gradient of a compactly supported scalar
onto a vector field, where it becomes minus the divergence. This is the weak
form of `∇· u` tested against smooth functions.

Pairing transport with the transported field gives minus one half of the
divergence pairing against its squared norm. Divergence-free transport
therefore does no work. Only the transported field needs compact support; the
transporting field is any `C¹` field. The identity field gives the dilation identity,
and the similarity drift contributes `(n - 2) / 4` times the squared L2 norm.
In three dimensions this is the coefficient `1/4` in the coercivity bound (4.3) of Hou, Wang
and Yang.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.1, (4.1) and (4.3).
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace Gradient

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Move a coordinate derivative between vector fields. The second field only
needs to be `C¹` near the compact support of the first. -/
theorem integral_inner_partialDeriv_eq_neg_of_contDiffAt
    {f g : ℝ^n → E} (i : Fin n) (hf : ContDiff ℝ 1 f)
    (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x)
    (hcompact : HasCompactSupport f) :
    (∫ x, ⟪f x, ∂[i] g x⟫_ℝ) = -∫ x, ⟪∂[i] f x, g x⟫_ℝ :=
  integral_bilinear_partialDeriv_eq_neg_of_contDiffAt (innerSL ℝ) i hf hg hcompact

/-- Coordinate integration by parts between globally `C¹` vector fields.
Compact support of the first field supplies the integrability conditions. -/
theorem integral_inner_partialDeriv_eq_neg
    {f g : ℝ^n → E} (i : Fin n) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hcompact : HasCompactSupport f) :
    (∫ x, ⟪f x, ∂[i] g x⟫_ℝ) = -∫ x, ⟪∂[i] f x, g x⟫_ℝ :=
  integral_bilinear_partialDeriv_eq_neg (innerSL ℝ) i hf hg hcompact

/-- The vector Laplacian dissipates Dirichlet energy. No finite-dimensional or
completeness assumption is imposed on the inner product space of values. -/
theorem integral_inner_laplacian_eq_neg_sum
    {u : ℝ^n → E} (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u) :
    (∫ x, ⟪u x, laplacian u x⟫_ℝ) =
      -∑ i : Fin n, ∫ x, ‖∂[i] u x‖ ^ 2 := by
  have hpartial (i : Fin n) : ContDiff ℝ 1 (∂[i] u) :=
    contDiff_partialDeriv_of_succ (m := 1) hu
  have hsecond (i : Fin n) : Continuous (∂[i] ∂[i] u) :=
    (contDiff_partialDeriv_of_succ (m := 0) (hpartial i)).continuous
  have hint (i : Fin n) : Integrable (fun x ↦ ⟪u x, ∂[i] ∂[i] u x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (hsecond i).locallyIntegrable.integrable_inner_right_of_hasCompactSupport
        hu.continuous hcompact
  simp only [laplacian, inner_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hint i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [real_inner_self_eq_norm_sq] using
    integral_inner_partialDeriv_eq_neg i (hu.of_le (by norm_num))
      (hpartial i) hcompact

/-- Moving the gradient off a compactly supported `C¹` scalar onto a `C¹` vector
field gives minus the divergence of the field. -/
theorem integral_inner_gradient_eq_neg_integral_mul_divergence
    {φ : ℝ^n → ℝ} {u : ℝ^n → ℝ^n} (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport φ) :
    (∫ x, ⟪∇ φ x, u x⟫_ℝ) = -∫ x, φ x * ∇· u x := by
  have hui (i : Fin n) : ContDiff ℝ 1 (fun x ↦ u x i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hu
  have hleft (i : Fin n) : Integrable (fun x ↦ ∂[i] φ x * u x i) :=
    ((hφ.continuous_partialDeriv i).mul (hui i).continuous).integrable_of_hasCompactSupport
      (hcompact.partialDeriv i).mul_right
  have hright (i : Fin n) : Integrable (fun x ↦ φ x * ∂[i] (fun y ↦ u y i) x) :=
    (hφ.continuous.mul ((hui i).continuous_partialDeriv i)).integrable_of_hasCompactSupport
      hcompact.mul_right
  have hinner (x : ℝ^n) : ⟪∇ φ x, u x⟫_ℝ = ∑ i : Fin n, ∂[i] φ x * u x i := by
    rw [inner_gradient_left, fderiv_apply_eq_sum_partialDeriv_mul]
  have hdiv (x : ℝ^n) : φ x * ∇· u x = ∑ i : Fin n, φ x * ∂[i] (fun y ↦ u y i) x := by
    simp [PDE.divergence, Finset.mul_sum]
  simp_rw [hinner, hdiv]
  rw [integral_finsetSum _ fun i _ ↦ hleft i, integral_finsetSum _ fun i _ ↦ hright i,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_mul_partialDeriv_eq_neg i hφ (hui i) hcompact, neg_neg]

/-- Transport energy is one half the negative divergence pairing. Only the
transported field needs compact support. -/
theorem integral_inner_advection_eq_neg_half_divergence
    {u : ℝ^n → E} {b : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport u) :
    (∫ x, ⟪fderiv ℝ u x (b x), u x⟫_ℝ) =
      -(1 / 2 : ℝ) * ∫ x, ‖u x‖ ^ 2 * PDE.divergence b x := by
  let φ : ℝ^n → ℝ := fun x ↦ ⟪u x, u x⟫_ℝ
  have hφ : ContDiff ℝ 1 φ := hu.inner ℝ hu
  have hφcompact : HasCompactSupport φ :=
    hc.comp_left (g := fun v : E ↦ ⟪v, v⟫_ℝ) (by simp)
  have hparts := integral_inner_gradient_eq_neg_integral_mul_divergence
    hφ hb hφcompact
  have hpoint (x : ℝ^n) :
      ⟪∇ φ x, b x⟫_ℝ = 2 * ⟪fderiv ℝ u x (b x), u x⟫_ℝ := by
    rw [inner_gradient_left]
    dsimp [φ]
    rw [fderiv_inner_apply ℝ hu.differentiable_one.differentiableAt
      hu.differentiable_one.differentiableAt, real_inner_comm (u x)]
    ring
  simp_rw [hpoint, φ, real_inner_self_eq_norm_sq] at hparts
  rw [integral_const_mul] at hparts
  linarith

/-- A divergence-free transporting velocity does no work on compact test fields. -/
theorem integral_inner_advection_eq_zero
    {u : ℝ^n → E} {b : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport u)
    (hdiv : ∀ x, PDE.divergence b x = 0) :
    (∫ x, ⟪fderiv ℝ u x (b x), u x⟫_ℝ) = 0 := by
  rw [integral_inner_advection_eq_neg_half_divergence hu hb hc]
  simp [hdiv]

/-- Pairing the spatial dilation derivative with a compact field gives minus
one half the spatial dimension times its squared L2 norm. -/
theorem integral_inner_dilation_eq_neg
    {u : ℝ^n → E} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∫ x, ⟪fderiv ℝ u x x, u x⟫_ℝ) =
      -(n : ℝ) / 2 * ∫ x, ‖u x‖ ^ 2 := by
  have hdiv (x : ℝ^n) : PDE.divergence (fun y : ℝ^n ↦ y) x = (n : ℝ) := by
    simp [PDE.divergence, partialDeriv_coord]
  have h := integral_inner_advection_eq_neg_half_divergence
    (b := fun x : ℝ^n ↦ x) hu contDiff_id hc
  simp_rw [hdiv] at h
  rw [integral_mul_const] at h
  calc
    (∫ x, ⟪fderiv ℝ u x x, u x⟫_ℝ) =
        -(1 / 2 : ℝ) * ((∫ x, ‖u x‖ ^ 2) * n) := h
    _ = -(n : ℝ) / 2 * ∫ x, ‖u x‖ ^ 2 := by ring

/-- The self-similar Navier–Stokes drift has coefficient `(n−2)/4`.
No divergence-free condition is needed for this cancellation. -/
theorem integral_inner_similarity_drift
    {u : ℝ^n → E} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∫ x, ⟪(-1 / 2 : ℝ) • u x - (1 / 2 : ℝ) • fderiv ℝ u x x, u x⟫_ℝ) =
      ((n : ℝ) - 2) / 4 * ∫ x, ‖u x‖ ^ 2 := by
  have hsquareCompact : HasCompactSupport (fun x ↦ ‖u x‖ ^ 2) :=
    hc.comp_left (g := fun v : E ↦ ‖v‖ ^ 2) (by simp)
  have hsquare : Integrable (fun x ↦ ‖u x‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hsquareCompact
  have hdu : Continuous (fun x ↦ fderiv ℝ u x x) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_id
  have hmixed : Integrable (fun x ↦ ⟪fderiv ℝ u x x, u x⟫_ℝ) :=
    hdu.locallyIntegrable.integrable_inner_right_of_hasCompactSupport hu.continuous hc
  simp_rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [integral_sub (hsquare.const_mul _) (hmixed.const_mul _),
    integral_const_mul, integral_const_mul, integral_inner_dilation_eq_neg hu hc]
  ring

end PDE.Analysis

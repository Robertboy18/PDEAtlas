/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Radial
public import PDE.FDeriv.Euclidean.Distance
public import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Calculus
public import PDE.FDeriv.Euclidean.NormSq
import PDE.FDeriv.Euclidean.Norm
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Iterated-coordinate Euclidean Laplacian calculus

LeanPDE's `laplacian f x = ∑ᵢ ∂ᵢ∂ᵢ f x` is built from iterated coordinate
derivatives. It depends only on the germ of `f` at `x` (`PDE.FDeriv.Laplacian.Congruence`,
imported here). The coordinate derivatives of `‖x‖` and `‖x‖²` give the two radial formulas

`Δ(f(‖x‖²)) = 4 ‖x‖² f''(‖x‖²) + 2n f'(‖x‖²)`  and  `Δ(f(‖x‖)) = f''(‖x‖) + (n - 1)/‖x‖ · f'(‖x‖)`,

and the Laplacian of an inverse distance power,

`Δₓ |x - y|⁻ᵏ = k (k + 2 - n) |x - y|⁻ᵏ⁻²  for x ≠ y`.

The radial formula is the computation with which Evans, §2.2.1, derives the fundamental solution (6)
of Laplace's equation from the radial equation (5). The inverse-power identity gives harmonicity of
`|x - y|^(2-n)` for `n ≥ 3` (take `k = n - 2`) and the identity `Δ |x - y|⁻ⁿ = 2n |x - y|⁻ⁿ⁻²` used
for the Poisson kernels (take `k = n`). On `C²` fields the coordinate operator agrees with Mathlib's
canonical Laplacian by `ContDiffAt.coordinate_laplacian_eq_laplacian`.

## Main results

* `laplacian_congr_nhds` (from `Laplacian.Congruence`): functions that agree near `x`
  have the same Laplacian at `x`.
* `partialDeriv_norm_sq` (from `Euclidean.NormSq`), `partialDeriv_norm_of_ne_zero`,
  `laplacian_norm_sq`: derivatives of the norm and the squared norm.
* `laplacian_comp_norm_sq`: the squared-radius formula, valid at the origin as well.
* `laplacian_radial`: the radial formula off the origin, expressed through
  `PDE.CoordinateSystems.radialLaplacian`.
* `secondPartial_inv_dist_pow`, `laplacian_inv_dist_pow`: repeated coordinate derivatives and
  the Laplacian of `dist(·, y)⁻ᵏ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1, (5)-(6), pp. 21-22.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

namespace EuclideanLaplacian

open Filter Topology

/-- The `i`th coordinate derivative of the Euclidean norm is `x i / ‖x‖`. At the origin both
sides are `0`: the norm is not differentiable there because `i` makes `ℝ^n` nontrivial. -/
theorem partialDeriv_norm_of_ne_zero {n : ℕ} (i : Fin n) {x : ℝ^n} :
    (∂[i] (norm : ℝ^n → ℝ)) x = x i / ‖x‖ := by
  unfold partialDeriv
  rcases eq_or_ne x 0 with rfl | hx
  · have : Nontrivial (ℝ^n) := ⟨⟨EuclideanSpace.single i 1, 0, by simp⟩⟩
    rw [fderiv_zero_of_not_differentiableAt (not_differentiableAt_norm_zero _)]
    simp
  rw [EuclideanNorm.fderiv_norm_of_ne_zero hx]
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right,
    div_eq_mul_inv, mul_comm]

/-- The Euclidean Laplacian of the squared norm is the constant `2 * n`. -/
@[simp]
theorem laplacian_norm_sq {n : ℕ} (x : ℝ^n) :
    laplacian (n := n) (fun z : ℝ^n ↦ ‖z‖ ^ 2) x = 2 * (n : ℝ) := by
  unfold laplacian
  have hSecond (i : Fin n) :
      (∂[i] (fun y : ℝ^n ↦ (∂[i] (fun z : ℝ^n ↦ ‖z‖ ^ 2)) y)) x = 2 := by
    rw [show (fun y : ℝ^n ↦ (∂[i] (fun z : ℝ^n ↦ ‖z‖ ^ 2)) y) = fun y : ℝ^n ↦ 2 * y i by
      funext y
      exact partialDeriv_norm_sq i y]
    simpa [smul_eq_mul] using
      (PDE.partialDeriv_const_smul (n := n) (E := ℝ) (c := (2 : ℝ))
        (i := i) (f := fun y : ℝ^n ↦ y i) (x := x))
  calc
    (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ (∂[i] (fun z : ℝ^n ↦ ‖z‖ ^ 2)) y)) x) =
        ∑ _i : Fin n, (2 : ℝ) :=
      Finset.sum_congr rfl fun i _ ↦ hSecond i
    _ = 2 * (n : ℝ) := by simp [mul_comm]

/-- Laplacian chain rule for a smooth function of the squared Euclidean norm:

`Δ(f (‖x‖²)) = 4 ‖x‖² f''(‖x‖²) + 2 n f'(‖x‖²)`.

Using the squared norm rather than the norm makes the formula valid at the
origin as well. -/
theorem laplacian_comp_norm_sq {n : ℕ} (f : ℝ → ℝ)
    (x : ℝ^n) (hf : ContDiffAt ℝ 2 f (‖x‖ ^ 2)) :
    laplacian (n := n) (fun y : ℝ^n ↦ f (‖y‖ ^ 2)) x =
      4 * ‖x‖ ^ 2 * deriv (deriv f) (‖x‖ ^ 2) +
        2 * (n : ℝ) * deriv f (‖x‖ ^ 2) := by
  let q : ℝ^n → ℝ := fun y ↦ ‖y‖ ^ 2
  have hq : ContDiff ℝ 2 q := contDiff_norm_sq ℝ
  have hfNear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (q y) := by
    apply hq.continuous.continuousAt.eventually
    simpa only [q] using hf.eventually (by simp)
  have hdfDiff : DifferentiableAt ℝ (deriv f) (q x) := by
    have hdf : ContDiffAt ℝ 1 (deriv f) (q x) := by
      simpa only [q] using hf.derivWithin (m := 1) (by norm_num)
    exact hdf.differentiableAt_one
  have hfirst (i : Fin n) :
      (fun y : ℝ^n ↦ (∂[i] (fun z ↦ f (q z))) y) =ᶠ[𝓝 x]
        fun y ↦ 2 * y i * deriv f (q y) := by
    filter_upwards [hfNear] with y hfy
    rw [PDE.partialDeriv_comp_real i (hfy.differentiableAt (by norm_num))
      ((hq.differentiable (by norm_num)) y)]
    simp [q, partialDeriv_norm_sq]
  have hsecond (i : Fin n) :
      (∂[i] (fun y ↦ (∂[i] (fun z ↦ f (q z))) y)) x =
        2 * deriv f (q x) + 4 * x i ^ 2 * deriv (deriv f) (q x) := by
    rw [PDE.partialDeriv_congr_nhds i (hfirst i)]
    have hcoord : DifferentiableAt ℝ (fun y : ℝ^n ↦ 2 * y i) x := by
      fun_prop
    have hcomp : DifferentiableAt ℝ (fun y : ℝ^n ↦ deriv f (q y)) x :=
      hdfDiff.comp x ((hq.differentiable (by norm_num)) x)
    rw [PDE.partialDeriv_mul hcoord hcomp]
    have hderivCoord :
        (∂[i] (fun y : ℝ^n ↦ 2 * y i)) x = 2 := by
      rw [PDE.partialDeriv_eq_deriv_coordinateLine i x (by fun_prop)]
      simp only [Function.comp_def, PDE.coordinateLine_apply_same]
      cas
    have hderivComp :
        (∂[i] (fun y : ℝ^n ↦ deriv f (q y))) x =
          2 * x i * deriv (deriv f) (q x) := by
      rw [PDE.partialDeriv_comp_real i hdfDiff
        ((hq.differentiable (by norm_num)) x)]
      simp [q, partialDeriv_norm_sq]
    rw [hderivCoord, hderivComp]
    ring
  unfold laplacian
  calc
    (∑ i : Fin n,
        (∂[i] (fun y ↦ (∂[i] (fun z ↦ f (q z))) y)) x) =
        ∑ i : Fin n,
          (2 * deriv f (q x) +
            4 * x i ^ 2 * deriv (deriv f) (q x)) := by
      exact Finset.sum_congr rfl fun i _ ↦ hsecond i
    _ = 2 * (n : ℝ) * deriv f (q x) +
        4 * (∑ i : Fin n, x i ^ 2) * deriv (deriv f) (q x) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hsum :
          (∑ i : Fin n, 4 * x i ^ 2 * deriv (deriv f) (q x)) =
            4 * (∑ i : Fin n, x i ^ 2) * deriv (deriv f) (q x) := by
        calc
          (∑ i : Fin n, 4 * x i ^ 2 * deriv (deriv f) (q x)) =
              ∑ i : Fin n, x i ^ 2 *
                (4 * deriv (deriv f) (q x)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i : Fin n, x i ^ 2) *
                (4 * deriv (deriv f) (q x)) := by
            rw [Finset.sum_mul]
          _ = 4 * (∑ i : Fin n, x i ^ 2) *
                deriv (deriv f) (q x) := by ring
      rw [hsum]
      ring
    _ = 4 * ‖x‖ ^ 2 * deriv (deriv f) (‖x‖ ^ 2) +
        2 * (n : ℝ) * deriv f (‖x‖ ^ 2) := by
      simp only [q]
      rw [← EuclideanSpace.real_norm_sq_eq]
      ring

/-- Radial Laplacian formula:
`Δ(f (‖x‖)) = f''(‖x‖) + (n - 1) / ‖x‖ * f'(‖x‖)`. -/
theorem laplacian_radial {n : ℕ} (f : ℝ → ℝ)
    (x : ℝ^n) (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    laplacian (f ∘ norm) x = PDE.CoordinateSystems.radialLaplacian n f ‖x‖ := by
  unfold PDE.CoordinateSystems.radialLaplacian
  let r := ‖x‖
  have hr : r ≠ 0 := norm_ne_zero_iff.2 hx
  have h_diff_f_nhds : ∀ᶠ r' in nhds r, DifferentiableAt ℝ f r' := by
    obtain ⟨U, hU_nhds, h_diff_on⟩ :=
      ContDiffAt.contDiffOn hf (le_refl (2 : WithTop ℕ∞)) (fun h ↦ by cases h)
    obtain ⟨V, hV_props⟩ := (nhds_basis_opens r).mem_iff.mp hU_nhds
    rcases hV_props with ⟨⟨hrV, hV_open⟩, hVU⟩
    filter_upwards [hV_open.mem_nhds hrV] with r' hr'
    apply DifferentiableOn.differentiableAt
      ((h_diff_on.mono hVU).differentiableOn (by norm_num))
    exact hV_open.mem_nhds hr'
  have h_partial_eq_nhds (i : Fin n) :
      ∀ᶠ y in nhds x,
        (∂[i] (f ∘ (norm : ℝ^n → ℝ))) y =
          deriv f ‖y‖ * (y i / ‖y‖) := by
    filter_upwards [continuous_norm.continuousAt.eventually h_diff_f_nhds,
      eventually_ne_nhds hx] with y h_diff_y hy_ne
    change (∂[i] (fun z : ℝ^n ↦ f ‖z‖)) y = _
    rw [PDE.partialDeriv_comp_real i h_diff_y
      (differentiableAt_id.norm ℝ hy_ne)]
    rw [partialDeriv_norm_of_ne_zero i]
    ring
  unfold laplacian
  have h_sum :
      ∑ i, (∂[i] (fun y ↦ (∂[i] (f ∘ (norm : ℝ^n → ℝ))) y)) x =
        ∑ i, (deriv f r / r - deriv f r * x i ^ 2 / r ^ 3 +
          deriv (deriv f) r * x i ^ 2 / r ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [PDE.partialDeriv_congr_nhds i (h_partial_eq_nhds i)]
    let u := fun y : ℝ^n ↦ deriv f ‖y‖
    let v := fun y : ℝ^n ↦ y i / ‖y‖
    have h_diff_deriv_f : DifferentiableAt ℝ (deriv f) r := by
      have hf' : ContDiffAt ℝ 1 (fderiv ℝ f) r := by
        simpa using (hf.fderiv_right (m := 1) (n := 2) (by norm_num))
      have hconst : ContDiffAt ℝ 1 (fun _ : ℝ ↦ (1 : ℝ)) r := by
        simpa using (contDiffAt_const :
          ContDiffAt ℝ 1 (fun _ : ℝ ↦ (1 : ℝ)) r)
      have happly : ContDiffAt ℝ 1 (fun y : ℝ ↦ (fderiv ℝ f y) 1) r :=
        hf'.clm_apply hconst
      simpa [← toSpanSingleton_deriv] using happly.differentiableAt
    have h_diff_u : DifferentiableAt ℝ u x := by
      apply DifferentiableAt.comp x h_diff_deriv_f
        (differentiableAt_id.norm ℝ hx)
    have h_diff_v : DifferentiableAt ℝ v x := by
      apply DifferentiableAt.mul
      · exact
          (EuclideanSpace.proj i :
            ℝ^n →L[ℝ] ℝ).differentiableAt
      · apply DifferentiableAt.inv
        · exact differentiableAt_id.norm ℝ hx
        · exact norm_ne_zero_iff.2 hx
    have h_du :
        (∂[i] u) x =
          deriv (deriv f) r * (x i / r) := by
      dsimp only [u]
      have h_diff_norm : DifferentiableAt ℝ (norm : ℝ^n → ℝ) x :=
        differentiableAt_id.norm ℝ hx
      rw [PDE.partialDeriv_comp_real (u := norm) i h_diff_deriv_f h_diff_norm]
      rw [partialDeriv_norm_of_ne_zero i]
      dsimp only [r]
      ring
    have h_dv :
        (∂[i] v) x = 1 / r - x i ^ 2 / r ^ 3 := by
      change (∂[i] (fun y : ℝ^n ↦ y i / ‖y‖)) x = _
      have h_diff_coord :
          DifferentiableAt ℝ
            (fun y : ℝ^n ↦ y i) x := by
        simpa using
          (EuclideanSpace.proj i :
            ℝ^n →L[ℝ] ℝ).differentiableAt
      have h_diff_norm : DifferentiableAt ℝ norm x :=
        differentiableAt_id.norm ℝ hx
      rw [PDE.partialDeriv_div i (fun y : ℝ^n ↦ y i) norm x
        h_diff_coord h_diff_norm (norm_ne_zero_iff.2 hx)]
      rw [partialDeriv_norm_of_ne_zero i]
      simp only [PDE.partialDeriv_coord, ite_eq_left, one_mul, r]
      field_simp [hr]
    change (∂[i] (fun y ↦ u y * v y)) x = _
    rw [PDE.partialDeriv_mul h_diff_u h_diff_v]
    rw [h_du, h_dv]
    dsimp [u, v]
    ring
  rw [h_sum]
  have h1 : ∑ i : Fin n, deriv f r / r = n * deriv f r / r := by
    simp
    ring
  have h_sum_sq : ∑ i, x i ^ 2 = r ^ 2 := by
    simp only [pow_two]
    have : ∑ i, x i * x i = @inner ℝ _ _ x x := rfl
    rw [this]
    rw [real_inner_self_eq_norm_sq]
    simp [r, pow_two]
  have h2 :
      ∑ i : Fin n, deriv f r * x i ^ 2 / r ^ 3 =
        deriv f r / r := by
    rw [← Finset.sum_div]
    rw [← Finset.mul_sum]
    rw [h_sum_sq]
    simp [r]
    field_simp [hr]
  have h3 :
      ∑ i : Fin n, deriv (deriv f) r * x i ^ 2 / r ^ 2 =
        deriv (deriv f) r := by
    rw [← Finset.sum_div]
    rw [← Finset.mul_sum]
    rw [h_sum_sq]
    simp [r]
    field_simp [hr]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  rw [h1, h2, h3]
  field_simp [hr]
  ring

/-- The diagonal coordinate of the derivative of
`z ↦ D(dist(·, y)⁻ᵏ)(z)`.

This is the coordinate Hessian formula reused by both pointwise and
differentiation-under-the-integral arguments. -/
theorem fderiv_invDistPowFDeriv_apply_basis {n k : ℕ} (i : Fin n)
    {x y : ℝ^n} (hxy : x ≠ y) :
    (fderiv ℝ
      (fun z : ℝ^n ↦
        EuclideanDistance.invDistPowFDerivFormula k z y
          (EuclideanSpace.single i (1 : ℝ))) x)
        (EuclideanSpace.single i (1 : ℝ)) =
      (-(k : ℝ)) / dist x y ^ (k + 2) +
        (k : ℝ) * ((k + 2 : ℕ) : ℝ) * (x - y) i ^ 2 /
          dist x y ^ (k + 4) := by
  rw [(EuclideanDistance.hasFDerivAt_invDistPowFDerivFormula_apply
    (k := k) (x := x) (y := y)
    (v := EuclideanSpace.single i (1 : ℝ)) hxy).fderiv]
  have hcoord :
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) (x - y) =
        (x - y) i := by
    simpa [innerSL_apply_apply] using
      (EuclideanSpace.inner_single_left
        (i := i) (a := (1 : ℝ)) (v := x - y))
  have hdiag :
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single i (1 : ℝ)) =
        (1 : ℝ) := by
    simp [innerSL_apply_apply]
  have hkernel :
      EuclideanDistance.invDistPowFDerivFormula (k + 2) x y
          (EuclideanSpace.single i (1 : ℝ)) =
        (-((k + 2 : ℕ) : ℝ) / dist x y ^ (k + 4)) *
          (x - y) i := by
    simpa [hcoord] using
      (EuclideanDistance.invDistPowFDerivFormula_apply_eq_of_ne
        (k := k + 2) (x := x) (y := y)
        (v := EuclideanSpace.single i (1 : ℝ)) hxy)
  simp [EuclideanDistance.invDistPowSecondFDerivFormula, hcoord, hdiag, hkernel,
    smul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm, div_eq_mul_inv]
  ring

/-- A repeated coordinate derivative of an inverse power of Euclidean
distance. The formula is valid away from the pole `y`. -/
theorem secondPartial_inv_dist_pow {n k : ℕ} (i : Fin n)
    {x y : ℝ^n} (hxy : x ≠ y) :
    (∂[i] (fun z ↦
          (∂[i] (fun w : ℝ^n ↦ (dist w y ^ k)⁻¹)) z)) x =
      (-(k : ℝ)) / dist x y ^ (k + 2) +
        (k : ℝ) * ((k + 2 : ℕ) : ℝ) * (x - y) i ^ 2 /
          dist x y ^ (k + 4) := by
  have hfirst :
      (fun z ↦
        (∂[i] (fun w : ℝ^n ↦ (dist w y ^ k)⁻¹)) z) =ᶠ[nhds x]
        fun z ↦
          EuclideanDistance.invDistPowFDerivFormula k z y
            (EuclideanSpace.single i (1 : ℝ)) := by
    filter_upwards [eventually_ne_nhds hxy] with z hz
    unfold partialDeriv
    rw [(EuclideanDistance.hasFDerivAt_inv_dist_pow
      (k := k) hz).fderiv]
  rw [PDE.partialDeriv_congr_nhds i hfirst]
  exact fderiv_invDistPowFDeriv_apply_basis i hxy

/-- Euclidean Laplacian of an inverse distance power:

`Δₓ |x-y|⁻ᵏ = k (k + 2 - n) |x-y|⁻ᵏ⁻²`.

For `3 ≤ n`, choosing `k = n - 2` gives the classical harmonic Newtonian
kernel. Choosing `k = n` gives the identity used by Poisson kernels. -/
theorem laplacian_inv_dist_pow {n k : ℕ}
    {x y : ℝ^n} (hxy : x ≠ y) :
    laplacian (n := n)
        (fun z : ℝ^n ↦ (dist z y ^ k)⁻¹) x =
      (k : ℝ) * (((k + 2 : ℕ) : ℝ) - (n : ℝ)) /
        dist x y ^ (k + 2) := by
  unfold laplacian
  rw [show
      (∑ i : Fin n,
        (∂[i] (fun z ↦
            (∂[i] (fun w : ℝ^n ↦ (dist w y ^ k)⁻¹)) z)) x) =
        ∑ i : Fin n,
          ((-(k : ℝ)) / dist x y ^ (k + 2) +
            (k : ℝ) * ((k + 2 : ℕ) : ℝ) * (x - y) i ^ 2 /
              dist x y ^ (k + 4)) by
    exact Finset.sum_congr rfl fun i _ ↦
      secondPartial_inv_dist_pow i hxy]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hsum :
      ∑ i : Fin n, (x - y) i ^ 2 = dist x y ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  have hsecond :
      (∑ i : Fin n,
        (k : ℝ) * ((k + 2 : ℕ) : ℝ) * (x - y) i ^ 2 /
          dist x y ^ (k + 4)) =
        (k : ℝ) * ((k + 2 : ℕ) : ℝ) * dist x y ^ 2 /
          dist x y ^ (k + 4) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  rw [hsecond]
  have hd : dist x y ≠ 0 := dist_ne_zero.mpr hxy
  have hpow :
      dist x y ^ (k + 4) =
        dist x y ^ (k + 2) * dist x y ^ 2 := by
    rw [show k + 4 = (k + 2) + 2 by omega, pow_add]
  rw [hpow]
  field_simp [hd, pow_ne_zero]
  ring

end EuclideanLaplacian

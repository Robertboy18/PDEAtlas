/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.IntegrationByParts
public import PDE.FDeriv.Calculus

/-!
# The integrated Rellich identity

The dilation derivative `advectiveDerivative id u x` is `x · Du(x)`. For a compactly
supported `C²` function on `ℝ^n`, integration by parts gives

`∫ (x · Du) Δu = (n - 2) / 2 * ∫ |Du|²`.

The proof uses coordinate integration by parts and symmetry of the Hessian. Every integral
is over Euclidean volume; compact support and continuous derivatives give integrability.
No positivity assumption on the dimension is needed. This boundary-free identity
is the one used in the compact-support Pohozaev theorem.

Up to sign, the left side is the term `A` of steps 2 and 3 of the proof of Evans, §9.4.2,
Theorem 3, computed in (15)-(17); for compact support the boundary integrals there vanish.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, proof of Theorem 3 (Nonexistence of nontrivial
  solution), steps 2-3, (15)-(17), pp. 552-553.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

noncomputable section

open MeasureTheory

namespace PDE.DistributionTheory

variable {n : ℕ}

/-- The dilation field has one continuous derivative when the scalar field has two. -/
private theorem contDiff_dilation {u : ℝ^n → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (fun x ↦ advectiveDerivative id u x) := by
  simp only [advectiveDerivative_eq_sum_mul_partialDeriv, id_eq]
  apply ContDiff.sum
  intro i _
  exact (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i).contDiff.mul
    (contDiff_partialDeriv_of_succ (m := 1) hu)

/-- The dilation derivative vanishes off the original topological support. -/
private theorem hasCompactSupport_dilation {u : ℝ^n → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (fun x ↦ advectiveDerivative id u x) := by
  apply hu.mono'
  intro x hx
  by_contra hxt
  have hzero : advectiveDerivative id u x = 0 := by
    simp only [advectiveDerivative, fderiv_of_notMem_tsupport ℝ hxt, zero_apply]
  exact hx hzero

/-- Integration of `x · Dv` gives `-n ∫ v` for a compactly supported `C¹` scalar field.
The coordinate factors need no compact support; only the differentiated field does. -/
theorem integral_dilation_eq {v : ℝ^n → ℝ}
    (hv : ContDiff ℝ 1 v) (hcompact : HasCompactSupport v) :
    (∫ x, advectiveDerivative id v x) = -(n : ℝ) * ∫ x, v x := by
  have hterm (i : Fin n) : Integrable (fun x : ℝ^n ↦ x i * (∂[i] v) x) := by
    have hi := hcompact.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
    have hc : Continuous (fun x ↦ (∂[i] v) x) := by
      exact (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hprod : Continuous (fun x : ℝ^n ↦ x i * (∂[i] v) x) :=
      (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i).continuous.mul hc
    exact hprod.integrable_of_hasCompactSupport hi.mul_left
  have hcoord (i : Fin n) :
      (∫ x : ℝ^n, x i * (∂[i] v) x) = -∫ x, v x := by
    have hproj : ContDiff ℝ 1 (fun x : ℝ^n ↦ x i) :=
      (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i).contDiff
    have h := PDE.Analysis.integral_mul_partialDeriv_eq_neg (f := v) (g := fun x : ℝ^n ↦ x i) i
      hv hproj hcompact
    simp only [partialDeriv_coord, ite_true, mul_one] at h
    have hcomm : (∫ x : ℝ^n, (∂[i] v) x * x i) =
        ∫ x : ℝ^n, x i * (∂[i] v) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _
    rw [hcomm] at h
    linarith
  simp only [advectiveDerivative_eq_sum_mul_partialDeriv, id_eq]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hterm i)]
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Apply the dilation identity to the square of a compactly supported `C¹` field. -/
private theorem integral_dilation_mul_self {v : ℝ^n → ℝ}
    (hv : ContDiff ℝ 1 v) (hcompact : HasCompactSupport v) :
    (∫ x, advectiveDerivative id v x * v x) = -(n : ℝ) / 2 * ∫ x, v x ^ 2 := by
  have hsquare : HasCompactSupport (fun x ↦ v x ^ 2) := by
    exact hcompact.comp_left (g := fun a : ℝ ↦ a ^ 2) (by simp)
  have h := integral_dilation_eq (hv.pow 2) hsquare
  have hderiv (x : ℝ^n) : advectiveDerivative id (fun y ↦ v y ^ 2) x =
      2 * (advectiveDerivative id v x * v x) := by
    simp only [pow_two, advectiveDerivative]
    rw [fderiv_fun_mul hv.differentiable_one.differentiableAt
      hv.differentiable_one.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, id_eq]
    ring
  simp_rw [hderiv] at h
  rw [integral_const_mul] at h
  linarith

/-- Differentiating the dilation derivative produces the original derivative and its dilation.
Symmetry of the `C²` Hessian changes the order of the two coordinate derivatives. -/
private theorem partialDeriv_dilation {u : ℝ^n → ℝ} (hu : ContDiff ℝ 2 u)
    (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y ↦ advectiveDerivative id u y)) x =
      (∂[i] u) x + advectiveDerivative id (fun y ↦ (∂[i] u) y) x := by
  rw [partialDeriv_advectiveDerivative i id u x contDiffAt_id hu.contDiffAt]
  simp only [id_eq, partialDeriv_coord, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [advectiveDerivative_eq_sum_mul_partialDeriv]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : ℝ ↦ x j * a) (partialDeriv_partialDeriv_comm i j hu x)

/-- The integrated Rellich identity for compactly supported `C²` functions on Euclidean space.
The Laplacian is `∑ᵢ ∂ᵢ²`, so the coefficient on the right is `(n - 2) / 2`.
Compact support removes the boundary flux without imposing a sign or a dimension restriction. -/
theorem integral_dilation_mul_laplacian_eq {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u) :
    (∫ x, advectiveDerivative id u x * laplacian u x) =
      ((n : ℝ) - 2) / 2 * ∫ x, ‖∇ u x‖ ^ 2 := by
  have hd (i : Fin n) : ContDiff ℝ 1 (fun x ↦ (∂[i] u) x) :=
    contDiff_partialDeriv_of_succ (m := 1) hu
  have hdc (i : Fin n) : HasCompactSupport (fun x ↦ (∂[i] u) x) := by
    simpa only [partialDeriv] using
      hcompact.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hm := contDiff_dilation hu
  have hmc := hasCompactSupport_dilation hcompact
  have hs (i : Fin n) : Integrable (fun x ↦ (∂[i] u) x ^ 2) := by
    have hc : Continuous (fun x : ℝ^n ↦ (∂[i] u) x ^ 2) := by
      have hbase : Continuous (fun x : ℝ^n ↦ (∂[i] u) x) := (hd i).continuous
      exact (continuous_pow 2).comp hbase
    have hsupport : HasCompactSupport (fun x : ℝ^n ↦ (∂[i] u) x ^ 2) :=
      (hdc i).comp_left (g := fun a : ℝ ↦ a ^ 2) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hsupport
  have hcross (i : Fin n) : Integrable
      (fun x ↦ advectiveDerivative id (fun y ↦ (∂[i] u) y) x * (∂[i] u) x) := by
    have hc : Continuous (fun x ↦ advectiveDerivative id (fun y ↦ (∂[i] u) y) x) := by
      exact ((hd i).continuous_fderiv one_ne_zero).clm_apply continuous_id
    exact (hc.mul (hd i).continuous).integrable_of_hasCompactSupport (hdc i).mul_left
  have hl (i : Fin n) : Integrable
      (fun x ↦ advectiveDerivative id u x * (∂[i] (fun y ↦ (∂[i] u) y)) x) := by
    have hc : Continuous (fun x : ℝ^n ↦ (∂[i] (fun y ↦ (∂[i] u) y)) x) :=
      (contDiff_partialDeriv_of_succ (m := 0) (i := i) (hd i)).continuous
    have hprod : Continuous
        (fun x : ℝ^n ↦ advectiveDerivative id u x *
          (∂[i] (fun y ↦ (∂[i] u) y)) x) :=
      hm.continuous.mul hc
    exact hprod.integrable_of_hasCompactSupport hmc.mul_right
  have hi (i : Fin n) :
      (∫ x, advectiveDerivative id u x * (∂[i] (fun y ↦ (∂[i] u) y)) x) =
        ((n : ℝ) - 2) / 2 * ∫ x, (∂[i] u) x ^ 2 := by
    have hibp := PDE.Analysis.integral_mul_partialDeriv_eq_neg
      (f := fun x ↦ advectiveDerivative id u x) (g := fun x ↦ (∂[i] u) x) i
      hm (hd i) hmc
    have heq : (fun x ↦ (∂[i] (fun y ↦ advectiveDerivative id u y)) x *
        (∂[i] u) x) = fun x ↦ (∂[i] u) x ^ 2 +
        advectiveDerivative id (fun y ↦ (∂[i] u) y) x * (∂[i] u) x := by
      funext x
      rw [partialDeriv_dilation hu]
      ring
    rw [heq, integral_add (hs i) (hcross i)] at hibp
    rw [integral_dilation_mul_self (hd i) (hdc i)] at hibp
    linarith
  have hnorm (x : ℝ^n) : ‖∇ u x‖ ^ 2 = ∑ i : Fin n, (∂[i] u) x ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gradient_apply_eq_partialDeriv]
  simp only [laplacian, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hl i)]
  simp_rw [hi, hnorm]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hs i), Finset.mul_sum]

/-- Testing the Laplacian against a compactly supported `C²` function gives its negative
Dirichlet energy. Integrability follows from the same regularity and support assumptions. -/
theorem integral_mul_laplacian_self_eq {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u) :
    (∫ x, u x * laplacian u x) = -∫ x, ‖∇ u x‖ ^ 2 := by
  have hd (i : Fin n) : ContDiff ℝ 1 (fun x ↦ (∂[i] u) x) :=
    contDiff_partialDeriv_of_succ (m := 1) hu
  have hdc (i : Fin n) : HasCompactSupport (fun x ↦ (∂[i] u) x) := by
    simpa only [partialDeriv] using
      hcompact.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hl (i : Fin n) : Integrable
      (fun x ↦ u x * (∂[i] (fun y ↦ (∂[i] u) y)) x) := by
    have hc : Continuous (fun x : ℝ^n ↦ (∂[i] (fun y ↦ (∂[i] u) y)) x) :=
      (contDiff_partialDeriv_of_succ (m := 0) (i := i) (hd i)).continuous
    have hprod : Continuous
        (fun x : ℝ^n ↦ u x * (∂[i] (fun y ↦ (∂[i] u) y)) x) :=
      hu.continuous.mul hc
    exact hprod.integrable_of_hasCompactSupport hcompact.mul_right
  have hs (i : Fin n) : Integrable (fun x ↦ (∂[i] u) x ^ 2) := by
    have hc : Continuous (fun x : ℝ^n ↦ (∂[i] u) x ^ 2) := by
      have hbase : Continuous (fun x : ℝ^n ↦ (∂[i] u) x) := (hd i).continuous
      exact (continuous_pow 2).comp hbase
    have hsupport : HasCompactSupport (fun x : ℝ^n ↦ (∂[i] u) x ^ 2) :=
      (hdc i).comp_left (g := fun a : ℝ ↦ a ^ 2) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hsupport
  have hi (i : Fin n) :
      (∫ x, u x * (∂[i] (fun y ↦ (∂[i] u) y)) x) =
        -∫ x, (∂[i] u) x ^ 2 := by
    have hibp := PDE.Analysis.integral_mul_partialDeriv_eq_neg
      (f := u) (g := fun x ↦ (∂[i] u) x) i
      (hu.of_le (by norm_num)) (hd i) hcompact
    simpa only [pow_two] using hibp
  have hnorm (x : ℝ^n) : ‖∇ u x‖ ^ 2 = ∑ i : Fin n, (∂[i] u) x ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gradient_apply_eq_partialDeriv]
  simp only [laplacian, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hl i)]
  simp_rw [hi, hnorm]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hs i), Finset.sum_neg_distrib]

end PDE.DistributionTheory

end

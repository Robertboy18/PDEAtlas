/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Current
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# The divergence of the scaling current

Differentiating the current leaves its multiplier times the wave residual
and a scalar bulk term. At weight `(n-1)/2`, the quadratic derivative terms
cancel. No equation is assumed in this identity.

With the weight `(n-1)/2` and the quintic potential in three dimensions, the identity applied to a
solution of the equation is the Morawetz-type identity (6) of the proof of Evans, §12.4, Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, equation (6).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- Differentiate the dilation multiplier using the second partial derivatives. -/
theorem partialDeriv_scalingMultiplier (a : ℝ) (c : ℝ^(n + 1)) {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u p) (j : Fin (n + 1)) :
    (∂[j] (scalingMultiplier a c u)) p = (1 + a) * (∂[j] u) p + ∑ k : Fin (n + 1),
      (p k - c k) * (∂[j] (∂[k] u)) p := by
  classical
  have hd := hu.differentiableAt (by norm_num)
  have hpartial (k : Fin (n + 1)) :=
    (PDE.contDiffAt_partialDeriv 1 hu k).differentiableAt one_ne_zero
  have hcoord (k : Fin (n + 1)) : DifferentiableAt ℝ (fun q : ℝ^(n + 1) ↦ q k - c k) p :=
    (EuclideanSpace.proj k : ℝ^(n + 1) →L[ℝ] ℝ).differentiableAt.sub_const _
  have hsum : DifferentiableAt ℝ
      (fun q : ℝ^(n + 1) ↦ ∑ k : Fin (n + 1), (q k - c k) * (∂[k] u) q) p :=
    DifferentiableAt.fun_sum fun k _ ↦ (hcoord k).mul (hpartial k)
  unfold scalingMultiplier
  rw [PDE.partialDeriv_add (i := j) hsum (hd.const_mul a)]
  rw [PDE.partialDeriv_sum Finset.univ (f := fun k q ↦ (q k - c k) * (∂[k] u) q)
    (fun k _ ↦ (hcoord k).mul (hpartial k)) j]
  have hc : (∂[j] (fun q ↦ a * u q)) p = a * (∂[j] u) p := by
    simpa only [smul_eq_mul] using (PDE.partialDeriv_const_smul a (i := j) (f := u) (x := p))
  rw [hc]
  have hterm (k : Fin (n + 1)) : (∂[j] (fun q ↦ (q k - c k) * (∂[k] u) q)) p =
        (if j = k then 1 else 0) * (∂[k] u) p +
          (p k - c k) * (∂[j] (∂[k] u)) p := by
    rw [PDE.partialDeriv_mul (hcoord k) (hpartial k)]
    rw [PDE.partialDeriv_sub (i := j) (f := fun q : ℝ^(n + 1) ↦ q k) (g := fun _ ↦ c k)
      (EuclideanSpace.proj k : ℝ^(n + 1) →L[ℝ] ℝ).differentiableAt
      (differentiableAt_const (c k)), PDE.partialDeriv_coord, PDE.partialDeriv_const, sub_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  cas

/-- The chain rule for the kinetic Lagrangian, retaining the potential derivative. -/
theorem partialDeriv_waveLagrangianDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hV : DifferentiableAt ℝ V (u p)) (hu : ContDiffAt ℝ 2 u p) (j : Fin (n + 1)) :
    (∂[j] (waveLagrangianDensity V u)) p = (∂[0] u) p * (∂[j] (∂[0] u)) p -
      (∑ i : Fin n, (∂[i.succ] u) p * (∂[j] (∂[i.succ] u)) p) - deriv V (u p) * (∂[j] u) p := by
  have hd := hu.differentiableAt (by norm_num)
  have hpartial (k : Fin (n + 1)) :=
    (PDE.contDiffAt_partialDeriv 1 hu k).differentiableAt one_ne_zero
  have hs : DifferentiableAt ℝ (fun q ↦ ∑ i : Fin n, (∂[i.succ] u) q ^ 2) p :=
    DifferentiableAt.fun_sum fun i _ ↦ (hpartial i.succ).pow 2
  have hp (k : Fin (n + 1)) : (∂[j] (fun q ↦ (∂[k] u) q ^ 2)) p =
        2 * ((∂[k] u) p * (∂[j] (∂[k] u)) p) := by
    simp only [pow_two]
    rw [PDE.partialDeriv_mul (hpartial k) (hpartial k)]
    cas
  have hbase : DifferentiableAt ℝ
      (fun q ↦ (∂[0] u) q ^ 2 - ∑ i : Fin n, (∂[i.succ] u) q ^ 2) p := by
    have hC : ContDiffAt ℝ 1 (fun q ↦ (∂[0] u) q ^ 2 - ∑ i : Fin n, (∂[i.succ] u) q ^ 2) p :=
      ((PDE.contDiffAt_partialDeriv 1 hu 0).pow 2).sub
        (ContDiffAt.sum fun i _ ↦ (PDE.contDiffAt_partialDeriv 1 hu i.succ).pow 2)
    exact hC.differentiableAt one_ne_zero
  have hkin : DifferentiableAt ℝ
      (fun q ↦ ((∂[0] u) q ^ 2 - ∑ i : Fin n, (∂[i.succ] u) q ^ 2) / 2) p := by
    simpa only [div_eq_mul_inv] using hbase.mul_const ((2 : ℝ)⁻¹)
  unfold waveLagrangianDensity
  rw [PDE.partialDeriv_sub (i := j)
    (f := fun q ↦ ((∂[0] u) q ^ 2 - ∑ i : Fin n, (∂[i.succ] u) q ^ 2) / 2)
    (g := fun q ↦ V (u q)) hkin (hV.comp p hd)]
  have hdiv : (∂[j] (fun q ↦ ((∂[0] u) q ^ 2 - ∑ i : Fin n, (∂[i.succ] u) q ^ 2) / 2)) p =
      ((∂[j] (fun q ↦ (∂[0] u) q ^ 2)) p -
        (∂[j] (fun q ↦ ∑ i : Fin n, (∂[i.succ] u) q ^ 2)) p) / 2 := by
    simp only [div_eq_mul_inv]
    rw [PDE.partialDeriv_mul (i := j)
      (f := fun q ↦ (∂[0] u) q ^ 2 - ∑ i : Fin n, (∂[i.succ] u) q ^ 2)
      (g := fun _ ↦ (2 : ℝ)⁻¹) hbase (differentiableAt_const _),
      PDE.partialDeriv_const, mul_zero, add_zero,
      PDE.partialDeriv_sub (i := j) (f := fun q ↦ (∂[0] u) q ^ 2)
        (g := fun q ↦ ∑ i : Fin n, (∂[i.succ] u) q ^ 2) ((hpartial 0).pow 2) hs]
  rw [hdiv, PDE.partialDeriv_sum Finset.univ
    (f := fun (i : Fin n) (q : ℝ^(n + 1)) ↦ (∂[i.succ] u) q ^ 2)
    (fun i _ ↦ (hpartial i.succ).pow 2) j]
  simp_rw [hp]
  rw [← Finset.mul_sum, PDE.partialDeriv_comp_real j hV hd]
  cas

private theorem scalingMultiplier_derivative_contraction {V : ℝ → ℝ} (a : ℝ) (c : ℝ^(n + 1))
    {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)} (hV : DifferentiableAt ℝ V (u p))
    (hu : ContDiffAt ℝ 2 u p) :
    (∂[0] (scalingMultiplier a c u)) p * (∂[0] u) p -
      (∑ i : Fin n, (∂[i.succ] (scalingMultiplier a c u)) p * (∂[i.succ] u) p) =
        (1 + a) * ((∂[0] u) p ^ 2 - ∑ i : Fin n, (∂[i.succ] u) p ^ 2) +
          ∑ j : Fin (n + 1), (p j - c j) *
            ((∂[j] (waveLagrangianDensity V u)) p + deriv V (u p) * (∂[j] u) p) := by
  have htime : (∑ k : Fin (n + 1), (p k - c k) * (∂[0] (∂[k] u)) p) * (∂[0] u) p =
        ∑ k : Fin (n + 1), (p k - c k) * ((∂[0] u) p * (∂[k] (∂[0] u)) p) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [PDE.partialDeriv_partialDeriv_comm_at 0 k hu]
    cas
  have hspace : (∑ i : Fin n, (∑ k : Fin (n + 1), (p k - c k) * (∂[i.succ] (∂[k] u)) p) *
          (∂[i.succ] u) p) = ∑ k : Fin (n + 1), (p k - c k) *
        (∑ i : Fin n, (∂[i.succ] u) p * (∂[k] (∂[i.succ] u)) p) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [PDE.partialDeriv_partialDeriv_comm_at i.succ k hu]
    cas
  have hsum : (∑ i : Fin n, ((1 + a) * (∂[i.succ] u) p +
        ∑ k : Fin (n + 1), (p k - c k) * (∂[i.succ] (∂[k] u)) p) * (∂[i.succ] u) p) =
        (1 + a) * (∑ i : Fin n, (∂[i.succ] u) p ^ 2) + ∑ i : Fin n,
            (∑ k : Fin (n + 1), (p k - c k) * (∂[i.succ] (∂[k] u)) p) *
              (∂[i.succ] u) p := by
    calc
      _ = ∑ i : Fin n, ((1 + a) * (∂[i.succ] u) p ^ 2 +
          (∑ k : Fin (n + 1), (p k - c k) * (∂[i.succ] (∂[k] u)) p) *
            (∂[i.succ] u) p) := by
        apply Finset.sum_congr rfl
        intro i _
        cas
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [partialDeriv_scalingMultiplier a c hu]
  rw [add_mul, hsum, htime, hspace]
  simp_rw [partialDeriv_waveLagrangianDensity hV hu, sub_add_cancel, mul_sub]
  rw [Finset.sum_sub_distrib]
  cas

/-- The scaling current identity in any spatial dimension, before choosing its
amplitude weight. It retains the wave residual, so it also applies to
forced equations. -/
theorem scalingCurrent_balance {V : ℝ → ℝ} (a : ℝ) (c : ℝ^(n + 1)) {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p) :
    (∂[0] (scalingCurrentDensity V a c u)) p -
      (∑ i : Fin n, (∂[i.succ] (scalingCurrentFlux V a c u i)) p) =
        scalingMultiplier a c u p * semilinearWaveOperator V u p +
          (a + 1 - ((n : ℝ) + 1) / 2) *
            ((∂[0] u) p ^ 2 - ∑ i : Fin n, (∂[i.succ] u) p ^ 2) +
          ((n : ℝ) + 1) * V (u p) - a * u p * deriv V (u p) := by
  have hm := (contDiffAt_scalingMultiplier a c hu).differentiableAt one_ne_zero
  have hL := (contDiffAt_waveLagrangianDensity hV hu).differentiableAt one_ne_zero
  have hpartial (k : Fin (n + 1)) :=
    (PDE.contDiffAt_partialDeriv 1 hu k).differentiableAt one_ne_zero
  have hcoord (k : Fin (n + 1)) : DifferentiableAt ℝ (fun q : ℝ^(n + 1) ↦ q k - c k) p :=
    (EuclideanSpace.proj k : ℝ^(n + 1) →L[ℝ] ℝ).differentiableAt.sub_const _
  have hcoordderiv (k : Fin (n + 1)) :
      (∂[k] (fun q : ℝ^(n + 1) ↦ q k - c k)) p = 1 := by
    rw [PDE.partialDeriv_sub (i := k) (f := fun q : ℝ^(n + 1) ↦ q k) (g := fun _ ↦ c k)
      (EuclideanSpace.proj k : ℝ^(n + 1) →L[ℝ] ℝ).differentiableAt
      (differentiableAt_const (c k)), PDE.partialDeriv_coord, PDE.partialDeriv_const]
    simp
  have ht : (∂[0] (scalingCurrentDensity V a c u)) p =
      (∂[0] (scalingMultiplier a c u)) p * (∂[0] u) p +
        scalingMultiplier a c u p * (∂[0] (∂[0] u)) p - (waveLagrangianDensity V u p +
            (p 0 - c 0) * (∂[0] (waveLagrangianDensity V u)) p) := by
    unfold scalingCurrentDensity
    rw [PDE.partialDeriv_sub (i := 0) (f := fun q ↦ scalingMultiplier a c u q * (∂[0] u) q)
      (g := fun q ↦ (q 0 - c 0) * waveLagrangianDensity V u q)
      (hm.mul (hpartial 0)) ((hcoord 0).mul hL),
      PDE.partialDeriv_mul hm (hpartial 0), PDE.partialDeriv_mul (hcoord 0) hL,
      hcoordderiv, one_mul]
  have hx (i : Fin n) : (∂[i.succ] (scalingCurrentFlux V a c u i)) p =
      (∂[i.succ] (scalingMultiplier a c u)) p * (∂[i.succ] u) p +
        scalingMultiplier a c u p * (∂[i.succ] (∂[i.succ] u)) p + (waveLagrangianDensity V u p +
            (p i.succ - c i.succ) * (∂[i.succ] (waveLagrangianDensity V u)) p) := by
    unfold scalingCurrentFlux
    rw [PDE.partialDeriv_add (i := i.succ)
      (f := fun q ↦ scalingMultiplier a c u q * (∂[i.succ] u) q)
      (g := fun q ↦ (q i.succ - c i.succ) * waveLagrangianDensity V u q)
      (hm.mul (hpartial i.succ)) ((hcoord i.succ).mul hL),
      PDE.partialDeriv_mul hm (hpartial i.succ), PDE.partialDeriv_mul (hcoord i.succ) hL,
      hcoordderiv, one_mul]
  have hflux : (∑ i : Fin n, (∂[i.succ] (scalingCurrentFlux V a c u i)) p) =
      (∑ i : Fin n, (∂[i.succ] (scalingMultiplier a c u)) p * (∂[i.succ] u) p) +
        scalingMultiplier a c u p * (∑ i : Fin n, (∂[i.succ] (∂[i.succ] u)) p) +
        ((n : ℝ) * waveLagrangianDensity V u p + ∑ i : Fin n, (p i.succ - c i.succ) *
            (∂[i.succ] (waveLagrangianDensity V u)) p) := by
    simp_rw [hx]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsource : (∑ j : Fin (n + 1), (p j - c j) *
        ((∂[j] (waveLagrangianDensity V u)) p + deriv V (u p) * (∂[j] u) p)) =
        (∑ j : Fin (n + 1), (p j - c j) * (∂[j] (waveLagrangianDensity V u)) p) +
          deriv V (u p) * (scalingMultiplier a c u p - a * u p) := by
    unfold scalingMultiplier
    rw [add_sub_cancel_right]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    cas
  have hc := scalingMultiplier_derivative_contraction a c (hV.differentiableAt one_ne_zero) hu
  rw [hsource, Fin.sum_univ_succ] at hc
  rw [ht, hflux]
  unfold semilinearWaveOperator waveOperator waveLagrangianDensity at *
  linear_combination hc

/-- The Morawetz weight cancels both quadratic derivative terms. The remaining
bulk term depends only on the potential and its derivative. -/
theorem morawetzCurrent_balance {V : ℝ → ℝ} (c : ℝ^(n + 1)) {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hV : ContDiffAt ℝ 1 V (u p)) (hu : ContDiffAt ℝ 2 u p) :
    (∂[0] (scalingCurrentDensity V (((n : ℝ) - 1) / 2) c u)) p -
      (∑ i : Fin n,
        (∂[i.succ] (scalingCurrentFlux V (((n : ℝ) - 1) / 2) c u i)) p) =
        scalingMultiplier (((n : ℝ) - 1) / 2) c u p * semilinearWaveOperator V u p +
          ((n : ℝ) + 1) * V (u p) - ((n : ℝ) - 1) / 2 * u p * deriv V (u p) := by
  rw [scalingCurrent_balance _ c hV hu]
  have hcancel : ((n : ℝ) - 1) / 2 + 1 - ((n : ℝ) + 1) / 2 = 0 := by cas
  rw [hcancel, zero_mul, add_zero]

end WaveEquation

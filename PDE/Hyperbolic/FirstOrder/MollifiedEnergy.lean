/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Caratheodory.QuadraticEnergy
public import PDE.Hyperbolic.FirstOrder.MollifiedCauchy
public import PDE.Hyperbolic.FirstOrder.SobolevEnergy
public import PDE.Spaces.Sobolev.Approximation.Mollification.L2Regularity
public import PDE.Spaces.Sobolev.Calculus.Product.MatrixPairing

/-!
# Uniform L² energy for the mollified symmetric Cauchy problem

The constructed operator is `-∑ j, Jε (Bⱼ ∂ⱼ Jε ·)`. Its quadratic bound follows from
self-adjointness and contraction of the standard mollifier, its proved H¹ regularity, and
integration by parts for symmetric W¹,∞ coefficient matrices. The bound contains only
spatial coefficient derivatives and is independent of ε.

For coefficients continuous in time in the spatial L∞ operator norm, L² forcing, and L²
initial data, Picard existence supplies a regularized trajectory with the same energy bound
at every positive scale. The equation and initial value are part of the constructed
Carathéodory solution. The bound plays the role of the `L²` estimate (21), which Evans, §7.3.2,
proves for the viscous approximations (11) rather than for a mollified operator.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, proof of Theorem 2, steps 1 and 2,
  equations (18)-(21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
  SobolevSpace.Approximation
open scoped InnerProductSpace

variable {n m : ℕ}

/-- The entrywise L-infinity divergence bound used in the energy estimate.
This quantity depends only on the spatial coefficient derivatives and contains no scale. -/
def coefficientDerivativeBound
    (A : Fin n → Fin m → Fin m → W^{1,∞}((Set.univ : Set (ℝ^n)))) : ℝ :=
  ∑ j, ∑ p, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n j)‖

/-- The coefficient derivative bound is nonnegative. -/
theorem coefficientDerivativeBound_nonneg
    (A : Fin n → Fin m → Fin m → W^{1,∞}((Set.univ : Set (ℝ^n)))) :
    0 ≤ coefficientDerivativeBound A := by
  refine Finset.sum_nonneg fun j _ ↦ ?_
  exact Finset.sum_nonneg fun p _ ↦ Finset.sum_nonneg (fun q _ ↦ norm_nonneg _)

/-- Each coefficient entry differentiated in its transport direction contributes one
nonnegative L∞ norm to the divergence bound. -/
theorem coefficientDerivativeBound_entry_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}((Set.univ : Set (ℝ^n)))) (j : Fin n) (p q : Fin m) :
    ‖(A j p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n j)‖ ≤
      coefficientDerivativeBound A := by
  unfold coefficientDerivativeBound
  exact (Finset.single_le_sum (f := fun q ↦
    ‖(A j p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n j)‖)
    (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ q)).trans
    ((Finset.single_le_sum (f := fun p ↦ ∑ q : Fin m,
      ‖(A j p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n j)‖)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ p)).trans
      (Finset.single_le_sum (f := fun j ↦ ∑ p : Fin m, ∑ q : Fin m,
        ‖(A j p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n j)‖)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)))

/-- The constructed mollified principal operator has an epsilon-independent quadratic
energy bound for symmetric W1,infinity coefficient matrices.

The operator field is identified entrywise with the Sobolev coefficients. Mollifier
self-adjointness, coordinate commutation and weak derivatives are proved from the standard
kernel. -/
theorem mollifiedPrincipalOperator_quadratic_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (B : Fin n → Lp (ℝ^m →L[ℝ] ℝ^m) ∞ (volume : Measure (ℝ^n)))
    (hAB : ∀ j p q, (fun x ↦ B j x (EuclideanSpace.single q 1) p) =ᵐ[volume]
      ((A j p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1) : ℝ^n → ℝ))
    (hA : ∀ j p q, (A j p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1) =
      (A j q p : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1))
    {ε : ℝ} (hε : 0 < ε) (u : Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) :
    2 * ⟪mollifiedPrincipalOperator (standardMollifier n) hε B u, u⟫_ℝ ≤
      coefficientDerivativeBound A * ‖u‖ ^ 2 := by
  classical
  let J := mollifierL2CLM (E := ℝ^m) (standardMollifier n) hε
  let K := fun j ↦ mollifierDerivativeL2CLM (E := ℝ^m) (standardMollifier n) hε j
  let c := fun j ↦ ∑ p, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n j)‖
  obtain ⟨U, hbase, hderiv⟩ := exists_H1_coordinates_mollifierL2CLM (standardMollifier n) hε u
  have hnorm : (∑ p, ‖(U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)‖ ^ 2) =
      ‖J u‖ ^ 2 := sum_norm_sq_eq_of_ae_coordinates _ _ hbase
  have hcontract : ‖J u‖ ≤ ‖u‖ := by
    calc
      ‖J u‖ ≤ ‖J‖ * ‖u‖ := J.le_opNorm u
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right
        (norm_mollifierL2CLM_le (standardMollifier n) hε) (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  have hsq : ‖J u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg (J u), norm_nonneg u]
  have hc (j : Fin n) : 0 ≤ c j :=
    Finset.sum_nonneg (fun p _ ↦ Finset.sum_nonneg (fun q _ ↦ norm_nonneg _))
  have hrow (j : Fin n) : -⟪multiplicationL2CLM (B j) (K j u), J u⟫_ℝ ≤
        (1 / 2 : ℝ) * c j * ‖u‖ ^ 2 := by
    have hpair := inner_multiplicationL2CLM_eq_sum_of_ae_coordinates (B j)
      (fun p q ↦ (A j p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1))
      (fun q ↦ (U q : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n j))
      (fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))
      (K j u) (J u) (hAB j) (hderiv j) hbase
    have henergy := symmetric_matrix_transport_energy_le (A j) (hA j) j U
    dsimp only at henergy
    rw [← hpair, hnorm] at henergy
    exact henergy.trans (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hc j)))
  calc
    2 * ⟪mollifiedPrincipalOperator (standardMollifier n) hε B u, u⟫_ℝ =
        2 * ∑ j, -⟪multiplicationL2CLM (B j) (K j u), J u⟫_ℝ := by
      rw [mollifiedPrincipalOperator_apply, inner_neg_left, sum_inner]
      simp only [inner_standardMollifierL2CLM_left, Finset.sum_neg_distrib, J, K]
    _ ≤ 2 * ∑ j, (1 / 2 : ℝ) * c j * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hrow j)) (by norm_num)
    _ = coefficientDerivativeBound A * ‖u‖ ^ 2 := by
      simp only [coefficientDerivativeBound, ← Finset.sum_mul, ← Finset.mul_sum, c]
      ring

/-- Every positive mollification scale admits a constructed Cauchy trajectory with the same
L2 energy bound. The exponent depends only on a uniform bound for the spatial coefficient
derivatives, not on epsilon or the derivative-kernel operator norm.

Coefficients are continuous in time in the spatial L-infinity operator norm. Their entries
are symmetric W1,infinity functions at each time in the interval. This theorem concerns regularized
trajectories. -/
theorem exists_mollified_cauchy_with_uniform_energy
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (B : Fin n → ℝ → Lp (ℝ^m →L[ℝ] ℝ^m) ∞ (volume : Measure (ℝ^n))) (hB : ∀ j, Continuous (B j))
    {a b : ℝ} (hab : a ≤ b)
    (hAB : ∀ t ∈ Icc a b, ∀ j p q, (fun x ↦ B j t x (EuclideanSpace.single q 1) p) =ᵐ[volume]
      ((A t j p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1) : ℝ^n → ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1))
    {C : ℝ} (hC : 0 ≤ C) (hderiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (f : ℝ → Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) (hf : MemLp f 2 (volume.restrict (Icc a b)))
    (u₀ : Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : AffineCaratheodorySolutionOn
      (fun t ↦ mollifiedPrincipalOperator (standardMollifier n) hε (fun j ↦ B j t))
      f a b u₀,
      ∀ t ∈ Icc a b,
        ‖U.trajectory t‖ ^ 2 ≤
          (‖u₀‖ ^ 2 + ∫ s in a..b, ‖f s‖ ^ 2) * Real.exp ((C + 1) * (t - a)) := by
  obtain ⟨U⟩ := exists_mollified_cauchy_of_memLp (standardMollifier n) hε B hB hab f hf u₀
  refine ⟨U, U.norm_sq_le_mul_exp_of_quadratic_bound hab hf hC fun t ht v ↦ ?_⟩
  exact (mollifiedPrincipalOperator_quadratic_le (A t) (fun j ↦ B j t)
    (hAB t ht) (hA t ht) hε v).trans (mul_le_mul_of_nonneg_right (hderiv t ht) (sq_nonneg ‖v‖))

end PDE.Hyperbolic.FirstOrder

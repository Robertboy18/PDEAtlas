/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.Implicit.Localized
public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Coordinates

/-!
# Localized Sobolev parameters in normal inverse recovery

Only the cutoff times each parameter needs to be Sobolev. The original parameters are
`Lp` fields. The identity
`η(y) (P(y) - P(x)) = (ηP)(y) - (ηP)(x) - (η(y) - η(x)) P(x)`
gives the extra cutoff error explicitly. This is the form needed when tangential
derivatives have been recovered locally in a boundary chart.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Composition.Implicit

open Filter MeasureTheory Set
open SobolevSpace.Extension.Lp SobolevSpace.GraphSpace.DifferenceQuotient
open SobolevSpace.GraphSpace.Rellich
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

variable {n k : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Assemble the representatives of a finite family of scalar parameter fields. -/
def parameterValues (P : Fin k → DerivLp n p (HalfSpace.upper n)) (x : ℝ^n) : ℝ^k :=
  WithLp.toLp 2 (fun j ↦ P j x)

/-- The parameter bound after localization. Its last term is the cutoff commutator. -/
def localizedParameterBound (K C D : ℝ)
    (u : DerivLp n p (HalfSpace.upper n))
    (P : Fin k → DerivLp n p (HalfSpace.upper n))
    (W : Fin k → W^{1,p}(HalfSpace.upper n)) : ℝ :=
  K * (‖u‖ + ∑ j, ‖P j‖) +
    C * ((∑ j, ‖wkpCoordinateCLM (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
      ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap (W j))‖) +
      D * ∑ j, ‖P j‖)

/-- Local Sobolev regularity of the parameters gives the weighted coefficient error.
No derivative of either the original parameters or the unknown is assumed. -/
theorem exists_localized_parameterMajorant (hp : p ≠ ∞)
    (A : ℝ^n → ℝ^k → ℝ → ℝ) (K C : ℝ≥0)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^k, ∀ t : ℝ,
      ‖A y w t - A x z t‖ ≤
        K * ‖y - x‖ * (‖t‖ + ∑ j, ‖z j‖) + C * ∑ j, ‖w j - z j‖)
    (η : ℝ^n → ℝ) {D : ℝ≥0} (hη : LipschitzWith D η)
    (hηbound : ∀ x ∈ HalfSpace.upper n, |η x| ≤ 1)
    (u : DerivLp n p (HalfSpace.upper n))
    (P : Fin k → DerivLp n p (HalfSpace.upper n))
    (W : Fin k → W^{1,p}(HalfSpace.upper n))
    (hW : ∀ j, ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM (W j) x = η x * P j x)
    {h : ℝ} (hh : 0 < h) :
    ∃ r : DerivLp n p (HalfSpace.upper n),
      ‖r‖ ≤ localizedParameterBound K C D u P W ∧
        ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
          |η (x + coordinateStep (PDE.Common.lastIndex (n := n)) h)| *
            ‖A (x + coordinateStep (PDE.Common.lastIndex (n := n)) h)
                (parameterValues P (x + coordinateStep (PDE.Common.lastIndex (n := n)) h))
                (u x) - A x (parameterValues P x) (u x)‖ ≤ h * ‖r x‖ := by
  let B : Fin k → DerivLp n p (HalfSpace.upper n) := fun j ↦ wkpBaseCoordinateCLM (W j)
  let Q : Fin k → DerivLp n p (HalfSpace.upper n) := fun j ↦
    restrictDerivLp (subset_univ (HalfSpace.upper n))
      (differenceQuotientLp p (PDE.Common.lastIndex (n := n)) h
        (zeroExtendLp (HalfSpace.measurableSet_upper n) (B j)))
  let N : DerivLp n p (HalfSpace.upper n) → DerivLp n p (HalfSpace.upper n) :=
    lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : ℝ)‖ = 0)
  let S := Lp.sumNorms Finset.univ P
  let T := Lp.sumNorms Finset.univ Q
  let r := (K : ℝ) • (N u + S) + (C : ℝ) • (T + (D : ℝ) • S)
  have hN : (N u : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] fun x ↦ ‖u x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : ℝ)‖ = 0) u
  have hS : (S : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun x ↦ ∑ j, ‖P j x‖ := Lp.sumNorms_ae Finset.univ P
  have hT : (T : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun x ↦ ∑ j, ‖Q j x‖ := Lp.sumNorms_ae Finset.univ Q
  have hr : (r : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun x ↦ K * (‖u x‖ + ∑ j, ‖P j x‖) +
        C * ((∑ j, ‖Q j x‖) + D * ∑ j, ‖P j x‖) := by
    filter_upwards [Lp.coeFn_add ((K : ℝ) • (N u + S)) ((C : ℝ) • (T + (D : ℝ) • S)),
      Lp.coeFn_smul (K : ℝ) (N u + S), Lp.coeFn_smul (C : ℝ) (T + (D : ℝ) • S),
      Lp.coeFn_add (N u) S, Lp.coeFn_add T ((D : ℝ) • S),
      Lp.coeFn_smul (D : ℝ) S, hN, hS, hT]
      with x ha hk hc hnu ht hd hn hs hq
    simp only [r, ha, Pi.add_apply, hk, hc, Pi.smul_apply, smul_eq_mul,
      hnu, ht, hd, hn, hs, hq]
  have hnorm : ‖r‖ ≤ localizedParameterBound K C D u P W := by
    have hn : ‖N u‖ ≤ ‖u‖ := by
      simpa only [N, NNReal.coe_one, one_mul] using
        lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : ℝ)‖ = 0) u
    have hs : ‖S‖ ≤ ∑ j, ‖P j‖ := Lp.norm_sumNorms_le Finset.univ P
    have ht : ‖T‖ ≤ ∑ j, ‖wkpCoordinateCLM
        (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
        ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap (W j))‖ :=
      (Lp.norm_sumNorms_le Finset.univ Q).trans
        (Finset.sum_le_sum fun j _ ↦ norm_inward_differenceQuotient_le hp (W j) hh.le)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul_of_nonneg K.coe_nonneg, norm_smul_of_nonneg C.coe_nonneg, localizedParameterBound]
    gcongr
    · exact (norm_add_le _ _).trans (add_le_add hn hs)
    · refine (norm_add_le _ _).trans (add_le_add ht ?_)
      rw [norm_smul_of_nonneg D.coe_nonneg]
      gcongr
  refine ⟨r, hnorm, ?_⟩
  have hQ : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), ∀ j,
      Q j x = h⁻¹ * (B j (x + coordinateStep (PDE.Common.lastIndex (n := n)) h) - B j x) :=
    ae_all_iff.mpr fun j ↦ inward_differenceQuotient_apply_ae (B j) hh.le
  have hBW : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), ∀ j, B j x = η x * P j x :=
    ae_all_iff.mpr hW
  filter_upwards [hr, hQ, hBW, ae_add_normalStep_upper hh.le hBW,
    ae_restrict_mem (HalfSpace.measurableSet_upper n)] with x hrx hQx hBx hBy hx
  let y := x + coordinateStep (PDE.Common.lastIndex (n := n)) h
  change ∀ j, B j y = η y * P j y at hBy
  have hy : y ∈ HalfSpace.upper n := mapsTo_add_normalStep_upper hh.le hx
  have hdist : ‖y - x‖ = h := by
    simp only [y, add_sub_cancel_left, norm_coordinateStep, abs_of_pos hh]
  have hηdiff : |η y - η x| ≤ D * h := by
    simpa only [dist_eq_norm, hdist, Real.norm_eq_abs] using hη.dist_le_mul y x
  have hdiff (j : Fin k) :
      |η y| * ‖P j y - P j x‖ ≤ h * (‖Q j x‖ + D * ‖P j x‖) := by
    have halg : η y * (P j y - P j x) = (B j y - B j x) - (η y - η x) * P j x := by
      rw [hBy j, hBx j]
      ring
    have hstep : ‖B j y - B j x‖ = h * ‖Q j x‖ := by
      rw [hQx j, norm_mul, norm_inv, Real.norm_of_nonneg hh.le, ← mul_assoc,
        mul_inv_cancel₀ hh.ne', one_mul]
    calc
      |η y| * ‖P j y - P j x‖ = ‖(B j y - B j x) - (η y - η x) * P j x‖ := by
        simp only [← halg, norm_mul, Real.norm_eq_abs]
      _ ≤ h * ‖Q j x‖ + D * h * ‖P j x‖ := by
        refine (norm_sub_le _ _).trans ?_
        simp only [hstep, norm_mul, Real.norm_eq_abs]
        gcongr
      _ = _ := by ring
  have hsum : |η y| * (∑ j, ‖P j y - P j x‖) ≤
      h * ((∑ j, ‖Q j x‖) + D * ∑ j, ‖P j x‖) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ ↦ hdiff j
  have hv := mul_le_mul_of_nonneg_left
    (hvariation x hx y hy (parameterValues P x) (parameterValues P y) (u x)) (abs_nonneg (η y))
  rw [hdist, mul_add] at hv
  have hspatial : |η y| * ((K : ℝ) * h * (‖u x‖ + ∑ j, ‖P j x‖)) ≤
      K * h * (‖u x‖ + ∑ j, ‖P j x‖) :=
    mul_le_of_le_one_left (by positivity) (hηbound y hy)
  rw [hrx, Real.norm_of_nonneg (show 0 ≤
    (K : ℝ) * (‖u x‖ + ∑ j, ‖P j x‖) +
      C * ((∑ j, ‖Q j x‖) + D * ∑ j, ‖P j x‖) by positivity)]
  calc
    _ ≤ |η y| * (K * h * (‖u x‖ + ∑ j, ‖P j x‖)) +
        |η y| * (C * ∑ j, ‖P j y - P j x‖) := hv
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hsum C.coe_nonneg]

/-- Normal recovery from localized Sobolev parameters and localized Sobolev output.
Every error constant is expressed in terms of the given fields and coefficient bounds. -/
theorem exists_localized_normal_weakDerivative_of_sobolev_parameters
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (A : ℝ^n → ℝ^k → ℝ → ℝ) (K C : ℝ≥0) {m : ℝ} (hm : 0 < m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z : ℝ^k, ∀ s t : ℝ,
      m * ‖s - t‖ * ‖s - t‖ ≤ ⟪A x z s - A x z t, s - t⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^k, ∀ t : ℝ,
      ‖A y w t - A x z t‖ ≤
        K * ‖y - x‖ * (‖t‖ + ∑ j, ‖z j‖) + C * ∑ j, ‖w j - z j‖)
    (η : ℝ^n → ℝ) {D : ℝ≥0} (hη : LipschitzWith D η)
    (hηbound : ∀ x ∈ HalfSpace.upper n, |η x| ≤ 1)
    (u q U : DerivLp n p (HalfSpace.upper n))
    (P : Fin k → DerivLp n p (HalfSpace.upper n))
    (W : Fin k → W^{1,p}(HalfSpace.upper n))
    (Q : W^{1,p}(HalfSpace.upper n))
    (hW : ∀ j, ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM (W j) x = η x * P j x)
    (heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (parameterValues P x) (u x) = q x)
    (hU : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), U x = η x * u x)
    (hQ : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM Q x = η x * q x) :
    ∃ g : DerivLp n p (HalfSpace.upper n),
      ‖g‖ ≤
        (‖wkpCoordinateCLM (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
          ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap Q)‖ +
          localizedParameterBound K C D u P W + D * (‖q‖ + m * ‖u‖)) / m ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [PDE.Common.lastIndex (n := n)]
        (U : ℝ^n → ℝ) (g : ℝ^n → ℝ) :=
  exists_localized_normal_weakDerivative hp hp_top
    (fun x t ↦ A x (parameterValues P x) t) hm
    (fun x hx ↦ hmono x hx (parameterValues P x)) η hη u q U Q heq hU hQ
    (localizedParameterBound K C D u P W)
    (fun _ hh ↦ exists_localized_parameterMajorant hp_top A K C hvariation
      η hη hηbound u P W hW hh)

end SobolevSpace.GraphSpace.Composition.Implicit

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.WholeSpace.Hessian
public import PDE.Spaces.Sobolev.Fractional.Integer.Reverse
public import PDE.Spaces.Sobolev.Fractional.Integer.RealPart
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceL2

/-!
# The homogeneous Hessian estimate for real Sobolev rows

The integer/Fourier equivalence sends a real W²,² bundle to its complexified
base function. Uniqueness of weak derivatives identifies the second derivative
representatives and their trace. The whole-space homogeneous estimate therefore
bounds each real second derivative by the L² norm of the Laplacian.

This is a compatibility theorem for the two Sobolev models, not a
second construction of either model. No first derivative norm appears.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped BesselPotentialSpace ENNReal Distributions SchwartzMap LineDeriv Laplacian Sobolev

namespace PDE.Elliptic.WholeSpace

variable {n : ℕ}

/-- Each second row of a real whole-space W²,² function is bounded by the
norm of the sum of its diagonal second rows. The sum is the Laplacian
class; cancellations in it are retained. -/
theorem norm_second_row_le_laplacian
    (U : W^{2,2}((Set.univ : Set (ℝ^n)))) (i j : Fin n) :
    ‖(U : WkpAmbientOn n 2 2 Set.univ)
      (derivIndexOfList [i, j] (by norm_num))‖ ≤
      ‖∑ k : Fin n, (U : WkpAmbientOn n 2 2 Set.univ) (topPureDerivIndex n 2 k)‖ := by
  classical
  let z := ofWkpSpace U
  let z₀ : Lp ℂ 2 (volume : Measure (ℝ^n)) := toL2Fun (by norm_num : (0 : ℝ) ≤ 2) z
  let z₁ (k : Fin n) := lineDerivLinear n 2 (EuclideanSpace.single k (1 : ℝ)) z
  let z₂ (k l : Fin n) :=
    lineDerivLinear n (2 - 1) (EuclideanSpace.single l (1 : ℝ)) (z₁ k)
  let d₁ (k : Fin n) : Lp ℂ 2 (volume : Measure (ℝ^n)) := toL2Fun (by norm_num) (z₁ k)
  let d₂ (k l : Fin n) : Lp ℂ 2 (volume : Measure (ℝ^n)) := toL2Fun (by norm_num) (z₂ k l)
  have hz : IsRealL2 z₀ := isRealL2_toL2Fun_ofWkpSpace U
  have hbase : reOfL2 z₀ =ᵐ[domainMeasure n Set.univ] baseRepresentative U := by
    simpa only [domainMeasure, Measure.restrict_univ, coordFun, baseRepresentative] using
      reOfL2_toL2Fun_ofWkpSpace U
  have hd₂real (k l : Fin n) : IsRealL2 (d₂ k l) :=
    isRealL2_lineDeriv_of_isRealL2 (by norm_num) l (z₁ k)
      (isRealL2_lineDeriv_of_isRealL2 (by norm_num) k z hz)
  have hd₂row (k l : Fin n) :
      reOfL2 (d₂ k l) =ᵐ[domainMeasure n Set.univ]
        ((U : WkpAmbientOn n 2 2 Set.univ) (derivIndexOfList [k, l] (by norm_num)) : ℝ^n → ℝ) :=
    ((hasWeakDerivativeOn_reOfL2_two (by norm_num) k l z hz).congr_ae hbase .rfl).unique_ae
      isOpen_univ (U.property.hasWeakDerivativeOn_list [k, l] (by norm_num))
  have hd₁dist (k : Fin n) :
      (d₁ k : 𝓢'(ℝ^n, ℂ)) =
        ∂_{EuclideanSpace.single k (1 : ℝ)} (z₀ : 𝓢'(ℝ^n, ℂ)) := by
    rw [← toDistr_eq_toL2Fun (by norm_num) (z₁ k)]
    change BesselPotentialSpace.toDistr (lineDerivLinear n 2 _ z) = _
    rw [toDistr_lineDerivLinear, toDistr_eq_toL2Fun (by norm_num) z]
  have hd₂dist (k l : Fin n) :
      (d₂ k l : 𝓢'(ℝ^n, ℂ)) =
        ∂_{EuclideanSpace.single l (1 : ℝ)}
          (∂_{EuclideanSpace.single k (1 : ℝ)} (z₀ : 𝓢'(ℝ^n, ℂ))) := by
    rw [← toDistr_eq_toL2Fun (by norm_num) (z₂ k l)]
    change BesselPotentialSpace.toDistr (lineDerivLinear n (2 - 1) _ (z₁ k)) = _
    rw [toDistr_lineDerivLinear, toDistr_eq_toL2Fun (by norm_num) (z₁ k), hd₁dist]
  let F : Lp ℂ 2 (volume : Measure (ℝ^n)) := ∑ k : Fin n, d₂ k k
  have hΔ : Δ (z₀ : 𝓢'(ℝ^n, ℂ)) = (F : 𝓢'(ℝ^n, ℂ)) := by
    rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ)]
    simp only [EuclideanSpace.basisFun_apply]
    change (∑ k : Fin n, ∂_{EuclideanSpace.single k (1 : ℝ)}
      (∂_{EuclideanSpace.single k (1 : ℝ)} (z₀ : 𝓢'(ℝ^n, ℂ)))) =
        Lp.toTemperedDistributionCLM ℂ volume 2 (∑ k : Fin n, d₂ k k)
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (hd₂dist k k).symm
  let T : DerivLp n 2 Set.univ :=
    ∑ k : Fin n, (U : WkpAmbientOn n 2 2 Set.univ) (topPureDerivIndex n 2 k)
  have hdiag (k : Fin n) :
      (d₂ k k : ℝ^n → ℂ) =ᵐ[volume]
        fun x ↦ (((U : WkpAmbientOn n 2 2 Set.univ)
          (topPureDerivIndex n 2 k) : ℝ^n → ℝ) x : ℂ) := by
    have hr := hd₂row k k
    simp only [domainMeasure, Measure.restrict_univ] at hr
    filter_upwards [hr, ofReal_reOfL2_ae (hd₂real k k)] with x hx hreal
    exact hreal.trans (congrArg Complex.ofReal hx)
  have hFnorm : ‖F‖ = ‖T‖ := by
    rw [← wholeSpaceL2Equiv.norm_map T]
    apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
    all_goals
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun k ↦ d₂ k k),
        wholeSpaceL2Equiv_ae T,
        show (T : ℝ^n → ℝ) =ᵐ[volume] fun x ↦
            ∑ k : Fin n, ((U : WkpAmbientOn n 2 2 Set.univ)
              (topPureDerivIndex n 2 k) : ℝ^n → ℝ) x from
          by simpa only [T, domainMeasure, Measure.restrict_univ] using
            Lp.coeFn_fun_finsetSum Finset.univ
              (fun k ↦ (U : WkpAmbientOn n 2 2 Set.univ) (topPureDerivIndex n 2 k)),
        (ae_all_iff.mpr hdiag)] with x hFx hTx hsum hx
      rw [hFx, hTx, hsum]
      simp only [hx, ← Complex.ofReal_sum, Complex.norm_real, le_refl]
  obtain ⟨D, hD, hDnorm⟩ := exists_lp_second_derivative_norm_le_of_laplacian z₀ F hΔ
    (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
  have hDweak :=
    (hasWeakDerivativeOn_re_of_lineDeriv_eq i z₀ (d₁ i) (hd₁dist i)).append_single j
      (hasWeakDerivativeOn_re_of_lineDeriv_eq j (d₁ i) D
        (by rw [hd₁dist]; exact hD.symm))
  have hrow : ((U : WkpAmbientOn n 2 2 Set.univ)
      (derivIndexOfList [i, j] (by norm_num)) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ (D x).re := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      (U.property.hasWeakDerivativeOn_list [i, j] (by norm_num)).unique_ae isOpen_univ
        (hDweak.congr_ae hbase .rfl)
  calc
    _ = ‖wholeSpaceL2Equiv ((U : WkpAmbientOn n 2 2 Set.univ)
        (derivIndexOfList [i, j] (by norm_num)))‖ :=
      (wholeSpaceL2Equiv.norm_map _).symm
    _ ≤ ‖D‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [wholeSpaceL2Equiv_ae
        ((U : WkpAmbientOn n 2 2 Set.univ) (derivIndexOfList [i, j] (by norm_num))),
        hrow] with x hx hr
      rw [hx, hr]
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (D x)
    _ ≤ ‖F‖ := by simpa only [PiLp.norm_single, norm_one, one_mul] using hDnorm
    _ = _ := hFnorm

end PDE.Elliptic.WholeSpace

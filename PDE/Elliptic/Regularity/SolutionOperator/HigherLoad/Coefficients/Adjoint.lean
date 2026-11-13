/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts

/-!
# Formal adjoints of full coefficients

The formal adjoint transposes the principal matrix, negates the drift, and
subtracts the divergence of the drift from the potential. The weak
form identity follows from polarized Sobolev integration by parts. It holds
for every pair of `H¹₀` functions, without assuming classical
representatives or boundary derivatives of those functions.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Coefficients of the formal adjoint of a full divergence operator. -/
def formalAdjoint (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω) :
    SmoothFullCoefficients n Ω where
  principal x i j := P.principal x j i
  drift i x := -P.drift i x
  potential x := P.potential x - ∑ i, (∂[i] (P.drift i)) x
  principal_smooth k i j := P.principal_smooth k j i
  drift_smooth k i := (P.drift_smooth k i).neg hopen
  potential_smooth k := (P.potential_smooth k).sub
    (ContDiffUpToBoundary.sum Finset.univ
      (fun i _ ↦ (P.drift_smooth (k + 1) i).partialDeriv_of_succ hopen i) hopen) hopen

/-- The formal adjoint is the transpose of the weak form.
The drift correction is derived by weak integration by parts. -/
theorem form_formalAdjoint
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (u v : H¹₀(Ω)) :
    (P.formalAdjoint hopen).form hopen hbounded u v = P.form hopen hbounded v u := by
  let a (i j : Fin n) := (P.principal_smooth 0 i j).toLp hopen hbounded ∞
  let b (i : Fin n) := (P.drift_smooth 0 i).toLp hopen hbounded ∞
  let d (i : Fin n) :=
    ((P.drift_smooth 1 i).partialDeriv_of_succ hopen i).toLp hopen hbounded ∞
  let c := (P.potential_smooth 0).toLp hopen hbounded ∞
  let Q := P.formalAdjoint hopen
  have hparts (i : Fin n) :
      ⟪b i • derivCoordCLM i u, baseCoordCLM v⟫_ℝ +
        ⟪b i • derivCoordCLM i v, baseCoordCLM u⟫_ℝ =
          -⟪d i • baseCoordCLM u, baseCoordCLM v⟫_ℝ := by
    let B := (P.drift_smooth 1 i).toWkpSpaceOn hopen hbounded ∞
    have hbase : (B : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) = b i :=
      Lp.ext (((P.drift_smooth 1 i).toWkpSpaceOn_base_ae hopen hbounded ∞).trans
        ((P.drift_smooth 0 i).toLp_coeFn hopen hbounded ∞).symm)
    have hderiv : (B : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = d i := by
      apply Lp.ext
      have h := (P.drift_smooth 1 i).toWkpSpaceOn_apply_ae hopen hbounded ∞
        (singleDerivIndex n i)
      simp only [singleDerivIndex_toList, iteratedPartialDeriv] at h
      exact h.trans (((P.drift_smooth 1 i).partialDeriv_of_succ hopen i).toLp_coeFn
        hopen hbounded ∞).symm
    simpa only [hbase, hderiv, baseCoordCLM_apply, derivCoordCLM_apply] using
      inner_mul_deriv_add_inner_mul_deriv_H10 hopen B i u.val v
  have hbneg (i : Fin n) (f : DerivLp n 2 Ω) :
      mulLpLeft ((Q.drift_smooth 0 i).toLp hopen hbounded ∞) f = -(b i • f) := by
    apply Lp.ext
    filter_upwards [
      mulLpLeft_apply_ae ((Q.drift_smooth 0 i).toLp hopen hbounded ∞) f,
      (Q.drift_smooth 0 i).toLp_coeFn hopen hbounded ∞,
      (P.drift_smooth 0 i).toLp_coeFn hopen hbounded ∞,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (b i) f,
      Lp.coeFn_neg (b i • f)] with x hmul hQ hP hb hn
    rw [hmul, hQ, hn, Pi.neg_apply, hb]
    change -P.drift i x * f x = -(b i x * f x)
    rw [show b i x = P.drift i x from hP]
    ring
  have hcsub (f : DerivLp n 2 Ω) :
      mulLpLeft ((Q.potential_smooth 0).toLp hopen hbounded ∞) f =
        c • f - ∑ i, d i • f := by
    apply Lp.ext
    filter_upwards [
      mulLpLeft_apply_ae ((Q.potential_smooth 0).toLp hopen hbounded ∞) f,
      (Q.potential_smooth 0).toLp_coeFn hopen hbounded ∞,
      (P.potential_smooth 0).toLp_coeFn hopen hbounded ∞,
      ae_all_iff.mpr (fun i ↦
        ((P.drift_smooth 1 i).partialDeriv_of_succ hopen i).toLp_coeFn hopen hbounded ∞),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) c f,
      ae_all_iff.mpr (fun i ↦ Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (d i) f),
      Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin n ↦ d i • f),
      Lp.coeFn_sub (c • f) (∑ i, d i • f)] with x hmul hQ hP hd hc hdf hsum hsub
    rw [hmul, hQ, hsub, Pi.sub_apply, hc, hsum]
    change (P.potential x - ∑ i, (∂[i] (P.drift i)) x) * f x =
      c x * f x - ∑ i, (d i • f : DerivLp n 2 Ω) x
    rw [show c x = P.potential x from hP]
    change ∀ i, d i x = (∂[i] (P.drift i)) x at hd
    simp only [hdf, smul_eq_mul, Pi.mul_apply, hd, sub_mul, Finset.sum_mul]
  have hprincipal :
      (∑ i, ∑ j, ⟪a j i • derivCoordCLM j u, derivCoordCLM i v⟫_ℝ) =
        ∑ i, ∑ j, ⟪a i j • derivCoordCLM j v, derivCoordCLM i u⟫_ℝ := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [Lp.inner_lpSMul_left, real_inner_comm]
  have hsum := congrArg (fun f : Fin n → ℝ ↦ ∑ i, f i) (funext hparts)
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum
  change Q.form hopen hbounded u v = _
  simp only [form, fullDivergenceForm_apply, hbneg, hcsub, inner_neg_left,
    inner_sub_left, sum_inner, Finset.sum_neg_distrib]
  change (∑ i, ∑ j, ⟪a j i • derivCoordCLM j u, derivCoordCLM i v⟫_ℝ) -
      (∑ i, ⟪b i • derivCoordCLM i u, baseCoordCLM v⟫_ℝ) +
      (⟪c • baseCoordCLM u, baseCoordCLM v⟫_ℝ -
        ∑ i, ⟪d i • baseCoordCLM u, baseCoordCLM v⟫_ℝ) = _
  have hcinner : ⟪c • baseCoordCLM u, baseCoordCLM v⟫_ℝ =
      ⟪c • baseCoordCLM v, baseCoordCLM u⟫_ℝ := by
    rw [Lp.inner_lpSMul_left, real_inner_comm]
  rw [hprincipal, hcinner]
  change _ = (∑ i, ∑ j, ⟪a i j • derivCoordCLM j v, derivCoordCLM i u⟫_ℝ) +
    (∑ i, ⟪b i • derivCoordCLM i v, baseCoordCLM u⟫_ℝ) +
      ⟪c • baseCoordCLM v, baseCoordCLM u⟫_ℝ
  linarith only [hsum]

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

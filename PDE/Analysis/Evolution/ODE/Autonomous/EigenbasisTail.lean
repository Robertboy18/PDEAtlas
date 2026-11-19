/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.EquilibriumTail

/-!
# Equilibrium tail rigidity in eigenbasis coordinates

A continuous linear change of coordinates transports the trajectory equation and its
linearization. A finite real eigenbasis with positive eigenvalues supplies coercivity
in the Euclidean coordinate norm, even when the original linearization is nonsymmetric.
The negative-eigenvalue assertion follows by time reversal.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology RealInnerProductSpace

namespace PDE.Analysis.Evolution

section Coordinates

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Coercivity after a continuous linear change of coordinates excludes nonconstant
trajectories converging forward to the equilibrium. No isometry is required. -/
theorem eq_const_of_tendsto_atTop_of_conjugate_fderiv_coercive
    {F : E → E} {p : E} {v : ℝ → E} {c : ℝ} (R : E ≃L[ℝ] H)
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0) (hc : 0 < c)
    (hA : ∀ z, c * ‖z‖ ^ 2 ≤ ⟪z, R (fderiv ℝ F p (R.symm z))⟫)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (hlim : Tendsto v atTop (𝓝 p)) :
    v = fun _ ↦ p := by
  let G : H → H := fun z ↦ R (F (p + R.symm z))
  let w : ℝ → H := fun t ↦ R (v t - p)
  have hshift : ContDiffAt ℝ 1 (fun z : H ↦ p + R.symm z) 0 :=
    contDiffAt_const.add R.symm.contDiff.contDiffAt
  have hFp : ContDiffAt ℝ 1 F (p + R.symm 0) := by simpa using hF
  have hG : ContDiffAt ℝ 1 G 0 :=
    R.contDiff.contDiffAt.comp 0 (hFp.comp 0 hshift)
  have hshiftD : HasFDerivAt (fun z : H ↦ p + R.symm z)
      R.symm.toContinuousLinearMap 0 :=
    R.symm.hasFDerivAt.const_add p
  have hGD : HasFDerivAt G
      (R.toContinuousLinearMap.comp ((fderiv ℝ F p).comp
        R.symm.toContinuousLinearMap)) 0 := by
    have hDF : HasFDerivAt F (fderiv ℝ F p) (p + R.symm 0) := by
      simpa using (hF.differentiableAt one_ne_zero).hasFDerivAt
    exact R.hasFDerivAt.comp 0 (hDF.comp 0 hshiftD)
  have hw (t : ℝ) : HasDerivAt w (G (w t)) t := by
    simpa [Function.comp_def, G, w] using R.hasFDerivAt.comp_hasDerivAt t ((hv t).sub_const p)
  have hwlim : Tendsto w atTop (𝓝 0) := by
    simpa only [Function.comp_def, w, map_zero, sub_self] using
      R.continuous.continuousAt.tendsto.comp (hlim.sub_const p)
  have heq : w = fun _ ↦ 0 := by
    apply eq_const_of_tendsto_atTop_of_fderiv_coercive hG (by simp [G, hp]) hc
    · intro z
      simpa only [hGD.fderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe] using hA z
    · exact hw
    · exact hwlim
  funext t
  apply sub_eq_zero.mp
  apply R.injective
  simpa only [w, map_zero] using congrFun heq t

end Coordinates

section Eigenbasis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι] [Nonempty ι]

/-- A complete real eigenbasis with positive eigenvalues excludes a nonconstant
trajectory converging forward. The eigenbasis is not assumed orthonormal. -/
theorem eq_const_of_tendsto_atTop_of_eigenbasis_pos
    {F : E → E} {p : E} {v : ℝ → E} (b : Module.Basis ι ℝ E) {a : ι → ℝ}
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0)
    (hb : ∀ i, fderiv ℝ F p (b i) = a i • b i) (ha : ∀ i, 0 < a i)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (hlim : Tendsto v atTop (𝓝 p)) :
    v = fun _ ↦ p := by
  classical
  let := Fintype.ofFinite ι
  let R : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    (b.equivFun.trans (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm).toContinuousLinearEquiv
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min a
  apply eq_const_of_tendsto_atTop_of_conjugate_fderiv_coercive R hF hp (ha i₀) ?_ hv hlim
  intro z
  have hcoords (y : E) (i : ι) : R (fderiv ℝ F p y) i = a i * R y i := by
    have hrepr := b.sum_repr y
    rw [← hrepr, map_sum]
    simp [R, map_sum, map_smul, hb, Module.Basis.equivFun_apply,
      Finsupp.single_apply, mul_ite, mul_comm]
  have hdiag (i : ι) : R (fderiv ℝ F p (R.symm z)) i = a i * z i := by
    rw [hcoords, R.apply_symm_apply]
  rw [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hdiag]
  simp only [RCLike.inner_apply, conj_trivial]
  nlinarith [mul_le_mul_of_nonneg_right (hi₀ i) (sq_nonneg (z i))]

/-- A complete real eigenbasis with negative eigenvalues excludes a nonconstant
trajectory converging backward. No bound on excursions of the trajectory is assumed. -/
theorem eq_const_of_tendsto_atBot_of_eigenbasis_neg
    {F : E → E} {p : E} {v : ℝ → E} (b : Module.Basis ι ℝ E) {a : ι → ℝ}
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0)
    (hb : ∀ i, fderiv ℝ F p (b i) = a i • b i) (ha : ∀ i, a i < 0)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (hlim : Tendsto v atBot (𝓝 p)) :
    v = fun _ ↦ p := by
  have hD : HasFDerivAt (fun x ↦ -F x) (-fderiv ℝ F p) p :=
    (hF.differentiableAt one_ne_zero).hasFDerivAt.neg
  have heq : (fun t ↦ v (-t)) = fun _ : ℝ ↦ p := by
    apply eq_const_of_tendsto_atTop_of_eigenbasis_pos b (a := fun i ↦ -a i) hF.neg
      (by simp only [hp, neg_zero])
    · intro i
      simp only [hD.fderiv, neg_apply, hb, neg_smul]
    · exact fun i ↦ neg_pos.mpr (ha i)
    · intro t
      simpa only [Function.comp_def, neg_one_smul] using (hv (-t)).scomp t (hasDerivAt_neg t)
    · exact hlim.comp tendsto_neg_atTop_atBot
  funext t
  simpa only [neg_neg] using congrFun heq (-t)

end Eigenbasis

end PDE.Analysis.Evolution

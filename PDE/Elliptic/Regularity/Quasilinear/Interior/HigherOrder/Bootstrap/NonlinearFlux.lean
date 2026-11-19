/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.WeakFlux
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Coefficients
import PDE.Spaces.Sobolev.Calculus.Composition.Flux.L2
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The nonlinear flux and its differentiated equations

The weak solution's gradient determines an L² flux. A classical representative
with the same gradient therefore satisfies the same local distributional
equation. Differentiating that equation produces the Hessian coefficients
for each first derivative of the representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped Sobolev ENNReal NNReal RealInnerProductSpace Gradient

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} {Ω : Set ℝ^n}

/-- A smooth density has a smooth gradient. -/
theorem contDiff_infty_gradient {L : ℝ^n → ℝ} (hL : ContDiff ℝ (⊤ : ℕ∞) L) :
    ContDiff ℝ (⊤ : ℕ∞) (∇ L) := by
  let R := (InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.comp (hL.fderiv_right (by simp))

/-- The Hessian entries used by the autonomous system are smooth in the
gradient variable. The change from a Euclidean tuple to a finite function
is a continuous linear equivalence. -/
theorem contDiff_infty_hessianEntry {L : ℝ^n → ℝ}
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Fin n → ℝ ↦ jacobianMatrix (∇ L) (WithLp.toLp 2 p) i j) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun p ↦ jacobianMatrix (∇ L) p i j) := by
    apply contDiff_infty.mpr
    intro m
    exact contDiff_pi.mp (contDiff_pi.mp
      (contDiff_jacobianMatrix (r := m)
        ((contDiff_infty_gradient hL).of_le (by simp))) i) j
  exact hh.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.contDiff

/-- The original H¹ weak equation transfers to the nonlinear flux of any
representative with the same gradient almost everywhere. -/
theorem hasZeroWeakDivergenceOn_gradientDensity
    (hb : Bornology.IsBounded Ω) {L : ℝ^n → ℝ} (hL : ContDiff ℝ 2 L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    (u : H¹(Ω))
    (hu : ∀ w : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (w : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0)
    {v : ℝ^n → ℝ}
    (hgrad : (∇ v : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u) :
    HasZeroWeakDivergenceOn Ω (fun i x ↦ ∇ L (∇ v x) i) := by
  obtain ⟨q, hq, hpair⟩ := exists_L2_flux_pairing_of_lipschitz hb
    (lipschitzWith_gradient_of_hessian_bound hL hbound) u
  apply hasZeroWeakDivergenceOn_of_pairing q
  · intro i
    filter_upwards [hq, Lp.euclideanTuple_apply_ae q, hgrad] with x hqx htx hgx
    exact (htx i).symm.trans
      (congrArg (fun p : ℝ^n ↦ p i) (hqx.symm.trans (congrArg (∇ L) hgx.symm)))
  · intro w
    rw [← (hpair w).2, hu w]

/-- Every first derivative of a C² solution satisfies the linearized
weak equation, with the Hessian evaluated at its classical gradient. -/
theorem hasZeroWeakDivergenceOn_linearized_gradientDensity
    (hΩ : IsOpen Ω) {L : ℝ^n → ℝ} (hL : ContDiff ℝ 2 L)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hQ : HasZeroWeakDivergenceOn Ω (fun i x ↦ ∇ L (∇ v x) i))
    (k : Fin n) :
    HasZeroWeakDivergenceOn Ω (fun i x ↦
      ∑ j, jacobianMatrix (∇ L) (∇ v x) i j * (∂[j] (∂[k] v)) x) := by
  have hg : ContDiffOn ℝ 1 (∇ v) Ω := by
    apply contDiffOn_piLp' 2
    intro i x hx
    simpa only [gradient_apply_eq_partialDeriv, Nat.cast_one] using
      (contDiffAt_partialDeriv 1 (hv.contDiffAt (hΩ.mem_nhds hx)) i).contDiffWithinAt
  have hA := contDiff_gradient_of_contDiff_two hL
  have hAc (i : Fin n) : ContDiff ℝ 1 (fun p ↦ ∇ L p i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hA
  apply (hQ.partialDeriv hΩ (fun i ↦ (hAc i).comp_contDiffOn hg) k).congr hΩ
  intro i x hx
  rw [partialDeriv_comp k (fun p ↦ ∇ L p i) (∇ v) x
    ((hAc i).differentiable_one _)
    ((hg.contDiffAt (hΩ.mem_nhds hx)).differentiableAt_one)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [gradient_apply_eq_partialDeriv]
  rw [partialDeriv_partialDeriv_comm_at k j (hv.contDiffAt (hΩ.mem_nhds hx))]
  change _ = (∂[j] (fun p ↦ ∇ L p i)) (∇ v x) * _
  simp only [gradient_apply_eq_partialDeriv]

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.Translation

/-!
# The energy–momentum tensor

We use the convention `Tᵢⱼ = L δᵢⱼ - Σₖ L_{Pₖᵢ} ∂ⱼuₖ`, so its columns are the
Noether currents of coordinate translations. Each column is divergence-free for
a classical Euler–Lagrange solution of an autonomous Lagrangian. More generally,
invariance in one coordinate direction conserves that column.

The proof specializes finite spatial translation invariance. It does not assume
the infinitesimal invariance equation or a divergence formula for the tensor.
Up to the overall sign, the column identity is Evans, §8.6.2, Example 1, equation (9),
which is stated there for scalar fields.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.2, Example 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ}

/-- The energy–momentum tensor, with columns equal to spatial translation currents.
The sign convention is `L I - (D_P L)ᵀ Du`. -/
def energyMomentumTensor (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (u : ℝ^n → ℝ^m) (x : ℝ^n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ fieldDensity L u x * (1 : Matrix (Fin n) (Fin n) ℝ) i j -
    ∑ k, momentum L u k i x * jacobianMatrix u x k j

variable {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {u : ℝ^n → ℝ^m} {x : ℝ^n}

/-- The current of a coordinate translation is the corresponding energy–momentum
column at every differentiability point of the field. -/
theorem noetherCurrent_eq_energyMomentum_column
    (hu : DifferentiableAt ℝ u x) (j : Fin n) :
    noetherCurrent L u (fun y ↦ -fderiv ℝ u y (EuclideanSpace.single j 1))
      (fun _ ↦ EuclideanSpace.single j 1) x =
      WithLp.toLp 2 (fun i ↦ energyMomentumTensor L u x i j) := by
  ext i
  simp only [noetherCurrent, energyMomentumTensor, PiLp.add_apply, PiLp.smul_apply,
    PiLp.neg_apply, smul_eq_mul, jacobianMatrix_apply_eq_fderiv hu, mul_neg,
    Finset.sum_neg_distrib]
  simp only [PiLp.single_apply, Matrix.one_apply, eq_comm]
  abel

/-- Invariance of `L` under small translations in coordinate `j` conserves column `j`
of the energy–momentum tensor. Regularity is required only at the evaluated germs. -/
theorem divergence_energyMomentum_of_translation
    (hL : ContDiffAt ℝ 2
      (fun q : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L q.1 q.2.1 q.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x) (j : Fin n)
    (hinvariant : ∀ P z,
      (fun t : ℝ ↦ L P z (x + t • EuclideanSpace.single j 1)) =ᶠ[𝓝 0]
        (fun _ ↦ L P z x))
    (hEL : ∀ k, classicalEulerLagrange L u x k = 0) :
    ∇· (fun y ↦ WithLp.toLp 2 (fun i ↦ energyMomentumTensor L u y i j)) x = 0 := by
  have hcurrent : noetherCurrent L u
      (fun y ↦ -fderiv ℝ u y (EuclideanSpace.single j 1))
      (fun _ ↦ EuclideanSpace.single j 1) =ᶠ[𝓝 x]
      (fun y ↦ WithLp.toLp 2 (fun i ↦ energyMomentumTensor L u y i j)) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact noetherCurrent_eq_energyMomentum_column (hy.differentiableAt (by norm_num)) j
  rw [← hcurrent.divergence_eq]
  exact noether_spatial_translation hL hu (EuclideanSpace.single j 1) hinvariant hEL

/-- Every energy–momentum column of a classical Euler–Lagrange solution is conserved
when the Lagrangian is independent of space. No ambient `C²` extension is required. -/
theorem divergence_energyMomentum
    {L₀ : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ}
    (hL : ContDiffAt ℝ 2
      (fun q : Matrix (Fin m) (Fin n) ℝ × ℝ^m ↦ L₀ q.1 q.2)
      (jacobianMatrix u x, u x))
    (hu : ContDiffAt ℝ 2 u x)
    (hEL : ∀ k, classicalEulerLagrange (fun P z _ ↦ L₀ P z) u x k = 0)
    (j : Fin n) :
    ∇· (fun y ↦ WithLp.toLp 2
      (fun i ↦ energyMomentumTensor (fun P z _ ↦ L₀ P z) u y i j)) x = 0 := by
  apply divergence_energyMomentum_of_translation
    (hL.comp (jacobianMatrix u x, (u x, x))
      (contDiffAt_fst.prodMk contDiffAt_snd.fst)) hu j _ hEL
  exact fun _ _ ↦ Filter.EventuallyEq.rfl

end PDE.CalculusOfVariations.Noether

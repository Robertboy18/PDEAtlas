/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.Calculus

/-!
# Local energy identity for the classical wave equation

For a spacetime field `u`, the classical wave-energy density is

`e = (uₜ² + |Dₓu|²) / 2`.

We prove the pointwise factorization

`∂ₜ e - divₓ (uₜ Dₓu) = uₜ (uₜₜ - Δu)`.

The proof uses the product rule and equality of mixed partial derivatives. Integrated over a ball,
the identity gives the energy computations in the proofs of Evans, §2.4.3, Theorems 5 and 6.

Coordinate `0` of `ℝ^(n + 1)` is time and `i.succ` is the `i`th spatial coordinate. The wave
operator is `uₜₜ - Δu`, so a homogeneous wave has zero local energy production.

## Main results

* `classicalWaveEnergyDensity`, `classicalWaveEnergyFlux`: the energy density
  `(uₜ² + |Dₓu|²) / 2` and the flux components `uₜ ∂ᵢu`.
* `classicalWaveEnergyBalanceResidual_eq_mul_waveOperator`: for a field that is `C²` at `p`,
  `∂ₜ e - divₓ (uₜ Dₓu) = uₜ (uₜₜ - Δu)` at `p`.
* `classicalWaveEnergyBalanceResidual_eq_zero`: a classical homogeneous wave has zero local
  energy defect.
* `classicalWaveEnergyDensity_nonneg`, and the `contDiff` lemmas recording that forming the
  density and flux costs one derivative and forming the residual costs two.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3, proofs of Theorems 5 and 6, equation (46).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

namespace WaveEquation

open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- The spatial gradient of a spacetime field, with coordinate `0` omitted. -/
noncomputable def classicalWaveSpatialGradient (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 fun i ↦ (∂[i.succ] u) p

/-- The `i`th component of the spatial gradient is the partial derivative in the `i`th spatial
coordinate, which is spacetime coordinate `i.succ`. -/
@[simp]
theorem classicalWaveSpatialGradient_apply (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) (i : Fin n) :
    classicalWaveSpatialGradient (n := n) u p i = (∂[i.succ] u) p := by
  simp [classicalWaveSpatialGradient]

/-- Taking the spatial gradient lowers finite spacetime regularity by one
derivative. -/
theorem contDiff_classicalWaveSpatialGradient {m : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ (m + 1) u) : ContDiff ℝ m (classicalWaveSpatialGradient (n := n) u) :=
  (contDiff_piLp (p := (2 : ENNReal))).2 fun i ↦ by
    simpa only [classicalWaveSpatialGradient_apply] using
      PDE.contDiff_partialDeriv_of_succ (i := i.succ) hu

/-- Classical wave-energy density `(uₜ² + |Dₓu|²) / 2`. -/
noncomputable def classicalWaveEnergyDensity (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  (1 / 2 : ℝ) * (((∂[0] u) p) ^ 2 + ‖classicalWaveSpatialGradient (n := n) u p‖ ^ 2)

/-- The `i`th spatial component `uₜ uᵢ` of the classical wave-energy flux.

The same flux appears in semilinear wave equations because a potential changes
the energy density but contributes no spatial derivative to the local balance
law. -/
noncomputable def classicalWaveEnergyFlux (u : ℝ^(n + 1) → ℝ) (i : Fin n) (p : ℝ^(n + 1)) : ℝ :=
  (∂[0] u) p * (∂[i.succ] u) p

/-- Taking the classical wave-energy density lowers finite spacetime
regularity by one derivative. -/
theorem contDiffAt_classicalWaveEnergyDensity {m : ℕ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ (m + 1) u p) :
    ContDiffAt ℝ m (classicalWaveEnergyDensity (n := n) u) p := by
  have hpartial (j : Fin (n + 1)) := PDE.contDiffAt_partialDeriv m hu j
  have henergy : classicalWaveEnergyDensity (n := n) u =
      fun p ↦ (1 / 2 : ℝ) * (((∂[0] u) p) ^ 2 + ∑ i : Fin n, ((∂[i.succ] u) p) ^ 2) := by
    funext p
    simp [classicalWaveEnergyDensity, EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient]
  rw [henergy]
  exact contDiffAt_const.mul
    ((hpartial 0).pow 2 |>.add (ContDiffAt.sum fun i _ ↦ (hpartial i.succ).pow 2))

/-- Taking the classical wave-energy density lowers finite spacetime
regularity by one derivative. -/
theorem contDiff_classicalWaveEnergyDensity {m : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ (m + 1) u) : ContDiff ℝ m (classicalWaveEnergyDensity (n := n) u) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_classicalWaveEnergyDensity hu.contDiffAt

/-- Forming a spacetime wave-energy flux component lowers finite regularity by
one derivative. -/
theorem contDiffAt_classicalWaveEnergyFlux {m : ℕ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ (m + 1) u p) (i : Fin n) :
    ContDiffAt ℝ m (classicalWaveEnergyFlux (n := n) u i) p :=
  (PDE.contDiffAt_partialDeriv m hu 0).mul (PDE.contDiffAt_partialDeriv m hu i.succ)

/-- Forming a spacetime wave-energy flux component lowers finite regularity by
one derivative. -/
theorem contDiff_classicalWaveEnergyFlux {m : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ (m + 1) u) (i : Fin n) :
    ContDiff ℝ m (classicalWaveEnergyFlux (n := n) u i) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_classicalWaveEnergyFlux hu.contDiffAt i

/-- The pointwise defect in the classical wave-energy conservation law. -/
noncomputable def classicalWaveEnergyBalanceResidual (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  (∂[0] (classicalWaveEnergyDensity (n := n) u)) p -
    ∑ i : Fin n, (∂[i.succ] (classicalWaveEnergyFlux (n := n) u i)) p

/-- Forming the classical local energy residual loses two derivatives of the
spacetime field. -/
theorem contDiff_classicalWaveEnergyBalanceResidual {m : ℕ} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ (m + 1 + 1) u) :
    ContDiff ℝ m (classicalWaveEnergyBalanceResidual (n := n) u) :=
  (PDE.contDiff_partialDeriv_of_succ (contDiff_classicalWaveEnergyDensity hu)).sub
    (ContDiff.sum fun i _ ↦ PDE.contDiff_partialDeriv_of_succ
      (contDiff_classicalWaveEnergyFlux hu i))

/-- The classical local energy defect is `uₜ` times the wave operator.

This is the differential identity behind the computation (46) of Evans, §2.4.3. It uses
the product rule and Clairaut commutation of the mixed derivatives, but no PDE
hypothesis or integral identity. -/
theorem classicalWaveEnergyBalanceResidual_eq_mul_waveOperator {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u p) :
    classicalWaveEnergyBalanceResidual (n := n) u p = (∂[0] u) p * waveOperator (n := n) u p := by
  have hd (j : Fin (n + 1)) : DifferentiableAt ℝ (fun q ↦ (∂[j] u) q) p :=
    (PDE.contDiffAt_partialDeriv 1 hu j).differentiableAt one_ne_zero
  have henergy : classicalWaveEnergyDensity (n := n) u =
      fun q ↦ (1 / 2 : ℝ) • ((∂[0] u) q * (∂[0] u) q +
        ∑ i : Fin n, (∂[i.succ] u) q * (∂[i.succ] u) q) := by
    funext q
    rw [classicalWaveEnergyDensity, EuclideanSpace.real_norm_sq_eq]
    simp [pow_two]
  unfold classicalWaveEnergyBalanceResidual classicalWaveEnergyFlux
  rw [henergy, PDE.partialDeriv_const_smul,
    PDE.partialDeriv_add ((hd 0).fun_mul (hd 0)) (.fun_sum fun i _ ↦ (hd _).fun_mul (hd _)),
    PDE.partialDeriv_sum _ fun i _ ↦ (hd _).fun_mul (hd _)]
  simp only [waveOperator, PDE.partialDeriv_mul (hd _) (hd _),
    PDE.partialDeriv_partialDeriv_comm_at 0 (Fin.succ _) hu]
  rw [smul_add, Finset.smul_sum, mul_sub, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp only [smul_eq_mul]
    ring
  · exact Finset.sum_congr rfl fun _ _ ↦ by simp only [smul_eq_mul]; ring

/-- A classical homogeneous wave has zero pointwise energy-balance residual. -/
theorem classicalWaveEnergyBalanceResidual_eq_zero {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u p) (hwave : waveOperator (n := n) u p = 0) :
    classicalWaveEnergyBalanceResidual (n := n) u p = 0 := by
  rw [classicalWaveEnergyBalanceResidual_eq_mul_waveOperator hu, hwave, mul_zero]

/-- The classical wave-energy density is nonnegative. -/
theorem classicalWaveEnergyDensity_nonneg (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) :
    0 ≤ classicalWaveEnergyDensity (n := n) u p := by
  unfold classicalWaveEnergyDensity
  positivity

end WaveEquation

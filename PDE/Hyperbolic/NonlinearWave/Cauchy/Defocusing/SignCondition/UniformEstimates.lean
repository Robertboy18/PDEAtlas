/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Virial
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Approximation

/-!
# Uniform estimates for sign-preserving wave approximations

Physical energy controls the velocity for all time. The displacement equation then gives a common L²
time modulus and a bound on every finite time interval. The mixed pairing identity controls the
nonnegative reaction product with a constant independent of the Lipschitz constant of the truncated
reaction. These are the bounds (6)-(8) in steps 2-3 of the proof of Theorem 1 of Evans, §12.3.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, steps 2-3 of the proof of Theorem 1,
  equations (6)-(8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert InnerProductSpace Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

variable {n : ℕ} {N : General.Nonlinearity n}
  {x : H¹(ℝ^n) × DerivLp n 2 univ}
  {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- A velocity bound gives a Lipschitz displacement in L², directly from the PDE. -/
theorem lipschitzOnWith_displacement (hu : N.IsEnergySolution x u) {C : NNReal}
    (hv : ∀ t, 0 ≤ t → ‖(u t).2‖ ≤ C) :
    LipschitzOnWith C (fun t ↦ (energyTriple n).inclusion (u t).1) (Ici 0) := by
  exact (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ hu.hasDerivWithinAt_displacement ht) (fun t ht ↦ hv t ht)

/-- The full L² displacement grows at most linearly under a uniform velocity bound. -/
theorem norm_displacement_le (hu : N.IsEnergySolution x u) {C : ℝ}
    (hv : ∀ t, 0 ≤ t → ‖(u t).2‖ ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ‖(energyTriple n).inclusion (u t).1‖ ≤ ‖(energyTriple n).inclusion x.1‖ + t * C := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs ↦ hu.hasDerivWithinAt_displacement hs) (fun s hs ↦ hv s hs)
    (x := 0) (y := t) le_rfl ht
  rw [hu.initial, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht] at h
  have htriangle := norm_le_norm_sub_add ((energyTriple n).inclusion (u t).1)
    ((energyTriple n).inclusion x.1)
  linarith

/-- An upper physical-energy bound controls the velocity without a reaction norm. -/
theorem norm_velocity_le_of_energy_le {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hs : ∀ z, 0 ≤ z * f z) {z : H¹(ℝ^n) × DerivLp n 2 univ}
    {E : ℝ} (he : physicalEnergy f z ≤ E) : ‖z.2‖ ≤ Real.sqrt (2 * E) := by
  exact ((lipschitzNonlinearity hf hs).norm_velocity_le z).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left he (by norm_num)))

/-- The integral of u f(u) on a finite time interval is controlled solely by the
initial L² displacement and a physical-energy bound. In particular the same
constant works for every sign-preserving truncation. -/
theorem integral_reaction_self_le {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (hs : ∀ z, 0 ≤ z * f z) (hu : Cauchy.IsEnergySolution hf (reaction_zero hf.continuous hs) x u)
    {E T : ℝ} (he : ∀ t, 0 ≤ t → physicalEnergy f (u t) ≤ E) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ∫ y, (energyTriple n).inclusion (u t).1 y *
      f ((energyTriple n).inclusion (u t).1 y) ∂domainMeasure n univ) ≤
      2 * Real.sqrt (2 * E) *
        (‖(energyTriple n).inclusion x.1‖ + T * Real.sqrt (2 * E)) +
        T * Real.sqrt (2 * E) ^ 2 := by
  have hN := (isEnergySolution_lipschitzNonlinearity_iff hf hs x u).mpr hu
  have hv (t : ℝ) (ht : 0 ≤ t) : ‖(u t).2‖ ≤ Real.sqrt (2 * E) :=
    norm_velocity_le_of_energy_le hf hs (he t ht)
  have hq (t : ℝ) (ht : t ∈ Icc 0 T) : ‖(energyTriple n).inclusion (u t).1‖ ≤
        ‖(energyTriple n).inclusion x.1‖ + T * Real.sqrt (2 * E) :=
    (norm_displacement_le hN hv ht.1).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg _)))
  have h := integral_source_pairing_le hN hT (fun t ht ↦ hv t ht.1) hq
  simpa only [lipschitzNonlinearity, ContinuousMap.coe_mk, inner_reaction_self] using h

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.EnergyIdentity
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Local energy identity for semilinear wave equations

We prove the pointwise energy identity for

`uₜₜ - Δu + V'(u) = 0`.

For a `C¹` potential and a `C²` field, the local energy residual is the time
derivative of

`(uₜ² + |Dₓu|²) / 2 + V(u)`

minus the spatial divergence of the flux `uₜ Dₓu`. It is exactly `uₜ` times
the semilinear wave operator. The result is purely local.

With `f = V'`, the equation is (1) of Evans, §12.1, and `V` plays the role of Evans's primitive
`F`. The identity is the pointwise form of the computation of `Ė(t)` in the proof of Evans,
§12.1.1, Theorem 1, before the divergence term is integrated away.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1, equation (1); §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- The semilinear wave operator `uₜₜ - Δu + V'(u)`. -/
noncomputable def semilinearWaveOperator
    (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) : ℝ :=
  waveOperator (n := n) u p + deriv V (u p)

/-- The semilinear wave-energy density `(uₜ² + |Dₓu|²) / 2 + V(u)`. -/
noncomputable def semilinearWaveEnergyDensity
    (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) : ℝ :=
  classicalWaveEnergyDensity (n := n) u p + V (u p)

/-- The pointwise defect in the semilinear local energy conservation law.

The decomposition into the classical residual and the potential-energy time
derivative makes the chain rule explicit. -/
noncomputable def semilinearWaveEnergyBalanceResidual
    (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) : ℝ :=
  classicalWaveEnergyBalanceResidual (n := n) u p +
    (∂[0] (fun q ↦ V (u q))) p

/-- Forming the semilinear local energy residual loses two derivatives of the
field and one derivative of the potential. -/
theorem contDiff_semilinearWaveEnergyBalanceResidual {m : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ (m + 1) V) (hu : ContDiff ℝ (m + 1 + 1) u) :
    ContDiff ℝ m (semilinearWaveEnergyBalanceResidual (n := n) V u) := by
  have hpotential : ContDiff ℝ (m + 1) (fun p ↦ V (u p)) :=
    hV.comp (hu.of_le (by norm_num))
  have hpotentialTime : ContDiff ℝ m (fun p ↦ (∂[0] (fun q ↦ V (u q))) p) :=
    PDE.contDiff_partialDeriv_of_succ (n := n + 1) (m := m) (i := 0) hpotential
  unfold semilinearWaveEnergyBalanceResidual
  exact (contDiff_classicalWaveEnergyBalanceResidual (n := n) hu).add hpotentialTime

/-- The energy residual of a C² field is continuous on its open regularity domain. -/
theorem continuousOn_semilinearWaveEnergyBalanceResidual {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {S : Set (ℝ^(n + 1))} (hV : ContDiff ℝ 1 V) (hu : ContDiffOn ℝ 2 u S) (hS : IsOpen S) :
    ContinuousOn (semilinearWaveEnergyBalanceResidual V u) S := by
  intro p hp
  have hup := hu.contDiffAt (hS.mem_nhds hp)
  have hP : ContDiffAt ℝ 1 (classicalWaveEnergyDensity u) p :=
    contDiffAt_classicalWaveEnergyDensity hup
  have hQ (i : Fin n) : ContDiffAt ℝ 1 (classicalWaveEnergyFlux u i) p :=
    contDiffAt_classicalWaveEnergyFlux hup i
  have hpot : ContDiffAt ℝ 1 (fun q ↦ V (u q)) p :=
    hV.contDiffAt.comp p (hup.of_le (by norm_num))
  exact (((hP.continuousAt_partialDeriv 0).sub
    (tendsto_finsetSum _ fun i _ ↦ (hQ i).continuousAt_partialDeriv i.succ)).add
      (hpot.continuousAt_partialDeriv 0)).continuousWithinAt

/-- Forming the semilinear wave-energy density loses one derivative of the
field locally and preserves the available regularity of the potential. -/
theorem contDiffAt_semilinearWaveEnergyDensity {m : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiffAt ℝ m V (u p)) (hu : ContDiffAt ℝ (m + 1) u p) :
    ContDiffAt ℝ m (semilinearWaveEnergyDensity (n := n) V u) p := by
  unfold semilinearWaveEnergyDensity
  exact (contDiffAt_classicalWaveEnergyDensity (n := n) hu).add
    (hV.comp p (hu.of_le (by exact_mod_cast Nat.le_succ m)))

/-- Forming the semilinear wave-energy density loses one derivative of the
field and preserves the available regularity of the potential. -/
theorem contDiff_semilinearWaveEnergyDensity {m : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ m V) (hu : ContDiff ℝ (m + 1) u) :
    ContDiff ℝ m (semilinearWaveEnergyDensity (n := n) V u) := by
  unfold semilinearWaveEnergyDensity
  exact (contDiff_classicalWaveEnergyDensity (n := n) hu).add
    (hV.comp (hu.of_le (by exact_mod_cast Nat.le_succ m)))

/-- The local residual is the time derivative of the energy density minus
the spatial divergence of the energy flux. -/
theorem semilinearWaveEnergyBalanceResidual_eq_partialDeriv_sub_sum {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiff ℝ 1 V) (hu : ContDiffAt ℝ 2 u p) :
    semilinearWaveEnergyBalanceResidual (n := n) V u p = (∂[0]
      (semilinearWaveEnergyDensity (n := n) V u)) p - ∑ i : Fin n,
      (∂[i.succ] (classicalWaveEnergyFlux (n := n) u i)) p := by
  have hclassical : DifferentiableAt ℝ (classicalWaveEnergyDensity (n := n) u) p :=
    (contDiffAt_classicalWaveEnergyDensity (n := n) hu).differentiableAt one_ne_zero
  have hpotential : DifferentiableAt ℝ (fun q ↦ V (u q)) p :=
    (hV.differentiable one_ne_zero).differentiableAt.comp p
      (hu.differentiableAt (by norm_num))
  have hsum : (∂[0] (semilinearWaveEnergyDensity (n := n) V u)) p = (∂[0]
            (classicalWaveEnergyDensity (n := n) u)) p +
          (∂[0] (fun q ↦ V (u q))) p := by
    exact PDE.partialDeriv_add (n := n + 1) (i := 0) (f := classicalWaveEnergyDensity (n := n) u)
      (g := fun q ↦ V (u q)) (x := p) hclassical hpotential
  rw [hsum]
  unfold semilinearWaveEnergyBalanceResidual
  unfold classicalWaveEnergyBalanceResidual
  ring

/-- The semilinear local energy residual is `uₜ` times the semilinear wave
operator. -/
theorem semilinearWaveEnergyBalanceResidual_eq_mul_operator {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : ContDiff ℝ 1 V) (hu : ContDiffAt ℝ 2 u p) :
    semilinearWaveEnergyBalanceResidual (n := n) V u p = (∂[0] u) p *
      semilinearWaveOperator (n := n) V u p := by
  rw [semilinearWaveEnergyBalanceResidual, classicalWaveEnergyBalanceResidual_eq_mul_waveOperator
      (n := n) hu]
  rw [PDE.partialDeriv_comp_real (i := (0 : Fin (n + 1)))
    (hV.differentiable one_ne_zero).differentiableAt
    (hu.differentiableAt (by norm_num))]
  unfold semilinearWaveOperator
  ring

/-- A classical semilinear wave has zero pointwise energy-balance residual. -/
theorem semilinearWaveEnergyBalanceResidual_eq_zero {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hV : ContDiff ℝ 1 V) (hu : ContDiffAt ℝ 2 u p)
    (hwave : semilinearWaveOperator (n := n) V u p = 0) :
    semilinearWaveEnergyBalanceResidual (n := n) V u p = 0 := by
  rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator (n := n) hV hu, hwave, mul_zero]

/-- A nonnegative potential makes the full semilinear energy density
nonnegative. -/
theorem semilinearWaveEnergyDensity_nonneg (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z) (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) :
    0 ≤ semilinearWaveEnergyDensity (n := n) V u p := by
  exact add_nonneg (classicalWaveEnergyDensity_nonneg (n := n) u p) (hVnonneg (u p))

end WaveEquation

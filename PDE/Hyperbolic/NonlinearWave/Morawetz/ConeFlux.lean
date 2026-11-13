/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Current
import CAS.ExactTactic

/-!
# The scaling current on a backward null cone

The potential cancels between the density and outward spatial flux. The
remaining expression depends on the derivative along the cone and the
amplitude weight. This algebraic identity requires no differentiability
assumption on the field.

This is the identity (11) of the proof of Evans, §12.4, Theorem 2, for a general potential and
amplitude weight.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, equation (11).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- On a backward null cone the potential terms cancel from the boundary
current. Only the derivative along the cone and the amplitude weight remain. -/
theorem scalingCurrent_normalFlux {V : ℝ → ℝ} (a : ℝ) (c : ℝ^(n + 1)) (u : ℝ^(n + 1) → ℝ)
    {p : ℝ^(n + 1)} {r : ℝ} {ν : Fin n → ℝ} (ht : p 0 - c 0 = -r)
    (hx : ∀ i, p i.succ - c i.succ = r * ν i) (hν : ∑ i : Fin n, ν i ^ 2 = 1) :
    scalingCurrentDensity V a c u p - (∑ i : Fin n, scalingCurrentFlux V a c u i p * ν i) =
      -r * ((∂[0] u) p - ∑ i : Fin n, ν i * (∂[i.succ] u) p) ^ 2 + a * u p *
      ((∂[0] u) p - ∑ i : Fin n, ν i * (∂[i.succ] u) p) := by
  have hm : scalingMultiplier a c u p =
      -r * (∂[0] u) p + r * (∑ i : Fin n, ν i * (∂[i.succ] u) p) + a * u p := by
    unfold scalingMultiplier
    rw [Fin.sum_univ_succ, ht]
    simp_rw [hx, mul_assoc]
    rw [← Finset.mul_sum]
  have hflux : (∑ i : Fin n, scalingCurrentFlux V a c u i p * ν i) =
      scalingMultiplier a c u p * (∑ i : Fin n, ν i * (∂[i.succ] u) p) +
        r * waveLagrangianDensity V u p := by
    calc
      _ = ∑ i : Fin n, (scalingMultiplier a c u p * (ν i * (∂[i.succ] u) p) +
            (r * waveLagrangianDensity V u p) * ν i ^ 2) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        unfold scalingCurrentFlux
        rw [hx]
        cas
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hν, mul_one]
  rw [hflux, scalingCurrentDensity, ht, hm]
  cas

end WaveEquation

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generator
public import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time averages of strongly continuous semigroups

For a strongly continuous semigroup `T` on a Banach space, the time averages

`x_t = t⁻¹ ∫ s in 0..t, T(s)x`

belong to the natural domain of the infinitesimal generator and converge to
`x` as `t ↓ 0`. Consequently the generator domain is dense. This is Evans §7.4.1,
Theorem 2(i), proved with the averages `u^t / t`, `u^t = ∫₀ᵗ S(s)u ds`, of his proof.

The proof uses Mathlib's Bochner interval integral and fundamental theorem of
calculus. Contractivity is not needed for this part of the semigroup theory.

## Implementation notes

The averages are called `yosidaApproximation`, but they are not the Yosida approximation
`A_λ = λ A R_λ` of the Hille–Yosida theorem (Evans §7.4.2, (18)); that one is
`HasContractionResolvent.yosidaApproximation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, Theorem 2(i) and steps 1-2 of its proof, (10),
  pp. 436-437. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Interval

namespace PDE.Analysis.Evolution

namespace StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized time average of the orbit through `x`, continuously extended by `x` at
time zero.

This time average plays the smoothing role of an approximation scheme for the
generator; it is not the classical Yosida approximation
`A_lambda = lambda * A * (lambda - A)⁻¹` from Hille–Yosida theory. -/
def yosidaApproximation
    (T : StronglyContinuousSemigroup E) (x : E) (t : NNReal) : E :=
  if t = 0 then x else
    ⨍ s : ℝ in (0 : ℝ)..(t : ℝ), T.realOrbit x s

/-- At time zero the average is `x` itself, by the `t = 0` case of the definition. -/
@[simp]
theorem yosidaApproximation_zero
    (T : StronglyContinuousSemigroup E) (x : E) :
    T.yosidaApproximation x 0 = x := by
  simp [yosidaApproximation]

private theorem map_intervalIntegral [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (x : E) (t h : NNReal) :
    T h (∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s) =
      (∫ s in (0 : ℝ)..(t + h : NNReal), T.realOrbit x s) -
        ∫ s in (0 : ℝ)..(h : ℝ), T.realOrbit x s := by
  have hint : IntervalIntegrable (T.realOrbit x) volume 0 (t : ℝ) :=
    (T.continuous_realOrbit x).intervalIntegrable 0 t
  calc
    T h (∫ s in (0 : ℝ)..(t : ℝ), T.realOrbit x s) =
        ∫ s in (0 : ℝ)..t, T h (T.realOrbit x s) := by
      exact ((T h).intervalIntegral_comp_comm hint).symm
    _ = ∫ s in (0 : ℝ)..t, T.realOrbit x (s + h) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs_nonneg : 0 ≤ s := by
        rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
        exact hs.1
      calc
        T h (T.realOrbit x s) = T (h + s.toNNReal) x := by
          rw [realOrbit]
          exact (T.map_add_apply h s.toNNReal x).symm
        _ = T (s.toNNReal + h) x := by rw [add_comm]
        _ = T.realOrbit x (s + h) := by
          have htoNNReal :
              (s + (h : ℝ)).toNNReal = s.toNNReal + h := by
            calc
              (s + (h : ℝ)).toNNReal =
                  s.toNNReal + ((h : ℝ).toNNReal) :=
                Real.toNNReal_add hs_nonneg h.property
              _ = s.toNNReal + h := by rw [Real.toNNReal_coe]
          rw [realOrbit, htoNNReal]
    _ = ∫ s in (h : ℝ)..(t + h : NNReal), T.realOrbit x s := by
      simpa only [zero_add, NNReal.coe_add] using
        intervalIntegral.integral_comp_add_right
          (a := 0) (b := (t : ℝ)) (T.realOrbit x) (h : ℝ)
    _ = (∫ s in (0 : ℝ)..(t + h : NNReal), T.realOrbit x s) -
          ∫ s in (0 : ℝ)..(h : ℝ), T.realOrbit x s := by
      have hlarge :
          IntervalIntegrable (T.realOrbit x) volume 0 ((t + h : NNReal) : ℝ) :=
        (T.continuous_realOrbit x).intervalIntegrable 0 (t + h : NNReal)
      have hsmall : IntervalIntegrable (T.realOrbit x) volume 0 (h : ℝ) :=
        (T.continuous_realOrbit x).intervalIntegrable 0 h
      simpa only [NNReal.coe_add] using
        (intervalIntegral.integral_interval_sub_left hlarge hsmall).symm

private theorem realOrbit_yosidaApproximation [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (x : E) (t : NNReal)
    (ht : t ≠ 0)
    {h : ℝ} (hh : h ∈ Ici 0) :
    T.realOrbit (T.yosidaApproximation x t) h =
      ((t : ℝ)⁻¹) •
        ((∫ s in (0 : ℝ)..(t : ℝ) + h, T.realOrbit x s) -
          ∫ s in (0 : ℝ)..h, T.realOrbit x s) := by
  rw [realOrbit, yosidaApproximation, ite_eq_right ht, interval_average_eq, sub_zero, map_smul,
    T.map_intervalIntegral]
  simp only [NNReal.coe_add, Real.coe_toNNReal _ hh]

/-- A positive-time average belongs to the natural generator domain,
with generator value `t⁻¹(T(t)x - x)`. -/
theorem hasGeneratorAt_yosidaApproximation [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (x : E) (t : NNReal) (ht : 0 < t) :
    T.HasGeneratorAt (T.yosidaApproximation x t)
      (((t : ℝ)⁻¹) • (T t x - x)) := by
  have hcontinuous := T.continuous_realOrbit x
  have hupper :
      HasDerivAt
        (fun h : ℝ ↦ ∫ s in (0 : ℝ)..(t : ℝ) + h, T.realOrbit x s)
        (T t x) 0 := by
    simpa only [add_zero, realOrbit_coe] using
      (hcontinuous.integral_hasStrictDerivAt 0 ((t : ℝ) + 0))
        |>.hasDerivAt.comp_const_add (t : ℝ) 0
  have hlower :
      HasDerivAt
        (fun h : ℝ ↦ ∫ s in (0 : ℝ)..h, T.realOrbit x s)
        x 0 := by
    simpa only [realOrbit_zero] using
      (hcontinuous.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hderiv :
      HasDerivAt
        (fun h : ℝ ↦
          ((t : ℝ)⁻¹) •
            ((∫ s in (0 : ℝ)..(t : ℝ) + h, T.realOrbit x s) -
              ∫ s in (0 : ℝ)..h, T.realOrbit x s))
        (((t : ℝ)⁻¹) • (T t x - x)) 0 :=
    (hupper.sub hlower).const_smul ((t : ℝ)⁻¹)
  exact hderiv.hasDerivWithinAt.congr
    (fun h hh ↦ T.realOrbit_yosidaApproximation x t ht.ne' hh)
    (by
      simpa using
        T.realOrbit_yosidaApproximation x t ht.ne' (show (0 : ℝ) ∈ Ici 0 by simp))

/-- The time averages converge strongly to their initial vector as time tends
to zero from the right. -/
theorem tendsto_yosidaApproximation_zero_right [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (x : E) :
    Tendsto (T.yosidaApproximation x) (𝓝[>] 0) (𝓝 x) := by
  have hreal :
      Tendsto
        (fun t : ℝ ↦
          t⁻¹ •
            ((∫ s in (0 : ℝ)..0 + t, T.realOrbit x s) -
              ∫ s in (0 : ℝ)..0, T.realOrbit x s))
        (𝓝[>] 0) (𝓝 x) := by
    simpa only [realOrbit_zero] using
      (T.continuous_realOrbit x).integral_hasStrictDerivAt 0 0
        |>.hasDerivAt.tendsto_slope_zero_right
  have hcoe :
      Filter.map ((↑) : NNReal → ℝ) (𝓝[>] (0 : NNReal)) = 𝓝[>] (0 : ℝ) := by
    exact NNReal.map_coe_nhdsGT (0 : NNReal)
  rw [← hcoe] at hreal
  refine (hreal.comp Filter.tendsto_map).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ (0 : NNReal) := ne_of_gt ht
  rw [yosidaApproximation, ite_eq_right ht0, interval_average_eq]
  simp [Function.comp_apply]

/-- The infinitesimal generator of every strongly continuous semigroup on a
Banach space has dense natural domain. -/
theorem dense_generatorPMap_domain_of_complete [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) :
    Dense (T.generatorPMap.domain : Set E) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  refine mem_closure_of_tendsto (T.tendsto_yosidaApproximation_zero_right x) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  · have ht' : 0 < t := ht
    change ∃ Ax, T.HasGeneratorAt (T.yosidaApproximation x t) Ax
    exact ⟨((t : ℝ)⁻¹) • (T t x - x), T.hasGeneratorAt_yosidaApproximation x t ht'⟩

end StronglyContinuousSemigroup

end PDE.Analysis.Evolution

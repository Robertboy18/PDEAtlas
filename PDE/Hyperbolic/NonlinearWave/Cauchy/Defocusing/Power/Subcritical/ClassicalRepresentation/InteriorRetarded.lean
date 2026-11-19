/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.PartialDeriv.Transforms
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation.InteriorOneDimension
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation.TimeBand
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalFreeField
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula

/-!
# Three-dimensional retarded representation with initial traces

Spherical reduction and the radius-zero derivative identify a zero-data field with its retarded
integral. Second derivatives are required only at positive time.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

private theorem partialDeriv_radiusMean_initial_of_contDiff_one {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 1 u)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = 0) (x : ℝ^1) :
    (∂[0] (radiusMean u)) (timeSpaceCons 0 x) = 0 := by
  rw [partialDeriv_timeSpaceCons_eq_deriv _ x 0
    ((contDiff_radiusMean hu).differentiable (by norm_num)).differentiableAt]
  have heq : (fun s ↦ radiusMean u (timeSpaceCons s x)) =
      fun s ↦ (x 0) * waveSphericalMean u 0 s (x 0) := by
    funext s
    simp only [radiusMean, timeSpaceCons_zero,
      show (1 : Fin 2) = (0 : Fin 1).succ from rfl, timeSpaceCons_succ]
  rw [heq, deriv_const_mul_field, (hasDerivAt_waveSphericalMean_time u 0 0 (x 0) hu).deriv]
  simp only [hinitial, unitSphereAverage, integral_zero, zero_div, mul_zero]

/-- A wave C² at positive times and C¹ across the initial time has the
characteristic source formula at its spatial center. -/
theorem eq_characteristic_integral_of_interior_zero_data {u f : ℝ^4 → ℝ} {L T : ℝ}
    (hu : ContDiff ℝ 1 u) (hu₂ : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) (hf : ContDiff ℝ 1 f)
    (hT : 0 < T) (hTL : T < L)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = 0) :
    u (timeSpaceCons T (0 : ℝ^3)) =
      ∫ s in (0 : ℝ)..T, (T - s) * waveSphericalMean f 0 s (T - s) := by
  have hrep (r : ℝ) := eq_dAlembertDuhamel_of_interior_zero_data
    (contDiff_radiusMean hu) (contDiffOn_two_radiusMean hu₂) (contDiff_radiusMean hf)
    (fun t ht x ↦ waveOperator_radiusMean_on_open_band hu₂ hf.continuous ht (hwave t ht) x)
    (fun x ↦ by
      simp only [radiusMean, timeSpaceCons_zero, waveSphericalMean, hzero,
        unitSphereAverage, integral_zero, zero_div, mul_zero])
    (partialDeriv_radiusMean_initial_of_contDiff_one hu hinitial) ⟨hT.le, hTL⟩
    (EuclideanSpace.single (0 : Fin 1) r)
  have hmean : ContDiff ℝ 1 (fun r ↦ waveSphericalMean u 0 T r) :=
    (contDiff_unitSphereAverage (hu.comp (contDiff_timeSpaceCons_spatial 3 T))).comp
      (contDiff_const.prodMk contDiff_id)
  have hleft : HasDerivAt (fun r ↦ radiusMean u
      (timeSpaceCons T (EuclideanSpace.single (0 : Fin 1) r)))
      (u (timeSpaceCons T (0 : ℝ^3))) 0 := by
    have hd := (hasDerivAt_id (0 : ℝ)).mul (hmean.differentiable one_ne_zero 0).hasDerivAt
    change HasDerivAt (fun r ↦ r * waveSphericalMean u 0 T r) _ 0 at hd
    simpa only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one,
      waveSphericalMean_zero, id_eq, zero_mul, one_mul, add_zero] using hd
  rw [← hleft.deriv, funext hrep,
    deriv_dAlembertDuhamel_radius_zero (contDiff_radiusMean hf) (radiusMean_odd f) hT.le]
  simp only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one]

/-- The retarded identity holds for interior C² waves with C¹ initial traces
and C¹ forcing. This proves a representation of the candidate, not regularity
of a generic three-dimensional retarded field. -/
theorem eq_oddDuhamel_of_interior_zero_data {u f : ℝ^4 → ℝ} {L T : ℝ} (hu : ContDiff ℝ 1 u)
    (hu₂ : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) (hf : ContDiff ℝ 1 f) (hT : 0 < T) (hTL : T < L)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = 0) (c : ℝ^3) :
    u (timeSpaceCons T c) = oddDuhamelSolution 0 f (timeSpaceCons T c) := by
  let a := timeSpaceCons 0 c
  have he (t : ℝ) (x : ℝ^3) : timeSpaceCons t x + a = timeSpaceCons t (c + x) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [a, add_comm]
  have hw (z : ℝ^4) : waveOperator (fun q ↦ u (q + a)) z = waveOperator u (z + a) := by
    simp only [waveOperator, partialDeriv_comp_add_right]
  have hshift : ContDiffOn ℝ 2 (fun q ↦ u (q + a)) {z | z 0 ∈ Ioo 0 L} := by
    refine hu₂.comp (contDiff_id.add contDiff_const).contDiffOn fun z hz ↦ ?_
    change z 0 ∈ Ioo 0 L at hz
    change (z + a) 0 ∈ Ioo 0 L
    simpa only [a, PiLp.add_apply, timeSpaceCons_zero, add_zero] using hz
  have hrep := eq_characteristic_integral_of_interior_zero_data
    (u := fun q ↦ u (q + a)) (f := fun q ↦ f (q + a))
    (hu.comp (contDiff_id.add contDiff_const)) hshift
    (hf.comp (contDiff_id.add contDiff_const)) hT hTL
    (fun t ht x ↦ by rw [hw, he]; exact hwave t ht (c + x))
    (fun x ↦ by rw [he]; exact hzero (c + x))
    (fun x ↦ by
      rw [partialDeriv_comp_add_right]
      change (∂[0] u) (timeSpaceCons 0 x + a) = 0
      rw [he]
      exact hinitial (c + x))
  rw [he, add_zero] at hrep
  rw [oddDuhamelSolution_eq_integral 0 f c hT.le]
  simp only [Nat.doubleFactorial, Nat.cast_one, inv_one, one_mul,
    oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  rw [hrep]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [waveSphericalMean, unitSphereAverage, he, zero_add]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

end

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.FactorThrough
public import PDE.Analysis.MeasureTheory.Lp.SignedPower.Mixed
public import PDE.Hyperbolic.Models.Wave.Strichartz.AdjointGram

/-!
# The homogeneous wave operator from TT*

Mixed-space norming and the Gram identity bound the normalized Newton
operator by the adjoint energy norm. Factoring through the closure of the
adjoint range constructs a bounded map from the full energy Hilbert space to
L4 time/L12 space. Orthogonal projection supplies the complement. The resulting map has the
all-energy weak adjoint identity.

This constructs the operator behind the case `f = 0` of the L⁴L¹² part of the estimate (4) of Evans,
§12.4, Theorem 1. Its identification with the physical wave is in
`Strichartz.PhysicalIdentification`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equations (3)-(4), and step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- Explicit mixed norming turns the Gram identity into the bound required
to factor the normalized Newton operator through the adjoint energy range. -/
theorem norm_smul_spacetimeNewtonOperator_le_energyAdjoint
    (u : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    ‖(4 * Real.pi)⁻¹ • spacetimeNewtonOperator u‖ ≤
      energyAdjointBound * ‖energyAdjointOperator u‖ := by
  refine Lp.norm_le_of_forall_integral_integral_mul_le
    (p := 12) (q := 12 / 11) (b := 4) (c := 4 / 3) (r := 11) (s := 3)
    (C := energyAdjointBound * ‖energyAdjointOperator u‖)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) _ ?_
  intro v
  calc
    _ = spacetimePairing ((4 * Real.pi)⁻¹ • spacetimeNewtonOperator u) v :=
      (spacetimePairing_eq_integral _ v).symm
    _ = (4 * Real.pi)⁻¹ * spacetimePairing (spacetimeNewtonOperator u) v :=
      congrArg (fun f : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3)))
        (4 / 3) (volume : Measure ℝ) →L[ℝ] ℝ ↦ f v)
        (map_smul spacetimePairing (4 * Real.pi)⁻¹ (spacetimeNewtonOperator u))
    _ = (inner ℂ (energyAdjointOperator v) (energyAdjointOperator u)).re :=
      (re_inner_energyAdjointOperator_eq u v).symm
    _ ≤ ‖energyAdjointOperator v‖ * ‖energyAdjointOperator u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ (energyAdjointBound * ‖v‖) * ‖energyAdjointOperator u‖ := mul_le_mul_of_nonneg_right
        ((energyAdjointOperator.le_opNorm v).trans
          (mul_le_mul_of_nonneg_right norm_energyAdjointOperator_le (norm_nonneg v)))
        (norm_nonneg _)
    _ = _ := mul_right_comm _ _ _

/-- The homogeneous mixed-space wave operator constructed from the
adjoint and Newton kernel. Orthogonal projection handles the complement of the closed adjoint
range. -/
noncomputable def homogeneousWaveOperator :
    WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))) →L[ℝ]
      Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ) :=
  (((4 * Real.pi)⁻¹ • spacetimeNewtonOperator).toLinearMap).factorThroughHilbert
    energyAdjointOperator.toLinearMap

/-- The constructed homogeneous operator recovers the normalized Newton
operator on every adjoint energy datum. -/
theorem homogeneousWaveOperator_energyAdjoint
    (u : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    homogeneousWaveOperator (energyAdjointOperator u) =
      (4 * Real.pi)⁻¹ • spacetimeNewtonOperator u :=
  LinearMap.factorThroughHilbert_apply _ _ norm_smul_spacetimeNewtonOperator_le_energyAdjoint u

/-- The TT* construction has the square-root kernel norm bound. -/
theorem norm_homogeneousWaveOperator_le : ‖homogeneousWaveOperator‖ ≤ energyAdjointBound :=
  LinearMap.norm_factorThroughHilbert_le _ _ (Real.sqrt_nonneg _)
    norm_smul_spacetimeNewtonOperator_le_energyAdjoint

/-- Real and complex inner products on the energy space have the same real
pairing, independently of the product-space instance presentation. -/
theorem real_inner_energy_eq_re
    (a b : WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3)))) :
    inner ℝ a b = (inner ℂ a b).re :=
  (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two a b).trans
    (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) a b).symm

/-- On every energy datum, the constructed spacetime operator is weakly adjoint
to the Fourier energy integral. -/
theorem spacetimePairing_homogeneousWaveOperator
    (h : WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))))
    (v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    spacetimePairing (homogeneousWaveOperator h) v = (inner ℂ (energyAdjointOperator v) h).re := by
  refine (LinearMap.apply_factorThroughHilbert_eq_inner
    (((4 * Real.pi)⁻¹ • spacetimeNewtonOperator).toLinearMap)
    energyAdjointOperator.toLinearMap norm_smul_spacetimeNewtonOperator_le_energyAdjoint
    (spacetimePairing.flip v) v ?_ h).trans (real_inner_energy_eq_re _ _)
  intro u
  calc
    _ = (4 * Real.pi)⁻¹ * spacetimePairing (spacetimeNewtonOperator u) v :=
      congrArg (fun f : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3)))
        (4 / 3) (volume : Measure ℝ) →L[ℝ] ℝ ↦ f v)
        (map_smul spacetimePairing (4 * Real.pi)⁻¹ (spacetimeNewtonOperator u))
    _ = (inner ℂ (energyAdjointOperator v) (energyAdjointOperator u)).re :=
      (re_inner_energyAdjointOperator_eq u v).symm
    _ = _ := (real_inner_energy_eq_re _ _).symm

end WaveEquation.Strichartz

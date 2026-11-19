/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.PhysicalTrace
public import PDE.Fluid.Incompressible.LerayProjection.DilationContinuity

/-!
# Physical energy bounds of weighted ancient perturbations

Strong dilation continuity supplies positive-time Bochner measurability.
The exact physical L² scaling gives a uniform velocity bound and an integrable
squared norm for first weak derivatives. The derivative identities use the
actual Sobolev chain rule. These are energy-space bounds, without an assertion
of the Navier--Stokes energy inequality.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped ENNReal Sobolev BoundedContinuousFunction

namespace NavierStokes.Selfsimilar

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The extra inverse length factor in a first physical weak derivative. -/
def physicalDerivativeL2 (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ) {a : ℝ}
    (u : Iic a →ᵇ E) (τ : ℝ) : WholeSpaceL2 n :=
  Real.exp (-τ / 2) • weightedPhysicalL2 T η u τ

/-- The physical vector field is strongly continuous on the ancient half-line. -/
theorem continuous_weightedPhysicalL2_Iic (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ)
    {a : ℝ} (u : Iic a →ᵇ E) :
    Continuous (fun τ : Iic a ↦ weightedPhysicalL2 T η u τ) := by
  have hfactor : Continuous (fun τ : Iic a ↦
      (⟨Real.exp (-τ.val / 2), by
        apply Real.exp_le_exp.mpr
        have hτ : τ.val ≤ a := τ.property
        linarith⟩ : Ici (Real.exp (-a / 2)))) :=
    (Real.continuous_exp.comp (continuous_subtype_val.neg.div_const 2)).subtype_mk _
  have hinput : Continuous (fun τ : Iic a ↦ T (ancientLift η u τ)) :=
    T.continuous.comp ((ancientLift η u).continuous.comp continuous_subtype_val)
  have hd := (continuous_l2Dilation_Ici (n := n) (Real.exp_pos (-a / 2))).comp
    (hinput.prodMk hfactor)
  simpa only [Function.comp_def, Pi.smul_def', Pi.neg_apply,
    weightedPhysicalL2, physicalL2Rescaling, smul_apply] using
    (Real.continuous_exp.comp (continuous_subtype_val.neg.div_const 2)).smul hd

/-- First physical derivative fields are strongly continuous in ancient time. -/
theorem continuous_physicalDerivativeL2_Iic (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ)
    {a : ℝ} (u : Iic a →ᵇ E) :
    Continuous (fun τ : Iic a ↦ physicalDerivativeL2 T η u τ) :=
  (Real.continuous_exp.comp (continuous_subtype_val.neg.div_const 2)).smul
    (continuous_weightedPhysicalL2_Iic T η u)

/-- The physical field is strongly continuous on the positive physical time interval. -/
theorem continuousOn_weightedPhysicalL2_log (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ)
    {a : ℝ} (u : Iic a →ᵇ E) :
    ContinuousOn (fun t ↦ weightedPhysicalL2 T η u (Real.log t)) (Ioc 0 (Real.exp a)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [Set.domRestrict_def]
  have hlog : Continuous (fun t : Ioc 0 (Real.exp a) ↦
      (⟨Real.log t.val, (Real.log_le_iff_le_exp t.property.1).mpr t.property.2⟩ : Iic a)) :=
    (continuous_subtype_val.log (fun t ↦ t.property.1.ne')).subtype_mk _
  have h := (continuous_weightedPhysicalL2_Iic T η u).comp hlog
  simpa only [Function.comp_def] using h

/-- The first physical derivative is strongly continuous at every positive time. -/
theorem continuousOn_physicalDerivativeL2_log (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ)
    {a : ℝ} (u : Iic a →ᵇ E) :
    ContinuousOn (fun t ↦ physicalDerivativeL2 T η u (Real.log t))
      (Ioc 0 (Real.exp a)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [Set.domRestrict_def]
  have hlog : Continuous (fun t : Ioc 0 (Real.exp a) ↦
      (⟨Real.log t.val, (Real.log_le_iff_le_exp t.property.1).mpr t.property.2⟩ : Iic a)) :=
    (continuous_subtype_val.log (fun t ↦ t.property.1.ne')).subtype_mk _
  have h := (continuous_physicalDerivativeL2_Iic T η u).comp hlog
  simpa only [Function.comp_def] using h

/-- A positive total physical weight gives a uniform L² bound up to the terminal time. -/
theorem norm_weightedPhysicalL2_log_le (T : E →L[ℝ] WholeSpaceL2 n) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E)
    {t : ℝ} (ht : t ∈ Ioc 0 (Real.exp a)) :
    ‖weightedPhysicalL2 T η u (Real.log t)‖ ≤
      ‖T‖ * ‖u‖ * Real.exp ((η + ((n : ℝ) - 2) / 4) * a) := by
  apply (norm_weightedPhysicalL2_le T η u (Real.log t)).trans
  gcongr
  exact (Real.log_le_iff_le_exp ht.1).mpr ht.2

/-- The physical velocity is a Bochner L∞ path in spatial L². -/
theorem memLp_weightedPhysicalL2_log_top (T : E →L[ℝ] WholeSpaceL2 n) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E) :
    MemLp (fun t ↦ weightedPhysicalL2 T η u (Real.log t)) ∞
      (volume.restrict (Ioc 0 (Real.exp a))) := by
  apply memLp_top_of_bound
    ((continuousOn_weightedPhysicalL2_log T η u).aestronglyMeasurable measurableSet_Ioc)
    (‖T‖ * ‖u‖ * Real.exp ((η + ((n : ℝ) - 2) / 4) * a))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact norm_weightedPhysicalL2_log_le T hη u ht

/-- The additional spatial derivative reduces the physical time exponent by one half. -/
theorem norm_physicalDerivativeL2_le (T : E →L[ℝ] WholeSpaceL2 n) (η : ℝ) {a : ℝ}
    (u : Iic a →ᵇ E) (τ : ℝ) :
    ‖physicalDerivativeL2 T η u τ‖ ≤
      ‖T‖ * ‖u‖ * Real.exp ((η + ((n : ℝ) - 2) / 4 - 1 / 2) * τ) := by
  rw [physicalDerivativeL2, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    _ ≤ Real.exp (-τ / 2) *
        (‖T‖ * ‖u‖ * Real.exp ((η + ((n : ℝ) - 2) / 4) * τ)) :=
      mul_le_mul_of_nonneg_left (norm_weightedPhysicalL2_le T η u τ) (Real.exp_nonneg _)
    _ = _ := by
      rw [show (η + ((n : ℝ) - 2) / 4 - 1 / 2) * τ =
        -τ / 2 + (η + ((n : ℝ) - 2) / 4) * τ by ring, Real.exp_add]
      ring

/-- The squared derivative norm is bounded by the exact integrable physical-time power. -/
theorem norm_physicalDerivativeL2_log_sq_le (T : E →L[ℝ] WholeSpaceL2 n)
    (η : ℝ) {a : ℝ} (u : Iic a →ᵇ E) {t : ℝ} (ht : 0 < t) :
    ‖physicalDerivativeL2 T η u (Real.log t)‖ ^ 2 ≤
      (‖T‖ * ‖u‖) ^ 2 * t ^ (2 * (η + ((n : ℝ) - 2) / 4) - 1) := by
  calc
    _ ≤ (‖T‖ * ‖u‖ *
        Real.exp ((η + ((n : ℝ) - 2) / 4 - 1 / 2) * Real.log t)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (norm_physicalDerivativeL2_le T η u (Real.log t))
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, Real.rpow_def_of_pos ht]
      congr 1
      congr 1
      ring

/-- First physical derivative energy is integrable down to initial time zero. -/
theorem integrableOn_norm_physicalDerivativeL2_log_sq (T : E →L[ℝ] WholeSpaceL2 n)
    {η a : ℝ} (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E) :
    IntegrableOn (fun t ↦ ‖physicalDerivativeL2 T η u (Real.log t)‖ ^ 2)
      (Ioc 0 (Real.exp a)) := by
  have hpow : IntegrableOn
      (fun t : ℝ ↦ (‖T‖ * ‖u‖) ^ 2 * t ^ (2 * (η + ((n : ℝ) - 2) / 4) - 1))
      (Ioc 0 (Real.exp a)) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith :
      -1 < 2 * (η + ((n : ℝ) - 2) / 4) - 1)).1.const_mul _
  apply hpow.mono'
    (((continuousOn_physicalDerivativeL2_log T η u).aestronglyMeasurable
      measurableSet_Ioc).norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖‖physicalDerivativeL2 T η u (Real.log t)‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact norm_physicalDerivativeL2_log_sq_le T η u ht.1

/-- First physical derivative fields belong to Bochner L² in time and space. -/
theorem memLp_physicalDerivativeL2_log_two (T : E →L[ℝ] WholeSpaceL2 n) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E) :
    MemLp (fun t ↦ physicalDerivativeL2 T η u (Real.log t)) 2
      (volume.restrict (Ioc 0 (Real.exp a))) :=
  (memLp_two_iff_integrable_sq_norm
    ((continuousOn_physicalDerivativeL2_log T η u).aestronglyMeasurable
      measurableSet_Ioc)).mpr (integrableOn_norm_physicalDerivativeL2_log_sq T hη u)

/-- The first-derivative energy has the explicit bound from the physical time power. -/
theorem integral_norm_physicalDerivativeL2_log_sq_le (T : E →L[ℝ] WholeSpaceL2 n)
    {η a : ℝ} (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ E) :
    ∫ t in Ioc 0 (Real.exp a), ‖physicalDerivativeL2 T η u (Real.log t)‖ ^ 2 ≤
      (‖T‖ * ‖u‖) ^ 2 * Real.exp (2 * (η + ((n : ℝ) - 2) / 4) * a) /
        (2 * (η + ((n : ℝ) - 2) / 4)) := by
  let κ := η + ((n : ℝ) - 2) / 4
  have hκ : 0 < κ := hη
  have hp : -1 < 2 * κ - 1 := by linarith
  have hpow : IntegrableOn (fun t : ℝ ↦ (‖T‖ * ‖u‖) ^ 2 * t ^ (2 * κ - 1))
      (Ioc 0 (Real.exp a)) :=
    (intervalIntegral.intervalIntegrable_rpow' hp).1.const_mul _
  calc
    _ ≤ ∫ t in Ioc 0 (Real.exp a), (‖T‖ * ‖u‖) ^ 2 * t ^ (2 * κ - 1) := by
      apply setIntegral_mono_on (integrableOn_norm_physicalDerivativeL2_log_sq T hη u)
        hpow measurableSet_Ioc
      intro t ht
      exact norm_physicalDerivativeL2_log_sq_le T η u ht.1
    _ = _ := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le (Real.exp_pos a).le,
        integral_rpow (Or.inl hp), sub_add_cancel,
        Real.zero_rpow (by positivity : 2 * κ ≠ 0), sub_zero,
        Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]
      rw [mul_comm a (2 * κ)]
      dsimp only [κ]
      ring

/-- Physical rescaling of an actual vector Sobolev graph. -/
def physicalSobolevRescaling (n k : ℕ) (τ : ℝ) : VectorH n k →L[ℝ] VectorH n k :=
  Real.exp (-τ / 2) • vectorDilation n k (Real.exp (-τ / 2)) (Real.exp_ne_zero _)

/-- The Sobolev base row agrees with physical L² rescaling. -/
theorem l2SobolevRow_base_physicalSobolevRescaling {k : ℕ} (τ : ℝ) (U : VectorH n k) :
    l2SobolevRow (baseIndex n k) (physicalSobolevRescaling n k τ U) =
      physicalL2Rescaling n τ (l2SobolevRow (baseIndex n k) U) := by
  simp only [physicalSobolevRescaling, physicalL2Rescaling, smul_apply, map_smul,
    l2SobolevRow_base_vectorDilation]

/-- An actual first weak derivative has one further physical inverse length factor. -/
theorem l2SobolevRow_first_physicalSobolevRescaling {k : ℕ}
    (α : DerivIndex n k) (hα : α.toList.length = 1) (τ : ℝ) (U : VectorH n k) :
    l2SobolevRow α (physicalSobolevRescaling n k τ U) =
      Real.exp (-τ / 2) • physicalL2Rescaling n τ (l2SobolevRow α U) := by
  simp only [physicalSobolevRescaling, physicalL2Rescaling, smul_apply, map_smul,
    l2SobolevRow_vectorDilation, hα, pow_one]

/-- The actual rescaled Sobolev velocity lies in physical L∞ time with values in L². -/
theorem memLp_sobolevPhysical_base_log_top {k : ℕ} {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ VectorH n k) :
    MemLp (fun t ↦ l2SobolevRow (baseIndex n k)
      (physicalSobolevRescaling n k (Real.log t) (ancientLift η u (Real.log t)))) ∞
      (volume.restrict (Ioc 0 (Real.exp a))) := by
  simpa only [l2SobolevRow_base_physicalSobolevRescaling, weightedPhysicalL2] using
    memLp_weightedPhysicalL2_log_top (l2SobolevRow (baseIndex n k)) hη u

/-- Every actual first weak derivative has finite physical space-time L² norm. -/
theorem memLp_sobolevPhysical_first_log_two {k : ℕ}
    (α : DerivIndex n k) (hα : α.toList.length = 1) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ VectorH n k) :
    MemLp (fun t ↦ l2SobolevRow α
      (physicalSobolevRescaling n k (Real.log t) (ancientLift η u (Real.log t)))) 2
      (volume.restrict (Ioc 0 (Real.exp a))) := by
  simpa only [l2SobolevRow_first_physicalSobolevRescaling α hα, physicalDerivativeL2,
    weightedPhysicalL2] using memLp_physicalDerivativeL2_log_two (l2SobolevRow α) hη u

/-- The actual weak derivative energy obeys the explicit physical time estimate. -/
theorem integral_norm_sobolevPhysical_first_log_sq_le {k : ℕ}
    (α : DerivIndex n k) (hα : α.toList.length = 1) {η a : ℝ}
    (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ VectorH n k) :
    ∫ t in Ioc 0 (Real.exp a), ‖l2SobolevRow α
      (physicalSobolevRescaling n k (Real.log t) (ancientLift η u (Real.log t)))‖ ^ 2 ≤
      (‖l2SobolevRow α‖ * ‖u‖) ^ 2 * Real.exp (2 * (η + ((n : ℝ) - 2) / 4) * a) /
        (2 * (η + ((n : ℝ) - 2) / 4)) := by
  simpa only [l2SobolevRow_first_physicalSobolevRescaling α hα, physicalDerivativeL2,
    weightedPhysicalL2] using integral_norm_physicalDerivativeL2_log_sq_le (l2SobolevRow α) hη u

/-- The sum of the actual directional weak derivative energies is integrable at zero. -/
theorem integrableOn_sobolevPhysical_gradient_energy {k : ℕ} (hk : 0 < k)
    {η a : ℝ} (hη : 0 < η + ((n : ℝ) - 2) / 4) (u : Iic a →ᵇ VectorH n k) :
    IntegrableOn (fun t ↦ ∑ i : Fin n, ‖l2SobolevRow (firstDerivIndex n k hk i)
      (physicalSobolevRescaling n k (Real.log t) (ancientLift η u (Real.log t)))‖ ^ 2)
      (Ioc 0 (Real.exp a)) := by
  apply integrable_finsetSum
  intro i _
  simpa only [l2SobolevRow_first_physicalSobolevRescaling
    (firstDerivIndex n k hk i) (by simp), physicalDerivativeL2, weightedPhysicalL2,
    IntegrableOn] using
    integrableOn_norm_physicalDerivativeL2_log_sq (l2SobolevRow (firstDerivIndex n k hk i)) hη u

end NavierStokes.Selfsimilar

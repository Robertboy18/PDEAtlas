/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.ProductChart
public import PDE.Fluid.NavierStokes.RieszPressure.Sobolev
public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCutoffSmoothness

/-!
# The pressure of the physical velocity

The pressure of the physical velocity `u` of an unstable profile (`physicalVelocity`) is the Riesz
pressure `P = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` of the velocity slice at each positive time, with `Rᵢ` the Riesz
transforms, and zero at nonpositive times (`physicalPressure`). On `(0, 1)` it is a smooth path in
every `Hᵏ(ℝ³)`, each of its slices at times in `(0, 1]` is smooth, and it is jointly smooth on
`(0, 1) × ℝ³`.

## Main definitions

* `physicalPressure`: the pressure of the physical velocity.
* `physicalVelocitySobolev`: the physical velocity at time `t` in `W^{k,4}(ℝ³)`.
* `physicalProductSobolev`, `physicalPressureSobolev`: the products `uᵢuⱼ` in `Hᵏ` and the pressure
  at time `t` in `Hᵏ(ℝ³)`.

## Main results

* `contDiffOn_physicalVelocitySobolev`: the velocity is a smooth path in every `W^{k,4}` on
  `(0, 1)`.
* `contDiffOn_physicalPressureSobolev`: the pressure is a smooth path in every `Hᵏ` on `(0, 1)`.
* `rieszPressure_velocitySlice_eq`: for `0 < t ≤ 1` and `k ≥ 3` the Riesz pressure of the slice is
  the classical representative of the pressure path in `Hᵏ`.
* `contDiff_rieszPressure_velocitySlice`: for `0 < t ≤ 1` the pressure slice is smooth.
* `contDiffOn_physicalPressure`, `contDiffAt_physicalPressure`: the pressure is jointly smooth on
  `(0, 1) × ℝ³`.

## How it works

The velocity is the sum of the profile part, the cutoff part and the correction. The first two are
smooth paths in `W^{k,4}` on `(0, 1)` (`UnstableProfile.contDiffOn_physicalProfileWkFour`,
`UnstableProfile.contDiffOn_physicalCutoffSobolev_four`), and the correction is a smooth path in
every `Hᵏ⁺³`, which embeds in `W^{k,4}` (`vectorHilbertEmbeddingCLM`); this gives
`contDiffOn_physicalVelocitySobolev`. The `L⁴`-by-`L⁴` product `l4Product` is a bounded bilinear map
from `W^{k,4}` to `Hᵏ`, so the products `uᵢuⱼ` are smooth paths in `Hᵏ`, and the pressure path is
their image under the bounded operator `rieszPressureSobolev`. The Riesz pressure of a slice is by
definition the continuous representative of its `L²` class, and for `k ≥ 3` the classical
representative of the pressure path is continuous and agrees with it almost everywhere
(`rieszPressure_velocitySlice_ae_eq`), so the two are equal. For joint smoothness of order `r` we
take the path in `Hʳ⁺³`, which is `Cʳ` in time, and apply the joint regularity of classical
representatives (`PDE.Hyperbolic.NonlinearWave.Cauchy.contDiffOn_joint_classicalRepresentative`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Common
open NavierStokes.SobolevConvection
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile) (R s : ℝ)

/-- The pressure of the physical velocity: the Riesz pressure of the velocity slice at positive
times and zero at nonpositive times. -/
def physicalPressure (z : ℝ^(3 + 1)) : ℝ :=
  if 0 < z 0 then rieszPressure (velocitySlice (physicalVelocity D R s) (z 0)) (spatialPart z)
  else 0

/-- At a positive time the physical pressure is the Riesz pressure of the velocity slice. -/
theorem physicalPressure_timeSpaceCons {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    physicalPressure D R s (timeSpaceCons t x) =
      rieszPressure (velocitySlice (physicalVelocity D R s) t) x := by
  rw [physicalPressure, timeSpaceCons_zero, spatialPart_timeSpaceCons, ite_eq_left ht]

/-- At a nonpositive time the physical pressure vanishes. -/
theorem physicalPressure_timeSpaceCons_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ^3) :
    physicalPressure D R s (timeSpaceCons t x) = 0 := by
  rw [physicalPressure, timeSpaceCons_zero, ite_eq_right ht.not_gt]

/-- The order condition of the correction in vector `Hᵏ⁺³`. -/
theorem three_lt_two_mul_add_two (k : ℕ) : (3 : ℝ) < 2 * ((k + 2 : ℕ) : ℝ) := by
  push_cast
  linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- The physical velocity at time `t` in `W^{k,4}(ℝ³)`: the physical profile, the physical
cutoff field and the image of the physical correction under `Hᵏ⁺³ ⊂ W^{k,4}`. -/
def physicalVelocitySobolev (k : ℕ) (t : ℝ) : Fin 3 → W^{k,4}(ℝ^3) :=
  physicalProfileWkFour D k t + physicalCutoffSobolev D R k le_rfl t +
    vectorHilbertEmbeddingCLM k memLp_four_baseRepresentative_three
      (physicalCorrection D R s (k + 2) (three_lt_two_mul_add_two k) t)

variable {D R s}

/-- **The velocity is a smooth path in every `W^{k,4}`** on `(0, 1)`. -/
theorem contDiffOn_physicalVelocitySobolev (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalVelocitySobolev D R s k) (Ioo 0 1) := by
  let _ : NormedSpace ℝ (Fin 3 → W^{k,4}(ℝ^3)) := Pi.normedSpace
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  refine contDiffOn_infty.mpr fun j ↦ ?_
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hp := (D.contDiffOn_physicalProfileWkFour k).of_le hj
  have hc := (D.contDiffOn_physicalCutoffSobolev_four hR0 k).of_le hj
  have hk := (vectorHilbertEmbeddingCLM k
    memLp_four_baseRepresentative_three).contDiff.comp_contDiffOn
    ((physical_time_regularity D R s hR hs).1 j (k + 2) (three_lt_two_mul_add_two k))
  exact (hp.add hc).add hk

/-- **The components of the velocity path are the velocity slice.** For `0 < t ≤ 1` the
base representatives of `physicalVelocitySobolev` are the components of the slice of the
physical velocity at `t`. -/
theorem baseRepresentative_physicalVelocitySobolev (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (j : Fin 3) :
    baseRepresentative (physicalVelocitySobolev D R s k t j) =ᵐ[volume]
      fun x ↦ velocitySlice (physicalVelocity D R s) t x j := by
  have hm := three_lt_two_mul_add_two k
  have hadd₁ := baseRepresentative_add_ae
    (physicalProfileWkFour D k t j + physicalCutoffSobolev D R k le_rfl t j)
    (vectorHilbertEmbeddingCLM k memLp_four_baseRepresentative_three
      (physicalCorrection D R s (k + 2) hm t) j)
  have hadd₂ := baseRepresentative_add_ae (physicalProfileWkFour D k t j)
    (physicalCutoffSobolev D R k le_rfl t j)
  simp only [domainMeasure, Measure.restrict_univ] at hadd₁ hadd₂
  have hP := baseRepresentative_vectorWkpOfContDiff (k := k) (p := 4)
    (dilateField (physicalFactor (Real.log t)) D.U) (contDiff_dilateField _ D.contDiff_U)
    (fun m _ ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne' D.contDiff_U
      (D.derivatives_memLp_four m)) j
  have hC := baseRepresentative_vectorWkpOfContDiff (k := k) (p := 4)
    (dilateField (physicalFactor (Real.log t)) (cutoffFieldFn D R (Real.log t)))
    (contDiff_dilateField _ (contDiff_cutoffFieldFn D R _))
    (fun m _ ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne'
      (contDiff_cutoffFieldFn D R _) (memLp_iteratedFDeriv_cutoffFieldFn D R le_rfl _ m)) j
  have hK : baseRepresentative (vectorHilbertEmbeddingCLM k memLp_four_baseRepresentative_three
      (physicalCorrection D R s (k + 2) hm t) j) =
        baseRepresentative (physicalCorrection D R s (k + 2) hm t j) :=
    baseRepresentative_hilbertEmbeddingCLM k _ _
  have hcl := classicalRepresentativeCLM_ae (three_lt_two_mul_succ_sub_one hm)
    (physicalCorrection D R s (k + 2) hm t j)
  rw [classicalRepresentativeCLM_physicalCorrection hR hs hm ht ht1 j] at hcl
  filter_upwards [hadd₁, hadd₂, hP, hC, hcl] with x h₁ h₂ h₃ h₄ h₅
  change baseRepresentative (physicalProfileWkFour D k t j +
    physicalCutoffSobolev D R k le_rfl t j + vectorHilbertEmbeddingCLM k
      memLp_four_baseRepresentative_three
      (physicalCorrection D R s (k + 2) hm t) j) x = _
  rw [h₁, h₂, hK, ← h₅]
  change baseRepresentative (vectorWkpOfContDiff _ _ _ j) x +
    baseRepresentative (vectorWkpOfContDiff _ _ _ j) x + _ = _
  rw [h₃, h₄, velocitySlice, physicalVelocity_timeSpaceCons_eq D R s ht x,
    D.dilateField_cutoffFieldFn ht x, dilateField, physicalFactor_log ht]
  simp only [PiLp.add_apply, PiLp.neg_apply, sub_eq_add_neg]

variable (D R s) in
/-- The products `uᵢuⱼ` of the velocity components at time `t`, as rows in vector `Hᵏ`. -/
def physicalProductSobolev (k : ℕ) (t : ℝ) : Fin 3 → VectorH 3 k :=
  fun i ↦ WithLp.toLp 2 fun j ↦
    l4Product k (physicalVelocitySobolev D R s k t i) (physicalVelocitySobolev D R s k t j)

variable (D R s) in
/-- The pressure at time `t` in `Hᵏ(ℝ³)`: the Riesz pressure operator applied to the products of
the velocity components. -/
def physicalPressureSobolev (k : ℕ) (t : ℝ) : W^{k,2}(ℝ^3) :=
  rieszPressureSobolev 3 k (physicalProductSobolev D R s k t)

/-- **The pressure is a smooth path in every `Hᵏ`** on `(0, 1)`. -/
theorem contDiffOn_physicalPressureSobolev (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalPressureSobolev D R s k) (Ioo 0 1) := by
  let _ : NormedAddCommGroup (W^{k,4}(ℝ^3) →L[ℝ] W^{k,2}(ℝ^3)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (W^{k,4}(ℝ^3) →L[ℝ] W^{k,2}(ℝ^3)) := ContinuousLinearMap.toNormedSpace
  let _ : NormedSpace ℝ (Fin 3 → W^{k,4}(ℝ^3)) := Pi.normedSpace
  have hv := contDiffOn_physicalVelocitySobolev hR hs k
  have hvi (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun t ↦ physicalVelocitySobolev D R s k t i)
      (Ioo 0 1) := (contDiffOn_pi.mp hv) i
  have hprod : ContDiffOn ℝ (⊤ : ℕ∞) (physicalProductSobolev D R s k) (Ioo 0 1) := by
    refine contDiffOn_pi.mpr fun i ↦ contDiffOn_piLp' 2 fun j ↦ ?_
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun t ↦ l4Product (n := 3) k
        (physicalVelocitySobolev D R s k t i)) (Ioo 0 1) :=
      (l4Product (n := 3) k).contDiff.comp_contDiffOn (hvi i)
    exact h1.clm_apply (hvi j)
  exact (rieszPressureSobolev 3 k).contDiff.comp_contDiffOn hprod

/-- For `0 < t ≤ 1` the Riesz pressure of the velocity slice is almost everywhere the base
representative of the pressure path. -/
theorem rieszPressure_velocitySlice_ae_eq (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    rieszPressure (velocitySlice (physicalVelocity D R s) t) =ᵐ[volume]
      baseRepresentative (physicalPressureSobolev D R s k t) := by
  refine rieszPressure_ae_eq_rieszPressureSobolev (by norm_num) _ fun i j ↦ ?_
  filter_upwards [l4Product_base_ae (physicalVelocitySobolev D R s k t i)
      (physicalVelocitySobolev D R s k t j),
    baseRepresentative_physicalVelocitySobolev hR hs k ht ht1 i,
    baseRepresentative_physicalVelocitySobolev hR hs k ht ht1 j] with x h₁ h₂ h₃
  change baseRepresentative (l4Product k (physicalVelocitySobolev D R s k t i)
    (physicalVelocitySobolev D R s k t j)) x = _
  rw [h₁, h₂, h₃]

/-- **The pressure slice is the classical representative of the pressure path.** For
`0 < t ≤ 1` and `k ≥ 3` the Riesz pressure of the velocity slice is the classical
representative of the pressure path in `Hᵏ`. -/
theorem rieszPressure_velocitySlice_eq (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {k : ℕ} (hk : ((3 : ℕ) : ℝ) < 2 * ((k : ℝ) - 1)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    rieszPressure (velocitySlice (physicalVelocity D R s) t) =
      classicalRepresentativeCLM hk (physicalPressureSobolev D R s k t) := by
  refine continuousRepresentative_eq (classicalRepresentativeCLM hk _).continuous ?_
  exact (classicalRepresentativeCLM_ae hk _).trans
    ((rieszPressure_velocitySlice_ae_eq hR hs k ht ht1).symm.trans (rieszPressure_ae_eq _))

/-- The order `r + 3` controls `r` derivatives of the classical representative. -/
theorem three_lt_two_mul_sub_one_add_three (r : ℕ) :
    ((3 : ℕ) : ℝ) < 2 * (((r + 3 : ℕ) : ℝ) - 1) := by
  push_cast
  linarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]

/-- **Every pressure slice is smooth.** For `0 < t ≤ 1` the Riesz pressure of the velocity
slice is smooth. -/
theorem contDiff_rieszPressure_velocitySlice (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszPressure (velocitySlice (physicalVelocity D R s) t)) := by
  refine contDiff_infty.mpr fun r ↦ ?_
  rw [rieszPressure_velocitySlice_eq hR hs (three_lt_two_mul_sub_one_add_three r) ht ht1]
  exact contDiff_classicalRepresentativeCLM _ (by push_cast; linarith) _

/-- **Joint smoothness of the pressure.** The physical pressure is jointly smooth in `(t, x)`
on `(0, 1) × ℝ³`. -/
theorem contDiffOn_physicalPressure (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ^3 ↦ physicalPressure D R s (timeSpaceCons p.1 p.2))
      (Ioo 0 1 ×ˢ univ) := by
  refine contDiffOn_infty.mpr fun r ↦ ?_
  have hk := three_lt_two_mul_sub_one_add_three r
  have hr : ((3 : ℕ) : ℝ) < 2 * (((r + 3 : ℕ) : ℝ) - (r : ℝ) - 1) := by
    push_cast
    linarith
  have hu : ContDiffOn ℝ r (physicalPressureSobolev D R s (r + 3)) (Ioo 0 1) :=
    (contDiffOn_physicalPressureSobolev hR hs (r + 3)).of_le (by exact_mod_cast le_top)
  refine (PDE.Hyperbolic.NonlinearWave.Cauchy.contDiffOn_joint_classicalRepresentative
    isOpen_Ioo hk hr hu).congr fun p hp ↦ ?_
  rw [physicalPressure_timeSpaceCons D R s hp.1.1,
    rieszPressure_velocitySlice_eq hR hs hk hp.1.1 hp.1.2.le]

/-- **The physical pressure is smooth on the open slab** `(0, 1) × ℝ³`. -/
theorem contDiffAt_physicalPressure (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {z : ℝ^(3 + 1)} (hz : z ∈ IncompressibleFlow.finiteTimeDomain 3 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalPressure D R s) z :=
  contDiffAt_of_contDiffOn_timeSpaceCons (isOpen_Ioo.prod isOpen_univ)
    (contDiffOn_physicalPressure hR hs) ⟨⟨hz.1, hz.2⟩, mem_univ _⟩

end NavierStokes.Nonuniqueness

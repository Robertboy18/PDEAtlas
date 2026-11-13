/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.MixedConvectionDilation
public import PDE.Fluid.NavierStokes.Nonuniqueness.CorrectionJointRegularity

/-!
# The physical forcing through coefficient paths

The convection is homogeneous under the physical change of variables,
`P_τ ((U·∇) V) = e^τ ((P_τ U)·∇)(P_τ V)` (`physicalMap_mixedConvection`), so the physical forcing
of the correction splits into a cutoff forcing path, a linear coefficient path applied to the
physical correction, and the convection of the physical correction (`physicalForcing_eq`):

`g(t) = f(t) + A(t) u_cor(t) - (u_cor(t)·∇) u_cor(t)`,

with `f(t) = t⁻¹ P_{log t} F(log t)` (`physicalCutoffForcing`) and
`A(t) = t⁻¹ P_{log t} (L_far(log t) - B) P_{log t}⁻¹` (`physicalCoefficient`). Both paths are built
from the profile and the cutoff field alone. If they are smooth in time on `(0, 1)` at every
order, the time bootstrap makes the physical correction smooth in time with values in every
vector `Hᵐ` (`contDiffOn_physicalCorrection_of_coefficients`), and the correction part of the
physical velocity is jointly smooth on `(0, 1) × ℝ³`
(`contDiffOn_physicalCorrectionField_of_coefficients`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- The physical map at `-τ` inverts the physical map at `τ`. -/
theorem physicalMap_neg_physicalMap (k : ℕ) (τ : ℝ) (v : VectorH 3 k) :
    physicalMap k (-τ) (physicalMap k τ v) = v := by
  have hf : physicalFactor (-τ) * physicalFactor τ = 1 := by
    rw [physicalFactor, physicalFactor, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [physicalMap_apply, physicalMap_apply, map_smul, smul_smul, ← vectorDilation_mul,
    vectorDilation_congr hf _ one_ne_zero, hf, one_smul]
  exact PiLp.ext fun j ↦ by rw [vectorDilation_apply, dilationWkpCLM_one]

/-- The convection in physical variables: `P_τ ((U·∇) V) = e^τ ((P_τ U)·∇)(P_τ V)`. -/
theorem physicalMap_mixedConvection {m : ℕ} (hm : (3 : ℝ) < 2 * m) (τ : ℝ) (U : VectorH 3 m)
    (V : VectorH 3 (m + 1)) :
    physicalMap m τ (mixedConvection m hm U V) =
      Real.exp τ • mixedConvection m hm (physicalMap m τ U) (physicalMap (m + 1) τ V) := by
  have hc : Real.exp τ * physicalFactor τ * physicalFactor τ * physicalFactor τ =
      physicalFactor τ := by
    rw [physicalFactor, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [physicalMap_apply, physicalMap_apply, physicalMap_apply, map_smul, map_smul,
    smul_apply, mixedConvection_vectorDilation, smul_smul, smul_smul, smul_smul, hc]

variable (D : UnstableProfile) (R : ℝ)

/-- The cutoff forcing in physical variables, `f(t) = t⁻¹ P_{log t} F(log t)`, in vector `Hᵐ⁺¹`. -/
def physicalCutoffForcing (m : ℕ) (t : ℝ) : VectorH 3 (m + 1) :=
  t⁻¹ • physicalMap (m + 1) (Real.log t) (cutoffForcing D R (m + 1) (Real.log t))

/-- The linear coefficient in physical variables,
`A(t) = t⁻¹ P_{log t} (L_far(log t) - B) P_{log t}⁻¹`, from vector `Hᵐ⁺²` to vector `Hᵐ⁺¹`, with
the cutoff coefficient `L_far` and the transport `B` of the linearization at the profile. -/
def physicalCoefficient (m : ℕ) (t : ℝ) : VectorH 3 (m + 2) →L[ℝ] VectorH 3 (m + 1) :=
  t⁻¹ • ((physicalMap (m + 1) (Real.log t)).comp ((cutoffCoefficient D R (m + 1) (Real.log t) -
    (D.profileCoefficientBounds (m + 1)).transport).comp (physicalMap (m + 2) (-Real.log t))))

variable {D R} {s : ℝ}

/-- **The physical forcing through coefficient paths.** For `0 < t ≤ 1`,
`g(t) = f(t) + A(t) u_cor(t) - (u_cor(t)·∇) u_cor(t)` with the physical corrections of orders
`m + 1` and `m + 2`. -/
theorem physicalForcing_eq (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ}
    (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    physicalForcing D R s m hm t = physicalCutoffForcing D R m t +
      physicalCoefficient D R m t (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t) -
      mixedConvection (m + 1) (three_lt_two_mul_succ hm) (physicalCorrection D R s m hm t)
        (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t) := by
  have hτ : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  rw [physicalForcing, liftForcing, correctionOperator, sub_apply, sub_apply,
    vectorLower_correctionLift_succ hR hs hm hτ, map_add, map_sub, map_sub,
    physicalMap_mixedConvection, Real.exp_log ht, smul_add, smul_sub, smul_sub, smul_smul,
    inv_mul_cancel₀ ht.ne', one_smul]
  simp only [physicalCutoffForcing, physicalCoefficient, physicalCorrection,
    smul_apply, ContinuousLinearMap.comp_apply, physicalMap_neg_physicalMap,
    sub_apply, map_sub, smul_sub]
  abel

/-- **Smoothness in time from smooth coefficient paths.** Above the threshold radius and for
`s ∈ [0, 1]`, if the cutoff forcing path and the linear coefficient path in physical variables
are smooth on `(0, 1)` at every order, then the physical correction is `Cʲ` on `(0, 1)` with
values in every vector `Hᵐ⁺¹`, for every `j`. -/
theorem contDiffOn_physicalCorrection_of_coefficients (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hf : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffForcing D R m) (Ioo 0 1))
    (hA : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCoefficient D R m) (Ioo 0 1)) :
    ∀ (j m : ℕ) (hm : (3 : ℝ) < 2 * m),
      ContDiffOn ℝ j (physicalCorrection D R s m hm) (Ioo 0 1) := by
  refine contDiffOn_physicalCorrection_of_forcing hR hs fun j hu m hm ↦ ?_
  have hm' := three_lt_two_mul_succ hm
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hc : ContDiffOn ℝ j (fun t ↦ physicalCutoffForcing D R m t +
      physicalCoefficient D R m t (physicalCorrection D R s (m + 1) hm' t) -
      mixedConvection (m + 1) hm' (physicalCorrection D R s m hm t)
        (physicalCorrection D R s (m + 1) hm' t)) (Ioo 0 1) :=
    (((hf m).of_le hj).add (((hA m).of_le hj).clm_apply (hu (m + 1) hm'))).sub
      (((mixedConvection (m + 1) hm').contDiff.comp_contDiffOn (hu m hm)).clm_apply
        (hu (m + 1) hm'))
  exact hc.congr fun t ht ↦ physicalForcing_eq hR hs hm ht.1 ht.2.le

/-- **Joint smoothness of the correction field from smooth coefficient paths.** Under the
hypotheses of `contDiffOn_physicalCorrection_of_coefficients`, the correction part
`t^{-1/2} U_cor(log t, x / √t)` of the physical velocity is jointly smooth on `(0, 1) × ℝ³`. -/
theorem contDiffOn_physicalCorrectionField_of_coefficients (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hf : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffForcing D R m) (Ioo 0 1))
    (hA : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCoefficient D R m) (Ioo 0 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ^3 ↦
      (Real.sqrt p.1)⁻¹ • correctionField D R s (Real.log p.1) ((Real.sqrt p.1)⁻¹ • p.2))
      (Ioo 0 1 ×ˢ univ) := by
  refine contDiffOn_infty.mpr fun r ↦ ?_
  have hm : (3 : ℝ) < 2 * ((r + 3 : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hk := three_lt_two_mul_succ_sub_one hm
  have hr : ((3 : ℕ) : ℝ) < 2 * (((r + 3 + 1 : ℕ) : ℝ) - (r : ℝ) - 1) := by
    push_cast
    linarith
  refine contDiffOn_piLp' 2 fun j ↦ ?_
  have hu : ContDiffOn ℝ r (fun t ↦ physicalCorrection D R s (r + 3) hm t j) (Ioo 0 1) :=
    (contDiffOn_piLp 2).mp (contDiffOn_physicalCorrection_of_coefficients hR hs hf hA r
      (r + 3) hm) j
  have h := PDE.Hyperbolic.NonlinearWave.Cauchy.contDiffOn_joint_classicalRepresentative
    isOpen_Ioo hk hr hu
  refine h.congr fun p hp ↦ ?_
  have heq := congrFun (classicalRepresentativeCLM_physicalCorrection hR hs hm hp.1.1
    hp.1.2.le j) p.2
  exact heq.symm

end NavierStokes.Nonuniqueness

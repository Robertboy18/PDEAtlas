/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarVector
public import PDE.Spaces.Sobolev.GraphSpace.Operators.VectorMultiplier
import PDE.Analysis.Fredholm.CompactAdjoint
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.BoundedMultiplier

/-!
# Heat smoothing after a localized multiplier is compact

Let `a` be a bounded coefficient with compact essential support. Multiplication by `a` after
the heat operator at a positive time is compact on `L²`: the heat operator gains one
derivative, and multiplication by `a` is compact from `H¹` to `L²` by the Rellich theorem.
The heat operator is self-adjoint, since its Fourier symbol is real, and multiplication by a real
coefficient is symmetric. So heat smoothing after multiplication by `a` is the adjoint of a
compact operator, and is compact by Schauder's theorem.

Spatial dilation is bounded, so the same holds for the free self-similar evolution at a
positive time, and for its componentwise action on vector fields.

The real heat operator `heatBaseL2` acts on the base coordinate space `DerivLp n 2 univ`, the
Hilbert space on which the Rellich theorem and the `L∞` multipliers are stated.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev InnerProductSpace ComplexConjugate

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- The heat symbol is real. -/
theorem conj_heatSymbolLinf_ae (t : ℝ≥0) :
    ∀ᵐ ξ ∂volume, conj (heatSymbolLinf n t ξ) = heatSymbolLinf n t ξ := by
  filter_upwards [MemLp.coeFn_toLp (memLp_top_heatSymbol (n := n) t)] with ξ hξ
  rw [heatSymbolLinf, hξ, heatSymbol, Complex.conj_ofReal]

/-- The L² heat operator is self-adjoint. -/
theorem isSelfAdjoint_heatL2 (t : ℝ≥0) : IsSelfAdjoint (heatL2 n t) :=
  PDE.Analysis.Fourier.isSelfAdjoint_fourierMultiplierL2 (conj_heatSymbolLinf_ae t)

/-- The heat operator on real whole-space `L²` base coordinates. -/
def heatBaseL2 (n : ℕ) (t : ℝ≥0) : DerivLp n 2 univ →L[ℝ] DerivLp n 2 univ :=
  wkpBaseCoordinateCLM.comp ((heatSobolev n 0 t).comp
    (lpEquivZeroOrder (n := n) (p := 2) (Ω := univ)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The real heat operator is the base coordinate of the heat operator on `W^{0,2}`. -/
theorem heatBaseL2_apply (t : ℝ≥0) (f : DerivLp n 2 univ) :
    heatBaseL2 n t f = wkpBaseCoordinateCLM (heatSobolev n 0 t (lpEquivZeroOrder f)) :=
  rfl

/-- Complexification intertwines the real and the complex heat operators. -/
theorem complexifyL2CLM_heatBaseL2 (t : ℝ≥0) (f : DerivLp n 2 univ) :
    complexifyL2CLM n (heatBaseL2 n t f) = heatL2 n t (complexifyL2CLM n f) := by
  rw [heatBaseL2_apply, complexifyL2CLM_base, baseL2_heatSobolev, ← complexifyL2CLM_base]
  rfl

/-- The real heat operator is self-adjoint. -/
theorem isSelfAdjoint_heatBaseL2 (t : ℝ≥0) : IsSelfAdjoint (heatBaseL2 n t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪heatBaseL2 n t f, g⟫_ℝ = ⟪f, heatBaseL2 n t g⟫_ℝ
  rw [inner_eq_re_inner_complexifyL2CLM, inner_eq_re_inner_complexifyL2CLM,
    complexifyL2CLM_heatBaseL2, complexifyL2CLM_heatBaseL2]
  exact congrArg Complex.re ((isSelfAdjoint_heatL2 t).isSymmetric _ _)

/-- At positive times the real heat operator is the base coordinate of the gaining operator. -/
theorem heatBaseL2_eq_gain {t : ℝ≥0} (ht : 0 < (t : ℝ)) (f : DerivLp n 2 univ) :
    heatBaseL2 n t f = wkpBaseCoordinateCLM (heatGainSobolev n 0 t ht (lpEquivZeroOrder f)) := by
  apply complexifyL2CLM_injective
  rw [complexifyL2CLM_heatBaseL2, complexifyL2CLM_base, baseL2_heatGainSobolev,
    ← complexifyL2CLM_base]
  rfl

variable {a : DerivLp n ∞ univ} {K : Set (ℝ^n)}

/-- Localization after heat smoothing at a positive time is compact on `L²`. -/
theorem isCompactOperator_mulLpLeft_comp_heatBaseL2 {t : ℝ≥0} (ht : 0 < t) (hK : IsCompact K)
    (ha : ∀ᵐ x ∂volume, a x = 0 ∨ x ∈ K) :
    IsCompactOperator ((mulLpLeft a).comp (heatBaseL2 n t)) := by
  have ht' : (0 : ℝ) < t := ht
  have heq : (mulLpLeft a).comp (heatBaseL2 n t) =
      ((mulLpLeft (p := 2) a).comp (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2)
        (Ω := univ))).comp ((heatGainSobolev n 0 t ht').comp
          ((lpEquivZeroOrder (n := n) (p := 2) (Ω := univ)).toContinuousLinearEquiv
            |>.toContinuousLinearMap)) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [ContinuousLinearMap.comp_apply]
    rw [heatBaseL2_eq_gain ht']
    rfl
  rw [heq]
  exact (RellichKondrachov.isCompactOperator_mulLpLeft_comp_base (by norm_num) a hK ha).comp_clm _

/-- Heat smoothing at a positive time after localization is compact on `L²`. It is the adjoint
of localization after heat smoothing. -/
theorem isCompactOperator_heatBaseL2_comp_mulLpLeft {t : ℝ≥0} (ht : 0 < t) (hK : IsCompact K)
    (ha : ∀ᵐ x ∂volume, a x = 0 ∨ x ∈ K) :
    IsCompactOperator ((heatBaseL2 n t).comp (mulLpLeft a)) := by
  have hadj : (heatBaseL2 n t).comp (mulLpLeft a) =
      ((mulLpLeft a).comp (heatBaseL2 n t)).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro f g
    simp only [ContinuousLinearMap.comp_apply, mulLpLeft_apply]
    have h : ⟪heatBaseL2 n t (a • f), g⟫_ℝ = ⟪a • f, heatBaseL2 n t g⟫_ℝ :=
      (isSelfAdjoint_heatBaseL2 t).isSymmetric _ _
    rw [h, inner_lpSMul_left_eq_right]
  rw [hadj]
  exact PDE.Analysis.isCompactOperator_adjoint
    (isCompactOperator_mulLpLeft_comp_heatBaseL2 ht hK ha)

/-- Heat smoothing at a positive time after localization is compact on `W^{0,2}`. -/
theorem isCompactOperator_heatSobolev_comp_wkMultiplication {t : ℝ≥0} (ht : 0 < t)
    (hK : IsCompact K) (ha : ∀ᵐ x ∂volume, a x = 0 ∨ x ∈ K) :
    IsCompactOperator ((heatSobolev n 0 t).comp (wkMultiplication 0 (lpToZeroOrder a))) := by
  have heq : (heatSobolev n 0 t).comp (wkMultiplication 0 (lpToZeroOrder a)) =
      (((lpEquivZeroOrder (n := n) (p := 2) (Ω := univ)).toContinuousLinearEquiv
        |>.toContinuousLinearMap).comp ((heatBaseL2 n t).comp (mulLpLeft a))).comp
          wkpBaseCoordinateCLM := by
    apply ContinuousLinearMap.ext
    intro u
    apply (lpEquivZeroOrder (n := n) (p := 2) (Ω := univ)).symm.injective
    change wkpBaseCoordinateCLM (heatSobolev n 0 t (wkMultiplication 0 (lpToZeroOrder a) u)) =
      wkpBaseCoordinateCLM (heatSobolev n 0 t (lpEquivZeroOrder
        (mulLpLeft a (wkpBaseCoordinateCLM u))))
    congr 2
  rw [heq]
  exact ((isCompactOperator_heatBaseL2_comp_mulLpLeft ht hK ha).clm_comp
    ((lpEquivZeroOrder (n := n) (p := 2) (Ω := univ)).toContinuousLinearEquiv
      |>.toContinuousLinearMap)).comp_clm wkpBaseCoordinateCLM

/-- The free self-similar evolution at a positive time after localization is compact on
`W^{0,2}`. -/
theorem isCompactOperator_selfsimilarHeatSobolev_comp_wkMultiplication {τ : ℝ≥0} (hτ : 0 < τ)
    (hK : IsCompact K) (ha : ∀ᵐ x ∂volume, a x = 0 ∨ x ∈ K) :
    IsCompactOperator
      ((selfsimilarHeatSobolev n 0 τ).comp (wkMultiplication 0 (lpToZeroOrder a))) := by
  have heq : (selfsimilarHeatSobolev n 0 τ).comp (wkMultiplication 0 (lpToZeroOrder a)) =
      selfsimilarFactor τ • ((dilationWkpCLM (by norm_num) (selfsimilarFactor τ)
        (selfsimilarFactor_pos τ).ne').comp
          ((heatSobolev n 0 (selfsimilarHeatTime τ)).comp
            (wkMultiplication 0 (lpToZeroOrder a)))) := by
    rw [selfsimilarHeatSobolev, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc]
  rw [heq]
  exact ((isCompactOperator_heatSobolev_comp_wkMultiplication
    (NNReal.coe_pos.mp (selfsimilarHeatTime_pos hτ)) hK ha).clm_comp
      (dilationWkpCLM (by norm_num) (selfsimilarFactor τ) (selfsimilarFactor_pos τ).ne')).smul
        (selfsimilarFactor τ)

/-- The free self-similar evolution at a positive time after localization is compact on vector
`L²` fields. -/
theorem isCompactOperator_vectorSelfsimilarHeat_comp_vectorMul {τ : ℝ≥0} (hτ : 0 < τ)
    (hK : IsCompact K) (ha : ∀ᵐ x ∂volume, a x = 0 ∨ x ∈ K) :
    IsCompactOperator ((vectorSelfsimilarHeat n 0 τ).comp (vectorMul n a)) := by
  have heq : (vectorSelfsimilarHeat n 0 τ).comp (vectorMul n a) =
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦
        (selfsimilarHeatSobolev n 0 τ).comp (wkMultiplication 0 (lpToZeroOrder a))) := by
    apply ContinuousLinearMap.ext
    intro u
    apply PiLp.ext
    intro j
    simp only [ContinuousLinearMap.comp_apply, vectorSelfsimilarHeat_apply, vectorMul_apply,
      ContinuousLinearMap.piLpMap_apply]
  rw [heq]
  exact ContinuousLinearMap.isCompactOperator_piLpMap 2 _
    fun _ ↦ isCompactOperator_selfsimilarHeatSobolev_comp_wkMultiplication hτ hK ha

end HeatEquation.WholeSpace

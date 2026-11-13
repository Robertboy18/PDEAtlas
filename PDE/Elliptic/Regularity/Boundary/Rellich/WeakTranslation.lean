/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.PoissonWeakForm
public import PDE.Spaces.Sobolev.Compactness.Rellich.FiniteExponentTranslation

/-!
# Weak Poisson energy under an admissible translation

Let `z ∈ H¹₀(Ω)` satisfy `Δz = f ∈ L²(Ω)`, and let `Z` be its Sobolev zero
extension. If the restriction of `Z(· + a)` belongs to `H¹₀(Ω)`, it is an
admissible energy test. Translation is an isometry, so testing with the difference
gives half the squared gradient translation defect. The first-order translation
estimate for the base coordinate then bounds this squared defect linearly in `‖a‖`.

Translation is composition with `x ↦ x + a`. In particular, moving the support
inward along `v` through distance `t` uses `a = -(t • v)`. Admissibility is an
explicit hypothesis here; no boundary geometry or boundary-strip estimate is asserted.
Only first weak derivatives are extended by zero.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Rellich

open MeasureTheory Set
open ZeroTrace
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Restricting the base-coordinate translation defect of a zero extension preserves
its linear translation bound. No admissibility or equation is needed. -/
theorem norm_base_sub_restrict_translate_zeroExtend_le
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω)) (a : ℝ^n) :
    ‖baseCoordCLM z - wkpBaseCoordinateCLM
        (restrictCLM hΩ (subset_univ Ω) (translateH1 a (zeroExtendH10 hΩ z)))‖ ≤
      (n : ℝ) * ‖a‖ * ‖z‖ := by
  let Z : H¹(ℝ^n) := zeroExtendH10 hΩ z
  let b : DerivLp n 2 Set.univ := wkpBaseCoordinateCLM Z
  have hbase : b = Extension.Lp.zeroExtendLp hΩ (baseCoordCLM z) :=
    zeroExtendAmbient_apply hΩ ((z : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)
  have htranslate : wkpBaseCoordinateCLM (translateH1 a Z) = translateLp 2 a b :=
    translateH1_apply a Z (baseIndex n 1)
  have hrestrict : wkpBaseCoordinateCLM
      (restrictCLM hΩ (subset_univ Ω) (translateH1 a Z)) =
      restrictDerivLp (subset_univ Ω) (translateLp 2 a b) := by
    change restrictDerivLp (subset_univ Ω)
      (wkpBaseCoordinateCLM (translateH1 a Z)) = _
    rw [htranslate]
  have hdifference : baseCoordCLM z - wkpBaseCoordinateCLM
      (restrictCLM hΩ (subset_univ Ω) (translateH1 a Z)) =
      restrictDerivLp (subset_univ Ω) (b - translateLp 2 a b) := by
    rw [map_sub, hrestrict, hbase, Extension.Lp.restrict_zeroExtendLp]
  calc
    _ = ‖restrictDerivLp (subset_univ Ω) (b - translateLp 2 a b)‖ :=
      congrArg norm hdifference
    _ ≤ ‖b - translateLp 2 a b‖ := norm_restrictDerivLp_le (subset_univ Ω) _
    _ = ‖translateLp 2 a b - b‖ := norm_sub_rev _ _
    _ ≤ (n : ℝ) * ‖a‖ * ‖Z‖ :=
      norm_translateLp_base_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞) a Z
    _ = _ := by rw [norm_zeroExtendH10]

/-- For a distributional solution of `Δz = f`, subtracting an admissible translate
of its zero extension gives an exact energy identity. The gradient defect is a
whole-space `L²` norm; the forcing pairs only with the restricted base defect. -/
theorem half_norm_gradient_zeroExtend_sub_translate_sq_eq
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure n Ω) = ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω)
    (a : ℝ^n)
    (hadmissible : restrictCLM hΩ (subset_univ Ω)
      (translateH1 a (zeroExtendH10 hΩ z)) ∈ h10Submodule (Ω := Ω)) :
    (1 / 2 : ℝ) * ‖∇ (zeroExtendH10 hΩ z) -
        ∇ (translateH1 a (zeroExtendH10 hΩ z))‖ ^ 2 =
      ⟪-f, baseCoordCLM z - wkpBaseCoordinateCLM
        (restrictCLM hΩ (subset_univ Ω) (translateH1 a (zeroExtendH10 hΩ z)))⟫_ℝ := by
  classical
  let Z := zeroExtendH10 hΩ z
  let v : H¹₀(Ω) := ⟨restrictCLM hΩ (subset_univ Ω) (translateH1 a Z), hadmissible⟩
  have hzero (q : DerivIndex n 1) : (Z : WkpAmbientOn n 1 2 Set.univ) q =
      Extension.Lp.zeroExtendLp hΩ (coordCLM q z) := by
    simp only [Z, zeroExtendH10_apply_coe, zeroExtendAmbient_apply, coordCLM_apply]
  have htranslate (q : DerivIndex n 1) : coordCLM q v =
      restrictDerivLp (subset_univ Ω)
        (translateLp 2 a ((Z : WkpAmbientOn n 1 2 Set.univ) q)) := by
    simp only [v, coordCLM_apply, restrictCLM_apply_coe, restrictAmbient_apply,
      translateH1_apply]
  have hcoordinate (i : Fin n) :
      (1 / 2 : ℝ) * ‖(Z : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i) -
        translateLp 2 a ((Z : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))‖ ^ 2 =
      ⟪derivCoordCLM i z, derivCoordCLM i (z - v)⟫_ℝ := by
    let g := (Z : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)
    calc
      (1 / 2 : ℝ) * ‖g - translateLp 2 a g‖ ^ 2 =
          ⟪g, g - translateLp 2 a g⟫_ℝ := by
        rw [norm_sub_sq_real, norm_translateLp, inner_sub_right,
          real_inner_self_eq_norm_sq]
        ring
      _ = ⟪derivCoordCLM i z, restrictDerivLp (subset_univ Ω)
          (g - translateLp 2 a g)⟫_ℝ := by
        change ⟪(Z : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i), _⟫_ℝ = _
        rw [hzero]
        exact Extension.Lp.inner_zeroExtendLp_eq_inner_restrict hΩ _ _
      _ = ⟪derivCoordCLM i z, derivCoordCLM i (z - v)⟫_ℝ := by
        rw [map_sub, map_sub]
        change ⟪_, restrictDerivLp (subset_univ Ω) g - _⟫_ℝ = _
        rw [show restrictDerivLp (subset_univ Ω) g = derivCoordCLM i z by
          dsimp only [g]
          rw [hzero, Extension.Lp.restrict_zeroExtendLp]]
        rw [← htranslate]
  have henergy := poisson_weakForm_of_integral_laplacian_eq (z : H¹(Ω)) f hweak (z - v)
  calc
    (1 / 2 : ℝ) * ‖∇ Z - ∇ (translateH1 a Z)‖ ^ 2 =
        ∑ i : Fin n, ⟪derivCoordCLM i z, derivCoordCLM i (z - v)⟫_ℝ := by
      rw [← map_sub, norm_wkpGradientCLM_sq_eq_sum_deriv_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Submodule.coe_sub, PiLp.sub_apply, translateH1_apply] using hcoordinate i
    _ = ⟪-f, baseCoordCLM (z - v)⟫_ℝ := henergy
    _ = _ := by rw [map_sub]; rfl

/-- An admissible translation of a weak Poisson solution has squared gradient
translation defect at most `2n ‖a‖ ‖f‖₂ ‖z‖H¹`. This uses the base-coordinate
translation estimate, without assuming any translation modulus for the gradient. -/
theorem norm_gradient_zeroExtend_sub_translate_sq_le
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure n Ω) = ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω)
    (a : ℝ^n)
    (hadmissible : restrictCLM hΩ (subset_univ Ω)
      (translateH1 a (zeroExtendH10 hΩ z)) ∈ h10Submodule (Ω := Ω)) :
    ‖∇ (zeroExtendH10 hΩ z) - ∇ (translateH1 a (zeroExtendH10 hΩ z))‖ ^ 2 ≤
      2 * (n : ℝ) * ‖a‖ * ‖f‖ * ‖z‖ := by
  have hid := half_norm_gradient_zeroExtend_sub_translate_sq_eq hΩ z f hweak a hadmissible
  have hinner := real_inner_le_norm (-f)
    (baseCoordCLM z - wkpBaseCoordinateCLM
      (restrictCLM hΩ (subset_univ Ω) (translateH1 a (zeroExtendH10 hΩ z))))
  rw [norm_neg] at hinner
  have hbase := mul_le_mul_of_nonneg_left
    (norm_base_sub_restrict_translate_zeroExtend_le hΩ z a) (norm_nonneg f)
  nlinarith

/-- Moving the support inward by `t v` means composing with `x ↦ x - t v`.
For every nonnegative step whose restriction is admissible, the squared gradient
translation defect is bounded linearly in `t`, including the zero step. -/
theorem norm_gradient_zeroExtend_sub_inward_translate_sq_le
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure n Ω) = ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω)
    (v : ℝ^n) {t : ℝ} (ht : 0 ≤ t)
    (hadmissible : restrictCLM hΩ (subset_univ Ω)
      (translateH1 (-(t • v)) (zeroExtendH10 hΩ z)) ∈ h10Submodule (Ω := Ω)) :
    ‖∇ (zeroExtendH10 hΩ z) - ∇ (translateH1 (-(t • v)) (zeroExtendH10 hΩ z))‖ ^ 2 ≤
      2 * (n : ℝ) * t * ‖v‖ * ‖f‖ * ‖z‖ := by
  simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_assoc] using
    norm_gradient_zeroExtend_sub_translate_sq_le hΩ z f hweak (-(t • v)) hadmissible

end SobolevSpace.GraphSpace.Rellich

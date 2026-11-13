/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
public import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.Analysis.Calculus.AbsoluteValue
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.PositivePart

/-!
# Absolute value in the zero-boundary energy space

Absolute value preserves `H¹₀(Ω)` for every open domain. The finite-exponent supported-closure
argument gives membership by smooth composition and strong Sobolev approximation. Here it is
applied at `p = 2`. No boundary regularity or boundedness of the domain is needed.

The weak chain rule gives the derivative coordinates. Products of two derivative
coordinates, and the `L²` mass, are unchanged.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace Sobolev

namespace SobolevSpace.GraphSpace

open ZeroTrace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Absolute value contracts the global `H¹` norm. This is a bound on each
individual function, not a Lipschitz bound on differences in the Sobolev norm. -/
theorem norm_absoluteValue_le (U : H¹(ℝ^n)) :
    ‖absoluteValue U‖ ≤ ‖U‖ := by
  let A := absoluteValue U
  have hcoord (a : DerivIndex n 1) :
      ‖(A : WkpAmbientOn n 1 2 univ) a‖ ≤ ‖(U : WkpAmbientOn n 1 2 univ) a‖ := by
    apply Lp.norm_le_norm_of_ae_le
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
    · subst a
      filter_upwards [absoluteValue_base_ae U]
        with x hx
      change ‖((absoluteValue U :
        WkpAmbientOn n 1 2 univ) (baseIndex n 1) : ℝ^n → ℝ) x‖ ≤ _
      rw [hx, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs]
    · subst a
      filter_upwards [absoluteValue_derivative_ae U i] with x hx
      change ‖((absoluteValue U :
        WkpAmbientOn n 1 2 univ) (singleDerivIndex n i) : ℝ^n → ℝ) x‖ ≤ _
      rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (PDE.Analysis.Calculus.abs_coe_sign_le_one _)
  have hsq : ‖A‖ ^ 2 ≤ ‖U‖ ^ 2 := by
    change ‖(A : WkpAmbientOn n 1 2 univ)‖ ^ 2 ≤
      ‖(U : WkpAmbientOn n 1 2 univ)‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum fun a _ ↦
      pow_le_pow_left₀ (norm_nonneg _) (hcoord a) 2
  exact (sq_le_sq₀ (norm_nonneg A) (norm_nonneg U)).mp hsq

/-- Take the absolute value of the global zero extension and restrict to the
original domain. Zero-boundary membership is `absoluteValueH1OfH10_mem`. -/
def absoluteValueH1OfH10 (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) :
    H¹(Ω) :=
  restrictCLM (n := n) (k := 1) (p := 2) hΩ (subset_univ Ω)
    (absoluteValue (zeroExtendH10 hΩ u))

/-- Each coordinate of the zero extension agrees almost everywhere on the
original domain with the original Sobolev coordinate. -/
private theorem zeroExtendH10_coordinate_ae_on
    (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) (a : DerivIndex n 1) :
    (((zeroExtendH10 hΩ u : WkpAmbientOn n 1 2 univ) a : DerivLp n 2 univ) :
      ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      ((((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) a : DerivLp n 2 Ω) :
        ℝ^n → ℝ) := by
  have h := (zeroExtendH10_coordinate_apply_ae hΩ u a).filter_mono
    (ae_mono (Measure.restrict_le_self (μ := volume) (s := Ω)))
  filter_upwards [h, ae_restrict_mem hΩ] with x hx hxΩ
  simpa only [indicator_of_mem hxΩ] using hx

/-- The base coordinate is the absolute value of the original `L²` function. -/
theorem absoluteValueH1OfH10_base_ae (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) :
    (wkpBaseCoordinateCLM (absoluteValueH1OfH10 hΩ u) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ |(baseCoordCLM u : ℝ^n → ℝ) x| := by
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simpa [domainMeasure] using (Measure.restrict_le_self (μ := volume) (s := Ω))
  have hrestrict := restrictCLM_apply_ae hΩ (subset_univ Ω)
    (absoluteValue (zeroExtendH10 hΩ u)) (baseIndex n 1)
  have habs := (absoluteValue_base_ae
    (zeroExtendH10 hΩ u)).filter_mono (ae_mono hmeasure)
  filter_upwards [hrestrict, habs, zeroExtendH10_coordinate_ae_on hΩ u (baseIndex n 1)]
    with x hr ha hz
  exact hr.trans (ha.trans (congrArg abs hz))

/-- Restricting the absolute value of a zero extension does not increase its `H¹` norm. -/
theorem norm_absoluteValueH1OfH10_le (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) :
    ‖absoluteValueH1OfH10 hΩ u‖ ≤ ‖u‖ := by
  calc
    ‖absoluteValueH1OfH10 hΩ u‖ ≤
        ‖absoluteValue (zeroExtendH10 hΩ u)‖ :=
      norm_restrictCLM_apply_le hΩ (subset_univ Ω) _
    _ ≤ ‖zeroExtendH10 hΩ u‖ := norm_absoluteValue_le _
    _ = ‖u‖ := norm_zeroExtendH10 hΩ u

/-- Absolute value preserves `H¹₀` on every open domain, by the supported
Sobolev closure theorem at exponent two. -/
theorem absoluteValueH1OfH10_mem (hΩ : IsOpen Ω) (u : H¹₀(Ω)) :
    absoluteValueH1OfH10 hΩ.measurableSet u ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  have hext : zeroExtendH10 hΩ.measurableSet u =
      zeroExtendWkp0 hΩ.measurableSet u := rfl
  change restrictCLM hΩ.measurableSet (subset_univ Ω)
      (absoluteValue
        (zeroExtendH10 hΩ.measurableSet u)) ∈
    (wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω)).toSubmodule
  rw [hext]
  exact restrict_absoluteValue_zeroExtendWkp0_mem hΩ.measurableSet
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u

/-- Absolute value as an operation on `H¹₀` of an arbitrary open domain. -/
def absoluteValueH10 (hΩ : IsOpen Ω) (u : H¹₀(Ω)) : H¹₀(Ω) :=
  ⟨absoluteValueH1OfH10 hΩ.measurableSet u, absoluteValueH1OfH10_mem hΩ u⟩

/-- The zero-boundary absolute value represents the pointwise absolute value almost everywhere. -/
theorem absoluteValueH10_base_ae (hΩ : IsOpen Ω) (u : H¹₀(Ω)) :
    (baseCoordCLM (absoluteValueH10 hΩ u) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ |(baseCoordCLM u : ℝ^n → ℝ) x| :=
  absoluteValueH1OfH10_base_ae hΩ.measurableSet u

/-- Absolute value preserves the `L²` mass of a zero-boundary Sobolev function. -/
theorem norm_base_absoluteValueH10 (hΩ : IsOpen Ω) (u : H¹₀(Ω)) :
    ‖baseCoordCLM (absoluteValueH10 hΩ u)‖ = ‖baseCoordCLM (n := n) (Ω := Ω) u‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [absoluteValueH10_base_ae hΩ u] with x hx
    simp only [hx, Real.norm_eq_abs, abs_abs, le_refl]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [absoluteValueH10_base_ae hΩ u] with x hx
    simp only [hx, Real.norm_eq_abs, abs_abs, le_refl]

/-- The Sobolev chain rule, transported to the zero-boundary absolute value. -/
theorem absoluteValueH10_derivative_ae
    (hΩ : IsOpen Ω) (u : H¹₀(Ω)) (i : Fin n) :
    (derivCoordCLM i (absoluteValueH10 hΩ u) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ (SignType.sign ((baseCoordCLM u : ℝ^n → ℝ) x) : ℝ) *
        (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ) x := by
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simpa [domainMeasure] using (Measure.restrict_le_self (μ := volume) (s := Ω))
  have hrestrict := restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω)
    (absoluteValue
      (zeroExtendH10 hΩ.measurableSet u)) (singleDerivIndex n i)
  have habs := (absoluteValue_derivative_ae
    (zeroExtendH10 hΩ.measurableSet u) i).filter_mono (ae_mono hmeasure)
  filter_upwards [hrestrict, habs,
    zeroExtendH10_coordinate_ae_on hΩ.measurableSet u (baseIndex n 1),
    zeroExtendH10_coordinate_ae_on hΩ.measurableSet u (singleDerivIndex n i)]
      with x hr ha hb hd
  exact hr.trans (ha.trans (by
    rw [hb, hd]
    simp only [baseCoordCLM_apply, derivCoordCLM_apply]))

/-- Products of weak partial derivatives are unchanged by absolute value. On the
zero level set the original derivatives vanish, by the level-set theorem. -/
theorem absoluteValueH10_derivative_mul_ae
    (hΩ : IsOpen Ω) (u : H¹₀(Ω)) (i j : Fin n) :
    (fun x ↦ (derivCoordCLM i (absoluteValueH10 hΩ u) : ℝ^n → ℝ) x *
      (derivCoordCLM j (absoluteValueH10 hΩ u) : ℝ^n → ℝ) x) =ᵐ[domainMeasure n Ω]
    fun x ↦ (derivCoordCLM i u : ℝ^n → ℝ) x *
      (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x := by
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simpa [domainMeasure] using (Measure.restrict_le_self (μ := volume) (s := Ω))
  have hzero := (derivative_eq_zero_ae_of_base_eq_zero
    (zeroExtendH10 hΩ.measurableSet u) i).filter_mono (ae_mono hmeasure)
  filter_upwards [absoluteValueH10_derivative_ae hΩ u i,
    absoluteValueH10_derivative_ae hΩ u j, hzero,
    zeroExtendH10_coordinate_ae_on hΩ.measurableSet u (baseIndex n 1),
    zeroExtendH10_coordinate_ae_on hΩ.measurableSet u (singleDerivIndex n i)]
      with x hi hj hz hb hd
  rw [hi, hj]
  rcases lt_trichotomy ((baseCoordCLM u : ℝ^n → ℝ) x) 0 with hx | hx | hx
  · rw [sign_neg hx]
    simp
  · have hdi : (derivCoordCLM i u : ℝ^n → ℝ) x = 0 :=
      hd.symm.trans (hz (hb.trans hx))
    rw [hdi]
    simp
  · rw [sign_pos hx]
    simp

end SobolevSpace.GraphSpace

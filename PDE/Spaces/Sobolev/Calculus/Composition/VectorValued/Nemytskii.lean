/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.VectorValued.WeakChainRule

/-!
# Banach-valued Nemytskii operators on Sobolev spaces

A `C¹` map with bounded derivative acts on `W^{1,p}` whenever its composed
base belongs to `Lp`. The derivative rows are the Fréchet derivative
applied to the input rows. This construction works on arbitrary open domains,
for arbitrary real Banach codomains, including exponent infinity.

When the map fixes zero, the base membership follows automatically, even on
domains of infinite measure.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Φ : E → F} {C : ℝ≥0}

/-- The value and first derivative rows prescribed by nonlinear composition. -/
def compositionRows (Φ : E → F) (U : W^{1,p}(Ω; E)) :
    DerivIndex n 1 → ℝ^n → F :=
  firstOrderRows (fun x ↦ Φ (U.val (baseIndex n 1) x))
    (fun i x ↦ fderiv ℝ Φ (U.val (baseIndex n 1) x)
      (U.val (singleDerivIndex n i) x))

omit [Fact (1 ≤ p)] [CompleteSpace F] in
/-- Every prescribed derivative row belongs to `Lp`; only the base row needs
a separate hypothesis. -/
theorem compositionRows_memLp (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E))
    (hbase : MemLp (fun x ↦ Φ (U.val (baseIndex n 1) x)) p (domainMeasure n Ω))
    (a : DerivIndex n 1) :
    MemLp (compositionRows Φ U a) p (domainMeasure n Ω) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [compositionRows, firstOrderRows_baseIndex] using hbase
  · simpa only [compositionRows, firstOrderRows_singleDerivIndex] using
      memLp_fderiv_apply hΦ hbound (Lp.memLp (U.val (baseIndex n 1))).aestronglyMeasurable
        (Lp.memLp (U.val (singleDerivIndex n i)))

/-- The prescribed rows satisfy the Banach weak-derivative relation. -/
theorem compositionRows_weak (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E))
    (hbase : MemLp (fun x ↦ Φ (U.val (baseIndex n 1) x)) p (domainMeasure n Ω))
    (a : DerivIndex n 1) :
    HasWeakDerivativeOn Ω a.toList (compositionRows Φ U (baseIndex n 1))
      (compositionRows Φ U a) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [compositionRows, firstOrderRows_baseIndex, baseIndex_toList] using
      hasWeakDerivativeOn_nil
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hbase.locallyIntegrable Fact.out))
  · simpa only [compositionRows, firstOrderRows_baseIndex, firstOrderRows_singleDerivIndex,
      singleDerivIndex_toList] using hasWeakDerivativeOn_comp hΦ hbound U i

/-- Compose a Banach-valued Sobolev element with a `C¹` map of bounded derivative.
The explicit base membership allows nonzero values at zero on arbitrary domains. -/
def compositionOfMemLp (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E))
    (hbase : MemLp (fun x ↦ Φ (U.val (baseIndex n 1) x)) p (domainMeasure n Ω)) :
    W^{1,p}(Ω; F) :=
  ofWeakDerivatives (compositionRows Φ U) (compositionRows_memLp hΦ hbound U hbase)
    (compositionRows_weak hΦ hbound U hbase)

/-- The base of the constructed Sobolev element is the composed value almost everywhere. -/
theorem compositionOfMemLp_base_ae (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E))
    (hbase : MemLp (fun x ↦ Φ (U.val (baseIndex n 1) x)) p (domainMeasure n Ω)) :
    ((compositionOfMemLp hΦ hbound U hbase).val (baseIndex n 1) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦ Φ (U.val (baseIndex n 1) x) := by
  simpa only [compositionOfMemLp, compositionRows, firstOrderRows_baseIndex] using
    ofWeakDerivatives_apply_ae (compositionRows Φ U)
      (compositionRows_memLp hΦ hbound U hbase) (compositionRows_weak hΦ hbound U hbase)
      (baseIndex n 1)

/-- Each first derivative of the constructed element is the chain-rule expression. -/
theorem compositionOfMemLp_derivative_ae (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E))
    (hbase : MemLp (fun x ↦ Φ (U.val (baseIndex n 1) x)) p (domainMeasure n Ω))
    (i : Fin n) :
    ((compositionOfMemLp hΦ hbound U hbase).val (singleDerivIndex n i) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦
        fderiv ℝ Φ (U.val (baseIndex n 1) x) (U.val (singleDerivIndex n i) x) := by
  simpa only [compositionOfMemLp, compositionRows, firstOrderRows_singleDerivIndex] using
    ofWeakDerivatives_apply_ae (compositionRows Φ U)
      (compositionRows_memLp hΦ hbound U hbase) (compositionRows_weak hΦ hbound U hbase)
      (singleDerivIndex n i)

/-- The derivative bound on the composing map gives the sharp coordinate `Lp` bound. -/
theorem norm_derivative_compositionOfMemLp_le (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E))
    (hbase : MemLp (fun x ↦ Φ (U.val (baseIndex n 1) x)) p (domainMeasure n Ω))
    (i : Fin n) :
    ‖(compositionOfMemLp hΦ hbound U hbase).val (singleDerivIndex n i)‖ ≤
      C * ‖U.val (singleDerivIndex n i)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [compositionOfMemLp_derivative_ae hΦ hbound U hbase i] with x hx
  rw [hx]
  exact norm_chainIntegrand_le hbound
    (U.val (baseIndex n 1) x, U.val (singleDerivIndex n i) x)

/-- A zero-preserving `C¹` map with bounded derivative acts on every Banach-valued
first-order Sobolev space, including on domains of infinite measure. -/
def composition (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E)) :
    W^{1,p}(Ω; F) :=
  compositionOfMemLp hΦ hbound U
    (memLp_comp_of_bounded_fderiv hΦ hzero hbound (Lp.memLp (U.val (baseIndex n 1))))

/-- The zero-preserving operator has the expected base representative. -/
theorem composition_base_ae (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E)) :
    ((composition hΦ hzero hbound U).val (baseIndex n 1) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦ Φ (U.val (baseIndex n 1) x) :=
  compositionOfMemLp_base_ae hΦ hbound U _

/-- The zero-preserving operator has the expected first derivative representatives. -/
theorem composition_derivative_ae (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E)) (i : Fin n) :
    ((composition hΦ hzero hbound U).val (singleDerivIndex n i) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦
        fderiv ℝ Φ (U.val (baseIndex n 1) x) (U.val (singleDerivIndex n i) x) :=
  compositionOfMemLp_derivative_ae hΦ hbound U _ i

end SobolevSpace.VectorValued

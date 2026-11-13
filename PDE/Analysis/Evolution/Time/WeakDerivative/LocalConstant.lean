/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Bochner
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Constancy from a zero weak derivative on an interval

A compactly supported test of integral zero has a primitive supported in the same
open interval. This identifies the integral of a Banach-valued function against
each test with a fixed constant. Dual separation is applied to these Bochner
integrals before using distributional uniqueness, so no separability assumption
on the Banach space is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- A zero-integral smooth test supported inside an interval has a smooth
antiderivative compactly supported inside that interval. -/
theorem exists_compactSupport_antiderivative_on_Ioo_of_integral_eq_zero
    {a b : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ioo a b) (hzero : ∫ x, φ x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo a b ∧ ∀ x, HasDerivAt ψ (φ x) x := by
  rcases (tsupport φ).eq_empty_or_nonempty with hempty | hnonempty
  · have hφzero : φ = 0 := by
      ext x
      exact image_eq_zero_of_notMem_tsupport (by simp [hempty])
    subst φ
    exact ⟨0, contDiff_const, hcs, hsupp, fun x ↦ hasDerivAt_const x 0⟩
  obtain ⟨l, hl⟩ := hcs.exists_isLeast hnonempty
  obtain ⟨r, hr⟩ := hcs.exists_isGreatest hnonempty
  let ψ : ℝ → ℝ := fun x ↦ ∫ t in a..x, φ t
  have hd (x : ℝ) : HasDerivAt ψ (φ x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hφ.continuous.intervalIntegrable a x)
      hφ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hφ.continuous.continuousAt
  have hψ : ContDiff ℝ ∞ ψ := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
    have heq : deriv ψ = φ := funext fun x ↦ (hd x).deriv
    rwa [heq]
  have hsupport : Function.support ψ ⊆ Icc l r := by
    intro x hx
    by_contra hnot
    apply hx
    change (∫ t in a..x, φ t) = 0
    simp only [mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hleft | hright
    · apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have htmax : t ≤ max a x := ht.2
      exact (not_lt_of_ge (hl.2 hmem))
        (htmax.trans_lt (max_lt (hsupp hl.1).1 hleft))
    · rw [intervalIntegral.integral_eq_integral_of_support_subset, hzero]
      intro t ht
      have ht' := subset_tsupport φ ht
      exact ⟨(hsupp ht').1, (hr.2 ht').trans hright.le⟩
  have htsupport : tsupport ψ ⊆ Icc l r :=
    closure_minimal hsupport isClosed_Icc
  refine ⟨ψ, hψ, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport,
    ?_, hd⟩
  exact htsupport.trans fun _ hx ↦
    ⟨(hsupp hl.1).1.trans_le hx.1, hx.2.trans_lt (hsupp hr.1).2⟩

namespace Evolution.HasWeakTimeDerivativeOn

/-- A Banach-valued locally integrable function with zero weak derivative
on a nonempty open interval is almost everywhere constant there. -/
theorem exists_ae_eq_const_on_Ioo_of_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {a b : ℝ} (hab : a < b) {f : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) f 0) :
    ∃ c : X, f =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ c := by
  let bump : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  let ρ : ℝ → ℝ := bump.normed volume
  have hρ : ContDiff ℝ ∞ ρ := bump.contDiff_normed
  have hρcs : HasCompactSupport ρ := bump.hasCompactSupport_normed
  have hρint : Integrable ρ volume := bump.integrable_normed
  have hρone : ∫ x, ρ x = 1 := bump.integral_normed
  have hρsupp : tsupport ρ ⊆ Ioo a b := by
    rw [bump.tsupport_normed_eq, Real.closedBall_eq_Icc]
    intro x hx
    change (a + b) / 2 - (b - a) / 4 ≤ x ∧
      x ≤ (a + b) / 2 + (b - a) / 4 at hx
    constructor <;> linarith
  have hρf : Integrable (fun x ↦ ρ x • f x) volume :=
    integrable_smul_test hweak.locallyIntegrable_f hρ.continuous hρcs hρsupp
  let c : X := ∫ x, ρ x • f x
  refine ⟨c, ?_⟩
  have hzero : ∀ᵐ x ∂volume, x ∈ Ioo a b → f x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hweak.locallyIntegrable_f.sub
        (continuous_const.locallyIntegrable.locallyIntegrableOn _))
    intro φ hφ hφcs hφsupp
    have hφint : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφcs
    have hφf : Integrable (fun x ↦ φ x • f x) volume :=
      integrable_smul_test hweak.locallyIntegrable_f hφ.continuous hφcs hφsupp
    let ψ : ℝ → ℝ := fun x ↦ φ x - (∫ t, φ t) * ρ x
    have hψ : ContDiff ℝ ∞ ψ := hφ.sub (contDiff_const.mul hρ)
    have hψcs : HasCompactSupport ψ := hφcs.sub hρcs.mul_left
    have hψsupp : tsupport ψ ⊆ Ioo a b :=
      (tsupport_sub _ _).trans (union_subset hφsupp (tsupport_mul_subset_right.trans hρsupp))
    have hψzero : ∫ x, ψ x = 0 := by
      dsimp only [ψ]
      rw [integral_sub hφint (hρint.const_mul _), integral_const_mul, hρone,
        mul_one, sub_self]
    obtain ⟨χ, hχ, hχcs, hχsupp, hdχ⟩ :=
      exists_compactSupport_antiderivative_on_Ioo_of_integral_eq_zero
        hψ hψcs hψsupp hψzero
    have hz : (∫ x, ψ x • f x) = 0 := by
      have h := hweak.integral_smul_eq hχ hχcs hχsupp
      have hderiv : deriv χ = ψ := funext fun x ↦ (hdχ x).deriv
      simpa only [Pi.zero_apply, smul_zero, integral_zero, hderiv, neg_eq_zero] using h.symm
    have halg (x : ℝ) :
        ψ x • f x = φ x • f x - (∫ t, φ t) • (ρ x • f x) := by
      dsimp only [ψ]
      rw [sub_smul, mul_smul]
    have hscaled : Integrable (fun x ↦ (∫ t, φ t) • (ρ x • f x)) volume :=
      hρf.smul (∫ t, φ t)
    have heq : (∫ x, φ x • f x) = (∫ x, φ x) • c := by
      apply sub_eq_zero.mp
      calc
        (∫ x, φ x • f x) - (∫ x, φ x) • c =
            ∫ x, φ x • f x - (∫ t, φ t) • (ρ x • f x) := by
          rw [integral_sub hφf hscaled, integral_smul]
        _ = ∫ x, ψ x • f x := integral_congr_ae (.of_forall fun x ↦ (halg x).symm)
        _ = 0 := hz
    change (∫ x, φ x • (f x - c)) = 0
    simp_rw [smul_sub]
    rw [integral_sub hφf (hφint.smul_const c), integral_smul_const, heq, sub_self]
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hzero] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

end Evolution.HasWeakTimeDerivativeOn

end PDE.Analysis

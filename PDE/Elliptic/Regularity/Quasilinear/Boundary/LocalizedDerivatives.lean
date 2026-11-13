/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedEnergy
import PDE.Elliptic.Regularity.Boundary.H2.TangentialCommutator
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Weak derivatives from localized tangential quotient bounds

The energy estimate controls `η Dʰv`, whereas weak compactness applies to `Dʰ(ηv)`.
The discrete product rule relates them by `(Dʰη) τʰv`. This error is bounded by the
Lipschitz constant of the fixed cutoff, independently of the step.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal NNReal Topology

variable {n : ℕ} [Fact (0 < n)]

/-- The complementary discrete product rule retains the unshifted multiplier on the
quotient of the unknown. The translated factor occurs only in the cutoff error. -/
theorem tangentialDifferenceQuotient_lpSMul_unshifted
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (a : DerivLp n ∞ (HalfSpace.upper n)) (v : DerivLp n 2 (HalfSpace.upper n)) :
    tangentialDifferenceQuotientLp 2 k hk h (a • v) =
      a • tangentialDifferenceQuotientLp 2 k hk h v +
        tangentialDifferenceQuotientLp ∞ k hk h a • tangentialTranslateLp 2 k hk h v := by
  apply Lp.ext
  have hpres := (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving
  have hshift := hpres.tendsto_ae.eventually (Lp.coeFn_lpSMul (r := 2) a v)
  filter_upwards [
    tangentialDifferenceQuotientLp.apply_ae 2 k hk h (a • v),
    tangentialDifferenceQuotientLp.apply_ae 2 k hk h v,
    tangentialDifferenceQuotientLp.apply_ae ∞ k hk h a,
    tangentialTranslateLp.apply_ae 2 k hk h v,
    Lp.coeFn_lpSMul (r := 2) a v, hshift,
    Lp.coeFn_lpSMul (r := 2) a (tangentialDifferenceQuotientLp 2 k hk h v),
    Lp.coeFn_lpSMul (r := 2) (tangentialDifferenceQuotientLp ∞ k hk h a)
      (tangentialTranslateLp 2 k hk h v),
    Lp.coeFn_add (a • tangentialDifferenceQuotientLp 2 k hk h v)
      (tangentialDifferenceQuotientLp ∞ k hk h a • tangentialTranslateLp 2 k hk h v)]
    with x hd hdv hda htv hav havt hmul hmult hadd
  change (a • v) x = a x * v x at hav
  change (a • v) (x + coordinateStep k h) =
    a (x + coordinateStep k h) * v (x + coordinateStep k h) at havt
  simp only [hd, hadd, Pi.add_apply, hmul, hmult, smul_eq_mul, Pi.mul_apply,
    hav, havt, hdv, hda, htv]
  ring

/-- A Lipschitz multiplier transfers the weighted quotient bound to a quotient of
the product, with precisely one cutoff commutator. -/
theorem norm_tangentialDifferenceQuotient_lpSMul_le
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (a : DerivLp n ∞ (HalfSpace.upper n)) (η : ℝ^n → ℝ) {D : ℝ≥0}
    (hη : LipschitzWith D η)
    (ha : (a : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] η)
    (v : DerivLp n 2 (HalfSpace.upper n)) {h : ℝ} (hh : h ≠ 0) :
    ‖tangentialDifferenceQuotientLp 2 k hk h (a • v)‖ ≤
      ‖a • tangentialDifferenceQuotientLp 2 k hk h v‖ + D * ‖v‖ := by
  rw [tangentialDifferenceQuotient_lpSMul_unshifted]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (Lp.norm_smul_le _ _).trans
  rw [tangentialTranslateLp.norm]
  exact mul_le_mul_of_nonneg_right
    (tangentialDifferenceQuotientLp.norm_top_le k hk a η hη ha h hh) (norm_nonneg _)

/-- Uniform weighted quotients for small positive steps produce a localized
weak derivative. The derivative is obtained by weak compactness of the zero extension,
then restricted to the half-space. No trace of `v` is assumed. -/
theorem exists_localized_tangential_weakDerivative
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (a : DerivLp n ∞ (HalfSpace.upper n)) (η : ℝ^n → ℝ) {D : ℝ≥0}
    (hη : LipschitzWith D η)
    (ha : (a : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] η)
    (v : DerivLp n 2 (HalfSpace.upper n)) {ρ B : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ h : ℝ, 0 < h → h ≤ ρ →
      ‖a • tangentialDifferenceQuotientLp 2 k hk h v‖ ≤ B) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n), ‖g‖ ≤ B + D * ‖v‖ ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [k] (a • v : DerivLp n 2 (HalfSpace.upper n))
        (g : ℝ^n → ℝ) := by
  let step : ℕ → ℝ := collarStep ρ
  have hpos (j : ℕ) : 0 < step j := by
    change 0 < ρ / ((j : ℝ) + 1)
    positivity
  have hsmall (j : ℕ) : step j ≤ ρ :=
    (le_abs_self (step j)).trans (abs_collarStep_le hρ j)
  have hzero : Tendsto step atTop (𝓝 0) := tendsto_collarStep_zero ρ
  have hquot (j : ℕ) :
      ‖differenceQuotientLp 2 k (step j)
        (Extension.Lp.zeroExtendLp (HalfSpace.measurableSet_upper n) (a • v))‖ ≤
        B + D * ‖v‖ := by
    rw [tangentialDifferenceQuotientL2.norm_zeroExtend_eq k hk]
    exact (norm_tangentialDifferenceQuotient_lpSMul_le k hk a η hη ha v
      (hpos j).ne').trans (add_le_add (hbound (step j) (hpos j) (hsmall j)) le_rfl)
  obtain ⟨G, hGnorm, hG⟩ :=
    exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm
      k step hzero (fun j ↦ (hpos j).ne') _ _ hquot
  obtain ⟨g, hgnorm, hg⟩ :=
    exists_restrictedWeakDerivative_of_zeroExtend_with_norm
      (HalfSpace.measurableSet_upper n) k (a • v) G hG
  exact ⟨g, hgnorm.trans hGnorm, hg⟩

end PDE.Elliptic.Regularity.Quasilinear

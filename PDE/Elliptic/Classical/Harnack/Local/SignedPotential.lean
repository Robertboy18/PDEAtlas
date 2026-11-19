/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.ExponentialExtension
public import PDE.Elliptic.Classical.Harnack.Local.ZeroPotential

/-!
# Signed potentials by exponential extension

For `v(s,x) = exp(s) u(x)`, use principal matrix `diag(1,a(x))` and
drift `(1+c(x),b(x))`. The two added derivatives cancel the extra unit
coefficient, leaving `exp(s) Lu`. Thus arbitrary signed bounded potentials
reduce to the zero-potential comparison in one higher dimension.
No derivatives of any coefficient are taken.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis PDE.Common EllipticMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Uniform local Harnack comparison with a signed bounded potential.
The solution is only assumed nonnegative, and the constant precedes it. -/
theorem exists_signed_harnack_comparison
    {α τ B K : ℝ} (hα : 0 < α) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
        (z : ℝ^n) (r : ℝ), 0 < r → r ≤ 1 →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), (a x).PosSemidef) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), (a x).trace ≤ τ) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), ‖b x‖ ≤ B) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), |c x| ≤ K) →
        ∀ u : ℝ^n → ℝ,
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), ContDiffAt ℝ 2 u x) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), 0 ≤ u x) →
        (∀ x ∈ ball z (r * (16 * ((n : ℝ) + 2))), matrixOperator a b c u x = 0) →
        ∀ x ∈ closedBall z (r / 2), ∀ y ∈ closedBall z (r / 2), u x ≤ C * u y := by
  obtain ⟨C, hC, hcompare⟩ := exists_scaled_harnack_comparison (Nat.succ_pos n)
    (α := min 1 α) (τ := 1 + τ) (B := B + 1 + K)
    (lt_min zero_lt_one hα) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a b c z r hr hr₁ ha hell htrace hdrift hpotential u hreg hnonneg hsol x hx y hy
  let z' := timeSpaceCons 0 z
  have hmaps : MapsTo (spatialPart (n := n))
      (ball z' (r * (16 * (((n + 1 : ℕ) : ℝ) + 1))))
      (ball z (r * (16 * ((n : ℝ) + 2)))) := by
    intro p hp
    have h := dist_spatialPart_le p z'
    simp only [z', spatialPart_timeSpaceCons] at h
    rw [mem_ball] at hp ⊢
    have hR : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hR] at hp
    exact h.trans_lt hp
  have hsmall (q : ℝ^n) (hq : q ∈ closedBall z (r / 2)) :
      timeSpaceCons 0 q ∈ closedBall z' (r / 2) := by
    simpa only [mem_closedBall, z', dist_timeSpaceCons_zero] using hq
  have h := hcompare (liftedPrincipal a) (liftedDrift b c) z' r hr hr₁
    (fun p hp ↦ posSemidef_prependScalarBlock zero_le_one (ha _ (hmaps hp)))
    (fun p hp v ↦ elliptic_prependScalarBlock (hell _ (hmaps hp)) v)
    (fun p hp ↦ by
      change (prependScalarBlock 1 (a (spatialPart p))).trace ≤ 1 + τ
      rw [trace_prependScalarBlock]
      exact add_le_add le_rfl (htrace _ (hmaps hp)))
    (fun p hp ↦ norm_liftedDrift_le b c p (hdrift _ (hmaps hp)) (hpotential _ (hmaps hp)))
    (exponentialExtension u)
    (fun p hp ↦ contDiffAt_exponentialExtension (hreg _ (hmaps hp)))
    (fun p hp ↦ mul_nonneg (Real.exp_pos _).le (hnonneg _ (hmaps hp)))
    (fun p hp ↦ by
      rw [matrixOperator_exponentialExtension a b c (hreg _ (hmaps hp)),
        hsol _ (hmaps hp), mul_zero])
    (timeSpaceCons 0 x) (hsmall x hx) (timeSpaceCons 0 y) (hsmall y hy)
  simpa only [exponentialExtension_timeSpaceCons, Real.exp_zero, one_mul] using h

end EllipticHarnack

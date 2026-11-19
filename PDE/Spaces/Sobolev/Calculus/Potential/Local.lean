/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Potential.Ball

/-!
# Local weak potentials

A locally L² field with commuting weak derivatives admits an H¹ potential on
some ball around every point. This is local and requires no topology of the domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal Distributions Sobolev

namespace SobolevSpace

open GraphSpace

/-- A locally L² weakly closed field has an H¹ potential near each interior point. -/
theorem exists_local_weak_potential
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : IsOpen Ω) (F : ℝ^n → ℝ^n)
    (hF : ∀ i : Fin n, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
      MemLp (fun x ↦ F x i) 2 (volume.restrict K))
    (hweak : ∀ i j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      (∫ x in Ω, F x j * (∂[i] (φ : ℝ^n → ℝ)) x) =
        ∫ x in Ω, F x i * (∂[j] (φ : ℝ^n → ℝ)) x)
    (x : Ω) : ∃ r : ℝ, 0 < r ∧ ball x.val r ⊆ Ω ∧
      ∃ w : W^{1,2}(ball x.val r),
        (∇ w : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (ball x.val r)] F := by
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩ x.val x.property
  have hclosed : closedBall x.val (δ / 2) ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hδ)).trans hδΩ
  have houter : ball x.val (δ / 2) ⊆ Ω := ball_subset_closedBall.trans hclosed
  have hmem (i : Fin n) :
      MemLp (fun y ↦ F y i) 2 (volume.restrict (ball x.val (δ / 2))) :=
    (hF i _ (isCompact_closedBall _ _) hclosed).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hpair (i j : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφ : tsupport φ ⊆ ball x.val (δ / 2)) :
      (∫ y in ball x.val (δ / 2), F y j * (∂[i] (φ : ℝ^n → ℝ)) y) =
        ∫ y in ball x.val (δ / 2), F y i * (∂[j] (φ : ℝ^n → ℝ)) y := by
    have hsupport (k : Fin n) :
        tsupport (∂[k] (φ : ℝ^n → ℝ)) ⊆ ball x.val (δ / 2) :=
      (tsupport_iteratedPartialDeriv_subset_tsupport [k] φ).trans hφ
    have hset (k l : Fin n) {S : Set (ℝ^n)}
        (hS : ball x.val (δ / 2) ⊆ S) :
        (∫ y in S, F y l * (∂[k] (φ : ℝ^n → ℝ)) y) =
          ∫ y, F y l * (∂[k] (φ : ℝ^n → ℝ)) y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hnot : y ∉ tsupport (∂[k] (φ : ℝ^n → ℝ)) :=
        fun h ↦ hy (hS (hsupport k h))
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
    rw [hset i j Subset.rfl, hset j i Subset.rfl]
    simpa only [hset i j houter, hset j i houter] using
      hweak i j φ (hφ.trans houter)
  obtain ⟨w, hw⟩ :=
    exists_wkpSpaceOn_gradient_eq_on_ball_of_memLp_weakly_closed
      x.val (show 0 < δ / 4 by positivity) (show δ / 4 < δ / 2 by linarith)
      (fun i y ↦ F y i) hmem hpair
  refine ⟨δ / 4, by positivity, (ball_subset_ball (by linarith)).trans houter, w, ?_⟩
  exact hw.mono fun y hy ↦ PiLp.ext fun i ↦ hy i

end SobolevSpace

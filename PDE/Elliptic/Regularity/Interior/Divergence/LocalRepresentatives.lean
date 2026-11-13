/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Divergence.Ordinary
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Local

/-!
# Locally L² weak derivatives from a divergence equation

The interior estimate gives H¹ representatives on small balls.
Uniqueness of their weak derivatives and measurable gluing then give locally
L² derivative functions on the entire open domain. These functions satisfy
the original weak derivative identity, not only identities on the balls.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace Metric
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Distributions Laplacian

namespace PDE.Elliptic.Interior

variable {n : ℕ} {ι : Type*} [Fintype ι] {Ω : Opens (ℝ^n)}

/-- Domain L² data satisfying the ordinary equation `Δu = div f` determine
locally L² first weak derivatives throughout the domain. -/
theorem exists_locally_memLp_weak_derivatives_of_distributional_laplacian_eq
    (u : Lp ℝ 2 (domainMeasure n Ω))
    (f : ι → Lp ℝ 2 (domainMeasure n Ω)) (v : ι → ℝ^n)
    (heq : Δ (Distribution.ofFun Ω u volume ⊤) =
      ∑ i, Distribution.lineDerivCLM (v i)
        (Distribution.ofFun Ω (f i) volume ⊤)) :
    ∃ g : Fin n → ℝ^n → ℝ,
      (∀ k, AEStronglyMeasurable (g k) (domainMeasure n Ω)) ∧
      (∀ k, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp (g k) 2 (domainMeasure n K)) ∧
      ∀ k, HasWeakDerivativeOn Ω [k] (u : ℝ^n → ℝ) (g k) := by
  apply exists_weak_derivatives_of_local_representatives u
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  have hcompact : IsCompact (closure (ball x (r / 2))) :=
    (isCompact_closedBall x (r / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hclΩ : closure (ball x (r / 2)) ⊆ Ω :=
    closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self hr)).trans hsub)
  obtain ⟨U, hU⟩ := exists_wkpSpaceOn_one_ae_eq_of_distributional_laplacian_eq
    u f v heq isOpen_ball hcompact hclΩ
  exact ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr), U, hU⟩

end PDE.Elliptic.Interior

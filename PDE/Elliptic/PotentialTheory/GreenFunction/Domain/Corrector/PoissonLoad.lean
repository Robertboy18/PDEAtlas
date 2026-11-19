/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.InteriorLoad
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10

/-!
# The Poisson load of a regularized corrector

Subtract the smooth regularized pole from the harmonic corrector. The resulting
zero-trace field solves a Poisson equation whose source is the negative Laplacian
of that same regularization. We keep this source explicitly: its zero extension
is smooth and compactly supported inside the domain, as needed for the volume
potential near the boundary.
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped InnerProductSpace Sobolev Topology

/-- The regularized corrector has a smooth source supported strictly inside the
domain. The L² load represents this explicit source and satisfies the
variational equation of the given corrector. -/
theorem exists_interior_load_of_regularized_corrector
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {x : ℝ^n} (hx : x ∈ Ω)
    (U : H¹(Ω)) (A : ℝ^n → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAc : HasCompactSupport A)
    (w : H¹₀(Ω))
    (hw : (w : H¹(Ω)) = U - mkWkpSpaceOnOfContDiff A hA hAc)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i) U, derivCoordCLM i t⟫_ℝ) = 0)
    (hreg : ∀ z ∈ frontier Ω,
      A =ᶠ[𝓝 z] fun y ↦ fundamentalSolution n (y - x)) :
    let F := Ω.indicator (fun y ↦ -PDE.laplacian A y)
    ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ω ∧
      ∃ f : DerivLp n 2 Ω,
        (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] F ∧
        ∀ t : H¹₀(Ω),
          (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i) (w : H¹(Ω)),
            derivCoordCLM i t⟫_ℝ) = -⟪f, baseCoordCLM t⟫_ℝ := by
  let F := Ω.indicator (fun y ↦ -PDE.laplacian A y)
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_indicator_neg_laplacian hΩ hx hA hreg
  have hsupport : tsupport F ⊆ Ω :=
    tsupport_indicator_neg_laplacian_subset hΩ hx hreg
  have hFc : HasCompactSupport F :=
    hbounded.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
      (hsupport.trans subset_closure)
  have hFmem : MemLp F 2 (domainMeasure n Ω) :=
    hFs.continuous.memLp_of_hasCompactSupport hFc
  let f : DerivLp n 2 Ω := hFmem.toLp F
  have hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] F := hFmem.coeFn_toLp
  refine ⟨hFs, hFc, hsupport, f, hf, ?_⟩
  intro t
  have hpair :=
    sum_inner_gradient_sub_smooth_eq_integral_laplacian U A hA hAc w hw hweak t
  change (∑ i, ⟪derivCoordCLM i w, derivCoordCLM i t⟫_ℝ) =
    -⟪f, baseCoordCLM t⟫_ℝ
  rw [hpair, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hf, ae_restrict_mem hΩ.measurableSet] with y hfy hy
  simp only [RCLike.inner_apply, conj_trivial, hfy, F, indicator_of_mem hy,
    mul_neg, neg_neg]

end PotentialTheory.GreenFunction.Domain

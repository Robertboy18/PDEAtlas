/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Transport.InvariantRectangle
public import PDE.Analysis.Calculus.Jet.Slab
public import PDE.Analysis.Evolution.ODE.Nonautonomous.Bounded.Existence

/-!
# Characteristics of diagonal transport on a closed slab

The invariant rectangle bounds the velocity of the actual candidate. Spatial
derivatives on the time faces come from the continuous closure jet. These two
facts permit finite Picard trajectories without any growth assumption on the
candidate or its derivatives.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Transport

variable {ι : Type*} [Fintype ι]
  {T : ℝ} {v : ℝ × ℝ → ι → ℝ} {B : ι → (ι → ℝ) → ℝ}

/-- Every characteristic of a raw classical diagonal solution can be
constructed throughout the closed finite time slab. Both the speed bound and
the local spatial Lipschitz estimates are derived from the data and the jet. -/
theorem exists_characteristic_on_timeSlab
    (hT : 0 < T) (hB : ∀ i, ContDiff ℝ 1 (B i))
    (hv : ContinuousSecondJetOn v (Ioo (0 : ℝ) T ×ˢ univ))
    {lo hi : ι → ℝ}
    (hinit : ∀ x i, lo i ≤ v (0, x) i ∧ v (0, x) i ≤ hi i)
    (hpde : ∀ p : ℝ × ℝ, p.1 ∈ Ioo 0 T → ∀ i,
      fderiv ℝ v p (1, B i (v p)) i = 0)
    (i : ι) (t₀ : Icc (0 : ℝ) T) (x₀ : ℝ) :
    ∃ α : ℝ → ℝ, α t₀ = x₀ ∧ ContinuousOn α (Icc (0 : ℝ) T) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt α (B i (v (t, α t))) (Icc (0 : ℝ) T) t := by
  classical
  have hclosure : closure (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) =
      Icc (0 : ℝ) T ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo hT.ne, closure_univ]
  have hcont : ContinuousOn v (Icc (0 : ℝ) T ×ˢ univ) :=
    hclosure ▸ hv.continuousOn
  have hfirst : ContinuousOn hv.first (Icc (0 : ℝ) T ×ˢ univ) :=
    hclosure ▸ hv.continuousOn_first
  have hrange := rectangle_on_timeSlab hT (fun j ↦ (hB j).continuous)
    (fun j ↦ (continuous_apply j).comp_continuousOn hcont) hinit (by
      intro p hp j
      refine ⟨(ContinuousLinearMap.proj j).comp (hv.first p),
        (hasFDerivAt_pi'.mp (hv.hasFDerivAt (isOpen_Ioo.prod isOpen_univ)
          ⟨hp, mem_univ _⟩)) j, ?_⟩
      change hv.first p (1, B j (v p)) j = 0
      rw [hv.first_eq ⟨hp, mem_univ _⟩]
      exact hpde p hp j)
  have hcompact : IsCompact (Icc lo hi) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hB i).continuous.continuousOn
  let M : NNReal := ⟨max C 0, le_max_right _ _⟩
  let D : ℝ × ℝ → ℝ →L[ℝ] ℝ := fun p ↦
    ContinuousLinearMap.toSpanSingleton ℝ
      (fderiv ℝ (B i) (v p) (hv.first p (0, 1)))
  apply Evolution.exists_solution_Icc_of_bounded_of_continuous_spatial_fderiv
    (F := fun p ↦ B i (v p)) (D := D) (M := M) t₀ x₀
  · intro p hp
    exact (hC (v p) ⟨fun j ↦ (hrange p hp j).1,
      fun j ↦ (hrange p hp j).2⟩).trans (le_max_left _ _)
  · exact (hB i).continuous.comp_continuousOn hcont
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn
      (((hB i).continuous_fderiv (by norm_num)).comp_continuousOn hcont
        |>.clm_apply (hfirst.clm_apply continuousOn_const))
  · intro p hp
    exact (((hB i).differentiable (by norm_num) (v p)).hasFDerivAt.comp_hasDerivAt p.2
      (hv.hasDerivAt_spatial_of_mem_Icc hT hp p.2)).hasFDerivAt

end PDE.Analysis.Transport

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Analysis.ODE.ExistUnique

/-!
# Identifying a supplied baseline speed family

Two supplied families for the same field `f x - μ • x` agree on a closed time slab
when their initial speed sections agree at any anchor in that slab. The speed
neighborhood is common to all times. Mathlib's endpoint uniqueness theorems apply
on the two sides of the anchor, including when either side is a singleton.

Consequently the first speed derivatives agree on the entire closed slab. This
identifies a newly constructed baseline with a family fixed before a correction;
no flow, variation, or initial section is selected here.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Supplied solutions with a common initial speed section have the same closed-slab
values and first speed derivatives. The anchor may be either endpoint. Actual ODEs
are required at every time in the closed slab on one speed neighborhood.

Only the field must be `C¹`: time continuity follows from the ODEs, and equality
of speed derivatives follows from equality of germs. A derivative supplied for
one family therefore transfers to the other without solving a variational ODE. -/
theorem eqOn_speed_families_of_common_initial_data
    {F G : ℝ → ℝ → E} {f : E → E} {lo hi c : ℝ} {I : Set ℝ}
    (hc : c ∈ Icc lo hi) (hf : ContDiff ℝ 1 f) (hI : I ∈ 𝓝 (0 : ℝ))
    (hodeF : ∀ μ ∈ I, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ μ ∈ I, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) - μ • G t μ) t)
    (hinit : ∀ μ ∈ I, G c μ = F c μ) :
    (∀ μ ∈ I, EqOn (fun t ↦ G t μ) (fun t ↦ F t μ) (Icc lo hi)) ∧
      EqOn (fun t ↦ deriv (G t) 0) (fun t ↦ deriv (F t) 0) (Icc lo hi) := by
  have hagree (μ : ℝ) (hμ : μ ∈ I) :
      EqOn (fun t ↦ G t μ) (fun t ↦ F t μ) (Icc lo hi) := by
    have hFc : ContinuousOn (fun t ↦ F t μ) (Icc lo hi) :=
      HasDerivAt.continuousOn (hodeF μ hμ)
    have hGc : ContinuousOn (fun t ↦ G t μ) (Icc lo hi) :=
      HasDerivAt.continuousOn (hodeG μ hμ)
    let K : Set E := (fun t ↦ G t μ) '' Icc lo hi ∪ (fun t ↦ F t μ) '' Icc lo hi
    have hK : IsCompact K :=
      (isCompact_Icc.image_of_continuousOn hGc).union
        (isCompact_Icc.image_of_continuousOn hFc)
    have hv : ContDiff ℝ 1 (fun x ↦ f x - μ • x) :=
      hf.sub (ContDiff.const_smul μ contDiff_id)
    obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
      hv.locallyLipschitz.locallyLipschitzOn
    rw [← Icc_union_Icc_eq_Icc hc.1 hc.2]
    apply EqOn.union
    · have hsub : Icc lo c ⊆ Icc lo hi := Icc_subset_Icc le_rfl hc.2
      exact ODE_solution_unique_of_mem_Icc_left
        (v := fun _ x ↦ f x - μ • x) (s := fun _ ↦ K) (fun _ _ ↦ hC)
        (hGc.mono hsub)
        (fun t ht ↦ (hodeG μ hμ t (hsub (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
        (fun t ht ↦ Or.inl ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩)
        (hFc.mono hsub)
        (fun t ht ↦ (hodeF μ hμ t (hsub (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
        (fun t ht ↦ Or.inr ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩) (hinit μ hμ)
    · have hsub : Icc c hi ⊆ Icc lo hi := Icc_subset_Icc hc.1 le_rfl
      exact ODE_solution_unique_of_mem_Icc_right
        (v := fun _ x ↦ f x - μ • x) (s := fun _ ↦ K) (fun _ _ ↦ hC)
        (hGc.mono hsub)
        (fun t ht ↦ (hodeG μ hμ t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (fun t ht ↦ Or.inl ⟨t, hsub (Ico_subset_Icc_self ht), rfl⟩)
        (hFc.mono hsub)
        (fun t ht ↦ (hodeF μ hμ t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (fun t ht ↦ Or.inr ⟨t, hsub (Ico_subset_Icc_self ht), rfl⟩) (hinit μ hμ)
  refine ⟨hagree, ?_⟩
  intro t ht
  have heq : G t =ᶠ[𝓝 (0 : ℝ)] F t := by
    filter_upwards [hI] with μ hμ
    exact hagree μ hμ ht
  exact heq.deriv_eq

end PDE.Analysis.ODE

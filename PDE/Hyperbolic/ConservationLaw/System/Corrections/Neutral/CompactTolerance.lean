/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.OpenJets

/-!
# One tolerance for a compact family of neutral Hessian corrections

The cutoff takes every value between zero and one. Its leading Hessian therefore
traces a compact family of segments, not merely the original endpoint Hessians.
If the correction has zero diagonal contractions in the original eigenbasis,
every point on these segments retains genuine nonlinearity exactly.

Openness then supplies one tolerance for simultaneous Jacobian and Hessian
errors. The tolerance is chosen before the point, cutoff value, and perturbation.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology

namespace ContinuousLinearMap

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

/-- A compact continuous family of neutral Hessian segments has one positive
joint perturbation tolerance preserving an ordered genuinely nonlinear
eigenbasis. Neutrality is measured in the same basis as the original nonzero
contractions. Only pointwise bases are needed; the correction need not be small. -/
theorem exists_pos_tolerance_of_compact_neutral_family (ι : Type*) [Finite ι] [LinearOrder ι]
    {K : Set X} {A : X → E →L[ℝ] E} {H B : X → E →L[ℝ] E →L[ℝ] E} (hK : IsCompact K)
    (hA : ContinuousOn A K) (hH : ContinuousOn H K) (hB : ContinuousOn B K)
    (hfamily : ∀ t ∈ K, ∃ (b : Module.Basis ι ℝ E) (eig : ι → ℝ), StrictMono eig ∧
      (∀ i, A t (b i) = eig i • b i) ∧ ∀ i, b.repr (H t (b i) (b i)) i ≠ 0 ∧
      b.repr (B t (b i) (b i)) i = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ (a : E →L[ℝ] E) (h : E →L[ℝ] E →L[ℝ] E),
      ‖a - A t‖ < ε → ‖h - (H t + θ • B t)‖ < ε → HasOrderedGenuinelyNonlinearEigenbasis ι a h := by
  let J : X × ℝ → (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) := fun p ↦ (A p.1, H p.1 + p.2 • B p.1)
  have hJ : ContinuousOn J (K ×ˢ Icc (0 : ℝ) 1) :=
    (hA.comp continuousOn_fst (fun _ hp ↦ hp.1)).prodMk
      ((hH.comp continuousOn_fst (fun _ hp ↦ hp.1)).add
        (continuousOn_snd.smul (hB.comp continuousOn_fst (fun _ hp ↦ hp.1))))
  have hcompact : IsCompact (J '' (K ×ˢ Icc (0 : ℝ) 1)) :=
    (hK.prod isCompact_Icc).image_of_continuousOn hJ
  have hsubset : J '' (K ×ˢ Icc (0 : ℝ) 1) ⊆
      {p | HasOrderedGenuinelyNonlinearEigenbasis ι p.1 p.2} := by
    rintro _ ⟨⟨t, θ⟩, ht, rfl⟩
    obtain ⟨b, eig, horder, hdiag, hnonzero⟩ := hfamily t ht.1
    refine ⟨b, eig, horder, hdiag, fun i ↦ ?_⟩
    change b.repr ((H t + θ • B t) (b i) (b i)) i ≠ 0
    simpa only [add_apply, smul_apply, map_add, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul, (hnonzero i).2, mul_zero, add_zero] using (hnonzero i).1
  obtain ⟨ε, hε, hthickening⟩ := @IsCompact.exists_thickening_subset_open
    ((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E)) (inferInstance : PseudoMetricSpace
      ((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E))).toPseudoEMetricSpace (J '' (K ×ˢ Icc (0 : ℝ) 1))
    {p | HasOrderedGenuinelyNonlinearEigenbasis ι p.1 p.2} hcompact
    (isOpen_setOf_hasOrderedGenuinelyNonlinearEigenbasis ι) hsubset
  refine ⟨ε, hε, fun t ht θ hθ a h ha hh ↦ ?_⟩
  apply hthickening (a := (a, h))
  apply mem_thickening_iff.mpr
  refine ⟨J (t, θ), mem_image_of_mem J ⟨ht, hθ⟩, ?_⟩
  change dist (a, h) (A t, H t + θ • B t) < ε
  rw [Prod.dist_eq]
  refine max_lt (by simpa only [dist_eq_norm] using ha) ?_
  rw [@dist_eq_norm (E →L[ℝ] E →L[ℝ] E)
    (ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ) (E := E) (F := E →L[ℝ] E)) h (H t + θ • B t)]
  exact hh

end ContinuousLinearMap

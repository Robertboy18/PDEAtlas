/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Localization of constant first-order operators

Multiplication by a scalar cutoff produces a source involving its first
derivative. The source is supported where the cutoff derivative is supported,
so compact support of the cutoff suffices without a global bound on the
original function. A spatial cutoff in a time-dependent system has no time
commutator term.
-/

@[expose] public noncomputable section

open scoped Topology

namespace PDE.Analysis

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype ι]

/-- The source created by a scalar cutoff for a constant first-order operator. -/
def firstOrderCutoffSource (v : ι → E) (A : ι → F →L[ℝ] G)
    (χ : E → ℝ) (u : E → F) (x : E) : G :=
  ∑ k, fderiv ℝ χ x (v k) • A k (u x)

/-- The product rule for a constant first-order operator. -/
theorem firstOrder_apply_cutoff
    (v : ι → E) (A : ι → F →L[ℝ] G)
    {χ : E → ℝ} {u : E → F} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) :
    (∑ k, A k (fderiv ℝ (fun y ↦ χ y • u y) x (v k))) =
      χ x • (∑ k, A k (fderiv ℝ u x (v k))) +
        firstOrderCutoffSource v A χ u x := by
  simp [firstOrderCutoffSource, fderiv_fun_smul hχ hu,
    Finset.sum_add_distrib, Finset.smul_sum]

/-- The cutoff source vanishes wherever the cutoff derivative vanishes. -/
theorem support_firstOrderCutoffSource_subset
    (v : ι → E) (A : ι → F →L[ℝ] G) (χ : E → ℝ) (u : E → F) :
    Function.support (firstOrderCutoffSource v A χ u) ⊆
      Function.support (fderiv ℝ χ) := by
  intro x hx hzero
  apply hx
  simp [firstOrderCutoffSource, hzero]

/-- Localization never creates source outside the closed support of the cutoff. -/
theorem tsupport_firstOrderCutoffSource_subset
    (v : ι → E) (A : ι → F →L[ℝ] G) (χ : E → ℝ) (u : E → F) :
    tsupport (firstOrderCutoffSource v A χ u) ⊆ tsupport χ :=
  (closure_mono (support_firstOrderCutoffSource_subset v A χ u)).trans
    (tsupport_fderiv_subset ℝ)

/-- Compactness of the cutoff supplies compact support of the derived source,
with no support or growth assumption on the original function. -/
theorem hasCompactSupport_firstOrderCutoffSource
    (v : ι → E) (A : ι → F →L[ℝ] G) {χ : E → ℝ} (hχ : HasCompactSupport χ)
    (u : E → F) :
    HasCompactSupport (firstOrderCutoffSource v A χ u) :=
  hχ.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_firstOrderCutoffSource_subset v A χ u)

/-- On any region where the cutoff is locally constant, the derived source is
zero. In particular this applies on the interior region where the cutoff is one. -/
theorem firstOrderCutoffSource_eq_zero_of_eventuallyEq
    (v : ι → E) (A : ι → F →L[ℝ] G) {χ : E → ℝ} (u : E → F)
    {x : E} {c : ℝ} (hχ : χ =ᶠ[𝓝 x] fun _ ↦ c) :
    firstOrderCutoffSource v A χ u x = 0 := by
  simp [firstOrderCutoffSource, hχ.fderiv_eq]

/-- A `C¹` cutoff and a continuous original function produce a continuous source. -/
theorem continuous_firstOrderCutoffSource
    (v : ι → E) (A : ι → F →L[ℝ] G) {χ : E → ℝ} {u : E → F}
    (hχ : ContDiff ℝ 1 χ) (hu : Continuous u) :
    Continuous (firstOrderCutoffSource v A χ u) := by
  apply continuous_finsetSum
  intro k _
  exact (((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul
    ((A k).continuous.comp hu))

/-- The full first-order evolution equation after a spatial cutoff.
Its source uses only spatial derivatives of the cutoff, and retains every
constant operator with its original sign. -/
theorem firstOrder_spatialCutoff
    (v : ι → E) (A : ι → F →L[ℝ] F)
    {χ : E → ℝ} {u : ℝ × E → F} {p : ℝ × E}
    (hχ : DifferentiableAt ℝ χ p.2) (hu : DifferentiableAt ℝ u p) :
    fderiv ℝ (fun q : ℝ × E ↦ χ q.2 • u q) p (1, 0) +
        ∑ k, A k (fderiv ℝ (fun q : ℝ × E ↦ χ q.2 • u q) p (0, v k)) =
      χ p.2 • (fderiv ℝ u p (1, 0) + ∑ k, A k (fderiv ℝ u p (0, v k))) +
        firstOrderCutoffSource v A χ (fun x ↦ u (p.1, x)) p.2 := by
  have hdχ : HasFDerivAt (fun q : ℝ × E ↦ χ q.2)
      ((fderiv ℝ χ p.2).comp (ContinuousLinearMap.snd ℝ ℝ E)) p :=
    hχ.hasFDerivAt.comp p hasFDerivAt_snd
  have hd := (hdχ.smul hu.hasFDerivAt).fderiv
  change fderiv ℝ (fun q : ℝ × E ↦ χ q.2 • u q) p = _ at hd
  rw [hd]
  simp [firstOrderCutoffSource, Finset.sum_add_distrib, Finset.smul_sum, smul_add,
    add_assoc]

/-- A homogeneous classical system gives the forced equation for its cutoff;
the forcing is derived from the cutoff and the original function. -/
theorem firstOrder_spatialCutoff_of_eq_zero
    (v : ι → E) (A : ι → F →L[ℝ] F)
    {χ : E → ℝ} {u : ℝ × E → F} {p : ℝ × E}
    (hχ : DifferentiableAt ℝ χ p.2) (hu : DifferentiableAt ℝ u p)
    (heq : fderiv ℝ u p (1, 0) + ∑ k, A k (fderiv ℝ u p (0, v k)) = 0) :
    fderiv ℝ (fun q : ℝ × E ↦ χ q.2 • u q) p (1, 0) +
        ∑ k, A k (fderiv ℝ (fun q : ℝ × E ↦ χ q.2 • u q) p (0, v k)) =
      firstOrderCutoffSource v A χ (fun x ↦ u (p.1, x)) p.2 := by
  rw [firstOrder_spatialCutoff v A hχ hu, heq, smul_zero, zero_add]

/-- The spatial cutoff source is jointly continuous on every region where the
original function is continuous, including closed time slabs. -/
theorem continuousOn_firstOrderCutoffSource_spatial
    (v : ι → E) (A : ι → F →L[ℝ] G) {χ : E → ℝ} {u : ℝ × E → F}
    {s : Set (ℝ × E)} (hχ : ContDiff ℝ 1 χ) (hu : ContinuousOn u s) :
    ContinuousOn (fun p : ℝ × E ↦
      firstOrderCutoffSource v A χ (fun x ↦ u (p.1, x)) p.2) s := by
  apply continuousOn_finsetSum
  intro k _
  exact ((((hχ.continuous_fderiv one_ne_zero).comp continuous_snd).clm_apply
    continuous_const).continuousOn.smul ((A k).continuous.comp_continuousOn hu))

end PDE.Analysis

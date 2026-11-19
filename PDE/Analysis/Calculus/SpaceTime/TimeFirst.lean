/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Sections and spatial differentials with time first

For a field on `T ×ˢ Ω`, the first factor is the parameter or time variable.
Spatial sections retain the joint regularity, and their differentials lose one
order. The time set is arbitrary: uniqueness of derivatives is needed only in
the spatial factor. In particular, a closed time interval may be degenerate.

On an open spatial domain these are ordinary spatial derivatives, including at
boundary times. Time derivatives at boundary times are taken within the time
set; an ordinary time derivative is asserted only in its interior.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

variable {P X E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : Set P} {Ω : Set X} {f : P × X → E} {r k : WithTop ℕ∞}

/-- Fixing a time in the parameter set preserves spatial regularity on the
spatial domain, without any regularity assumption on the parameter set. -/
theorem ContDiffOn.contDiffOn_prodMk_right (hf : ContDiffOn ℝ r f (T ×ˢ Ω))
    {t : P} (ht : t ∈ T) : ContDiffOn ℝ r (fun x ↦ f (t, x)) Ω :=
  hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨ht, hx⟩)

/-- With unrestricted spatial domain, every spatial section is globally
regular, including sections at boundary or isolated parameter values. -/
theorem ContDiffOn.contDiff_prodMk_right
    (hf : ContDiffOn ℝ r f (T ×ˢ univ)) {t : P} (ht : t ∈ T) :
    ContDiff ℝ r (fun x ↦ f (t, x)) :=
  contDiffOn_univ.mp (hf.contDiffOn_prodMk_right ht)

/-- Fixing a spatial point preserves regularity relative to the time set. -/
theorem ContDiffOn.contDiffOn_prodMk_left (hf : ContDiffOn ℝ r f (T ×ˢ Ω))
    {x : X} (hx : x ∈ Ω) : ContDiffOn ℝ r (fun t ↦ f (t, x)) T :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht ↦ ⟨ht, hx⟩)

/-- At an interior spatial point the differential within the joint product,
restricted to spatial directions, is the differential of the section.
The time coordinate need not be an interior point. -/
theorem DifferentiableWithinAt.hasFDerivAt_prodMk_right {p : P × X}
    (hf : DifferentiableWithinAt ℝ f (T ×ˢ Ω) p) (hΩ : IsOpen Ω)
    (hp : p ∈ T ×ˢ Ω) :
    HasFDerivAt (fun x ↦ f (p.1, x))
      ((fderivWithin ℝ f (T ×ˢ Ω) p).comp (ContinuousLinearMap.inr ℝ P X)) p.2 := by
  apply hf.hasFDerivWithinAt.comp_hasFDerivAt p.2
    (_root_.hasFDerivAt_prodMk_right p.1 p.2)
  exact Filter.Eventually.mono (hΩ.mem_nhds hp.2) (fun _ hx ↦ ⟨hp.1, hx⟩)

/-- Joint regularity of the spatial differential within the spatial domain.
Only that domain needs unique differentials; the parameter set is arbitrary. -/
theorem ContDiffOn.fderivWithin_snd (hf : ContDiffOn ℝ r f (T ×ˢ Ω))
    (hΩ : UniqueDiffOn ℝ Ω) (hkr : k + 1 ≤ r) :
    ContDiffOn ℝ k (fun p : P × X ↦ fderivWithin ℝ (fun x ↦ f (p.1, x)) Ω p.2)
      (T ×ˢ Ω) := by
  intro p hp
  have hfamily : ContDiffWithinAt ℝ r
      (fun q : (P × X) × X ↦ f (q.1.1, q.2)) ((T ×ˢ Ω) ×ˢ Ω) (p, p.2) := by
    apply (hf p hp).comp (p, p.2)
      (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
    intro q hq
    exact ⟨hq.1.1, hq.2⟩
  exact hfamily.fderivWithin contDiffWithinAt_snd hΩ hkr hp (fun _ hq ↦ hq.2)

/-- On an open spatial domain, the ordinary spatial differential is jointly
regular one order below the field, even at boundary times. -/
theorem ContDiffOn.fderiv_snd (hf : ContDiffOn ℝ r f (T ×ˢ Ω))
    (hΩ : IsOpen Ω) (hkr : k + 1 ≤ r) :
    ContDiffOn ℝ k (fun p : P × X ↦ fderiv ℝ (fun x ↦ f (p.1, x)) p.2)
      (T ×ˢ Ω) := by
  apply (hf.fderivWithin_snd hΩ.uniqueDiffOn hkr).congr
  intro p hp
  exact (fderivWithin_of_isOpen hΩ hp.2).symm

/-- A C¹ field has a time derivative relative to its time set. The coefficient
uses the differential within the joint product, also at a time endpoint. -/
theorem ContDiffOn.hasDerivWithinAt_prodMk_left {T : Set ℝ} {f : ℝ × X → E}
    (hf : ContDiffOn ℝ 1 f (T ×ˢ Ω)) {t : ℝ} (ht : t ∈ T) {x : X} (hx : x ∈ Ω) :
    HasDerivWithinAt (fun s ↦ f (s, x))
      (fderivWithin ℝ f (T ×ˢ Ω) (t, x) (1, 0)) T t := by
  apply (hf.differentiableOn_one (t, x) ⟨ht, hx⟩).hasFDerivWithinAt.comp_hasDerivWithinAt t
    (((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt)
  intro s hs
  exact ⟨hs, hx⟩

/-- In the interior of the time set the relative time derivative is an
ordinary derivative. Spatial boundary points are allowed. -/
theorem ContDiffOn.hasDerivAt_prodMk_left {T : Set ℝ} {f : ℝ × X → E}
    (hf : ContDiffOn ℝ 1 f (T ×ˢ Ω)) {t : ℝ} (ht : t ∈ interior T)
    {x : X} (hx : x ∈ Ω) :
    HasDerivAt (fun s ↦ f (s, x))
      (fderivWithin ℝ f (T ×ˢ Ω) (t, x) (1, 0)) t :=
  (hf.hasDerivWithinAt_prodMk_left (interior_subset ht) hx).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)

/-- Where both factors are neighborhoods, the time derivative is given by
the ambient joint differential. For a closed slab this applies at every
interior time and interior spatial point. -/
theorem ContDiffOn.hasDerivAt_prodMk_left_of_mem_nhds {T : Set ℝ} {f : ℝ × X → E}
    (hf : ContDiffOn ℝ 1 f (T ×ˢ Ω)) {t : ℝ} (ht : T ∈ 𝓝 t)
    {x : X} (hx : Ω ∈ 𝓝 x) :
    HasDerivAt (fun s ↦ f (s, x)) (fderiv ℝ f (t, x) (1, 0)) t := by
  simpa only [fderivWithin_of_mem_nhds (prod_mem_nhds ht hx)] using
    hf.hasDerivAt_prodMk_left (mem_interior_iff_mem_nhds.mpr ht) (mem_of_mem_nhds hx)

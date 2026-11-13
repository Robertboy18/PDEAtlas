/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.Regularity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Coordinate slices and joint regularity on slabs

The derivative of `t ↦ f (x + t eᵢ)` is the ordinary coordinate partial
where the ambient map is differentiable. For families depending on an
additional normed-space parameter, joint regularity gives regularity of
the spatial coordinate derivatives.

On a closed time slab we use the joint derivative within the slab. Spatial
openness identifies its spatial directions with the derivatives of each
slice, including at the temporal endpoints. Joint C¹ regularity on the
slab therefore suffices for continuity there; no extension across those
endpoints is assumed.
-/

@[expose] public noncomputable section

open Filter Set PDE
open scoped Topology

variable {n : ℕ} {E P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace PDE

/-- A coordinate slice has derivative equal to the ambient
coordinate partial at the point on the line. -/
theorem hasDerivAt_coordinateSlice (i : Fin n) (x : ℝ^n) (t : ℝ)
    {f : ℝ^n → E}
    (hf : DifferentiableAt ℝ f (x + t • EuclideanSpace.single i (1 : ℝ))) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • EuclideanSpace.single i (1 : ℝ)))
      ((∂[i] f) (x + t • EuclideanSpace.single i (1 : ℝ))) t := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) t := by
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt t hline

/-- The same derivative statement for the coordinate-line
convention, whose parameter is the value of coordinate `i`. -/
theorem hasDerivAt_comp_coordinateLine (i : Fin n) (x : ℝ^n) (t : ℝ)
    {f : ℝ^n → E} (hf : DifferentiableAt ℝ f (coordinateLine i x t)) :
    HasDerivAt (f ∘ coordinateLine i x) ((∂[i] f) (coordinateLine i x t)) t :=
  hf.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_coordinateLine i x t)

/-- A spatial coordinate derivative is the joint derivative in the
corresponding spatial direction, for any additional normed-space parameter. -/
theorem partialDeriv_fst_eq_fderiv {f : ℝ^n × P → E} {p : ℝ^n × P}
    (hf : DifferentiableAt ℝ f p) (i : Fin n) :
    (∂[i] (fun x ↦ f (x, p.2))) p.1 =
      fderiv ℝ f p (EuclideanSpace.single i (1 : ℝ), 0) := by
  have h := hf.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  exact congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single i (1 : ℝ))) h.fderiv

/-- Spatial directions of the joint derivative within a product agree
with the ambient derivatives of its spatial slices. The parameter set
need not be open. -/
theorem partialDeriv_fst_eq_fderivWithin
    {Ω : Set (ℝ^n)} {T : Set P} {f : ℝ^n × P → E} {p : ℝ^n × P}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω ×ˢ T)
    (hf : DifferentiableWithinAt ℝ f (Ω ×ˢ T) p) (i : Fin n) :
    (∂[i] (fun x ↦ f (x, p.2))) p.1 =
      fderivWithin ℝ f (Ω ×ˢ T) p (EuclideanSpace.single i (1 : ℝ), 0) := by
  have hnear : ∀ᶠ x in 𝓝 p.1, (x, p.2) ∈ Ω ×ˢ T :=
    Filter.Eventually.mono (hΩ.mem_nhds hp.1) fun _ hx ↦ ⟨hx, hp.2⟩
  have h := hf.hasFDerivWithinAt.comp_hasFDerivAt p.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2) hnear
  exact congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single i (1 : ℝ))) h.fderiv

end PDE

variable {f : ℝ^n × P → E} {p : ℝ^n × P} {k r : WithTop ℕ∞}

/-- General-order local regularity of spatial partials of a joint family. -/
theorem ContDiffAt.partialDeriv_fst (hf : ContDiffAt ℝ r f p) (i : Fin n)
    (hkr : k + 1 ≤ r) :
    ContDiffAt ℝ k (fun q : ℝ^n × P ↦ (∂[i] (fun x ↦ f (x, q.2))) q.1) p := by
  have hr : (1 : WithTop ℕ∞) ≤ r := (le_add_self (a := 1) (b := k)).trans hkr
  have hdiff := (hf.of_le hr).eventually (by simp)
  have hfield : ContDiffAt ℝ k
      (fun q ↦ fderiv ℝ f q (EuclideanSpace.single i (1 : ℝ), 0)) p :=
    (hf.fderiv_right hkr).clm_apply contDiffAt_const
  apply ContDiffAt.congr_of_eventuallyEq hfield
  filter_upwards [hdiff] with q hq
  exact partialDeriv_fst_eq_fderiv hq.differentiableAt_one i

/-- Global joint regularity gives general-order regularity of the
spatial coordinate derivatives, with a varying parameter. -/
theorem ContDiff.partialDeriv_fst (hf : ContDiff ℝ r f) (i : Fin n)
    (hkr : k + 1 ≤ r) :
    ContDiff ℝ k (fun q : ℝ^n × P ↦ (∂[i] (fun x ↦ f (x, q.2))) q.1) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ hf.contDiffAt.partialDeriv_fst i hkr

/-- Joint regularity on a product with open spatial factor controls the
spatial partials even at parameter-boundary points. -/
theorem ContDiffOn.partialDeriv_fst {Ω : Set (ℝ^n)} {T : Set P}
    (hf : ContDiffOn ℝ r f (Ω ×ˢ T)) (i : Fin n)
    (hΩ : IsOpen Ω) (hT : UniqueDiffOn ℝ T) (hkr : k + 1 ≤ r) :
    ContDiffOn ℝ k (fun q : ℝ^n × P ↦ (∂[i] (fun x ↦ f (x, q.2))) q.1) (Ω ×ˢ T) := by
  have hr : (1 : WithTop ℕ∞) ≤ r := (le_add_self (a := 1) (b := k)).trans hkr
  have hfield : ContDiffOn ℝ k
      (fun q ↦ fderivWithin ℝ f (Ω ×ˢ T) q (EuclideanSpace.single i (1 : ℝ), 0))
      (Ω ×ˢ T) :=
    (hf.fderivWithin ((hΩ.uniqueDiffOn (𝕜 := ℝ)).prod hT) hkr).clm_apply contDiffOn_const
  apply hfield.congr
  intro q hq
  exact partialDeriv_fst_eq_fderivWithin hΩ hq ((hf.of_le hr).differentiableOn_one q hq) i

/-- C¹ regularity on a closed, nondegenerate time slab gives joint
continuity of spatial partials up to both temporal endpoints. -/
theorem ContDiffOn.continuousOn_partialDeriv_slab
    {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^n × ℝ → E}
    (hu : ContDiffOn ℝ 1 u (Ω ×ˢ Icc a b)) (i : Fin n)
    (hΩ : IsOpen Ω) (hab : a < b) :
    ContinuousOn (fun q : ℝ^n × ℝ ↦ (∂[i] (fun x ↦ u (x, q.2))) q.1)
      (Ω ×ˢ Icc a b) :=
  (hu.partialDeriv_fst i hΩ (uniqueDiffOn_Icc hab) (k := 0) (by simp)).continuousOn

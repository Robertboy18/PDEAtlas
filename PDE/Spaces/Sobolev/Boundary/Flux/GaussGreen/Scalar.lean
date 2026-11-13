/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Integral
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphCover

/-!
# Directional Gauss–Green on bounded C¹ graph domains

We prove the directional Gauss–Green formula for every C¹ function on a bounded open set with C¹
graph boundary, with no support condition on the function.

`integral_fderiv_eq_normalFlux` is formula (1) of Evans App. C.2, Theorem 1(i), in an arbitrary
direction `v` (Evans takes `v = e_i`): for `f` that is C¹ on `ℝⁿ`,
`∫_Ω ∂_v f dx = ∫_{∂Ω} f (v · ν) dS`. Evans states (1) without proof, for `u ∈ C¹(Ū)` on a bounded
open set with C¹ boundary. Our boundary need only be a C¹ graph in linear coordinates
(`HasC1GraphBoundary`), `ν` is the outward unit normal `outwardUnitNormal`, and `dS` is
`surfaceMeasure Ω`, Mathlib's `MeasureTheory.Measure.euclideanHausdorffMeasure (n - 1)` restricted
to `∂Ω`.

## How it works

We prove the formula by localization. `HasC1GraphBoundary` gives a finite cover of `closure Ω` by
graph patches and one interior set (`nonempty_c1GraphBoundaryCover`), and we split `f` as `∑ᵢ ψᵢ f`
with the smooth partition of unity `cover.smoothPartition`, which sums to one on `closure Ω`. A
piece supported in a graph patch satisfies the formula by
`Graph.integral_fderiv_eq_normalFlux_of_graph_patch`, which reduces it to an epigraph and the area
formula. For the interior piece both sides vanish
(`integral_fderiv_eq_normalFlux_of_support_subset`): its derivative integrates to zero over `ℝⁿ` and
it vanishes on `∂Ω`. Summing the finitely many identities gives the formula for `f`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 1(i), (1), p. 711.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.HalfSpace Trace.C1 Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- Directional Gauss–Green formula for a C¹ function `f` with compact support
`tsupport f ⊆ Ω`: both `∫_Ω ∂_v f dx` and the boundary integral of the flux of `f v`
vanish. -/
theorem integral_fderiv_eq_normalFlux_of_support_subset
    {f : ℝ^(m + 1) → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ Ω) (v : ℝ^(m + 1)) :
    ∫ x in Ω, fderiv ℝ f x v =
      ∫ x, normalFlux (Ω := Ω) (fun y ↦ f y • v) x ∂surfaceMeasure Ω := by
  have hvolume : ∫ x in Ω, fderiv ℝ f x v = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact PDE.integral_fderiv_eq_zero_of_hasCompactSupport hf hcompact v
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hsupport h))]
      rfl
  have hflux : normalFlux (Ω := Ω) (fun y ↦ f y • v) = fun _ ↦ 0 := by
    funext x
    by_cases hx : x ∈ frontier Ω
    · have hfx : f x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ.isOpen))
          hx (hsupport h)
      simp [normalFlux, hx, hfx]
    · simp [normalFlux, hx]
  rw [hvolume, hflux, integral_zero]

/-- Directional Gauss–Green formula (Evans App. C.2, Theorem 1(i)): if `Ω` carries a
`C1ExtensionAtlas` (so is bounded and open) and has C¹ graph boundary and `f : ℝⁿ → ℝ` is C¹, then
`∫_Ω ∂_v f dx = ∫_{∂Ω} f (v · ν) dS` for every `v ∈ ℝⁿ`, with `ν` the intrinsic outward unit normal
and `dS` the Hausdorff surface measure `surfaceMeasure Ω`. -/
theorem integral_fderiv_eq_normalFlux
    (hgraph : HasC1GraphBoundary Ω) {f : ℝ^(m + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) (v : ℝ^(m + 1)) :
    ∫ x in Ω, fderiv ℝ f x v =
      ∫ x, normalFlux (Ω := Ω) (fun y ↦ f y • v) x ∂surfaceMeasure Ω := by
  classical
  let graphs := Classical.choice
    (hgraph.nonempty_c1GraphBoundaryCover hΩ.isOpen hΩ.bounded)
  let cover := graphs.toFiniteBoundaryCover
  let F : Fin (cover.N + 1) → ℝ^(m + 1) → ℝ :=
    fun i x ↦ cover.smoothPartition i x * f x
  have hF (i : Fin (cover.N + 1)) : ContDiff ℝ 1 (F i) :=
    ((cover.smoothPartition_contDiff i).of_le (by simp)).mul hf
  have hFc (i : Fin (cover.N + 1)) : HasCompactSupport (F i) :=
    (cover.smoothPartition_hasCompactSupport i).mul_right
  have hsum {x : ℝ^(m + 1)} (hx : x ∈ closure Ω) : ∑ i, F i x = f x := by
    have h := cover.smoothPartition.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at h
    simp only [F, ← Finset.sum_mul, h, one_mul]
  have hd {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
      fderiv ℝ f x v = ∑ i, fderiv ℝ (F i) x v := by
    have hderiv := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ ((hF i).differentiable one_ne_zero x).hasFDerivAt)
    have heq : (fun y ↦ ∑ i, F i y) =ᶠ[nhds x] f := by
      filter_upwards [hΩ.isOpen.mem_nhds hx] with y hy
      exact hsum (subset_closure hy)
    rw [(hderiv.congr_of_eventuallyEq heq.symm).fderiv]
    simp
  have hlocal (i : Fin (cover.N + 1)) :
      ∫ x in Ω, fderiv ℝ (F i) x v =
        ∫ x, normalFlux (Ω := Ω) (fun y ↦ F i y • v) x ∂surfaceMeasure Ω := by
    induction i using Fin.lastCases with
    | last =>
      apply integral_fderiv_eq_normalFlux_of_support_subset (hF _) (hFc _)
      exact tsupport_mul_subset_left.trans cover.interiorCutoff_support
    | cast i =>
      let A := (graphs.coordinates i).trans tangentialNormalContinuousLinearEquiv.symm
      apply Graph.integral_fderiv_eq_normalFlux_of_graph_patch
        (cover.boundaryPatch_open i) A (graphs.height_contDiff i) ?_ (hF _) (hFc _)
      · exact tsupport_mul_subset_left.trans (cover.boundaryCutoff_support i)
      · intro x hx
        simpa [Graph.linearEpigraph, A] using graphs.mem_iff_epigraph i x hx
  have hvolume (i : Fin (cover.N + 1)) :
      IntegrableOn (fun x ↦ fderiv ℝ (F i) x v) Ω := by
    have hc := ((hF i).continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
    exact (hc.integrable_of_hasCompactSupport ((hFc i).fderiv_apply ℝ v)).integrableOn
  have hsurface (i : Fin (cover.N + 1)) :
      Integrable (normalFlux (Ω := Ω) (fun y ↦ F i y • v)) (surfaceMeasure Ω) :=
    integrable_normalFlux ((hF i).continuous.smul continuous_const).continuousOn
  calc
    ∫ x in Ω, fderiv ℝ f x v = ∫ x in Ω, ∑ i, fderiv ℝ (F i) x v :=
      setIntegral_congr_fun hΩ.isOpen.measurableSet (fun x hx ↦ hd hx)
    _ = ∑ i, ∫ x in Ω, fderiv ℝ (F i) x v :=
      integral_finsetSum _ (fun i _ ↦ hvolume i)
    _ = ∑ i, ∫ x, normalFlux (Ω := Ω) (fun y ↦ F i y • v) x ∂surfaceMeasure Ω := by
      simp only [hlocal]
    _ = ∫ x, ∑ i, normalFlux (Ω := Ω) (fun y ↦ F i y • v) x ∂surfaceMeasure Ω :=
      (integral_finsetSum _ (fun i _ ↦ hsurface i)).symm
    _ = ∫ x, normalFlux (Ω := Ω) (fun y ↦ f y • v) x ∂surfaceMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      simp only [normalFlux_eq_inner _ hx, inner_smul_left, starRingEnd_apply, star_trivial,
        ← Finset.sum_mul, hsum (frontier_subset_closure hx)]

end SobolevSpace.Boundary.Flux

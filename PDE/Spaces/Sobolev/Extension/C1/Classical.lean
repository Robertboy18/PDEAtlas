/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
import Mathlib.Analysis.Calculus.FDeriv.Extend
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalJets

/-!
# Classical extension from ambient jet fields

Value and derivative fields that are `C^k` and form a classical first jet in a bounded
`C^{k+1}` domain admit an ambient `C^{k+1}` extension. Each boundary cutoff is flattened,
extended by weighted reflection, and composed with its chart. The partition of
unity then patches these extensions with the interior term.

Uniform continuity of the interior first derivatives supplies the continuous jet fields.
Thus classical regularity up to a raw graph boundary suffices; an ambient differentiable
extension is a conclusion, not an input.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Extension.C1

open Filter Set
open scoped Topology
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open GraphSpace.HigherOrderReflection

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

private theorem exists_contDiff_succ_eqOn_boundarySupport (k : ℕ)
    (hchart : ∀ i, ContDiff ℝ (k + 1) (hΩ.chart i))
    (hinv : ∀ i, ContDiff ℝ (k + 1) (hΩ.chart i).symm)
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)}
    (hf : ContDiff ℝ k f) (hf' : ContDiff ℝ k f')
    (hderiv : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) (i : Fin hΩ.N) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ (k + 1) g ∧
      EqOn g f (Ω ∩ tsupport (hΩ.boundaryCutoff i).toFun) := by
  let e := hΩ.chart i
  let η := targetSupportCutoff (n := n) (Ω := Ω) i
  let q : ℝ^n → ℝ := fun y ↦ η y * f (e.symm y)
  let q' : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun y ↦
    η y • ((f' (e.symm y)).comp (fderiv ℝ e.symm y)) +
      f (e.symm y) • fderiv ℝ η y
  have he : ContDiff ℝ (k + 1) e := hchart i
  have he' : ContDiff ℝ (k + 1) e.symm := hinv i
  have hη : ContDiff ℝ (k + 1) η := η.contDiff.of_le (by simp)
  have hηk : ContDiff ℝ k η := hη.of_le (by exact_mod_cast Nat.le_succ k)
  have he'k : ContDiff ℝ k e.symm := he'.of_le (by exact_mod_cast Nat.le_succ k)
  have hq : Continuous q := hη.continuous.mul (hf.continuous.comp he'.continuous)
  have hq' : ContDiff ℝ k q' := by
    exact (hηk.smul
      ((hf'.comp he'k).clm_comp (he'.fderiv_right (by simp)))).add
      ((hf.comp he'k).smul (hη.fderiv_right (by simp)))
  have hqd (y : ℝ^n) (hy : y ∈ HalfSpace.upper n) :
      HasFDerivAt q (q' y) y := by
    by_cases hs : y ∈ tsupport η.toFun
    · have ht : y ∈ e.target := tsupport_targetSupportCutoff_subset_target i hs
      have hyΩ : e.symm y ∈ Ω := by
        apply (hΩ.chart_mem_iff_upper i _ (e.map_target ht)).mpr
        change e (e.symm y) ∈ HalfSpace.upper n
        simpa only [e.right_inv ht] using hy
      exact (hη.differentiable (by simp) y).hasFDerivAt.mul
        ((hderiv _ hyΩ).comp y (he'.differentiable (by simp) y).hasFDerivAt)
    · have hzero : (η : ℝ^n → ℝ) =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [(isClosed_tsupport η.toFun).isOpen_compl.mem_nhds hs] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      have hη0 : η y = 0 := hzero.eq_of_nhds
      have hηd : fderiv ℝ η y = 0 := by
        rw [hzero.fderiv_eq]
        exact fderiv_const_apply (0 : ℝ)
      have hq0 : q =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [hzero] with z hz
        simp only [q, hz, zero_mul]
      have hq'd : q' y = 0 := by simp only [q', hη0, hηd, zero_smul, smul_zero, add_zero]
      rw [hq'd]
      exact (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hq0
  have hclosed : {y : ℝ^n | 0 ≤ y (PDE.Common.lastIndex (n := n))} =
      closure (HalfSpace.upper n) := by
    rw [closure_eq_self_union_frontier, HalfSpace.frontier_upper]
    ext y
    change (0 ≤ y (PDE.Common.lastIndex (n := n))) ↔
      (0 < y (PDE.Common.lastIndex (n := n)) ∨ y (PDE.Common.lastIndex (n := n)) = 0)
    exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
  have hqc (y : ℝ^n) : HasFDerivWithinAt q (q' y)
      {z | 0 ≤ z (PDE.Common.lastIndex (n := n))} y := by
    rw [hclosed]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun z hz ↦ (hqd z hz).differentiableAt.differentiableWithinAt)
      (HalfSpace.convex_upper n) (HalfSpace.isOpen_upper n)
      (fun _ _ ↦ hq.continuousWithinAt)
    apply Tendsto.congr' ?_ (hq'.continuous.continuousAt.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hqd z hz).fderiv.symm
  let r := weightedReflectionFun (PDE.Common.lastIndex (n := n)) (k + 1) q
  have hr : ContDiff ℝ (k + 1) r :=
    contDiff_succ_weightedReflectionFun _ k hq' (fun y _ ↦ hqc y)
  refine ⟨r ∘ e, hr.comp he, ?_⟩
  intro x hx
  have hxs : x ∈ e.source := hΩ.boundaryCutoff_support i hx.2
  have hu : e x ∈ HalfSpace.upper n := (hΩ.chart_mem_iff_upper i x hxs).mp hx.1
  have hη1 : η (e x) = 1 :=
    targetSupportCutoff_eq_one_on_boundarySupportInTarget i _ ⟨x, hx.2, rfl⟩
  change weightedReflectionFun (PDE.Common.lastIndex (n := n)) (k + 1) q (e x) = f x
  rw [weightedReflectionFun_eq_of_nonneg _ (k + 1) q _ (le_of_lt hu)]
  simp only [q, hη1, e.left_inv hxs, one_mul]

/-- Ambient `C^k` value and derivative fields that form a first jet inside the domain
give a compactly supported `C^{k+1}` extension through a `C^{k+1}` atlas. -/
theorem exists_contDiff_succ_extension_of_jet (k : ℕ)
    (hchart : ∀ i, ContDiff ℝ (k + 1) (hΩ.chart i))
    (hinv : ∀ i, ContDiff ℝ (k + 1) (hΩ.chart i).symm)
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)}
    (hf : ContDiff ℝ k f) (hf' : ContDiff ℝ k f')
    (hderiv : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ (k + 1) g ∧ HasCompactSupport g ∧ EqOn g f Ω := by
  classical
  choose g hg hgf using
    exists_contDiff_succ_eqOn_boundarySupport k hchart hinv hf hf' hderiv
  let v : ℝ^n → ℝ := fun x ↦ hΩ.interiorCutoff.toFun x * f x
  have hv : ContDiff ℝ (k + 1) v := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport hΩ.interiorCutoff.toFun
    · have hxΩ : x ∈ Ω := hΩ.interiorCutoff_support hx
      have hc : ContDiffAt ℝ (k + 1) f x := contDiffAt_succ_iff_hasFDerivAt.mpr
        ⟨f', ⟨Ω, hΩ.isOpen.mem_nhds hxΩ, hderiv⟩, hf'.contDiffAt⟩
      exact (hΩ.interiorCutoff.contDiff.of_le (by simp)).contDiffAt.mul hc
    · have hz : v =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [(isClosed_tsupport hΩ.interiorCutoff.toFun).isOpen_compl.mem_nhds hx]
          with y hy
        simp only [v, image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  let G : ℝ^n → ℝ := fun x ↦ v x + ∑ i, (hΩ.boundaryCutoff i).toFun x * g i x
  refine ⟨G, hv.add (ContDiff.sum fun i _ ↦
    ((hΩ.boundaryCutoff i).contDiff.of_le (by simp)).mul (hg i)), ?_, ?_⟩
  · have hsum : HasCompactSupport (fun x ↦ ∑ i, (hΩ.boundaryCutoff i).toFun x * g i x) := by
      have heq : (fun x ↦ ∑ i, (hΩ.boundaryCutoff i).toFun x * g i x) =
          ∑ i, (fun x ↦ (hΩ.boundaryCutoff i).toFun x * g i x) := by
        funext x
        simp only [Finset.sum_apply]
      rw [heq]
      exact HasCompactSupport.finset_sum
        (fun i _ ↦ (hΩ.boundaryCutoff i).hasCompactSupport.mul_right)
    exact hΩ.interiorCutoff.hasCompactSupport.mul_right.add hsum
  · intro x hx
    have hterm (i : Fin hΩ.N) :
        (hΩ.boundaryCutoff i).toFun x * g i x = (hΩ.boundaryCutoff i).toFun x * f x := by
      by_cases hi : (hΩ.boundaryCutoff i).toFun x = 0
      · simp only [hi, zero_mul]
      · rw [hgf i ⟨hx, subset_tsupport _ (Function.mem_support.mpr hi)⟩]
    simp only [G, v, hterm, ← Finset.sum_mul, ← add_mul, hΩ.cutoff_sum_eq_one x hx, one_mul]

/-- Continuous first-jet data on a bounded `C¹` domain have a compactly supported ambient
`C¹` extension. Differentiability is assumed only at interior points. -/
theorem exists_contDiff_one_extension_of_continuous_jet
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)}
    (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ EqOn g f Ω :=
  exists_contDiff_succ_extension_of_jet 0 hΩ.chart_contDiff hΩ.chart_symm_contDiff
    (contDiff_zero.mpr hf) (contDiff_zero.mpr hf') hderiv

end SobolevSpace.Extension.C1

namespace SobolevSpace.ContDiffUpToBoundary

open Set

/-- Raw classical `C¹` data up to a bounded open graph boundary admit a compactly supported
ambient `C¹` representative. The atlas, derivative fields, and extension are all constructed. -/
theorem exists_contDiff_one_extension {n : ℕ} [Fact (0 < n)]
    {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} (hf : ContDiffUpToBoundary 1 f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ EqOn g f Ω := by
  obtain ⟨atlas, _, _⟩ :=
    (Boundary.hasContDiffGraphBoundary_one_iff.mpr hgraph).exists_c1ExtensionAtlas
      le_rfl hopen hbounded
  let := atlas
  obtain ⟨F, F', hF, hF', hFf, hderiv⟩ := hf.exists_continuous_firstJet hopen
  obtain ⟨g, hg, hcompact, hgF⟩ :=
    Extension.C1.exists_contDiff_one_extension_of_continuous_jet hF hF' hderiv
  exact ⟨g, hg, hcompact, hgF.trans hFf⟩

end SobolevSpace.ContDiffUpToBoundary

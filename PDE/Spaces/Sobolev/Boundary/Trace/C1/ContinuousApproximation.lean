/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Global.Translated
public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.ContinuousLimit
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator

/-!
# Smooth approximation of continuous Sobolev representatives

Inward translated mollifications, multiplied by a finite smooth partition, converge
both in `W^{1,p}` and pointwise on the closure to any continuous representative.
The first-order extension is used only for Sobolev convergence. Each convolution
at a boundary point samples the original domain, so continuity of the extension
across the boundary is not needed.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Metric
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.Trace.C1

open Approximation Approximation.UpToBoundary GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (0 < n)]
  {Ω : Set (ℝ^n)} [H : Boundary.C1ExtensionAtlas n Ω]

/-- Smooth compactly supported ambient functions approximate a continuous Sobolev
representative in the graph norm and pointwise everywhere on the closure. -/
theorem continuous_approximation (P : InwardPartition Ω) (hp : p ≠ ∞)
    (U : W^{1,p}(Ω)) {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω))
    (hUf : baseRepresentative U =ᵐ[domainMeasure n Ω] f) :
    ∃ g : ℕ → ℝ^n → ℝ, ∃ hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j),
      ∃ hc : ∀ j, HasCompactSupport (g j),
        Tendsto (fun j ↦ mkWkpSpaceOnOfContDiff (g j) (hg j) (hc j))
            atTop (𝓝 U) ∧
          ∀ x ∈ closure Ω, Tendsto (fun j ↦ g j x) atTop (𝓝 (f x)) := by
  classical
  let E := Extension.C1.extensionCLM U
  have hEU : baseRepresentative E =ᵐ[domainMeasure n Ω] baseRepresentative U :=
    Extension.C1.extensionCLM_agree_ae U
  let μ := standardMollifier n
  obtain ⟨R₀, hR₀⟩ := μ.compactSupport.isBounded.subset_closedBall (0 : ℝ^n)
  let R := max R₀ 1
  have hRpos : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hR : tsupport μ.ρ ⊆ closedBall (0 : ℝ^n) R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  let t (i : Fin P.N) (j : ℕ) := P.radius i / ((j : ℝ) + 2)
  have htpos (i : Fin P.N) (j : ℕ) : 0 < t i j := div_pos (P.radius_pos i) (by positivity)
  have htδ (i : Fin P.N) (j : ℕ) : t i j < P.radius i :=
    div_lt_self (P.radius_pos i) (lt_add_of_nonneg_of_lt (Nat.cast_nonneg j) one_lt_two)
  have ht0 (i : Fin P.N) : Tendsto (t i) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop).const_div_atTop (P.radius i)
  let ε (i : Fin P.N) (j : ℕ) := t i j / (2 * R)
  have hεpos (i : Fin P.N) (j : ℕ) : 0 < ε i j := div_pos (htpos i j) (by positivity)
  have hε0 (i : Fin P.N) : Tendsto (ε i) atTop (𝓝 0) := by
    simpa only [zero_div] using (ht0 i).div_const (2 * R)
  have htv (i : Fin P.N) : Tendsto (fun j ↦ t i j • P.direction i) atTop (𝓝 0) := by
    simpa only [zero_smul] using (ht0 i).smul_const (P.direction i)
  let F (i : Fin P.N) (j : ℕ) (x : ℝ^n) :=
    mollify μ (ε i j) (baseRepresentative E) (x + t i j • P.direction i)
  have hlocal (i : Fin P.N) := translated_mollification_approximation μ hp E
    (ε i) (hεpos i) (hε0 i) (fun j ↦ t i j • P.direction i) (htv i)
  choose hF A hAbase hA using hlocal
  let S := restrictCLM (k := 1) (p := p) H.isOpen.measurableSet (subset_univ Ω)
  let M (i : Fin P.N) := cutoffCLM (p := p) (Ω := Ω) (P.cutoff i)
  let B (j : ℕ) := ∑ i, M i (S (A i j))
  let g (j : ℕ) (x : ℝ^n) := ∑ i, (P.cutoff i).toFun x * F i j x
  have hg (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g j) :=
    ContDiff.sum fun i _ ↦ (P.cutoff i).contDiff.mul (hF i j)
  have hc (j : ℕ) : HasCompactSupport (g j) := by
    convert HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ ↦ ((P.cutoff i).hasCompactSupport.mul_right :
        HasCompactSupport ((P.cutoff i).toFun * F i j))) using 1
    ext x
    simp only [g, Finset.sum_apply, Pi.mul_apply]
    rfl
  have hMbase (i : Fin P.N) (W : W^{1,p}(ℝ^n)) :
      baseRepresentative (M i (S W)) =ᵐ[domainMeasure n Ω]
        fun x ↦ (P.cutoff i).toFun x * baseRepresentative W x := by
    filter_upwards [cutoffCLM_base_apply_ae (P.cutoff i) (S W),
      restrictCLM_apply_ae H.isOpen.measurableSet (subset_univ Ω) W (baseIndex n 1)]
      with x hx hs
    exact hx.trans (congrArg ((P.cutoff i).toFun x * ·) hs)
  have hBbase (j : ℕ) : baseRepresentative (B j) =ᵐ[domainMeasure n Ω] g j := by
    have hi (i : Fin P.N) : baseRepresentative (M i (S (A i j)))
        =ᵐ[domainMeasure n Ω] fun x ↦ (P.cutoff i).toFun x * F i j x := by
      filter_upwards [hMbase i (A i j), ae_restrict_of_ae (hAbase i j)] with x hx ha
      exact hx.trans (congrArg ((P.cutoff i).toFun x * ·) ha)
    filter_upwards [baseRepresentative_sum_ae (fun i ↦ M i (S (A i j))),
      ae_all_iff.mpr hi] with x hx hxi
    exact hx.trans (Finset.sum_congr rfl fun i _ ↦ hxi i)
  have hsum : ∑ i, M i (S E) = U := by
    apply WkpSpaceOn.ext_of_base_ae H.isOpen
    filter_upwards [baseRepresentative_sum_ae (fun i ↦ M i (S E)),
      ae_all_iff.mpr (fun i ↦ hMbase i E), hEU,
      ae_restrict_mem H.isOpen.measurableSet] with x hx hxi hu hxΩ
    refine (hx.trans (Finset.sum_congr rfl fun i _ ↦ hxi i)).trans ?_
    rw [← Finset.sum_mul, P.sum_eq_one x (subset_closure hxΩ), one_mul, hu]
    rfl
  have hB : Tendsto B atTop (𝓝 U) := by
    rw [← hsum]
    exact tendsto_finsetSum _ fun i _ ↦
      ((M i).continuous.continuousAt.tendsto.comp
        (S.continuous.continuousAt.tendsto.comp (hA i)))
  have heq (j : ℕ) : mkWkpSpaceOnOfContDiff (g j) (hg j) (hc j) = B j := by
    apply WkpSpaceOn.ext_of_base_ae H.isOpen
    have hctor : baseRepresentative
        (mkWkpSpaceOnOfContDiff (k := 1) (p := p) (Ω := Ω) (g j) (hg j) (hc j))
        =ᵐ[domainMeasure n Ω] g j := by
      simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
        mkWkpSpaceOnOfContDiff_apply_ae (p := p) (Ω := Ω)
          (g j) (hg j) (hc j) (baseIndex n 1)
    exact hctor.trans (hBbase j).symm
  refine ⟨g, hg, hc, ?_, ?_⟩
  · simpa only [heq] using hB
  · intro x hx
    have hi (i : Fin P.N) :
        Tendsto (fun j ↦ (P.cutoff i).toFun x * F i j x)
          atTop (𝓝 ((P.cutoff i).toFun x * f x)) := by
      by_cases hi : (P.cutoff i).toFun x = 0
      · simpa only [hi, zero_mul] using tendsto_const_nhds
      · have hxV : x ∈ P.patch i := P.cutoff_support i (subset_tsupport _ hi)
        exact (mollify_inward_tendsto μ hRpos hR H.isOpen (P.patch_open i) hf
          (hEU.trans hUf) (P.direction i) (t i) (htpos i) (ht0 i)
          (fun j ↦ P.interior_ball i (t i j) ⟨htpos i j, htδ i j⟩) ⟨hxV, hx⟩).const_mul _
    simpa only [← Finset.sum_mul, P.sum_eq_one x hx, one_mul] using
      tendsto_finsetSum Finset.univ (fun i _ ↦ hi i)

end SobolevSpace.Trace.C1

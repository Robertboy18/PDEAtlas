/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.Composition.Truncation
import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Compact support implies zero trace

We prove the density step used in Evans, §§5.3.1 and 6.3.1, in the interior regularity argument: a
global `H¹(ℝ^n)` function whose support has a positive collar inside an open set `Ω` restricts to an
element of `H¹₀(Ω)`. The proof uses support-controlled mollification and no trace or extension
theorem.

A continuous compactly supported representative that vanishes outside `Ω` also
has zero trace. Removing the clamp on a shrinking interval about zero places
each approximant strictly inside `Ω`; strong Sobolev convergence then gives
the result on any open set, including domains with corners.

In particular, a compactly supported Lipschitz function vanishing outside `Ω` gives an element
of `H¹₀(Ω)` whose value and coordinate derivatives are, almost everywhere, the function and its
classical partial derivatives (`exists_H10_of_lipschitzWith_zero_outside`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.1, Theorem 1, pp. 264-265, for local approximation by
  mollification, and §6.3.1, Theorem 1 and its proof, pp. 327-331, the interior regularity argument,
  whose test functions are compactly supported in `U`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions NNReal Sobolev

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set Function ENNReal
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}


/-- A compactly supported global `H¹` field restricts to `H¹₀(Ω)` whenever a
vanishing sequence of mollifier scales remains inside a fixed support collar. -/
theorem restrict_mem_H10_of_mollifier_scales
    (hΩopen : IsOpen Ω) (μ : Approximation.Mollifier n)
    (U : H¹(ℝ^n))
    (f : ℝ^n → ℝ)
    (hUbase :
      ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f)
    (hUcs : HasCompactSupport f)
    {R δ : ℝ}
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (hcollar : Metric.cthickening δ (tsupport f) ⊆ Ω)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hεR : ∀ m, ε m * R < δ) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω) U ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  obtain ⟨f_m, hf_smooth, hf_cs, hf_eq, hf_tendsto⟩ :=
    mollify_tendsto_globalH1Space_of_base_ae μ U f
      hUbase hUcs ε hεpos hε0
  have hf_support (m : ℕ) : tsupport (f_m m) ⊆ Ω := by
    apply closure_minimal _ Metric.isClosed_cthickening |>.trans hcollar
    rw [hf_eq m]
    exact Approximation.support_mollify_subset_cthickening
      μ (hεpos m) hR (hεR m) f
  let ψ : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ) := fun m ↦
    ⟨f_m m, hf_smooth m, hf_cs m, subset_univ _⟩
  let ψΩ : ℕ → TestFunctionOn n Ω := fun m ↦ ⟨ψ m, hf_support m⟩
  have hrestrict (m : ℕ) :
      testFunctionToH1 (n := n) (Ω := Ω) (ψΩ m) =
        restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
          (subset_univ Ω)
          (mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2)
            (Ω := (Set.univ : Set (ℝ^n)))
            (f := f_m m) (hf_smooth m) (hf_cs m)) := by
    apply WkpSpaceOn.ext_of_base_ae hΩopen
    have hlocal := mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := 2) (Ω := Ω)
      (f := f_m m) (hf_smooth m) (hf_cs m)
      (baseIndex n 1)
    have hglobal := mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := 2) (Ω := (Set.univ : Set (ℝ^n)))
      (f := f_m m) (hf_smooth m) (hf_cs m)
      (baseIndex n 1)
    have hres := restrictCLM_apply_ae
      (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω)
      (mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2)
        (Ω := (Set.univ : Set (ℝ^n)))
        (f := f_m m) (hf_smooth m) (hf_cs m)) (baseIndex n 1)
    have hmeasure : domainMeasure n Ω ≤ domainMeasure n (Set.univ : Set (ℝ^n)) := by
      exact MeasureTheory.Measure.restrict_mono (subset_univ Ω) (le_refl _)
    have hglobalΩ := hglobal.filter_mono (MeasureTheory.ae_mono hmeasure)
    exact hlocal.trans (hres.trans hglobalΩ).symm
  apply mem_H10_of_tendsto_testFunctionToH1
    (restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω) U) ψΩ
  rw [show (fun m ↦ testFunctionToH1 (n := n) (Ω := Ω) (ψΩ m)) =
      fun m ↦ restrictCLM (n := n) (k := 1) (p := 2)
        hΩopen.measurableSet (subset_univ Ω)
        (mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2)
          (Ω := (Set.univ : Set (ℝ^n)))
          (f := f_m m) (hf_smooth m) (hf_cs m)) by
    funext m
    exact hrestrict m]
  exact (restrictCLM (n := n) (k := 1) (p := 2)
    hΩopen.measurableSet (subset_univ Ω)).continuous.continuousAt.tendsto.comp hf_tendsto

/-- Compact-support criterion. A positive collar around the support supplies a
vanishing mollifier scale sequence, so no approximation schedule appears in the
statement. -/
theorem restrict_mem_H10_of_compactSupport_collar
    (hΩopen : IsOpen Ω) (μ : Approximation.Mollifier n)
    (U : H¹(ℝ^n))
    (f : ℝ^n → ℝ)
    (hUbase :
      ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f)
    (hUcs : HasCompactSupport f)
    {R δ : ℝ} (hRnonneg : 0 ≤ R) (hδ : 0 < δ)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (hcollar : Metric.cthickening δ (tsupport f) ⊆ Ω) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω) U ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  let c : ℝ := δ / (2 * (R + 1))
  let ε : ℕ → ℝ := fun m ↦ c / ((m : ℝ) + 1)
  have hden : 0 < 2 * (R + 1) := by positivity
  have hcpos : 0 < c := div_pos hδ hden
  have hεpos : ∀ m, 0 < ε m := by
    intro m
    exact div_pos hcpos (by positivity)
  have hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    have hbase : Filter.Tendsto
        (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hbase.const_mul c
    simpa [ε, div_eq_mul_inv] using hmul
  have hcRlt : c * R < δ := by
    rw [show c * R = (δ * R) / (2 * (R + 1)) by
      dsimp [c]
      ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hεR : ∀ m, ε m * R < δ := by
    intro m
    have hmone : (1 : ℝ) ≤ (m : ℝ) + 1 := by norm_num
    have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 := by
      exact (div_le_one (by positivity)).2 hmone
    have hεle : ε m ≤ c := by
      rw [show ε m = c * (1 / ((m : ℝ) + 1)) by
        simp [ε, div_eq_mul_inv]]
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεle hRnonneg) hcRlt
  exact restrict_mem_H10_of_mollifier_scales hΩopen μ U f hUbase hUcs hR hcollar
    ε hεpos hε0 hεR

/-- A compactly supported global `H¹` field whose topological support is contained in an open
set restricts to `H¹₀` on that set.

This is the standard user-facing form of compact-support zero trace.  The positive support collar
and a containing ball for the standard mollifier are consequences of compactness and are chosen
inside the proof. -/
theorem restrict_mem_H10_of_tsupport_subset
    (hΩopen : IsOpen Ω)
    (U : H¹(ℝ^n))
    (f : ℝ^n → ℝ)
    (hUbase :
      ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f)
    (hUcs : HasCompactSupport f)
    (hsupport : tsupport f ⊆ Ω) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω) U ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  have hK : IsCompact (tsupport f) := by
    simpa [HasCompactSupport] using hUcs
  obtain ⟨δ, hδ, hδΩ⟩ :=
    hK.exists_cthickening_subset_open hΩopen hsupport
  have hμcompact :
      IsCompact (tsupport (Approximation.standardMollifier n).ρ) := by
    simpa [HasCompactSupport] using
      (Approximation.standardMollifier n).compactSupport
  obtain ⟨R₀, hR₀⟩ :=
    hμcompact.isBounded.subset_closedBall (0 : ℝ^n)
  let R : ℝ := max R₀ 0
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have hμR : tsupport (Approximation.standardMollifier n).ρ ⊆
      Metric.closedBall (0 : ℝ^n) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  exact restrict_mem_H10_of_compactSupport_collar hΩopen
    (Approximation.standardMollifier n) U f hUbase hUcs
    hRnonneg hδ hμR hδΩ

/-- A global `H¹` field with a continuous compactly supported representative
vanishing outside an open set restricts to `H¹₀` on that set. Corners and other
boundary irregularities require no separate trace theorem. -/
theorem restrict_mem_H10_of_continuous_zero_outside
    {n : ℕ} {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω)
    (U : H¹(ℝ^n)) (f : ℝ^n → ℝ)
    (hUbase : (wkpCoordinateCLM (baseIndex n 1) U : ℝ^n → ℝ) =ᵐ[volume] f)
    (hf : Continuous f) (hcompact : HasCompactSupport f)
    (hzero : ∀ x ∉ Ω, f x = 0) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet (subset_univ Ω) U ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεzero : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let B (j : ℕ) : H¹(ℝ^n) :=
    intervalTruncation (by norm_num) (neg_nonpos.mpr (hεpos j).le) (hεpos j).le U
  let g (j : ℕ) (x : ℝ^n) :=
    f x - PDE.Analysis.Calculus.intervalTruncation (-ε j) (ε j) (f x)
  have hgcompact (j : ℕ) : HasCompactSupport (g j) := by
    apply hcompact.mono
    intro x hx
    by_contra h
    have hfx : f x = 0 := not_not.mp h
    apply hx
    simp only [g, hfx]
    rw [PDE.Analysis.Calculus.intervalTruncation_eq_min_max (by linarith [hεpos j])]
    simp [(hεpos j).le]
  -- Removing small values leaves a closed superlevel set inside the open domain.
  have hgsupport (j : ℕ) : tsupport (g j) ⊆ Ω := by
    have hclosed : IsClosed {x : ℝ^n | ε j ≤ |f x|} :=
      isClosed_le continuous_const hf.abs
    have hsubset : tsupport (g j) ⊆ {x : ℝ^n | ε j ≤ |f x|} := by
      apply closure_minimal _ hclosed
      intro x hx
      by_contra h
      have hsmall : |f x| < ε j := lt_of_not_ge h
      have hbounds := abs_lt.mp hsmall
      apply hx
      change f x - PDE.Analysis.Calculus.intervalTruncation (-ε j) (ε j) (f x) = 0
      rw [PDE.Analysis.Calculus.intervalTruncation_eq_min_max (by linarith [hεpos j]),
        max_eq_right hbounds.1.le, min_eq_right hbounds.2.le, sub_self]
    intro x hx
    by_contra hout
    have hle := hsubset hx
    simp only [mem_ofPred_eq, hzero x hout, abs_zero] at hle
    exact (not_le_of_gt (hεpos j)) hle
  have hbase (j : ℕ) :
      (wkpCoordinateCLM (baseIndex n 1) (U - B j) : ℝ^n → ℝ) =ᵐ[volume] g j := by
    have hB := intervalTruncation_base_ae (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (neg_nonpos.mpr (hεpos j).le) (hεpos j).le U
    have hmeasure : volume ≤ domainMeasure n univ := by simp [domainMeasure]
    have hBvolume := hB.filter_mono (ae_mono hmeasure)
    have hsubvolume :=
      (Lp.coeFn_sub (wkpCoordinateCLM (baseIndex n 1) U)
        (wkpCoordinateCLM (baseIndex n 1) (B j))).filter_mono (ae_mono hmeasure)
    filter_upwards [hUbase, hBvolume, hsubvolume] with x hx hbx hsub
    simp only [map_sub]
    rw [hsub]
    simp only [Pi.sub_apply]
    change (wkpCoordinateCLM (baseIndex n 1) (B j) : ℝ^n → ℝ) x =
      PDE.Analysis.Calculus.intervalTruncation (-ε j) (ε j)
        ((wkpCoordinateCLM (baseIndex n 1) U : ℝ^n → ℝ) x) at hbx
    rw [hbx, hx]
  have hmem (j : ℕ) :
      restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω) (U - B j) ∈
          (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule :=
    restrict_mem_H10_of_tsupport_subset hΩopen (U - B j) (g j) (hbase j)
      (hgcompact j) (hgsupport j)
  -- Stampacchia vanishing on the zero level set makes the derivative error disappear.
  have hlimit : Tendsto (fun j ↦ U - B j) atTop (𝓝 U) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_intervalTruncation_zero (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        U (fun j ↦ (hεpos j).le) hεzero)
  apply (h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'.mem_of_tendsto
    ((restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω)).continuous.tendsto U |>.comp hlimit)
  exact Eventually.of_forall hmem


/-- A compact Lipschitz function vanishing outside an open domain determines an
`H¹₀` element with the same value and coordinate derivative representatives. No
boundary regularity is needed. -/
theorem exists_H10_of_lipschitzWith_zero_outside
    {n : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} {K : ℝ≥0}
    (hΩopen : IsOpen Ω) (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    (hzero : ∀ x ∉ Ω, f x = 0) :
    ∃ U : H¹₀(Ω), (baseCoordCLM U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      ∀ i, (derivCoordCLM i U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] ∂[i] f := by
  let V := mkW1pOfLipschitzCompactSupport 2 hf hc
  have hbase : (wkpCoordinateCLM (baseIndex n 1) V : ℝ^n → ℝ) =ᵐ[volume] f := by
    simpa only [V, wkpCoordinateCLM_apply, firstOrderRows_baseIndex] using
      mkW1pOfLipschitzCompactSupport_apply_ae 2 hf hc (baseIndex n 1)
  have hmem := restrict_mem_H10_of_continuous_zero_outside hΩopen V f hbase
    hf.continuous hc hzero
  let U : H¹₀(Ω) := ⟨restrictCLM hΩopen.measurableSet (subset_univ Ω) V, hmem⟩
  have hrows (a : DerivIndex n 1) :
      (coordCLM a U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        firstOrderRows f (fun i ↦ ∂[i] f) a := by
    have hglobal := mkW1pOfLipschitzCompactSupport_apply_ae 2 hf hc a
    have hmeasure : domainMeasure n Ω ≤ volume := by
      exact Measure.restrict_le_self
    exact (restrictCLM_apply_ae hΩopen.measurableSet (subset_univ Ω) V a).trans
      (hglobal.filter_mono (ae_mono hmeasure))
  refine ⟨U, ?_, fun i ↦ ?_⟩
  · simpa only [firstOrderRows_baseIndex] using hrows (baseIndex n 1)
  · simpa only [firstOrderRows_singleDerivIndex] using hrows (singleDerivIndex n i)


end SobolevSpace.GraphSpace

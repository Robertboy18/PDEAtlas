/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.ApproximationBounds
public import PDE.Spaces.Sobolev.Calculus.Product.Interpolation
import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall
import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Smooth composition of bounded Sobolev functions on Euclidean space

A bounded `H^k` function may be composed with a smooth scalar reaction in every
spatial dimension. The reaction is required to vanish at zero because the
ambient space has infinite measure; its growth away from the bounded value
range is unrestricted. Uniform derivative bounds for smooth approximations
and weak compactness construct the weak derivatives of the composition.
Above the sharp continuity threshold `n < 2k`, Fourier reconstruction supplies
the essential bound, so no separate boundedness hypothesis is needed.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Composition

open GagliardoNirenberg GraphSpace

variable {n : ℕ} [NeZero n]

/-- Smooth scalar composition preserves bounded global `H^k` in every positive
dimension. The conclusion constructs a Sobolev graph for the same pointwise
composition; it does not presume any of its weak derivatives. -/
theorem exists_hk_composition_of_bounded (k : ℕ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (u : GlobalSobolevSpace n k 2) {B : ℝ}
    (hB : ∀ᵐ x ∂volume, ‖u.toFun x‖ ≤ B) :
    ∃ W : WkpSpaceOn n k 2 univ,
      baseRepresentative W =ᵐ[volume] fun x ↦ f (u.toFun x) := by
  classical
  obtain ⟨v, hv, hvc, hvB, hbase, hlim⟩ :=
    exists_bounded_globalApproximation_Wkp (Approximation.standardMollifier n)
      2 (by norm_num) k u hB
  have hrange (j : ℕ) (x : ℝ^n) : v j x ∈ Icc (-max B 0) (max B 0) := by
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using (hvB j x).trans (le_max_left B 0)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨K, hK⟩ := hf1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-max B 0) (max B 0)) isCompact_Icc
  obtain ⟨g, hg, hgf⟩ := hK.extend_real
  have hg0 : g 0 = 0 :=
    (hgf ⟨neg_nonpos.mpr (le_max_right B 0), le_max_right B 0⟩).symm.trans hf0
  have hvmem (j : ℕ) : MemLp (v j) 2 (domainMeasure n univ) :=
    (hv j).continuous.memLp_of_hasCompactSupport (hvc j)
  let V (j : ℕ) : DerivLp n 2 univ := (hvmem j).toLp (v j)
  let U : DerivLp n 2 univ := u.memLp.toLp u.toFun
  have hV : Tendsto V atTop (𝓝 U) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hvmem u.toFun u.memLp).mpr
    simpa only [domainMeasure, Measure.restrict_univ, Pi.sub_def] using hbase
  have hcomp (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f ∘ v j) := hf.comp (hv j)
  have hcompc (j : ℕ) : HasCompactSupport (f ∘ v j) :=
    (hvc j).comp_left hf0
  let W (j : ℕ) : WkpSpaceOn n k 2 univ :=
    mkWkpSpaceOnOfContDiff (f ∘ v j) (hcomp j) (hcompc j)
  have hWbase (j : ℕ) :
      wkpBaseCoordinateCLM (W j) = hg.compLp hg0 (V j) := by
    apply Lp.ext
    have he := mkWkpSpaceOnOfContDiff_apply_ae
      (p := (2 : ℝ≥0∞)) (Ω := univ) (f ∘ v j) (hcomp j) (hcompc j) (baseIndex n k)
    filter_upwards [he, hg.coeFn_compLp hg0 (V j), (hvmem j).coeFn_toLp] with x hx hy hz
    change (W j).val (baseIndex n k) x = _
    simp only [baseIndex_toList, iteratedPartialDeriv, Function.comp_apply] at hx hy
    exact hx.trans ((hgf (hrange j x)).trans ((congrArg g hz).symm.trans hy.symm))
  have hWlim : Tendsto (fun j ↦ wkpBaseCoordinateCLM (W j)) atTop
      (𝓝 (hg.compLp hg0 U)) := by
    simpa only [hWbase, Function.comp_def] using
      (hg.continuous_compLp hg0).continuousAt.tendsto.comp hV
  obtain ⟨C₀, hC₀⟩ := (Metric.isBounded_range_of_tendsto _ hWlim).exists_norm_le
  have hcoord (a : DerivIndex n k) :
      ∃ C : ℝ, ∀ j, ‖(W j).val a‖ ≤ C := by
    by_cases ha : a.toList.length = 0
    · refine ⟨C₀, fun j ↦ ?_⟩
      have hnil : a.toList = [] := List.length_eq_zero_iff.mp ha
      have ha0 : a = baseIndex n k := by
        apply DerivIndex.ext
        simpa only [baseIndex_toList] using hnil
      subst a
      exact hC₀ _ (mem_range_self j)
    · obtain ⟨C, _, hC⟩ := exists_uniform_lpNorm_iteratedFDeriv_comp_bound
        (Nat.pos_of_ne_zero ha) hf hv hvc hvB (fun α hα ↦ by
          obtain ⟨g, hg, _, ht⟩ := hlim α (hα ▸ a.toList_length_le)
          exact ⟨g, hg, ht⟩)
      refine ⟨C, fun j ↦ ?_⟩
      have hpoint (x : ℝ^n) : ‖iteratedPartialDeriv a.toList (f ∘ v j) x‖ ≤
          ‖iteratedFDeriv ℝ a.toList.length (f ∘ v j) x‖ :=
        PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
          ((hcomp j).of_le (by simp)).contDiffAt
      change ‖(mkWkpSpaceOnOfContDiff (f ∘ v j) (hcomp j) (hcompc j)).val a‖ ≤ C
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      exact (lpNorm_mono_real (hC j).1.norm hpoint).trans
        ((lpNorm_norm (hC j).1.aestronglyMeasurable 2).le.trans (hC j).2)
  choose C hC using hcoord
  have hnorm (j : ℕ) : ‖W j‖ ≤ ∑ a : DerivIndex n k, C a :=
    (PiLp.norm_le_sum_norm (W j).val).trans (Finset.sum_le_sum fun a _ ↦ hC a j)
  obtain ⟨w, _, hw⟩ := exists_hk_of_tendsto_base W _ hnorm hWlim
  refine ⟨w, ?_⟩
  have he : baseRepresentative w =ᵐ[domainMeasure n univ] fun x ↦ g (u.toFun x) := by
    change (wkpBaseCoordinateCLM w : ℝ^n → ℝ) =ᵐ[_] _
    rw [hw]
    filter_upwards [hg.coeFn_compLp hg0 U, u.memLp.coeFn_toLp] with x hx hu
    simpa only [Function.comp_apply, U, hu] using hx
  simp only [domainMeasure, Measure.restrict_univ] at he
  filter_upwards [he, hB] with x hx hxb
  rw [hx]
  symm
  apply hgf
  apply abs_le.mp
  simpa only [Real.norm_eq_abs] using hxb.trans (le_max_left B 0)

/-- Above the strict Sobolev continuity threshold, smooth zero-preserving scalar
composition stays in `H^k`. The zero-order Fourier-moment theorem supplies a
bounded representative; the general bounded-composition theorem constructs
all weak derivatives of the composed function. -/
theorem exists_hk_composition_of_dimension_lt {k : ℕ}
    (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (u : GlobalSobolevSpace n k 2) :
    ∃ W : W^{k,2}(ℝ^n),
      baseRepresentative W =ᵐ[volume] fun x ↦ f (u.toFun x) := by
  obtain ⟨B, hB⟩ := Product.exists_ae_bound_of_dimension_lt hk u
  exact exists_hk_composition_of_bounded k hf hf0 u hB

end SobolevSpace.Composition

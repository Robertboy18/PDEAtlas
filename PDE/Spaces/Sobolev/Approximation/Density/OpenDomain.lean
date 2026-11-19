/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.LocalizedApproximation
public import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.Summation
import Mathlib.Algebra.FiniteSupport.Basic
import CAS.ExactTactic

/-!
# Smooth density on arbitrary open domains

Smooth functions on an open set are dense in its Sobolev space at every finite order and every
finite exponent at least one. This is the theorem of Meyers and Serrin; Evans proves it for bounded
open sets (§5.3.2, Theorem 2). The open set need not be bounded or admit a bounded extension
operator.

The final approximant is smooth on the domain. It need not have compact support
there or be smooth across the boundary; those stronger conclusions fail for
general Sobolev functions on arbitrary open sets.

## How it works

We use a partition of unity as Evans does, here by test functions `ψᵢ` with compact supports in `Ω`,
locally finite there (`exists_testFunction_partition`); these exist on every open set. For each `i`,
`exists_localized_smooth_error` extends `χ u` by zero for a cutoff `χ = 1` on the support of `ψᵢ`,
approximates it by a smooth `vᵢ` (`globalApproximation_WkpSpace`), and gives `‖ψᵢ (vᵢ - u)‖ < δᵢ` in
`W^{k,p}(Ω)`, where `δᵢ = (ε/4) 2⁻ⁱ`. Evans instead mollifies each product `ζᵢ u`; we smooth first
and multiply afterwards. The errors are summable, so `V = u + ∑ᵢ ψᵢ (vᵢ - u)` lies in the complete
space `W^{k,p}(Ω)` with `‖V - u‖ ≤ ε/2`, and its base representative is the locally finite sum
`∑ᵢ ψᵢ vᵢ`, smooth on `Ω` by `contDiffOn_finsum_of_locallyFinite`.

## References

* N. G. Meyers and J. Serrin, "H = W", *Proc. Nat. Acad. Sci. U.S.A.* 51 (1964), no. 6, 1055-1056.
  <https://doi.org/10.1073/pnas.51.6.1055>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.2, Theorem 2, pp. 265-266, for global approximation by
  smooth functions on a bounded open set, proved with a partition of unity subordinate to the sets
  `{x ∈ U : dist(x, ∂U) > 1/i}`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.Approximation.OpenDomain

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Meyers–Serrin approximation with prescribed graph-norm error. For an arbitrary open
domain and finite `p ≥ 1`, every Sobolev element has an arbitrarily close Sobolev element
whose base representative is smooth on the domain. -/
theorem exists_smooth_approximation {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hp : p ≠ ∞) (U : W^{k,p}(Ω)) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : W^{k,p}(Ω), ∃ f : ℝ^n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
      baseRepresentative V =ᵐ[domainMeasure n Ω] f ∧ ‖V - U‖ < ε := by
  let O : Opens (ℝ^n) := ⟨Ω, hΩ⟩
  obtain ⟨ψ, hψ, hfin, hone⟩ := exists_testFunction_partition O
  let δ (i : ℕ) : ℝ := (ε / 4) * (1 / 2) ^ i
  have hδ (i : ℕ) : 0 < δ i := mul_pos (by positivity) (by positivity)
  have hsδ : Summable δ := summable_geometric_two.mul_left (ε / 4)
  have htδ : (∑' i, δ i) = ε / 2 := by
    rw [show δ = (fun i ↦ (ε / 4) * (1 / 2 : ℝ) ^ i) from rfl,
      tsum_mul_left, hasSum_geometric_two.tsum_eq]
    cas
  choose v hv E hEbase hE using fun i ↦
    exists_localized_smooth_error hΩ hp U (ψ i) (hψ i) (hδ i)
  have hsE : Summable (fun i ↦ ‖E i‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ (hE i).le) hsδ
  let V := U + ∑' i, E i
  let f (x : ℝ^n) := ∑ᶠ i, (ψ i).toFun x * v i x
  have hprod : LocallyFinite
      (fun i ↦ (Subtype.val : O → ℝ^n) ⁻¹' support (fun x ↦ (ψ i).toFun x * v i x)) :=
    hfin.subset fun _ _ hx ↦ left_ne_zero_of_mul hx
  refine ⟨V, f, contDiffOn_finsum_of_locallyFinite O _ (fun i ↦ (ψ i).contDiff.mul (hv i))
    hprod, ?_, ?_⟩
  · have hall : ∀ᵐ x ∂domainMeasure n Ω, ∀ i,
        baseRepresentative (E i) x =
          (ψ i).toFun x * (v i x - baseRepresentative U x) :=
      ae_all_iff.mpr hEbase
    filter_upwards [baseRepresentative_add_ae U (∑' i, E i),
      baseRepresentative_tsum_ae E hsE, hall, ae_restrict_mem hΩ.measurableSet]
      with x hadd hsum hx hxΩ
    change baseRepresentative (U + ∑' i, E i) x = f x
    rw [hadd, hsum, tsum_congr hx]
    have hfinite : HasFiniteSupport (fun i ↦ (ψ i).toFun x) :=
      hfin.point_finite ⟨x, hxΩ⟩
    rw [tsum_eq_finsum (hfinite.fun_mul_left (fun i ↦ v i x - baseRepresentative U x))]
    simp_rw [mul_sub]
    rw [finsum_sub_distrib (hfinite.fun_mul_left (fun i ↦ v i x))
      (hfinite.fun_mul_left (fun _ ↦ baseRepresentative U x)),
      ← finsum_mul, hone ⟨x, hxΩ⟩, one_mul]
    simp only [← add_sub_assoc, add_sub_cancel_left, f]
  · change ‖(U + ∑' i, E i) - U‖ < ε
    rw [add_sub_cancel_left]
    calc
      ‖∑' i, E i‖ ≤ ∑' i, ‖E i‖ := norm_tsum_le_tsum_norm hsE
      _ ≤ ∑' i, δ i := hsE.tsum_le_tsum (fun i ↦ (hE i).le) hsδ
      _ = ε / 2 := htδ
      _ < ε := half_lt_self hε

/-- Smooth representatives form a dense subset of the Sobolev graph on every open domain,
at every finite order and finite exponent at least one. -/
theorem dense_smooth {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (hp : p ≠ ∞) :
    Dense {U : W^{k,p}(Ω) | ∃ f : ℝ^n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        baseRepresentative U =ᵐ[domainMeasure n Ω] f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨V, f, hf, hbase, hnorm⟩ := exists_smooth_approximation hΩ hp U hε
  exact ⟨V, ⟨f, hf, hbase⟩, by simpa only [dist_eq_norm, norm_sub_rev] using hnorm⟩

/-- The sequential Meyers–Serrin theorem on an arbitrary open domain. The approximants
belong to the Sobolev graph, have smooth representatives on the domain, and converge
in its graph norm. No extension or boundary regularity hypothesis is required. -/
theorem meyers_serrin {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hp : p ≠ ∞) (U : W^{k,p}(Ω)) :
    ∃ V : ℕ → W^{k,p}(Ω), ∃ f : ℕ → ℝ^n → ℝ,
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) Ω) ∧
      (∀ j, baseRepresentative (V j) =ᵐ[domainMeasure n Ω] f j) ∧
      Filter.Tendsto (fun j ↦ ‖V j - U‖) Filter.atTop (𝓝 0) := by
  obtain ⟨V, hV, ht⟩ := mem_closure_iff_seq_limit.mp (dense_smooth hΩ hp U)
  choose f hf hbase using hV
  refine ⟨V, f, hf, hbase, ?_⟩
  simpa only [sub_self, norm_zero] using
    (ht.sub (tendsto_const_nhds (x := U))).norm

end SobolevSpace.Approximation.OpenDomain

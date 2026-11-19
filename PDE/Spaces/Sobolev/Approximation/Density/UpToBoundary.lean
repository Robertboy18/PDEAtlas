/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Partition
public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.LocalApproximation
public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Cutoff
public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary

/-!
# Smooth approximation up to a C¹ boundary

Evans §5.3.3: on a bounded open set with C¹ boundary, restrictions of ambient smooth
functions are dense in `W^{k,p}` for every finite order `k` and `1 ≤ p < ∞`.
The C¹ assumption is expressed by local regular defining functions.

The proof translates inward on each boundary patch, mollifies, and assembles the
local approximants with a finite smooth partition of unity. It uses no Sobolev
extension operator and requires no higher boundary regularity when `k > 1`.
The approximants have compact support in the ambient space; their supports may
meet the boundary of the domain.

The scalar assembly specializes the Banach-valued theorem through the canonical
linear isometry, preserving the scalar smooth constructor and every derivative row.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268, for approximation by
  functions smooth up to a C¹ boundary; its proof translates inward in each boundary chart,
  mollifies and glues with a partition of unity.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Function MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.Approximation.UpToBoundary

open Boundary GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Inward mollification on a finite partition gives ambient smooth approximants
in the full Sobolev graph norm. -/
theorem InwardPartition.smooth_approximation (P : InwardPartition Ω)
    (hΩ : IsOpen Ω) (hp : p ≠ ∞) (U : W^{k,p}(Ω)) :
    ∃ f : ℕ → ℝ^n → ℝ, ∃ hf : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m),
      ∃ hc : ∀ m, HasCompactSupport (f m),
        Tendsto (fun m ↦
          ‖mkWkpSpaceOnOfContDiff (f m) (hf m) (hc m) - U‖) atTop (𝓝 0) := by
  let e := VectorValued.scalarEquiv (k := k) (p := p) (Ω := ⟨Ω, hΩ⟩)
  obtain ⟨A, f, hf, hc, hderiv, hA⟩ :=
    VectorValued.smooth_approximation_of_inwardPartition P hp (e.symm U)
  have heq (m : ℕ) : mkWkpSpaceOnOfContDiff (f m) (hf m) (hc m) = e (A m) := by
    apply Subtype.ext
    refine PiLp.ext fun a ↦ ?_
    apply Lp.ext
    exact (mkWkpSpaceOnOfContDiff_apply_ae (f m) (hf m) (hc m) a).trans
      (hderiv m a).symm
  have hscalar : Tendsto (fun m ↦ e (A m)) atTop (𝓝 U) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply, Function.comp_def] using
      e.continuous.continuousAt.tendsto.comp hA
  refine ⟨f, hf, hc, ?_⟩
  simp_rw [heq]
  simpa only [sub_self, norm_zero] using
    (hscalar.sub (tendsto_const_nhds (x := U))).norm

/-- Evans §5.3.3, Theorem 3: if `Ω` is open and bounded with C¹ boundary and `1 ≤ p < ∞`, every
`U ∈ W^{k,p}(Ω)` is the limit in the Sobolev norm of smooth compactly supported functions on `ℝ^n`.
Only C¹ boundary regularity is required, independently of the finite order `k`.
Compact support here is in `ℝ^n`, with no support restriction inside `Ω`. -/
theorem smooth_approximation (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC : HasC1Boundary Ω) (hp : p ≠ ∞) (U : W^{k,p}(Ω)) :
    ∃ f : ℕ → ℝ^n → ℝ, ∃ hf : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m),
      ∃ hc : ∀ m, HasCompactSupport (f m),
        Tendsto (fun m ↦
          ‖mkWkpSpaceOnOfContDiff (f m) (hf m) (hc m) - U‖) atTop (𝓝 0) := by
  obtain ⟨P⟩ := exists_inwardPartition hΩ hb hC
  exact P.smooth_approximation hΩ hp U

/-- `smooth_approximation` for a bounded open `Ω` whose boundary is locally the graph of a C¹
function, Evans's definition of a C¹ boundary (App. C.1).
No regularity of the graph beyond C¹ is used, even for higher Sobolev orders. -/
theorem smooth_approximation_of_local_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    (hp : p ≠ ∞) (U : W^{k,p}(Ω)) :
    ∃ f : ℕ → ℝ^n → ℝ, ∃ hf : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m),
      ∃ hc : ∀ m, HasCompactSupport (f m),
        Tendsto (fun m ↦
          ‖mkWkpSpaceOnOfContDiff (f m) (hf m) (hc m) - U‖) atTop (𝓝 0) :=
  smooth_approximation hΩ hb (hasC1Boundary_of_local_graph hgraph) hp U

/-- An ambient test function approximates any Sobolev element to prescribed positive
accuracy on a bounded C¹ domain. Its support may meet the boundary. -/
theorem exists_testFunction_approximation (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC : HasC1Boundary Ω) (hp : p ≠ ∞) (U : W^{k,p}(Ω))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), ‖globalTestFunctionToWkpOn φ - U‖ < ε := by
  obtain ⟨f, hf, hc, ht⟩ := smooth_approximation hΩ hb hC hp U
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨⟨f m, hf m, hc m, subset_univ _⟩, hm⟩

/-- Restrictions of ambient test functions have dense range in `W^{k,p}(Ω)` for
bounded C¹ domains and finite `p ≥ 1`. -/
theorem denseRange_globalTestFunctionToWkpOn (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC : HasC1Boundary Ω) (hp : p ≠ ∞) :
    DenseRange (globalTestFunctionToWkpOn (n := n) (k := k) (p := p) (Ω := Ω)) := by
  apply Metric.denseRange_iff.mpr
  intro U ε hε
  obtain ⟨φ, hφ⟩ := exists_testFunction_approximation hΩ hb hC hp U hε
  exact ⟨φ, by simpa only [dist_eq_norm, norm_sub_rev] using hφ⟩

end SobolevSpace.Approximation.UpToBoundary

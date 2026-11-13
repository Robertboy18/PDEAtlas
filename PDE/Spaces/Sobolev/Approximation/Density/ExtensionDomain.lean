/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.Representative.Basic
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge

/-!
# Approximation on domains with extension operators

Density of restrictions of `C_c^∞(ℝ^n)` functions in `W^{k,p}(Ω)`, `1 ≤ p < ∞`, for domains
that admit a Sobolev extension. The argument is the extend-approximate-restrict corollary: extend
`u ∈ W^{k,p}(Ω)` to `U ∈ W^{k,p}(ℝ^n)`, approximate `U` by mollified truncations `u_m` in
`W^{k,p}(ℝ^n)`, and restrict; since `eLpNorm` over `Ω` is at most `eLpNorm` over `ℝ^n`, every
row converges on `Ω`. The conclusion is that of Evans's approximation by functions smooth up to the
boundary (§5.3.3, Theorem 3), which Evans proves by translating and mollifying in boundary charts;
with an extension operator, as in §5.4, the argument becomes global.

The extension is not constructed here. Both theorems take the proposition
`Extension.Representative.HasExtension n k p Ω`, which asks only for a map
`W^{k,p}(Ω) → W^{k,p}(ℝ^n)` whose values agree with the original function almost everywhere on
`Ω`, with no linearity or boundedness. For one fixed input, the proof only needs one extension:
after choosing it, whole-space convergence restricts contractively to the domain. A uniform
bound on the extension map would control a family of inputs, but is not used in this argument.
Whichever domain class supplies such a map inherits the density statement.

## Main results

* `Approximation.approximation_Wkp`: for `u : SobolevSpaceOn n k p Ω` on an open `Ω` with an
  extension, there are `u_m ∈ C_c^∞(ℝ^n)` with `u_m → u` in `Lᵖ(Ω)` and, for every derivative
  word of length at most `k`, `∂^α u_m → D^α u` in `Lᵖ(Ω)`.
* `GraphSpace.approximation_WkpSpaceOn`: the same statement in the graph-space norm,
  `‖mkWkpSpaceOnOfContDiff (u_m) - U‖ → 0`.

## Implementation notes

The global approximation `globalApproximation_Wkp` and the mollifier calculus live in
`Approximation.Density.Global` and `Approximation.Mollification`; here we transport
them through the extension. The weak derivative of the restricted limit is identified with the
graph-space row by `HasWeakDerivativeOn.unique_ae`, which is why openness of `Ω` is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268, for approximation by
  functions smooth up to the boundary, and §5.4, Theorem 1, pp. 268-271, for the extension operator.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology Sobolev


namespace Approximation

variable {n : ℕ}

/-- Approximation on an open domain with `Extension.Representative.HasExtension`.

Choose a global Sobolev extension, approximate it in every derivative coordinate, and
restrict to `Ω`. The approximants have compact support in `ℝ^n`; their supports need not
lie inside `Ω`, so this is a density statement for the full Sobolev space, not its
zero-boundary subspace. -/
theorem approximation_Wkp (μ : Mollifier n) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (k : ℕ)
    (Ω : Set (ℝ^n)) (u : SobolevSpaceOn n k p Ω) (hΩopen : IsOpen Ω)
    (hExt : SobolevSpace.Extension.Representative.HasExtension n k p Ω) :
      ∃ u_m : ℕ → (ℝ^n → ℝ),
        (∀ m, ContDiff ℝ (⊤ : ℕ∞) (u_m m)) ∧
        (∀ m, HasCompactSupport (u_m m)) ∧
        Filter.Tendsto
          (fun m ↦
            MeasureTheory.eLpNorm (fun x ↦ u_m m x - u.toFun x) p (domainMeasure n Ω))
          Filter.atTop (𝓝 0) ∧
        (∀ α : List (Fin n), α.length ≤ k →
          ∃ g : ℝ^n → ℝ,
            MeasureTheory.MemLp g p (domainMeasure n Ω) ∧
            HasWeakDerivativeOn (n := n) Ω α u.toFun g ∧
            Filter.Tendsto
              (fun m ↦
                MeasureTheory.eLpNorm
                  (fun x ↦ iteratedPartialDeriv (n := n) α (u_m m) x - g x) p
                  (domainMeasure n Ω))
              Filter.atTop (𝓝 0)) := by
  classical
  rcases hExt with ⟨extend, hExtend⟩
  let U : _root_.SobolevSpace.GlobalSobolevSpace n k p := extend u
  have hUae : (∀ᵐ x ∂ domainMeasure n Ω, U.toFun x = u.toFun x) := by
    simpa [U] using hExtend u
  -- approximate the extension globally
  rcases (globalApproximation_Wkp (n := n) (μ := μ) (p := p) hp k U) with
    ⟨u_m, hu_m_smooth, hu_m_cs, hu0, huα⟩
  refine ⟨u_m, hu_m_smooth, hu_m_cs, ?_, fun α hαk ↦ ?_⟩
  · -- `L^p(Ω)` convergence: the norm on `Ω` is at most the global one
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0 (fun _ ↦ zero_le)
      fun m ↦ (MeasureTheory.eLpNorm_congr_ae ?_).trans_le
        (MeasureTheory.eLpNorm_restrict_le _ p volume Ω)
    filter_upwards [hUae] with x hx
    rw [hx]
  · obtain ⟨g, hgLpVol, hweakU, htendVol⟩ := huα α hαk
    -- restrict the global weak-derivative identity to tests supported in `Ω`
    exact ⟨g, hgLpVol.restrict Ω, (hasWeakDerivativeOn_congr_ae hUae .rfl).1
      (hweakU.mono hΩopen.measurableSet (Set.subset_univ Ω)),
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htendVol (fun _ ↦ zero_le)
        fun m ↦ MeasureTheory.eLpNorm_restrict_le _ p volume Ω⟩

end Approximation

namespace GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Extension-and-restriction approximation in the Sobolev graph-space representative norm on
`Ω`.

The representative-level theorem gives convergence of every weak derivative. Uniqueness of weak
derivatives on the open set identifies these limits with the graph coordinates of `U`; since
there are finitely many coordinates, their convergence gives convergence in the graph norm.
Compact support belongs to the global approximants and imposes no zero boundary value on `U`. -/
theorem approximation_WkpSpaceOn (μ : Approximation.Mollifier n) (hp : p ≠ ∞) (k : ℕ)
    (Ω : Set (ℝ^n)) (U : W^{k,p}(Ω)) (hΩopen : IsOpen Ω)
    (hExt : SobolevSpace.Extension.Representative.HasExtension n k p Ω) :
      ∃ f_m : ℕ → (ℝ^n → ℝ),
      ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
      ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
        Filter.Tendsto
          (fun m ↦
            ‖(mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p) (Ω := Ω)
                  (f := f_m m) (hf := hf_m m) (hcs := hcs_m m) - U)‖)
          Filter.atTop (𝓝 0) := by
  let u : SobolevSpaceOn n k p Ω :=
    toRepresentative (n := n) (k := k) (p := p) (Ω := Ω) U
  rcases (SobolevSpace.Approximation.approximation_Wkp
      (n := n) (μ := μ) (p := p) hp (k := k) (Ω := Ω) u hΩopen hExt) with
    ⟨u_m, hu_m_smooth, hu_m_cs, _hu0, hDeriv⟩
  refine ⟨u_m, hu_m_smooth, hu_m_cs, ?_⟩
  have hcoord (a : DerivIndex n k) : Filter.Tendsto (fun m ↦
      ‖((mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p) (Ω := Ω) (f := u_m m)
        (hu_m_smooth m) (hu_m_cs m) : WkpAmbientOn n k p Ω) a - (U : WkpAmbientOn n k p Ω) a)‖)
      Filter.atTop (𝓝 0) := by
    obtain ⟨g, -, hweak, htend⟩ := hDeriv a.toList a.toList_length_le
    have hg_ae : g =ᵐ[domainMeasure n Ω] ((U : WkpAmbientOn n k p Ω) a : ℝ^n → ℝ) :=
      hweak.unique_ae hΩopen (by simpa [u, toRepresentative] using U.property a)
    simpa using tendsto_coord_from_eLpNorm a hu_m_smooth hu_m_cs
      (htend.congr fun m ↦ MeasureTheory.eLpNorm_congr_ae (hg_ae.mono fun x hx ↦ by simp [hx]))
  simpa using tendsto_piLp_norm_of_forall hp (x := fun m ↦
    (mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p) (Ω := Ω) (f := u_m m) (hu_m_smooth m)
      (hu_m_cs m) : WkpAmbientOn n k p Ω) - (U : WkpAmbientOn n k p Ω))
    fun a ↦ by simpa using hcoord a

end GraphSpace

end SobolevSpace

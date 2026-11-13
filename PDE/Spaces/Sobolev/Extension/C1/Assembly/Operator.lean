/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Assembly
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.InteriorPiece
import PDE.Spaces.Sobolev.Approximation.Density.ExtensionDomain
import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.RepresentativeBridge

/-!
# Global C¹ extension assembly

We construct the bounded extension operator from operational
`Boundary.C1ExtensionAtlas` data, using the flattening and reflection argument
of Evans §5.4, Theorem 1. For a domain `Ω` with that atlas, the construction gives

  `E : W^{1,p}(Ω) → W^{1,p}(ℝ^n)`

with `E u = u` almost everywhere on `Ω`, and `E` can be arranged to vanish
outside any prescribed open neighbourhood of `closure Ω`.

We then derive two standard consequences of extension, both obtained by extending to `ℝ^n`,
applying the global result, and restricting. The first is density of restrictions of smooth
compactly supported functions in `W^{1,p}(Ω)` for `p < ∞`, which is Evans §5.3.3, Theorem 3, for
`k = 1`; Evans proves that theorem directly, by translating and mollifying near the boundary. The
second is the Gagliardo–Nirenberg–Sobolev embedding `W^{1,q}(Ω) ⊆ L^{q*}(Ω)` for `1 ≤ q < n`,
whose proof in Evans (§5.6.1, Theorem 2) also goes through the extension operator.

## Main definitions and results

* `extensionCLM`, `extensionCLM_agree_ae`: the assembled operator and its
  agreement with the input on `Ω`.
* `operator`, `exists_extensionOperator_W1p`: the extension operator as a bundled structure.
* `supportedOperator`, `exists_supportedExtensionOperator_W1p`: the version
  supported in a prescribed neighbourhood `V ⊇ closure Ω`.
* `exists_representativeExtensionOperator_W1p`: the representative-level
  interface.
* `approximation_W1p`, `approximation_W1pSpaceOn`: density of smooth
  compactly supported functions.
* `memLp_pStar_of_sobolevSpaceOn`, `memLp_of_le_pStar_of_sobolevSpaceOn`:
  Sobolev embedding into `L^{q*}(Ω)` and into `L^r(Ω)` for `r ≤ q*`.

## How it works

We follow Evans's proof, with a different reflection in the flat step. The partition of unity of the
atlas splits `u` into the interior term `ψ₀ u`, which `InteriorAssembly.extensionCLM` extends by
zero, and boundary terms `ψᵢ u`. `BoundaryPiece.boundaryCLM i` flattens `ψᵢ u` by its chart, extends
it across the hyperplane with `Extension.GraphSpace.HalfSpace.operator`, and pulls the result back.
Evans extends `C¹` functions by the higher-order reflection (3) and reaches `W^{1,p}` by density;
the even reflection we use acts on `W^{1,p}(ℝ^n₊)` directly, so no approximation step is needed.
`extensionCLM` is the sum of these pieces, and it agrees with `u` on `Ω` because each piece
reproduces its partition term `ψᵢ u` there and the partition functions sum to one on `Ω`.

## Implementation notes

The hypothesis is the operational atlas, not the geometric statement that
`∂Ω` is `C¹`. `HasC1GraphBoundary.c1ExtensionAtlas` builds the atlas for a bounded open set
with `C¹` graph boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268; §5.4, Theorem 1, pp. 268-271;
  and §5.6.1, Theorem 2, p. 279.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization

variable [Fact (1 ≤ p)]

variable [Fact (0 < n)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The bounded extension map assembled from the interior contribution and the finite family of
flattened, reflected, and pulled-back boundary pieces supplied by `Boundary.C1ExtensionAtlas`. -/
noncomputable def extensionCLM :
    W^{1,p}(Ω) →L[ℝ]
      W^{1,p}(ℝ^n) :=
  InteriorAssembly.extensionCLM (n := n) (p := p) (Ω := Ω) +
    ∑ i : Fin hΩ.N,
      BoundaryPiece.boundaryCLM (n := n) (p := p) (Ω := Ω) i

/-- The base coordinate of the bounded extension equals the original function
almost everywhere on `Ω`. -/
theorem extensionCLM_agree_ae
    (U : W^{1,p}(Ω)) :
    ∀ᵐ x ∂ domainMeasure n Ω,
      GraphSpace.baseRepresentative
          (extensionCLM (n := n) (p := p) (Ω := Ω) U) x =
        GraphSpace.baseRepresentative U x := by
  classical
  have hinterior := InteriorAssembly.extensionCLM_agree_ae
    (n := n) (p := p) (Ω := Ω) U
  have hboundary : ∀ᵐ x ∂ domainMeasure n Ω, ∀ i : Fin hΩ.N,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (BoundaryPiece.boundaryCLM
            (n := n) (p := p) (Ω := Ω) i U) x =
        (hΩ.boundaryCutoff i).toFun x *
          GraphSpace.baseRepresentative (n := n) (p := p) U x :=
    MeasureTheory.ae_all_iff.2 fun i ↦
      BoundaryPiece.boundaryCLM_agree_ae
        (n := n) (p := p) (Ω := Ω) i U
  have hmem : ∀ᵐ x ∂ domainMeasure n Ω, x ∈ Ω := by
    simpa [domainMeasure] using
      (MeasureTheory.ae_restrict_mem hΩ.isOpen.measurableSet :
        ∀ᵐ x ∂ (MeasureTheory.volume : Measure (ℝ^n)).restrict Ω, x ∈ Ω)
  let I := InteriorAssembly.extensionCLM (n := n) (p := p) (Ω := Ω) U
  let B := (∑ i : Fin hΩ.N,
    BoundaryPiece.boundaryCLM (n := n) (p := p) (Ω := Ω) i) U
  have haddGlobal := GraphSpace.baseRepresentative_add_ae (n := n) (p := p) I B
  have hsumGlobal := GraphSpace.baseRepresentative_sum_ae (n := n) (p := p)
    (fun i : Fin hΩ.N ↦
      BoundaryPiece.boundaryCLM (n := n) (p := p) (Ω := Ω) i U)
  have haddΩ' := MeasureTheory.ae_restrict_of_ae (s := Ω) haddGlobal
  have hsumΩ' := MeasureTheory.ae_restrict_of_ae (s := Ω) hsumGlobal
  have haddΩ : ∀ᵐ x ∂ domainMeasure n Ω,
      GraphSpace.baseRepresentative (n := n) (p := p) (I + B) x =
        GraphSpace.baseRepresentative (n := n) (p := p) I x +
          GraphSpace.baseRepresentative (n := n) (p := p) B x := by
    simpa [domainMeasure, Measure.restrict_restrict, inter_univ] using haddΩ'
  have hsumΩ : ∀ᵐ x ∂ domainMeasure n Ω,
      GraphSpace.baseRepresentative (n := n) (p := p) B x =
        ∑ i : Fin hΩ.N,
          GraphSpace.baseRepresentative (n := n) (p := p)
            (BoundaryPiece.boundaryCLM
              (n := n) (p := p) (Ω := Ω) i U) x := by
    simpa [B, domainMeasure, Measure.restrict_restrict, inter_univ] using hsumΩ'
  filter_upwards [hinterior, hboundary, hmem, haddΩ, hsumΩ] with
      x hxInterior hxBoundary hxΩ hxAdd hxSum
  rw [show extensionCLM (n := n) (p := p) (Ω := Ω) U = I + B by
      simp [extensionCLM, I, B]]
  rw [hxAdd]
  have hxInterior' :
      GraphSpace.baseRepresentative (n := n) (p := p) I x =
        (hΩ.interiorCutoff).toFun x *
          GraphSpace.baseRepresentative (n := n) (p := p) U x := by
    simpa [I] using hxInterior
  rw [hxInterior', hxSum]
  rw [Finset.sum_congr rfl (fun i _ ↦ hxBoundary i)]
  rw [← Finset.sum_mul, ← add_mul, hΩ.cutoff_sum_eq_one x hxΩ]
  simp

/-- The operator `extensionCLM`, bundled with its almost-everywhere agreement with the input
on `Ω`, for a domain `Ω` carrying `Boundary.C1ExtensionAtlas` (the chart and partition data of
the proof of Evans §5.4, Theorem 1). -/
noncomputable def operator :
    SobolevSpace.Extension.GraphSpace.Operator n 1 p Ω where
  toContinuousLinearMap := extensionCLM (n := n) (p := p) (Ω := Ω)
  agree_ae := extensionCLM_agree_ae (n := n) (p := p) (Ω := Ω)

/-- Every domain carrying the operational chart and partition data admits a
bounded linear extension `W^{1,p}(Ω) → W^{1,p}(ℝ^n)`. -/
theorem exists_extensionOperator_W1p :
    SobolevSpace.Extension.GraphSpace.HasExtensionOperator n 1 p Ω :=
  ⟨operator (n := n) (p := p) (Ω := Ω)⟩

/-- The operational `C¹` extension localized to a prescribed open
neighborhood `V` of `closure Ω`.

Its base representative agrees with the original function almost everywhere
on `Ω` and vanishes almost everywhere outside `V`, the almost-everywhere form of
condition (ii), "`Eu` has support within `V`", of Evans §5.4, Theorem 1. -/
noncomputable def supportedOperator
    (V : Set (ℝ^n)) (hVopen : IsOpen V) (hΩV : closure Ω ⊆ V) :
    SobolevSpace.Extension.GraphSpace.SupportedOperator n 1 p Ω V :=
  (operator (n := n) (p := p) (Ω := Ω)).withSupportIn
    V hΩ.isOpen.measurableSet hVopen hΩ.bounded.isCompact_closure hΩV

/-- On a domain carrying the operational `Boundary.C1ExtensionAtlas`, the bounded
`W¹ᵖ` extension can be chosen to be supported almost everywhere in every
prescribed open neighborhood of `closure Ω`. -/
theorem exists_supportedExtensionOperator_W1p
    (V : Set (ℝ^n)) (hVopen : IsOpen V) (hΩV : closure Ω ⊆ V) :
    SobolevSpace.Extension.GraphSpace.HasSupportedExtensionOperator
      n 1 p Ω V :=
  ⟨supportedOperator
    (n := n) (p := p) (Ω := Ω) V hVopen hΩV⟩

/-- Forgetting the chosen `Lᵖ` derivative coordinates recovers the original
representative-level extension interface. -/
theorem exists_representativeExtensionOperator_W1p :
    SobolevSpace.Extension.Representative.HasExtension n 1 p Ω :=
  SobolevSpace.Extension.GraphSpace.exists_representativeExtensionOperator
    (exists_extensionOperator_W1p (n := n) (p := p) (Ω := Ω))

/-!
## Density consequences

Smooth approximation on a regular domain follows by extending to `ℝ^n`, applying the global
mollification theorem `SobolevSpace.Approximation.approximation_Wkp`, and restricting back to the
domain; Evans §5.3.3, Theorem 3 argues directly instead. The extension theorem above discharges
the extension hypothesis of `approximation_Wkp` for domains carrying `Boundary.C1ExtensionAtlas`,
and `HasC1GraphBoundary.c1ExtensionAtlas` supplies that atlas for a bounded open set in
`ℝ^(n + 1)` with `C¹` graph boundary.
-/

/-- For `p < ∞` and a domain `Ω` carrying `Boundary.C1ExtensionAtlas`, every `u ∈ W¹ᵖ(Ω)` is
approximated by smooth compactly supported functions `u_m` on `ℝ^n`: `u_m → u` in `Lᵖ(Ω)`, and
for every list `alpha` of length at most one, `∂^alpha u_m` tends in `Lᵖ(Ω)` to an `Lᵖ` weak
derivative of `u` along `alpha`. This is Evans §5.3.3, Theorem 3, for `k = 1`, with the atlas in
place of the `C¹` boundary. -/
theorem approximation_W1p
    (hp : p ≠ ∞)
    (u : SobolevSpaceOn n 1 p Ω) :
    ∃ u_m : ℕ → (ℝ^n → ℝ),
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (u_m m)) ∧
      (∀ m, HasCompactSupport (u_m m)) ∧
      Filter.Tendsto
        (fun m ↦
          MeasureTheory.eLpNorm (fun x ↦ u_m m x - u.toFun x) p (domainMeasure n Ω))
        Filter.atTop (nhds 0) ∧
      (∀ alpha : List (Fin n), alpha.length ≤ 1 →
        ∃ g : ℝ^n → ℝ,
          MeasureTheory.MemLp g p (domainMeasure n Ω) ∧
          HasWeakDerivativeOn (n := n) Ω alpha u.toFun g ∧
          Filter.Tendsto
            (fun m ↦
              MeasureTheory.eLpNorm
                (fun x ↦ iteratedPartialDeriv (n := n) alpha (u_m m) x - g x) p
                (domainMeasure n Ω))
            Filter.atTop (nhds 0)) := by
  let mu := SobolevSpace.Approximation.standardMollifier n
  exact SobolevSpace.Approximation.approximation_Wkp
    (n := n) (p := p) mu hp 1 Ω u hΩ.isOpen
      (exists_representativeExtensionOperator_W1p (n := n) (p := p) (Ω := Ω))

/-- The restrictions of globally smooth compactly supported functions are dense in the
Sobolev graph space `W¹ᵖ(Ω)` on a domain carrying `Boundary.C1ExtensionAtlas`, when `p < ∞`. -/
theorem approximation_W1pSpaceOn
    (hp : p ≠ ∞)
    (U : W^{1,p}(Ω)) :
    ∃ f_m : ℕ → (ℝ^n → ℝ),
    ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
    ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
      Filter.Tendsto
        (fun m ↦
          ‖(SobolevSpace.GraphSpace.mkWkpSpaceOnOfContDiff
              (n := n) (k := 1) (p := p) (Ω := Ω)
              (f := f_m m)
              (hf := hf_m m) (hcs := hcs_m m) - U)‖)
        Filter.atTop (nhds 0) := by
  let mu := SobolevSpace.Approximation.standardMollifier n
  exact SobolevSpace.GraphSpace.approximation_WkpSpaceOn
    (n := n) (p := p) mu hp 1 Ω U hΩ.isOpen
      (exists_representativeExtensionOperator_W1p (n := n) (p := p) (Ω := Ω))

/-!
## Sobolev embedding consequences

The bounded-domain embedding of Evans §5.6.1, Theorem 2 is also proved by extension to `ℝ^n`.
The corollaries below discharge the extension hypothesis of the embedding theorems in
`SobolevSpace.Inequalities` with the operator above.
-/

/-- The critical Sobolev embedding on a domain carrying `Boundary.C1ExtensionAtlas`: if
`1 ≤ q < n`, then every `W¹ᵠ(Ω)` function belongs to `L^{q*}(Ω)`, where `1/q* = 1/q - 1/n`
(the membership part of Evans §5.6.1, Theorem 2, with the atlas in place of the `C¹`
boundary). -/
theorem memLp_pStar_of_sobolevSpaceOn
    {q : NNReal} (hq : (1 : NNReal) ≤ q) (hq_lt : (q : ℝ) < (n : ℝ))
    (u : SobolevSpaceOn n 1 (q : ℝ≥0∞) Ω) :
    MeasureTheory.MemLp u.toFun
      (SobolevSpace.Inequalities.pStar n q : ℝ≥0∞) (domainMeasure n Ω) := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  exact SobolevSpace.Inequalities.memLp_pStar_of_sobolevSpaceOn_of_extension
    (n := n) hq (Fact.out : 0 < n) hq_lt
      (exists_representativeExtensionOperator_W1p
        (n := n) (p := (q : ℝ≥0∞)) (Ω := Ω)) u

/-- On a domain carrying `Boundary.C1ExtensionAtlas`, `W¹ᵠ(Ω)` embeds into every `Lʳ(Ω)` with
`r ≤ q*`, under `1 ≤ q < n`. -/
theorem memLp_of_le_pStar_of_sobolevSpaceOn
    {q : NNReal} (hq : (1 : NNReal) ≤ q) (hq_lt : (q : ℝ) < (n : ℝ))
    (u : SobolevSpaceOn n 1 (q : ℝ≥0∞) Ω)
    {r : ℝ≥0∞} (hr : r ≤ (SobolevSpace.Inequalities.pStar n q : ℝ≥0∞)) :
    MeasureTheory.MemLp u.toFun r (domainMeasure n Ω) := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  exact SobolevSpace.Inequalities.memLp_of_le_pStar_of_sobolevSpaceOn_of_extension
    (n := n) hq (Fact.out : 0 < n) hq_lt
      (exists_representativeExtensionOperator_W1p
        (n := n) (p := (q : ℝ≥0∞)) (Ω := Ω)) hΩ.bounded u hr

end C1

end Extension

end SobolevSpace

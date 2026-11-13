/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge
import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator

/-!
# Planar `H²` to `W^{1,p}` embeddings

On a bounded planar domain `Ω ⊆ ℝ^2` carrying a `Boundary.C1ExtensionAtlas`, every function in
`H²(Ω)` has base and first-derivative coordinates in `L^p(Ω)` for every finite `p`, and the
resulting inclusion `H²(Ω) → W^{1,p}(Ω)` is a bounded linear map.

The mechanism is the first-order Sobolev embedding in dimension two. Each order-at-most-one
slice of an `H²` function is an `H¹ = W^{1,2}` function. On a domain of finite measure it also
lies in `W^{1,q}` for every `1 ≤ q < 2`, and the extension theorem for `C¹` atlases places it in
`L^{q^*}` with `q^* = 2q/(2-q)`. As `q` runs over `[1, 2)`, `q^*` runs over `[2, ∞)`, so every
finite exponent is reached. This is the planar instance of the embedding `W^{1,q} ⊆ L^{q^*}` on
bounded `C¹` domains, Evans, PDE, §5.6.1, Theorem 2. The detour
through `q < 2` is forced by `p = 2` being the critical exponent in dimension two; the
planar Hölder and continuity results build on this embedding.

## Main results

* `H1SpaceOn.memLp_of_le_pStar_of_c1ExtensionAtlas`: the base coordinate of an `H¹` function on
  such a domain lies in `L^p` whenever `p ≤ q^*` for some `1 ≤ q < 2`.
* `memLp_orderOneCoordinate_of_c1ExtensionAtlas`: the same for every order-at-most-one
  coordinate of an `H²` function.
* `h2ToW1pOfC1ExtensionAtlas`: the `W^{1,p}` bundle assembled from those coordinates, with
  `h2ToW1pOfC1ExtensionAtlas_apply_ae` recording that its rows are the original ones a.e.
* `h2ToW1pOfC1ExtensionAtlasCLM`: the inclusion as a continuous linear map, and
  `norm_h2ToW1pOfC1ExtensionAtlas_le`, the resulting operator-norm bound.

## Implementation notes

The target exponent `p : ℝ≥0∞` is arbitrary subject to `1 ≤ p ≤ q^*`; `p = ∞` is excluded only
because `q^* < ∞`. Continuity is proved without an explicit constant: convergence in either Sobolev
space implies convergence in measure of every coordinate, and source and target coordinates
agree a.e., so the graph is closed and the closed graph theorem applies.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, Theorem 2, (15), p. 279.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace

open Set MeasureTheory Function
open scoped ENNReal Topology Sobolev

/-- Every exponent at most the Sobolev conjugate of `1 ≤ q < 2` is available for the base
representative of a `W¹²` function on a planar domain carrying `Boundary.C1ExtensionAtlas`. -/
theorem H1SpaceOn.memLp_of_le_pStar_of_c1ExtensionAtlas
    {Ω : Set (ℝ^2)} [Fact (0 < (2 : ℕ))] [Boundary.C1ExtensionAtlas 2 Ω]
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    (V : H¹(Ω)) {p : ℝ≥0∞}
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞)) :
    MeasureTheory.MemLp
      ((V : WkpAmbientOn 2 1 2 Ω) (baseIndex 2 1) : ℝ^2 → ℝ)
      p (domainMeasure 2 Ω) := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
  have hqle : (q : ℝ≥0∞) ≤ 2 := by
    exact_mod_cast (le_of_lt hq2)
  let Vq : W^{1,(q : ℝ≥0∞)}(Ω) :=
    lowerExponentOfFiniteMeasure
      (n := 2) (k := 1) (p := 2) (q := (q : ℝ≥0∞))
      (Ω := Ω) hqle V
  have hVq := Extension.C1.memLp_of_le_pStar_of_sobolevSpaceOn
    (n := 2) (q := q) (Ω := Ω) hq1 hq2
      (toRepresentative Vq) hp
  have hae :=
    lowerExponentOfFiniteMeasure_apply_ae
      (n := 2) (k := 1) (p := 2) (q := (q : ℝ≥0∞))
      (Ω := Ω) hqle V (baseIndex 2 1)
  exact (MeasureTheory.memLp_congr_ae hae).1 (by
    simpa [Vq, baseRepresentative] using hVq)

/-- Quantitative boundedness of every first-order slice extracted from an
order-two Sobolev bundle. -/
theorem norm_derivativeSlice_le {m : ℕ} {S : Set (ℝ^m)}
    (U : W^{2,2}(S)) (α : List (Fin m)) (hα : α.length < 2) :
    ‖derivativeSlice (n := m) (Ω := S) α hα U‖ ≤
      ‖derivativeSlice (n := m) (Ω := S) α hα‖ * ‖U‖ :=
  (derivativeSlice (n := m) (Ω := S) α hα).le_opNorm U

section Assembly

variable {Ω : Set (ℝ^2)} [Fact (0 < (2 : ℕ))]
  [Boundary.C1ExtensionAtlas 2 Ω]

/-- Every base or first-derivative coordinate of an `H²` function is in `Lᵖ`,
provided `p` is at most the Sobolev conjugate of an auxiliary `1 ≤ q < 2`. -/
theorem memLp_orderOneCoordinate_of_c1ExtensionAtlas
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞}
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞))
    (U : W^{2,2}(Ω)) (a : DerivIndex 2 1) :
    MeasureTheory.MemLp
      ((U : WkpAmbientOn 2 2 2 Ω)
        (a.castOrder (by omega)) : ℝ^2 → ℝ)
      p (domainMeasure 2 Ω) := by
  let V := derivativeSlice (n := 2) (Ω := Ω) a.toList
    (Nat.lt_succ_of_le a.toList_length_le) U
  have hV := H1SpaceOn.memLp_of_le_pStar_of_c1ExtensionAtlas
    (Ω := Ω) hq1 hq2 V hp
  have hae :
      (((V : H¹(Ω)) : WkpAmbientOn 2 1 2 Ω) (baseIndex 2 1) :
          ℝ^2 → ℝ) =ᵐ[domainMeasure 2 Ω]
        ((U : WkpAmbientOn 2 2 2 Ω)
          (a.castOrder (by omega)) : ℝ^2 → ℝ) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simp [V]
    · simp [V, derivativeSliceIndex, derivIndexOfList_singleton]
  exact (MeasureTheory.memLp_congr_ae hae).1 hV

/-- The order-one bundle formed from the original base and first derivative
coordinates of an `H²` function, at exponent `p`. -/
noncomputable def h2ToW1pOfC1ExtensionAtlas
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞}
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞))
    (U : W^{2,2}(Ω)) : W^{1,p}(Ω) := by
  let f : ℝ^2 → ℝ :=
    ((U : WkpAmbientOn 2 2 2 Ω)
      ((baseIndex 2 1).castOrder (by omega)) : ℝ^2 → ℝ)
  let d : DerivIndex 2 1 → ℝ^2 → ℝ := fun a ↦
    ((U : WkpAmbientOn 2 2 2 Ω)
      (a.castOrder (by omega)) : ℝ^2 → ℝ)
  apply mkWkpSpaceOnOfWeakDerivatives (n := 2) (k := 1) (p := p)
    (Ω := Ω) f d
  · rfl
  · intro a
    exact memLp_orderOneCoordinate_of_c1ExtensionAtlas
      (Ω := Ω) hq1 hq2 hp U a
  · intro a
    let V := lowerOrderCLM (n := 2) (k := 1) (m := 2)
      (p := 2) (Ω := Ω) (by omega) U
    simpa [f, d, V, lowerOrderCLM_apply] using V.property a

/-- The assembled `W¹,p` bundle uses the original H2 coordinate in every
row, almost everywhere on the domain. -/
theorem h2ToW1pOfC1ExtensionAtlas_apply_ae
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞}
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞))
    (U : W^{2,2}(Ω)) (a : DerivIndex 2 1) :
    (((h2ToW1pOfC1ExtensionAtlas (Ω := Ω) hq1 hq2 hp U :
        WkpAmbientOn 2 1 p Ω) a : DerivLp 2 p Ω) : ℝ^2 → ℝ)
      =ᵐ[domainMeasure 2 Ω]
        ((U : WkpAmbientOn 2 2 2 Ω)
          (a.castOrder (by omega)) : ℝ^2 → ℝ) := by
  simp only [h2ToW1pOfC1ExtensionAtlas, mkWkpSpaceOnOfWeakDerivatives]
  exact (memLp_orderOneCoordinate_of_c1ExtensionAtlas
    (Ω := Ω) hq1 hq2 hp U a).coeFn_toLp

-- The algebraic map used in the closed-graph construction below.
/-- The coordinate-preserving planar inclusion from `H²` into `W¹,p` as a linear
map. -/
noncomputable def h2ToW1pOfC1ExtensionAtlasLinearMap
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞}
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞)) :
    W^{2,2}(Ω) →ₗ[ℝ] W^{1,p}(Ω) where
  toFun := h2ToW1pOfC1ExtensionAtlas (Ω := Ω) hq1 hq2 hp
  map_add' U V := by
    apply Subtype.ext
    refine PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
    filter_upwards
      [h2ToW1pOfC1ExtensionAtlas_apply_ae (Ω := Ω) hq1 hq2 hp (U + V) a,
       h2ToW1pOfC1ExtensionAtlas_apply_ae (Ω := Ω) hq1 hq2 hp U a,
       h2ToW1pOfC1ExtensionAtlas_apply_ae (Ω := Ω) hq1 hq2 hp V a,
       MeasureTheory.Lp.coeFn_add
         ((U : WkpAmbientOn 2 2 2 Ω)
           (a.castOrder (by omega)))
         ((V : WkpAmbientOn 2 2 2 Ω)
           (a.castOrder (by omega))),
       MeasureTheory.Lp.coeFn_add
         ((h2ToW1pOfC1ExtensionAtlas
            (Ω := Ω) hq1 hq2 hp U : WkpAmbientOn 2 1 p Ω) a)
         ((h2ToW1pOfC1ExtensionAtlas
            (Ω := Ω) hq1 hq2 hp V : WkpAmbientOn 2 1 p Ω) a)]
      with x huv hu hv hsource htarget
    rw [huv]
    change
      ((((U : WkpAmbientOn 2 2 2 Ω)
          (a.castOrder (by omega))) +
        ((V : WkpAmbientOn 2 2 2 Ω)
          (a.castOrder (by omega))) :
            DerivLp 2 2 Ω) : ℝ^2 → ℝ) x =
        ((((h2ToW1pOfC1ExtensionAtlas
            (Ω := Ω) hq1 hq2 hp U : WkpAmbientOn 2 1 p Ω) a) +
          ((h2ToW1pOfC1ExtensionAtlas
            (Ω := Ω) hq1 hq2 hp V : WkpAmbientOn 2 1 p Ω) a) :
            DerivLp 2 p Ω) : ℝ^2 → ℝ) x
    rw [hsource, htarget]
    simp only [Pi.add_apply]
    rw [hu, hv]
  map_smul' c U := by
    apply Subtype.ext
    refine PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
    filter_upwards
      [h2ToW1pOfC1ExtensionAtlas_apply_ae (Ω := Ω) hq1 hq2 hp (c • U) a,
       h2ToW1pOfC1ExtensionAtlas_apply_ae (Ω := Ω) hq1 hq2 hp U a,
       MeasureTheory.Lp.coeFn_smul c
         ((U : WkpAmbientOn 2 2 2 Ω)
           (a.castOrder (by omega))),
       MeasureTheory.Lp.coeFn_smul c
         ((h2ToW1pOfC1ExtensionAtlas
            (Ω := Ω) hq1 hq2 hp U : WkpAmbientOn 2 1 p Ω) a)]
      with x hcu hu hsource htarget
    rw [hcu]
    change
      ((c • ((U : WkpAmbientOn 2 2 2 Ω)
        (a.castOrder (by omega))) :
          DerivLp 2 2 Ω) : ℝ^2 → ℝ) x =
        ((c • ((h2ToW1pOfC1ExtensionAtlas (Ω := Ω) hq1 hq2 hp U :
          WkpAmbientOn 2 1 p Ω) a) : DerivLp 2 p Ω) : ℝ^2 → ℝ) x
    rw [hsource, htarget]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu]

/-- The coordinate-preserving planar inclusion from `H²` into `W¹,p`.

Continuity follows from the closed graph theorem: convergence in either Sobolev
space implies convergence in measure of every coordinate, and the source and
target coordinates agree almost everywhere. -/
noncomputable def h2ToW1pOfC1ExtensionAtlasCLM
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞)) :
    W^{2,2}(Ω) →L[ℝ] W^{1,p}(Ω) := by
  let g := h2ToW1pOfC1ExtensionAtlasLinearMap
    (Ω := Ω) hq1 hq2 hp
  let sourceProj (a : DerivIndex 2 1) :
      W^{2,2}(Ω) →L[ℝ] DerivLp 2 2 Ω :=
    (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (β := fun _ : DerivIndex 2 2 ↦ DerivLp 2 2 Ω)
      (a.castOrder (by omega))).comp
      (Submodule.subtypeL (wkpSubmoduleOn 2 2 2 Ω))
  let targetProj (a : DerivIndex 2 1) :
      W^{1,p}(Ω) →L[ℝ] DerivLp 2 p Ω :=
    (PiLp.proj (𝕜 := ℝ) (p := p)
      (β := fun _ : DerivIndex 2 1 ↦ DerivLp 2 p Ω) a).comp
      (Submodule.subtypeL (wkpSubmoduleOn 2 1 p Ω))
  exact ContinuousLinearMap.ofSeqClosedGraph (g := g) (by
    intro u U V hu hgu
    apply Subtype.ext
    refine PiLp.ext fun a ↦ MeasureTheory.Lp.ext ?_
    have h2 : TendstoInMeasure (domainMeasure 2 Ω)
        (fun j ↦ ((sourceProj a (u j) : DerivLp 2 2 Ω) : ℝ^2 → ℝ)) Filter.atTop
        ((sourceProj a U : DerivLp 2 2 Ω) : ℝ^2 → ℝ) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp
        (((sourceProj a).continuous.tendsto U).comp hu)
    have hp' : TendstoInMeasure (domainMeasure 2 Ω)
        (fun j ↦ ((targetProj a (g (u j)) : DerivLp 2 p Ω) : ℝ^2 → ℝ)) Filter.atTop
        ((targetProj a V : DerivLp 2 p Ω) : ℝ^2 → ℝ) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp
        (((targetProj a).continuous.tendsto V).comp hgu)
    have hsame : ∀ j,
        ((targetProj a (g (u j)) : DerivLp 2 p Ω) : ℝ^2 → ℝ)
          =ᵐ[domainMeasure 2 Ω]
            ((sourceProj a (u j) : DerivLp 2 2 Ω) : ℝ^2 → ℝ) := by
      intro j
      exact h2ToW1pOfC1ExtensionAtlas_apply_ae
        (Ω := Ω) hq1 hq2 hp (u j) a
    have hVU := MeasureTheory.tendstoInMeasure_ae_unique
      (hp'.congr_left hsame) h2
    exact hVU.trans
      (h2ToW1pOfC1ExtensionAtlas_apply_ae
        (Ω := Ω) hq1 hq2 hp U a).symm)

/-- The continuous inclusion agrees with the assembled bundle `h2ToW1pOfC1ExtensionAtlas` on
elements. -/
@[simp]
theorem h2ToW1pOfC1ExtensionAtlasCLM_apply
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞))
    (U : W^{2,2}(Ω)) :
    h2ToW1pOfC1ExtensionAtlasCLM (Ω := Ω) hq1 hq2 hp U =
      h2ToW1pOfC1ExtensionAtlas (Ω := Ω) hq1 hq2 hp U :=
  rfl

/-- The planar `H² → W¹,p` inclusion is bounded by its operator norm. -/
theorem norm_h2ToW1pOfC1ExtensionAtlas_le
    {q : NNReal} (hq1 : (1 : NNReal) ≤ q) (hq2 : (q : ℝ) < 2)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≤ (SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞))
    (U : W^{2,2}(Ω)) :
    ‖h2ToW1pOfC1ExtensionAtlas (Ω := Ω) hq1 hq2 hp U‖ ≤
      ‖h2ToW1pOfC1ExtensionAtlasCLM (Ω := Ω) hq1 hq2 hp‖ * ‖U‖ := by
  simpa using
    (h2ToW1pOfC1ExtensionAtlasCLM
      (Ω := Ω) hq1 hq2 hp).le_opNorm U

end Assembly

end GraphSpace
end SobolevSpace

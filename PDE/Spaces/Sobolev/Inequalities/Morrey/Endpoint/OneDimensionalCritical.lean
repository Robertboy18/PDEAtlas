/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.ContinuousRepresentative.Linearity

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
import PDE.Spaces.Sobolev.Calculus.Slicing.FundamentalTheorem

/-!
# The one-dimensional critical Sobolev embedding

The positive-exponent Morrey space omits the endpoint `n = p = 1`, handled here:
every global `W^{1,1}(ℝ)` class has a unique bounded continuous representative.
The construction first proves the smooth estimate

`‖u‖∞ ≤ ‖u'‖₁`

for compactly supported functions, then extends the lift by global Sobolev
density. On a domain carrying `Boundary.C1ExtensionAtlas`, composition with
the extension operator and restriction gives the corresponding domain map.

In dimension `n ≥ 2` the space `W^{1,n}` does not embed into `L^∞` (Evans, PDE, §5.6.1, p. 280,
gives `log log (1 + 1/|x|)` on the unit ball), which is why this endpoint is one-dimensional.

## Main results

* `norm_sub_le_eLpNorm_weakDerivative_one_toReal`: for a continuous `f` with weak derivative
  `g ∈ L¹(ℝ)`, `|f(x) - f(y)| ≤ ‖g‖₁`.
* `norm_apply_le_eLpNorm_partialDeriv_one_toReal`: `‖u‖_∞ ≤ ‖u'‖₁` for smooth compactly
  supported `u`.
* `boundedContinuousRepresentative`, `criticalEmbedding`: the continuous representative of a
  `W^{1,1}(ℝ)` class and the resulting bounded linear map `W^{1,1}(ℝ) → C⁰_b(ℝ)` of norm at
  most `1`, agreeing a.e. with the base coordinate (`criticalEmbedding_ae`).
* `criticalEmbeddingOn`, `norm_criticalEmbeddingOn_le`: the domain version obtained by extension
  and restriction, with operator norm bounded by that of the extension operator.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 8, for the embedding `W^{1,p}(I) ⊂ L^∞(I)` on an interval `I` for every
  `1 ≤ p ≤ ∞`, including the endpoint `p = 1`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, The borderline case p = n, p. 280, which shows that
  for `n > 1` the function `log log (1 + 1/|x|)` belongs to `W^{1,n}(B^0(0, 1))` but not to `L^∞`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory PDE.Common Set
open scoped BoundedContinuousFunction ENNReal Sobolev

namespace CriticalOneDimensional

/-- The oscillation of a continuous global weak `W^{1,1}` representative is
bounded by the global `L¹` norm of its weak derivative. -/
theorem norm_sub_le_eLpNorm_weakDerivative_one_toReal
    (f g : ℝ^1 → ℝ)
    (hf : Continuous f)
    (hg : MemLp g 1 (volume : Measure (ℝ^1)))
    (hweak : HasWeakDerivativeOn (n := 1) Set.univ [0] f g)
    (x y : ℝ^1) :
    ‖f y - f x‖ ≤ (eLpNorm g 1 volume).toReal := by
  let a := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x
  let b := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) y
  have hftc :=
    FundamentalTheorem.intervalIntegral_weakDerivative_eq_sub
      f g hf hg hweak a b
  have hgCoord :
      Integrable
        (fun t ↦ g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t))
        (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp <|
      hg.comp_measurePreserving
        ((PiLp.volume_preserving_toLp (Fin 1)).comp
          ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  have heLp :
      eLpNorm
          (fun t ↦ g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t))
          1 (volume : Measure ℝ) =
        eLpNorm g 1 (volume : Measure (ℝ^1)) :=
    eLpNorm_comp_measurePreserving
      hg.aestronglyMeasurable
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  calc
    ‖f y - f x‖ =
        ‖∫ t in a..b, g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)‖ := by
      rw [hftc]
      simp only [a, b]
      rw [(PiLp.equivOfUnique 2 ℝ
        (fun _ : Fin 1 ↦ ℝ)).symm_apply_apply]
      rw [(PiLp.equivOfUnique 2 ℝ
        (fun _ : Fin 1 ↦ ℝ)).symm_apply_apply]
    _ ≤ ∫ t in Set.uIoc a b, ‖g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t, ‖g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)‖ := by
      exact MeasureTheory.setIntegral_le_integral
        hgCoord.norm
        (MeasureTheory.ae_of_all _ fun t ↦
          norm_nonneg (g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)))
    _ = (eLpNorm (fun t ↦ g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)) 1
          (volume : Measure ℝ)).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hgCoord.aestronglyMeasurable,
        integral_norm_eq_lintegral_enorm hgCoord.aestronglyMeasurable]
    _ = (eLpNorm g 1 (volume : Measure (ℝ^1))).toReal := by
      rw [heLp]

/-- A smooth compactly supported function on the line has pointwise norm at
most the `L¹` norm of its derivative. -/
theorem norm_apply_le_eLpNorm_partialDeriv_one_toReal
    (u : ℝ^1 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcompact : HasCompactSupport u)
    (x : ℝ^1) :
    ‖u x‖ ≤
      (eLpNorm (fun z ↦ (∂[0] u) z)
        1 volume).toReal := by
  obtain ⟨R, hR⟩ :=
    hcompact.isCompact.isBounded.subset_closedBall (0 : ℝ^1)
  let y : ℝ^1 := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm (|R| + 1)
  have hyNorm : ‖y‖ = |R| + 1 := by
    simp only [y]
    rw [PiLp.equivOfUnique_symm_apply]
    rw [show uniqueElim (|R| + 1) =
        Function.const (Fin 1) (|R| + 1) by
      funext i
      fin_cases i
      rfl]
    rw [PiLp.norm_toLp_const (by norm_num)]
    norm_num
    positivity
  have hy : y ∉ tsupport u := by
    intro hySupport
    have hyBall := hR hySupport
    rw [Metric.mem_closedBall, dist_zero_right, hyNorm] at hyBall
    linarith [le_abs_self R]
  have hy0 : u y = 0 :=
    image_eq_zero_of_notMem_tsupport hy
  have hderiv :
      MemLp (fun z ↦ (∂[0] u) z)
        1 (volume : Measure (ℝ^1)) := by
    have hsmooth :
        Continuous (fun z ↦ (∂[0] u) z) := by
      have happly : Continuous (fun z : ℝ^1 ↦
          (fderiv ℝ u z : ℝ^1 →L[ℝ] ℝ)
            (EuclideanSpace.single 0 (1 : ℝ))) :=
        (hu.continuous_fderiv_apply (hn := by simp)).comp
          (continuous_id.prodMk continuous_const)
      simpa [partialDeriv] using happly
    exact hsmooth.memLp_of_hasCompactSupport
      (hcompact.fderiv_apply
        (𝕜 := ℝ) (v := EuclideanSpace.single 0 (1 : ℝ)))
  have hweak :
      HasWeakDerivativeOn (n := 1) Set.univ [0] u
        (fun z ↦ (∂[0] u) z) :=
    WeakChangeOfVariables.hasWeakDerivativeOn_of_contDiff_one
      (hu.of_le (by simp))
  have hbound :=
    norm_sub_le_eLpNorm_weakDerivative_one_toReal
      u (fun z ↦ (∂[0] u) z)
      hu.continuous hderiv hweak x y
  simpa [hy0] using hbound

/-- A compactly supported continuous function, bundled in the bounded
continuous-function space. -/
def compactSupportToBoundedContinuousFunction
    (u : ℝ^1 → ℝ) (hu : Continuous u)
    (hcompact : HasCompactSupport u) :
    (ℝ^1) →ᵇ ℝ :=
  ofCompactSupport u hu hcompact

/-- Evaluating the bundled bounded continuous function is evaluating `u`. -/
@[simp]
theorem compactSupportToBoundedContinuousFunction_apply
    (u : ℝ^1 → ℝ) (hu : Continuous u)
    (hcompact : HasCompactSupport u) (x : ℝ^1) :
    compactSupportToBoundedContinuousFunction u hu hcompact x = u x :=
  rfl

/-- Uniform norm bound for the smooth compactly supported lift. -/
theorem norm_compactSupportToBoundedContinuousFunction_le
    (u : ℝ^1 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcompact : HasCompactSupport u) :
    ‖compactSupportToBoundedContinuousFunction
        u hu.continuous hcompact‖ ≤
      (eLpNorm (fun z ↦ (∂[0] u) z)
        1 volume).toReal := by
  apply (BoundedContinuousFunction.norm_le ENNReal.toReal_nonneg).2
  intro x
  exact norm_apply_le_eLpNorm_partialDeriv_one_toReal
    u hu hcompact x

/-- The smooth endpoint lift is a contraction for the finite `PiLp`
`W^{1,1}` norm. -/
theorem norm_compactSupportToBoundedContinuousFunction_le_W11
    (u : ℝ^1 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcompact : HasCompactSupport u) :
    ‖compactSupportToBoundedContinuousFunction
        u hu.continuous hcompact‖ ≤
      ‖GraphSpace.mkWkpSpaceOnOfContDiff
        (n := 1) (k := 1) (p := (1 : ENNReal))
        (Ω := (Set.univ : Set (ℝ^1)))
        u hu hcompact‖ := by
  let U : W^{1,1}(ℝ^1) :=
    GraphSpace.mkWkpSpaceOnOfContDiff
      (n := 1) (k := 1) (p := (1 : ENNReal))
      (Ω := (Set.univ : Set (ℝ^1)))
      u hu hcompact
  calc
    ‖compactSupportToBoundedContinuousFunction
        u hu.continuous hcompact‖
        ≤ (eLpNorm (fun z ↦ (∂[0] u) z)
            1 volume).toReal :=
      norm_compactSupportToBoundedContinuousFunction_le
        u hu hcompact
    _ =
        ‖((GraphSpace.mkWkpSpaceOnOfContDiff
              (n := 1) (k := 1) (p := (1 : ENNReal))
              (Ω := (Set.univ : Set (ℝ^1)))
              u hu hcompact :
            GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.singleDerivIndex 1 0))‖ := by
      symm
      simpa [GraphSpace.singleDerivIndex_toList,
        iteratedPartialDeriv] using
        GraphSpace.norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal
          (n := 1) (k := 1) (p := (1 : ENNReal)) (Ω := Set.univ)
          u hu hcompact
          (GraphSpace.singleDerivIndex 1 0)
    _ ≤ ‖U‖ := by
      simpa [U] using
        PiLp.norm_apply_le
          (U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.singleDerivIndex 1 0)

private theorem compactSupportToBoundedContinuousFunction_sub
    (u v : ℝ^1 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hcompactU : HasCompactSupport u)
    (hcompactV : HasCompactSupport v) :
    compactSupportToBoundedContinuousFunction
        (fun x ↦ u x - v x) (hu.sub hv).continuous
        (hcompactU.sub hcompactV) =
      compactSupportToBoundedContinuousFunction
          u hu.continuous hcompactU -
        compactSupportToBoundedContinuousFunction
          v hv.continuous hcompactV := by
  ext x
  rfl

private theorem dist_compactSupportToBoundedContinuousFunction_le
    (u v : ℝ^1 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hcompactU : HasCompactSupport u)
    (hcompactV : HasCompactSupport v) :
    dist
        (compactSupportToBoundedContinuousFunction
          u hu.continuous hcompactU)
        (compactSupportToBoundedContinuousFunction
          v hv.continuous hcompactV) ≤
      dist
        (GraphSpace.mkWkpSpaceOnOfContDiff
          (n := 1) (k := 1) (p := (1 : ENNReal))
          (Ω := (Set.univ : Set (ℝ^1)))
          u hu hcompactU)
        (GraphSpace.mkWkpSpaceOnOfContDiff
          (n := 1) (k := 1) (p := (1 : ENNReal))
          (Ω := (Set.univ : Set (ℝ^1)))
          v hv hcompactV) := by
  rw [dist_eq_norm, dist_eq_norm,
    ← compactSupportToBoundedContinuousFunction_sub
      u v hu hv hcompactU hcompactV,
    ← GraphSpace.mkWkpSpaceOnOfContDiff_sub
      u v hu hv hcompactU hcompactV]
  exact norm_compactSupportToBoundedContinuousFunction_le_W11
    (fun x ↦ u x - v x) (hu.sub hv)
    (hcompactU.sub hcompactV)

/-- Every global one-dimensional `W^{1,1}` class has a bounded continuous
representative agreeing almost everywhere with its base coordinate. The
representative's uniform norm is at most the Sobolev norm. -/
theorem exists_boundedContinuousRepresentative
    (U : W^{1,1}(ℝ^1)) :
    ∃ F : (ℝ^1) →ᵇ ℝ,
      (fun x ↦ F x) =ᵐ[volume]
        (((U : GraphSpace.WkpAmbientOn 1 1 1 Set.univ)
          (GraphSpace.baseIndex 1 1) :
          GraphSpace.DerivLp 1 1 Set.univ) :
          ℝ^1 → ℝ) ∧
      ‖F‖ ≤ ‖U‖ := by
  simpa using
    (GraphSpace.exists_boundedRepresentative_of_smoothCore
      (n := 1) (p := (1 : ENNReal))
      (Approximation.standardMollifier 1)
      (by norm_num) 1
      (fun u hu hcompact ↦
        compactSupportToBoundedContinuousFunction
          u hu.continuous hcompact)
      (fun x ↦ BoundedContinuousFunction.evalCLM (𝕜 := ℝ) x)
      1 (by norm_num)
      (by intros; rfl)
      (fun u v hu hv hcompactU hcompactV ↦ by
        simpa using
          dist_compactSupportToBoundedContinuousFunction_le
            u v hu hv hcompactU hcompactV)
      (fun u hu hcompact ↦ by
        simpa using
          norm_compactSupportToBoundedContinuousFunction_le_W11
            u hu hcompact)
      U)

/-- The unique bounded continuous representative of a global
one-dimensional `W^{1,1}` element. -/
noncomputable def boundedContinuousRepresentative
    (U : W^{1,1}(ℝ^1)) :
    (ℝ^1) →ᵇ ℝ :=
  Classical.choose (exists_boundedContinuousRepresentative U)

/-- The selected continuous representative agrees almost everywhere with the
Sobolev base coordinate. -/
theorem boundedContinuousRepresentative_ae
    (U : W^{1,1}(ℝ^1)) :
    (fun x ↦ boundedContinuousRepresentative U x) =ᵐ[volume]
      GraphSpace.baseRepresentative U :=
  (Classical.choose_spec
    (exists_boundedContinuousRepresentative U)).1

/-- Uniform norm estimate for the selected continuous representative. -/
theorem norm_boundedContinuousRepresentative_le
    (U : W^{1,1}(ℝ^1)) :
    ‖boundedContinuousRepresentative U‖ ≤ ‖U‖ :=
  (Classical.choose_spec
    (exists_boundedContinuousRepresentative U)).2

/-- The selected endpoint representative is additive. -/
theorem boundedContinuousRepresentative_add
    (U V : W^{1,1}(ℝ^1)) :
    boundedContinuousRepresentative (U + V) =
      boundedContinuousRepresentative U +
        boundedContinuousRepresentative V := by
  have hbase := GraphSpace.baseRepresentative_add_ae U V
  simp only [domainMeasure, Measure.restrict_univ] at hbase
  apply BoundedContinuousFunction.ext
  exact congrFun (map_add_of_continuous_ae_eq
    (fun W ↦ (boundedContinuousRepresentative W).continuous)
    (boundedContinuousRepresentative_ae) hbase)

/-- The selected endpoint representative respects scalar multiplication. -/
theorem boundedContinuousRepresentative_smul
    (c : ℝ) (U : W^{1,1}(ℝ^1)) :
    boundedContinuousRepresentative (c • U) =
      c • boundedContinuousRepresentative U := by
  have hbase := GraphSpace.baseRepresentative_smul_ae c U
  simp only [domainMeasure, Measure.restrict_univ] at hbase
  apply BoundedContinuousFunction.ext
  exact congrFun (map_smul_of_continuous_ae_eq
    (fun W ↦ (boundedContinuousRepresentative W).continuous)
    (boundedContinuousRepresentative_ae) hbase)

/-- The critical embedding `W^{1,1}(ℝ) → C⁰_b(ℝ)` as a linear map, before the
operator norm bound is attached. -/
noncomputable def criticalEmbeddingLinearMap :
    W^{1,1}(ℝ^1) →ₗ[ℝ] ((ℝ^1) →ᵇ ℝ) where
  toFun := boundedContinuousRepresentative
  map_add' := boundedContinuousRepresentative_add
  map_smul' := boundedContinuousRepresentative_smul

/-- The global one-dimensional critical Sobolev embedding
`W^{1,1}(ℝ) → C⁰_b(ℝ)`. -/
noncomputable def criticalEmbedding :
    W^{1,1}(ℝ^1) →L[ℝ] ((ℝ^1) →ᵇ ℝ) :=
  LinearMap.mkContinuous
    criticalEmbeddingLinearMap 1 (by
      intro U
      change ‖boundedContinuousRepresentative U‖ ≤ 1 * ‖U‖
      simpa using norm_boundedContinuousRepresentative_le U)

/-- As a function, the critical embedding is `boundedContinuousRepresentative`; the continuous
linear map only adds linearity and the norm bound. -/
@[simp]
theorem criticalEmbedding_apply
    (U : W^{1,1}(ℝ^1)) :
    criticalEmbedding U = boundedContinuousRepresentative U :=
  rfl

/-- The global critical embedding agrees almost everywhere with the Sobolev
base coordinate. -/
theorem criticalEmbedding_ae
    (U : W^{1,1}(ℝ^1)) :
    (fun x ↦ criticalEmbedding U x) =ᵐ[volume]
      GraphSpace.baseRepresentative U :=
  boundedContinuousRepresentative_ae U

/-- Restriction of a bounded continuous function on `ℝ` to a subset `Ω`, as a
continuous linear map of norm at most one. -/
noncomputable def restrictCLM (Ω : Set (ℝ^1)) :
    ((ℝ^1) →ᵇ ℝ) →L[ℝ] (Ω →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.domRestrict Ω
      map_add' := by
        intro f g
        ext x
        rfl
      map_smul' := by
        intro c f
        ext x
        rfl }
    1 (by
      intro f
      change ‖f.domRestrict Ω‖ ≤ 1 * ‖f‖
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
      intro x
      exact BoundedContinuousFunction.norm_coe_le_norm f x)

/-- The one-dimensional critical embedding on a domain carrying the
operational `C¹` extension atlas. -/
noncomputable def criticalEmbeddingOn
    {Ω : Set (ℝ^1)}
    [Boundary.C1ExtensionAtlas 1 Ω] :
    W^{1,1}(Ω) →L[ℝ] (Ω →ᵇ ℝ) :=
  (restrictCLM Ω).comp
    (criticalEmbedding.comp
      (Extension.C1.extensionCLM
        (n := 1) (p := (1 : ENNReal)) (Ω := Ω)))

/-- On a domain, the embedding is the global embedding of the extension `E U`, evaluated at
points of `Ω`. -/
@[simp]
theorem criticalEmbeddingOn_apply
    {Ω : Set (ℝ^1)}
    [Boundary.C1ExtensionAtlas 1 Ω]
    (U : W^{1,1}(Ω))
    (x : Ω) :
    criticalEmbeddingOn U x =
      criticalEmbedding
        (Extension.C1.extensionCLM
          (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U) x :=
  rfl

/-- The domain critical embedding agrees almost everywhere with the original
Sobolev base coordinate. -/
theorem criticalEmbeddingOn_ae
    {Ω : Set (ℝ^1)}
    [Boundary.C1ExtensionAtlas 1 Ω]
    (U : W^{1,1}(Ω)) :
    (fun x ↦
      criticalEmbedding
        (Extension.C1.extensionCLM
          (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U) x) =ᵐ[
      domainMeasure 1 Ω]
        (((U : GraphSpace.WkpAmbientOn 1 1 1 Ω)
          (GraphSpace.baseIndex 1 1) :
          GraphSpace.DerivLp 1 1 Ω) :
          ℝ^1 → ℝ) := by
  have hglobal :=
    criticalEmbedding_ae
      (Extension.C1.extensionCLM
        (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U)
  have hglobalΩ :=
    MeasureTheory.ae_restrict_of_ae (s := Ω) hglobal
  filter_upwards
    [hglobalΩ,
      Extension.C1.extensionCLM_agree_ae
        (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U] with x hx hE
  exact hx.trans hE

/-- Explicit operator-norm estimate for the domain critical embedding. -/
theorem norm_criticalEmbeddingOn_le
    {Ω : Set (ℝ^1)}
    [Boundary.C1ExtensionAtlas 1 Ω]
    (U : W^{1,1}(Ω)) :
    ‖criticalEmbeddingOn U‖ ≤
      ‖Extension.C1.extensionCLM
        (n := 1) (p := (1 : ENNReal)) (Ω := Ω)‖ * ‖U‖ := by
  calc
    ‖criticalEmbeddingOn U‖
        ≤ ‖criticalEmbedding
            (Extension.C1.extensionCLM
              (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U)‖ := by
      apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
      intro x
      exact BoundedContinuousFunction.norm_coe_le_norm
        (criticalEmbedding
          (Extension.C1.extensionCLM
            (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U))
        (x : ℝ^1)
    _ ≤ ‖Extension.C1.extensionCLM
          (n := 1) (p := (1 : ENNReal)) (Ω := Ω) U‖ :=
      norm_boundedContinuousRepresentative_le _
    _ ≤ ‖Extension.C1.extensionCLM
          (n := 1) (p := (1 : ENNReal)) (Ω := Ω)‖ * ‖U‖ :=
      (Extension.C1.extensionCLM
        (n := 1) (p := (1 : ENNReal)) (Ω := Ω)).le_opNorm U

end CriticalOneDimensional
end SobolevSpace

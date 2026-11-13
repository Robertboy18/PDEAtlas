/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.WkpExtensionByZero
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Zero extension of `H¹₀`

The zero extension of an arbitrary `H¹(Ω)` function can create a boundary measure. It is valid on
`H¹₀(Ω)`, because that space is the `H¹` closure of smooth functions compactly supported inside `Ω`.
The generic construction in `WkpExtensionByZero` passes the weak derivative identities through this
closure. We state its `H¹` specialization as a linear isometry and prove the extension identities
along inclusions of open domains.

The zero extension acts coordinatewise on the derivative bundle: the function
and each first weak derivative are extended by zero separately, and the weak
derivative identities on `ℝ^n` are inherited by closure from the dense
subspace of compactly supported smooth functions, for which they hold
literally. The `L²` norm of every coordinate is preserved, so the map is an
isometry. The same construction, followed by restriction, gives zero
extension `H¹₀(V) → H¹₀(Ω)` along an inclusion of open sets `V ⊆ Ω`; these
maps are isometries, restriction is a left inverse, and they compose
functorially.

## Main results

* `zeroExtendH10`, `zeroExtendH10ₗᵢ`: zero extension `H¹₀(Ω) → H¹(ℝ^n)` as a bounded
  operator and as a linear isometry, with `norm_zeroExtendH10` and
  `zeroExtendH10_injective`.
* `zeroExtendH10_coordinate_apply_ae`: every derivative coordinate of the extension is the
  pointwise zero extension of the corresponding coordinate of `u`.
* `zeroExtendH10ToSuperset`, `zeroExtendH10ToSupersetₗᵢ`: zero extension `H¹₀(V) → H¹₀(Ω)`
  for open `V ⊆ Ω`, with `norm_zeroExtendH10ToSuperset`, `restrict_zeroExtendH10ToSuperset`
  (restriction is a left inverse), `zeroExtendH10ToSuperset_self`, and
  `zeroExtendH10ToSuperset_comp` (functoriality along `U ⊆ V ⊆ Ω`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for the extension by zero of functions in `W^{1,p}_0(Ω)`, whose weak
  derivatives are the zero extensions of those of `u`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, for the definition of `W^{1,p}_0(U)` as the
  closure of `C_c^∞(U)` in `W^{1,p}(U)`, and §5.5, Theorem 2, pp. 273-275, which identifies it, for
  bounded `U` with `C¹` boundary and `1 ≤ p < ∞`, with the functions of trace zero.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace
namespace GraphSpace
namespace ZeroTrace

open Set MeasureTheory Function
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}


/-- Continuous zero extension from `H¹₀(Ω)` into global `H¹(ℝ^n)`. -/
noncomputable def zeroExtendH10 (hΩmeas : MeasurableSet Ω) :
    H¹₀(Ω) →L[ℝ] H¹(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((zeroExtendAmbient (n := n) (Ω := Ω) hΩmeas).comp
      ((Submodule.subtypeL (wkpSubmoduleOn n 1 2 Ω)).comp
        (Submodule.subtypeL
          ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule))))
    (wkpSubmoduleOn n 1 2 (Set.univ : Set (ℝ^n)))
    (fun u ↦ zeroExtendAmbient_mem_globalWkp (n := n) (Ω := Ω) hΩmeas u)

/-- Zero extension of a compactly supported smooth function is the same
global smooth function, bundled in `H¹(ℝ^n)`. -/
theorem zeroExtendH10_testFunction_eq
    (hΩmeas : MeasurableSet Ω) (φΩ : TestFunctionOn n Ω) :
    zeroExtendH10 (n := n) (Ω := Ω) hΩmeas
        (testFunctionToH10 (n := n) (Ω := Ω) φΩ) =
      testFunctionToH1 (n := n) (Ω := Set.univ)
        (⟨φΩ.1, subset_univ _⟩ : TestFunctionOn n Set.univ) := by
  apply Subtype.ext
  exact zeroExtendAmbient_testFunction_eq (n := n) (Ω := Ω) hΩmeas φΩ

/-- Coordinatewise zero extension is an isometry from `H¹₀(Ω)` into global
`H¹(ℝ^n)`. -/
theorem norm_zeroExtendH10
    (hΩmeas : MeasurableSet Ω) (u : H¹₀(Ω)) :
    ‖zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u‖ = ‖u‖ := by
  exact norm_zeroExtendAmbient (n := n) (k := 1) (p := 2) hΩmeas
    ((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)

/-- Zero extension from `H¹₀(Ω)` to global `H¹(ℝ^n)` as a linear isometry. -/
noncomputable def zeroExtendH10ₗᵢ (hΩmeas : MeasurableSet Ω) :
    H¹₀(Ω) →ₗᵢ[ℝ] H¹(ℝ^n) where
  toLinearMap := (zeroExtendH10 (n := n) (Ω := Ω) hΩmeas).toLinearMap
  norm_map' := norm_zeroExtendH10 (n := n) (Ω := Ω) hΩmeas

/-- The bundled isometry evaluates to the zero-extension map from `H¹₀(Ω)` to global `H¹`. -/
@[simp] theorem zeroExtendH10ₗᵢ_apply
    (hΩmeas : MeasurableSet Ω) (u : H¹₀(Ω)) :
    zeroExtendH10ₗᵢ (n := n) (Ω := Ω) hΩmeas u =
      zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u :=
  rfl

/-- Zero extension from `H¹₀(Ω)` to global `H¹(ℝ^n)` is injective. -/
theorem zeroExtendH10_injective (hΩmeas : MeasurableSet Ω) :
    Function.Injective (zeroExtendH10 (n := n) (Ω := Ω) hΩmeas) :=
  (zeroExtendH10ₗᵢ (n := n) (Ω := Ω) hΩmeas).injective

/-- Forgetting the global `H¹` subtype reveals the coordinatewise zero-extension bundle. -/
@[simp] theorem zeroExtendH10_apply_coe
    (hΩmeas : MeasurableSet Ω) (u : H¹₀(Ω)) :
    ((zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) =
      zeroExtendAmbient (n := n) (Ω := Ω) hΩmeas
        ((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) :=
  rfl

/-- Every derivative coordinate of the global `H¹` object is represented by
the literal zero extension of the corresponding `H¹₀(Ω)` coordinate. -/
theorem zeroExtendH10_coordinate_apply_ae
    (hΩmeas : MeasurableSet Ω) (u : H¹₀(Ω))
    (a : DerivIndex n 1) :
    ((((zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) a : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume]
        Ω.indicator fun x ↦
          ((((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) a :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
  simpa [zeroExtendH10_apply_coe, zeroExtendAmbient_apply,
    Extension.Lp.extensionByZero, domainMeasure] using
    (Extension.Lp.zeroExtendLp_apply_ae
      (n := n) (p := 2) (Ω := Ω) hΩmeas
      (((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) a))

/-- Extend an `H¹₀(V)` function to the whole space by zero, then restrict it
to the open set `Ω`. No inclusion between `V` and `Ω` is required. -/
noncomputable def zeroExtendH10ToSupersetH1
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω) :
    H¹₀(V) →L[ℝ] H¹(Ω) :=
  (restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω)).comp
    (zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet)

/-- On a smooth test function supported in `V ⊆ Ω`, zero extension to `Ω`
is the same smooth test function regarded as an element of `H¹(Ω)`. -/
private theorem zeroExtendH10ToSupersetH1_testFunction_eq
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (φV : TestFunctionOn n V) :
    zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen
        (testFunctionToH10 (n := n) (Ω := V) φV) =
      testFunctionToH1 (n := n) (Ω := Ω)
        (⟨φV.1, φV.2.trans hVΩ⟩ : TestFunctionOn n Ω) := by
  change restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
      (subset_univ Ω)
      (zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet
        (testFunctionToH10 (n := n) (Ω := V) φV)) =
    testFunctionToH1 (n := n) (Ω := Ω)
      (⟨φV.1, φV.2.trans hVΩ⟩ : TestFunctionOn n Ω)
  rw [zeroExtendH10_testFunction_eq
    (n := n) (Ω := V) hVopen.measurableSet φV]
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  have hres := restrictCLM_apply_ae
    (n := n) (k := 1) (p := 2) hΩopen.measurableSet
    (subset_univ Ω)
    (testFunctionToH1 (n := n) (Ω := Set.univ)
      (⟨φV.1, subset_univ _⟩ : TestFunctionOn n Set.univ))
    (baseIndex n 1)
  have hglobal := mkWkpSpaceOnOfContDiff_apply_ae
    (n := n) (k := 1) (p := 2) (Ω := (Set.univ : Set (ℝ^n)))
    φV.1.toFun φV.1.contDiff φV.1.hasCompactSupport (baseIndex n 1)
  have hlocal := mkWkpSpaceOnOfContDiff_apply_ae
    (n := n) (k := 1) (p := 2) (Ω := Ω)
    φV.1.toFun φV.1.contDiff φV.1.hasCompactSupport (baseIndex n 1)
  have hmeasure :
      domainMeasure n Ω ≤ domainMeasure n (Set.univ : Set (ℝ^n)) :=
    MeasureTheory.Measure.restrict_mono (subset_univ Ω) (le_refl _)
  have hglobalΩ := hglobal.filter_mono (MeasureTheory.ae_mono hmeasure)
  exact hres.trans (hglobalΩ.trans hlocal.symm)

/-- Zero extension from `H¹₀(V)` into `H¹(Ω)` lies in `H¹₀(Ω)` when `V ⊆ Ω`. -/
theorem zeroExtendH10ToSupersetH1_mem_H10
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen u ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  let A := zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen
  refine DenseRange.induction_on
    (denseRange_testFunctionToH10Linear
      (n := n) (Ω := V)) u ?_ ?_
  · exact
      (h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'.preimage A.continuous
  · intro φV
    rw [show A (testFunctionToH10Linear (n := n) (Ω := V) φV) =
      testFunctionToH1 (n := n) (Ω := Ω)
        (⟨φV.1, φV.2.trans hVΩ⟩ : TestFunctionOn n Ω) by
      exact zeroExtendH10ToSupersetH1_testFunction_eq
        (n := n) hVopen hΩopen hVΩ φV]
    exact testFunctionToH1_mem_H10
      (n := n) (Ω := Ω)
      (⟨φV.1, φV.2.trans hVΩ⟩ : TestFunctionOn n Ω)

/-- Bounded zero extension along an inclusion of open sets,
`H¹₀(V) → H¹₀(Ω)`. -/
noncomputable def zeroExtendH10ToSuperset
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) :
    H¹₀(V) →L[ℝ]
      H¹₀(Ω) :=
  ContinuousLinearMap.codRestrict
    (zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen)
    (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule
    (zeroExtendH10ToSupersetH1_mem_H10
      (n := n) hVopen hΩopen hVΩ)

/-- Forgetting the zero-trace subtype reveals global zero extension restricted
to the larger open set. -/
@[simp] theorem zeroExtendH10ToSuperset_apply_coe
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    ((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
        H¹₀(Ω)) : H¹(Ω)) =
      zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen u :=
  rfl

/-- Every derivative coordinate of zero extension along `V ⊆ Ω` is the
indicator of `V` times the corresponding coordinate on `V`. -/
theorem zeroExtendH10ToSuperset_coordinate_apply_ae
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V))
    (a : DerivIndex n 1) :
    (((((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
        H¹₀(Ω)) : H¹(Ω)) :
          WkpAmbientOn n 1 2 Ω) a : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        V.indicator fun x ↦
          ((((u : H¹(V)) : WkpAmbientOn n 1 2 V) a :
            DerivLp n 2 V) : ℝ^n → ℝ) x := by
  have hres := restrictCLM_apply_ae
    (n := n) (k := 1) (p := 2) hΩopen.measurableSet
    (subset_univ Ω)
    (zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet u) a
  have hzero := zeroExtendH10_coordinate_apply_ae
    (n := n) (Ω := V) hVopen.measurableSet u a
  have hmeasure : domainMeasure n Ω ≤ MeasureTheory.volume := by
    simpa [domainMeasure] using
      (MeasureTheory.Measure.restrict_le_self :
        (MeasureTheory.volume : Measure (ℝ^n)).restrict Ω ≤ MeasureTheory.volume)
  have hzeroΩ := hzero.filter_mono (MeasureTheory.ae_mono hmeasure)
  simpa [zeroExtendH10ToSuperset_apply_coe,
    zeroExtendH10ToSupersetH1] using hres.trans hzeroΩ

/-- Pairing against a coordinate of zero extension from `V` to `Ω` is the
same as pairing the restricted field on `V`. -/
theorem inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (w : DerivLp n 2 Ω)
    (u : H¹₀(V)) (a : DerivIndex n 1) :
    inner ℝ w
        (((((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
            H¹₀(Ω)) : H¹(Ω)) :
              WkpAmbientOn n 1 2 Ω) a : DerivLp n 2 Ω)) =
      inner ℝ
        (restrictDerivLp (n := n) (p := 2) hVΩ w)
        ((((u : H¹(V)) : WkpAmbientOn n 1 2 V) a :
          DerivLp n 2 V)) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hzero := zeroExtendH10ToSuperset_coordinate_apply_ae
    (n := n) hVopen hΩopen hVΩ u a
  have hrestrict := restrictDerivLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) hVΩ w
  let G : ℝ^n → ℝ := fun x ↦
    inner ℝ (w x)
      (((((u : H¹(V)) : WkpAmbientOn n 1 2 V) a :
        DerivLp n 2 V)) x)
  calc
    (∫ x, inner ℝ (w x)
        (((((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
            H¹₀(Ω)) : H¹(Ω)) :
              WkpAmbientOn n 1 2 Ω) a : DerivLp n 2 Ω) x)
        ∂domainMeasure n Ω) =
        ∫ x, V.indicator G x ∂domainMeasure n Ω := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hzero] with x hxzero
      rw [hxzero]
      by_cases hxV : x ∈ V
      · simp [G, hxV]
      · simp [G, hxV]
    _ = ∫ x, G x ∂(domainMeasure n Ω).restrict V :=
      MeasureTheory.integral_indicator hVopen.measurableSet
    _ = ∫ x, G x ∂domainMeasure n V := by
      congr 1
      rw [domainMeasure, Measure.restrict_restrict hVopen.measurableSet]
      congr 1
      exact Set.inter_eq_left.2 hVΩ
    _ = ∫ x, inner ℝ
          ((restrictDerivLp (n := n) (p := 2)
            hVΩ w : DerivLp n 2 V) x)
          (((((u : H¹(V)) : WkpAmbientOn n 1 2 V) a :
            DerivLp n 2 V)) x)
        ∂domainMeasure n V := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hrestrict] with x hxrestrict
      rw [hxrestrict]

/-- Zero extension along `V ⊆ Ω` sends a smooth test function to the same
test function with its support viewed inside `Ω`. -/
@[simp] theorem zeroExtendH10ToSuperset_testFunction_eq
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (φV : TestFunctionOn n V) :
    zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ
        (testFunctionToH10 (n := n) (Ω := V) φV) =
      testFunctionToH10 (n := n) (Ω := Ω)
        (⟨φV.1, φV.2.trans hVΩ⟩ : TestFunctionOn n Ω) := by
  apply Subtype.ext
  exact zeroExtendH10ToSupersetH1_testFunction_eq
    (n := n) hVopen hΩopen hVΩ φV

/-- Restriction is a left inverse to zero extension on `H¹₀(Ω)`. -/
@[simp]
theorem restrict_zeroExtendH10
    (hΩopen : IsOpen Ω) (u : H¹₀(Ω)) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω)
        (zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet u) =
      (u : H¹(Ω)) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  change restrictDerivLp (subset_univ Ω)
      (wkpCoordinateCLM a (zeroExtendWkp0 hΩopen.measurableSet u)) =
    wkpCoordinateCLM a (u : W^{1,2}(Ω))
  exact restrict_zeroExtendWkp0_coordinate hΩopen.measurableSet u a

/-- Restriction composed with zero extension is the canonical inclusion
`H¹₀(Ω) → H¹(Ω)`. -/
@[simp] theorem restrictCLM_comp_zeroExtendH10
    (hΩopen : IsOpen Ω) :
    (restrictCLM (n := n) (k := 1) (p := 2)
      hΩopen.measurableSet (subset_univ Ω)).comp
        (zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet) =
      h10SubtypeL (n := n) (Ω := Ω) := by
  apply ContinuousLinearMap.ext
  intro u
  exact restrict_zeroExtendH10 (n := n) (Ω := Ω) hΩopen u

/-- Restricting the `H¹(Ω)` zero extension along `V ⊆ Ω` back to `V`
recovers the canonical inclusion `H¹₀(V) → H¹(V)`. -/
@[simp] theorem restrict_zeroExtendH10ToSupersetH1
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    restrictCLM (n := n) (k := 1) (p := 2)
        hVopen.measurableSet hVΩ
        (zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen u) =
      (u : H¹(V)) := by
  calc
    restrictCLM (n := n) (k := 1) (p := 2)
        hVopen.measurableSet hVΩ
        (zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen u) =
      restrictCLM (n := n) (k := 1) (p := 2)
        hVopen.measurableSet (subset_univ V)
        (zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet u) := by
      have hcomp := congrArg
        (fun T : H¹(ℝ^n) →L[ℝ] H¹(V) ↦
          T (zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet u))
        (restrictCLM_comp (n := n) (k := 1) (p := 2)
          hVopen.measurableSet hΩopen.measurableSet hVΩ (subset_univ Ω))
      simpa only [ContinuousLinearMap.comp_apply,
        zeroExtendH10ToSupersetH1] using hcomp
    _ = (u : H¹(V)) :=
      restrict_zeroExtendH10 (n := n) (Ω := V) hVopen u

/-- Restricting zero extension in `H¹₀(Ω)` along `V ⊆ Ω` back to `V`
recovers the canonical inclusion `H¹₀(V) → H¹(V)`. -/
theorem restrict_zeroExtendH10ToSuperset
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    restrictCLM (n := n) (k := 1) (p := 2)
        hVopen.measurableSet hVΩ
        ((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
          H¹₀(Ω)) : H¹(Ω)) =
      (u : H¹(V)) := by
  rw [zeroExtendH10ToSuperset_apply_coe]
  exact restrict_zeroExtendH10ToSupersetH1
    (n := n) hVopen hΩopen hVΩ u

/-- Zero extension along an inclusion of open sets preserves the `H¹₀` norm. -/
theorem norm_zeroExtendH10ToSuperset
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    ‖zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u‖ = ‖u‖ := by
  apply le_antisymm
  · change
      ‖((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
        H¹₀(Ω)) : H¹(Ω))‖ ≤ ‖u‖
    rw [zeroExtendH10ToSuperset_apply_coe]
    calc
      ‖zeroExtendH10ToSupersetH1 (n := n) hVopen hΩopen u‖ ≤
          ‖zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet u‖ :=
        norm_restrictCLM_apply_le
          (n := n) (k := 1) (p := 2) (Ω := Ω) (Ωbig := Set.univ)
          hΩopen.measurableSet (subset_univ Ω) _
      _ = ‖u‖ :=
        norm_zeroExtendH10 (n := n) (Ω := V) hVopen.measurableSet u
  · have hle := norm_restrictCLM_apply_le
      (n := n) (k := 1) (p := 2) (Ω := V) (Ωbig := Ω)
      hVopen.measurableSet hVΩ
      ((zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :
        H¹₀(Ω)) : H¹(Ω))
    rw [restrict_zeroExtendH10ToSuperset
      (n := n) hVopen hΩopen hVΩ u] at hle
    exact hle

/-- Zero extension along `V ⊆ Ω` as a linear isometry
`H¹₀(V) → H¹₀(Ω)`. -/
noncomputable def zeroExtendH10ToSupersetₗᵢ
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) :
    H¹₀(V) →ₗᵢ[ℝ]
      H¹₀(Ω) where
  toLinearMap :=
    (zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ).toLinearMap
  norm_map' := norm_zeroExtendH10ToSuperset
    (n := n) hVopen hΩopen hVΩ

/-- The bundled isometry along `V ⊆ Ω` evaluates to zero extension from `H¹₀(V)` to `H¹₀(Ω)`. -/
@[simp] theorem zeroExtendH10ToSupersetₗᵢ_apply
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    zeroExtendH10ToSupersetₗᵢ (n := n) hVopen hΩopen hVΩ u =
      zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ u :=
  rfl

/-- Zero extension along an inclusion of open sets is injective. -/
theorem zeroExtendH10ToSuperset_injective
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) :
    Function.Injective
      (zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ) :=
  (zeroExtendH10ToSupersetₗᵢ (n := n) hVopen hΩopen hVΩ).injective

/-- Restriction composed with zero extension along `V ⊆ Ω` is the
canonical inclusion `H¹₀(V) → H¹(V)`. -/
@[simp] theorem restrictCLM_comp_zeroExtendH10ToSuperset
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) :
    (restrictCLM (n := n) (k := 1) (p := 2)
      hVopen.measurableSet hVΩ).comp
        ((h10SubtypeL (n := n) (Ω := Ω)).comp
          (zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ)) =
      h10SubtypeL (n := n) (Ω := V) := by
  apply ContinuousLinearMap.ext
  intro u
  exact restrict_zeroExtendH10ToSuperset
    (n := n) hVopen hΩopen hVΩ u

/-- Zero extension along the identity inclusion is the identity map. -/
@[simp] theorem zeroExtendH10ToSuperset_self
    (hΩopen : IsOpen Ω) :
    zeroExtendH10ToSuperset (n := n) hΩopen hΩopen (Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ (H¹₀(Ω)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change zeroExtendH10ToSupersetH1 (n := n) hΩopen hΩopen u =
    (u : H¹(Ω))
  exact restrict_zeroExtendH10 (n := n) (Ω := Ω) hΩopen u

/-- Zero extension is functorial along a chain of open-set inclusions. -/
@[simp] theorem zeroExtendH10ToSuperset_comp
    {U V : Set (ℝ^n)}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hUV : U ⊆ V) (hVΩ : V ⊆ Ω) :
    (zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ).comp
        (zeroExtendH10ToSuperset (n := n) hUopen hVopen hUV) =
      zeroExtendH10ToSuperset
        (n := n) hUopen hΩopen (hUV.trans hVΩ) := by
  apply ContinuousLinearMap.ext
  intro u
  refine DenseRange.induction_on
    (denseRange_testFunctionToH10Linear
      (n := n) (Ω := U)) u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro φU
    change
      zeroExtendH10ToSuperset (n := n) hVopen hΩopen hVΩ
          (zeroExtendH10ToSuperset (n := n) hUopen hVopen hUV
            (testFunctionToH10
              (n := n) (Ω := U) φU)) =
        zeroExtendH10ToSuperset
          (n := n) hUopen hΩopen (hUV.trans hVΩ)
          (testFunctionToH10
            (n := n) (Ω := U) φU)
    rw [zeroExtendH10ToSuperset_testFunction_eq,
      zeroExtendH10ToSuperset_testFunction_eq,
      zeroExtendH10ToSuperset_testFunction_eq]

end ZeroTrace
end GraphSpace
end SobolevSpace

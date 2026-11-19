/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Measure
public import PDE.FDeriv.Reflection.Local

/-!
# Reflection parity in weighted Sobolev spaces

Let `σ_i` be the reflection `x_i ↦ -x_i` of `ℝ^n`. A function `f` is a reflection eigenfunction
with eigenvalue `c` on a set `s` if `f (σ_i x) = c · f x` for all `x ∈ s`; the cases `c = 1` and
`c = -1` are the even and odd functions. For classical functions this is an exact pointwise
identity. For `L^p` and Sobolev functions it is an identity in Mathlib's `Lp` quotient, expressed
through the pullback isometry `u ↦ u ∘ σ_i` of `L^p(ℝ^n)`, so it does not depend on a
representative.

Differentiating a `C^1` eigenfunction in the reflected coordinate reverses the sign, while a
tangential derivative preserves it. Hence a `C^k` eigenfunction with eigenvalue `c` has iterated
derivative `D^α f` with eigenvalue `c · (-1)^{α_i}`, where `α_i` is the multiplicity of `i` in
`α`. The derivative-row parity predicate `IsDerivativeRowUnderCoordinateReflectionOn` assigns
exactly these signs.

## Main results

* `reflectionEigenfunctionSubmoduleOn`: the submodule of functions with exact parity
  `PDE.Common.IsReflectionEigenfunctionOn` on a set.
* `IsReflectionEigenfunctionOn.classicalDerivativeRow`: the sign rules for the derivative rows of
  classical eigenfunctions, from the derivative rules of `PDE.FDeriv.Reflection.Local`.
* `coordinateReflectionLpLinearIsometry`, `lpReflectionEigenspace`: the pullback isometry of
  whole-space `L^p` and its eigenspaces.
* `sobolevReflectionParitySubmodule`: whole-space Sobolev graph elements each of whose
  coordinates lies in the eigenspace with the sign dictated by its multiplicity.
* `weightedSobolevReflectionParitySubmodule`, `weightedEvenHkSubmodule`,
  `weightedOddHkSubmodule`: the intersection with the weighted-integrability submodule.

## Implementation notes

`sobolevReflectionParitySubmodule` is an intersection over all derivative indices `a`, imposing
the parity of each row as a separate constraint. For Sobolev functions on `ℝ^n` the parity of
the base coordinate already forces the parity of every weak derivative row, by uniqueness of
weak derivatives, so the remaining constraints are redundant; that implication is not proved
here and is not used.

The weighted parity spaces are submodules of the unweighted graph space `WkpSpace n k p`, cut out
by weighted integrability and parity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal Sobolev

namespace SobolevSpace
namespace Weighted

/-! ## Exact parity for classical functions -/

/-- Exact evenness under a coordinate reflection on a set. -/
def IsEvenUnderCoordinateReflectionOn {n : ℕ} (s : Set (ℝ^n))
    (i : Fin n) (f : ℝ^n → ℝ) : Prop :=
  IsReflectionEigenfunctionOn s i 1 f

/-- Exact oddness under a coordinate reflection on a set. -/
def IsOddUnderCoordinateReflectionOn {n : ℕ} (s : Set (ℝ^n))
    (i : Fin n) (f : ℝ^n → ℝ) : Prop :=
  IsReflectionEigenfunctionOn s i (-1) f

/-- The set of functions with a fixed reflection eigenvalue is a linear
subspace. -/
def reflectionEigenfunctionSubmoduleOn {n : ℕ} (s : Set (ℝ^n))
    (i : Fin n) (c : ℝ) : Submodule ℝ (ℝ^n → ℝ) where
  carrier := {f | IsReflectionEigenfunctionOn s i c f}
  zero_mem' := by simp [IsReflectionEigenfunctionOn]
  add_mem' := by
    intro f g hf hg x hx
    simp only [Pi.add_apply]
    rw [hf x hx, hg x hx, mul_add]
  smul_mem' := by
    intro a f hf x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf x hx]
    ring

/-- Exact even functions on `s`, as a submodule. -/
def evenFunctionSubmoduleOn {n : ℕ} (s : Set (ℝ^n)) (i : Fin n) :
    Submodule ℝ (ℝ^n → ℝ) :=
  reflectionEigenfunctionSubmoduleOn s i 1

/-- Exact odd functions on `s`, as a submodule. -/
def oddFunctionSubmoduleOn {n : ℕ} (s : Set (ℝ^n)) (i : Fin n) :
    Submodule ℝ (ℝ^n → ℝ) :=
  reflectionEigenfunctionSubmoduleOn s i (-1)

/-- Membership in the even submodule is exact evenness on `s`. -/
@[simp] theorem mem_evenFunctionSubmoduleOn_iff {n : ℕ}
    {s : Set (ℝ^n)} {i : Fin n} {f : ℝ^n → ℝ} :
    f ∈ evenFunctionSubmoduleOn s i ↔
      IsEvenUnderCoordinateReflectionOn s i f :=
  Iff.rfl

/-- Membership in the odd submodule is exact oddness on `s`. -/
@[simp] theorem mem_oddFunctionSubmoduleOn_iff {n : ℕ}
    {s : Set (ℝ^n)} {i : Fin n} {f : ℝ^n → ℝ} :
    f ∈ oddFunctionSubmoduleOn s i ↔
      IsOddUnderCoordinateReflectionOn s i f :=
  Iff.rfl

/-- On `univ`, the set-local definition is the global evenness predicate. -/
theorem isEvenUnderCoordinateReflectionOn_univ_iff {n : ℕ}
    {i : Fin n} {f : ℝ^n → ℝ} :
    IsEvenUnderCoordinateReflectionOn Set.univ i f ↔
      PDE.Common.IsEvenUnderCoordinateReflection i f := by
  simp [IsEvenUnderCoordinateReflectionOn, IsReflectionEigenfunctionOn,
    PDE.Common.IsEvenUnderCoordinateReflection]

/-- On `univ`, the set-local definition is the global oddness predicate. -/
theorem isOddUnderCoordinateReflectionOn_univ_iff {n : ℕ}
    {i : Fin n} {f : ℝ^n → ℝ} :
    IsOddUnderCoordinateReflectionOn Set.univ i f ↔
      PDE.Common.IsOddUnderCoordinateReflection i f := by
  simp [IsOddUnderCoordinateReflectionOn, IsReflectionEigenfunctionOn,
    PDE.Common.IsOddUnderCoordinateReflection]

/-! ## Exact parity of derivative rows -/

/-- Exact parity of a symmetric derivative row whose base reflection
eigenvalue is `c`. -/
def IsDerivativeRowUnderCoordinateReflectionOn {n k : ℕ}
    (s : Set (ℝ^n)) (i : Fin n) (c : ℝ)
    (F : GraphSpace.DerivIndex n k → ℝ^n → ℝ) : Prop :=
  ∀ a, IsReflectionEigenfunctionOn s i
    (c * (-1 : ℝ) ^ a.multiplicity i) (F a)

/-- Exact derivative-row parity induced by an even base function. -/
def IsEvenDerivativeRowUnderCoordinateReflectionOn {n k : ℕ}
    (s : Set (ℝ^n)) (i : Fin n)
    (F : GraphSpace.DerivIndex n k → ℝ^n → ℝ) : Prop :=
  IsDerivativeRowUnderCoordinateReflectionOn s i 1 F

/-- Exact derivative-row parity induced by an odd base function. -/
def IsOddDerivativeRowUnderCoordinateReflectionOn {n k : ℕ}
    (s : Set (ℝ^n)) (i : Fin n)
    (F : GraphSpace.DerivIndex n k → ℝ^n → ℝ) : Prop :=
  IsDerivativeRowUnderCoordinateReflectionOn s i (-1) F

/-- Derivative rows with a fixed base parity form a submodule. -/
def derivativeRowSubmoduleOn {n k : ℕ} (s : Set (ℝ^n))
    (i : Fin n) (c : ℝ) :
    Submodule ℝ (GraphSpace.DerivIndex n k → ℝ^n → ℝ) where
  carrier := {F | IsDerivativeRowUnderCoordinateReflectionOn s i c F}
  zero_mem' := by simp [IsDerivativeRowUnderCoordinateReflectionOn,
    IsReflectionEigenfunctionOn]
  add_mem' := by
    intro F G hF hG a
    exact (reflectionEigenfunctionSubmoduleOn s i
      (c * (-1 : ℝ) ^ a.multiplicity i)).add_mem (hF a) (hG a)
  smul_mem' := by
    intro r F hF a
    exact (reflectionEigenfunctionSubmoduleOn s i
      (c * (-1 : ℝ) ^ a.multiplicity i)).smul_mem r (hF a)

/-- Exact derivative rows induced by even base functions, as a submodule. -/
def evenDerivativeRowSubmoduleOn {n k : ℕ} (s : Set (ℝ^n))
    (i : Fin n) :
    Submodule ℝ (GraphSpace.DerivIndex n k → ℝ^n → ℝ) :=
  derivativeRowSubmoduleOn s i 1

/-- Exact derivative rows induced by odd base functions, as a submodule. -/
def oddDerivativeRowSubmoduleOn {n k : ℕ} (s : Set (ℝ^n))
    (i : Fin n) :
    Submodule ℝ (GraphSpace.DerivIndex n k → ℝ^n → ℝ) :=
  derivativeRowSubmoduleOn s i (-1)

/-- Membership in the even derivative-row submodule is the row parity predicate with base
eigenvalue `1`. -/
@[simp] theorem mem_evenDerivativeRowSubmoduleOn_iff {n k : ℕ}
    {s : Set (ℝ^n)} {i : Fin n}
    {F : GraphSpace.DerivIndex n k → ℝ^n → ℝ} :
    F ∈ evenDerivativeRowSubmoduleOn s i ↔
      IsEvenDerivativeRowUnderCoordinateReflectionOn s i F :=
  Iff.rfl

/-- Membership in the odd derivative-row submodule is the row parity predicate with base
eigenvalue `-1`. -/
@[simp] theorem mem_oddDerivativeRowSubmoduleOn_iff {n k : ℕ}
    {s : Set (ℝ^n)} {i : Fin n}
    {F : GraphSpace.DerivIndex n k → ℝ^n → ℝ} :
    F ∈ oddDerivativeRowSubmoduleOn s i ↔
      IsOddDerivativeRowUnderCoordinateReflectionOn s i F :=
  Iff.rfl

/-- The classical derivative row through order `k`. -/
def classicalDerivativeRow {n k : ℕ} (f : ℝ^n → ℝ)
    (a : GraphSpace.DerivIndex n k) : ℝ^n → ℝ :=
  fun x ↦ PDE.iteratedPartialDeriv a.toList f x

/-- The derivative row of a `C^k` reflection eigenfunction has the expected
normal-multiplicity signs. -/
theorem _root_.PDE.Common.IsReflectionEigenfunctionOn.classicalDerivativeRow {n k : ℕ}
    {i : Fin n} {c : ℝ} {f : ℝ^n → ℝ}
    (hf : IsReflectionEigenfunctionOn Set.univ i c f)
    (hcont : ContDiff ℝ k f) :
    IsDerivativeRowUnderCoordinateReflectionOn Set.univ i c
      (classicalDerivativeRow (k := k) f) := by
  intro a
  change IsReflectionEigenfunctionOn Set.univ i
    (c * (-1 : ℝ) ^ a.multiplicity i)
    (fun x ↦ PDE.iteratedPartialDeriv a.toList f x)
  simpa only [GraphSpace.DerivIndex.toList_count] using
    hf.iteratedPartialDeriv isOpen_univ (fun _ _ ↦ mem_univ _) a.toList
      (hcont.of_le (by exact_mod_cast a.toList_length_le)).contDiffOn

/-! ## Parity in `Lp` and Sobolev graph spaces -/

/-- Coordinate reflection preserves the whole-space domain measure. -/
theorem measurePreserving_coordinateReflection_domainMeasure_univ {n : ℕ}
    (i : Fin n) :
    MeasurePreserving (PDE.Common.coordinateReflection i : ℝ^n → ℝ^n)
      (domainMeasure n Set.univ) (domainMeasure n Set.univ) := by
  simpa [domainMeasure] using
    PDE.Common.measurePreserving_coordinateReflection i

/-- Pullback by a coordinate reflection as an isometry of whole-space
`L^p`. -/
def coordinateReflectionLpLinearIsometry {n : ℕ} (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin n) :
    GraphSpace.DerivLp n p Set.univ →ₗᵢ[ℝ]
      GraphSpace.DerivLp n p Set.univ :=
  Lp.compMeasurePreservingₗᵢ ℝ (PDE.Common.coordinateReflection i)
    (measurePreserving_coordinateReflection_domainMeasure_univ i)

/-- The `L^p` eigenspace of coordinate reflection with eigenvalue `c`.

For `c = 1` this is the even subspace, and for `c = -1` it is the odd
subspace. -/
def lpReflectionEigenspace {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) (c : ℝ) :
    Submodule ℝ (GraphSpace.DerivLp n p Set.univ) :=
  LinearMap.ker
    ((coordinateReflectionLpLinearIsometry p i).toLinearMap -
      c • LinearMap.id)

/-- `u` lies in the reflection eigenspace with eigenvalue `c` iff its pullback under the
reflection equals `c • u` in `L^p`. -/
@[simp] theorem mem_lpReflectionEigenspace_iff {n : ℕ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {i : Fin n} {c : ℝ}
    {u : GraphSpace.DerivLp n p Set.univ} :
    u ∈ lpReflectionEigenspace p i c ↔
      coordinateReflectionLpLinearIsometry p i u = c • u := by
  simp [lpReflectionEigenspace, sub_eq_zero]

/-- Extract one Sobolev derivative coordinate as a linear map. -/
def sobolevCoordinateLinearMap {n k : ℕ} (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (a : GraphSpace.DerivIndex n k) :
    W^{k,p}(ℝ^n) →ₗ[ℝ] GraphSpace.DerivLp n p Set.univ :=
  ((ContinuousLinearMap.proj a).comp
      ((PiLp.continuousLinearEquiv (p := p) (𝕜 := ℝ)
        (fun _ : GraphSpace.DerivIndex n k ↦
          GraphSpace.DerivLp n p Set.univ)).toContinuousLinearMap.comp
        (Submodule.subtypeL
          (GraphSpace.wkpSubmoduleOn n k p Set.univ)))).toLinearMap

/-- Whole-space Sobolev graph elements whose coordinate `a` is a reflection eigenfunction in
`L^p` with eigenvalue `c · (-1)^{a_i}`, for every derivative index `a`. The parity of each row is
required separately; the definition does not derive the derivative-row signs from the base
coordinate. -/
def sobolevReflectionParitySubmodule {n k : ℕ} (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin n) (c : ℝ) :
    Submodule ℝ (W^{k,p}(ℝ^n)) :=
  ⨅ a : GraphSpace.DerivIndex n k,
    (lpReflectionEigenspace p i
      (c * (-1 : ℝ) ^ a.multiplicity i)).comap
        (sobolevCoordinateLinearMap p a)

/-- Whole-space Sobolev rows induced by even base functions. -/
def evenSobolevSubmodule {n k : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) : Submodule ℝ (W^{k,p}(ℝ^n)) :=
  sobolevReflectionParitySubmodule p i 1

/-- Whole-space Sobolev rows induced by odd base functions. -/
def oddSobolevSubmodule {n k : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) : Submodule ℝ (W^{k,p}(ℝ^n)) :=
  sobolevReflectionParitySubmodule p i (-1)

/-- A Sobolev graph element has reflection parity `c` iff every coordinate `u_a` satisfies the
eigenvalue equation `u_a ∘ σ_i = c · (-1)^{a_i} · u_a` in `L^p`. -/
@[simp] theorem mem_sobolevReflectionParitySubmodule_iff
    {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {i : Fin n} {c : ℝ}
    {U : W^{k,p}(ℝ^n)} :
    U ∈ sobolevReflectionParitySubmodule p i c ↔
      ∀ a : GraphSpace.DerivIndex n k,
        coordinateReflectionLpLinearIsometry p i
            ((U : GraphSpace.WkpAmbientOn n k p Set.univ) a) =
          (c * (-1 : ℝ) ^ a.multiplicity i) •
            ((U : GraphSpace.WkpAmbientOn n k p Set.univ) a) := by
  simp [sobolevReflectionParitySubmodule, sobolevCoordinateLinearMap]

/-- Reflection parity is preserved by convergence in the Sobolev graph norm. Each row
condition is an equality between two continuous maps into `Lᵖ`. -/
theorem isClosed_sobolevReflectionParitySubmodule
    {n k : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin n) (c : ℝ) :
    IsClosed (sobolevReflectionParitySubmodule (n := n) (k := k) p i c :
      Set (W^{k,p}(ℝ^n))) := by
  have hcoord (a : GraphSpace.DerivIndex n k) :
      Continuous (fun U : W^{k,p}(ℝ^n) ↦
        (U : GraphSpace.WkpAmbientOn n k p Set.univ) a) :=
    (PiLp.proj (𝕜 := ℝ) (p := p)
      (β := fun _ : GraphSpace.DerivIndex n k ↦
        GraphSpace.DerivLp n p Set.univ) a).continuous.comp continuous_subtype_val
  have hclosed (a : GraphSpace.DerivIndex n k) :
      IsClosed {U : W^{k,p}(ℝ^n) |
        coordinateReflectionLpLinearIsometry p i
            ((U : GraphSpace.WkpAmbientOn n k p Set.univ) a) =
          (c * (-1 : ℝ) ^ a.multiplicity i) •
            ((U : GraphSpace.WkpAmbientOn n k p Set.univ) a)} :=
    isClosed_eq ((coordinateReflectionLpLinearIsometry p i).continuous.comp (hcoord a))
      ((continuous_const (y := c * (-1 : ℝ) ^ a.multiplicity i)).smul (hcoord a))
  convert isClosed_iInter hclosed using 1
  ext U
  simp only [SetLike.mem_coe, mem_sobolevReflectionParitySubmodule_iff,
    Set.mem_iInter, Set.mem_ofPred_eq]

/-! ## Weighted parity classes -/

/-- Sobolev elements whose every graph coordinate also belongs to
`L^p(w dx)`, as a submodule of the unweighted graph space. -/
def coordinatesMemLpWithDensitySubmodule {n k : ℕ} (p : ℝ≥0∞)
    (w : ℝ^n → ℝ≥0∞) :
    Submodule ℝ (W^{k,p}(ℝ^n)) where
  carrier := {U | CoordinatesMemLpWithDensity w U}
  zero_mem' := by
    intro a
    have hcoe := (withDensity_absolutelyContinuous
      (domainMeasure n Set.univ) w).ae_eq
      (Lp.coeFn_zero ℝ p
        (domainMeasure n (Set.univ : Set (ℝ^n))))
    exact (memLp_congr_ae hcoe).2 MemLp.zero
  add_mem' := by
    intro U V hU hV a
    have hcoe := (withDensity_absolutelyContinuous
      (domainMeasure n Set.univ) w).ae_eq
      (Lp.coeFn_add
        ((U : GraphSpace.WkpAmbientOn n k p Set.univ) a)
        ((V : GraphSpace.WkpAmbientOn n k p Set.univ) a))
    exact (memLp_congr_ae hcoe).2 ((hU a).add (hV a))
  smul_mem' := by
    intro c U hU a
    have hcoe := (withDensity_absolutelyContinuous
      (domainMeasure n Set.univ) w).ae_eq
      (Lp.coeFn_smul c
        ((U : GraphSpace.WkpAmbientOn n k p Set.univ) a))
    exact (memLp_congr_ae hcoe).2 ((hU a).const_smul c)

/-- Membership in the weighted-integrability submodule is the predicate
`CoordinatesMemLpWithDensity w`. -/
@[simp] theorem mem_coordinatesMemLpWithDensitySubmodule_iff
    {n k : ℕ} {p : ℝ≥0∞} {w : ℝ^n → ℝ≥0∞}
    {U : W^{k,p}(ℝ^n)} :
    U ∈ coordinatesMemLpWithDensitySubmodule p w ↔
      CoordinatesMemLpWithDensity w U :=
  Iff.rfl

/-- Weighted whole-space Sobolev functions with base reflection eigenvalue
`c`. -/
def weightedSobolevReflectionParitySubmodule {n k : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (w : ℝ^n → ℝ≥0∞)
    (i : Fin n) (c : ℝ) : Submodule ℝ (W^{k,p}(ℝ^n)) :=
  coordinatesMemLpWithDensitySubmodule p w ⊓
    sobolevReflectionParitySubmodule p i c

/-- Weighted even `H^k(ℝ^n)` functions. -/
def weightedEvenHkSubmodule {n k : ℕ} (w : ℝ^n → ℝ≥0∞)
    (i : Fin n) : Submodule ℝ (W^{k,2}(ℝ^n)) :=
  weightedSobolevReflectionParitySubmodule 2 w i 1

/-- Weighted odd `H^k(ℝ^n)` functions. -/
def weightedOddHkSubmodule {n k : ℕ} (w : ℝ^n → ℝ≥0∞)
    (i : Fin n) : Submodule ℝ (W^{k,2}(ℝ^n)) :=
  weightedSobolevReflectionParitySubmodule 2 w i (-1)

/-- Weighted parity membership is weighted integrability of every coordinate together with
unweighted reflection parity. -/
@[simp] theorem mem_weightedSobolevReflectionParitySubmodule_iff
    {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : ℝ^n → ℝ≥0∞}
    {i : Fin n} {c : ℝ} {U : W^{k,p}(ℝ^n)} :
    U ∈ weightedSobolevReflectionParitySubmodule p w i c ↔
      CoordinatesMemLpWithDensity w U ∧
        U ∈ sobolevReflectionParitySubmodule p i c := by
  rfl

/-- Weighted even `H^k` membership is weighted integrability together with evenness. -/
@[simp] theorem mem_weightedEvenHkSubmodule_iff
    {n k : ℕ} {w : ℝ^n → ℝ≥0∞} {i : Fin n}
    {U : W^{k,2}(ℝ^n)} :
    U ∈ weightedEvenHkSubmodule w i ↔
      CoordinatesMemLpWithDensity w U ∧
        U ∈ evenSobolevSubmodule 2 i := by
  rfl

/-- Weighted odd `H^k` membership is weighted integrability together with oddness. -/
@[simp] theorem mem_weightedOddHkSubmodule_iff
    {n k : ℕ} {w : ℝ^n → ℝ≥0∞} {i : Fin n}
    {U : W^{k,2}(ℝ^n)} :
    U ∈ weightedOddHkSubmodule w i ↔
      CoordinatesMemLpWithDensity w U ∧
        U ∈ oddSobolevSubmodule 2 i := by
  rfl

end Weighted
end SobolevSpace

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.InitialData
public import PDE.Fluid.Incompressible.SpatialFields
import Mathlib.MeasureTheory.Function.L2Space
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.SpaceTime

/-!
# Common weak-form data for incompressible flow

The Euler and Navier–Stokes weak formulations share the test fields `IsWeakMomentumTest`
(vanishing at the terminal time), the velocity pairings, the inviscid momentum integrand
`inviscidWeakMomentumIntegrand`, and the zero-extended `L²` velocity slices `velocityL2SliceOn`.
The time derivative, spatial gradient and spatial divergence of a test are continuous with
compact support, and the `L²` slices on `[0,T]` have the distances and norms of the slices.
The Navier–Stokes integrand adds a viscous term to `inviscidWeakMomentumIntegrand`.

The tests and pairings are those of the weak Euler equation (3) of Wiedemann, on the whole space
and a finite time slab instead of a periodic cell and all nonnegative times; Wiedemann's tests are
also periodic and divergence-free. `velocityTestPairing` and `initialVelocityTestPairing` are
the pairings `∫ v · φ` of a velocity with a test slice.

## References

* E. Wiedemann, "Existence of weak solutions for the incompressible Euler equations", *Ann. Inst. H.
  Poincaré C Anal. Non Linéaire* 28 (2011), no. 5, 727-730; numbering of arXiv:1102.3614v1,
  equation (3), p. 1.
  <https://doi.org/10.1016/j.anihpc.2011.05.002>
  <https://arxiv.org/abs/1102.3614v1>
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace MeasureTheory PDE

set_option linter.missingDocs true

/-- A smooth compactly supported momentum test field that vanishes at terminal time.

The field may be nonzero at time zero, where it records the initial boundary term. -/
def IsWeakMomentumTest {n : ℕ} (T : ℝ)
    (φ : ℝ^(n + 1) → ℝ^n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    ∀ x : ℝ^n, φ (PDE.Common.timeSpaceCons T x) = 0

/-- Every fixed-time spatial slice of a weak momentum test has compact support. -/
theorem IsWeakMomentumTest.hasCompactSupport_spatialSlice
    {n : ℕ} {T : ℝ} {φ : ℝ^(n + 1) → ℝ^n}
    (hφ : IsWeakMomentumTest T φ) (t : ℝ) :
    HasCompactSupport
      (fun x : ℝ^n ↦ φ (PDE.Common.timeSpaceCons t x)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((PDE.Common.isProperMap_timeSpaceCons n t).isCompact_preimage
      hφ.2.1)
  intro x hx
  exact subset_tsupport φ hx

/-- Every fixed-time spatial slice of a weak momentum test belongs to every `Lᵖ` space. -/
theorem IsWeakMomentumTest.spatialSlice_memLp
    {n : ℕ} {T : ℝ} {φ : ℝ^(n + 1) → ℝ^n}
    (hφ : IsWeakMomentumTest T φ) (t : ℝ) {p : ENNReal} :
    MemLp (fun x : ℝ^n ↦ φ (PDE.Common.timeSpaceCons t x)) p
      (volume : Measure (ℝ^n)) := by
  apply Continuous.memLp_of_hasCompactSupport
  · exact hφ.1.continuous.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t
        (m := ⊤)).continuous
  · exact hφ.hasCompactSupport_spatialSlice t

/-- The coordinate derivatives of the components of a weak momentum test are continuous. -/
theorem IsWeakMomentumTest.continuous_partialDeriv {n : ℕ} {T : ℝ} {φ : ℝ^(n + 1) → ℝ^n}
    (hφ : IsWeakMomentumTest T φ) (k : Fin (n + 1)) (i : Fin n) :
    Continuous (∂[k] (fun y ↦ φ y i)) := by
  have hc : ContDiff ℝ 1 (fun y ↦ φ y i) :=
    (EuclideanSpace.proj i).contDiff.comp (hφ.1.of_le (by simp))
  exact hc.continuous_partialDeriv k

/-- The coordinate derivatives of the components of a vector field vanish off the support of the
field. -/
theorem partialDeriv_component_eq_zero_of_notMem_tsupport {n : ℕ} {φ : ℝ^(n + 1) → ℝ^n}
    (k : Fin (n + 1)) (i : Fin n) {z : ℝ^(n + 1)} (hz : z ∉ tsupport φ) :
    (∂[k] (fun y ↦ φ y i)) z = 0 :=
  partialDeriv_eq_zero_of_notMem_tsupport k
    fun h ↦ hz (tsupport_comp_subset (g := fun v : ℝ^n ↦ v i) (by simp) φ h)

/-- The time derivative of a weak momentum test is continuous with compact support. -/
theorem IsWeakMomentumTest.continuous_hasCompactSupport_timeDerivative {n : ℕ} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n}
    (hφ : IsWeakMomentumTest T φ) :
    Continuous (timeDerivative n φ) ∧ HasCompactSupport (timeDerivative n φ) := by
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦
    hφ.continuous_partialDeriv 0 i), HasCompactSupport.intro hφ.2.1 ?_⟩
  intro z hz
  ext i
  simp [partialDeriv_component_eq_zero_of_notMem_tsupport 0 i hz]

/-- The spatial gradient of a weak momentum test is continuous with compact support. -/
theorem IsWeakMomentumTest.continuous_hasCompactSupport_spatialVelocityGradient {n : ℕ} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n}
    (hφ : IsWeakMomentumTest T φ) :
    Continuous (spatialVelocityGradient n φ) ∧
      HasCompactSupport (spatialVelocityGradient n φ) := by
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun ij ↦
    hφ.continuous_partialDeriv ij.2.succ ij.1),
    HasCompactSupport.intro hφ.2.1 ?_⟩
  intro z hz
  ext ⟨i, j⟩
  simp [partialDeriv_component_eq_zero_of_notMem_tsupport j.succ i hz]

/-- The spatial divergence of a weak momentum test is continuous with compact support. -/
theorem IsWeakMomentumTest.continuous_hasCompactSupport_spatialDivergence {n : ℕ} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n}
    (hφ : IsWeakMomentumTest T φ) :
    Continuous (spatialDivergence n φ) ∧ HasCompactSupport (spatialDivergence n φ) := by
  refine ⟨continuous_finsetSum _ fun i _ ↦
    hφ.continuous_partialDeriv i.succ i,
    HasCompactSupport.intro hφ.2.1 ?_⟩
  intro z hz
  simp [spatialDivergence, partialDeriv_component_eq_zero_of_notMem_tsupport _ _ hz]

/-- Pointwise pairing of a velocity slice with a spatial vector test field. -/
noncomputable def velocityTestPairingDensity {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ)
    (φ : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ :=
  inner ℝ (u (PDE.Common.timeSpaceCons t x)) (φ x)

/-- Coordinate formula for the velocity-test pairing density. -/
theorem velocityTestPairingDensity_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ)
    (φ : ℝ^n → ℝ^n) (x : ℝ^n) :
    velocityTestPairingDensity u t φ x =
      ∑ i : Fin n, u (PDE.Common.timeSpaceCons t x) i * φ x i := by
  simp [velocityTestPairingDensity, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

/-- Pairing of a velocity slice with a spatial vector test field. -/
noncomputable def velocityTestPairing {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (φ : ℝ^n → ℝ^n) : ℝ :=
  ∫ x : ℝ^n, velocityTestPairingDensity u t φ x

/-- Pointwise pairing of prescribed initial velocity with a spatial vector test field. -/
noncomputable def initialVelocityTestPairingDensity {n : ℕ}
    (data : InitialValueData n) (φ : ℝ^n → ℝ^n)
    (x : ℝ^n) : ℝ :=
  inner ℝ (data.initialVelocity x) (φ x)

/-- Coordinate formula for the initial-velocity test-pairing density. -/
theorem initialVelocityTestPairingDensity_eq_sum {n : ℕ}
    (data : InitialValueData n) (φ : ℝ^n → ℝ^n)
    (x : ℝ^n) :
    initialVelocityTestPairingDensity data φ x =
      ∑ i : Fin n, data.initialVelocity x i * φ x i := by
  simp [initialVelocityTestPairingDensity, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

/-- An `L²` initial velocity pairs integrably with the initial slice of every weak momentum
test. -/
theorem integrable_initialVelocityTestPairingDensity_of_memLp
    {n : ℕ} {data : InitialValueData n} {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n}
    (hdata : MemLp data.initialVelocity 2
      (volume : Measure (ℝ^n)))
    (hφ : IsWeakMomentumTest T φ) :
    Integrable (initialVelocityTestPairingDensity data
      (fun x ↦ φ (PDE.Common.timeSpaceCons 0 x))) := by
  let initialL2 : MeasureTheory.Lp (ℝ^n) 2
      (volume : Measure (ℝ^n)) :=
    hdata.toLp data.initialVelocity
  have htest := hφ.spatialSlice_memLp (p := 2) 0
  let testL2 : MeasureTheory.Lp (ℝ^n) 2
      (volume : Measure (ℝ^n)) :=
    htest.toLp (fun x : ℝ^n ↦
      φ (PDE.Common.timeSpaceCons 0 x))
  have hinner :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℝ) initialL2 testL2
  apply hinner.congr
  filter_upwards [hdata.coeFn_toLp, htest.coeFn_toLp] with x hinitial htest
  rw [show initialL2 x = data.initialVelocity x by exact hinitial]
  rw [show testL2 x =
      φ (PDE.Common.timeSpaceCons 0 x) by exact htest]
  rfl

/-- Pairing of prescribed initial velocity with a spatial vector test field. -/
noncomputable def initialVelocityTestPairing {n : ℕ}
    (data : InitialValueData n) (φ : ℝ^n → ℝ^n) : ℝ :=
  ∫ x : ℝ^n, initialVelocityTestPairingDensity data φ x

/-- Scalar spacetime integrand of the pressure-retaining weak momentum equation without viscosity.

For `u_t + div(u ⊗ u) + ∇p - f = 0`, integration by parts against `φ` gives
`-u · φ_t - (u ⊗ u) : ∇φ - p div φ - f · φ`. -/
noncomputable def inviscidWeakMomentumIntegrand {n : ℕ}
    (f u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  -inner ℝ
      (u (PDE.Common.timeSpaceCons t x))
      (timeDerivative n φ (PDE.Common.timeSpaceCons t x))
  -inner ℝ
      (spatialOuterProduct
        (u (PDE.Common.timeSpaceCons t x))
        (u (PDE.Common.timeSpaceCons t x)))
      (spatialVelocityGradient n φ (PDE.Common.timeSpaceCons t x))
  - p (PDE.Common.timeSpaceCons t x) *
      spatialDivergence n φ (PDE.Common.timeSpaceCons t x)
  - inner ℝ (f (PDE.Common.timeSpaceCons t x)) (φ (PDE.Common.timeSpaceCons t x))

/-- Coordinate formula for the inviscid weak momentum integrand. -/
theorem inviscidWeakMomentumIntegrand_eq_sum {n : ℕ}
    (f u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    inviscidWeakMomentumIntegrand f u p φ t x =
      -(∑ i : Fin n, u (PDE.Common.timeSpaceCons t x) i *
        (∂[0] (fun y ↦ φ y i)) (PDE.Common.timeSpaceCons t x))
      -(∑ i : Fin n, ∑ j : Fin n,
        u (PDE.Common.timeSpaceCons t x) i *
          u (PDE.Common.timeSpaceCons t x) j *
          (∂[j.succ] (fun y ↦ φ y i))
            (PDE.Common.timeSpaceCons t x))
      -(∑ i : Fin n, p (PDE.Common.timeSpaceCons t x) *
        (∂[i.succ] (fun y ↦ φ y i))
          (PDE.Common.timeSpaceCons t x))
      -(∑ i : Fin n, f (PDE.Common.timeSpaceCons t x) i *
        φ (PDE.Common.timeSpaceCons t x) i) := by
  simp [inviscidWeakMomentumIntegrand, PiLp.inner_apply,
    RCLike.inner_apply, Fintype.sum_prod_type,
    Finset.mul_sum, mul_comm, mul_assoc]

/-- The `L²_x` slice of a velocity field whose slices on `[0,T]` are square integrable,
extended by zero outside `[0,T]`. -/
noncomputable def velocityL2SliceOn {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) {T : ℝ}
    (hu : ∀ {t : ℝ}, t ∈ Set.Icc 0 T →
      MemLp (velocitySlice u t) 2 (volume : Measure (ℝ^n)))
    (t : ℝ) : MeasureTheory.Lp (ℝ^n) 2 (volume : Measure (ℝ^n)) :=
  if ht : t ∈ Set.Icc 0 T then (hu ht).toLp (velocitySlice u t) else 0

/-- On `[0,T]`, `velocityL2SliceOn` represents the velocity slice almost everywhere. -/
theorem velocityL2SliceOn_apply_ae {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {T : ℝ}
    (hu : ∀ {t : ℝ}, t ∈ Set.Icc 0 T →
      MemLp (velocitySlice u t) 2 (volume : Measure (ℝ^n)))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (velocityL2SliceOn u hu t : ℝ^n → ℝ^n) =ᵐ[volume] velocitySlice u t := by
  simp [velocityL2SliceOn, ht, MemLp.coeFn_toLp]

/-- Outside `[0,T]`, `velocityL2SliceOn` is zero. -/
theorem velocityL2SliceOn_of_notMem {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {T : ℝ}
    (hu : ∀ {t : ℝ}, t ∈ Set.Icc 0 T →
      MemLp (velocitySlice u t) 2 (volume : Measure (ℝ^n)))
    {t : ℝ} (ht : t ∉ Set.Icc 0 T) :
    velocityL2SliceOn u hu t = 0 := by
  simp [velocityL2SliceOn, ht]

section L2Slice

variable {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {T : ℝ}
  (hu : ∀ {t : ℝ}, t ∈ Set.Icc 0 T → MemLp (velocitySlice u t) 2 volume)

/-- Two `L²` velocity slices on `[0,T]` are at the `L²` distance of the slices. -/
theorem dist_velocityL2SliceOn {s t : ℝ} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) :
    dist (velocityL2SliceOn u hu s) (velocityL2SliceOn u hu t) =
      (eLpNorm (velocitySlice u s - velocitySlice u t) 2 volume).toReal := by
  simp only [velocityL2SliceOn, hs, ht, ↓reduceDIte]
  rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]

/-- An `L²` velocity slice on `[0,T]` has the `L²` norm of the slice. -/
theorem norm_velocityL2SliceOn {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖velocityL2SliceOn u hu t‖ = (eLpNorm (velocitySlice u t) 2 volume).toReal := by
  simp only [velocityL2SliceOn, ht, ↓reduceDIte]
  rw [Lp.norm_toLp]

/-- An `L²` velocity slice on `[0,T]` is the class of any almost everywhere equal function. -/
theorem velocityL2SliceOn_eq_toLp {t : ℝ} (ht : t ∈ Set.Icc 0 T) {v : ℝ^n → ℝ^n}
    (hv : MemLp v 2 volume) (heq : velocitySlice u t =ᵐ[volume] v) :
    velocityL2SliceOn u hu t = hv.toLp v := by
  simp only [velocityL2SliceOn, ht, ↓reduceDIte]
  exact MemLp.toLp_congr _ _ heq

end L2Slice

end IncompressibleFlow

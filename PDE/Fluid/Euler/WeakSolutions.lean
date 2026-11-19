/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.WeakForm
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Weak solutions of the incompressible Euler equations

`WeakSolution` is a finite-time, pressure-retaining weak formulation on `ℝ^n`. Its momentum
identity uses the iterated space-then-time Euler momentum pairing. For zero forcing and
divergence-free tests, moving the initial pairing to the left and reversing signs gives the sign
convention of equation (3) in Wiedemann. That equation is posed on a periodic spatial cell for all
nonnegative times; the interface here uses the whole space, a finite time slab, and spatially
compactly supported tests.

The standard divergence-free-test formulation suppresses pressure. Here general vector test fields
are allowed, pressure is retained explicitly, and distributional incompressibility is recorded as a
separate condition. Every displayed integral is accompanied by an integrability hypothesis, so the
interface does not rely on the totalization of Lean's Bochner integral.

## References

* E. Wiedemann, "Existence of weak solutions for the incompressible Euler equations", *Ann. Inst. H.
  Poincaré C Anal. Non Linéaire* 28 (2011), no. 5, 727-730; numbering of arXiv:1102.3614v1,
  equation (3), p. 1.
  <https://doi.org/10.1016/j.anihpc.2011.05.002>
  <https://arxiv.org/abs/1102.3614v1>
-/

@[expose] public section

namespace Euler

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- Scalar spacetime integrand in the pressure-retaining weak Euler momentum equation. -/
noncomputable def weakMomentumIntegrand {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  IncompressibleFlow.inviscidWeakMomentumIntegrand data.forcing u p φ t x

/-- Spatial integral of the weak Euler momentum integrand at one time. -/
noncomputable def weakMomentumSlice {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n, weakMomentumIntegrand data u p φ t x

/-- Integrability obligations behind the iterated weak Euler momentum integral.

The initial boundary pairing is integrable automatically from the stored `L²` initial datum and
compact support of the test field; see
`WeakSolution.initialVelocityTestPairingDensity_integrable`. -/
def WeakMomentumIntegrableOn {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (T : ℝ) (φ : ℝ^(n + 1) → ℝ^n) : Prop :=
  (∀ t ∈ Set.Icc 0 T,
    Integrable (fun x : ℝ^n ↦ weakMomentumIntegrand data u p φ t x)) ∧
  IntegrableOn (weakMomentumSlice data u p φ) (Set.Icc 0 T)

/-- Pressure-retaining weak Euler solution on a closed finite time slab `[0,T]`.

The initial datum enters through the boundary term in `weak_momentum_eq`; no value assigned
to an arbitrary representative on the measure-zero slice `t = 0` is treated as an initial trace.
This is a pressure-retaining strong-data interface: velocity, pressure, and forcing have `L²`
spatial slices at every physical time, while `weak_momentum_integrable_on` gives integrability of
the full spacetime pairing. -/
structure WeakSolution {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n) where
  /-- Velocity field unknown. -/
  u : ℝ^(n + 1) → ℝ^n
  /-- Pressure field unknown. -/
  p : ℝ^(n + 1) → ℝ
  /-- Positive finite time horizon. -/
  T : Set.Ioi (0 : ℝ)
  /-- The prescribed initial velocity belongs to `L²(ℝ^n)`. -/
  initialVelocity_memLp :
    MemLp data.initialVelocity 2
      (MeasureTheory.volume : Measure (ℝ^n))
  /-- Every physical velocity slice belongs to `L²(ℝ^n)`. -/
  velocity_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (IncompressibleFlow.velocitySlice u t) 2
      (MeasureTheory.volume : Measure (ℝ^n))
  /-- Every physical pressure slice belongs to `L²(ℝ^n)`. -/
  pressure_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (fun x : ℝ^n ↦ p (PDE.Common.timeSpaceCons t x)) 2
      (MeasureTheory.volume : Measure (ℝ^n))
  /-- Every physical forcing slice belongs to `L²(ℝ^n)`. -/
  force_memLp_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    MemLp (fun x : ℝ^n ↦ data.forcing (PDE.Common.timeSpaceCons t x)) 2
      (MeasureTheory.volume : Measure (ℝ^n))
  /-- Every admissible test field gives integrable, non-totalized integrals. -/
  weak_momentum_integrable_on :
    ∀ φ : ℝ^(n + 1) → ℝ^n,
      IncompressibleFlow.IsWeakMomentumTest T φ →
      WeakMomentumIntegrableOn data u p T φ
  /-- Distributional momentum equation, including the initial boundary term.

  For `u_t + div(u ⊗ u) + ∇p - f = 0`, integration by parts gives
  `-u · φ_t - (u ⊗ u) : ∇φ - p div φ - f · φ`. -/
  weak_momentum_eq :
    ∀ φ : ℝ^(n + 1) → ℝ^n,
      IncompressibleFlow.IsWeakMomentumTest T φ →
      (∫ t in Set.Icc 0 (T : ℝ), weakMomentumSlice data u p φ t) =
        IncompressibleFlow.initialVelocityTestPairing data
          (fun x ↦ φ (PDE.Common.timeSpaceCons 0 x))
  /-- Every velocity slice is incompressible in the distributional sense. -/
  distributionallyDivergenceFree_at : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    IncompressibleFlow.DistributionallyDivergenceFree
      (IncompressibleFlow.velocitySlice u t)

/-- The initial boundary pairing in the weak Euler equation is integrable. -/
theorem WeakSolution.initialVelocityTestPairingDensity_integrable {n : ℕ}
    {data : IncompressibleFlow.InitialValueData n}
    (sol : WeakSolution data) (φ : ℝ^(n + 1) → ℝ^n)
    (hφ : IncompressibleFlow.IsWeakMomentumTest sol.T φ) :
    Integrable (IncompressibleFlow.initialVelocityTestPairingDensity data
      (fun x ↦ φ (PDE.Common.timeSpaceCons 0 x))) :=
  IncompressibleFlow.integrable_initialVelocityTestPairingDensity_of_memLp
    sol.initialVelocity_memLp hφ

/-- Zero-extended `L²_x` velocity slice associated with a weak Euler solution. -/
noncomputable def WeakSolution.velocityL2Slice {n : ℕ}
    {data : IncompressibleFlow.InitialValueData n}
    (sol : WeakSolution data) (t : ℝ) :
    MeasureTheory.Lp (ℝ^n) 2
      (MeasureTheory.volume : Measure (ℝ^n)) :=
  IncompressibleFlow.velocityL2SliceOn sol.u sol.velocity_memLp_at t

/-- On the physical slab, `velocityL2Slice` represents the stored velocity almost everywhere. -/
theorem WeakSolution.velocityL2Slice_apply_ae {n : ℕ}
    {data : IncompressibleFlow.InitialValueData n}
    (sol : WeakSolution data) {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ)) :
    (sol.velocityL2Slice t : ℝ^n → ℝ^n)
      =ᵐ[MeasureTheory.volume] IncompressibleFlow.velocitySlice sol.u t :=
  IncompressibleFlow.velocityL2SliceOn_apply_ae sol.velocity_memLp_at ht

/-- The weak divergence pairing of every physical velocity slice vanishes. -/
theorem WeakSolution.weakDivergencePairing_eq_zero {n : ℕ}
    {data : IncompressibleFlow.InitialValueData n}
    (sol : WeakSolution data) {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ))
    (ψ : ℝ^n → ℝ) (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    IncompressibleFlow.weakDivergencePairing
      (IncompressibleFlow.velocitySlice sol.u t) ψ = 0 :=
  (sol.distributionallyDivergenceFree_at ht).weakDivergencePairing_eq_zero
    ψ hψsmooth hψcompact

/-- The weak divergence-pairing density of every physical velocity slice is integrable. -/
theorem WeakSolution.weakDivergencePairingDensity_integrable {n : ℕ}
    {data : IncompressibleFlow.InitialValueData n}
    (sol : WeakSolution data) {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ))
    (ψ : ℝ^n → ℝ) (hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    Integrable (IncompressibleFlow.weakDivergencePairingDensity
      (IncompressibleFlow.velocitySlice sol.u t) ψ) :=
  (sol.distributionallyDivergenceFree_at ht).weakDivergencePairingDensity_integrable
    ψ hψsmooth hψcompact

end Euler

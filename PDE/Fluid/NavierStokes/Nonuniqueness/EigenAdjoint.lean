/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ClassicalEigen
public import PDE.Fluid.NavierStokes.Selfsimilar.GraphWeakForm
public import PDE.Fluid.NavierStokes.Stationary.TestFieldRepresentative
public import PDE.Fluid.NavierStokes.Selfsimilar.PairingIntegrals

/-!
# The weak eigenvalue density against the adjoint, for every divergence-free `H¹` field

The weak eigenvalue density of `v ∈ H¹(ℝ³)³` at a profile `B` keeps the derivatives of `v`. A
weak limit of solutions on balls is known only through pairings in which every derivative has
been moved to the test field `φ`: `∫ v · (L_B)* φ`, with `(L_B)* φ = profileAdjoint B φ`. This
module shows that the two agree for every divergence-free `v` in `H¹`, with no regularity of `v`
beyond `H¹`. The profile is bounded and classical off the origin; a profile that is only in
`L²_loc` and divergence-free in the sense of distributions is not treated.

## Main results

* `NavierStokes.Stationary.inner_massCLM_testFieldH1`: in every dimension,
  `⟨w, φ⟩_{L²} = ∫ w · φ` for the `H¹` class of a smooth compactly supported `φ`.
* `integral_weakEigenDensity_eq_integral_inner_profileAdjoint_of_divergenceFree`: let `B` be a
  bounded continuous profile that is `C¹` and divergence-free off the origin, with locally
  integrable derivatives. For every divergence-free `v` in `H¹(ℝ³)³` and every smooth compactly
  supported `φ`, the density is integrable and
  `∫ weakEigenDensity B 0 v φ = ∫ v · profileAdjoint B φ`.

## How it works

For a bounded profile both sides are continuous linear functionals of `v` in `H¹`: the density
integrates to the tested linearization (`Selfsimilar.integral_weakEigenDensity`), and the adjoint
pairing is an `L²` pairing. For a smooth compactly supported divergence-free `v` they agree by the
classical integration by parts (`integral_weakEigenDensity_eq_integral_inner_profileAdjoint`,
which covers every `v` that is smooth off the origin). These fields are dense in the
divergence-free part of `H¹` (`Stationary.mem_topologicalClosure_span_solenoidalTestFields`), so
the two functionals agree there.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff

namespace NavierStokes.Stationary

/-- The `L²` pairing of a field of `H¹(ℝⁿ)ⁿ` with the class of a smooth compactly supported
field `φ` is `∫ w · φ`. -/
theorem inner_massCLM_testFieldH1 {n : ℕ} (w : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ⟪massCLM w, massCLM (testFieldH1 φ hφ hφc)⟫ = ∫ x, ⟪representative w x, φ x⟫ := by
  rw [← Selfsimilar.massPairing_eq_integral_of_ae (v := w) Filter.EventuallyEq.rfl
    (representative_testFieldH1_ae hφ hφc), ← Selfsimilar.massForm_apply]
  rfl

end NavierStokes.Stationary

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- **The weak eigenvalue density against the adjoint.** Let `B` be bounded and continuous,
`C¹` and divergence-free off the origin, with locally integrable first partial derivatives,
and let `b` be its `L^∞` class. For every divergence-free `v ∈ H¹(ℝ³)³` and every smooth
compactly supported `φ`, the weak eigenvalue density at `μ = 0` is integrable and

`∫ weakEigenDensity B 0 v φ = ∫ v · profileAdjoint B φ`.

Both sides are continuous linear functionals of `v`, they agree on the smooth compactly
supported divergence-free fields, and these are dense in the divergence-free part of `H¹`. -/
theorem integral_weakEigenDensity_eq_integral_inner_profileAdjoint_of_divergenceFree
    {B : ℝ^3 → ℝ^3} (b : Fin 3 → DerivLp 3 ∞ univ)
    (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ B x i) (hBc : Continuous B)
    (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x i)) volume)
    {v : H} (hv : Stationary.divergenceCLM v = 0) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    Integrable (weakEigenDensity B 0 v φ) ∧
      ∫ x, weakEigenDensity B 0 v φ x =
        ∫ x, ⟪Stationary.representative v x, profileAdjoint B φ x⟫ := by
  have hBm : AEStronglyMeasurable B volume := hBc.aestronglyMeasurable
  have hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume := (hBc.norm.pow 2).locallyIntegrable
  refine ⟨(Selfsimilar.integral_weakEigenDensity B b hb 0 v hφ hφc).1, ?_⟩
  -- The difference of the two sides, as a continuous linear functional of the field.
  let Λ : StrongDual ℝ H :=
    (Selfsimilar.boundedPart b).flip (Stationary.testFieldH1 φ hφ hφc) -
      (1 / 2 : ℝ) • Selfsimilar.testedDrift hφ.continuous hφc -
      (innerSL ℝ (profileAdjointCoordinates hBm hB2 hφ hφc)).comp Stationary.massCLM
  have hΛ (w : H) : Λ w = (∫ x, weakEigenDensity B 0 w φ x) -
      ∫ x, ⟪Stationary.representative w x, profileAdjoint B φ x⟫ := by
    rw [(Selfsimilar.integral_weakEigenDensity B b hb 0 w hφ hφc).2,
      ← inner_massCLM_profileAdjointCoordinates hBm hB2 hφ hφc w, real_inner_comm]
    simp only [Λ, sub_apply, smul_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul, zero_mul, add_zero]
  have htest : ∀ w ∈ Stationary.solenoidalTestFields 3, Λ w = 0 := by
    rintro _ ⟨ψ, hψ, hψc, hψdiv, rfl⟩
    rw [hΛ, sub_eq_zero]
    exact (integral_weakEigenDensity_eq_integral_inner_profileAdjoint hBc hB hBdiv hBD
      hψ.continuous (fun x _ ↦ (hψ.of_le (by simp)).contDiffAt) (fun x _ ↦ hψdiv x)
      (fun i j ↦ ((Stationary.contDiff_component hψ i).continuous_fderiv
        (by simp)).clm_apply continuous_const |>.locallyIntegrable)
      (Stationary.representative_testFieldH1_ae hψ hψc)
      (fun i j ↦ Stationary.gradientRepresentative_testFieldH1_ae hψ hψc i j) hφ hφc).2.trans
      (integral_congr_ae (by
        filter_upwards [Stationary.representative_testFieldH1_ae hψ hψc] with x hx
        rw [hx]))
  have hker : (Submodule.span ℝ (Stationary.solenoidalTestFields 3)).topologicalClosure ≤
      LinearMap.ker Λ.toLinearMap :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr fun w hw ↦ LinearMap.mem_ker.mpr (htest w hw)) Λ.isClosed_ker
  have h0 : Λ v = 0 := LinearMap.mem_ker.mp
    (hker (Stationary.mem_topologicalClosure_span_solenoidalTestFields (by norm_num) v hv))
  rw [hΛ, sub_eq_zero] at h0
  exact h0

end NavierStokes.Nonuniqueness

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Flux.TargetIdentity
public import PDE.Spaces.Sobolev.Calculus.Divergence.LocalTesting

/-!
# Localized tests for a transported flux equation

Only the values of the extended flux and load on the cutoff support enter
the equation. Smooth chart tests give the identity there, and density extends
it to cutoffs of arbitrary `H¹₀` tests on the half-space.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Boundary

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.WeakChangeOfVariables
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- An arbitrary extension of the transformed flux and load satisfies the
equation on tests cut off inside the chart. Agreement is required
only where the cutoff can be nonzero. -/
theorem weakFlux_chartPullback_cutoff_identity
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ (hΩ.chart a).target)
    (Q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (F : DerivLp n 2 (HalfSpace.upper n))
    (hQ : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ tsupport χ.toFun →
      ∀ i : Fin n, Q i y =
        (piolaTransform (hΩ.chart a) (fun x ↦ WithLp.toLp 2 (fun j ↦ q j x)) y) i)
    (hF : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ tsupport χ.toFun →
      F y = |(fderiv ℝ (fun z ↦ (hΩ.chart a).symm z) y).det| *
        f ((hΩ.chart a).symm y))
    (v : H¹₀(HalfSpace.upper n)) :
    (∑ i, ⟪Q i, derivCoordCLM i (cutoffH10 (HalfSpace.isOpen_upper n) χ v)⟫) =
      ⟪F, baseCoordCLM (cutoffH10 (HalfSpace.isOpen_upper n) χ v)⟫ := by
  apply weakDivergence_cutoff_pairing_of_testFunctions
  intro φ
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
  let ψ : TestFunctionOn n (HalfSpace.upper n) :=
    ⟨TestFunction.mul χ φ.1, tsupport_mul_subset_right.trans φ.2⟩
  have hψχ : tsupport ψ.1.toFun ⊆ tsupport χ.toFun := tsupport_mul_subset_left
  have hψE : tsupport ψ.1.toFun ⊆ E.target := by
    rw [SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
    exact fun y hy ↦ ⟨hχ (hψχ hy), ψ.2 hy⟩
  let ψE : TestFunctionOn n E.target := ⟨ψ.1, hψE⟩
  have hEupper : E.target ⊆ HalfSpace.upper n :=
    SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper a
  rw [cutoffH10_testFunction]
  change (∑ i, ⟪Q i, derivCoordCLM i (testFunctionToH10 ψ)⟫) =
    ⟪F, baseCoordCLM (testFunctionToH10 ψ)⟫
  apply weakDivergence_test_pairing_of_restricted_integral
    (HalfSpace.isOpen_upper n).measurableSet hEupper Q F ψ hψE
    (fun y i ↦ (piolaTransform E (fun x ↦ WithLp.toLp 2 (fun j ↦ q j x)) y) i)
    (fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y))
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hEupper hQ] with y hy hyψ
    exact hy (hψχ hyψ)
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hEupper hF] with y hy hyψ
    exact hy (hψχ hyψ)
  · have h := weakFlux_chartPullback_target_identity hΩ a q f hweak ψE
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using h

end PDE.Elliptic.Regularity.Boundary

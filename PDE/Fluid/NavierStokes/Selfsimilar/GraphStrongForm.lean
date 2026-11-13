/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphWeakForm
public import PDE.Fluid.NavierStokes.Selfsimilar.WeightedRepresenters
import PDE.Fluid.NavierStokes.Stationary.TestFieldRepresentative

/-!
# Fields of the graph domain with a square-integrable strong form

Let `T` be a dilation test space in dimension three and `b` the `L∞` class of a profile `U`. If
a field `v` of the closed span `E` of the test fields satisfies
`∫ weakEigenDensity U 0 v φ = ∫ ⟪R, φ⟫` for every test field `φ`, with `R` square integrable,
then its tested drift extends continuously to `E`, so `v` lies in the graph domain, and the weak
linearization at `v` is the `L²` pairing with `R`:
`⟨L_b v, w⟩ = ⟪R, w⟫_{L²}` for every `w ∈ E` (`exists_mem_graphDomain_linearization_eq`). The
same holds on the weighted copy of `E` with the weighted mass map
(`exists_mem_weightedGraphDomain_weightedLinearization_eq`). This is the weak-strong identity
of a field whose strong residual is computed classically.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev RealInnerProductSpace SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary
open PDE.Analysis.Evolution (restrictForm restrictForm_apply)

set_option linter.missingDocs true

namespace DilationTestSpace

variable (T : DilationTestSpace 3) (U : ℝ^3 → ℝ^3) (b : Fin 3 → DerivLp 3 ∞ univ)

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

local notation "Mass" => PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 univ)

/-- The `L²` pairing with a mass field as a functional on the closed span. -/
def massPairingAt (q : Mass) : StrongDual ℝ T.space :=
  (innerSL ℝ q).comp (massCLM.comp T.space.subtypeL)

theorem massPairingAt_apply (q : Mass) (w : T.space) :
    T.massPairingAt q w = ⟪q, massCLM ((w : T.space) : H)⟫ :=
  rfl

/-- **Weak-strong identity.** A field of the closed span whose weak eigenvalue density at
`μ = 0` integrates against every test field to the `L²` pairing with a square-integrable `R`
lies in the graph domain, and the weak linearization at it is the `L²` pairing with `R`. -/
theorem exists_mem_graphDomain_linearization_eq
    (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i) {v : T.space} {R : ℝ^3 → ℝ^3}
    (hR : MemLp R 2 volume)
    (hv : ∀ φ : T.carrier, ∫ x, Nonuniqueness.weakEigenDensity U 0 (v : _) φ x =
      ∫ x, ⟪R x, (φ : ℝ^3 → ℝ^3) x⟫) :
    ∃ h : v ∈ T.graphDomain, T.linearization b ⟨v, h⟩ = T.massPairingAt (massField R hR) := by
  have hpt (φ : T.carrier) : T.massPairingAt (massField R hR) (T.point φ) =
      ∫ x, ⟪R x, (φ : ℝ^3 → ℝ^3) x⟫ := by
    rw [massPairingAt_apply, coe_point, toH1]
    refine inner_massField_massCLM hR _
      ((T.contDiff φ φ.2).continuous.memLp_of_hasCompactSupport (T.hasCompactSupport φ φ.2))
      (representative_testFieldH1_ae (T.contDiff φ φ.2) (T.hasCompactSupport φ φ.2))
  have hint (φ : T.carrier) := (integral_weakEigenDensity U b hb 0 (v : _)
    (T.contDiff φ φ.2) (T.hasCompactSupport φ φ.2)).2
  have hmem : v ∈ T.graphDomain := by
    refine ⟨(2 : ℝ) • (restrictForm T.space (boundedPart b) v -
      T.massPairingAt (massField R hR)), fun φ ↦ ?_⟩
    have h := hint φ
    rw [hv φ, ← hpt φ, zero_mul, add_zero] at h
    rw [smul_apply, sub_apply, restrictForm_apply, smul_eq_mul]
    change 2 * (boundedPart b (v : _) (T.toH1 φ) - T.massPairingAt (massField R hR) (T.point φ)) =
      T.driftAt φ (v : _)
    change T.massPairingAt (massField R hR) (T.point φ) =
      boundedPart b (v : _) (T.toH1 φ) - 1 / 2 * T.driftAt φ (v : _) at h
    linarith
  refine ⟨hmem, T.ext_point fun φ ↦ ?_⟩
  rw [linearization_point, hpt φ, ← hv φ, hint φ, zero_mul, add_zero]
  rfl

/-- **Weak-strong identity on the weighted copy.** Under the hypotheses of
`exists_mem_graphDomain_linearization_eq`, the image of `v` in the weighted copy lies in the
weighted graph domain and the weighted linearization at it is the pairing with `R` through the
weighted mass map. -/
theorem exists_mem_weightedGraphDomain_weightedLinearization_eq {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i) {v : T.space} {R : ℝ^3 → ℝ^3}
    (hR : MemLp R 2 volume)
    (hv : ∀ φ : T.carrier, ∫ x, Nonuniqueness.weakEigenDensity U 0 (v : _) φ x =
      ∫ x, ⟪R x, (φ : ℝ^3 → ℝ^3) x⟫) :
    ∃ h : T.weightedEquiv hc v ∈ T.weightedGraphDomain hc, ∀ x : T.weighted c,
      T.weightedLinearization hc b ⟨T.weightedEquiv hc v, h⟩ x =
        ⟪massField R hR, T.weightedMass hc x⟫ := by
  obtain ⟨h, hL⟩ := T.exists_mem_graphDomain_linearization_eq U b hb hR hv
  have hw : T.weightedEquiv hc v ∈ T.weightedGraphDomain hc := ⟨v, h, rfl⟩
  refine ⟨hw, fun x ↦ ?_⟩
  have hsymm : (T.weightedGraphEquiv hc).symm ⟨T.weightedEquiv hc v, hw⟩ = ⟨v, h⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [weightedLinearization_apply, hsymm, hL, weightedMass_apply, massPairingAt_apply]

end DilationTestSpace

end NavierStokes.Selfsimilar

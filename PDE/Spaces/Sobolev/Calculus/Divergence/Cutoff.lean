/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates
public import PDE.Spaces.Sobolev.Calculus.Divergence.Component
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Localization of a weak divergence equation

Testing `-div q = f` on `ηv` yields
`-div(ηq) = ηf - ∑ (∂ᵢη)qᵢ`.
All fields on the right are `L²` elements. The hypothesis only asks for
the equation on these localized tests, allowing the original equation to hold
in a neighborhood of the cutoff support.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The localized source, with the sign prescribed by `-div q = f`. -/
def divergenceCutoffSource (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω) : DerivLp n 2 Ω :=
  testFunctionLpTop (Ω := Ω) η • f -
    ∑ i, partialTestFunctionLpTop (Ω := Ω) η i • q i

/-- The localized load is controlled by the original load and the
cutoff corrections, without derivatives of the flux. -/
theorem norm_divergenceCutoffSource_le
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω) :
    ‖divergenceCutoffSource η q f‖ ≤
      ‖testFunctionLpTop (Ω := Ω) η‖ * ‖f‖ +
        ∑ i, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ * ‖q i‖ := by
  refine (norm_sub_le _ _).trans (add_le_add (Lp.norm_smul_le _ _) ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ Lp.norm_smul_le _ _)

/-- Moving cutoff multipliers across the L² pairings retains exactly the signed
lower-order correction in the source. -/
theorem divergenceCutoff_pairing (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω) (v : H¹₀(Ω))
    (hdiv : (∑ i, ⟪q i, derivCoordCLM i (cutoffH10 hΩ η v)⟫) =
      ⟪f, baseCoordCLM (cutoffH10 hΩ η v)⟫) :
    (∑ i, ⟪testFunctionLpTop (Ω := Ω) η • q i, derivCoordCLM i v⟫) =
      ⟪divergenceCutoffSource η q f, baseCoordCLM v⟫ := by
  simp only [derivCoordCLM_cutoffH10, baseCoordCLM_cutoffH10, inner_add_right,
    Finset.sum_add_distrib] at hdiv
  simp only [divergenceCutoffSource, inner_sub_left, sum_inner, Lp.inner_lpSMul_left]
  linarith only [hdiv]

/-- The localized weak equation holds on the smooth test functions of the
domain; no regularity of the flux components has been assumed. -/
theorem weakDivergence_cutoff (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hdiv : ∀ φ : TestFunctionOn n Ω,
      (∑ i, ⟪q i, derivCoordCLM i (cutoffH10 hΩ η (testFunctionToH10 φ))⟫) =
        ⟪f, baseCoordCLM (cutoffH10 hΩ η (testFunctionToH10 φ))⟫) :
    ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport φ.toFun ⊆ Ω →
      (∑ i, ∫ x, (testFunctionLpTop (Ω := Ω) η • q i : DerivLp n 2 Ω) x *
        (∂[i] φ.toFun) x ∂domainMeasure n Ω) =
      ∫ x, divergenceCutoffSource η q f x * φ.toFun x ∂domainMeasure n Ω := by
  intro φ hφ
  let ψ : TestFunctionOn n Ω := ⟨φ, hφ⟩
  have hpair := divergenceCutoff_pairing hΩ η q f (testFunctionToH10 ψ) (hdiv ψ)
  have hcoord (i : Fin n) :
      ⟪testFunctionLpTop (Ω := Ω) η • q i, derivCoordCLM i (testFunctionToH10 ψ)⟫ =
      ∫ x, (testFunctionLpTop (Ω := Ω) η • q i : DerivLp n 2 Ω) x *
        (∂[i] φ.toFun) x ∂domainMeasure n Ω := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [derivCoordCLM_testFunction_apply_ae i ψ] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simpa only [hcoord, inner_base_testFunction_eq_integral] using hpair

end SobolevSpace.GraphSpace

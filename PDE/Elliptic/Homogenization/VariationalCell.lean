/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram

/-!
# Variational cell correction

A coercive bilinear form on a Hilbert space determines a unique correction in any
complete gradient subspace. The construction uses the Lax–Milgram solver.
For an isometric family of constant fields orthogonal to the gradient subspace,
the effective form retains the original ellipticity lower bound.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace PDE.Elliptic.Homogenization.VariationalCell

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (G : Submodule ℝ H) [CompleteSpace G]
  (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B) (e : E →ₗᵢ[ℝ] H)

/-- Restriction of the coefficient form to the cell gradient space. -/
def form : G →L[ℝ] G →L[ℝ] ℝ := B.bilinearComp G.subtypeL G.subtypeL

omit [CompleteSpace G] in
include hB in
/-- Coercivity restricts to the gradient subspace. -/
theorem form_isCoercive : IsCoercive (form G B) := by
  obtain ⟨c, hc, hbound⟩ := hB
  exact ⟨c, hc, fun g ↦ hbound (g : H)⟩

/-- The cell correction constructed by the canonical Lax–Milgram solver. -/
def correctorCLM : E →L[ℝ] G :=
  (Analysis.Variational.solveCLM (form G B) (form_isCoercive G B hB)).comp
    (-(B.bilinearComp e.toContinuousLinearMap G.subtypeL))

/-- The corrected field has flux orthogonal to all admissible cell gradients. -/
theorem corrector_equation (ξ : E) (g : G) :
    B (e ξ + (correctorCLM G B hB e ξ : H)) g = 0 := by
  have h := Analysis.Variational.solve.isWeakSolution (form G B)
    (form_isCoercive G B hB)
    ((-(B.bilinearComp e.toContinuousLinearMap G.subtypeL)) ξ) g
  change B (correctorCLM G B hB e ξ : H) (g : H) = -B (e ξ) g at h
  rw [map_add, add_apply, h, add_neg_cancel]

/-- The cell correction is uniquely determined by its variational equation. -/
theorem corrector_unique (ξ : E) {g : G}
    (hg : ∀ h : G, B (e ξ + (g : H)) h = 0) :
    g = correctorCLM G B hB e ξ := by
  apply Analysis.Variational.IsWeakSolution.unique (form G B) (form_isCoercive G B hB)
    ((-(B.bilinearComp e.toContinuousLinearMap G.subtypeL)) ξ)
  · intro h
    have hh := hg h
    change B (g : H) h = -B (e ξ) h
    rw [map_add, add_apply] at hh
    linarith
  · exact Analysis.Variational.solve.isWeakSolution (form G B)
      (form_isCoercive G B hB) _

/-- The imposed constant field plus its cell correction. -/
def totalGradientCLM : E →L[ℝ] H :=
  e.toContinuousLinearMap + G.subtypeL.comp (correctorCLM G B hB e)

/-- The effective form pairs the corrected flux with a constant field. -/
def effectiveForm : E →L[ℝ] E →L[ℝ] ℝ :=
  B.bilinearComp (totalGradientCLM G B hB e) e.toContinuousLinearMap

/-- A second corrector may be inserted by the cell equation. -/
theorem effectiveForm_eq (ξ η : E) :
    effectiveForm G B hB e ξ η =
      B (totalGradientCLM G B hB e ξ) (totalGradientCLM G B hB e η) := by
  change B (e ξ + (correctorCLM G B hB e ξ : H)) (e η) =
    B (e ξ + (correctorCLM G B hB e ξ : H))
      (e η + (correctorCLM G B hB e η : H))
  rw [(B _).map_add, corrector_equation G B hB e, add_zero]

/-- Orthogonality to constants preserves the original ellipticity lower bound. -/
theorem effectiveForm_lower_bound (α : ℝ) (hα : 0 ≤ α)
    (hlower : ∀ v : H, α * ‖v‖ ^ 2 ≤ B v v)
    (horth : ∀ (ξ : E) (g : G), ⟪e ξ, (g : H)⟫_ℝ = 0) (ξ : E) :
    α * ‖ξ‖ ^ 2 ≤ effectiveForm G B hB e ξ ξ := by
  rw [effectiveForm_eq]
  apply le_trans _ (hlower _)
  apply mul_le_mul_of_nonneg_left _ hα
  change ‖ξ‖ ^ 2 ≤ ‖e ξ + (correctorCLM G B hB e ξ : H)‖ ^ 2
  rw [norm_add_sq_real, horth ξ _, e.norm_map]
  simp only [mul_zero, add_zero]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The effective form is coercive when cell gradients are orthogonal to constants. -/
theorem effectiveForm_isCoercive
    (horth : ∀ (ξ : E) (g : G), ⟪e ξ, (g : H)⟫_ℝ = 0) :
    IsCoercive (effectiveForm G B hB e) := by
  obtain ⟨α, hα, hlower⟩ := hB
  have hB : IsCoercive B := ⟨α, hα, hlower⟩
  refine ⟨α, hα, fun ξ ↦ ?_⟩
  simpa only [pow_two, mul_assoc] using effectiveForm_lower_bound G B hB e α hα.le
    (fun v ↦ by simpa only [pow_two, mul_assoc] using hlower v) horth ξ

/-- Symmetry of the microscopic form passes to the effective form. -/
theorem effectiveForm_symmetric (hsymm : ∀ v w : H, B v w = B w v) (ξ η : E) :
    effectiveForm G B hB e ξ η = effectiveForm G B hB e η ξ := by
  rw [effectiveForm_eq, effectiveForm_eq, hsymm]

end PDE.Elliptic.Homogenization.VariationalCell

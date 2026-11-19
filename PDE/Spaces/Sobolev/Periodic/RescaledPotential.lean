/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.Dilation
public import PDE.Analysis.Integration.PeriodicAveraging.LocalLp
public import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Rescaled periodic potentials in Euclidean Sobolev spaces

On a bounded measurable domain, `ε u(x/ε)` belongs to the Euclidean
`W¹²` space. Its stored weak gradient is precisely the rescaled periodic gradient.
The uniform rescaling bound controls its Sobolev norm as the period tends to zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Periodic

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω)

include hΩm in
/-- The rescaled value and gradient form a canonical Euclidean Sobolev graph. -/
theorem exists_scaledPotential (u : h1Space n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ U : W^{1,2}(Ω),
      GraphSpace.wkpBaseCoordinateCLM U = ε • rescaleLp hΩ ε hε hε1 (valueCLM n u) ∧
      ∇ U = rescaleLp hΩ ε hε hε1 (gradientCLM n u) := by
  obtain ⟨U, hU, hDU⟩ := GraphSpace.exists_of_weakGradient
    ((memLp_rescale hΩ ε hε hε1 (valueCLM n u)).const_smul ε)
    (memLp_rescale hΩ ε hε hε1 (gradientCLM n u))
    (fun i ↦ (hasWeakDerivativeOn_scaledPotential u ε hε.ne' i).mono hΩm (subset_univ Ω))
  refine ⟨U, Lp.ext ?_, Lp.ext ?_⟩
  · filter_upwards [hU, Lp.coeFn_smul ε (rescaleLp hΩ ε hε hε1 (valueCLM n u)),
      rescaleLp_ae hΩ ε hε hε1 (valueCLM n u)] with x hx hy hz
    exact hx.trans (by simp only [hy, Pi.smul_apply, hz])
  · exact hDU.trans (rescaleLp_ae hΩ ε hε hε1 (gradientCLM n u)).symm

/-- The canonical Sobolev element represented by the amplitude-scaled periodic potential. -/
def scaledPotential (u : h1Space n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : W^{1,2}(Ω) :=
  (exists_scaledPotential hΩ hΩm u ε hε hε1).choose

/-- The base coordinate of the rescaled potential is `ε u(x/ε)` in local `L²`. -/
theorem base_scaledPotential (u : h1Space n) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    GraphSpace.wkpBaseCoordinateCLM (scaledPotential hΩ hΩm u ε hε hε1) =
      ε • rescaleLp hΩ ε hε hε1 (valueCLM n u) :=
  (exists_scaledPotential hΩ hΩm u ε hε hε1).choose_spec.1

/-- The weak gradient of `ε u(x/ε)` is the rescaled periodic weak gradient. -/
@[simp] theorem gradient_scaledPotential (u : h1Space n) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∇ (scaledPotential hΩ hΩm u ε hε hε1) =
      rescaleLp hΩ ε hε hε1 (gradientCLM n u) :=
  (exists_scaledPotential hΩ hΩm u ε hε hε1).choose_spec.2

/-- The rescaled potentials have uniformly bounded Euclidean Sobolev norms. -/
theorem exists_norm_scaledPotential_le (u : h1Space n) :
    ∃ C : ℝ, ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε1 : ε ≤ 1,
      ‖scaledPotential hΩ hΩm u ε hε hε1‖ ≤ C := by
  obtain ⟨Cv, _hCv, hv⟩ := exists_norm_rescaleLp_le (E := ℝ) (p := 2) hΩ
  obtain ⟨Cg, _hCg, hg⟩ := exists_norm_rescaleLp_le (E := ℝ^n) (p := 2) hΩ
  refine ⟨Cv * ‖valueCLM n u‖ + n * (Cg * ‖gradientCLM n u‖), fun ε hε hε1 ↦ ?_⟩
  let U := scaledPotential hΩ hΩm u ε hε hε1
  have hb : ‖GraphSpace.wkpBaseCoordinateCLM U‖ ≤ Cv * ‖valueCLM n u‖ := by
    rw [base_scaledPotential, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact (mul_le_of_le_one_left (norm_nonneg _) hε1).trans (hv ε hε hε1 _)
  have hd (i : Fin n) :
      ‖U.val (GraphSpace.singleDerivIndex n i)‖ ≤ Cg * ‖gradientCLM n u‖ := by
    apply (GraphSpace.norm_derivCoordinate_le_wkpGradientCLM U i).trans
    rw [gradient_scaledPotential]
    exact hg ε hε hε1 _
  calc
    ‖U‖ ≤ ‖GraphSpace.wkpBaseCoordinateCLM U‖ +
        ∑ i : Fin n, ‖U.val (GraphSpace.singleDerivIndex n i)‖ :=
      GraphSpace.ambient_norm_le_base_add_sum_deriv U.val
    _ ≤ Cv * ‖valueCLM n u‖ + ∑ _i : Fin n, Cg * ‖gradientCLM n u‖ :=
      add_le_add hb (Finset.sum_le_sum fun i _ ↦ hd i)
    _ = _ := by simp

end SobolevSpace.Periodic

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Energy

/-!
# Superlevel energy with bounded forcing

For an essentially bounded source, the truncated source has `L²` norm at most
its essential bound times the square root of the superlevel measure. Combining
this with the truncated test estimate gives the measure term used in De Giorgi
iteration. The superlevel set is defined by the representative of the shifted
Sobolev element, so no pointwise representative of the solution is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal InnerProductSpace Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]
variable [IsFiniteMeasure (domainMeasure n Ω)]

omit [Fact (0 < n)] hΩ in
private theorem norm_superlevel_forcing_le
    (U : H¹(Ω)) (f g : DerivLp n 2 Ω) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M)
    (hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ if 0 < wkpBaseCoordinateCLM U x then f x else 0) :
    ‖g‖ ≤ M * (domainMeasure n Ω).real {x | 0 < wkpBaseCoordinateCLM U x} ^
      (1 / 2 : ℝ) := by
  let E := {x | 0 < wkpBaseCoordinateCLM U x}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
  let H : DerivLp n 2 Ω :=
    indicatorConstLp 2 hE (measure_ne_top (domainMeasure n Ω) E) M
  have hnorm : ‖g‖ ≤ ‖H‖ := by
    apply Lp.norm_le_norm_of_ae_le
    have hH : (H : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] E.indicator (fun _ ↦ M) :=
      indicatorConstLp_coeFn
    filter_upwards [hg, hf, hH] with x hgx hfx hHx
    rw [hgx, hHx]
    by_cases hx : x ∈ E
    · have hx' : 0 < wkpBaseCoordinateCLM U x := hx
      simpa only [ite_eq_left hx', Set.indicator_of_mem hx,
        Real.norm_eq_abs, abs_of_nonneg hM] using hfx
    · have hx' : ¬0 < wkpBaseCoordinateCLM U x := hx
      simp only [ite_eq_right hx', Set.indicator_of_notMem hx, norm_zero, le_refl]
  exact hnorm.trans_eq (by
    dsimp only [H]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [Real.norm_eq_abs, abs_of_nonneg hM, ENNReal.toReal_ofNat, E])

/-- The superlevel Caccioppoli estimate for an essentially bounded scalar
source. The forcing term contains the square root of the superlevel
measure, derived from the source bound. No regularity of the solution or of
the measurable coefficient representatives is assumed. -/
theorem IsInteriorWeakDivergenceSolution.superlevel_cutoff_gradient_sq_le_measure
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) (hu : IsInteriorWeakDivergenceSolution a f u)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M)
    (k : ℝ) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    let U := u - wkpConstant k
    let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
    let q : DerivLp n ∞ Ω := testFunctionLpTop η
    α ^ 2 * ∑ i, ‖(q • wkpCoordinateCLM (singleDerivIndex n i) T :
      DerivLp n 2 Ω)‖ ^ 2 ≤
      4 * (∑ i, ∑ j, ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 *
        ‖wkpBaseCoordinateCLM T‖ ^ 2 +
      2 * α * ‖q‖ ^ 2 * M *
        (domainMeasure n Ω).real {x | 0 < wkpBaseCoordinateCLM U x} ^ (1 / 2 : ℝ) *
        ‖wkpBaseCoordinateCLM T‖ := by
  obtain ⟨g, hg, he⟩ := hu.superlevel_cutoff_gradient_sq_le a ha f u k η hη
  have hgNorm := norm_superlevel_forcing_le (u - wkpConstant k) f g hM hf hg
  refine he.trans ?_
  have hfactor : 0 ≤ 2 * α * ‖testFunctionLpTop (Ω := Ω) η‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) ha.1.le) (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgNorm hfactor)
    (norm_nonneg (wkpBaseCoordinateCLM
      (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
        (u - wkpConstant k))))
  simpa only [mul_assoc] using add_le_add le_rfl hscaled

end SobolevSpace.GraphSpace

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Vector
public import PDE.Analysis.MeasureTheory.Lp.IntegralCoercivity

/-!
# Coercive extended energies for coupled Sobolev systems

Full-matrix power coercivity bounds every finite energy sublevel in an
affine zero-trace class. The integrand may couple every value and gradient
entry and may have arbitrarily fast upper growth.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev

namespace PDE.CalculusOfVariations

/-- Finite sublevels of a coupled, matrix-coercive energy are bounded in the
product Sobolev norm. The boundary lift need not have finite energy, and the
density need not be integrable. -/
theorem isBounded_sublevel_vectorWkpLIntegral_prescribed_boundary
    {m n : ℕ} (hn : 0 < n) {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 ≤ p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) {K : ℝ≥0∞} (hK : K ≠ ∞) :
    Bornology.IsBounded {w : Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω) |
      (∫⁻ x, ENNReal.ofReal (F x
        (vectorWkpValueCLM (g + fun i ↦ (w i : W^{1,(p : ℝ≥0∞)}(Ω))) x,
          ∇ (g + fun i ↦ (w i : W^{1,(p : ℝ≥0∞)}(Ω))) x)
            + b x) ∂domainMeasure n Ω) ≤ K} := by
  let W := Fin m → W^{1,(p : ℝ≥0∞)}(Ω)
  let B : W →L[ℝ] Lp (ℝ^m) p (domainMeasure n Ω) := vectorWkpValueCLM
  let G : W →L[ℝ] Lp (ℝ^(m * n)) p (domainMeasure n Ω) := vectorWkpGradientCLM
  let I (u : W) : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (F x (B u x, G u x) + b x) ∂domainMeasure n Ω
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : 1 ≤ (p : ℝ≥0∞))).ne'
  have hIlower (u : W) : ENNReal.ofReal (c * ‖G u‖ ^ (p : ℝ)) ≤ I u := by
    apply Lp.ofReal_mul_norm_rpow_le_lintegral hp0 ENNReal.coe_ne_top (G u) hc.le
    filter_upwards [hlower] with x hx
    simpa only [ENNReal.coe_toReal] using (sub_le_iff_le_add.mp (hx (B u x) (G u x)))
  obtain ⟨P, hP⟩ := exists_norm_le_vectorWkpGradientCLM (m := m) hn hΩ hp
  let R : ℝ := max 1 (K.toReal / c)
  refine isBounded_iff_forall_norm_le.mpr ⟨(P : ℝ) * (R + ‖G g‖), ?_⟩
  intro w hw
  let v : W := fun i ↦ (w i : W^{1,(p : ℝ≥0∞)}(Ω))
  change I (g + v) ≤ K at hw
  have hpower : c * ‖G (g + v)‖ ^ (p : ℝ) ≤ K.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hK).mp ((hIlower (g + v)).trans hw)
  have hgradient : ‖G (g + v)‖ ≤ R := by
    by_contra h
    have hlt : R < ‖G (g + v)‖ := lt_of_not_ge h
    have hone : 1 ≤ ‖G (g + v)‖ := (le_max_left _ _).trans hlt.le
    have hquot : K.toReal / c < ‖G (g + v)‖ := (le_max_right _ _).trans_lt hlt
    have hlarge := (div_lt_iff₀ hc).mp hquot
    have hpow := mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_one_le hone hpR) hc.le
    nlinarith
  have hdiff : G v = G (g + v) - G g := by rw [map_add, add_sub_cancel_left]
  have hbound : ‖G v‖ ≤ R + ‖G g‖ := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add hgradient le_rfl)
  exact (hP w).trans (mul_le_mul_of_nonneg_left hbound P.coe_nonneg)

end PDE.CalculusOfVariations

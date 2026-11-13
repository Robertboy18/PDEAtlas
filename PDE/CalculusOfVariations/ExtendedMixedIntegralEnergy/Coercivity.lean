/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent
public import PDE.Analysis.MeasureTheory.Lp.IntegralCoercivity

/-!
# Finite sublevels of coercive extended Sobolev energies

A positive lower bound `c |Du|ᵖ - b(x)` controls the gradient on every finite sublevel
of the nonnegative energy `∫⁻ ofReal (F(x, u, Du) + b(x))`. Poincaré then bounds the
full Sobolev norm of the zero-boundary correction in any prescribed affine class.

The density can grow arbitrarily fast from above. The proof integrates only the
known `Lᵖ` gradient power and compares its integral with the extended energy. In
particular, it never replaces a potentially infinite energy by a Bochner integral.
Boundedness of the domain suffices; no boundary atlas is used.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal

namespace PDE.CalculusOfVariations

/-- Positive gradient coercivity bounds every finite extended-energy sublevel in a
prescribed affine Sobolev class on a bounded set of positive dimension, for every
finite `p ≥ 1`. The boundary condition is the supported-core closure: the variable
`w` lies in `W¹ᵖ₀`, and the full field is `g + w`.

No upper growth bound or finite energy for every Sobolev field is required. A finite
energy competitor is needed separately to make such a finite sublevel nonempty.
When `b` is integrable, adding it is a finite shift of the original energy. -/
theorem isBounded_sublevel_mixedWkpLIntegral_prescribed_boundary
    {n : ℕ} (hn : 0 < n) {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 ≤ p)
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : W^{1,p}(Ω)) {K : ℝ≥0∞} (hK : K ≠ ∞) :
    Bornology.IsBounded {w : W₀^{1,(p : ℝ≥0∞)}(Ω) |
      (∫⁻ x, ENNReal.ofReal (F x
        (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞))
            (g + (w : W^{1,p}(Ω))) x,
          ∇ (g + (w : W^{1,p}(Ω))) x) + b x)
        ∂domainMeasure n Ω) ≤ K} := by
  let W := W^{1,p}(Ω)
  let B : W →L[ℝ] Lp ℝ p (domainMeasure n Ω) := wkpBaseCoordinateCLM
  let G : W →L[ℝ] Lp (ℝ^n) p (domainMeasure n Ω) := wkpGradientCLM
  let I (u : W) : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (F x (B u x, G u x) + b x) ∂domainMeasure n Ω
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : 1 ≤ (p : ℝ≥0∞))).ne'
  have hIlower (u : W) : ENNReal.ofReal (c * ‖G u‖ ^ (p : ℝ)) ≤ I u := by
    apply Lp.ofReal_mul_norm_rpow_le_lintegral hp0 ENNReal.coe_ne_top (G u) hc.le
    filter_upwards [hlower] with x hx
    simpa only [ENNReal.coe_toReal] using (sub_le_iff_le_add.mp (hx (B u x) (G u x)))
  obtain ⟨P, hP⟩ := exists_norm_le_wkpGradientCLM hn hΩ hp
  let R : ℝ := max 1 (K.toReal / c)
  refine isBounded_iff_forall_norm_le.mpr ⟨(P : ℝ) * (R + ‖G g‖), ?_⟩
  intro w hw
  change I (g + (w : W)) ≤ K at hw
  have hpower : c * ‖G (g + (w : W))‖ ^ (p : ℝ) ≤ K.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hK).mp ((hIlower (g + (w : W))).trans hw)
  have hgradient : ‖G (g + (w : W))‖ ≤ R := by
    by_contra h
    have hlt : R < ‖G (g + (w : W))‖ := lt_of_not_ge h
    have hone : 1 ≤ ‖G (g + (w : W))‖ := (le_max_left _ _).trans hlt.le
    have hquot : K.toReal / c < ‖G (g + (w : W))‖ :=
      (le_max_right _ _).trans_lt hlt
    have hlarge := (div_lt_iff₀ hc).mp hquot
    have hpow := mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_one_le hone hpR) hc.le
    nlinarith
  have hdiff : G (w : W) = G (g + (w : W)) - G g := by
    rw [map_add, add_sub_cancel_left]
  have hbound : ‖G (w : W)‖ ≤ R + ‖G g‖ := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add hgradient le_rfl)
  exact (hP w).trans (mul_le_mul_of_nonneg_left hbound P.coe_nonneg)

end PDE.CalculusOfVariations

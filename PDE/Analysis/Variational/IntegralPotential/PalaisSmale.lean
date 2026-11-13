/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.IntegralPotential.Hilbert
public import PDE.Analysis.Variational.CriticalPoint.PalaisSmale.CompactPerturbation

/-!
# Palais–Smale from a scalar potential inequality

The inequality `G(z) ≤ γ g(z) z`, with `0 ≤ γ < 1/2`, bounds a vector's
quadratic norm by its energy and gradient. A compact inclusion into `Lᵖ` then
gives the whole-range Palais–Smale condition for the integral energy. The inequality is the
upper half of Evans's hypothesis (24) in §8.5.2, and `norm_sq_le_energy_gradient`,
`(1/2 - γ) ‖u‖² ≤ I u + γ ‖∇ I u‖ ‖u‖`, is the estimate behind his bound on `‖u_k‖²` in
step 4 of the proof of Theorem 3. `palaisSmale_energy` then applies
`palaisSmale_of_compact_perturbation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, the hypothesis (24), p. 507, and step 4 of the
  proof of Theorem 3 (Existence), (31)-(35), pp. 509-510. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ENNReal

namespace PDE.Analysis.Variational.IntegralPotential

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure α} [IsFiniteMeasure μ]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  {G g : ℝ → ℝ} {A B C γ : ℝ}

include q in
/-- The scalar potential inequality supplies the coercive energy-gradient bound
for every vector in the Hilbert space. -/
theorem norm_sq_le_energy_gradient
    (J : H →L[ℝ] Lp ℝ p μ) (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hG : ∀ z, |G z| ≤ A + B * |z| ^ p.toReal)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1)))
    (hγ : 0 ≤ γ) (hAR : ∀ z, G z ≤ γ * g z * z) (u : H) :
    (1 / 2 - γ) * ‖u‖ ^ 2 ≤ energy J G u +
      γ * ‖∇ (energy J G) u‖ * ‖u‖ := by
  have hcont : Continuous G := continuous_iff_continuousAt.mpr fun z ↦ (hd z).continuousAt
  have hint : Integrable (fun x ↦ G (J u x)) μ := by
    apply (Lp.memLp (J u)).integrable_comp_of_norm_rpow_le
      (ne_of_gt (zero_lt_one.trans hp)) hp_top (G := fun _ ↦ G)
      (hcont.measurable.comp measurable_snd) (integrable_const A)
    exact ae_of_all μ fun _ z ↦ by simpa only [Real.norm_eq_abs] using hG z
  have hpair : Integrable (fun x ↦ g (J u x) * J u x) μ :=
    (memLp_comp_of_conjugate_growth (q := q) hc hg (J u)).integrable_mul
      (Lp.memLp (J u))
  have hARint : (∫ x, G (J u x) ∂μ) ≤ γ * ∫ x, g (J u x) * J u x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hint (hpair.const_mul γ)
    exact ae_of_all μ fun x ↦ by simpa only [mul_assoc] using hAR (J u x)
  have hidentity : inner ℝ (∇ (energy J G) u) u =
      ‖u‖ ^ 2 - ∫ x, g (J u x) * J u x ∂μ := by
    rw [gradient_energy (q := q) J hp hp_top hd hc hG hg,
      inner_sub_left, real_inner_self_eq_norm_sq, inner_dualLift]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_superposition (fun _ : α ↦ g)
      (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg) (J u)]
      with x hx
    rw [hx]
  have hinner : -inner ℝ (∇ (energy J G) u) u ≤
      ‖∇ (energy J G) u‖ * ‖u‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hscaled := mul_le_mul_of_nonneg_left hinner hγ
  dsimp only [energy]
  nlinarith

include q in
/-- A compact `Lᵖ` inclusion and the scalar potential inequality imply the full
Palais–Smale condition. The nonlinear term is the superposition of `g`. -/
theorem palaisSmale_energy
    (J : H →L[ℝ] Lp ℝ p μ) (hJ : IsCompactOperator J)
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1)))
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) (hAR : ∀ z, G z ≤ γ * g z * z) :
    PalaisSmale (energy J G) := by
  -- The growth of `G` follows from that of `g` by the mean value theorem on `[0, z]`.
  have hpR : 1 < p.toReal := by simpa using ENNReal.toReal_strict_mono hp_top hp
  have hC : 0 ≤ C := by
    have h0 := hg 0
    rw [abs_zero, Real.zero_rpow (by linarith), add_zero, mul_one] at h0
    exact (abs_nonneg _).trans h0
  have hG : ∀ z, |G z| ≤ (|G 0| + C) + 2 * C * |z| ^ p.toReal := by
    intro z
    have hmvt : ‖G z - G 0‖ ≤ C * (1 + |z| ^ (p.toReal - 1)) * ‖z - 0‖ :=
      (convex_uIcc 0 z).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun ξ _ ↦ (hd ξ).hasDerivWithinAt)
        (fun ξ hξ ↦ by
          have hξz : |ξ| ≤ |z| := by
            rcases Set.mem_uIcc.mp hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
              exact h2
            · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
              linarith
          have hpow := Real.rpow_le_rpow (abs_nonneg ξ) hξz (sub_nonneg.mpr hpR.le)
          rw [Real.norm_eq_abs]
          exact (hg ξ).trans (mul_le_mul_of_nonneg_left (by linarith) hC))
        Set.left_mem_uIcc Set.right_mem_uIcc
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hmvt
    have hpow : |z| ^ (p.toReal - 1) * |z| = |z| ^ p.toReal := by
      conv_rhs => rw [show p.toReal = (p.toReal - 1) + 1 by ring,
        Real.rpow_add' (abs_nonneg z) (by linarith), Real.rpow_one]
    have hz1 : |z| ≤ 1 + |z| ^ p.toReal := by
      rcases le_total |z| 1 with h | h
      · linarith [Real.rpow_nonneg (abs_nonneg z) p.toReal]
      · have := Real.rpow_le_rpow_of_exponent_le h hpR.le
        rw [Real.rpow_one] at this
        linarith
    have h1 := mul_le_mul_of_nonneg_left hz1 hC
    have h2 : C * (1 + |z| ^ (p.toReal - 1)) * |z| = C * |z| + C * |z| ^ p.toReal := by
      rw [← hpow]
      ring
    have h3 := abs_sub_abs_le_abs_sub (G z) (G 0)
    linarith
  let N := Lp.superposition (fun _ : α ↦ g)
    (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg)
  have hN : Continuous N :=
    Lp.continuous_superposition_of_conjugate_growth hp hp_top (G := fun _ : α ↦ g)
      (hc.measurable.comp measurable_snd) (ae_of_all μ fun _ ↦ hc) (memLp_const C)
      (ae_of_all μ fun _ z ↦ by simpa [Real.norm_eq_abs, mul_add] using hg z)
  exact palaisSmale_of_compact_perturbation J hJ (fun z ↦ dualLift J (N z))
    ((dualLift (q := q) J).continuous.comp hN)
    (gradient_energy J hp hp_top hd hc hG hg) (sub_pos.mpr hγhalf) hγ
    (norm_sq_le_energy_gradient (q := q) J hp hp_top hd hc hG hg hγ hAR)

end PDE.Analysis.Variational.IntegralPotential

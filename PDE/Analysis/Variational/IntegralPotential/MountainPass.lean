/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.IntegralPotential.Geometry
public import PDE.Analysis.Variational.IntegralPotential.GradientLipschitz
public import PDE.Analysis.Variational.IntegralPotential.PalaisSmale
public import PDE.Analysis.Variational.CriticalPoint.Minimax.MountainPass

/-!
# Nonzero critical points of superquadratic integral energies

The scalar power and potential inequalities give every analytic input of the
mountain-pass theorem: differentiability, the gradient formula, the Palais–Smale
condition, and the energy barrier. The inclusion is compact and not identically
zero.

`exists_nonzero_criticalPoint` is an abstract form of Evans, §8.5.2, Theorem 3. There
`H = H¹₀(U)`, `J` is the inclusion into `L^{p+1}(U)`, which is compact since `p + 1 < 2*`,
and `G = F`, `g = f` and `dg = f'`; our exponent `p` is his `p + 1`. The hypotheses `hg` and
`hbound` are his growth conditions (23), `hAR` is the upper half of (24), and `hupper` and
`hlower` are (25), where his `F ≥ 0` removes the absolute value in the lower bound. By
`inner_eq_integral_of_gradient_eq_zero`, the critical point is a weak solution `u ≠ 0` of
his problem (22).

## Main results

* `exists_nonzero_criticalPoint`: for a compact `J : H →L[ℝ] Lp ℝ p μ` that is not
  identically zero, with `p > 2`, and a potential `G` with `G 0 = 0` satisfying these bounds,
  the energy `½ ‖u‖² - ∫ G (J u)` has a nonzero critical point.

## How it works

We follow Evans's proof. `contDiff_energy`, `gradient_energy` and
`exists_lipschitzOnWith_gradient_energy` are his steps 2 and 3, which put `I` in the class
`C` of §8.5.1; `palaisSmale_energy` is step 4; `exists_sphere_barrier` and
`exists_escape_point` are step 5; and `PalaisSmale.mountain_pass` gives the critical point, as
in step 6. The abstraction is ours: a compact `J` and the Riesz lift `dualLift` replace
`H¹₀(U)`, the Sobolev inequalities and the Lax–Milgram operator `K`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, (22)-(25) and Theorem 3 (Existence) with its
  proof, (26)-(36), pp. 507-511. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE.Analysis.Variational.IntegralPotential

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure α} [IsFiniteMeasure μ]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  {G g dg : ℝ → ℝ} {a A C D γ : ℝ}

include q in
/-- A compact inclusion and scalar superquadratic data produce a nonzero
critical point of the integral energy. -/
theorem exists_nonzero_criticalPoint
    (J : H →L[ℝ] Lp ℝ p μ) (hJ : IsCompactOperator J) (hp2 : 2 < p.toReal)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hzero : G 0 = 0) (ha : 0 < a) (hA : 0 ≤ A)
    (hupper : ∀ z, |G z| ≤ A * |z| ^ p.toReal)
    (hlower : ∀ z, a * |z| ^ p.toReal ≤ G z)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1)))
    (hdg : ∀ z, HasDerivAt g (dg z) z)
    (hbound : ∀ z, ‖dg z‖ ≤ D * (1 + ‖z‖ ^ (p.toReal - 2)))
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) (hAR : ∀ z, G z ≤ γ * g z * z)
    (hnonzero : ∃ w, J w ≠ 0) :
    ∃ u : H, u ≠ 0 ∧ ∇ (energy J G) u = 0 := by
  have hp_top : p ≠ ∞ := by
    rintro rfl
    norm_num at hp2
  have hp : 1 < p := by
    by_contra h
    have := ENNReal.toReal_mono ENNReal.one_ne_top (not_lt.mp h)
    rw [ENNReal.toReal_one] at this
    linarith
  have hp_zero := ne_of_gt (zero_lt_one.trans hp)
  have hG : ∀ z, |G z| ≤ 0 + A * |z| ^ p.toReal := by
    simpa only [zero_add] using hupper
  have hcont : Continuous G := continuous_iff_continuousAt.mpr fun z ↦ (hd z).continuousAt
  obtain ⟨r, b, hr, hb, hbarrier⟩ :=
    exists_sphere_barrier J hp_zero hp_top hp2 hcont hA hupper
  obtain ⟨w, hw⟩ := hnonzero
  obtain ⟨v, hv, hIv⟩ :=
    exists_escape_point J hp_zero hp_top hp2 hcont ha hupper hlower hw r
  have hPS := palaisSmale_energy (q := q) J hJ hp hp_top hd hc hg hγ hγhalf hAR
  have hI := contDiff_energy (q := q) J hp hp_top hd hc hG hg
  have hL (R : ℝ) (hR : 0 < R) :=
    exists_lipschitzOnWith_gradient_energy (q := q) J hp2 hd hc hG hg hdg hbound hR.le
  have hIzero : energy J G 0 = 0 := by
    simp only [energy, norm_zero, zero_pow two_ne_zero, mul_zero, map_zero]
    have heq : (fun x ↦ G ((0 : Lp ℝ p μ) x)) =ᵐ[μ] 0 := by
      filter_upwards [Lp.coeFn_zero ℝ p μ] with x hx
      simp only [hx, Pi.zero_apply, hzero]
    rw [integral_congr_ae heq]
    simp
  obtain ⟨_, u, hu, _, hcrit⟩ :=
    hPS.mountain_pass hI hL hIzero hr hb hbarrier hv hIv
  exact ⟨u, hu, hcrit⟩

end PDE.Analysis.Variational.IntegralPotential

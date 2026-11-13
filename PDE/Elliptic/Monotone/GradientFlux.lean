/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition
public import PDE.Analysis.Operator.Minty
public import PDE.Elliptic.Variational.PrincipalForms
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak Dirichlet solutions for monotone gradient fluxes

For a measurable flux `a(x, p)` with linear growth, the expression
`∫_Ω ⟨a(x, Du), Dv⟩` is an integrable pairing for every `u, v ∈ H¹₀`.
Pointwise monotonicity and one-sided hemicontinuity pass to the induced
operator from `H¹₀` to its continuous dual. A lower bound
`c |p|² - b(x) ≤ ⟨a(x, p), p⟩`, with `c > 0` and `b ∈ L¹`, combines with
bounded-domain Poincaré to give operator coercivity.

Browder–Minty then gives a weak solution for every continuous dual load.
The flux need not be a gradient of a potential or globally Lipschitz.
Uniqueness under strict monotonicity is `Monotone.Uniqueness`.

The domain is bounded and the dimension is positive. The proofs use the
closure-defined Sobolev graph space; no boundary regularity is needed.
On open domains the conclusion is the usual weak Dirichlet equation.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "V" => H¹₀(Ω)
local notation "μ" => domainMeasure n Ω
local notation "G" => gradientCLM (n := n) (Ω := Ω)

private theorem integrable_inner_flux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    {q r : ℝ^n → ℝ^n} (hq : MemLp q 2 μ) (hr : MemLp r 2 μ) :
    Integrable (fun x ↦ inner ℝ (a x (q x)) (r x)) μ := by
  have hflux := hq.comp_of_norm_le hmeas hh hgrowth
  have hbound := hflux.norm.integrable_mul hr.norm
  refine hbound.mono'
    (hflux.aestronglyMeasurable.inner hr.aestronglyMeasurable) ?_
  exact ae_of_all μ fun x ↦ norm_inner_le_norm (a x (q x)) (r x)

/-- A linearly growing measurable flux pairs integrably with every weak
gradient in `L²`. This holds for every trial and test field, independently
of monotonicity or the existence theorem. -/
theorem integrable_inner_gradientFlux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (u v : V) :
    Integrable (fun x ↦ inner ℝ (a x (∇ (u : H¹(Ω)) x)) (∇ (v : H¹(Ω)) x)) μ :=
  integrable_inner_flux a hmeas hh hgrowth (Lp.memLp (G u)) (Lp.memLp (G v))

/-- The continuous dual functional obtained by testing the flux of `Du`
against weak gradients. The linear growth hypothesis constructs the flux
as an `L²` class; continuity is in the test variable. -/
def gradientFluxOperator
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (u : V) : StrongDual ℝ V :=
  (innerSL ℝ (Lp.superposition a
    (fun q : Lp (ℝ^n) 2 μ ↦ (Lp.memLp q).comp_of_norm_le hmeas hh hgrowth)
    (G u))).comp G

/-- The dual functional agrees with the integral of the pointwise flux.
Its integrability is `integrable_inner_gradientFlux`. -/
theorem gradientFluxOperator_apply
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (u v : V) :
    gradientFluxOperator a hmeas hh hgrowth u v =
      ∫ x, inner ℝ (a x (∇ (u : H¹(Ω)) x)) (∇ (v : H¹(Ω)) x) ∂μ := by
  unfold gradientFluxOperator
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_superposition a
    (fun q : Lp (ℝ^n) 2 μ ↦ (Lp.memLp q).comp_of_norm_le hmeas hh hgrowth)
    (G u)] with x hx
  rw [hx]
  rfl

/-- Monotonicity of the flux at almost every spatial point gives
monotonicity of its weak Dirichlet operator. -/
theorem gradientFluxOperator_monotone
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hmono : ∀ᵐ x ∂μ, ∀ p q, 0 ≤ inner ℝ (a x p - a x q) (p - q))
    (u v : V) :
    0 ≤ (gradientFluxOperator a hmeas hh hgrowth u -
      gradientFluxOperator a hmeas hh hgrowth v) (u - v) := by
  rw [sub_apply, gradientFluxOperator_apply, gradientFluxOperator_apply,
    ← integral_sub
      (integrable_inner_gradientFlux a hmeas hh hgrowth u (u - v))
      (integrable_inner_gradientFlux a hmeas hh hgrowth v (u - v))]
  apply integral_nonneg_of_ae
  have hsub : G (u - v) =ᵐ[μ] fun x ↦ G u x - G v x := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (G u) (G v)] with x hx
    exact hx
  filter_upwards [hmono, hsub] with x hx hsubx
  change 0 ≤ inner ℝ (a x (G u x)) (G (u - v) x) -
    inner ℝ (a x (G v x)) (G (u - v) x)
  rw [hsubx, ← inner_sub_left]
  exact hx _ _

private theorem continuousWithinAt_integral_inner_flux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hhemi : ∀ᵐ x ∂μ, ∀ p q : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (p + t • q)) q) (Ici 0) 0)
    (q r : Lp (ℝ^n) 2 μ) :
    ContinuousWithinAt
      (fun t : ℝ ↦ ∫ x, inner ℝ (a x (q x + t • r x)) (r x) ∂μ)
      (Ici 0) 0 := by
  let B (x : ℝ^n) : ℝ :=
    (‖h x‖ + |C| * (‖q x‖ + ‖r x‖)) * ‖r x‖
  have hB₂ : MemLp (fun x ↦ ‖h x‖ + |C| * (‖q x‖ + ‖r x‖)) 2 μ :=
    hh.norm.add (((Lp.memLp q).norm.add (Lp.memLp r).norm).const_mul |C|)
  have hB : Integrable B μ := hB₂.integrable_mul (Lp.memLp r).norm
  have hline (t : ℝ) : MemLp (fun x ↦ q x + t • r x) 2 μ :=
    (Lp.memLp q).add ((Lp.memLp r).const_smul t)
  have hmeasline : ∀ᶠ t : ℝ in 𝓝[Ici 0] 0,
      AEStronglyMeasurable (fun x ↦ inner ℝ (a x (q x + t • r x)) (r x)) μ :=
    Eventually.of_forall fun t ↦
      (integrable_inner_flux a hmeas hh hgrowth
        (hline t) (Lp.memLp r)).aestronglyMeasurable
  have hdom : ∀ᶠ t : ℝ in 𝓝[Ici 0] 0, ∀ᵐ x ∂μ,
      ‖inner ℝ (a x (q x + t • r x)) (r x)‖ ≤ B x := by
    have htlt : ∀ᶠ t : ℝ in 𝓝[Ici 0] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, htlt] with t ht0 ht1
    filter_upwards [hgrowth] with x hx
    have hnorm : ‖q x + t • r x‖ ≤ ‖q x‖ + ‖r x‖ := by
      calc
        ‖q x + t • r x‖ ≤ ‖q x‖ + ‖t • r x‖ := norm_add_le _ _
        _ ≤ ‖q x‖ + ‖r x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          nlinarith [norm_nonneg (r x)]
    have hflux : ‖a x (q x + t • r x)‖ ≤
        ‖h x‖ + |C| * (‖q x‖ + ‖r x‖) := by
      calc
        ‖a x (q x + t • r x)‖ ≤ h x + C * ‖q x + t • r x‖ := hx _
        _ ≤ ‖h x‖ + |C| * ‖q x + t • r x‖ :=
          add_le_add (by simpa only [Real.norm_eq_abs] using le_abs_self (h x))
            (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
        _ ≤ ‖h x‖ + |C| * (‖q x‖ + ‖r x‖) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm (abs_nonneg C))
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hflux (norm_nonneg _))
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun t : ℝ ↦ inner ℝ (a x (q x + t • r x)) (r x))
        (𝓝[Ici 0] 0) (𝓝 (inner ℝ (a x (q x)) (r x))) := by
    filter_upwards [hhemi] with x hx
    simpa only [ContinuousWithinAt, zero_smul, add_zero] using hx (q x) (r x)
  simpa only [ContinuousWithinAt, zero_smul, add_zero] using
    tendsto_integral_filter_of_dominated_convergence B hmeasline hdom hB hlim

/-- One-sided pointwise hemicontinuity passes to the weak operator.
The proof uses an `L² · L²` dominating function on each bounded line
segment, so no global Lipschitz condition is needed. -/
theorem gradientFluxOperator_hemicontinuous
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hhemi : ∀ᵐ x ∂μ, ∀ p q : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (p + t • q)) q) (Ici 0) 0)
    (u v : V) :
    ContinuousWithinAt
      (fun t : ℝ ↦ gradientFluxOperator a hmeas hh hgrowth (u + t • v) v)
      (Ici 0) 0 := by
  have heq (t : ℝ) :
      gradientFluxOperator a hmeas hh hgrowth (u + t • v) v =
        ∫ x, inner ℝ (a x (G u x + t • G v x)) (G v x) ∂μ := by
    rw [gradientFluxOperator_apply]
    change (∫ x, inner ℝ (a x (G (u + t • v) x)) (G v x) ∂μ) = _
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (G u) (t • G v), Lp.coeFn_smul t (G v)]
      with x hadd hsmul
    simp only [map_add, map_smul, hadd, Pi.add_apply, hsmul, Pi.smul_apply]
  simp_rw [heq]
  exact continuousWithinAt_integral_inner_flux a hmeas hh hgrowth hhemi (G u) (G v)

/-- A positive quadratic lower bound for the flux pairing becomes a
quadratic lower bound in the full `H¹₀` norm on bounded domains. The
constant is derived from the bounded-domain Poincaré theorem. -/
theorem exists_pos_quadratic_lower_bound_gradientFluxOperator
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ p, c * ‖p‖ ^ 2 - b x ≤ inner ℝ (a x p) p) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : V, K * ‖u‖ ^ 2 - (∫ x, b x ∂μ) ≤
      gradientFluxOperator a hmeas hh hgrowth u u := by
  obtain ⟨k, hk, hP⟩ := dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded
  have hgrad (u : V) : k * ‖u‖ ^ 2 ≤ ‖G u‖ ^ 2 := by
    rw [← wkpGradientCLM_h10SubtypeL, h10SubtypeL_apply,
      norm_gradientCLM_sq_eq_sum_deriv_sq, ← dirichletForm_self_eq_sum_norm_sq]
    simpa only [pow_two, mul_assoc] using hP u
  refine ⟨c * k, mul_pos hc hk, ?_⟩
  intro u
  have hint : Integrable (fun x ↦ ‖G u x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      L2.integrable_inner (𝕜 := ℝ) (G u) (G u)
  have hnorm : (∫ x, ‖G u x‖ ^ 2 ∂μ) = ‖G u‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.inner_def (𝕜 := ℝ) (G u) (G u)).symm
  have hpoint :
      c * ‖G u‖ ^ 2 - (∫ x, b x ∂μ) ≤ gradientFluxOperator a hmeas hh hgrowth u u := by
    rw [gradientFluxOperator_apply]
    calc
      c * ‖G u‖ ^ 2 - (∫ x, b x ∂μ) =
          ∫ x, c * ‖G u x‖ ^ 2 - b x ∂μ := by
        rw [integral_sub (hint.const_mul c) hb, integral_const_mul, hnorm]
      _ ≤ ∫ x, inner ℝ (a x (G u x)) (G u x) ∂μ :=
        integral_mono_ae ((hint.const_mul c).sub hb)
          (integrable_inner_gradientFlux a hmeas hh hgrowth u u)
          (hlower.mono fun x hx ↦ hx (G u x))
  have hmul := mul_le_mul_of_nonneg_left (hgrad u) hc.le
  linarith

/-- Every continuous dual load has a weak Dirichlet solution for a
monotone, hemicontinuous gradient flux with linear growth and a positive
quadratic pairing lower bound. All integral pairings are integrable by
`integrable_inner_gradientFlux`. The solution is tested against every
element of `H¹₀`; uniqueness would require a further hypothesis. -/
theorem exists_weak_solution_of_monotone_gradientFlux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a))
    (hh : MemLp h 2 (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ p q, 0 ≤ inner ℝ (a x p - a x q) (p - q))
    (hhemi : ∀ᵐ x ∂μ, ∀ p q : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (p + t • q)) q) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ p, c * ‖p‖ ^ 2 - b x ≤ inner ℝ (a x p) p)
    (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V,
      (∫ x, inner ℝ (a x (∇ (u : H¹(Ω)) x)) (∇ (v : H¹(Ω)) x) ∂μ) = ℓ v := by
  let A := gradientFluxOperator a hmeas hh hgrowth
  obtain ⟨K, hK, hlowerA⟩ :=
    exists_pos_quadratic_lower_bound_gradientFluxOperator a hmeas hh hgrowth
      hn hΩbounded hc hb hlower
  have hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : V, R ≤ ‖u‖ → M * ‖u‖ ≤ A u u := by
    intro M hM
    let B : ℝ := ∫ x, b x ∂μ
    let R : ℝ := 1 + (M + |B|) / K
    have hquot : 0 < (M + |B|) / K := div_pos (by positivity) hK
    refine ⟨R, by dsimp [R]; linarith, ?_⟩
    intro u hu
    change 1 + (M + |B|) / K ≤ ‖u‖ at hu
    have huone : 1 ≤ ‖u‖ := by linarith
    have hprod : M + |B| ≤ K * ‖u‖ := by
      have hquotle : (M + |B|) / K ≤ ‖u‖ := by linarith
      have := (div_le_iff₀ hK).mp hquotle
      simpa only [mul_comm] using this
    have htimes := mul_le_mul_of_nonneg_right hprod (norm_nonneg u)
    have habs := mul_le_mul_of_nonneg_left huone (abs_nonneg B)
    have hlow := hlowerA u
    change K * ‖u‖ ^ 2 - B ≤ A u u at hlow
    nlinarith [le_abs_self B]
  obtain ⟨u, hu⟩ :=
    @PDE.Analysis.Operator.surjective_of_monotone_of_hemicontinuous_of_coercive
      V inferInstance inferInstance
      (@PDE.Analysis.inclusionInDoubleDual_surjective V
        inferInstance inferInstance inferInstance)
      A (gradientFluxOperator_monotone a hmeas hh hgrowth hmono)
      (gradientFluxOperator_hemicontinuous a hmeas hh hgrowth hhemi) hcoercive ℓ
  refine ⟨u, fun v ↦ ?_⟩
  rw [← gradientFluxOperator_apply a hmeas hh hgrowth u v]
  exact congrArg (fun f : StrongDual ℝ V ↦ f v) hu

end SobolevSpace.GraphSpace

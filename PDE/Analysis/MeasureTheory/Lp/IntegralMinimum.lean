/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First variation at integral minima

A conjugate-power bound on the density derivative gives integrability along each nearby
`Lᵖ` line once the density is integrable at the minimum. Fermat's theorem then makes
the first variation vanish. The real-integral formulation needs no spatial lower bound.

For a nonnegative extended-integral minimum, finiteness supplies the integrability.
A spatial lower bound is absorbed into the density before differentiating. Only
measurability of that shift is needed, since it is constant along the variation.
The state space can be any real normed space with its Borel measurable structure.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]

/-- At a local minimum along an `Lᵖ` line, the integral of the density derivative
vanishes. The density need only be integrable at the minimum: conjugate growth of
its derivative supplies nearby integrability and differentiates the integral.
No uniform lower bound on the density is required. -/
theorem MemLp.integral_derivative_eq_zero_of_isLocalMin
    {u v : α → E} (hu : MemLp u p μ) (hv : MemLp v p μ) (hp_top : p ≠ ∞)
    {F : α → E → ℝ} {dF : α → E → E →L[ℝ] ℝ} {h : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hdF : Measurable (fun z : α × E × E ↦ dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hbase : Integrable (fun x ↦ F x (u x)) μ)
    (hmin : IsLocalMin (fun t : ℝ ↦ ∫ x, F x (u x + t • v x) ∂μ) 0) :
    Integrable (fun x ↦ dF x (u x) (v x)) μ ∧
      (∫ x, dF x (u x) (v x) ∂μ) = 0 := by
  obtain ⟨_, hint, hdiff⟩ := hu.hasDerivAt_integral_of_deriv_growth
    (q := q) hv hp_top hF hdF hderiv hh hgrowth hbase
  exact ⟨hint, hmin.hasDerivAt_eq_zero hdiff⟩

/-- A linear map into `Lᵖ` may record several fields and their derivatives together.
Minimizing the resulting integral on an affine subspace gives zero first variation
in every direction of that subspace. This separates the variational argument from
the particular choice of fields or boundary condition. -/
theorem integral_firstVariation_eq_zero_of_affine_min
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Lp E p μ) (S : Submodule ℝ V)
    (hp_top : p ≠ ∞)
    {F : α → E → ℝ} {dF : α → E → E →L[ℝ] ℝ} {h : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hdF : Measurable (fun z : α × E × E ↦ dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (g u : V) (hu : u - g ∈ S)
    (hbase : Integrable (fun x ↦ F x (J u x)) μ)
    (hmin : ∀ w : V, w - g ∈ S →
      (∫ x, F x (J u x) ∂μ) ≤ ∫ x, F x (J w x) ∂μ)
    (v : V) (hv : v ∈ S) :
    Integrable (fun x ↦ dF x (J u x) (J v x)) μ ∧
      (∫ x, dF x (J u x) (J v x) ∂μ) = 0 := by
  apply (Lp.memLp (J u)).integral_derivative_eq_zero_of_isLocalMin
    (q := q) (Lp.memLp (J v)) hp_top hF hdF hderiv hh hgrowth hbase
  apply Eventually.of_forall
  intro t
  have ht : u + t • v - g ∈ S := by
    simpa only [sub_add_eq_add_sub] using S.add_mem hu (S.smul_mem t hv)
  have hrep : (fun x ↦ J (u + t • v) x) =ᵐ[μ]
      fun x ↦ J u x + t • J v x := by
    simp only [map_add, map_smul]
    filter_upwards [Lp.coeFn_add (J u) (t • J v), Lp.coeFn_smul t (J v)] with x ha hs
    simp only [ha, hs, Pi.add_apply, Pi.smul_apply]
  simpa only [zero_smul, add_zero,
    integral_congr_ae (hrep.mono fun x hx ↦ congrArg (F x) hx)] using hmin (u + t • v) ht

/-- A finite local minimum along an `Lᵖ` line has zero integral first variation.
The density derivative has conjugate power growth outside one fixed null set.
This includes `p = 1, q = ∞`, arbitrary measures, and infinite-dimensional state spaces.

No separate upper bound on the density, integrability of the shift, or derivative of
the integral functional is assumed. The minimum is formulated with a nonnegative
extended integral. -/
theorem MemLp.integral_derivative_eq_zero_of_lintegral_min
    {u v : α → E} (hu : MemLp u p μ) (hv : MemLp v p μ) (hp_top : p ≠ ∞)
    {F : α → E → ℝ} {dF : α → E → E →L[ℝ] ℝ}
    {b h : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hdF : Measurable (fun z : α × E × E ↦ dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hlower : ∀ᵐ x ∂μ, ∀ z, -b x ≤ F x z)
    (hfinite : (∫⁻ x, ENNReal.ofReal (F x (u x) + b x) ∂μ) ≠ ∞)
    (hmin : ∀ᶠ t : ℝ in 𝓝 0,
      (∫⁻ x, ENNReal.ofReal (F x (u x) + b x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (F x (u x + t • v x) + b x) ∂μ) :
    Integrable (fun x ↦ dF x (u x) (v x)) μ ∧
      (∫ x, dF x (u x) (v x) ∂μ) = 0 := by
  let H (x : α) (z : E) := F x z + b x
  have hH : Measurable (Function.uncurry H) := hF.add (hb.comp measurable_fst)
  have hHderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (H x) (dF x z) z := by
    filter_upwards [hderiv] with x hx
    intro z
    exact (hx z).add_const (b x)
  have hHnonneg : ∀ᵐ x ∂μ, ∀ z, 0 ≤ H x z := by
    filter_upwards [hlower] with x hx
    intro z
    exact neg_le_iff_add_nonneg.mp (hx z)
  have hUmeas : AEStronglyMeasurable (fun x ↦ H x (u x)) μ :=
    (hH.comp_aemeasurable
      (aemeasurable_id.prodMk hu.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hbase : Integrable (fun x ↦ H x (u x)) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hUmeas
      (hHnonneg.mono fun x hx ↦ hx (u x))).mp hfinite
  obtain ⟨hnear, hint, hdiff⟩ := hu.hasDerivAt_integral_of_deriv_growth
    (q := q) hv hp_top hH hdF hHderiv hh hgrowth hbase
  have hlocal : IsLocalMin (fun t : ℝ ↦ ∫ x, H x (u x + t • v x) ∂μ) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0,
      (∫ x, H x (u x + (0 : ℝ) • v x) ∂μ) ≤
        ∫ x, H x (u x + t • v x) ∂μ
    filter_upwards [hmin, Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t hle ht
    change (∫⁻ x, ENNReal.ofReal (H x (u x)) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (H x (u x + t • v x)) ∂μ at hle
    rw [← ofReal_integral_eq_lintegral_ofReal hbase
      (hHnonneg.mono fun x hx ↦ hx (u x)),
      ← ofReal_integral_eq_lintegral_ofReal (hnear t ht)
        (hHnonneg.mono fun x hx ↦ hx (u x + t • v x))] at hle
    have hnonneg : 0 ≤ ∫ x, H x (u x + t • v x) ∂μ :=
      integral_nonneg_of_ae (hHnonneg.mono fun x hx ↦ hx (u x + t • v x))
    simpa only [zero_smul, add_zero] using (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hle
  exact ⟨hint, hlocal.hasDerivAt_eq_zero hdiff⟩

end MeasureTheory

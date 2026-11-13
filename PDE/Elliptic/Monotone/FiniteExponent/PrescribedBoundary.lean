/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.FiniteExponent.Reaction
public import PDE.Elliptic.Monotone.FiniteExponent.Uniqueness
import PDE.Analysis.Operator.PowerGrowthTranslation

/-!
# Prescribed Sobolev boundary classes with monotone reactions

A lifting `φ ∈ W^{1,p}` specifies the affine class `φ + W^{1,p}_0`. Translating
both coefficient arguments reduces the weak equation to the zero-boundary problem.
The translated coercivity estimate is derived from the original flux bounds;
Hölder and the lifting's `Lᵖ` coordinates make all translation errors integrable.

Existence holds for `1 < p < ∞` on any bounded set in positive dimension. On an
open set the supported-core closure gives the usual Sobolev boundary class.
No classical trace, boundary regularity, potential, or vanishing reaction at zero
is assumed. Strict flux monotonicity gives uniqueness in each affine class.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Sobolev Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "q" => ENNReal.conjExponent (p : ℝ≥0∞)
local notation "V" => W₀^{1,p}(Ω)
local notation "Q" =>
  wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)

/-- A monotone coercive flux and a continuous monotone reaction of conjugate
power growth admit a weak solution in every prescribed affine Sobolev boundary
class. The lifting is an arbitrary `W^{1,p}` element. The constants and integrable
offsets for the translated equation are proved from the original coefficients. -/
theorem exists_weak_solution_monotone_wkp_prescribed_boundary
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    (g : ℝ^n → ℝ → ℝ) {h₀ : ℝ^n → ℝ} {C₀ : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh₀ : MemLp h₀ q μ)
    (hggrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h₀ x + C₀ * ‖s‖ ^ ((p : ℝ) - 1))
    (hgcont : ∀ᵐ x ∂μ, Continuous (g x))
    (hgmono : ∀ᵐ x ∂μ, Monotone (g x))
    (ℓ : StrongDual ℝ V) (φ : W^{1,p}(Ω)) :
    ∃ u : W^{1,p}(Ω), u - φ ∈ wkp0SubmoduleOn (n := n) (k := 1)
        (p := (p : ℝ≥0∞)) (Ω := Ω) ∧
      ∀ v : V, (∫ x, inner ℝ (a x (∇ u x)) (∇ (v : W^{1,p}(Ω)) x) ∂μ) +
        (∫ x, g x (Q u x) * Q (v : W^{1,p}(Ω)) x ∂μ) = ℓ v := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hr : 0 ≤ (p : ℝ) - 1 := (sub_pos.mpr hpR).le
  let dφ := ∇ φ
  let sφ := Q φ
  let aφ (x z : ℝ^n) := a x (dφ x + z)
  let gφ (x : ℝ^n) (s : ℝ) := g x (sφ x + s)
  have haφmeas : Measurable (Function.uncurry aφ) := hmeas.comp (measurable_fst.prodMk
    (((Lp.stronglyMeasurable dφ).measurable.comp measurable_fst).add measurable_snd))
  have hgφmeas : Measurable (Function.uncurry gφ) := hgmeas.comp (measurable_fst.prodMk
    (((Lp.stronglyMeasurable sφ).measurable.comp measurable_fst).add measurable_snd))
  let Cφ : ℝ := |C| * 2 ^ ((p : ℝ) - 1)
  let C₀φ : ℝ := |C₀| * 2 ^ ((p : ℝ) - 1)
  have hhφ : MemLp (fun x ↦ ‖h x‖ + Cφ * ‖dφ x‖ ^ ((p : ℝ) - 1)) q μ :=
    hh.norm.add (((Lp.memLp dφ).norm_rpow_sub_one ENNReal.coe_ne_top).const_mul Cφ)
  have hh₀φ : MemLp (fun x ↦ ‖h₀ x‖ + C₀φ * ‖sφ x‖ ^ ((p : ℝ) - 1)) q μ :=
    hh₀.norm.add (((Lp.memLp sφ).norm_rpow_sub_one ENNReal.coe_ne_top).const_mul C₀φ)
  have haφgrowth : ∀ᵐ x ∂μ, ∀ z, ‖aφ x z‖ ≤
      (‖h x‖ + Cφ * ‖dφ x‖ ^ ((p : ℝ) - 1)) + Cφ * ‖z‖ ^ ((p : ℝ) - 1) :=
    hgrowth.mono fun x hx z ↦ PDE.Analysis.Operator.norm_flux_translate_le_rpow (a x) hr hx (dφ x) z
  have hgφgrowth : ∀ᵐ x ∂μ, ∀ s, ‖gφ x s‖ ≤
      (‖h₀ x‖ + C₀φ * ‖sφ x‖ ^ ((p : ℝ) - 1)) + C₀φ * ‖s‖ ^ ((p : ℝ) - 1) :=
    hggrowth.mono fun x hx s ↦
      PDE.Analysis.Operator.norm_flux_translate_le_rpow (g x) hr hx (sφ x) s
  have haφmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (aφ x z - aφ x w) (z - w) :=
    hmono.mono fun x hx z w ↦ by
      simpa only [add_sub_add_left_eq_sub] using hx (dφ x + z) (dφ x + w)
  have haφhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (aφ x (z + t • w)) w) (Ici 0) 0 :=
    hhemi.mono fun x hx z w ↦ by simpa only [aφ, add_assoc] using hx (dφ x + z) w
  have hgφcont : ∀ᵐ x ∂μ, Continuous (gφ x) :=
    hgcont.mono fun x hx ↦ hx.comp (continuous_const.add continuous_id)
  have hgφmono : ∀ᵐ x ∂μ, Monotone (gφ x) :=
    hgmono.mono fun x hx z w hzw ↦ hx (add_le_add le_rfl hzw)
  obtain ⟨c', K, hc', _, htranslate⟩ :=
    PDE.Analysis.Operator.exists_pos_rpow_lower_bound_flux_translate (E := ℝ^n) hpR hc C
  let bφ (x : ℝ^n) := b x + ‖h x‖ * ‖dφ x‖ + K * ‖dφ x‖ ^ (p : ℝ)
  have hbφ : Integrable bφ μ := (hb.add (hh.norm.integrable_mul (Lp.memLp dφ).norm)).add
    (((Lp.memLp dφ).integrable_norm_rpow (ENNReal.HolderConjugate.ne_zero (p : ℝ≥0∞) q)
      ENNReal.coe_ne_top).const_mul K)
  have haφlower : ∀ᵐ x ∂μ, ∀ z, c' * ‖z‖ ^ (p : ℝ) - bφ x ≤ inner ℝ (aφ x z) z := by
    filter_upwards [hgrowth, hlower] with x hx hxl
    exact fun z ↦ htranslate (a x) (h x) (b x) hx hxl (dφ x) z
  obtain ⟨w, hw⟩ := exists_weak_solution_of_monotone_wkpGradientFlux_reaction
    hp aφ haφmeas hhφ haφgrowth hn hΩ haφmono haφhemi hc' hbφ haφlower
    gφ hgφmeas hh₀φ hgφgrowth hgφcont hgφmono ℓ
  refine ⟨φ + (w : W^{1,p}(Ω)), by rw [add_sub_cancel_left]; exact w.property, fun v ↦ ?_⟩
  have hgrad : ∇ (φ + (w : W^{1,p}(Ω))) =ᵐ[μ] fun x ↦ dφ x + ∇ (w : W^{1,p}(Ω)) x := by
    rw [map_add]
    exact Lp.coeFn_add dφ (∇ (w : W^{1,p}(Ω)))
  have hbase : Q (φ + (w : W^{1,p}(Ω))) =ᵐ[μ] fun x ↦ sφ x + Q (w : W^{1,p}(Ω)) x := by
    rw [map_add]
    exact Lp.coeFn_add sφ (Q (w : W^{1,p}(Ω)))
  refine Eq.trans ?_ (hw v)
  congr 1 <;> refine integral_congr_ae ?_
  · filter_upwards [hgrad] with x hx
    rw [hx]
  · filter_upwards [hbase] with x hx
    rw [hx]

/-- A strictly monotone flux and a monotone reaction determine at most one weak
solution in an affine supported-core boundary class. This comparison holds for
all finite `p ≥ 1`, including `p = 1`. It needs neither continuity nor coercivity:
subtracting the equations makes the tested flux difference nonpositive, so the
strict-flux comparison theorem applies. -/
theorem eq_of_strictMonotone_wkpGradientFlux_reaction
    (hp : 1 ≤ p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ z w, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w))
    (g : ℝ^n → ℝ → ℝ) {h₀ : ℝ^n → ℝ} {C₀ : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh₀ : MemLp h₀ q μ)
    (hggrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h₀ x + C₀ * ‖s‖ ^ ((p : ℝ) - 1))
    (hgmono : ∀ᵐ x ∂μ, Monotone (g x))
    (ℓ : V → ℝ) (u v : W^{1,p}(Ω))
    (huv : u - v ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω))
    (hu : ∀ z : V, (∫ x, inner ℝ (a x (∇ u x)) (∇ (z : W^{1,p}(Ω)) x) ∂μ) +
      (∫ x, g x (Q u x) * Q (z : W^{1,p}(Ω)) x ∂μ) = ℓ z)
    (hv : ∀ z : V, (∫ x, inner ℝ (a x (∇ v x)) (∇ (z : W^{1,p}(Ω)) x) ∂μ) +
      (∫ x, g x (Q v x) * Q (z : W^{1,p}(Ω)) x ∂μ) = ℓ z) :
    u = v := by
  let w : V := ⟨u - v, huv⟩
  have hgrad : ∇ (w : W^{1,p}(Ω)) =ᵐ[μ] fun x ↦ ∇ u x - ∇ v x := by
    change ∇ (u - v) =ᵐ[μ] fun x ↦ ∇ u x - ∇ v x
    rw [map_sub]
    exact Lp.coeFn_sub (∇ u) (∇ v)
  have hbase : Q (w : W^{1,p}(Ω)) =ᵐ[μ] fun x ↦ Q u x - Q v x := by
    change Q (u - v) =ᵐ[μ] fun x ↦ Q u x - Q v x
    rw [map_sub]
    exact Lp.coeFn_sub (Q u) (Q v)
  have hgu := integrable_wkpNemytskii_test g hgmeas hh₀ hggrowth u (w : W^{1,p}(Ω))
  have hgv := integrable_wkpNemytskii_test g hgmeas hh₀ hggrowth v (w : W^{1,p}(Ω))
  have hreaction : 0 ≤ (∫ x, g x (Q u x) * Q (w : W^{1,p}(Ω)) x ∂μ) -
      (∫ x, g x (Q v x) * Q (w : W^{1,p}(Ω)) x ∂μ) := by
    rw [← integral_sub hgu hgv]
    apply integral_nonneg_of_ae
    filter_upwards [hgmono, hbase] with x hx hbx
    rw [← sub_mul, hbx]
    exact (hx.monovary monotone_id).sub_mul_sub_nonneg (Q v x) (Q u x)
  apply eq_of_strictMonotone_wkpGradientFlux_of_pairing_le
    hp a hmeas hh hgrowth hn hΩ hstrict u v huv
  have hIu := integrable_inner_wkpGradientFlux ENNReal.coe_ne_top a hmeas hh hgrowth u w.1
  have hIv := integrable_inner_wkpGradientFlux ENNReal.coe_ne_top a hmeas hh hgrowth v w.1
  calc
    _ = (∫ x, inner ℝ (a x (∇ u x)) (∇ (w : W^{1,p}(Ω)) x) ∂μ) -
          (∫ x, inner ℝ (a x (∇ v x)) (∇ (w : W^{1,p}(Ω)) x) ∂μ) := by
      rw [← integral_sub hIu hIv]
      apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      rw [hx, inner_sub_left]
    _ ≤ 0 := by linarith [hu w, hv w]

/-- Strict flux monotonicity gives exactly one weak solution in each prescribed
Sobolev boundary class under the finite-exponent existence hypotheses. The same
constructed solution satisfies the flux-reaction equation for every zero-boundary
test function and the specified affine boundary condition. -/
theorem existsUnique_weak_solution_strictMonotone_wkp_prescribed_boundary
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ z w, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    (g : ℝ^n → ℝ → ℝ) {h₀ : ℝ^n → ℝ} {C₀ : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh₀ : MemLp h₀ q μ)
    (hggrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h₀ x + C₀ * ‖s‖ ^ ((p : ℝ) - 1))
    (hgcont : ∀ᵐ x ∂μ, Continuous (g x))
    (hgmono : ∀ᵐ x ∂μ, Monotone (g x))
    (ℓ : StrongDual ℝ V) (φ : W^{1,p}(Ω)) :
    ∃! u : W^{1,p}(Ω), u - φ ∈ wkp0SubmoduleOn (n := n) (k := 1)
        (p := (p : ℝ≥0∞)) (Ω := Ω) ∧
      ∀ v : V, (∫ x, inner ℝ (a x (∇ u x)) (∇ (v : W^{1,p}(Ω)) x) ∂μ) +
        (∫ x, g x (Q u x) * Q (v : W^{1,p}(Ω)) x ∂μ) = ℓ v := by
  have hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w) :=
    hstrict.mono fun x hx z w ↦ (eq_or_ne z w).elim (fun h ↦ by simp [h]) fun h ↦ (hx z w h).le
  obtain ⟨u, hu⟩ := exists_weak_solution_monotone_wkp_prescribed_boundary
    hp a hmeas hh hgrowth hn hΩ hmono hhemi hc hb hlower
    g hgmeas hh₀ hggrowth hgcont hgmono ℓ φ
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  apply eq_of_strictMonotone_wkpGradientFlux_reaction hp.le a hmeas hh hgrowth
    hn hΩ hstrict g hgmeas hh₀ hggrowth hgmono (fun z ↦ ℓ z) v u ?_ hv.2 hu.2
  change v - u ∈
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  simpa only [sub_sub_sub_cancel_right] using
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
      (Ω := Ω)).toSubmodule.sub_mem hv.1 hu.1

end SobolevSpace.GraphSpace

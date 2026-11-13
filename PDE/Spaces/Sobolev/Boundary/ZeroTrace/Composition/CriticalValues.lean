/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Composition.Smooth
public import PDE.Analysis.Calculus.Primitive.Localization
public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent

/-!
# Critical values of potentials on the zero-boundary Sobolev space

If the derivative of a smooth scalar potential vanishes on the values of a
zero-boundary Sobolev function, that potential equals its value at zero almost
everywhere. We apply Poincaré to bounded-slope localized primitives, then exhaust
the real line by countably many intervals. The potential itself need not define
a Sobolev function. No connectedness or boundary regularity is required.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal}
variable [Fact (1 ≤ (p : ℝ≥0∞))]

/-- A bounded-slope composition whose chain-rule coefficient vanishes is zero
almost everywhere on a bounded domain, by the zero-boundary Poincaré inequality. -/
theorem comp_ae_eq_zero_of_deriv_ae_eq_zero
    (hn : 0 < n) (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (hp : 1 ≤ p)
    {F F' : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF' : Continuous F')
    (hd : ∀ s, HasDerivAt F (F' s) s) (hzero : F 0 = 0)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ s, |F' s| ≤ M)
    (u : W₀^{1,p}(Ω))
    (hcritical : (fun x ↦ F' (wkpCoordinateCLM (baseIndex n 1)
      (u : W^{1,p}(Ω)) x)) =ᵐ[domainMeasure n Ω] 0) :
    (fun x ↦ F (wkpCoordinateCLM (baseIndex n 1)
      (u : W^{1,p}(Ω)) x)) =ᵐ[domainMeasure n Ω] 0 := by
  let f : ℝ → ℝ := fun s ↦ F s / M
  let f' : ℝ → ℝ := fun s ↦ F' s / M
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hF.div_const M
  have hf' : Continuous f' := hF'.div_const M
  have hdf (s : ℝ) : HasDerivAt f (f' s) s := (hd s).div_const M
  have hfzero : f 0 = 0 := by simp [f, hzero]
  have hfbound (s : ℝ) : |f' s| ≤ 1 := by
    dsimp [f']
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).mpr (hbound s)
  have hfLip : LipschitzWith 1 f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun s ↦ (hdf s).differentiableAt)
    intro s
    rw [(hdf s).deriv]
    exact_mod_cast hfbound s
  let w := smoothCompositionWkp0 hΩ ENNReal.coe_ne_top hf hf' hdf hfzero hfLip hfbound u
  have hwderiv (i : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n i) (w : W^{1,p}(Ω)) = 0 := by
    apply Lp.ext
    filter_upwards
      [smoothCompositionWkp0_derivative_ae hΩ ENNReal.coe_ne_top
        hf hf' hdf hfzero hfLip hfbound u i, hcritical,
       Lp.coeFn_zero ℝ (p : ℝ≥0∞) (domainMeasure n Ω)]
      with x hx hc hz
    change _ = 0 at hc
    simpa only [f', hc, zero_div, zero_mul, hz, Pi.zero_apply] using hx
  obtain ⟨C, hP⟩ := exists_poincare_Wkp0 hn hΩb hp
  have hnorm := hP w
  change ‖wkpCoordinateCLM (baseIndex n 1) (w : W^{1,p}(Ω))‖ ≤
    (C : ℝ) * ∑ i : Fin n,
      ‖wkpCoordinateCLM (singleDerivIndex n i) (w : W^{1,p}(Ω))‖ at hnorm
  simp only [hwderiv, norm_zero, Finset.sum_const_zero, mul_zero] at hnorm
  have hwbase : wkpCoordinateCLM (baseIndex n 1) (w : W^{1,p}(Ω)) = 0 :=
    norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  have hbase := smoothCompositionWkp0_base_ae hΩ ENNReal.coe_ne_top
    hf hf' hdf hfzero hfLip hfbound u
  change (wkpCoordinateCLM (baseIndex n 1) (w : W^{1,p}(Ω)) : ℝ^n → ℝ) =ᵐ[
    domainMeasure n Ω] _ at hbase
  rw [hwbase] at hbase
  filter_upwards [hbase, Lp.coeFn_zero ℝ (p : ℝ≥0∞) (domainMeasure n Ω)]
    with x hx hz
  have hquot : F (wkpCoordinateCLM (baseIndex n 1)
      (u : W^{1,p}(Ω)) x) / M = 0 := hx.symm.trans hz
  exact (div_eq_zero_iff).mp hquot |>.resolve_right hM.ne'

/-- A smooth potential with vanishing derivative along a zero-boundary
Sobolev function takes its boundary value almost everywhere. No growth bound on
the potential is needed: only bounded-slope localized primitives are composed. -/
theorem potential_ae_eq_at_zero_of_deriv_ae_eq_zero
    (hn : 0 < n) (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (hp : 1 ≤ p)
    {G g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hd : ∀ s, HasDerivAt G (g s) s)
    (u : W₀^{1,p}(Ω))
    (hcritical : (fun x ↦ g (wkpCoordinateCLM (baseIndex n 1)
      (u : W^{1,p}(Ω)) x)) =ᵐ[domainMeasure n Ω] 0) :
    (fun x ↦ G (wkpCoordinateCLM (baseIndex n 1)
      (u : W^{1,p}(Ω)) x)) =ᵐ[domainMeasure n Ω] fun _ ↦ G 0 := by
  have hlocal (j : ℕ) : ∀ᵐ x ∂domainMeasure n Ω,
      |wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω)) x| ≤ (j : ℝ) + 1 →
        G (wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω)) x) = G 0 := by
    obtain ⟨F, F', M, hM, hF, hF', hdF, hFzero, hbound, hcrit, heq⟩ :=
      PDE.Analysis.exists_localized_primitive hg hd
        (show 0 < (j : ℝ) + 1 by positivity)
    have hc : (fun x ↦ F' (wkpCoordinateCLM (baseIndex n 1)
        (u : W^{1,p}(Ω)) x)) =ᵐ[domainMeasure n Ω] 0 := by
      filter_upwards [hcritical] with x hx
      exact hcrit _ hx
    have hz := comp_ae_eq_zero_of_deriv_ae_eq_zero hn hΩ hΩb hp
      hF hF'.continuous hdF hFzero hM hbound u hc
    filter_upwards [hz] with x hx hle
    exact sub_eq_zero.mp ((heq _ hle).symm.trans hx)
  filter_upwards [ae_all_iff.mpr hlocal] with x hx
  obtain ⟨j, hj⟩ := exists_nat_gt
    |wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω)) x|
  exact hx j (by linarith)

end SobolevSpace.GraphSpace

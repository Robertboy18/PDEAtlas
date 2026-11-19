/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ScalarPartials
public import PDE.Analysis.Normed.Operator.PowerGrowth
public import PDE.CalculusOfVariations.EulerLagrange.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Coordinate first variation for coupled integral energies

The state records a finite family of value-gradient pairs. The growth bounds use
the Euclidean norm of the values and the Euclidean norm of all gradient entries.
Continuous linear maps to these two spaces transport the growth bounds to the
maximum norm used by the Sobolev first jet.

The value and row-gradient coefficients are the partial derivatives of the density. Pointwise
differentiability of the density identifies their finite sum with its full differential. No
differentiability of the energy is assumed. The conclusion is the sum of integrals defining
a weak solution of the Euler–Lagrange system (45) in Evans, §8.2.4(a), Theorem 7.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(a), Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped Sobolev ENNReal

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)
local notation "J" =>
  (fun w : ι → W^{1,p}(Ω) ↦ fun x : ℝ^n ↦ fun i : ι ↦ (B (w i) x, ∇ (w i) x))

include q

/-- A coupled ordinary-energy minimum satisfies the Euler–Lagrange system in
coordinates. Separate Euclidean growth bounds supply integrability of each equation
and justify every zero-boundary Sobolev variation. -/
theorem sum_integral_eulerLagrange_eq_zero_of_vectorWkpIntegral_minimizer
    [IsFiniteMeasure μ] (hp_top : p ≠ ∞)
    {F : ℝ^n → (ι → ℝ × ℝ^n) → ℝ}
    {A : ℝ^n → (ι → ℝ × ℝ^n) → ι → ℝ}
    {D : ℝ^n → (ι → ℝ × ℝ^n) → ι → ℝ^n}
    {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F))
    (hA : Measurable (Function.uncurry A))
    (hD : Measurable (Function.uncurry D))
    (hdiff : ∀ᵐ x ∂μ, Differentiable ℝ (F x))
    (hvalue : ∀ᵐ x ∂μ, ∀ z i, HasDerivAt
      (fun t ↦ F x (Function.update z i (t, (z i).2))) (A x z i) (z i).1)
    (hgradient : ∀ᵐ x ∂μ, ∀ z i, HasFDerivAt
      (fun y ↦ F x (Function.update z i ((z i).1, y)))
        (innerSL ℝ (D x z i)) (z i).2)
    (hAcont : ∀ᵐ x ∂μ, Continuous (A x))
    (hDcont : ∀ᵐ x ∂μ, Continuous (D x))
    (hupper : ∀ᵐ x ∂μ, ∀ z, ‖F x z‖ ≤ C *
      (‖WithLp.toLp 2 (fun i ↦ (z i).1)‖ ^ p.toReal +
        ‖WithLp.toLp 2 (fun i ↦ (z i).2)‖ ^ p.toReal + 1))
    (hAgrowth : ∀ᵐ x ∂μ, ∀ z, ‖WithLp.toLp 2 (A x z)‖ ≤ C *
      (‖WithLp.toLp 2 (fun i ↦ (z i).1)‖ ^ (p.toReal - 1) +
        ‖WithLp.toLp 2 (fun i ↦ (z i).2)‖ ^ (p.toReal - 1) + 1))
    (hDgrowth : ∀ᵐ x ∂μ, ∀ z, ‖WithLp.toLp 2 (D x z)‖ ≤ C *
      (‖WithLp.toLp 2 (fun i ↦ (z i).1)‖ ^ (p.toReal - 1) +
        ‖WithLp.toLp 2 (fun i ↦ (z i).2)‖ ^ (p.toReal - 1) + 1))
    (g u : ι → W^{1,p}(Ω)) (hu : ∀ i, u i - g i ∈ S)
    (hmin : ∀ w : ι → W^{1,p}(Ω), (∀ i, w i - g i ∈ S) →
      (∫ x, F x (J u x) ∂μ) ≤ ∫ x, F x (J w x) ∂μ)
    (v : ι → W^{1,p}(Ω)) (hv : ∀ i, v i ∈ S) :
    (∀ k, Integrable (fun x ↦
      (∑ i, D x (J u x) k i * ∇ (v k) x i) + A x (J u x) k * B (v k) x) μ) ∧
      (∑ k, ∫ x, (∑ i, D x (J u x) k i * ∇ (v k) x i) +
        A x (J u x) k * B (v k) x ∂μ) = 0 := by
  let T₀ : (ι → ℝ × ℝ^n) →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦
        (ContinuousLinearMap.fst ℝ ℝ (ℝ^n)).comp (ContinuousLinearMap.proj i))
  let T₁ : (ι → ℝ × ℝ^n) →L[ℝ] PiLp 2 (fun _ : ι ↦ ℝ^n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ^n)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦
        (ContinuousLinearMap.snd ℝ ℝ (ℝ^n)).comp (ContinuousLinearMap.proj i))
  let K (r : ℝ) := C * (‖T₀‖ ^ r + ‖T₁‖ ^ r)
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top (ENNReal.HolderConjugate.one_le p q)
  have hbound (r : ℝ) (hr : 0 ≤ r) (z : ι → ℝ × ℝ^n) :
      C * (‖WithLp.toLp 2 (fun i ↦ (z i).1)‖ ^ r +
        ‖WithLp.toLp 2 (fun i ↦ (z i).2)‖ ^ r + 1) ≤ C + K r * ‖z‖ ^ r :=
    T₀.mul_add_norm_rpow_le T₁ hr hC z
  have hupper' : ∀ᵐ x ∂μ, ∀ z, ‖F x z‖ ≤ C + K p.toReal * ‖z‖ ^ p.toReal :=
    hupper.mono fun x hx z ↦ (hx z).trans (hbound _ ENNReal.toReal_nonneg z)
  have hA' : ∀ᵐ x ∂μ, ∀ z i, |A x z i| ≤ C + K (p.toReal - 1) *
      ‖z‖ ^ (p.toReal - 1) := by
    filter_upwards [hAgrowth] with x hx
    intro z i
    exact (PiLp.norm_apply_le (WithLp.toLp 2 (A x z)) i).trans
      ((hx z).trans (hbound _ (sub_nonneg.mpr hp1) z))
  have hD' : ∀ᵐ x ∂μ, ∀ z i, ‖D x z i‖ ≤ C + K (p.toReal - 1) *
      ‖z‖ ^ (p.toReal - 1) := by
    filter_upwards [hDgrowth] with x hx
    intro z i
    exact (PiLp.norm_apply_le (WithLp.toLp 2 (D x z)) i).trans
      ((hx z).trans (hbound _ (sub_nonneg.mpr hp1) z))
  let dF (x : ℝ^n) (z : ι → ℝ × ℝ^n) :=
    ∑ i, ((ContinuousLinearMap.toSpanSingleton ℝ (A x z i)).coprod
      (innerSL ℝ (D x z i))).comp (ContinuousLinearMap.proj i)
  have happly (x : ℝ^n) (z w : ι → ℝ × ℝ^n) :
      dF x z w = ∑ i, (inner ℝ (D x z i) (w i).2 + A x z i * (w i).1) := by
    simp only [dF, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, innerSL_apply_apply, mul_comm, add_comm]
  have hfull : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z := by
    filter_upwards [hdiff, hvalue, hgradient, hAcont, hDcont] with x hx hvx hgx hAx hDx
    intro z
    exact hasFDerivAt_of_continuous_component_partials hvx hgx
      (fun i ↦ (continuous_apply i).comp hAx) (fun i ↦ (continuous_apply i).comp hDx)
      z (hx z)
  have hmeas : Measurable (fun z :
      (ℝ^n) × (ι → ℝ × ℝ^n) × (ι → ℝ × ℝ^n) ↦ dF z.1 z.2.1 z.2.2) := by
    simp only [dF, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    apply Finset.measurable_sum
    intro i hi
    have hs : Measurable (fun z :
        (ℝ^n) × (ι → ℝ × ℝ^n) × (ι → ℝ × ℝ^n) ↦ (z.1, z.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    exact measurable_toSpanSingleton_coprod_innerSL_apply
      (((measurable_pi_apply i).comp hA).comp hs)
      (((measurable_pi_apply i).comp hD).comp hs)
      (((measurable_pi_apply i).comp measurable_snd.snd).fst)
      (((measurable_pi_apply i).comp measurable_snd.snd).snd)
  have hnorm (x : ℝ^n) (z : ι → ℝ × ℝ^n) :
      ‖dF x z‖ ≤ ∑ i, (|A x z i| + ‖D x z i‖) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ ↦ by positivity)
    intro w
    simp only [dF, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    let L := (ContinuousLinearMap.toSpanSingleton ℝ (A x z i)).coprod (innerSL ℝ (D x z i))
    exact (L.le_opNorm (w i)).trans (mul_le_mul
      (norm_toSpanSingleton_coprod_innerSL_le _ _) (norm_le_pi_norm w i)
      (norm_nonneg _) (by positivity))
  have hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤
      (Fintype.card ι : ℝ) * (2 * C) +
        ((Fintype.card ι : ℝ) * (2 * K (p.toReal - 1))) * ‖z‖ ^ (p.toReal - 1) := by
    filter_upwards [hA', hD'] with x hAx hDx
    intro z
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) ↦
      add_le_add (hAx z i) (hDx z i)
    have hn := (hnorm x z).trans hs
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← two_mul, mul_add, mul_assoc] using hn
  have hzero := (integral_firstVariation_eq_zero_of_vectorWkpIntegral_minimizer
    (p := p) (q := q) hp_top hF hmeas hfull (integrable_const C) hupper'
    (memLp_const ((Fintype.card ι : ℝ) * (2 * C))) hgrowth g u hu hmin v hv).2
  have hjet : MemLp (J u) p μ := memLp_pi_iff.mpr fun i ↦
    memLp_prod_iff.mpr ⟨Lp.memLp (B (u i)), Lp.memLp (∇ (u i))⟩
  have hrow (k : ι) : Integrable (fun x ↦
      inner ℝ (D x (J u x) k) (∇ (v k) x) + A x (J u x) k * B (v k) x) μ := by
    have ha : MemLp (fun x ↦ A x (J u x) k) q μ :=
      hjet.comp_of_norm_rpow_sub_one_le (a := fun x z ↦ A x z k)
        hp_top ((measurable_pi_apply k).comp hA)
        (memLp_const C) (hA'.mono fun x hx z ↦ hx z k)
    have hd : MemLp (fun x ↦ D x (J u x) k) q μ :=
      hjet.comp_of_norm_rpow_sub_one_le (a := fun x z ↦ D x z k)
        hp_top ((measurable_pi_apply k).comp hD)
        (memLp_const C) (hD'.mono fun x hx z ↦ hx z k)
    have hi : Integrable (fun x ↦ inner ℝ (D x (J u x) k) (∇ (v k) x)) μ :=
      (hd.norm.integrable_mul (Lp.memLp (∇ (v k))).norm).mono'
        (hd.aestronglyMeasurable.inner (Lp.aestronglyMeasurable (∇ (v k))))
        (Filter.Eventually.of_forall fun x ↦ norm_inner_le_norm _ _)
    exact hi.add (ha.integrable_mul (Lp.memLp (B (v k))))
  simp_rw [happly] at hzero
  rw [integral_finsetSum _ (fun i _ ↦ hrow i)] at hzero
  have hinner (a b : ℝ^n) : inner ℝ a b = ∑ i, a i * b i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  simpa only [hinner] using And.intro hrow hzero

end PDE.CalculusOfVariations

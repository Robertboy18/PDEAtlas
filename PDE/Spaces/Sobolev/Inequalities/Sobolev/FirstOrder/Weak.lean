/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Quantitative Sobolev inequality for weak first derivatives

Compact smooth approximation and Fatou extend the homogeneous Sobolev
inequality to specified weak derivatives. The approximation preserves the
original constant; the right-hand side contains only derivative norms.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SobolevSpace.Inequalities

/-- The homogeneous Sobolev bound for specified weak first derivatives. Smooth
approximation and Fatou retain the same constant and do not add a base norm. -/
theorem eLpNorm_le_sum_eLpNorm_weakDeriv {n : ℕ} {p q : NNReal}
    (hp : 1 ≤ p) (hn : 0 < n)
    (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹)
    {f : ℝ^n → ℝ} {g : Fin n → ℝ^n → ℝ}
    (hf : MemLp f p volume) (hg : ∀ i, MemLp (g i) p volume)
    (hw : ∀ i, HasWeakDerivativeOn univ [i] f (g i)) :
    eLpNorm f q volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) (p : ℝ) : ℝ≥0∞) *
        ∑ i, eLpNorm (g i) p volume := by
  classical
  have hpE : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  let : Fact ((1 : ℝ≥0∞) ≤ (p : ℝ≥0∞)) := ⟨hpE⟩
  let u : GlobalSobolevSpace n 1 p :=
    { toFun := f
      memLp := by simpa only [domainMeasure, Measure.restrict_univ] using hf
      weak_derivs_inLp := by
        intro α hα
        cases α with
        | nil =>
          exact ⟨f, by simpa only [domainMeasure, Measure.restrict_univ] using hf,
            hasWeakDerivativeOn_nil ((hf.locallyIntegrable hpE).locallyIntegrableOn univ)⟩
        | cons i α =>
          have hz : α = [] := List.length_eq_zero_iff.mp (by simpa using hα)
          subst α
          exact ⟨g i, by simpa only [domainMeasure, Measure.restrict_univ] using hg i, hw i⟩ }
  obtain ⟨v, hv, hvc, hvf, hvd⟩ := Approximation.globalApproximation_Wkp
    (Approximation.standardMollifier n) (p : ℝ≥0∞) (by simp) 1 u
  have hderiv (i : Fin n) : Tendsto
      (fun m ↦ eLpNorm (fun x ↦ (∂[i] (v m)) x - g i x) p volume) atTop (𝓝 0) := by
    obtain ⟨d, _, hd, hlim⟩ := hvd [i] (by simp)
    have he : d =ᵐ[volume] g i := by
      simpa only [domainMeasure, Measure.restrict_univ] using hd.unique_ae isOpen_univ (hw i)
    apply hlim.congr'
    filter_upwards with m
    apply eLpNorm_congr_ae
    filter_upwards [he] with x hx
    simp only [iteratedPartialDeriv, hx]
  let C : ℝ≥0∞ := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) (p : ℝ)
  let B (m : ℕ) : ℝ≥0∞ := C * ∑ i,
    (eLpNorm (fun x ↦ (∂[i] (v m)) x - g i x) p volume + eLpNorm (g i) p volume)
  have hbound (m : ℕ) : eLpNorm (v m) q volume ≤ B m := by
    refine (eLpNorm_le_sum_eLpNorm_partialDeriv_of_eq
      ((hv m).of_le (by simp)) (hvc m) hp hn hq).trans ?_
    apply mul_le_mul_right
    apply Finset.sum_le_sum
    intro i _
    calc
      eLpNorm (∂[i] (v m)) p volume =
          eLpNorm ((fun x ↦ (∂[i] (v m)) x - g i x) + g i) p volume := by
        congr 1
        funext x
        exact (sub_add_cancel _ _).symm
      _ ≤ _ := eLpNorm_add_le hpE
  have hlimit : Tendsto B atTop (𝓝 (C * ∑ i, eLpNorm (g i) p volume)) := by
    apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.coe_ne_top)
    have hi (i : Fin n) (_ : i ∈ Finset.univ) :=
      (hderiv i).add_const (eLpNorm (g i) p volume)
    simpa only [zero_add] using tendsto_finsetSum Finset.univ hi
  have hinMeasure : TendstoInMeasure volume v atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (ne_of_gt (lt_of_lt_of_le (by simp) hpE)) hvf
  obtain ⟨φ, hφ, hφlim⟩ := hinMeasure.exists_seq_tendsto_ae
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (q : ℝ≥0∞))
    (fun m ↦ (hv (φ m)).continuous.aestronglyMeasurable) f hf.aestronglyMeasurable hφlim
  exact hfatou.trans ((Filter.liminf_le_liminf (.of_forall fun m ↦ hbound (φ m))).trans_eq
    (hlimit.comp hφ.tendsto_atTop).liminf_eq)

end SobolevSpace.Inequalities

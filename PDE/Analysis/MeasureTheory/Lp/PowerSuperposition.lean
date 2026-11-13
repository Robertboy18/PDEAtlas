/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition
import Mathlib.Tactic.Positivity.Finset

/-!
# Power growth and continuity between Lebesgue spaces

Taking the `r`th power of the norm of an a.e. strongly measurable function
changes the natural integrability exponent from `p` to `p/r`. For the restrictions
in Vitali's criterion, finite seminorm bounds provide the required measurability.
The identity therefore transfers both control on sets of small measure and control
outside a common set of finite measure.

In particular the norm-power map is continuous. A continuous nonlinear density with the same
power growth is then handled by the superposition theorem. The measure can be infinite; the
offset must belong to the target Lebesgue space.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p : ℝ≥0∞} {r : ℝ}

/-- A positive norm power commutes with restriction. Measurability of the
restricted function is sufficient for the seminorm identity; the function
outside the set need not be measurable. -/
private theorem eLpNorm_indicator_norm_rpow (hr : 0 < r) (s : Set α) (f : α → E)
    (hf : AEStronglyMeasurable (s.indicator f) μ) :
    eLpNorm (s.indicator (fun x ↦ ‖f x‖ ^ r)) (p / ENNReal.ofReal r) μ =
      eLpNorm (s.indicator f) p μ ^ r := by
  have heq : s.indicator (fun x ↦ ‖f x‖ ^ r) =
      fun x ↦ ‖s.indicator f x‖ ^ r := by
    funext x
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, norm_zero, Real.zero_rpow hr.ne']
  rw [heq, eLpNorm_norm_rpow _ hf hr, div_eq_mul_inv, mul_assoc,
    ENNReal.inv_mul_cancel (by positivity : ENNReal.ofReal r ≠ 0)
      ENNReal.ofReal_ne_top, mul_one]

/-- Uniform integrability passes to positive norm powers at the divided
exponent. Each finite restricted seminorm bound supplies local measurability;
no global measurability or finite-measure hypothesis is required. -/
theorem UnifIntegrable.norm_rpow {ι : Type*} {f : ι → α → E}
    (hf : UnifIntegrable f p μ) (hr : 0 < r) :
    UnifIntegrable (fun i x ↦ ‖f i x‖ ^ r) (p / ENNReal.ofReal r) μ := by
  rw [unifIntegrable_iff'] at hf ⊢
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | hεtop
  · exact ⟨1, zero_lt_one, fun _ _ _ _ ↦ le_top⟩
  have hrinv : 0 ≤ 1 / r := (one_div_pos.mpr hr).le
  obtain ⟨δ, hδ, hfδ⟩ := hf (ε ^ (1 / r))
    (ENNReal.rpow_pos_of_nonneg hε hrinv)
  refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
  have hbound : eLpNorm (s.indicator (f i)) p μ ≤ ε ^ (1 / r) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    exact hfδ i s hs hμs
  have hmem : MemLp (s.indicator (f i)) p μ :=
    hbound.trans_lt (ENNReal.rpow_lt_top_of_nonneg hrinv hεtop.ne)
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
    eLpNorm_indicator_norm_rpow hr s (f i) hmem.aestronglyMeasurable]
  calc
    _ ≤ (ε ^ (1 / r)) ^ r := ENNReal.rpow_le_rpow hbound hr.le
    _ = ε := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

/-- Uniform tightness passes to positive norm powers at the divided
exponent. The finite tail bound ensures measurability of that tail, and the
same finite-measure set controls its norm power. -/
theorem UnifTight.norm_rpow {ι : Type*} {f : ι → α → E}
    (hf : UnifTight f p μ) (hr : 0 < r) :
    UnifTight (fun i x ↦ ‖f i x‖ ^ r) (p / ENNReal.ofReal r) μ := by
  rw [unifTight_iff_real] at hf ⊢
  intro ε hε
  obtain ⟨s, hμs, hfs⟩ := hf (ε ^ (1 / r)) (Real.rpow_pos_of_pos hε (1 / r))
  refine ⟨s, hμs, fun i ↦ ?_⟩
  have hmem : MemLp (sᶜ.indicator (f i)) p μ :=
    (hfs i).trans_lt ENNReal.ofReal_lt_top
  rw [eLpNorm_indicator_norm_rpow hr sᶜ (f i) hmem.aestronglyMeasurable]
  calc
    _ ≤ (ENNReal.ofReal (ε ^ (1 / r))) ^ r :=
      ENNReal.rpow_le_rpow (hfs i) hr.le
    _ = ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε.le _) hr.le,
        ← Real.rpow_mul hε.le, div_mul_cancel₀ _ hr.ne', Real.rpow_one]

namespace Lp

/-- The norm power of an `Lᵖ` function, in its natural target space. -/
def normRpow {p : ℝ≥0∞} {s : ℝ} (hs : 0 ≤ s) (u : Lp ℝ p μ) :
    Lp ℝ (p / ENNReal.ofReal s) μ :=
  (show MemLp (fun x ↦ ‖u x‖ ^ s) (p / ENNReal.ofReal s) μ by
    simpa only [ENNReal.toReal_ofReal hs] using
      (Lp.memLp u).norm_rpow_div (ENNReal.ofReal s)).toLp _

/-- The bundled norm power has the expected almost-everywhere representative. -/
theorem coeFn_normRpow {p : ℝ≥0∞} {s : ℝ} (hs : 0 ≤ s) (u : Lp ℝ p μ) :
    normRpow hs u =ᵐ[μ] fun x ↦ ‖u x‖ ^ s :=
  MemLp.coeFn_toLp _

/-- Raising a function's norm to a positive power raises its `Lᵖ` norm
to that power when the target exponent is divided by the same number. -/
theorem norm_normRpow {p : ℝ≥0∞} {s : ℝ} (hs : 0 < s) (u : Lp ℝ p μ) :
    ‖normRpow hs.le u‖ = ‖u‖ ^ s := by
  rw [normRpow, Lp.norm_toLp, eLpNorm_norm_rpow _ (Lp.aestronglyMeasurable u) hs]
  have hs0 : ENNReal.ofReal s ≠ 0 := by positivity
  rw [div_eq_mul_inv, mul_assoc,
    ENNReal.inv_mul_cancel hs0 ENNReal.ofReal_ne_top, mul_one,
    ← ENNReal.toReal_rpow, Lp.norm_def]

/-- The bundled positive norm power is continuous from `Lp` to `L(p/r)`
when both exponents are at least one and `p` is finite. Vitali convergence
handles powers below one as well as superlinear powers. -/
theorem continuous_normRpow [Fact (1 ≤ p)]
    [Fact (1 ≤ p / ENNReal.ofReal r)] (hp : p ≠ ∞) (hr : 0 < r) :
    Continuous (normRpow (μ := μ) (p := p) hr.le) := by
  let q := p / ENNReal.ofReal r
  have hq : q ≠ ∞ :=
    ENNReal.div_ne_top hp (by positivity : ENNReal.ofReal r ≠ 0)
  have hmem (u : Lp ℝ p μ) : MemLp (fun x ↦ ‖u x‖ ^ r) q μ := by
    simpa only [ENNReal.toReal_ofReal hr.le] using
      (Lp.memLp u).norm_rpow_div (ENNReal.ofReal r)
  rw [continuous_iff_seqContinuous]
  intro u v huv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun n ↦ hmem (u n)) _ (hmem v)).mpr
  have hconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp huv
  obtain ⟨_, hui, hut⟩ := (tendstoInMeasure_iff_tendsto_Lp
    (Fact.out : 1 ≤ p) hp (fun n ↦ Lp.memLp (u n)) (Lp.memLp v)).mpr hconv
  have huiR := hui.norm_rpow hr
  have hutR := hut.norm_rpow hr
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, _, hms⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp huv).comp hns).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ q) hq
    (fun n ↦ (hmem (u (ns (ms n)))).aestronglyMeasurable) (hmem v) ?_ ?_ ?_⟩
  · exact huiR.comp (fun i ↦ ns (ms i))
  · exact hutR.comp (fun i ↦ ns (ms i))
  · filter_upwards [hms] with x hx
    exact ((Real.continuous_rpow_const hr.le).tendsto ‖v x‖).comp hx.norm

/-- A continuous density with growth `a + C |z|^r` defines a continuous
map from `Lp` to `L(p/r)`. The offset belongs to the target space; continuity
of the norm-power bound supplies the uniform integrability and tightness.
The hypothesis `hG` supplies membership in the target space for each input. -/
theorem continuous_superposition_of_rpow_growth
    {F : Type*} [NormedAddCommGroup F]
    [Fact (1 ≤ p)] [Fact (1 ≤ p / ENNReal.ofReal r)]
    (hp : p ≠ ∞) (hr : 0 < r) {G : α → E → F}
    (hG : ∀ u : Lp E p μ, MemLp (fun x ↦ G x (u x)) (p / ENNReal.ofReal r) μ)
    (hcont : ∀ᵐ x ∂μ, Continuous (G x)) {a : α → ℝ} {C : ℝ}
    (ha : MemLp a (p / ENNReal.ofReal r) μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖G x z‖ ≤ a x + C * ‖z‖ ^ r) :
    Continuous (superposition G hG) := by
  let N : Lp E p μ → Lp ℝ p μ :=
    lipschitzWith_one_norm.compLp (_root_.norm_zero)
  let B : Lp E p μ → Lp ℝ (p / ENNReal.ofReal r) μ :=
    fun u ↦ ha.toLp a + C • normRpow hr.le (N u)
  have hBcont : Continuous B :=
    continuous_const.add (((continuous_normRpow hp hr).comp
      (lipschitzWith_one_norm.continuous_compLp (_root_.norm_zero))).const_smul C)
  have hB (u : Lp E p μ) : B u =ᵐ[μ] fun x ↦ a x + C * ‖u x‖ ^ r := by
    filter_upwards [Lp.coeFn_add (ha.toLp a) (C • normRpow hr.le (N u)),
      ha.coeFn_toLp, Lp.coeFn_smul C (normRpow hr.le (N u)),
      coeFn_normRpow hr.le (N u),
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) u]
      with x hadd ha' hsmul hrpow hnorm
    simp only [B, hadd, Pi.add_apply, ha', hsmul, Pi.smul_apply, smul_eq_mul]
    rw [hrpow]
    change a x + C * ‖N u x‖ ^ r = _
    rw [show N u x = ‖u x‖ from hnorm, norm_norm]
  refine continuous_superposition_of_continuous_bound
    (ENNReal.div_ne_top hp (by positivity : ENNReal.ofReal r ≠ 0))
    hG hcont B hBcont ?_
  intro u
  filter_upwards [hgrowth, hB u] with x hx hBx
  rw [hBx, Real.norm_eq_abs]
  exact (hx (u x)).trans (le_abs_self _)

end Lp

end MeasureTheory

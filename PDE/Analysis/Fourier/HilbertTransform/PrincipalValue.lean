/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import CAS.ExactTactic

/-!
# Real principal values for the Hilbert transform

`hilbertTruncation f x ε` is `(1 / π) ∫_{|t| > ε} f(x - t) / t dt`.
The tail is a Lebesgue integral; only the singularity at zero is interpreted as a
principal value. `HasHilbertPV f x h` records convergence as `ε → 0+`, and
`hilbertPV f x` returns that limit when it exists. For integrable `f`, every
positive truncation is integrable.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Symmetric deletion of a radius `ε` around the singularity of the real Hilbert kernel. -/
def hilbertTruncation (f : ℝ → ℝ) (x ε : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ t in {t : ℝ | ε < |t|}, f (x - t) / t

/-- The real Hilbert principal value exists and equals `h`; the tail is Lebesgue integrable. -/
def HasHilbertPV (f : ℝ → ℝ) (x h : ℝ) : Prop :=
  (∀ ε > 0, IntegrableOn (fun t ↦ f (x - t) / t) {t : ℝ | ε < |t|}) ∧
    Tendsto (hilbertTruncation f x) (𝓝[>] 0) (𝓝 h)

/-- The real Hilbert principal value, with an unspecified value when the limit does not exist. -/
def hilbertPV (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder (𝓝[>] 0) (hilbertTruncation f x)

/-- A convergent principal value determines the value of `hilbertPV`. -/
theorem HasHilbertPV.hilbertPV_eq {f : ℝ → ℝ} {x h : ℝ} (hf : HasHilbertPV f x h) :
    hilbertPV f x = h :=
  hf.2.limUnder_eq

/-- Principal values are unique. -/
theorem HasHilbertPV.unique {f : ℝ → ℝ} {x a b : ℝ}
    (ha : HasHilbertPV f x a) (hb : HasHilbertPV f x b) : a = b :=
  tendsto_nhds_unique ha.2 hb.2

/-- The punctured real line is measurable for every cutoff. -/
theorem measurableSet_hilbertCutoff (ε : ℝ) : MeasurableSet {t : ℝ | ε < |t|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

/-- The centered truncation is the usual punctured integral of `f(y)/(x-y)`. -/
theorem hilbertTruncation_eq_integral (f : ℝ → ℝ) (x ε : ℝ) :
    hilbertTruncation f x ε =
      Real.pi⁻¹ * ∫ y in {y : ℝ | ε < |x - y|}, f y / (x - y) := by
  have hs : MeasurableSet {y : ℝ | ε < |x - y|} :=
    measurableSet_lt measurable_const
      (continuous_abs.comp (continuous_const.sub continuous_id)).measurable
  unfold hilbertTruncation
  rw [← integral_indicator (measurableSet_hilbertCutoff ε), ← integral_indicator hs]
  congr 1
  convert integral_sub_left_eq_self
    ({y : ℝ | ε < |x - y|}.indicator (fun y ↦ f y / (x - y))) volume x using 1
  congr 1
  funext t
  simp [indicator]

/-- Changing an input on a null set does not change any of its truncations. -/
theorem hilbertTruncation_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (x ε : ℝ) :
    hilbertTruncation f x ε = hilbertTruncation g x ε := by
  have hcomp := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hfg
  unfold hilbertTruncation
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hcomp] with t ht
  simp only [Function.comp_apply] at ht
  rw [ht]

/-- Principal values depend only on the almost-everywhere class of the input. -/
theorem HasHilbertPV.congr_ae {f g : ℝ → ℝ} {x h : ℝ}
    (hf : HasHilbertPV f x h) (hfg : f =ᵐ[volume] g) : HasHilbertPV g x h := by
  have hcomp := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hfg
  constructor
  · intro ε hε
    apply (hf.1 ε hε).congr
    filter_upwards [ae_restrict_of_ae hcomp] with t ht
    simp only [Function.comp_apply] at ht
    rw [ht]
  · convert hf.2 using 1
    exact funext fun ε ↦ (hilbertTruncation_congr_ae hfg x ε).symm

/-- Symmetric punctures shrink to a null set as their radii tend to zero. -/
theorem aecover_hilbertCutoff :
    AECover (volume : Measure ℝ) (𝓝[>] 0) (fun ε : ℝ ↦ {t : ℝ | ε < |t|}) where
  ae_eventually_mem := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (f := fun ε : ℝ ↦ ε) tendsto_id |>.eventually_lt_const (abs_pos.mpr ht)
  measurableSet := measurableSet_hilbertCutoff

/-- Removing a shrinking symmetric interval does not change the limit of an integrable
function's integral. -/
theorem tendsto_integral_hilbertCutoff {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun ε : ℝ ↦ ∫ t in {t : ℝ | ε < |t|}, g t)
      (𝓝[>] 0) (𝓝 (∫ t, g t)) :=
  aecover_hilbertCutoff.integral_tendsto_of_countably_generated hg

/-- Absolute integrability of the full kernel suffices for existence of its principal value. -/
theorem hasHilbertPV_of_integrable {f : ℝ → ℝ} {x : ℝ}
    (hf : Integrable (fun t ↦ f (x - t) / t)) :
    HasHilbertPV f x (Real.pi⁻¹ * ∫ t, f (x - t) / t) :=
  ⟨fun _ _ ↦ hf.integrableOn, (tendsto_integral_hilbertCutoff hf).const_mul _⟩

/-- An `L¹` function has an integrable Hilbert kernel outside every positive cutoff. -/
theorem integrableOn_hilbertKernel {f : ℝ → ℝ} (hf : Integrable f)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t ↦ f (x - t) / t) {t : ℝ | ε < |t|} := by
  refine ((hf.comp_sub_left x).norm.div_const ε).integrableOn.mono'
    (((hf.comp_sub_left x).aestronglyMeasurable.div₀
      measurable_id.aestronglyMeasurable).restrict) ?_
  filter_upwards [ae_restrict_mem (measurableSet_hilbertCutoff ε)] with t ht
  simp only [norm_div, Real.norm_eq_abs]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hε ht.le

/-- Every truncation of the zero input is zero. -/
@[simp]
theorem hilbertTruncation_zero (x ε : ℝ) :
    hilbertTruncation (fun _ ↦ 0) x ε = 0 := by
  simp [hilbertTruncation]

/-- Scalar multiplication commutes with every truncation. -/
theorem hilbertTruncation_const_mul (f : ℝ → ℝ) (c x ε : ℝ) :
    hilbertTruncation (fun y ↦ c * f y) x ε = c * hilbertTruncation f x ε := by
  simp only [hilbertTruncation, mul_div_assoc, integral_const_mul]
  exact mul_left_comm _ _ _

/-- Addition commutes with a positive truncation for integrable inputs. -/
theorem hilbertTruncation_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    hilbertTruncation (fun y ↦ f y + g y) x ε =
      hilbertTruncation f x ε + hilbertTruncation g x ε := by
  simp only [hilbertTruncation, add_div]
  rw [integral_add (integrableOn_hilbertKernel hf x hε)
    (integrableOn_hilbertKernel hg x hε), mul_add]

/-- Principal values respect real scalar multiplication. -/
theorem HasHilbertPV.const_mul {f : ℝ → ℝ} {x h : ℝ}
    (hf : HasHilbertPV f x h) (c : ℝ) :
    HasHilbertPV (fun y ↦ c * f y) x (c * h) := by
  constructor
  · intro ε hε
    simpa only [IntegrableOn, mul_div_assoc] using (hf.1 ε hε).const_mul c
  · convert hf.2.const_mul c using 1
    exact funext fun ε ↦ hilbertTruncation_const_mul f c x ε

/-- Convergent principal values add. -/
theorem HasHilbertPV.add {f g : ℝ → ℝ} {x a b : ℝ}
    (ha : HasHilbertPV f x a) (hb : HasHilbertPV g x b) :
    HasHilbertPV (fun y ↦ f y + g y) x (a + b) := by
  constructor
  · intro ε hε
    simpa only [IntegrableOn, add_div] using
      Integrable.fun_add (ha.1 ε hε) (hb.1 ε hε)
  · apply (ha.2.add hb.2).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [hilbertTruncation, add_div]
    rw [integral_add (ha.1 ε hε) (hb.1 ε hε), mul_add]

/-- Translation of the input translates the evaluation point by the same amount. -/
theorem hilbertTruncation_translate (f : ℝ → ℝ) (a x ε : ℝ) :
    hilbertTruncation (fun y ↦ f (y + a)) x ε = hilbertTruncation f (x + a) ε := by
  unfold hilbertTruncation
  congr 1
  apply setIntegral_congr_fun (measurableSet_hilbertCutoff ε)
  intro t _
  cas

/-- Translation preserves convergence of the principal value. -/
theorem HasHilbertPV.translate {f : ℝ → ℝ} {a x h : ℝ}
    (hf : HasHilbertPV f (x + a) h) :
    HasHilbertPV (fun y ↦ f (y + a)) x h := by
  have heq : (fun t ↦ f ((x - t) + a) / t) = (fun t ↦ f ((x + a) - t) / t) := by
    funext t
    congr 2
    cas
  refine ⟨?_, ?_⟩
  · simpa only [heq] using hf.1
  · convert hf.2 using 1
    exact funext fun ε ↦ hilbertTruncation_translate f a x ε

end

end PDE.Analysis

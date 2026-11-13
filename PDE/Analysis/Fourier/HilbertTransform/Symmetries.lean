/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Cancellation
import CAS.ExactTactic

/-!
# Symmetries of real Hilbert principal values

Reflection reverses the sign of the Hilbert transform. Consequently odd inputs
have even transforms, and even inputs have odd transforms. All identities concern
singular integrals.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Reflection preserves integrability outside a symmetric cutoff. -/
theorem integrableOn_hilbertCutoff_neg {g : ℝ → ℝ} {ε : ℝ}
    (hg : IntegrableOn g {t : ℝ | ε < |t|}) :
    IntegrableOn (fun t ↦ g (-t)) {t : ℝ | ε < |t|} := by
  have hs : -{t : ℝ | ε < |t|} = {t : ℝ | ε < |t|} := by
    ext t
    simp
  simpa only [hs] using hg.comp_neg

/-- Reflection preserves integration over a symmetric cutoff. -/
theorem integral_hilbertCutoff_neg (g : ℝ → ℝ) (ε : ℝ) :
    (∫ t in {t : ℝ | ε < |t|}, g (-t)) =
      ∫ t in {t : ℝ | ε < |t|}, g t := by
  rw [← integral_indicator (measurableSet_hilbertCutoff ε),
    ← integral_indicator (measurableSet_hilbertCutoff ε)]
  convert integral_neg_eq_self ({t : ℝ | ε < |t|}.indicator g) volume using 1
  congr 1
  funext t
  simp [indicator]

/-- Every truncation of an odd kernel integrates to zero. -/
theorem integral_hilbertCutoff_eq_zero_of_odd {g : ℝ → ℝ}
    (hg : Function.Odd g) (ε : ℝ) :
    (∫ t in {t : ℝ | ε < |t|}, g t) = 0 := by
  have h := integral_hilbertCutoff_neg g ε
  rw [show (fun t ↦ g (-t)) = (fun t ↦ -g t) from funext hg, integral_neg] at h
  linarith

/-- An odd real function has zero Lebesgue integral. -/
theorem integral_eq_zero_of_odd {f : ℝ → ℝ} (hf : Function.Odd f) :
    (∫ y, f y) = 0 := by
  have h := integral_neg_eq_self f volume
  rw [show (fun t ↦ f (-t)) = (fun t ↦ -f t) from funext hf, integral_neg] at h
  linarith

/-- Reflection of the input reverses the sign and reflects the evaluation point. -/
theorem hilbertTruncation_reflect (f : ℝ → ℝ) (x ε : ℝ) :
    hilbertTruncation (fun y ↦ f (-y)) x ε = -hilbertTruncation f (-x) ε := by
  unfold hilbertTruncation
  rw [← integral_hilbertCutoff_neg (fun t ↦ f (-x - t) / t) ε]
  simp only [sub_neg_eq_add, div_neg, integral_neg, mul_neg, neg_neg]
  congr 1
  apply setIntegral_congr_fun (measurableSet_hilbertCutoff ε)
  intro t _
  cas

/-- Reflection transports a convergent principal value, including its integrability. -/
theorem HasHilbertPV.reflect {f : ℝ → ℝ} {x h : ℝ}
    (hf : HasHilbertPV f (-x) h) :
    HasHilbertPV (fun y ↦ f (-y)) x (-h) := by
  constructor
  · intro ε hε
    have hint := (integrableOn_hilbertCutoff_neg (hf.1 ε hε)).neg
    apply IntegrableOn.congr_fun hint (hs := measurableSet_hilbertCutoff ε)
    intro t _
    simp only [div_neg, sub_neg_eq_add]
    cas
  · convert hf.2.neg using 1
    exact funext fun ε ↦ hilbertTruncation_reflect f x ε

/-- Odd inputs have equal truncations at opposite evaluation points. -/
theorem hilbertTruncation_neg_of_odd {f : ℝ → ℝ} (hf : Function.Odd f) (x ε : ℝ) :
    hilbertTruncation f (-x) ε = hilbertTruncation f x ε := by
  have h := hilbertTruncation_reflect f x ε
  rw [show (fun y ↦ f (-y)) = (fun y ↦ (-1) * f y) from
    funext fun y ↦ by rw [hf y, neg_one_mul],
    hilbertTruncation_const_mul, neg_one_mul] at h
  exact (neg_injective h).symm

/-- The real Hilbert PV operator takes odd inputs to even functions. Equal
truncations also give the same chosen value when a PV does not exist. -/
theorem hilbertPV_even_of_odd {f : ℝ → ℝ} (hf : Function.Odd f) :
    Function.Even (hilbertPV f) := by
  intro x
  unfold hilbertPV
  congr 1
  exact funext fun ε ↦ hilbertTruncation_neg_of_odd hf x ε

/-- Even inputs have opposite truncations at opposite evaluation points. -/
theorem hilbertTruncation_neg_of_even {f : ℝ → ℝ} (hf : Function.Even f) (x ε : ℝ) :
    hilbertTruncation f (-x) ε = -hilbertTruncation f x ε := by
  have h := hilbertTruncation_reflect f x ε
  rw [show (fun y ↦ f (-y)) = f from funext hf] at h
  linarith

/-- Reflection changes the sign of the principal value of an even input. -/
theorem HasHilbertPV.neg_of_even {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Function.Even f) :
    HasHilbertPV f (-x) (-h) := by
  have hinput : HasHilbertPV f (-(-x)) h := by simpa only [neg_neg] using hpv
  have hout := hinput.reflect
  rwa [show (fun y ↦ f (-y)) = f from funext hf] at hout

/-- An even integrable input has principal value zero at the origin. -/
theorem hasHilbertPV_zero_of_even {f : ℝ → ℝ} (hf : Function.Even f)
    (hint : Integrable f) : HasHilbertPV f 0 0 := by
  refine ⟨fun _ hε ↦ integrableOn_hilbertKernel hint 0 hε, ?_⟩
  have hzero : hilbertTruncation f 0 = fun _ ↦ 0 := by
    funext ε
    have h := hilbertTruncation_neg_of_even hf 0 ε
    simp only [neg_zero] at h
    linarith
  rw [hzero]
  exact tendsto_const_nhds

/-- Odd, integrable inputs have zero mean, so the first-moment commutator vanishes. -/
theorem HasHilbertPV.mul_id_of_odd {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Integrable f) (hodd : Function.Odd f) :
    HasHilbertPV (fun y ↦ y * f y) x (x * h) :=
  hpv.mul_id_of_integral_eq_zero hf (integral_eq_zero_of_odd hodd)

end

end PDE.Analysis

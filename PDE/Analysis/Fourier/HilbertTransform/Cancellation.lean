/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue
import CAS.ExactTactic

/-!
# Coordinate commutators for real Hilbert principal values

For integrable `f`, multiplication by the coordinate satisfies
`H(y f)(x) = x Hf(x) - (1 / π) ∫ f`. In particular, zero-mean inputs commute
with multiplication by the coordinate.

If `f/y` is integrable and `Hf(x)` exists for `x ≠ 0`, the same identity gives
existence of `H(f/y)(x)` and the formula `(Hf(x) - Hf(0)) / x`.

This is the principal-value cancellation behind the identities involving `x`
in Chen, Hou and Huang, Appendix A.1, Lemma A.2.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Appendix A.1, Lemma A.2, (A.1)-(A.3). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The algebraic kernel identity underlying the first-moment commutator. -/
theorem hilbertKernel_mul_id (x t a : ℝ) (ht : t ≠ 0) :
    (x - t) * a / t = x * (a / t) - a := by
  cas using ht

/-- Multiplication of an integrable input by the coordinate still gives integrable
positive truncations, even without an integrable first moment. -/
theorem integrableOn_hilbertKernel_mul_id {f : ℝ → ℝ} (hf : Integrable f)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t ↦ (x - t) * f (x - t) / t) {t : ℝ | ε < |t|} := by
  have hint : IntegrableOn (fun t ↦ x * (f (x - t) / t) - f (x - t))
      {t : ℝ | ε < |t|} :=
    IntegrableOn.fun_sub ((integrableOn_hilbertKernel hf x hε).const_mul x)
      (hf.comp_sub_left x).integrableOn
  apply hint.congr_fun (hs := measurableSet_hilbertCutoff ε)
  intro t ht
  exact (hilbertKernel_mul_id x t (f (x - t)) (abs_pos.mp (hε.trans ht))).symm

/-- At a finite positive cutoff, the coordinate commutator is the corresponding
truncated mass. -/
theorem hilbertTruncation_mul_id {f : ℝ → ℝ} (hf : Integrable f)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    hilbertTruncation (fun y ↦ y * f y) x ε =
      x * hilbertTruncation f x ε -
        Real.pi⁻¹ * ∫ t in {t : ℝ | ε < |t|}, f (x - t) := by
  unfold hilbertTruncation
  rw [setIntegral_congr_fun (measurableSet_hilbertCutoff ε)
    (fun t ht ↦ hilbertKernel_mul_id x t (f (x - t)) (abs_pos.mp (hε.trans ht)))]
  rw [integral_sub ((integrableOn_hilbertKernel hf x hε).const_mul x)
    (hf.comp_sub_left x).integrableOn, integral_const_mul, mul_sub]
  congr 1
  exact mul_left_comm _ _ _

/-- The first-moment commutator, proved by taking the principal-value limit of the
finite-cutoff identity and the ordinary integral limit of the mass. -/
theorem HasHilbertPV.mul_id {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Integrable f) :
    HasHilbertPV (fun y ↦ y * f y) x (x * h - Real.pi⁻¹ * ∫ y, f y) := by
  refine ⟨fun _ hε ↦ integrableOn_hilbertKernel_mul_id hf x hε, ?_⟩
  have hmass := tendsto_integral_hilbertCutoff (hf.comp_sub_left x)
  rw [integral_sub_left_eq_self f volume x] at hmass
  apply (hpv.2.const_mul x |>.sub (hmass.const_mul Real.pi⁻¹)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertTruncation_mul_id hf x hε).symm

/-- For zero-mean integrable inputs, multiplication by the coordinate commutes
with the principal-value Hilbert transform. -/
theorem HasHilbertPV.mul_id_of_integral_eq_zero {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Integrable f) (hmean : ∫ y, f y = 0) :
    HasHilbertPV (fun y ↦ y * f y) x (x * h) := by
  simpa only [hmean, mul_zero, sub_zero] using hpv.mul_id hf

/-- The coordinate-weighted transform always has a principal value at the origin
for integrable inputs, independently of whether the unweighted transform does. -/
theorem hasHilbertPV_mul_id_zero {f : ℝ → ℝ} (hf : Integrable f) :
    HasHilbertPV (fun y ↦ y * f y) 0 (-Real.pi⁻¹ * ∫ y, f y) := by
  have heq : (fun t : ℝ ↦ (0 - t) * f (0 - t) / t) =ᵐ[volume]
      (fun t ↦ -f (0 - t)) := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht
    simpa only [zero_mul, zero_sub] using hilbertKernel_mul_id 0 t (f (0 - t)) ht
  have hint := (hf.comp_sub_left 0).neg.congr heq.symm
  have hpv := hasHilbertPV_of_integrable (f := fun y ↦ y * f y) (x := 0) hint
  rw [integral_congr_ae heq, integral_neg, integral_sub_left_eq_self f volume 0] at hpv
  simpa only [mul_neg, neg_mul] using hpv

/-- The operator form of the coordinate commutator, under a PV existence proof. -/
theorem hilbertPV_mul_id {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Integrable f) :
    hilbertPV (fun y ↦ y * f y) x =
      x * hilbertPV f x - Real.pi⁻¹ * ∫ y, f y := by
  rw [hpv.hilbertPV_eq]
  exact (hpv.mul_id hf).hilbertPV_eq

/-- Multiplication by the coordinate cancels division by it outside a null set. -/
theorem mul_div_id_ae (f : ℝ → ℝ) :
    (fun y ↦ y * (f y / y)) =ᵐ[volume] f := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with y hy
  simpa only [mul_comm] using div_mul_cancel₀ (f y) hy

/-- Integrability of `f(y)/y` gives the value of the Hilbert transform at zero. -/
theorem hasHilbertPV_zero_of_div_id_integrable {f : ℝ → ℝ}
    (hf : Integrable (fun y ↦ f y / y)) :
    HasHilbertPV f 0 (-Real.pi⁻¹ * ∫ y, f y / y) :=
  (hasHilbertPV_mul_id_zero hf).congr_ae (mul_div_id_ae f)

/-- If `f/y` is integrable and `Hf(x)` exists away from zero, then `H(f/y)(x)`
exists as well. The constant term is the ordinary integral of `f/y`. -/
theorem HasHilbertPV.div_id {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Integrable (fun y ↦ f y / y)) (hx : x ≠ 0) :
    HasHilbertPV (fun y ↦ f y / y) x ((h + Real.pi⁻¹ * ∫ y, f y / y) / x) := by
  refine ⟨fun _ hε ↦ integrableOn_hilbertKernel hf x hε, ?_⟩
  have hmass := tendsto_integral_hilbertCutoff (hf.comp_sub_left x)
  rw [integral_sub_left_eq_self (fun y ↦ f y / y) volume x] at hmass
  apply ((hpv.2.add (hmass.const_mul Real.pi⁻¹)).div_const x).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hcomm := hilbertTruncation_mul_id hf x hε
  rw [hilbertTruncation_congr_ae (mul_div_id_ae f)] at hcomm
  apply (div_eq_iff hx).mpr
  rw [mul_comm _ x]
  linarith

/-- The difference-quotient identity (A.1) in Appendix A, with existence of
all principal values derived from convergence of `Hf(x)` and integrability of `f/y`. -/
theorem hilbertPV_div_id {f : ℝ → ℝ} {x h : ℝ}
    (hpv : HasHilbertPV f x h) (hf : Integrable (fun y ↦ f y / y)) (hx : x ≠ 0) :
    hilbertPV (fun y ↦ f y / y) x = (hilbertPV f x - hilbertPV f 0) / x := by
  rw [(hpv.div_id hf hx).hilbertPV_eq, hpv.hilbertPV_eq,
    (hasHilbertPV_zero_of_div_id_integrable hf).hilbertPV_eq, neg_mul, sub_neg_eq_add]

end

end PDE.Analysis

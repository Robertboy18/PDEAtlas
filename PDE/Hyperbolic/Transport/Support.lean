/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.GlobalCharacteristics
public import PDE.Analysis.Evolution.Time.GronwallInterior
import PDE.Representations.Similarity.Dynamic
import CAS.IntegrationTactic

/-!
# Support preservation for one-dimensional transport with stretching

For `W_t + b W_x = c W`, a characteristic carries the initial value multiplied by
the exponential of the integral of `c`. With a uniform spatial Lipschitz bound
on `b`, backward characteristics exist on the whole finite time interval. If the
velocity vanishes at both endpoints of a spatial interval, a characteristic ending
outside it also starts outside it. Consequently zero initial exterior remains zero.

With continuous closed-time traces, differentiability at interior times suffices:
the squared amplitude satisfies a Grönwall inequality along each characteristic.

The velocity and a regular solution of the transport equation are given.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open PDE.Analysis.Evolution PDE.Representations.Similarity

namespace TransportEquation

/-- The joint chain rule turns a transport equation into a scalar stretching ODE. -/
theorem hasDerivAt_transport_along_characteristic {W b c : ℝ → ℝ → ℝ} {times : Set ℝ}
    (hW : ∀ x t, t ∈ times → DifferentiableAt ℝ (Function.uncurry W) (x, t))
    (htransport : ∀ x t, t ∈ times → deriv (W x) t + b x t * deriv (fun y ↦ W y t) x =
      c x t * W x t)
    {path : ℝ → ℝ} {t : ℝ} (ht : t ∈ times) (hpath : HasDerivAt path (b (path t) t) t) :
    HasDerivAt (fun s ↦ W (path s) s) (c (path t) t * W (path t) t) t := by
  have hω := hW (path t) t ht
  have hcurve : HasDerivAt (fun s ↦ (path s, s)) (b (path t) t, 1) t :=
    hpath.prodMk (hasDerivAt_id t)
  have hcomp : HasDerivAt (fun s ↦ W (path s) s)
      (fderiv ℝ (Function.uncurry W) (path t, t) (b (path t) t, 1)) t :=
    hω.hasFDerivAt.comp_hasDerivAt (f := fun s ↦ (path s, s)) t hcurve
  apply hcomp.congr_deriv
  rw [fderiv_uncurry_apply_prod W (path t) (b (path t) t) t 1 hω]
  simpa only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul, add_comm] using htransport (path t) t ht

/-- The stretching formula uses a continuous coefficient and its interval integral.
In particular, integrability of the coefficient is derived from continuity of the path. -/
theorem transport_characteristic_eq_exp_integral {W b c : ℝ → ℝ → ℝ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (hc : Continuous (Function.uncurry c))
    (hW : ∀ x t, t ∈ Icc t₀ T → DifferentiableAt ℝ (Function.uncurry W) (x, t))
    (htransport : ∀ x t, t ∈ Icc t₀ T → deriv (W x) t + b x t * deriv (fun y ↦ W y t) x =
      c x t * W x t)
    {path : ℝ → ℝ} (hcont : Continuous path)
    (hpath : ∀ t ∈ Icc t₀ T, HasDerivAt path (b (path t) t) t) :
    W (path T) T = W (path t₀) t₀ * Real.exp (∫ s in t₀..T, c (path s) s) := by
  have hg : Continuous (fun s ↦ c (path s) s) := hc.comp (hcont.prodMk continuous_id)
  let primitive : ℝ → ℝ := fun t ↦ ∫ s in t₀..t, c (path s) s
  have hp (t : ℝ) : HasDerivAt primitive (c (path t) t) t := by
    dsimp only [primitive]
    cas
  have hzero (t : ℝ) (ht : t ∈ Icc t₀ T) :
      HasDerivAt (fun s ↦ W (path s) s * Real.exp (-primitive s)) 0 t := by
    convert (hasDerivAt_transport_along_characteristic hW htransport ht (hpath t ht)).mul
      (hp t).neg.exp using 1
    cas
  have hzero_integrable : IntervalIntegrable (fun _ ↦ (0 : ℝ)) volume t₀ T :=
    IntervalIntegrable.zero
  have hftc : (∫ s in t₀..T, (0 : ℝ)) = W (path T) T * Real.exp (-primitive T) -
        W (path t₀) t₀ * Real.exp (-primitive t₀) := by
    cas using (fun s (hs : s ∈ uIcc t₀ T) ↦ hzero s (uIcc_of_le hT ▸ hs))
  have hproduct : W (path T) T * Real.exp (-primitive T) = W (path t₀) t₀ := by
    have := sub_eq_zero.mp (by simpa using hftc.symm)
    simpa only [primitive, intervalIntegral.integral_same, neg_zero,
      Real.exp_zero, mul_one] using this
  have hquotient := (eq_div_iff (Real.exp_ne_zero (-primitive T))).mpr hproduct
  simpa only [primitive, Real.exp_neg, div_eq_mul_inv, inv_inv] using hquotient

/-- A transport equation with stretching preserves zero exterior on the whole time interval.
Backward characteristics are constructed from the data, and boundary uniqueness proves
their exterior property rather than assuming it. -/
theorem transport_eq_zero_outside_Icc {W b c : ℝ → ℝ → ℝ} {t₀ T A B : ℝ}
    (hb : Continuous (Function.uncurry b)) (hc : Continuous (Function.uncurry c)) (K : NNReal)
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t)) (hA : ∀ t ∈ Icc t₀ T, b A t = 0)
    (hB : ∀ t ∈ Icc t₀ T, b B t = 0)
    (hW : ∀ x t, t ∈ Icc t₀ T → DifferentiableAt ℝ (Function.uncurry W) (x, t))
    (htransport : ∀ x t, t ∈ Icc t₀ T → deriv (W x) t + b x t * deriv (fun y ↦ W y t) x =
      c x t * W x t)
    (hinitial : ∀ x, x ∉ Icc A B → W x t₀ = 0) :
    ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Icc A B → W x t = 0 := by
  intro t ht x hx
  have hsub : Icc t₀ t ⊆ Icc t₀ T := Icc_subset_Icc_right ht.2
  have hKt (s : ℝ) (hs : s ∈ Icc t₀ t) := hK s (hsub hs)
  obtain ⟨path, hcont, hterminal, hpath⟩ := exists_backward_characteristic_Icc ht.1 b hb K hKt x
  have hfoot : path t₀ ∉ Icc A B := by
    have hexterior : x < A ∨ B < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hx
    rcases hexterior with hx | hx
    · have hleft := characteristic_lt_boundary_of_terminal_lt hKt
        (fun s hs ↦ hA s (hsub hs)) hpath
        (by simpa only [hterminal] using hx) (left_mem_Icc.mpr ht.1)
      exact fun h ↦ (not_lt_of_ge h.1) hleft
    · have hright := boundary_lt_characteristic_of_lt_terminal hKt
        (fun s hs ↦ hB s (hsub hs)) hpath
        (by simpa only [hterminal] using hx) (left_mem_Icc.mpr ht.1)
      exact fun h ↦ (not_lt_of_ge h.2) hright
  have hformula := transport_characteristic_eq_exp_integral ht.1 hc (fun y s hs ↦ hW y s (hsub hs))
    (fun y s hs ↦ htransport y s (hsub hs)) hcont hpath
  simpa only [hterminal, hinitial (path t₀) hfoot, zero_mul] using hformula

/-- Set-theoretic support formulation of transport support preservation. -/
theorem transport_support_subset_Icc {W b c : ℝ → ℝ → ℝ} {t₀ T A B : ℝ}
    (hb : Continuous (Function.uncurry b)) (hc : Continuous (Function.uncurry c)) (K : NNReal)
    (hK : ∀ t ∈ Icc t₀ T, LipschitzWith K (fun x ↦ b x t)) (hA : ∀ t ∈ Icc t₀ T, b A t = 0)
    (hB : ∀ t ∈ Icc t₀ T, b B t = 0)
    (hW : ∀ x t, t ∈ Icc t₀ T → DifferentiableAt ℝ (Function.uncurry W) (x, t))
    (htransport : ∀ x t, t ∈ Icc t₀ T → deriv (W x) t + b x t * deriv (fun y ↦ W y t) x =
      c x t * W x t)
    (hinitial : Function.support (fun x ↦ W x t₀) ⊆ Icc A B) :
    ∀ t ∈ Icc t₀ T, Function.support (fun x ↦ W x t) ⊆ Icc A B := by
  have hzero := transport_eq_zero_outside_Icc hb hc K hK hA hB hW htransport
    (fun x hx ↦ by
      by_contra h
      exact hx (hinitial h))
  intro t ht x hx
  by_contra hout
  exact hx (hzero t ht x hout)


/-- Continuous closed traces and an interior classical transport equation
preserve support between stationary boundaries. -/
theorem transport_support_subset_Icc_of_interior {W b c : ℝ → ℝ → ℝ} {T A B : ℝ} (hT : 0 ≤ T)
    (hb : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ b p.1 p.2))
    (hc : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ c p.1 p.2))
    (hWcont : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ W p.1 p.2)) (K : NNReal)
    (hK : ∀ t ∈ Icc 0 T, LipschitzWith K (fun x ↦ b x t)) (hA : ∀ t ∈ Icc 0 T, b A t = 0)
    (hB : ∀ t ∈ Icc 0 T, b B t = 0)
    (hW : ∀ x t, t ∈ Ioo 0 T → DifferentiableAt ℝ (Function.uncurry W) (x, t))
    (htransport : ∀ x t, t ∈ Ioo 0 T → deriv (W x) t + b x t * deriv (fun y ↦ W y t) x =
      c x t * W x t)
    (hinitial : Function.support (fun x ↦ W x 0) ⊆ Icc A B) :
    ∀ t ∈ Icc 0 T, Function.support (fun x ↦ W x t) ⊆ Icc A B := by
  let bext : ℝ → ℝ → ℝ := fun x t ↦ b x (projIcc 0 T hT t)
  have hbext : Continuous (Function.uncurry bext) :=
    hb.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
  have hext (x t : ℝ) (ht : t ∈ Icc 0 T) : bext x t = b x t := by
    simp only [bext, projIcc_of_mem hT ht]
  intro t ht x hx
  by_contra hout
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hKt (s : ℝ) (hs : s ∈ Icc 0 t) : LipschitzWith K (fun y ↦ bext y s) := by
    simpa only [hext _ _ (hsub hs)] using hK s (hsub hs)
  obtain ⟨path, hcont, hterminal, hpath⟩ :=
    exists_backward_characteristic_Icc ht.1 bext hbext K hKt x
  have hfoot : path 0 ∉ Icc A B := by
    rcases (show x < A ∨ B < x by
      simpa only [mem_Icc, not_and_or, not_le] using hout) with hl | hr
    · have hleft := characteristic_lt_boundary_of_terminal_lt hKt
        (fun s hs ↦ by rw [hext _ _ (hsub hs), hA s (hsub hs)])
        hpath (by simpa only [hterminal] using hl) (left_mem_Icc.mpr ht.1)
      exact fun h ↦ (not_lt_of_ge h.1) hleft
    · have hright := boundary_lt_characteristic_of_lt_terminal hKt
        (fun s hs ↦ by rw [hext _ _ (hsub hs), hB s (hsub hs)])
        hpath (by simpa only [hterminal] using hr) (left_mem_Icc.mpr ht.1)
      exact fun h ↦ (not_lt_of_ge h.2) hright
  let incl : Icc (0 : ℝ) t → Icc (0 : ℝ) T := fun r ↦ ⟨r, hsub r.property⟩
  have hi : Continuous incl := continuous_subtype_val.subtype_mk _
  have hpathmap : Continuous (fun r : Icc (0 : ℝ) t ↦ (path r, incl r)) :=
    (hcont.comp continuous_subtype_val).prodMk hi
  have hwcont : ContinuousOn (fun s ↦ W (path s) s) (Icc 0 t) :=
    continuousOn_iff_continuous_domRestrict.mpr (hWcont.comp hpathmap)
  have hccont : ContinuousOn (fun s ↦ c (path s) s) (Icc 0 t) :=
    continuousOn_iff_continuous_domRestrict.mpr (hc.comp hpathmap)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hccont
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun r ↦ W (path r) r) (c (path s) s * W (path s) s) s := by
    apply hasDerivAt_transport_along_characteristic hW htransport ⟨hs.1, hs.2.trans_le ht.2⟩
    simpa only [hext _ _ (hsub (Ioo_subset_Icc_self hs))] using hpath s (Ioo_subset_Icc_self hs)
  have hzero := eq_zero_on_Icc_of_deriv_le_mul (hwcont.pow 2)
    (fun _ _ ↦ sq_nonneg _) (fun s hs ↦ (hd s hs).differentiableAt.pow 2)
    (K := 2 * C) (fun s hs ↦ ?_) (show W (path 0) 0 ^ 2 = 0 from ?_)
  · exact hx (by
      have hz := hzero t (right_mem_Icc.mpr ht.1)
      change W (path t) t ^ 2 = 0 at hz
      rw [hterminal] at hz
      exact sq_eq_zero_iff.mp hz)
  · rw [((hd s hs).pow 2).deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
    have hbound : c (path s) s ≤ C := (le_abs_self _).trans (hC s (Ioo_subset_Icc_self hs))
    have hm := mul_le_mul_of_nonneg_right hbound (sq_nonneg (W (path s) s))
    nlinarith
  · have hz : W (path 0) 0 = 0 := by
      by_contra hn
      exact hfoot (hinitial hn)
    rw [hz, zero_pow (by decide : 2 ≠ 0)]

end TransportEquation

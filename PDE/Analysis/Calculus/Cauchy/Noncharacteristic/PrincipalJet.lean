/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Affine.IteratedDerivative
public import PDE.Analysis.Calculus.Jet.Finite
public import PDE.Analysis.Calculus.Jet.Product

/-!
# The principal part of a differentiated quasilinear equation

For two smooth solutions whose lower jets agree, differentiate the actual
equation along an affine line. Smooth dependence on the lower jets and
Leibniz's formula cancel every term except the unchanged principal coefficients
times the highest derivative difference.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ContDiff

namespace PDE.Analysis.Cauchy

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Differentiating a quasilinear equation leaves its principal contraction
when all lower derivatives of the two solutions agree. The equation is needed
only as a germ at the point. -/
theorem principal_jet_difference_eq_zero
    {k r : ℕ} (d : ι → Fin k → E)
    (a : ι → E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
    (b : E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
    {u v : E → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (x e : E)
    (ha : ∀ α p, ContDiffAt ℝ ∞ (a α) (x, p))
    (hb : ∀ p, ContDiffAt ℝ ∞ b (x, p))
    (hPu : ∀ᶠ y in 𝓝 x,
      ∑ α, a α (y, jetLT ℝ k u y) * iteratedFDeriv ℝ k u y (d α) =
        b (y, jetLT ℝ k u y))
    (hPv : ∀ᶠ y in 𝓝 x,
      ∑ α, a α (y, jetLT ℝ k v y) * iteratedFDeriv ℝ k v y (d α) =
        b (y, jetLT ℝ k v y))
    (heq : ∀ i < r + k, iteratedFDeriv ℝ i u x = iteratedFDeriv ℝ i v x) :
    ∑ α, a α (x, jetLT ℝ k u x) *
      (iteratedFDeriv ℝ (r + k) u x (Fin.append (fun _ : Fin r ↦ e) (d α)) -
        iteratedFDeriv ℝ (r + k) v x (Fin.append (fun _ : Fin r ↦ e) (d α))) = 0 := by
  classical
  let line : ℝ → E := fun t ↦ x + t • e
  let coeff (Φ : E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
      (w : E → ℝ) : ℝ → ℝ := fun t ↦ Φ (line t, jetLT ℝ k w (line t))
  let factor (w : E → ℝ) (α : ι) : ℝ → ℝ :=
    fun t ↦ iteratedFDeriv ℝ k w (line t) (d α)
  have hline : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hC (w : E → ℝ) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (fun y ↦ (y, jetLT ℝ k w y)) :=
    contDiff_id.prodMk (hw.jetLT k)
  have hF (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (α : ι) :
      ContDiff ℝ ∞ (fun y ↦ iteratedFDeriv ℝ k w y (d α)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) ℝ (d α)).contDiff.comp
      (hw.iteratedFDeriv_right (by simp : ∞ + (k : ℕ∞ω) ≤ ∞))
  have hcoeff (Φ : E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
      (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (x, p))
      (w : E → ℝ) (hw : ContDiff ℝ ∞ w) :
      ContDiffAt ℝ ∞ (coeff Φ w) 0 := by
    have hΦ' : ContDiffAt ℝ ∞ Φ (line 0, jetLT ℝ k w (line 0)) := by
      simpa only [line, zero_smul, add_zero] using hΦ (jetLT ℝ k w x)
    exact hΦ'.comp 0 ((hC w hw).comp hline).contDiffAt
  have hfactor (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (α : ι) :
      ContDiff ℝ ∞ (factor w α) :=
    (hF w hw α).comp hline
  have hcoeff_eq (Φ : E × (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
      (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (x, p)) (i : ℕ) (hi : i ≤ r) :
      iteratedDeriv i (coeff Φ u) 0 = iteratedDeriv i (coeff Φ v) 0 := by
    apply iteratedDeriv_comp_eq_of_iteratedDeriv_eq
      (((hC u hu).comp hline).contDiffAt.of_le (by simp : (i : ℕ∞ω) ≤ ∞))
      (((hC v hv).comp hline).contDiffAt.of_le (by simp : (i : ℕ∞ω) ≤ ∞))
      (by simpa only [Function.comp_def, line, zero_smul, add_zero] using
        (hΦ (jetLT ℝ k u x)).of_le (by simp : (i : ℕ∞ω) ≤ ∞))
    intro j hj
    change iteratedDeriv j (fun t ↦ (x + t • e, jetLT ℝ k u (x + t • e))) 0 =
      iteratedDeriv j (fun t ↦ (x + t • e, jetLT ℝ k v (x + t • e))) 0
    rw [iteratedDeriv_comp_affine_line (hC u hu) x e 0 (by simp : (j : ℕ∞ω) ≤ ∞),
      iteratedDeriv_comp_affine_line (hC v hv) x e 0 (by simp : (j : ℕ∞ω) ≤ ∞)]
    simp only [zero_smul, add_zero]
    exact congrArg (fun A ↦ A (fun _ ↦ e))
      (iteratedFDeriv_comp_jetLT_eq_of_iteratedFDeriv_eq hu hv k j x
        (Φ := id) contDiff_id (fun l hl ↦ heq l (by omega)))
  have hfactor_deriv (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (α : ι) (i : ℕ) :
      iteratedDeriv i (factor w α) 0 =
        iteratedFDeriv ℝ (i + k) w x (Fin.append (fun _ : Fin i ↦ e) (d α)) := by
    change iteratedDeriv i (fun t ↦ iteratedFDeriv ℝ k w (x + t • e) (d α)) 0 = _
    rw [iteratedDeriv_comp_affine_line (hF w hw α) x e 0 (by simp : (i : ℕ∞ω) ≤ ∞)]
    simp only [zero_smul, add_zero, iteratedFDeriv_eval_iteratedFDeriv hw]
  have hfactor_eq (α : ι) (i : ℕ) (hi : i < r) :
      iteratedDeriv i (factor u α) 0 = iteratedDeriv i (factor v α) 0 := by
    rw [hfactor_deriv u hu, hfactor_deriv v hv, heq (i + k) (by omega)]
  have hproduct (α : ι) :
      iteratedDeriv r (coeff (a α) u * factor u α) 0 -
        iteratedDeriv r (coeff (a α) v * factor v α) 0 =
        a α (x, jetLT ℝ k u x) *
          (iteratedFDeriv ℝ (r + k) u x (Fin.append (fun _ : Fin r ↦ e) (d α)) -
            iteratedFDeriv ℝ (r + k) v x (Fin.append (fun _ : Fin r ↦ e) (d α))) := by
    rw [iteratedDeriv_mul_sub_eq_of_jet_eq
      ((hcoeff (a α) (ha α) u hu).of_le (by simp))
      ((hcoeff (a α) (ha α) v hv).of_le (by simp))
      ((hfactor u hu α).contDiffAt.of_le (by simp))
      ((hfactor v hv α).contDiffAt.of_le (by simp))
      (hcoeff_eq (a α) (ha α)) (hfactor_eq α),
      hfactor_deriv u hu, hfactor_deriv v hv]
    simp [coeff, line]
  have hP (w : E → ℝ) (hw : ContDiff ℝ ∞ w)
      (hp : ∀ᶠ y in 𝓝 x,
        ∑ α, a α (y, jetLT ℝ k w y) * iteratedFDeriv ℝ k w y (d α) =
          b (y, jetLT ℝ k w y)) :
      ∑ α, iteratedDeriv r (coeff (a α) w * factor w α) 0 =
        iteratedDeriv r (coeff b w) 0 := by
    have ht : Tendsto line (𝓝 0) (𝓝 x) := by
      simpa only [ContinuousAt, line, zero_smul, add_zero] using
        hline.continuous.continuousAt (x := 0)
    have h : (fun t ↦ ∑ α, (coeff (a α) w * factor w α) t) =ᶠ[𝓝 0] coeff b w :=
      ht.eventually hp
    have hd := (h.iteratedDeriv r).self_of_nhds
    exact (iteratedDeriv_fun_sum
      (f := fun α ↦ coeff (a α) w * factor w α) (I := Finset.univ)
      (fun α _ ↦ (((hcoeff (a α) (ha α) w hw).mul
        (hfactor w hw α).contDiffAt).of_le (by simp)))).symm.trans hd
  simp_rw [← hproduct]
  rw [Finset.sum_sub_distrib, hP u hu hPu, hP v hv hPv, hcoeff_eq b hb r le_rfl, sub_self]

end PDE.Analysis.Cauchy

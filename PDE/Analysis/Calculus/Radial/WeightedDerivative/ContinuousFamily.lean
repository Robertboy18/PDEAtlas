/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Radial.WeightedDerivative.Regularity
public import PDE.Analysis.Calculus.ContinuousFamily.Bilinear

/-!
# Continuous jets of weighted radial transforms

The weighted recurrence is valid at signed radius zero. Applying it to a
continuously indexed family loses exactly one spatial derivative per step,
without differentiating the index.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {A : Type*} [TopologicalSpace A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jets of a weighted radial transform depend continuously on a
continuous index, through zero as well as positive and negative radii. -/
theorem continuous_iteratedFDeriv_oddRadialTransform_pow_mul_family
    (k s : ℕ) {F : A → E × ℝ → ℝ}
    (hF : ∀ a, ContDiff ℝ (k + s) (F a))
    (hjet : ∀ j ≤ k + s, Continuous
      (fun p : A × (E × ℝ) ↦ iteratedFDeriv ℝ j (F p.1) p.2)) :
    Continuous (fun p : A × (E × ℝ) ↦ iteratedFDeriv ℝ s
      (fun q : E × ℝ ↦
        oddRadialTransform k (fun r ↦ r ^ (2 * k + 1) * F p.1 (q.1, r)) q.2) p.2) := by
  have hR (i : ℕ) : ContDiff ℝ i (fun p : E × ℝ ↦ p.2) := contDiff_snd
  have hRj (i : ℕ) : Continuous (fun p : A × (E × ℝ) ↦
      iteratedFDeriv ℝ i (fun q : E × ℝ ↦ q.2) p.2) :=
    ((hR i).continuous_iteratedFDeriv le_rfl).comp continuous_snd
  induction k generalizing F with
  | zero =>
    simpa using (ContinuousLinearMap.mul ℝ ℝ).continuous_iteratedFDeriv_bilinear_family
      (fun _ ↦ hR s) (fun a ↦ by simpa using hF a)
      (fun i _ ↦ hRj i) (fun i hi ↦ hjet i (by simpa using hi))
  | succ k ih =>
    have hF₁ (a : A) : ContDiff ℝ 1 (F a) := (hF a).of_le (by norm_cast; omega)
    have hF₀ (a : A) : ContDiff ℝ (k + s) (F a) :=
      (hF a).of_le (by norm_cast; omega)
    let Fr (a : A) (p : E × ℝ) := deriv (fun r ↦ F a (p.1, r)) p.2
    have hFr (a : A) : ContDiff ℝ (k + s) (Fr a) := by
      apply contDiff_deriv_prod_snd
      convert hF a using 1
      push_cast
      ring
    have hFrj (i : ℕ) (hi : i ≤ k + s) : Continuous
        (fun p : A × (E × ℝ) ↦ iteratedFDeriv ℝ i (Fr p.1) p.2) := by
      have heq (a : A) : Fr a = fun p ↦ fderiv ℝ (F a) p (0, 1) := by
        funext p
        exact deriv_prod_timeSlice _ _ _ ((hF₁ a).differentiable one_ne_zero p)
      simp_rw [heq]
      exact continuous_iteratedFDeriv_fderiv_apply_family
        (fun a ↦ (hF a).of_le (by exact_mod_cast (show i + 1 ≤ k + 1 + s by omega)))
        (hjet (i + 1) (by omega)) (0, 1)
    let G (a : A) (p : E × ℝ) :=
      (2 * k + 3 : ℝ) * F a p + p.2 * Fr a p
    have hG (a : A) : ContDiff ℝ (k + s) (G a) :=
      (contDiff_const.mul (hF₀ a)).add (contDiff_snd.mul (hFr a))
    have hGj (i : ℕ) (hi : i ≤ k + s) : Continuous
        (fun p : A × (E × ℝ) ↦ iteratedFDeriv ℝ i (G p.1) p.2) := by
      have hFa (a : A) : ContDiff ℝ i (F a) :=
        (hF₀ a).of_le (by exact_mod_cast hi)
      have hFra (a : A) : ContDiff ℝ i (Fr a) :=
        (hFr a).of_le (by exact_mod_cast hi)
      have hc := ContinuousLinearMap.continuous_iteratedFDeriv_comp_family
        ((ContinuousLinearMap.mul ℝ ℝ) (2 * k + 3 : ℝ)) hFa (hjet i (by omega))
      have hm := (ContinuousLinearMap.mul ℝ ℝ).continuous_iteratedFDeriv_bilinear_family
        (fun _ ↦ hR i) hFra (fun l _ ↦ hRj l)
        (fun l hl ↦ hFrj l (hl.trans hi))
      convert hc.add hm using 1
      ext p
      simp only [G, Function.comp_def, ContinuousLinearMap.mul_apply', Pi.add_apply,
        fun_iteratedFDeriv_add_apply (contDiff_const.mul (hFa _)).contDiffAt
          (contDiff_snd.mul (hFra _)).contDiffAt]
    have he : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have hrec (a : A) :
        (fun p : E × ℝ ↦ oddRadialTransform (k + 1)
          (fun r ↦ r ^ (2 * (k + 1) + 1) * F a (p.1, r)) p.2) =
        (fun p : E × ℝ ↦ oddRadialTransform k
          (fun r ↦ r ^ (2 * k + 1) * G a (p.1, r)) p.2) := by
      funext p
      simpa only [he, G, Fr, Function.comp_def] using congrFun
        (oddRadialTransform_step k
          ((hF₁ a).comp (contDiff_const.prodMk contDiff_id) :
            ContDiff ℝ 1 (fun r ↦ F a (p.1, r)))) p.2
    simp_rw [hrec]
    exact ih hG hGj

end PDE.Analysis

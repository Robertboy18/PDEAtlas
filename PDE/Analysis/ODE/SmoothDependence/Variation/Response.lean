/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Interval

import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Duhamel.Identification
import PDE.Analysis.ODE.SmoothDependence.Variation
import PDE.Analysis.ODE.SmoothDependence.Variation.SecondOrder

/-!
# Actual second speed response from any anchor in a closed interval

Two supplied solution families solve the fields `f` and `f + P` with the same
speed damping and agree as speed germs at an arbitrary time in the interval.
Vanishing of `P` and its first differential along the original base trajectory
identifies both actual base trajectories and their first speed derivatives.
The projected second-derivative difference is an oriented propagator integral
from the data anchor to the evaluation time.

Both endpoints and singleton time intervals are included. The original theorem
with a left endpoint anchor is retained as a specialization.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Actual base paths and first speed variations agree on both sides of the
anchor. The second speed response is the oriented integral of `D²P(γ)[W,W]`,
with coefficient one. The common initial speed germ supplies the base, first,
and second initial equalities; no individual initial derivative must vanish.
Only the actual ODE germs on the displayed closed interval are required. -/
theorem exists_projected_secondSpeedVariation_response_of_mem_Icc
    {F G : ℝ → ℝ → E} {f P : E → E} {a b c : ℝ} (hc : c ∈ Icc a b)
    (hF : ContDiff ℝ 3 F.uncurry) (hG : ContDiff ℝ 3 G.uncurry)
    (hf : ContDiff ℝ 2 f) (hP : ContDiff ℝ 2 P)
    (hodeF : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t)
    (hinit : G c =ᶠ[𝓝 (0 : ℝ)] F c)
    (hjet : ∀ t ∈ Icc a b, P (F t 0) = 0 ∧ fderiv ℝ P (F t 0) = 0)
    (L : E →L[ℝ] V) :
    ∃ S : FundamentalSolution (fun t ↦ fderiv ℝ f (F t 0)) c (Icc a b),
      EqOn (fun t ↦ G t 0) (fun t ↦ F t 0) (Icc a b) ∧
      EqOn (fun t ↦ deriv (G t) 0) (fun t ↦ deriv (F t) 0) (Icc a b) ∧
      ∀ t ∈ Icc a b,
        L (deriv (deriv (G t)) 0 - deriv (deriv (F t)) 0) =
          ∫ s in c..t, L (S.propagator t s
            (fderiv ℝ (fderiv ℝ P) (F s 0) (deriv (F s) 0) (deriv (F s) 0))) := by
  have hFc : Continuous (fun t ↦ F t 0) := hF.continuous.uncurry_right 0
  have hGc : Continuous (fun t ↦ G t 0) := hG.continuous.uncurry_right 0
  have hsum : ContDiff ℝ 2 (fun x ↦ f x + P x) := hf.add hP
  -- Compact trajectory images suffice for the existing endpoint uniqueness theorem.
  let K : Set E := (fun t ↦ G t 0) '' Icc a b ∪ (fun t ↦ F t 0) '' Icc a b
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_Icc.image hGc).union (isCompact_Icc.image hFc))
    ((hsum.of_le (by norm_num)).locallyLipschitz.locallyLipschitzOn)
  have hbaseG (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ G s 0) (f (G t 0) + P (G t 0)) t := by
    simpa only [zero_smul, sub_zero] using (hodeG t ht).self_of_nhds
  have hbaseF (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ F s 0) (f (F t 0) + P (F t 0)) t := by
    simpa only [(hjet t ht).1, add_zero, zero_smul, sub_zero] using (hodeF t ht).self_of_nhds
  have hbase : EqOn (fun t ↦ G t 0) (fun t ↦ F t 0) (Icc a b) := by
    rw [← Icc_union_Icc_eq_Icc hc.1 hc.2]
    refine EqOn.union ?_ ?_
    · have hsub : Ioc a c ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hc.2)
      exact ODE_solution_unique_of_mem_Icc_left (v := fun _ x ↦ f x + P x) (s := fun _ ↦ K)
        (fun _ _ ↦ hC) hGc.continuousOn (fun t ht ↦ (hbaseG t (hsub ht)).hasDerivWithinAt)
        (fun t ht ↦ Or.inl ⟨t, hsub ht, rfl⟩) hFc.continuousOn
        (fun t ht ↦ (hbaseF t (hsub ht)).hasDerivWithinAt) (fun t ht ↦ Or.inr ⟨t, hsub ht, rfl⟩)
        hinit.self_of_nhds
    · have hsub : Ico c b ⊆ Icc a b := Ico_subset_Icc_self.trans (Icc_subset_Icc hc.1 le_rfl)
      exact ODE_solution_unique_of_mem_Icc_right (v := fun _ x ↦ f x + P x) (s := fun _ ↦ K)
        (fun _ _ ↦ hC) hGc.continuousOn (fun t ht ↦ (hbaseG t (hsub ht)).hasDerivWithinAt)
        (fun t ht ↦ Or.inl ⟨t, hsub ht, rfl⟩) hFc.continuousOn
        (fun t ht ↦ (hbaseF t (hsub ht)).hasDerivWithinAt) (fun t ht ↦ Or.inr ⟨t, hsub ht, rfl⟩)
        hinit.self_of_nhds
  -- Mathlib's derivative regularity gives continuity up to both time endpoints.
  have hcont {Q : ℝ → ℝ → E} (hQ : ContDiff ℝ 1 Q.uncurry) :
      Continuous (fun t ↦ deriv (Q t) 0) := by
    simpa only [fderiv_apply_one_eq_deriv] using (hQ.fderiv_apply (n := 0) (g := fun _ ↦ 0)
      (k := fun _ ↦ (1 : ℝ)) contDiff_const contDiff_const (by norm_num)).continuous
  have hregularity (Q : ℝ → ℝ → E) (hQ : ContDiff ℝ 3 Q.uncurry) :
      Continuous (fun t ↦ deriv (Q t) 0) ∧
      Continuous (fun t ↦ deriv (deriv (Q t)) 0) := by
    have hD : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ deriv (Q z.1) z.2) := by
      simpa only [fderiv_apply_one_eq_deriv] using
        ContDiff.fderiv_apply (f := fun (z : ℝ × ℝ) μ ↦ Q z.1 μ) (k := fun _ ↦ (1 : ℝ))
          (hQ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd contDiff_const le_rfl
    exact ⟨hcont (hQ.of_le (by norm_num)), hcont (hD.of_le (by norm_num))⟩
  obtain ⟨hWF, hZF⟩ := hregularity F hF
  obtain ⟨hWG, hZG⟩ := hregularity G hG
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDP : ContDiff ℝ 1 (fderiv ℝ P) := hP.fderiv_right (by norm_num)
  have hDadd : fderiv ℝ (fun x ↦ f x + P x) = fun x ↦ fderiv ℝ f x + fderiv ℝ P x :=
    funext fun x ↦ fderiv_fun_add (hf.differentiable (by norm_num) x)
      (hP.differentiable (by norm_num) x)
  have hDDadd : fderiv ℝ (fderiv ℝ (fun x ↦ f x + P x)) =
      fun x ↦ fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ P) x :=
    hDadd ▸ funext fun x ↦ fderiv_fun_add (hDf.differentiable (by norm_num) x)
      (hDP.differentiable (by norm_num) x)
  -- Apply the existing first-variation theorem; only the affine field is evaluated here.
  have hvariation {Q : ℝ → ℝ → E} {v : E → E} {t : ℝ}
      (hQ : ContDiff ℝ 3 Q.uncurry) (hv : ContDiff ℝ 2 v)
      (hode : ∀ᶠ μ in 𝓝 (0 : ℝ),
        HasDerivAt (fun s ↦ Q s μ) (v (Q t μ) - μ • Q t μ) t) :
      HasDerivAt (fun s ↦ deriv (Q s) 0)
        (fderiv ℝ v (Q t 0) (deriv (Q t) 0) - Q t 0) t := by
    have hfield := ((hv.differentiable (by norm_num) (Q t 0)).hasFDerivAt.comp ((0 : ℝ), Q t 0)
      (hasFDerivAt_snd (𝕜 := ℝ))).fun_sub
        ((hasFDerivAt_fst (𝕜 := ℝ)).fun_smul (hasFDerivAt_snd (𝕜 := ℝ)))
    refine (hasDerivAt_parameterVariation_of_contDiffAt (F := Q) (t := t) (p := 0)
      (hQ.contDiffAt.of_le (by norm_num)) hfield.differentiableAt hode (1 : ℝ)).congr_deriv ?_
    simpa only [Function.comp_def, fderiv_apply_one_eq_deriv, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      zero_apply, zero_smul, one_smul, zero_add] using
      congrArg (fun D : (ℝ × E) →L[ℝ] E ↦ D (1, deriv (Q t) 0)) hfield.fderiv
  let A : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ f (F t 0)
  let S : FundamentalSolution A c (Icc a b) :=
    fundamentalSolutionIcc (hDf.continuous.comp hFc).continuousOn ⟨c, hc⟩
  have hWGode (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ deriv (G s) 0) (A t (deriv (G t) 0) - F t 0) t := by
    simpa only [A, hbase ht, hDadd, (hjet t ht).2, add_zero] using
      hvariation hG hsum (hodeG t ht)
  have hfirst : EqOn (fun t ↦ deriv (G t) 0) (fun t ↦ deriv (F t) 0) (Icc a b) := by
    intro t ht
    have hGsol := S.eq_propagator_add_integral_of_hasDerivWithinAt
      (z := fun s ↦ deriv (G s) 0) (r := fun s ↦ -F s 0)
      hWG.continuousOn hFc.neg.continuousOn
      (fun s hs ↦ by simpa only [sub_eq_add_neg] using
        (hWGode s (Ioo_subset_Icc_self hs)).hasDerivWithinAt) hc ht
    have hFsol := S.eq_propagator_add_integral_of_hasDerivWithinAt
      (z := fun s ↦ deriv (F s) 0) (r := fun s ↦ -F s 0)
      hWF.continuousOn hFc.neg.continuousOn
      (fun s hs ↦ by simpa only [sub_eq_add_neg] using
        (hvariation hF hf (hodeF s (Ioo_subset_Icc_self hs))).hasDerivWithinAt) hc ht
    rw [hinit.deriv_eq] at hGsol
    exact hGsol.trans hFsol.symm
  let R : ℝ → E := fun t ↦ fderiv ℝ (fderiv ℝ P) (F t 0) (deriv (F t) 0) (deriv (F t) 0)
  let Δ : ℝ → E := fun t ↦ deriv (deriv (G t)) 0 - deriv (deriv (F t)) 0
  have hR : Continuous R :=
    ((hDP.continuous_fderiv (by norm_num)).comp hFc).clm_apply hWF |>.clm_apply hWF
  have hΔode (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt Δ (A t (Δ t) + R t) t := by
    have h0 : HasDerivAt (fun s ↦ deriv (deriv (F s)) 0)
        (A t (deriv (deriv (F t)) 0) +
          fderiv ℝ (fderiv ℝ f) (F t 0) (deriv (F t) 0) (deriv (F t) 0) -
          (2 : ℝ) • deriv (F t) 0) t := by
      simpa only [A, zero_smul, sub_zero] using
        hasDerivAt_secondSpeedVariation_sub_smul hF hf (hodeF t ht)
    have h1 : HasDerivAt (fun s ↦ deriv (deriv (G s)) 0)
        (A t (deriv (deriv (G t)) 0) +
          fderiv ℝ (fderiv ℝ f) (F t 0) (deriv (F t) 0) (deriv (F t) 0) +
          R t - (2 : ℝ) • deriv (F t) 0) t := by
      have h := hasDerivAt_secondSpeedVariation_sub_smul hG hsum (hodeG t ht)
      rw [hDDadd, hDadd] at h
      simpa only [A, R, hbase ht, hfirst ht, (hjet t ht).2, add_zero,
        add_apply, zero_smul, sub_zero, add_assoc] using h
    refine (h1.fun_sub h0).congr_deriv ?_
    simp only [Δ, map_sub]
    abel
  refine ⟨S, hbase, hfirst, fun t ht ↦ ?_⟩
  have hsolution := S.eq_propagator_add_integral_of_hasDerivWithinAt
    (z := Δ) (r := R) (hZG.sub hZF).continuousOn hR.continuousOn
    (fun s hs ↦ (hΔode s (Ioo_subset_Icc_self hs)).hasDerivWithinAt) hc ht
  rw [show Δ c = 0 from sub_eq_zero.mpr hinit.deriv.deriv_eq, map_zero, zero_add] at hsolution
  have hprop : ContinuousOn (fun s ↦ S.propagator t s (R s)) (Icc a b) := by
    simpa only [FundamentalSolution.propagator, mul_apply_eq_comp, Function.comp_def] using
      (S.forward t).continuous.comp_continuousOn
        (S.continuousOn_backward.clm_apply hR.continuousOn)
  exact (congrArg L hsolution).trans (L.intervalIntegral_comp_comm
    ((hprop.mono (uIcc_subset_Icc hc ht)).intervalIntegrable)).symm

/-- First-jet agreement of the fields preserves the actual zero-speed path and
first speed variation. The projected change in the second speed derivative is
an exact variation-of-constants integral for the same path and first variation.
Only the ODE germs near speed zero on the displayed closed interval are needed.
The linear fundamental solution is constructed from the unperturbed coefficient;
no trajectory, variational equation, or initial derivative is assumed separately. -/
theorem exists_projected_secondSpeedVariation_response
    {F G : ℝ → ℝ → E} {f P : E → E} {a b : ℝ} (hab : a ≤ b)
    (hF : ContDiff ℝ 3 F.uncurry) (hG : ContDiff ℝ 3 G.uncurry)
    (hf : ContDiff ℝ 2 f) (hP : ContDiff ℝ 2 P)
    (hodeF : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t)
    (hinit : G a =ᶠ[𝓝 (0 : ℝ)] F a)
    (hjet : ∀ t ∈ Icc a b, P (F t 0) = 0 ∧ fderiv ℝ P (F t 0) = 0)
    (L : E →L[ℝ] V) :
    ∃ S : FundamentalSolution (fun t ↦ fderiv ℝ f (F t 0)) a (Icc a b),
      EqOn (fun t ↦ G t 0) (fun t ↦ F t 0) (Icc a b) ∧
      EqOn (fun t ↦ deriv (G t) 0) (fun t ↦ deriv (F t) 0) (Icc a b) ∧
      ∀ t ∈ Icc a b,
        L (deriv (deriv (G t)) 0 - deriv (deriv (F t)) 0) =
          ∫ s in a..t, L (S.propagator t s
            (fderiv ℝ (fderiv ℝ P) (F s 0) (deriv (F s) 0) (deriv (F s) 0))) := by
  exact exists_projected_secondSpeedVariation_response_of_mem_Icc
    (c := a) ⟨le_rfl, hab⟩ hF hG hf hP hodeF hodeG hinit hjet L

end PDE.Analysis.ODE

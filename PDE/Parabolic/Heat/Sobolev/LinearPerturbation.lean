/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.TimeRestriction
import PDE.Analysis.ODE.Volterra.Quadratic
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Finite systems with a bounded first-order perturbation

The scalar heat response and its causal estimate construct a coupled system
on every finite interval. The perturbation acts from the native H¹ graph to
L² and is continuous in operator norm on the closed time interval. Its norm
bound is derived by compactness. Iteration of the quadratic Volterra bound
removes any restriction on the interval length.

The finite product carries its product norm. Every component has an H²
Bochner state, an L² weak time derivative, and a closed-interval H¹
representative.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Laplacian NNReal Sobolev

variable {n : ℕ} {ι : Type*} [Finite ι] {ε a b : ℝ}

/-- Finite-component heat evolution with an arbitrary bounded linear
H¹-to-L² perturbation, on any finite interval of positive length. -/
theorem exists_heat_solution_of_continuous_linear_perturbation
    (hε : 0 < ε) (hab : a < b)
    (B : ℝ → (ι → W^{1,2}(ℝ^n)) →L[ℝ] (ι → DerivLp n 2 univ))
    (hB : ContinuousOn B (Icc a b))
    (F : ι → Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (q : ι → W^{1,2}(ℝ^n)) :
    ∃ (u : ι → Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
      (g : ι → Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
      (z : ℝ → ι → W^{1,2}(ℝ^n)),
      ContinuousOn z (Icc a b) ∧ z a = q ∧
      ∀ i,
        (fun t ↦ g i t) =ᵐ[volume.restrict (Ioc a b)]
          (fun t ↦ ε • Δ (u i t) + F i t + B t (z t) i) ∧
        HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ wkpBaseCoordinateCLM (u i t)) (fun t ↦ g i t) ∧
        (fun t ↦ z t i) =ᵐ[volume.restrict (Ioc a b)]
          (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u i t)) := by
  classical
  let := Fintype.ofFinite ι
  let μ := volume.restrict (Ioc a b)
  let E := ι → W^{1,2}(ℝ^n)
  let X := C(Icc a b, E)
  let e (v : X) (t : ℝ) := v (projIcc a b hab.le t)
  have he (v : X) : Continuous (e v) := v.continuous.comp continuous_projIcc
  have hR (v : X) (i : ι) : MemLp (fun t ↦ B t (e v t) i) 2 μ :=
    ContinuousOn.memLp_of_subset_isCompact
      ((continuous_apply i).comp_continuousOn (hB.clm_apply (he v).continuousOn))
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  let R (v : X) (i : ι) := F i + (hR v i).toLp (fun t ↦ B t (e v t) i)
  have hRa (v : X) (i : ι) :
      (fun t ↦ R v i t) =ᵐ[μ] fun t ↦ F i t + B t (e v t) i := by
    filter_upwards [Lp.coeFn_add (F i) ((hR v i).toLp _), (hR v i).coeFn_toLp]
      with t ht ht'
    exact ht.trans (congrArg (F i t + ·) ht')
  choose u g z heq _hH2 hw hc hr hi _hb using
    fun (v : X) (i : ι) ↦ exists_heat_solution hε hab (R v i) (q i)
  let P : X → X := fun v ↦
    ⟨fun t i ↦ z v i t,
      continuous_pi fun i ↦ (continuousOn_iff_continuous_domRestrict.mp (hc v i))⟩
  have hBn : ContinuousOn (fun t ↦ ‖B t‖) (Icc a b) :=
    (show Continuous (fun L : E →L[ℝ] (ι → DerivLp n 2 univ) ↦ ‖L‖) from
      continuous_norm (E := E →L[ℝ] (ι → DerivLp n 2 univ))).comp_continuousOn hB
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hBn
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  have hBM (t : ℝ) (ht : t ∈ Icc a b) : ‖B t‖ ≤ M :=
    (le_abs_self _).trans ((hM₀ t ht).trans (le_max_right _ _))
  let K : ℝ≥0 := ⟨((1 + (n : ℝ) / ε) * Real.exp (b - a)) * M ^ 2, by positivity⟩
  have hP (v w : X) (t : Icc a b) :
      dist (P v t) (P w t) ^ 2 ≤
        (K : ℝ) * ∫ s in a..t.1, dist (e v s) (e w s) ^ 2 := by
    have hnon : 0 ≤ (K : ℝ) * ∫ s in a..t.1, dist (e v s) (e w s) ^ 2 :=
      mul_nonneg K.coe_nonneg
        (intervalIntegral.integral_nonneg t.2.1 fun _ _ ↦ sq_nonneg _)
    apply (Real.sqrt_le_sqrt_iff hnon).mp
    rw [Real.sqrt_sq (dist_nonneg)]
    apply (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    have hb := heat_solution_sub_norm_sq_le_past_forcing hε (u v i) (u w i)
      (g v i) (g w i) (R v i) (R w i) (heq v i) (heq w i) (hw v i) (hw w i)
      (z v i) (z w i) (hc v i) (hc w i) (hr v i) (hr w i)
      ((hi v i).trans (hi w i).symm) t t.2
    rw [dist_eq_norm]
    apply hb.trans
    have hdiff : (fun s ↦ (R v i - R w i) s) =ᵐ[μ]
        fun s ↦ B s (e v s - e w s) i := by
      filter_upwards [Lp.coeFn_sub (R v i) (R w i), hRa v i, hRa w i]
        with s hs hsv hsw
      rw [hs, Pi.sub_apply, hsv, hsw, map_sub, Pi.sub_apply]
      abel
    have hint :
        (∫ s in a..t.1, ‖(R v i - R w i) s‖ ^ 2) ≤
          M ^ 2 * ∫ s in a..t.1, dist (e v s) (e w s) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le t.2.1,
        intervalIntegral.integral_of_le t.2.1]
      refine integral_mono_ae (((Lp.memLp (R v i - R w i)).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)).mono_measure
          (volume.restrict_mono_set (Ioc_subset_Ioc_right t.2.2)))
        ((Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self) ?_
      filter_upwards [hdiff.filter_mono (ae_mono (volume.restrict_mono_set
        (Ioc_subset_Ioc_right t.2.2))), ae_restrict_mem measurableSet_Ioc] with s hs hst
      rw [hs, dist_eq_norm, ← mul_pow]
      gcongr
      exact (norm_le_pi_norm _ i).trans ((B s).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (hBM s ⟨hst.1.le, hst.2.trans t.2.2⟩) (norm_nonneg _)))
    have hI := intervalIntegral.integral_nonneg (μ := volume) t.2.1
      (fun s _ ↦ sq_nonneg (dist (e v s) (e w s)))
    calc
      _ ≤ ((1 + (n : ℝ) / ε) * Real.exp (t.1 - a)) *
          (M ^ 2 * ∫ s in a..t.1, dist (e v s) (e w s) ^ 2) := by gcongr
      _ ≤ ((1 + (n : ℝ) / ε) * Real.exp (b - a)) *
          (M ^ 2 * ∫ s in a..t.1, dist (e v s) (e w s) ^ 2) := by
        gcongr
        exact t.2.2
      _ = (K : ℝ) * ∫ s in a..t.1, dist (e v s) (e w s) ^ 2 := (mul_assoc _ _ _).symm
  obtain ⟨v, hv, _⟩ :=
    PDE.Analysis.ODE.existsUnique_isFixedPt_of_integral_dist_sq_le hab.le P K hP
  have hfix (t : ℝ) (ht : t ∈ Icc a b) (i : ι) : e v t i = z v i t := by
    simp only [e, projIcc_of_mem hab.le ht]
    exact (congrArg (fun w : X ↦ w ⟨t, ht⟩ i) hv).symm
  refine ⟨u v, g v, e v, (he v).continuousOn, ?_, fun i ↦ ⟨?_, hw v i, ?_⟩⟩
  · funext i
    exact (hfix a (left_mem_Icc.mpr hab.le) i).trans (hi v i)
  · have hg' : (fun t ↦ g v i t) =ᵐ[μ] fun t ↦
        ε • Δ (u v i t) + R v i t := by
      rw [heq v i]
      filter_upwards [Lp.coeFn_add
        ((ε • (wkpLaplacianCLM :
          W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL 2 μ (u v i)) (R v i),
        (ε • (wkpLaplacianCLM :
          W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).coeFn_compLpL (u v i)]
        with t ht ht'
      rw [ht, Pi.add_apply, ht']
      rfl
    filter_upwards [hg', hRa v i] with t ht ht'
    rw [ht, ht', add_assoc]
  · filter_upwards [hr v i, ae_restrict_mem measurableSet_Ioc] with t ht hti
    exact (hfix t (Ioc_subset_Icc_self hti) i).trans ht

end PDE.Parabolic.Heat

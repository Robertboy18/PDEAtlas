/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.SeparateTraces
public import PDE.Analysis.Calculus.AbsolutelyContinuous.PowerGrowth

/-!
# Large-data blowup with an omitted initial/lateral corner

Let `Ω` be a bounded open set and `w > 0` a Dirichlet eigenfunction of `-Δ` in `Ω` with eigenvalue
`λ > 0`, normalized by `∫ w = 1`, that is `C²` in `Ω` and continuous with zero values on the
boundary. If `∫ w g > λ`, then for some `T` there is no solution of `uₜ - Δu = u²` on `[0, T] × Ω`
with zero lateral values and initial value `g` that is bounded, `C²` in the open cylinder,
continuous on the initial face in `Ω` and continuous up to the lateral boundary at positive times
(`not_global_bounded_dirichlet_square_solution`,
`not_global_bounded_square_solution_of_contDiffOn`). The data `g` may change sign, the initial and
lateral data may be incompatible at the corner, and no value or derivative is prescribed there.

This is Evans's §9.4.1, Theorem 1, for solutions that are bounded on each finite cylinder but need
not be regular at the boundary or at the corner. Unbounded corner singularities are not included.

## How it works

The weighted moment of a bounded candidate is continuous at time zero by dominated convergence. On
each positive-time strip, compactly supported truncations of `w` (`dirichletTest`) approximate the
moment uniformly (`abs_moment_sub_dirichletTest_le`), and their Green pairing needs only the lateral
traces (`dirichletTest_laplacian_pairing_lower`). This gives a form of Evans's inequality (5) for
signed solutions with an error from a shrinking boundary layer, which uniform lateral continuity
makes small. Neither nonnegativity of `u` nor a minimum principle is used. A strict margin in the
initial moment absorbs the error into slightly larger damping, and the scalar comparison
`le_mul_rpow_of_global_local_damped_power_trajectories_le` gives the contradiction.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 1 (Blow-up for large data) and its proof,
  (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open PDE.Analysis
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The strict eigenfunction threshold excludes bounded global candidates with
separate initial and lateral traces, including incompatible corner data. -/
theorem not_global_bounded_dirichlet_square_solution
    {g w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hlarge : lambda < ∫ x in Ω, w x * g x) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u, IsBoundedDirichletSquareSolution Ω T g u := by
  intro hglobal
  obtain ⟨L, hlambdaL, hLM⟩ := exists_between hlarge
  obtain ⟨m, hLm, hmM⟩ := exists_between hLM
  have hL : 0 < L := hlambda.trans hlambdaL
  have hm : 0 < m := hL.trans hLm
  have hwn : ∀ x ∈ Ω, 0 ≤ w x := fun x hx ↦ (hwpos x hx).le
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have hV : 0 ≤ volume.real Ω := measureReal_nonneg
  have hbound := le_mul_rpow_of_global_local_damped_power_trajectories_le
    (c := 1) (p := 2) hm (by norm_num) (by norm_num) hL (by
      intro T hT
      obtain ⟨u, hu⟩ := hglobal (T + 2) (by linarith)
      obtain ⟨B, hB, hBu⟩ := hu.bounded
      let M : ℝ → ℝ := fun t ↦ ∫ x in Ω, w x * u t x
      have hMc : ContinuousOn M (Icc 0 (T + 2)) :=
        hu.weighted_moment_continuous hΩ.measurableSet (hint hwc)
      have hM0 : M 0 = ∫ x in Ω, w x * g x :=
        setIntegral_congr_fun hΩ.measurableSet fun x hx ↦ by simp only [hu.initial x hx]
      obtain ⟨a, hk, ha0, ha1⟩ : ∃ a, m < M a ∧ 0 < a ∧ a < 1 := by
        have hc := (hMc.continuousWithinAt ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin
          (mem_of_superset (Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < T + 2)) Ioo_subset_Icc_self)
        exact ((hc.tendsto.eventually (lt_mem_nhds (by rw [hM0]; exact hmM))).and
          (Ioo_mem_nhdsGT one_pos)).exists.imp fun a h ↦ ⟨h.1, h.2.1, h.2.2⟩
      have hu' := hu.shift (S := T + 1) ha0 (by linarith)
      have huc (t : ℝ) (ht : t ∈ Ioc 0 (T + 2)) : ContinuousOn (u t) (closure Ω) :=
        hu.lateral_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun _ hx ↦ ⟨ht, hx⟩)
      let gap := (L - lambda) * L
      have hgap : 0 < gap := mul_pos (sub_pos.mpr hlambdaL) hL
      obtain ⟨η, hη, hηgap⟩ := exists_pos_mul_lt (half_pos hgap) lambda
      obtain ⟨e, he, helayer⟩ := hu.exists_boundary_layer hb hwc hwpos hwzero
        ha0 (b := a + (T + 1)) (by linarith) hη
      obtain ⟨e₀, he₀, he₀gap⟩ := exists_pos_mul_lt
        (sub_pos.mpr hk) (2 * B * volume.real Ω)
      obtain ⟨e₁, he₁, he₁gap⟩ := exists_pos_mul_lt (half_pos hgap)
        (2 * lambda * (η + B) * volume.real Ω)
      let ε := min e (min e₀ e₁)
      have hε : 0 < ε := lt_min he (lt_min he₀ he₁)
      have hεe : ε ≤ e := min_le_left _ _
      have hε₀ : ε ≤ e₀ := (min_le_right _ _).trans (min_le_left _ _)
      have hε₁ : ε ≤ e₁ := (min_le_right _ _).trans (min_le_right _ _)
      have herr₀ : 2 * ε * B * volume.real Ω < M a - m := by
        have h := (mul_le_mul_of_nonneg_left hε₀
          (by positivity : 0 ≤ 2 * B * volume.real Ω)).trans_lt he₀gap
        change _ < M a - m at h
        nlinarith
      let E := η * lambda + (2 * lambda * ε) * (η + B) * volume.real Ω
      have herr : E < (L - lambda) * L := by
        have h := (mul_le_mul_of_nonneg_left hε₁
          (by positivity : 0 ≤ 2 * lambda * (η + B) * volume.real Ω)).trans_lt he₁gap
        dsimp only [E, gap] at *
        nlinarith
      let φ := dirichletTest Ω w ε
      have hφ : ContDiff ℝ 2 φ := contDiff_dirichletTest hΩ hε hw hwc hwzero
      have hc : HasCompactSupport φ := hasCompactSupport_dirichletTest hb hε hwc hwzero
      have hs : tsupport φ ⊆ Ω := tsupport_dirichletTest_subset hε hwc hwzero
      have hφpos : ∀ x, 0 ≤ φ x := fun x ↦ (dirichletTest_bounds hwn x).1
      have hmass : ∫ x, φ x ≤ 1 := by
        rw [← hunit]
        exact integral_dirichletTest_le hΩ hb hε hw hwc hwzero hwn
      let y : ℝ → ℝ := fun t ↦ ∫ x, φ x * u (a + t) x
      have hzero : m < y 0 := by
        have h := abs_moment_sub_dirichletTest_le hΩ hb hε hw hwc hwzero hwn
          (huc a ⟨ha0, by linarith⟩)
          (fun x hx ↦ hBu a ⟨ha0.le, by linarith⟩ x hx)
        have hle := (abs_le.mp h).2
        change M a - (∫ x, φ x * u a x) ≤ _ at hle
        dsimp only [y]
        simp only [add_zero]
        linarith
      have hy : ContinuousOn y (Icc 0 (T + 1)) :=
        hu'.compact_moment_continuous hφ.continuous hc hs
      have hd (t : ℝ) (ht : t ∈ Ioo 0 (T + 1)) : DifferentiableAt ℝ y t :=
        (hu'.hasDerivAt_compact_moment hΩ hφ.continuous hc hs ht).differentiableAt
      have hgrowth (t : ℝ) (ht : t ∈ Ioo 0 (T + 1)) :
          y t ^ 2 ≤ deriv y t + lambda * y t + E := by
        have hj := hu'.compact_moment_reaction_le hΩ hφ hc hs hφpos hmass ht
        have he := dirichletTest_laplacian_pairing_lower hΩ hb hε hlambda.le hη.le hB.le
          hw hwc hwzero hwn hunit.le heigen
          (huc (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          (fun x hx ↦ hBu (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx)
          (fun x hx hxw ↦ (helayer (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
            x hx (hxw.trans (mul_le_mul_of_nonneg_left hεe (by norm_num)))).le)
        change y t ^ 2 ≤ deriv y t - (∫ x, laplacian φ x * u (a + t) x) at hj
        change -lambda * y t - η * lambda -
          (2 * lambda * ε) * (η + B) * volume.real Ω ≤ _ at he
        dsimp only [E]
        linarith
      have hbarrier := le_of_continuousOn_deriv_pos_at_level hy (hLm.trans hzero) hd (by
        intro t ht heq
        have h := hgrowth t ht
        rw [heq] at h
        nlinarith)
      refine ⟨y, hy.mono (Icc_subset_Icc le_rfl (by linarith)), ?_, hzero.le, ?_, ?_⟩
      · intro b hb
        exact (hu'.compact_moment_regularity hΩ hφ.continuous hc hs hb.1
          (by linarith) hb.2).1
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hL.le.trans (hbarrier t ⟨ht.1.le, by linarith [ht.2]⟩)
      · rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have ht' : t ∈ Ioo 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
        have h := hgrowth t ht'
        have hk := hbarrier t ⟨ht.1.le, ht'.2⟩
        have herr' := herr.trans_le (mul_le_mul_of_nonneg_left hk (sub_pos.mpr hlambdaL).le)
        simpa only [one_mul, Real.rpow_two] using (show y t ^ 2 ≤ deriv y t + L * y t by
          nlinarith))
  norm_num only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
    ← div_eq_mul_inv] at hbound
  have hle := (le_div_iff₀ hm).mp hbound
  exact hLm.not_ge (by simpa only [one_mul] using hle)

/-- Explicit PDE form of the bounded, separate-trace blowup theorem. The initial
trace is imposed inside the domain; no continuity or value is imposed at the
initial/lateral corner. Boundedness is explicit and no derivative trace is used. -/
theorem not_global_bounded_square_solution_of_contDiffOn
    {g w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hlarge : lambda < ∫ x in Ω, w x * g x) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u : ℝ → ℝ^n → ℝ,
      ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω) ∧
      ContinuousOn u.uncurry (Ioc 0 T ×ˢ closure Ω) ∧
      (∃ B > 0, ∀ t ∈ Icc 0 T, ∀ x ∈ Ω, |u t x| ≤ B) ∧
      ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω) ∧
      (∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
        deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2) ∧
      (∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u t x = 0) ∧
      (∀ x ∈ Ω, u 0 x = g x) := by
  intro hglobal
  apply not_global_bounded_dirichlet_square_solution hΩ hb hw hwc hwzero hwpos hunit
    heigen hlambda hlarge
  intro T hT
  obtain ⟨u, hinitc, hlatc, hB, hs, heq, hboundary, hinit⟩ := hglobal T hT
  exact ⟨u, hinitc, hlatc, hB, hs, heq, hboundary, hinit⟩

end HeatEquation.Nonlinear

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave
import CAS.ExactTactic

/-!
# Free waves and compact families of Cauchy data

Kirchhoff's formula gives the full free field, its initial traces, and joint
regularity in profile parameters. A common support radius on a compact
parameter set gives a uniform bound on each finite forward time slab.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The full free wave in time-first product coordinates. -/
def cauchyFreeField (g h : ℝ^3 → ℝ) (p : ℝ × ℝ^3) : ℝ :=
  spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons p.1 p.2)

/-- Two displacement derivatives and one velocity derivative give a jointly
C¹ free field, including the initial time. -/
theorem contDiff_one_cauchyFreeField {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 1 (cauchyFreeField g h) := by
  have hc : ContDiff ℝ 1 (spaceTimeUncurry (kirchhoffFormula g h)) := by
    rw [kirchhoffFormula_eq_potentials (hg.of_le (by norm_num)) hh.continuous]
    exact (contDiff_partialDeriv_of_succ (m := 1)
      (contDiff_kirchhoffPotential hg)).add (contDiff_kirchhoffPotential hh)
  exact hc.comp (contDiff_timeSpaceCons_uncurry 3)

/-- The full free field retains the arbitrary initial displacement. -/
@[simp] theorem cauchyFreeField_initial_position (g h : ℝ^3 → ℝ) (x : ℝ^3) :
    cauchyFreeField g h (0, x) = g x := kirchhoffFormula_initial_position g h x

/-- The full free field has the prescribed ordinary time derivative at zero. -/
theorem hasDerivAt_cauchyFreeField_initial_velocity {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (x : ℝ^3) :
    HasDerivAt (fun t ↦ cauchyFreeField g h (t, x)) (h x) 0 := by
  have hc : ContDiff ℝ 1 (spaceTimeUncurry (kirchhoffFormula g h)) := by
    rw [kirchhoffFormula_eq_potentials (hg.of_le (by norm_num)) hh.continuous]
    exact (contDiff_partialDeriv_of_succ (m := 1)
      (contDiff_kirchhoffPotential hg)).add (contDiff_kirchhoffPotential hh)
  have hd : DifferentiableAt ℝ (fun t : ℝ ↦ cauchyFreeField g h (t, x)) 0 :=
    ((contDiff_one_cauchyFreeField hg hh).comp
      (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero (0 : ℝ)
  convert hd.hasDerivAt using 1
  rw [← partialDeriv_kirchhoffFormula_initial_velocity hg hh x,
    partialDeriv_timeSpaceCons_eq_deriv _ _ _ (hc.differentiable one_ne_zero _)]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite joint regularity of the Cauchy profiles gives joint regularity of
parameterized free waves, including time zero. -/
theorem contDiff_cauchyFreeField_family {k : ℕ} {g h : E × ℝ^3 → ℝ}
    (hg : ContDiff ℝ (k + 1 : ℕ) g) (hh : ContDiff ℝ k h) :
    ContDiff ℝ k (fun z : E × (ℝ × ℝ^3) ↦
      cauchyFreeField (fun x ↦ g (z.1, x)) (fun x ↦ h (z.1, x)) z.2) := by
  -- Expand the time derivative before integrating, so the parameter stays explicit.
  let A : (E × (ℝ × ℝ^3)) × ℝ^3 → E × ℝ^3 := fun z ↦ (z.1.1, z.1.2.2 + z.1.2.1 • z.2)
  let F : (E × (ℝ × ℝ^3)) × ℝ^3 → ℝ := fun z ↦
    g (A z) + z.1.2.1 * fderiv ℝ g (A z) (0, z.2) + z.1.2.1 * h (A z)
  have hA : ContDiff ℝ k A := contDiff_fst.fst.prodMk (contDiff_fst.snd.snd.add
      (contDiff_fst.snd.fst.smul contDiff_snd))
  have hF : ContDiff ℝ k F :=
    ((hg.of_le (by norm_num)).comp hA).add (contDiff_fst.snd.fst.mul
        (((hg.fderiv_right (by norm_num)).comp hA).clm_apply
          (contDiff_const.prodMk contDiff_snd))) |>.add (contDiff_fst.snd.fst.mul (hh.comp hA))
  have havg := (contDiff_integral_compact_parametrization
    (μ := (volume : Measure (ℝ^3)).toSphere) hF continuous_subtype_val).div_const (unitSphereArea 3)
  suffices heq : (fun z : E × (ℝ × ℝ^3) ↦
      cauchyFreeField (fun x ↦ g (z.1, x)) (fun x ↦ h (z.1, x)) z.2) =
      (fun z ↦ (∫ ω : Metric.sphere (0 : ℝ^3) 1, F (z, (ω : ℝ^3))
        ∂(volume : Measure (ℝ^3)).toSphere) / unitSphereArea 3) by
    rw [heq]
    exact havg
  funext z
  have hgs : ContDiff ℝ 1 (fun x : ℝ^3 ↦ g (z.1, x)) :=
    (hg.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id)
  have hhs : Continuous (fun x : ℝ^3 ↦ h (z.1, x)) :=
    hh.continuous.comp (continuous_const.prodMk continuous_id)
  have hder (y ω : ℝ^3) :
      fderiv ℝ (fun x : ℝ^3 ↦ g (z.1, x)) y ω = fderiv ℝ g (z.1, y) (0, ω) := by
    have hdg := ((hg.differentiable (by norm_num) _).hasFDerivAt.comp y
      ((hasFDerivAt_const z.1 y).prodMk (hasFDerivAt_id y))).fderiv
    change fderiv ℝ (fun x ↦ g (z.1, x)) y = _ at hdg
    rw [hdg]
    rfl
  have hd := ((hasDerivAt_id z.2.1).fun_mul
    (hasDerivAt_unitSphereAverage (fun x ↦ g (z.1, x)) z.2.2 z.2.1 hgs)).deriv
  simp only [id_eq, one_mul] at hd
  have hi {f : Metric.sphere (0 : ℝ^3) 1 → ℝ} (hf : Continuous f) :
      Integrable f ((volume : Measure (ℝ^3)).toSphere) := hf.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ mem_univ _))
  have hc : Continuous (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ (z.1, z.2.2 + z.2.1 • (ω : ℝ^3))) := by
    fun_prop
  have hgi := hi (hg.continuous.comp hc)
  have hhi := hi (hh.continuous.comp hc)
  have hdi := hi (((hg.continuous_fderiv (by norm_num)).comp hc).clm_apply
    ((continuous_const (y := (0 : E))).prodMk continuous_subtype_val))
  change kirchhoffFormula (fun x ↦ g (z.1, x)) (fun x ↦ h (z.1, x)) z.2.2 z.2.1 = _
  rw [kirchhoffFormula_eq_sphericalMean hgs hhs, hd]
  simp only [unitSphereAverage, F, A]
  simp_rw [hder]
  have hadd := integral_add (hgi.add (hdi.const_mul z.2.1)) (hhi.const_mul z.2.1)
  have hgd := integral_add hgi (hdi.const_mul z.2.1)
  simp only [Pi.add_apply, Function.comp_apply] at hadd hgd
  rw [hadd, hgd, integral_const_mul, integral_const_mul]
  cas

/-- A compact family of Cauchy profiles with one common support radius has a
uniformly bounded free wave on each finite forward time slab. -/
theorem exists_bound_cauchyFreeField_family_of_common_support {g h : E × ℝ^3 → ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {K : Set E} (hK : IsCompact K) {R : ℝ}
    (hgs : ∀ a ∈ K, ∀ x : ℝ^3, R < ‖x‖ → g (a, x) = 0)
    (hhs : ∀ a ∈ K, ∀ x : ℝ^3, R < ‖x‖ → h (a, x) = 0) (S : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ K, ∀ p : ℝ × ℝ^3,
      p.1 ∈ Icc 0 S → |cauchyFreeField (fun x ↦ g (a, x)) (fun x ↦ h (a, x)) p| ≤ B := by
  have hH := contDiff_cauchyFreeField_family (k := 1) hg hh
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc.prod
    (isCompact_closedBall (0 : ℝ^3) (R + S)))).exists_bound_of_continuousOn
      hH.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun a ha p hp ↦ ?_⟩
  by_cases hx : p.2 ∈ Metric.closedBall (0 : ℝ^3) (R + S)
  · exact (show |cauchyFreeField (fun x ↦ g (a, x)) (fun x ↦ h (a, x)) p| ≤ B by
      simpa only [Real.norm_eq_abs] using hB (a, p) ⟨ha, hp, hx⟩).trans (le_max_left _ _)
  · have hzero := WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      ((hg.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id))
      (hh.continuous.comp (continuous_const.prodMk continuous_id))
      (hgs a ha) (hhs a ha) p.1 hp.1 p.2
    have hout : R + S < ‖p.2‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hz := hzero (by linarith [hp.2])
    change |kirchhoffFormula (fun x ↦ g (a, x)) (fun x ↦ h (a, x)) p.2 p.1| ≤ max B 0
    change kirchhoffFormula (fun x ↦ g (a, x)) (fun x ↦ h (a, x)) p.2 p.1 = 0 at hz
    rw [hz, abs_zero]
    exact le_max_right _ _

/-- The Kirchhoff field of compact data is uniformly bounded on each finite
closed forward slab. The bound follows from finite propagation and compactness. -/
theorem exists_bound_cauchyFreeField_of_compact_data {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) (S : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S → |cauchyFreeField g h p| ≤ B := by
  obtain ⟨Rg, _, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  obtain ⟨B, hB, hbound⟩ := exists_bound_cauchyFreeField_family_of_common_support
    (E := ℝ) (hg.comp contDiff_snd) (hh.comp contDiff_snd)
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) (R := max Rg Rh)
    (fun _ _ x hx ↦ hgR x ((le_max_left _ _).trans hx.le))
    (fun _ _ x hx ↦ hhR x ((le_max_right _ _).trans hx.le)) S
  exact ⟨B, hB, fun q hq ↦ hbound 0 (mem_singleton 0) q hq⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

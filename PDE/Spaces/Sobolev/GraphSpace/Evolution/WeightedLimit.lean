/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.Limit

/-!
# Origin traces and weighted energies of H¹ limits

Graph-norm convergence gives convergence of the real `L²` derivative
coordinates and of continuous point traces. Fatou then passes a uniform
weighted derivative error bound to the limit, including its integrability.
The time-convergence corollary constructs the limit and proves these
properties from the approximating trajectory.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Every real derivative coordinate preserves a uniformly bounded
nonnegative weighted error energy under H¹ convergence. -/
theorem weighted_coordinate_error_limit
    {ν : Measure ℝ} (hν : ν ≤ volume)
    {u : ℕ → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)}
    {b w : ℝ → ℝ} {C : ℝ} (a : DerivIndex 1 1)
    (hu : Tendsto u atTop (𝓝 U)) (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (henergy : ∀ n, Integrable
      (fun x ↦ (realLineCoordinateCLM a (u n) x - b x) ^ 2 * w x) ν)
    (hbound : ∀ n,
      (∫ x, (realLineCoordinateCLM a (u n) x - b x) ^ 2 * w x ∂ν) ≤ C) :
    Integrable (fun x ↦ (realLineCoordinateCLM a U x - b x) ^ 2 * w x) ν ∧
      (∫ x, (realLineCoordinateCLM a U x - b x) ^ 2 * w x ∂ν) ≤ C :=
  integrable_weighted_sq_sub_and_integral_le_of_tendsto_L2 hν
    (((realLineCoordinateCLM a).continuous.tendsto U).comp hu) hw henergy hbound

/-- A weighted bound on the real derivatives of weak H¹ data passes
to the real derivative of their graph-space limit. -/
theorem weighted_derivative_error_limit_of_mkW12_tendsto
    {ν : Measure ℝ} (hν : ν ≤ volume)
    {f g : ℕ → ℝ → ℝ} (hf : ∀ n, MemLp (f n) 2 volume)
    (hg : ∀ n, MemLp (g n) 2 volume)
    (hweak : ∀ n, HasWeakTimeDerivativeOn univ (f n) (g n))
    {U : W^{1,2}(ℝ^1)}
    (hu : Tendsto (fun n ↦ mkW12OfWeakDerivative (hf n) (hg n) (hweak n)) atTop (𝓝 U))
    {b w : ℝ → ℝ} {C : ℝ} (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (henergy : ∀ n, Integrable (fun x ↦ (g n x - b x) ^ 2 * w x) ν)
    (hbound : ∀ n, (∫ x, (g n x - b x) ^ 2 * w x ∂ν) ≤ C) :
    Integrable
      (fun x ↦ (realLineCoordinateCLM (singleDerivIndex 1 0) U x - b x) ^ 2 * w x) ν ∧
      (∫ x, (realLineCoordinateCLM (singleDerivIndex 1 0) U x - b x) ^ 2 * w x ∂ν) ≤ C := by
  have hae (n : ℕ) :
      (fun x ↦ (realLineCoordinateCLM (singleDerivIndex 1 0)
        (mkW12OfWeakDerivative (hf n) (hg n) (hweak n)) x - b x) ^ 2 * w x)
      =ᵐ[ν] (fun x ↦ (g n x - b x) ^ 2 * w x) := by
    rw [realLineCoordinateCLM_mkW12_single]
    filter_upwards [(MemLp.coeFn_toLp (hg n)).filter_mono (ae_mono hν)] with x hx
    rw [hx]
  apply weighted_coordinate_error_limit hν (singleDerivIndex 1 0) hu hw
  · intro n
    exact (henergy n).congr (hae n).symm
  · intro n
    rw [integral_congr_ae (hae n)]
    exact hbound n

/-- A shared value at the origin of continuous weak H¹ inputs passes to
the explicit continuous representative of their graph-space limit. -/
theorem realLineRepresentative_zero_of_mkW12_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f g : ι → ℝ → ℝ} (hf : ∀ i, MemLp (f i) 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakTimeDerivativeOn univ (f i) (g i))
    {U : W^{1,2}(ℝ^1)}
    (hu : Tendsto (fun i ↦ mkW12OfWeakDerivative (hf i) (hg i) (hweak i)) l (𝓝 U))
    (hcont : ∀ᶠ i in l, Continuous (f i))
    (hzero : ∀ᶠ i in l, f i 0 = 0) :
    realLineRepresentative U 0 = 0 := by
  apply realLineRepresentative_limit_value hu
  filter_upwards [hcont, hzero] with i hi hzi
  rw [realLineRepresentative_mkW12 (hf i) (hg i) (hweak i) hi]
  exact hzi

/-- Exponentially decaying real `L²` time derivatives construct an
H¹ limit whose continuous representative vanishes at the origin and whose
weighted derivative error remains bounded. All limit properties are
conclusions: the hypotheses concern the trajectory and its time derivatives. -/
theorem exists_limit_mkW12_with_origin_and_weighted_error
    {ν : Measure ℝ} (hν : ν ≤ volume)
    {f g : ℝ → ℝ → ℝ} (hf : ∀ t, MemLp (f t) 2 volume)
    (hg : ∀ t, MemLp (g t) 2 volume)
    (hweak : ∀ t, HasWeakTimeDerivativeOn univ (f t) (g t))
    {F G : ℝ → Lp ℝ 2 (volume : Measure ℝ)} {a C γ E : ℝ}
    {b w : ℝ → ℝ} (hγ : 0 < γ)
    (hF : ∀ t ∈ Ici a, HasDerivAt (fun s ↦ (hf s).toLp (f s)) (F t) t)
    (hG : ∀ t ∈ Ici a, HasDerivAt (fun s ↦ (hg s).toLp (g s)) (G t) t)
    (hFm : AEStronglyMeasurable F (volume.restrict (Ioi a)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioi a)))
    (hdecay : ∀ t ∈ Ioi a, ‖F t‖ + ‖G t‖ ≤ C * Real.exp (-γ * t))
    (hcont : ∀ t ∈ Ici a, Continuous (f t))
    (hzero : ∀ t ∈ Ici a, f t 0 = 0)
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (henergy : ∀ t ∈ Ici a, Integrable (fun x ↦ (g t x - b x) ^ 2 * w x) ν)
    (hbound : ∀ t ∈ Ici a, (∫ x, (g t x - b x) ^ 2 * w x ∂ν) ≤ E) :
    ∃ U : W^{1,2}(ℝ^1),
      Tendsto (fun t ↦ mkW12OfWeakDerivative (hf t) (hg t) (hweak t)) atTop (𝓝 U) ∧
      (∀ t ∈ Ici a, ‖U - mkW12OfWeakDerivative (hf t) (hg t) (hweak t)‖ ≤
        C * Real.exp (-γ * t) / γ) ∧
      realLineRepresentative U 0 = 0 ∧
      Integrable
        (fun x ↦ (realLineCoordinateCLM (singleDerivIndex 1 0) U x - b x) ^ 2 * w x) ν ∧
      (∫ x, (realLineCoordinateCLM (singleDerivIndex 1 0) U x - b x) ^ 2 * w x ∂ν) ≤ E := by
  obtain ⟨U, hU, hrate⟩ :=
    exists_limit_mkW12OfWeakDerivative_of_norm_le_exp hf hg hweak hγ hF hG hFm hGm hdecay
  have htendsto : Tendsto (fun n : ℕ ↦ a + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop a tendsto_natCast_atTop_atTop
  have htime (n : ℕ) : a + (n : ℝ) ∈ Ici a := by
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hsample := hU.comp htendsto
  have hweighted := weighted_derivative_error_limit_of_mkW12_tendsto hν
    (fun n ↦ hf (a + (n : ℝ))) (fun n ↦ hg (a + (n : ℝ)))
    (fun n ↦ hweak (a + (n : ℝ))) hsample hw
    (fun n ↦ henergy _ (htime n)) (fun n ↦ hbound _ (htime n))
  refine ⟨U, hU, hrate, ?_, hweighted⟩
  apply realLineRepresentative_zero_of_mkW12_tendsto (l := atTop)
    (fun n : ℕ ↦ hf (a + (n : ℝ))) (fun n : ℕ ↦ hg (a + (n : ℝ)))
    (fun n : ℕ ↦ hweak (a + (n : ℝ))) hsample
  · exact Eventually.of_forall fun n ↦ hcont _ (htime n)
  · exact Eventually.of_forall fun n ↦ hzero _ (htime n)

end SobolevSpace.GraphSpace

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Basic
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.LocalizedMaximum
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SpatialComparison
import PDE.Analysis.Metric.QuadraticPenalty
import CAS.ExactTactic

/-!
# Finite-horizon comparison for position-dependent Hamiltonians

Assume that `H(p,x)` is uniformly Lipschitz in momentum and satisfies
`|H(p,x)-H(p,y)| ≤ Cx * ‖x-y‖ * (1+‖p‖)`. Ordered initial values then give
an ordering between a viscosity subsolution and a supersolution that are
bounded and uniformly continuous on the prescribed finite closed time slab.
The equation is needed only in its open interior.

The proof uses the local `C¹` touching-test predicates. Finite dimensionality gives compact balls,
and `exists_isMaxOn_quadratic_barrier` constructs an interior maximum.

There are two errors after subtracting the viscosity inequalities.
Uniform momentum Lipschitz control makes the localization error small
before the doubling scale is chosen. Comparing the maximum with both
diagonal pairs then makes the separation penalty small. This second step
controls `‖x-y‖²/ε`, not just `‖x-y‖`, in the spatial Hamiltonian error.
The positive time barrier contradicts the resulting small upper bound.

The two Lipschitz constants may differ and may vanish. The autonomous
theorem in `InitialComparison` needs only continuity of `H`.

A barrier horizon between the target time and the supplied terminal time keeps
every contact inside the equation domain. Continuity gives terminal comparison.

The assumptions are condition (3) of Evans, §10.2, and the result is his Theorem 1 in comparison
form, proved by doubling variables. Evans takes one parameter `ε` in (5) for the doubling and the
localization; we choose the localization scale first.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, condition (3), Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

noncomputable section

open Set

-- Localization controls the two momentum corrections independently of ε.
private theorem localization_momentum_error_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Cp : NNReal} {α M r c : ℝ} {z w : E × ℝ}
    (hα : 0 < α) (hM : 0 < M) (hr : 0 < r)
    (hαH : α < r ^ 2 / (16 * (M + 1)))
    (hzbound : α * quadraticSize z < M) (hwbound : α * quadraticSize w < M)
    (hrscale : ((Cp : ℝ) + 1) * r = c / 4) :
    2 * Cp * |α| * (‖z.1‖ + ‖w.1‖) < c / 4 := by
  have hgz := norm_localization_gradient_lt hα hM hr hαH hzbound
  have hgw := norm_localization_gradient_lt hα hM hr hαH hwbound
  have hgradient_sum : 2 * α * (‖z.1‖ + ‖w.1‖) < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * α)] at hgz hgw
    nlinarith only [hgz, hgw]
  have hmomentum_error :
      2 * Cp * |α| * (‖z.1‖ + ‖w.1‖) < c / 4 := by
    have hnonneg : 0 ≤ 2 * α * (‖z.1‖ + ‖w.1‖) := by positivity
    have hle := mul_le_mul_of_nonneg_right
      (show (Cp : ℝ) ≤ (Cp : ℝ) + 1 by linarith only []) hnonneg
    have hlt := mul_lt_mul_of_pos_left hgradient_sum
      (show (0 : ℝ) < (Cp : ℝ) + 1 by positivity)
    rw [hrscale] at hlt
    rw [abs_of_pos hα]
    nlinarith only [hle, hlt]
  exact hmomentum_error

-- Put the attained barrier maximum into the two-diagonal estimate.
private theorem exists_small_separation_penalty {E : Type*} [NormedAddCommGroup E] {K : Set (E × ℝ)}
    {u v : E × ℝ → ℝ} {M δ : ℝ} (hu : UniformContinuousOn u K) (hv : UniformContinuousOn v K)
    (hM : 0 < M) (hδ : 0 < δ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ α a T : ℝ,
      ∀ z ∈ K, ∀ w ∈ K, quadraticSize (z - w) / (2 * ε) < M →
        IsMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦
          u q.1 - v q.2 -
            (quadraticSize (q.1 - q.2) / (2 * ε) +
              α * (quadraticSize q.1 + quadraticSize q.2) +
              a / (T - q.1.2) + a / (T - q.2.2))) (K ×ˢ K) (z, w) →
        quadraticSize (z - w) / (2 * ε) < δ / 2 := by
  obtain ⟨ε₀, hε₀, hsmall⟩ := Metric.exists_penalty_lt_of_isMaxOn_sub
    hu hv hM (show 0 < δ / 2 by positivity)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε α a T z hzK w hwK hbound hmax
  have hdiag (x : E × ℝ) (_hx : x ∈ K) : quadraticSize (x - x) = 0 := by
    simp only [sub_self, quadraticSize, Prod.fst_zero, Prod.snd_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero]
  have hmax' : IsMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 -
          (quadraticSize (q.1 - q.2) / (2 * ε) + (α * quadraticSize q.1 + a / (T - q.1.2)) +
            (α * quadraticSize q.2 + a / (T - q.2.2))))
      (K ×ˢ K) (z, w) := by
    apply isMaxOn_iff.mpr
    intro q hq
    have h := (isMaxOn_iff.mp hmax) q hq
    change u q.1 - v q.2 - (quadraticSize (q.1 - q.2) / (2 * ε) +
        α * (quadraticSize q.1 + quadraticSize q.2) + a / (T - q.1.2) + a / (T - q.2.2)) ≤
      u z - v w - (quadraticSize (z - w) / (2 * ε) + α * (quadraticSize z + quadraticSize w) +
          a / (T - z.2) + a / (T - w.2)) at h
    simpa only [mul_add, add_assoc, add_left_comm, add_comm] using h
  exact hsmall ε hε (fun x y ↦ quadraticSize (x - y)) (fun x ↦ α * quadraticSize x + a / (T - x.2))
    hdiag z hzK w hwK (dist_sq_le_quadraticSize_sub z w) hbound.le hmax'

-- Both the separation and its squared-over-scale term must be small.
private theorem separation_spatial_error_lt {E : Type*} [NormedAddCommGroup E] {Cx : NNReal}
    {ε M δ c : ℝ} {z w : E × ℝ} (hε : 0 < ε) (hM : 0 < M) (hδ : 0 < δ)
    (hεdistance : ε < δ ^ 2 / (2 * M)) (hbound : quadraticSize (z - w) / (2 * ε) < M)
    (hsmall_penalty : quadraticSize (z - w) / (2 * ε) < δ / 2)
    (hδscale : ((Cx : ℝ) + 1) * δ = c / 8) :
    Cx * (‖z.1 - w.1‖ + ‖z.1 - w.1‖ ^ 2 / ε) < c / 4 := by
  have hspace_sq : ‖z.1 - w.1‖ ^ 2 ≤ quadraticSize (z - w) := norm_fst_sq_le_quadraticSize (z - w)
  have hseparation : ‖z.1 - w.1‖ < δ := by
    have hcost := (div_lt_iff₀ (show 0 < 2 * ε by positivity)).mp hbound
    have hscale := (lt_div_iff₀ (show 0 < 2 * M by positivity)).mp hεdistance
    apply (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp
    nlinarith only [hspace_sq, hcost, hscale]
  have hseparation_sq : ‖z.1 - w.1‖ ^ 2 / ε < δ := by
    have hcost := (div_lt_iff₀ (show 0 < 2 * ε by positivity)).mp hsmall_penalty
    apply (div_lt_iff₀ hε).mpr
    nlinarith only [hspace_sq, hcost]
  have hspatial_error :
      Cx * (‖z.1 - w.1‖ + ‖z.1 - w.1‖ ^ 2 / ε) < c / 4 := by
    have hsum : ‖z.1 - w.1‖ + ‖z.1 - w.1‖ ^ 2 / ε < 2 * δ := by
      linarith only [hseparation, hseparation_sq]
    have hnonneg : 0 ≤ ‖z.1 - w.1‖ + ‖z.1 - w.1‖ ^ 2 / ε := by positivity
    have hle := mul_le_mul_of_nonneg_right
      (show (Cx : ℝ) ≤ (Cx : ℝ) + 1 by linarith only []) hnonneg
    have hlt := mul_lt_mul_of_pos_left hsum
      (show (0 : ℝ) < (Cx : ℝ) + 1 by positivity)
    nlinarith only [hle, hlt, hδscale]
  exact hspatial_error

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

-- Both contacts stay strictly inside the supplied finite horizon.
private theorem le_of_initial_le_of_lipschitz_of_lt_horizon {H : E → E → ℝ} {u v : E × ℝ → ℝ}
    {Cp Cx : NNReal} {U V : Set (E × ℝ)} {T₀ : ℝ} (hu : IsSpatialViscositySubsolution H U u)
    (hv : IsSpatialViscositySupersolution H V v) (hU : openTimeSlab T₀ ⊆ U)
    (hV : openTimeSlab T₀ ⊆ V) (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T₀) ∧ UniformContinuousOn u (closedTimeSlab T₀))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T₀) ∧ UniformContinuousOn v (closedTimeSlab T₀))
    (hinit : ∀ x : E, u (x, 0) ≤ v (x, 0)) {z₀ : E × ℝ} (hz₀ : 0 ≤ z₀.2) (hz₀T₀ : z₀.2 < T₀) :
    u z₀ ≤ v z₀ := by
  by_contra hnot
  have hgap : 0 < u z₀ - v z₀ := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨T, hz₀ltT, hTT₀⟩ := exists_between hz₀T₀
  have hT : 0 < T := lt_of_le_of_lt hz₀ hz₀ltT
  have hslab : closedTimeSlab (E := E) T ⊆ closedTimeSlab T₀ :=
    fun _ hz ↦ ⟨hz.1, hz.2.trans hTT₀.le⟩
  have hubT : Bornology.IsBounded (u '' closedTimeSlab T) ∧
      UniformContinuousOn u (closedTimeSlab T) :=
    ⟨hub.1.subset (image_mono hslab), hub.2.mono hslab⟩
  have hvbT : Bornology.IsBounded (v '' closedTimeSlab T) ∧
      UniformContinuousOn v (closedTimeSlab T) :=
    ⟨hvb.1.subset (image_mono hslab), hvb.2.mono hslab⟩
  obtain ⟨M, hM, a, ha, S, hST, ε₀, hε₀, hlocalize⟩ :=
    exists_localized_maximum_of_initial_le hubT.1 hvbT.1 hubT.2 hvbT.2 hinit hz₀ hz₀ltT hgap
  let c := a / T ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  let r := c / (4 * ((Cp : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrscale : ((Cp : ℝ) + 1) * r = c / 4 := by
    dsimp only [r]
    have hne : (Cp : ℝ) + 1 ≠ 0 := by positivity
    cas using hne
  obtain ⟨α, hα, hαH, R, hmaximum⟩ := hlocalize r hr
  let K : Set (E × ℝ) := closedTimeSlab S ∩ Metric.closedBall 0 R
  have hKslab {z : (E × ℝ)} (hz : z ∈ K) : z ∈ closedTimeSlab T := ⟨hz.1.1, hz.1.2.trans hST.le⟩
  have hden {z : (E × ℝ)} (hz : z ∈ K) : 0 < T - z.2 := sub_pos.mpr (hz.1.2.trans_lt hST)
  let δ := c / (8 * ((Cx : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδscale : ((Cx : ℝ) + 1) * δ = c / 8 := by
    dsimp only [δ]
    have hne : (Cx : ℝ) + 1 ≠ 0 := by positivity
    cas using hne
  obtain ⟨ε₁, hε₁, hpenalty_small⟩ := exists_small_separation_penalty (K := K) (u := u) (v := v)
    (hubT.2.mono (fun _ hz ↦ hKslab hz)) (hvbT.2.mono (fun _ hz ↦ hKslab hz)) hM hδ
  obtain ⟨ε, hε, hεsmall⟩ := exists_between
    (show (0 : ℝ) < min ε₀ (min ε₁ (δ ^ 2 / (2 * M))) by positivity)
  have hεlt : ε < ε₀ := hεsmall.trans_le (min_le_left _ _)
  have hεrest := hεsmall.trans_le (min_le_right _ _)
  have hεpenalty : ε < ε₁ := hεrest.trans_le (min_le_left _ _)
  have hεdistance : ε < δ ^ 2 / (2 * M) := hεrest.trans_le (min_le_right _ _)
  obtain ⟨z, hzK, w, hwK, ⟨hzpos, hwpos⟩, hbds, hmax, hlocal, htime_lower⟩ := hmaximum ε ⟨hε, hεlt⟩
  have hcontact := hu.doubling_barrier_le_of_lipschitz hv hp hx
    (hU ⟨hzpos, (hzK.1.2.trans_lt hST).trans hTT₀⟩) (hV ⟨hwpos, (hwK.1.2.trans_lt hST).trans hTT₀⟩)
    hε (hden hzK).ne' (hden hwK).ne' (hlocal.isLocalMaxOn _)
  have htime_nonneg : 0 ≤ 2 * α * (z.2 + w.2) := by positivity
  have htime_other : 0 ≤ a / (T - w.2) ^ 2 := by positivity
  have hmomentum_error := localization_momentum_error_lt hα hM hr hαH hbds.2.1 hbds.2.2 hrscale
  have hsmall_penalty := hpenalty_small ε ⟨hε, hεpenalty⟩ α a T z hzK w hwK hbds.1 hmax
  have hspatial_error := separation_spatial_error_lt
    hε hM hδ hεdistance hbds.1 hsmall_penalty hδscale
  linarith only [hcontact, htime_lower, htime_nonneg, htime_other,
    hmomentum_error, hspatial_error, hc]

/-- Evans's comparison on a prescribed finite closed slab. Uniform momentum Lipschitz
control and the spatial bound growing linearly in momentum suffice. The candidates
are bounded and uniformly continuous only on this slab and solve the PDE in its interior. -/
theorem IsSpatialViscositySubsolution.le_of_initial_le_on_slab_of_lipschitz {H : E → E → ℝ}
    {u v : E × ℝ → ℝ} {Cp Cx : NNReal} {U V : Set (E × ℝ)} {T : ℝ}
    (hu : IsSpatialViscositySubsolution H U u) (hv : IsSpatialViscositySupersolution H V v)
    (hU : openTimeSlab T ⊆ U) (hV : openTimeSlab T ⊆ V) (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (hinit : ∀ x, u (x, 0) ≤ v (x, 0)) (hT : 0 < T) {z : E × ℝ} (hz : z ∈ closedTimeSlab T) :
    u z ≤ v z := by
  apply le_on_closedTimeSlab hT hub.2.continuousOn hvb.2.continuousOn ?_ z hz
  exact fun _ hw ↦ le_of_initial_le_of_lipschitz_of_lt_horizon
    hu hv hU hV hp hx hub hvb hinit hw.1.le hw.2

/-- The finite-horizon uniqueness theorem under Evans's momentum and spatial bounds.
There is no equation or regularity hypothesis at times beyond the supplied horizon. -/
theorem IsSpatialViscositySolution.eqOn_closedTimeSlab_of_lipschitz {H : E → E → ℝ}
    {u v : E × ℝ → ℝ} {Cp Cx : NNReal} {T : ℝ}
    (hu : IsSpatialViscositySolution H (openTimeSlab T) u)
    (hv : IsSpatialViscositySolution H (openTimeSlab T) v)
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (hinit : ∀ x, u (x, 0) = v (x, 0)) (hT : 0 < T) :
    EqOn u v (closedTimeSlab T) := by
  intro z hz
  exact le_antisymm
    (hu.1.le_of_initial_le_on_slab_of_lipschitz hv.2 Subset.rfl Subset.rfl hp hx hub hvb
      (fun x ↦ (hinit x).le) hT hz)
    (hv.1.le_of_initial_le_on_slab_of_lipschitz hu.2 Subset.rfl Subset.rfl hp hx hvb hub
      (fun x ↦ (hinit x).ge) hT hz)

end

end HamiltonJacobi

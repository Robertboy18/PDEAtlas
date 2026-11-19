/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Continuation
public import PDE.Analysis.Evolution.Semigroup.Semilinear.Lifespan

/-!
# Maximal forward semilinear mild solutions

Compatible finite prefixes define a continuous mild solution before the
maximal lifetime. `exists_maximal_mildSolution_of_locallyLipschitz` constructs
this trajectory with its initial value and variation-of-constants equation.
A finite maximal endpoint cannot belong to another finite-interval solution;
an infinite lifetime gives a solution at every nonnegative time.

The norm blowup alternative additionally assumes that the nonlinearity is
Lipschitz on each norm ball. Its constant may depend on the radius. Local
Lipschitz continuity alone does not supply these bounds in infinite dimensions.
Bounds for finite solutions on each finite time horizon imply an infinite
lifespan; the bound may grow with the horizon. The maximal trajectory then
gives a global solution through `maximalMildSolution_global_of_lifespan_eq_top`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The maximal forward trajectory, chosen from its compatible finite prefixes.
Its values outside the nonnegative preterminal interval are set to `x₀`. -/
def maximalMildSolution (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E) (t : ℝ) : E :=
  if ht : 0 ≤ t ∧ ENNReal.ofReal t < T.mildLifespan F x₀ then
    IccExtend t.toNNReal.coe_nonneg
      ((T.lt_mildLifespan_iff hF x₀ (τ := t.toNNReal)).mp ht.2).choose t
  else x₀

/-- Every finite mild solution is a restriction of the maximal trajectory.
In particular, the construction does not depend on choices of local solutions. -/
theorem maximalMildSolution_eqOn {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} (hF : LocallyLipschitz F) {x₀ : E} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)} (hu : T.IsMildSolutionOn F x₀ τ u) :
    EqOn (T.maximalMildSolution hF x₀) (IccExtend τ.coe_nonneg u)
      (Icc (0 : ℝ) (τ : ℝ)) := by
  intro t ht
  have hτ := (T.lt_mildLifespan_iff hF x₀).mpr ⟨u, hu⟩
  have hητ : t.toNNReal ≤ τ := Real.toNNReal_le_iff_le_coe.mpr ht.2
  have hη : ENNReal.ofReal t < T.mildLifespan F x₀ :=
    (ENNReal.coe_le_coe.mpr hητ).trans_lt hτ
  rw [maximalMildSolution, dite_eq_left ⟨ht.1, hη⟩]
  apply (((T.lt_mildLifespan_iff hF x₀ (τ := t.toNNReal)).mp hη).choose_spec).eqOn_overlap
    hF hu
  exact ⟨ht.1, le_min (Real.coe_toNNReal t ht.1).symm.le ht.2⟩

/-- The maximal trajectory has the prescribed initial state. -/
theorem maximalMildSolution_zero (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E) :
    T.maximalMildSolution hF x₀ 0 = x₀ := by
  obtain ⟨τ, _, u, hu, _⟩ :=
    T.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted hF x₀
  rw [maximalMildSolution_eqOn hF hu ⟨le_rfl, τ.coe_nonneg⟩,
    IccExtend_of_mem τ.coe_nonneg u ⟨le_rfl, τ.coe_nonneg⟩]
  exact hu.initial_value

/-- Every compact initial interval strictly below the lifetime carries the
continuous mild curve determined by the maximal trajectory. -/
theorem exists_mildSolutionOn_eqOn_maximalMildSolution
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F) (x₀ : E) {τ : NNReal}
    (hτ : (τ : ℝ≥0∞) < T.mildLifespan F x₀) :
    ∃ u : C(Icc (0 : ℝ) (τ : ℝ), E),
      T.IsMildSolutionOn F x₀ τ u ∧
        EqOn (IccExtend τ.coe_nonneg u) (T.maximalMildSolution hF x₀)
          (Icc (0 : ℝ) (τ : ℝ)) := by
  obtain ⟨u, hu⟩ := (T.lt_mildLifespan_iff hF x₀).mp hτ
  exact ⟨u, hu, (maximalMildSolution_eqOn hF hu).symm⟩

/-- Continuity holds at every preterminal time, including right-continuity at zero.
Each point has a neighborhood on which the trajectory equals one longer mild curve. -/
theorem continuousOn_maximalMildSolution (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E) :
    ContinuousOn (T.maximalMildSolution hF x₀)
      {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < T.mildLifespan F x₀} := by
  intro t ht
  obtain ⟨τ, htτ, u, hu⟩ :=
    (T.lt_mildLifespan_iff_exists_longer F x₀ (τ := t.toNNReal)).mp ht.2
  have htτ' : t < (τ : ℝ) := (Real.toNNReal_lt_iff_lt_coe ht.1).mp htτ
  have heq := maximalMildSolution_eqOn hF hu
  have hc : Continuous (IccExtend τ.coe_nonneg u) := u.continuous.Icc_extend'
  apply hc.continuousWithinAt.congr_of_eventuallyEq _ (heq ⟨ht.1, htτ'.le⟩)
  have hsmall : ∀ᶠ s in
      𝓝[{r : ℝ | 0 ≤ r ∧ ENNReal.ofReal r < T.mildLifespan F x₀}] t,
      s < (τ : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds htτ')
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hsτ
  exact heq ⟨hs.1, hsτ.le⟩

/-- The maximal trajectory satisfies the variation-of-constants equation at every
nonnegative time strictly before its lifetime. -/
theorem maximalMildSolution_equation (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E) {t : ℝ}
    (ht : 0 ≤ t) (hlt : ENNReal.ofReal t < T.mildLifespan F x₀) :
    T.maximalMildSolution hF x₀ t =
      T t.toNNReal x₀ + T.duhamel (fun s ↦ F (T.maximalMildSolution hF x₀ s)) t := by
  obtain ⟨u, hu⟩ := (T.lt_mildLifespan_iff hF x₀ (τ := t.toNNReal)).mp hlt
  have htmem : t ∈ Icc (0 : ℝ) (t.toNNReal : ℝ) :=
    ⟨ht, (Real.coe_toNNReal t ht).symm.le⟩
  have heq := maximalMildSolution_eqOn hF hu
  rw [heq htmem, IccExtend_of_mem t.toNNReal.coe_nonneg u htmem, hu ⟨t, htmem⟩]
  congr 1
  apply T.duhamel_congr ht
  intro s hs
  exact congrArg F (heq ⟨hs.1, hs.2.trans htmem.2⟩).symm

/-- A finite maximal lifetime gives a preterminal mild solution
(`IsMildSolutionBefore`). -/
theorem isMildSolutionBefore_maximalMildSolution (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E)
    (hb : T.mildLifespan F x₀ ≠ ∞) :
    T.IsMildSolutionBefore F x₀ (T.mildLifespan F x₀).toReal
      (T.maximalMildSolution hF x₀) := by
  refine ⟨(T.continuousOn_maximalMildSolution hF x₀).mono ?_, ?_⟩
  · intro t ht
    exact ⟨ht.1, (ENNReal.ofReal_lt_iff_lt_toReal ht.1 hb).mpr ht.2⟩
  · intro t ht
    exact T.maximalMildSolution_equation hF x₀ ht.1
      ((ENNReal.ofReal_lt_iff_lt_toReal ht.1 hb).mpr ht.2)

/-- No finite-interval mild solution can include a finite maximal endpoint.
Otherwise local existence at its terminal state would increase the supremum. -/
theorem not_exists_mildSolutionOn_at_or_after_lifespan
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F) (x₀ : E) (hb : T.mildLifespan F x₀ ≠ ∞) :
    ¬ ∃ τ : NNReal, (T.mildLifespan F x₀).toReal ≤ (τ : ℝ) ∧
      ∃ u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  rintro ⟨τ, hτ, u, hu⟩
  have hlt := (T.lt_mildLifespan_iff hF x₀).mpr ⟨u, hu⟩
  have hlt' : (τ : ℝ) < (T.mildLifespan F x₀).toReal :=
    (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hb).mpr hlt
  exact (not_lt_of_ge hτ) hlt'

/-- Infinite maximal lifetime gives a continuous forward solution with the mild
equation at every nonnegative time. -/
theorem maximalMildSolution_global_of_lifespan_eq_top
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F) (x₀ : E) (hb : T.mildLifespan F x₀ = ∞) :
    ContinuousOn (T.maximalMildSolution hF x₀) (Ici 0) ∧
      ∀ t ∈ Ici (0 : ℝ), T.maximalMildSolution hF x₀ t =
        T t.toNNReal x₀ +
          T.duhamel (fun s ↦ F (T.maximalMildSolution hF x₀ s)) t := by
  constructor
  · apply (T.continuousOn_maximalMildSolution hF x₀).mono
    intro t ht
    exact ⟨ht, by rw [hb]; exact ENNReal.ofReal_lt_top⟩
  · intro t ht
    exact T.maximalMildSolution_equation hF x₀ ht (by rw [hb]; exact ENNReal.ofReal_lt_top)

/-- A maximal forward mild solution exists for every initial state. Its lifetime
is positive, may be infinite, and includes exactly the attainable compact prefixes. -/
theorem exists_maximal_mildSolution_of_locallyLipschitz
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F) (x₀ : E) :
    ∃ b : ℝ≥0∞, 0 < b ∧ ∃ u : ℝ → E,
      u 0 = x₀ ∧ ContinuousOn u {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < b} ∧
      (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < b →
        u t = T t.toNNReal x₀ + T.duhamel (fun s ↦ F (u s)) t) ∧
      (∀ τ : NNReal, (τ : ℝ≥0∞) < b ↔
        ∃ v : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ v) := by
  exact ⟨T.mildLifespan F x₀, T.mildLifespan_pos hF x₀,
    T.maximalMildSolution hF x₀, T.maximalMildSolution_zero hF x₀,
    T.continuousOn_maximalMildSolution hF x₀,
    fun _ ht hlt ↦ T.maximalMildSolution_equation hF x₀ ht hlt,
    fun _ ↦ T.lt_mildLifespan_iff hF x₀⟩

/-- Under Lipschitz bounds on norm balls, a finite maximal lifetime forces the
state norm to exceed every threshold throughout a sufficiently short terminal
interval. Local Lipschitz continuity alone is not used to infer these bounds. -/
theorem maximalMildSolution_norm_eventually_gt_of_lifespan_ne_top
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    (x₀ : E) (hb : T.mildLifespan F x₀ ≠ ∞) :
    ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ico 0 (T.mildLifespan F x₀).toReal,
        (T.mildLifespan F x₀).toReal - t < ε →
          R < ‖T.maximalMildSolution
            (locallyLipschitz_of_lipschitzOn_closedBall_zero hF) x₀ t‖ := by
  let hlocal := locallyLipschitz_of_lipschitzOn_closedBall_zero hF
  have hmax := T.isMildSolutionBefore_maximalMildSolution hlocal x₀ hb
  apply hmax.norm_eventually_gt_of_not_exists_extension hF
  rintro ⟨τ, hτ, u, hu, _⟩
  exact T.not_exists_mildSolutionOn_at_or_after_lifespan hlocal x₀ hb
    ⟨τ, hτ.le, u, hu⟩

/-- A maximal mild trajectory bounded throughout its forward lifetime is global
when the source has a Lipschitz bound on every norm ball. -/
theorem mildLifespan_eq_top_of_bounded
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F)
    (hballs : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    (x₀ : E) {R : ℝ}
    (hbounded : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < T.mildLifespan F x₀ →
      ‖T.maximalMildSolution hF x₀ t‖ ≤ R) :
    T.mildLifespan F x₀ = ∞ := by
  by_contra hfinite
  have hb : 0 < (T.mildLifespan F x₀).toReal :=
    ENNReal.toReal_pos (ne_of_gt (T.mildLifespan_pos hF x₀)) hfinite
  obtain ⟨ε, hε, hlarge⟩ :=
    T.maximalMildSolution_norm_eventually_gt_of_lifespan_ne_top hballs x₀ hfinite R
  obtain ⟨t, htlow, hthigh⟩ :=
    exists_between (max_lt hb (sub_lt_self _ hε))
  have ht : 0 ≤ t := (lt_of_le_of_lt (le_max_left _ _) htlow).le
  have hgap : (T.mildLifespan F x₀).toReal - t < ε := by
    have hlow := lt_of_le_of_lt (le_max_right 0 _) htlow
    linarith
  exact (not_lt_of_ge (hbounded t ht
    ((ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mpr hthigh)))
      (hlarge t ⟨ht, hthigh⟩ hgap)

/-- A priori bounds for finite solutions imply global existence. For each positive
time horizon, one bound must control the terminal states of all solutions ending
before that horizon. The bound may depend on the horizon and the fixed initial
state; it need not remain bounded as the horizon tends to infinity.

Only finite solutions occur in the hypothesis. Local existence constructs their
maximal trajectory, and a bound at a hypothetical finite lifetime contradicts the
norm blowup alternative. -/
theorem mildLifespan_eq_top_of_finite_time_bounds
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    (x₀ : E)
    (hbound : ∀ H : ℝ, 0 < H → ∃ R : ℝ,
      ∀ τ : NNReal, (τ : ℝ) ≤ H →
        ∀ u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u →
          ‖u ⟨τ, τ.coe_nonneg, le_rfl⟩‖ ≤ R) :
    T.mildLifespan F x₀ = ∞ := by
  let hlocal := locallyLipschitz_of_lipschitzOn_closedBall_zero hF
  by_contra hfinite
  have hb : 0 < (T.mildLifespan F x₀).toReal :=
    ENNReal.toReal_pos (ne_of_gt (T.mildLifespan_pos hlocal x₀)) hfinite
  obtain ⟨R, hR⟩ := hbound (T.mildLifespan F x₀).toReal hb
  apply hfinite
  apply T.mildLifespan_eq_top_of_bounded hlocal hF x₀ (R := R)
  intro t ht hlt
  obtain ⟨u, hu⟩ := (T.lt_mildLifespan_iff hlocal x₀ (τ := t.toNNReal)).mp hlt
  have htmem : t ∈ Icc (0 : ℝ) (t.toNNReal : ℝ) :=
    ⟨ht, (Real.coe_toNNReal t ht).symm.le⟩
  rw [maximalMildSolution_eqOn hlocal hu htmem,
    IccExtend_of_mem t.toNNReal.coe_nonneg u htmem]
  have htH : (t.toNNReal : ℝ) ≤ (T.mildLifespan F x₀).toReal := by
    rw [Real.coe_toNNReal t ht]
    exact ((ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp hlt).le
  simpa only [Real.coe_toNNReal t ht] using hR t.toNNReal htH u hu

end PDE.Analysis.Evolution.StronglyContinuousSemigroup

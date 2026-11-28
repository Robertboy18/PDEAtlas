/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Rearrangement.Polarization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A radial limit of iterated polarizations

A nonnegative Lipschitz function with compact support on `ℝⁿ` becomes radial and nonincreasing
in `|x|` in a limit of polarizations. Every quantity that polarization preserves, or does not
increase, then passes to a radial function. This is the symmetrization step of Talenti's proof of
the sharp Sobolev inequality. No explicit sequence of hyperplanes is given: the limit comes from
compactness. `PDE.Analysis.Rearrangement.PolyaSzego` passes integrals of the values and the
difference energies to the limit, and `PDE.Analysis.Rearrangement.SymmDecr` identifies it with the
symmetric decreasing rearrangement.

## Main results

* `lipClass L R M`: the `L`-Lipschitz functions with values in `[0, M]` that vanish outside the
  closed ball of radius `R`. On every normed group the class is compact for pointwise convergence
  (`isCompact_lipClass`), and on a proper one pointwise neighbourhoods are uniformly small on it
  (`exists_nhds_forall_abs_sub_le`).
* `Polarized u w`: `w` is obtained from `u` by finitely many polarizations.
* `exists_seq_polarized`, `exists_seq_polarized_tendsto`: on a proper real inner product space,
  every pointwise limit of iterated polarizations of a function of the class is a uniform, hence
  pointwise, limit of a sequence of iterated polarizations.
* `exists_radial_antitone`: on a finite-dimensional real inner product space, the closure of the
  iterated polarizations of a function of the class contains a function `v` with `v y ≤ v x`
  whenever `|x| ≤ |y|`.

## How it works

Polarization keeps the three properties that define `lipClass L R M` (`LipschitzWith.polarize`,
`polarize_eq_zero_of_lt`), so all iterated polarizations of `u` lie in the class. For pointwise
convergence the class is closed in the product of the intervals `[0, M]`, hence compact by
Tychonoff's theorem. On it pointwise convergence is uniform convergence, because the functions are
equi-Lipschitz and live on one compact ball.

So the closure of the iterated polarizations of `u` is compact, and the second moment
`∫ w(x) |x|² dx` is continuous on it (`continuousOn_secondMoment`). Take a point `v` of the
closure where the second moment is smallest. Polarizing `v` gives another point of the closure,
with a second moment that is not larger, hence equal. By the rigidity of the second moment
(`le_of_secondMoment_le_secondMoment_polarize`), `v (σ x) ≤ v x` whenever `x` is closer to the
origin than its mirror image `σ x`. Every pair of points with `|x| < |y|` is swapped by such a
reflection (`exists_mirror_eq`), so `v y ≤ v x`, and by continuity the same holds when
`|x| = |y|`.

## References

* F. Brock and A. Yu. Solynin, "An approach to symmetrization via polarization",
  *Trans. Amer. Math. Soc.* 352 (2000), 1759-1796: the rearrangement as a limit of iterated
  polarizations. <https://doi.org/10.1090/S0002-9947-99-02558-1>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal NNReal Topology

namespace PDE.Analysis.Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : ℝ≥0} {R M : ℝ}
  {u v w : E → ℝ}

/-! ## The class of functions -/

/-- The functions on `E` that are `L`-Lipschitz, take values in `[0, M]` and vanish outside the
closed ball of radius `R`. -/
def lipClass (L : ℝ≥0) (R M : ℝ) : Set (E → ℝ) :=
  {w | LipschitzWith L w ∧ (∀ x, w x ∈ Icc 0 M) ∧ ∀ x, R < ‖x‖ → w x = 0}

omit [InnerProductSpace ℝ E] in
/-- The class is closed for pointwise convergence. -/
theorem isClosed_lipClass (L : ℝ≥0) (R M : ℝ) : IsClosed (lipClass (E := E) L R M) := by
  have h1 : IsClosed {w : E → ℝ | LipschitzWith L w} := isClosed_setOfPred_lipschitzWith L
  have h2 : IsClosed {w : E → ℝ | ∀ x, w x ∈ Icc 0 M} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_Icc.preimage (continuous_apply x)
  have h3 : IsClosed {w : E → ℝ | ∀ x, R < ‖x‖ → w x = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply x) continuous_const
  exact h1.inter (h2.inter h3)

omit [InnerProductSpace ℝ E] in
/-- The class is compact for pointwise convergence, by Tychonoff's theorem. -/
theorem isCompact_lipClass (L : ℝ≥0) (R M : ℝ) : IsCompact (lipClass (E := E) L R M) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset (isClosed_lipClass L R M)
    fun _ hw x _ ↦ hw.2.1 x

/-- Polarization maps the class to itself. -/
theorem polarize_mem_lipClass (a : E) (hw : w ∈ lipClass L R M) :
    polarize a w ∈ lipClass L R M :=
  ⟨hw.1.polarize a, polarize_mem hw.2.1 a,
    fun _ hx ↦ polarize_eq_zero_of_lt (fun x ↦ (hw.2.1 x).1) hw.2.2 a hx⟩

omit [InnerProductSpace ℝ E] in
/-- The functions of the class have compact support in a proper space. -/
theorem hasCompactSupport_of_mem_lipClass [ProperSpace E] (hw : w ∈ lipClass L R M) :
    HasCompactSupport w :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx ↦
    hw.2.2 x (by simpa using hx)

omit [InnerProductSpace ℝ E] in
/-- **Pointwise convergence is uniform on the class.** Every function of the class has a
neighbourhood, for pointwise convergence, whose members in the class are uniformly within `ε`
of it. -/
theorem exists_nhds_forall_abs_sub_le [ProperSpace E] {w₀ : E → ℝ} (hw₀ : w₀ ∈ lipClass L R M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 w₀, ∀ w ∈ U, w ∈ lipClass L R M → ∀ x, |w x - w₀ x| ≤ ε := by
  set δ : ℝ := ε / (3 * (L + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hLδ : (L : ℝ) * δ ≤ ε / 3 := by
    have e : (L : ℝ) * δ = ε / 3 * (L / (L + 1)) := by
      rw [hδ]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  obtain ⟨F, -, hFfin, hF⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : E) R) hδ0
  refine ⟨⋂ y ∈ F, {w | |w y - w₀ y| < ε / 3}, ?_, fun w hwU hw x ↦ ?_⟩
  · refine (hFfin.isOpen_biInter fun y _ ↦ ?_).mem_nhds ?_
    · exact isOpen_lt ((continuous_apply y).sub continuous_const).abs continuous_const
    · simp only [mem_iInter, mem_ofPred_eq, sub_self, abs_zero]
      exact fun _ _ ↦ by positivity
  · by_cases hx : R < ‖x‖
    · rw [hw.2.2 x hx, hw₀.2.2 x hx, sub_self, abs_zero]
      exact hε.le
    · have hxB : x ∈ closedBall (0 : E) R := by simpa using not_lt.mp hx
      obtain ⟨y, hyF, hxy⟩ := mem_iUnion₂.mp (hF hxB)
      have hd : (L : ℝ) * dist x y ≤ ε / 3 :=
        (mul_le_mul_of_nonneg_left (le_of_lt hxy) L.coe_nonneg).trans hLδ
      have h1 := (hw.1.dist_le_mul x y).trans hd
      have h2 := (hw₀.1.dist_le_mul x y).trans hd
      have h3 : |w y - w₀ y| < ε / 3 := by
        simp only [mem_iInter, mem_ofPred_eq] at hwU
        exact hwU y hyF
      rw [Real.dist_eq] at h1 h2
      calc |w x - w₀ x| ≤ |w x - w y| + |w y - w₀ x| := abs_sub_le _ _ _
        _ ≤ |w x - w y| + (|w y - w₀ y| + |w₀ y - w₀ x|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ ≤ ε / 3 + (ε / 3 + ε / 3) := by
          rw [abs_sub_comm (w₀ y)]
          gcongr
        _ = ε := by ring

/-! ## Iterated polarizations -/

/-- `Polarized u w`: the function `w` is obtained from `u` by finitely many polarizations. -/
inductive Polarized (u : E → ℝ) : (E → ℝ) → Prop
  /-- No polarization: `u` itself. -/
  | refl : Polarized u u
  /-- One more polarization, in the perpendicular bisector of `0` and `a`. -/
  | step {w : E → ℝ} (a : E) : Polarized u w → Polarized u (polarize a w)

/-- The iterated polarizations of a function of the class are in the class. -/
theorem Polarized.mem_lipClass (hu : u ∈ lipClass L R M) (h : Polarized u w) :
    w ∈ lipClass L R M := by
  induction h with
  | refl => exact hu
  | step a _ ih => exact polarize_mem_lipClass a ih

/-- The pointwise limits of iterated polarizations of a function of the class are in the
class. -/
theorem mem_lipClass_of_mem_closure (hu : u ∈ lipClass L R M)
    (hv : v ∈ closure {w | Polarized u w}) : v ∈ lipClass L R M :=
  closure_minimal (fun _ hw ↦ Polarized.mem_lipClass hu hw) (isClosed_lipClass L R M) hv

/-- The polarization of a pointwise limit of iterated polarizations is again one. -/
theorem polarize_mem_closure (a : E) (hv : v ∈ closure {w | Polarized u w}) :
    polarize a v ∈ closure {w | Polarized u w} := by
  have hS : polarize a '' {w | Polarized u w} ⊆ {w | Polarized u w} := by
    rintro _ ⟨w, hw, rfl⟩
    exact Polarized.step a hw
  exact closure_mono hS
    (image_closure_subset_closure_image (continuous_polarize a) ⟨v, hv, rfl⟩)

/-- **Uniform approximation.** A pointwise limit of iterated polarizations of a function of
the class is the uniform limit of a sequence of iterated polarizations. -/
theorem exists_seq_polarized [ProperSpace E] (hu : u ∈ lipClass L R M)
    (hv : v ∈ closure {w | Polarized u w}) :
    ∃ w : ℕ → E → ℝ, (∀ k, Polarized u (w k)) ∧ ∀ k x, |w k x - v x| ≤ 1 / (k + 1) := by
  have hvK := mem_lipClass_of_mem_closure hu hv
  have key (k : ℕ) : ∃ w, Polarized u w ∧ ∀ x, |w x - v x| ≤ 1 / (k + 1) := by
    obtain ⟨U, hU, hUv⟩ := exists_nhds_forall_abs_sub_le hvK (ε := 1 / (k + 1)) (by positivity)
    obtain ⟨w, hwU, hw⟩ := mem_closure_iff_nhds.mp hv U hU
    exact ⟨w, hw, hUv w hwU (hw.mem_lipClass hu)⟩
  choose w hw using key
  exact ⟨w, fun k ↦ (hw k).1, fun k ↦ (hw k).2⟩

/-- A pointwise limit of iterated polarizations of a function of the class is the pointwise
limit of a sequence of iterated polarizations. -/
theorem exists_seq_polarized_tendsto [ProperSpace E] (hu : u ∈ lipClass L R M)
    (hv : v ∈ closure {w | Polarized u w}) :
    ∃ w : ℕ → E → ℝ, (∀ k, Polarized u (w k)) ∧ ∀ x, Tendsto (fun k ↦ w k x) atTop (𝓝 (v x)) := by
  obtain ⟨w, hw, hwv⟩ := exists_seq_polarized hu hv
  refine ⟨w, hw, fun x ↦ ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [Real.dist_eq]
  exact hwv k x

/-! ## The second moment on the class -/

section Moment

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Two functions of the class that are uniformly within `ε` have second moments within
`ε R² |B_R|`. -/
theorem abs_secondMoment_sub_le {w₀ : E → ℝ} (hw : w ∈ lipClass L R M) (hw₀ : w₀ ∈ lipClass L R M)
    {ε : ℝ} (h : ∀ x, |w x - w₀ x| ≤ ε) :
    |secondMoment w - secondMoment w₀| ≤ ε * R ^ 2 * volume.real (closedBall (0 : E) R) := by
  have hn : Continuous fun x : E ↦ ‖x‖ ^ 2 := continuous_norm.pow 2
  have hi {w : E → ℝ} (hw : w ∈ lipClass L R M) : Integrable fun x ↦ w x * ‖x‖ ^ 2 :=
    (hw.1.continuous.mul hn).integrable_of_hasCompactSupport
      (hasCompactSupport_of_mem_lipClass hw).mul_right
  have hz : ∀ x, x ∉ closedBall (0 : E) R → w x * ‖x‖ ^ 2 - w₀ x * ‖x‖ ^ 2 = 0 := by
    intro x hx
    have hx' : R < ‖x‖ := by simpa using hx
    rw [hw.2.2 x hx', hw₀.2.2 x hx']
    ring
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h 0)
  rw [secondMoment, secondMoment, ← integral_sub (hi hw) (hi hw₀),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← Real.norm_eq_abs]
  refine norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun x hx ↦ ?_
  have hx' : ‖x‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg x) (mem_closedBall_zero_iff.mp hx) 2
  calc ‖w x * ‖x‖ ^ 2 - w₀ x * ‖x‖ ^ 2‖ = |w x - w₀ x| * ‖x‖ ^ 2 := by
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) 2)]
    _ ≤ ε * R ^ 2 := mul_le_mul (h x) hx' (pow_nonneg (norm_nonneg x) 2) hε

/-- The second moment is continuous on the class, for pointwise convergence. -/
theorem continuousOn_secondMoment (L : ℝ≥0) (R M : ℝ) :
    ContinuousOn (secondMoment : (E → ℝ) → ℝ) (lipClass L R M) := by
  intro w₀ hw₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hB := measureReal_nonneg (μ := (volume : Measure E)) (s := closedBall (0 : E) R)
  set C : ℝ := R ^ 2 * volume.real (closedBall (0 : E) R) + 1 with hC
  have hC0 : 0 < C := by positivity
  obtain ⟨U, hU, hUw⟩ := exists_nhds_forall_abs_sub_le hw₀ (div_pos hε hC0)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with w hwU hwK
  rw [Real.dist_eq]
  calc |secondMoment w - secondMoment w₀| ≤ ε / C * R ^ 2 * volume.real (closedBall (0 : E) R) :=
        abs_secondMoment_sub_le hwK hw₀ (hUw w hwU hwK)
    _ = ε * (R ^ 2 * volume.real (closedBall (0 : E) R) / C) := by ring
    _ < ε * 1 := by
        gcongr
        rw [div_lt_one hC0]
        linarith
    _ = ε := mul_one ε

/-! ## The radial limit -/

/-- **A radial nonincreasing limit of iterated polarizations.** Let `u` be `L`-Lipschitz on a
finite-dimensional real inner product space, with values in `[0, M]`, and zero outside the
closed ball of radius `R`. Then some pointwise limit `v` of iterated polarizations of `u`
satisfies `v y ≤ v x` whenever `|x| ≤ |y|`. It is a point of the closure where the second
moment is smallest. -/
theorem exists_radial_antitone (hu : u ∈ lipClass L R M) :
    ∃ v ∈ closure {w | Polarized u w}, ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x := by
  have hsub : closure {w | Polarized u w} ⊆ lipClass L R M :=
    fun _ hv ↦ mem_lipClass_of_mem_closure hu hv
  obtain ⟨v, hv, hmin⟩ := ((isCompact_lipClass L R M).of_isClosed_subset isClosed_closure
    hsub).exists_isMinOn ⟨u, subset_closure Polarized.refl⟩
    ((continuousOn_secondMoment L R M).mono hsub)
  have hvK := hsub hv
  have hvc : Continuous v := hvK.1.continuous
  -- `v` is polarized with respect to every hyperplane
  have hpol (a x : E) (hx : ‖x‖ < ‖mirror a x‖) : v (mirror a x) ≤ v x :=
    le_of_secondMoment_le_secondMoment_polarize hvc (hasCompactSupport_of_mem_lipClass hvK)
      (hmin (polarize_mem_closure a hv)) hx
  have hlt (x y : E) (h : ‖x‖ < ‖y‖) : v y ≤ v x := by
    obtain ⟨a, rfl⟩ := exists_mirror_eq h.ne
    exact hpol a x h
  refine ⟨v, hv, fun x y hxy ↦ ?_⟩
  rcases hxy.eq_or_lt with heq | h
  · rcases eq_or_ne y 0 with rfl | hy
    · rw [norm_zero, norm_eq_zero] at heq
      rw [heq]
    -- push `y` slightly outwards and pass to the limit
    have hc : Tendsto (fun s : ℝ ↦ v ((1 + s) • y)) (𝓝[>] 0) (𝓝 (v y)) := by
      have hcont : Continuous fun s : ℝ ↦ v ((1 + s) • y) :=
        hvc.comp ((continuous_const.add continuous_id).smul continuous_const)
      have h0 := hcont.tendsto 0
      simp only [add_zero, one_smul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hc (eventually_nhdsWithin_of_forall fun s hs ↦ hlt _ _ ?_)
    have hs0 : (0 : ℝ) < s := hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), heq]
    have := norm_pos_iff.mpr hy
    nlinarith
  · exact hlt x y h

end Moment

end PDE.Analysis.Rearrangement

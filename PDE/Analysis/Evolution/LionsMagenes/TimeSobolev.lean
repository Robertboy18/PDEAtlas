/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.MeasureTheory.Integral.IntervalAverage
import PDE.Analysis.Evolution.LionsMagenes.Basic.Continuity
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# One-dimensional time Sobolev bounds

For a finite interval, the Lions–Magenes theorem upgrades a Gelfand weak
trajectory

`u ∈ L²(a,b;V)`, `uₜ ∈ L²(a,b;V*)`

to a representative continuous from `[a,b]` into the pivot space `H`.
Compactness of `[a,b]` then gives the vector-valued one-dimensional Sobolev
consequence `u ∈ L∞(a,b;H)`.

We give an explicit pivot bound in terms of the `L²` norms of the
trajectory and its weak derivative, the abstract form of Evans §5.9.2,
Theorem 3(iii), estimate (10). The theorem is stated for ordinary Bochner
trajectories and Gelfand triples; no PDE-specific forcing bound is assumed.
For the identity Gelfand triple, this
specializes to the familiar Hilbert-valued one-dimensional Sobolev bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3(iii), estimate (10), and §7.1.3, proof of
  Theorem 5, step 4. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

open scoped ENNReal

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]

/--
A finite-interval Gelfand weak trajectory is essentially bounded in the
pivot norm.

The proof first obtains the canonical closed-interval Lions–Magenes
representative.  Its norm is continuous on the compact interval, hence
bounded.  The almost-everywhere identification with the original Bochner
trajectory transfers that pointwise bound back to the `Lp` representative.
-/
theorem HasGelfandWeakTimeDerivativeOn.exists_ae_inclusion_norm_le
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn T u g) (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖T.inclusion (u t)‖ ≤ C := by
  obtain ⟨Eopen⟩ := h.hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn T hab (Lp.memLp u) (Lp.memLp g)
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn E.continuousOn
  have hrep : E.representative =ᵐ[volume.restrict (Ioc a b)] fun t ↦ T.inclusion (u t) := by
    simpa only [uIcc_of_le hab.le, restrict_Ioc_eq_restrict_Icc] using E.ae_eq_inclusion
  refine ⟨C, (norm_nonneg _).trans (hC a left_mem_uIcc), ?_⟩
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioc] with t ht htab
  exact ht ▸ hC t (Icc_subset_uIcc (Ioc_subset_Icc_self htab))

/--
The quantitative time-Sobolev bound associated with a Gelfand triple.

For a trajectory `u` and dual derivative `g` on `(a,b)`, the bound is

`sqrt (‖J‖² ‖u‖² / (b-a) + 2 ‖u‖ ‖g‖)`,

where `J : V → H` is the Gelfand inclusion.
-/
def gelfandTimeSobolevBound
    {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (u : Lp V 2 (volume.restrict (Ioc a b)))
    (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))) : ℝ :=
  √
    (‖T.inclusion‖ ^ 2 * ‖u‖ ^ 2 / (b - a) + 2 * ‖u‖ * ‖g‖)

omit [CompleteSpace V] [CompleteSpace H]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] in
/-- The quantitative Gelfand time-Sobolev bound is nonnegative. -/
theorem gelfandTimeSobolevBound_nonneg
    {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (u : Lp V 2 (volume.restrict (Ioc a b)))
    (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))) :
    0 ≤ gelfandTimeSobolevBound T u g :=
  Real.sqrt_nonneg _

omit [CompleteSpace V] [CompleteSpace H]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] in
/--
Every Lions–Magenes representative satisfies the quantitative Gelfand
time-Sobolev bound on the closed time interval.
-/
theorem ContinuousPivotEvolutionOn.norm_representative_le_gelfandTimeSobolevBound
    {a b : ℝ}
    {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    (hab : a < b) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖E.representative t‖ ≤ gelfandTimeSobolevBound T u g := by
  let μ := volume.restrict (Ioc a b)
  let uH : Lp H 2 μ := T.inclusion.compLpL 2 μ u
  have hvol : volume (uIoc a b) = ENNReal.ofReal (b - a) := by
    rw [uIoc_of_le hab.le, Real.volume_Ioc]
  -- a time `c` where `‖u(c)‖²` equals its interval average
  obtain ⟨c, hc, hcAverage⟩ := exists_eq_interval_average_of_nullSingletonClass
    (f := fun r ↦ ‖E.representative r‖ ^ 2) (E.continuousOn.norm.pow 2)
    (hvol ▸ ENNReal.ofReal_ne_top)
    (hvol ▸ (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne')
  have hcU : c ∈ uIcc a b := uIoo_subset_uIcc_self hc
  have htU : t ∈ uIcc a b := by rwa [uIcc_of_le hab.le]
  have hrep : E.representative =ᵐ[μ] fun t ↦ T.inclusion (u t) := by
    simpa only [μ, uIcc_of_le hab.le, restrict_Ioc_eq_restrict_Icc] using E.ae_eq_inclusion
  have hcNormSq : ‖E.representative c‖ ^ 2 = ‖uH‖ ^ 2 / (b - a) := by
    rw [hcAverage, interval_average_eq_div, intervalIntegral.integral_of_le hab.le,
      Lp.norm_sq_eq_integral_norm_sq]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hrep, T.inclusion.coeFn_compLpL u] with r h₁ h₂
    rw [h₁, h₂]
  have huH : ‖uH‖ ≤ ‖T.inclusion‖ * ‖u‖ :=
    (T.inclusion.compLpL 2 μ).le_of_opNorm_le_of_le (T.inclusion.norm_compLpL_le) le_rfl
  -- Hölder for the pairing `∫ g(u)` on the subinterval between `c` and `t`
  have hprodInt : Integrable (fun r ↦ ‖g r‖ * ‖u r‖) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp g).norm.fun_mul (Lp.memLp u).norm)
  have hholder : (∫ r, ‖g r‖ * ‖u r‖ ∂μ) ≤ ‖g‖ * ‖u‖ := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (by simpa using (Lp.memLp g).norm) (by simpa using (Lp.memLp u).norm)
    simp only [norm_norm, Real.rpow_two, ← Lp.norm_sq_eq_integral_norm_sq] at h
    rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)] at h
  have hsub : uIoc c t ⊆ Ioc a b :=
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hcU htU)).trans
      (uIoc_of_le hab.le).le
  have hpairBound : ‖∫ r in c..t, g r (u r)‖ ≤ ‖g‖ * ‖u‖ :=
    calc ‖∫ r in c..t, g r (u r)‖ ≤ ∫ r in uIoc c t, ‖g r (u r)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ r in uIoc c t, ‖g r‖ * ‖u r‖ :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
            (hprodInt.mono_measure (Measure.restrict_mono_set _ hsub))
            (.of_forall fun r ↦ (g r).le_opNorm (u r))
      _ ≤ ∫ r, ‖g r‖ * ‖u r‖ ∂μ :=
          setIntegral_mono_set hprodInt (.of_forall fun r ↦ by positivity) (.of_forall hsub)
      _ ≤ ‖g‖ * ‖u‖ := hholder
  -- the energy identity between `c` and `t`
  have hcBound : ‖E.representative c‖ ^ 2 ≤ ‖T.inclusion‖ ^ 2 * ‖u‖ ^ 2 / (b - a) := by
    rw [hcNormSq, ← mul_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) huH 2)
      (sub_pos.2 hab).le
  exact Real.le_sqrt_of_sq_le (by
    linarith [E.energyIdentity c t hcU htU, Real.le_norm_self (∫ r in c..t, g r (u r))])

omit [CompleteSpace V] [CompleteSpace H]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] in
/--
Uniform `L²` bounds on a Gelfand trajectory and its dual derivative give a
uniform pivot bound for its Lions–Magenes representative.
-/
theorem ContinuousPivotEvolutionOn.norm_representative_le_of_L2_norm_le
    {a b : ℝ}
    {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    (hab : a < b) {M G : ℝ} (hM : 0 ≤ M)
    (hu : ‖u‖ ≤ M) (hg : ‖g‖ ≤ G)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖E.representative t‖ ≤
      √
        (‖T.inclusion‖ ^ 2 * M ^ 2 / (b - a) + 2 * M * G) := by
  refine (E.norm_representative_le_gelfandTimeSobolevBound hab t ht).trans (Real.sqrt_le_sqrt ?_)
  have hfirst : ‖T.inclusion‖ ^ 2 * ‖u‖ ^ 2 / (b - a) ≤ ‖T.inclusion‖ ^ 2 * M ^ 2 / (b - a) :=
    div_le_div_of_nonneg_right (by gcongr) (sub_nonneg.mpr hab.le)
  linarith [mul_le_mul hu hg (norm_nonneg _) hM]

section Identity

variable [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (StrongDual ℝ H)] [BorelSpace (StrongDual ℝ H)]

/--
The explicit one-dimensional Hilbert-valued Sobolev bound used below.

For an interval of length `b - a`, this is

`sqrt (‖u‖² / (b - a) + 2 ‖u‖ ‖du‖)`.

The expression under the square root is nonnegative when `a < b`.
-/
def timeSobolevBound
    {a b : ℝ}
    (u du : Lp H 2 (volume.restrict (Set.Ioc a b))) : ℝ :=
  √(‖u‖ ^ 2 / (b - a) + 2 * ‖u‖ * ‖du‖)

omit [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (StrongDual ℝ H)] [BorelSpace (StrongDual ℝ H)] in
/-- The explicit Hilbert-valued time-Sobolev bound is nonnegative. -/
theorem timeSobolevBound_nonneg
    {a b : ℝ}
    (u du : Lp H 2 (volume.restrict (Set.Ioc a b))) :
    0 ≤ timeSobolevBound u du :=
  Real.sqrt_nonneg _

/--
Quantitative Hilbert-valued one-dimensional `H¹` estimate.

If `u, du ∈ L²(a,b;H)` and `du` is the weak time derivative of `u`, then
the Lions–Magenes representative is continuous on `[a,b]` and satisfies

`‖u(t)‖ ≤ sqrt (‖u‖² / (b-a) + 2 ‖u‖ ‖du‖)`

at every time in the closed interval.  It agrees almost everywhere with
the original Bochner trajectory, so the same explicit estimate holds
almost everywhere for that trajectory.

The constant is the standard non-sharp one-dimensional Sobolev estimate:
choose an interior time where the squared norm equals its interval average,
then apply the exact Hilbert-space energy identity and `L²` Hölder on the
subinterval joining that time to `t`.
-/
theorem HasGelfandWeakTimeDerivativeOn.exists_continuousRepresentative_norm_le_of_identity
    {a b : ℝ}
    {u du : Lp H 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity H) u
      ((GelfandTriple.identity H).energyToDual.compLpL
        2 (volume.restrict (Set.Ioc a b)) du))
    (hab : a < b) :
    ∃ E : ContinuousPivotEvolutionOn
        (GelfandTriple.identity H) (fun t ↦ u t)
        (fun t ↦
          ((GelfandTriple.identity H).energyToDual.compLpL
            2 (volume.restrict (Set.Ioc a b)) du) t)
        a b,
      (∀ t ∈ Set.Icc a b, ‖E.representative t‖ ≤ timeSobolevBound u du) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        ‖u t‖ ≤ timeSobolevBound u du) := by
  let μ := volume.restrict (Set.Ioc a b)
  let g : Lp (StrongDual ℝ H) 2 μ := (GelfandTriple.identity H).energyToDual.compLpL 2 μ du
  obtain ⟨Eopen⟩ := h.hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn (GelfandTriple.identity H) hab
    (Lp.memLp u) (Lp.memLp g)
  have hdual : ‖(GelfandTriple.identity H).energyToDual‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ by
        simpa only [GelfandTriple.energyToDual_apply, GelfandTriple.identity_inclusion_apply,
          one_mul, Real.norm_eq_abs] using abs_real_inner_le_norm v w
  have hg : ‖g‖ ≤ ‖du‖ := ((GelfandTriple.identity H).energyToDual.norm_compLp_le du).trans
    (mul_le_of_le_one_left (norm_nonneg _) hdual)
  have hpoint : ∀ t ∈ Set.Icc a b, ‖E.representative t‖ ≤ timeSobolevBound u du := by
    intro t ht
    refine (E.norm_representative_le_of_L2_norm_le hab (norm_nonneg u) le_rfl hg t ht).trans
      (Real.sqrt_le_sqrt ?_)
    have hfirst : ‖(GelfandTriple.identity H).inclusion‖ ^ 2 * ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _)
        ContinuousLinearMap.norm_id_le)
    linarith [div_le_div_of_nonneg_right hfirst (sub_nonneg.mpr hab.le)]
  refine ⟨E, hpoint, ?_⟩
  have hae : E.representative =ᵐ[μ] fun t ↦ u t := by
    simpa only [μ, uIcc_of_le hab.le, restrict_Ioc_eq_restrict_Icc,
      GelfandTriple.identity_inclusion_apply] using E.ae_eq_inclusion
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t ht htab
  exact ht ▸ hpoint t (Ioc_subset_Icc_self htab)

/--
Hilbert-valued `H¹` time data admit an absolutely continuous representative
with the prescribed strong derivative.

The representative agrees almost everywhere with the original Bochner
trajectory and retains the quantitative one-dimensional Sobolev bound. This
is the representative form needed when an `H¹_t` forcing is differentiated
inside a Galerkin system, as in step 4 of the proof of Evans §7.1.3, Theorem 5.
-/
theorem HasGelfandWeakTimeDerivativeOn.exists_absolutelyContinuousRepresentative_norm_le_of_identity
    {a b : ℝ}
    {u du : Lp H 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity H) u
      ((GelfandTriple.identity H).energyToDual.compLpL
        2 (volume.restrict (Set.Ioc a b)) du))
    (hab : a < b) :
    ∃ representative : ℝ → H,
      AbsolutelyContinuousOnInterval representative a b ∧
      representative =ᵐ[volume.restrict (Set.Ioc a b)]
        (fun t ↦ u t) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt representative (du t) t) ∧
      (∀ t ∈ Set.Icc a b,
        ‖representative t‖ ≤ timeSobolevBound u du) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        ‖u t‖ ≤ timeSobolevBound u du) := by
  let μ := volume.restrict (Set.Ioc a b)
  let T := GelfandTriple.identity H
  let g : Lp (StrongDual ℝ H) 2 μ := T.energyToDual.compLpL 2 μ du
  obtain ⟨E, hpoint, huBound⟩ := h.exists_continuousRepresentative_norm_le_of_identity hab
  have hdu : IntervalIntegrable (fun t ↦ du t) volume a b :=
    intervalIntegrable_coeFn_L2_restrict_Ioc du hab.le
  have hpivot : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      RepresentsPivotDerivative T (g t) (du t) := by
    rw [uIoc_of_le hab.le]
    filter_upwards [T.energyToDual.coeFn_compLpL du] with t ht v
    rw [show g t = T.energyToDual (du t) from ht]
    simp only [T, GelfandTriple.energyToDual_apply, GelfandTriple.identity_inclusion_apply]
  have hAC : AbsolutelyContinuousOnInterval E.representative a b :=
    E.integratedDerivative.absolutelyContinuousOnInterval_of_ae_pivotDerivative _ hdu hpivot
  have hderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt E.representative (du t) t :=
    E.integratedDerivative.ae_hasDerivAt_of_ae_pivotDerivative hab _ hdu hpivot
  have huEq : E.representative =ᵐ[volume.restrict (Set.Ioc a b)] fun t ↦ u t := by
    simpa only [uIcc_of_le hab.le, restrict_Ioc_eq_restrict_Icc,
      GelfandTriple.identity_inclusion_apply] using E.ae_eq_inclusion
  exact ⟨E.representative, hAC, huEq, hderiv, hpoint, huBound⟩

/--
Almost-everywhere form of the quantitative Hilbert-valued time Sobolev
estimate, the form suited to Bochner-space PDE data.
-/
theorem HasGelfandWeakTimeDerivativeOn.ae_norm_le_timeSobolevBound_of_identity
    {a b : ℝ}
    {u du : Lp H 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity H) u
      ((GelfandTriple.identity H).energyToDual.compLpL
        2 (volume.restrict (Set.Ioc a b)) du))
    (hab : a < b) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖u t‖ ≤ timeSobolevBound u du := by
  obtain ⟨E, _hpoint, hae⟩ :=
    h.exists_continuousRepresentative_norm_le_of_identity hab
  exact hae

/--
Hilbert-valued `H¹` time regularity implies an almost-everywhere uniform
bound on the original trajectory.

Here the derivative is represented in the dual through the identity
Gelfand triple.  This is the form used for an `L²_x`-valued forcing
`f ∈ H¹(a,b;L²_x)`.
-/
theorem HasGelfandWeakTimeDerivativeOn.exists_ae_norm_le_of_identity
    {a b : ℝ}
    {u du : Lp H 2 (volume.restrict (Set.Ioc a b))}
    (h : HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity H) u
      ((GelfandTriple.identity H).energyToDual.compLpL
        2 (volume.restrict (Set.Ioc a b)) du))
    (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖u t‖ ≤ C := by
  exact ⟨timeSobolevBound u du, Real.sqrt_nonneg _,
    h.ae_norm_le_timeSobolevBound_of_identity hab⟩

end Identity

end PDE.Analysis.Evolution

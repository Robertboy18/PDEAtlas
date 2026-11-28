/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.List.GetD
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import PDE.Analysis.Calculus.Deriv
public import PDE.Analysis.ENNReal.Basic
public import PDE.Analysis.ODE.DifferentialInequalities
public import PDE.Analysis.Order.MinMax

set_option linter.style.header false

/-!
# Lower Lebesgue integrals

The lemmas compare and split integrals of functions with values in `ℝ≥0∞`, apply Hölder-type bounds,
and relate the lower integral of a norm to a Bochner integral. The proofs use `lintegral_mono`,
`lintegral_add_left`, `ENNReal.lintegral_mul_le_Lp_mul_Lq` and the lemmas of Mathlib on `ofReal`.

## Main results

* `PDE.Analysis.lintegral_Icc_coe_addCircle`: For every `g : AddCircle (1 : ℝ) → ℝ≥0∞`, the lower
  integral of `σ ↦ g ↑σ` over `Icc 0 1` equals the lower integral of `g` over the circle:
  `∫⁻ σ in Icc 0 1, g ↑σ = ∫⁻ t, g t`. No measurability is assumed.
* `PDE.Analysis.lintegral_Ioc_periodic`: For a `1`-periodic `Φ : ℝ → ℝ≥0∞` and every real `c`, the
  lower integral over one period does not depend on the starting point:
  `∫⁻ σ in Ioc c (c + 1), Φ σ = ∫⁻ σ in Icc 0 1, Φ σ`. No measurability of `Φ` is assumed.
* `PDE.Analysis.lintegral_Ioo_eq_lintegral_Ioc_of_periodic`: For `F : ℝ → ℝ≥0∞` periodic with period
  `2 * π`, `∫⁻ θ in Ioo (-π) π, F θ = ∫⁻ θ in Ioc 0 (2 * π), F θ`.
* `PDE.Analysis.exists_bound_of_le_add_lintegral_rpow`: For real `A`, `C`, `K`, `T` there is a bound
  `B` such that, for every `T'` in `Set.Icc 0 T` and all `n w : ℝ → ℝ` continuous and nonnegative on
  `Set.Icc 0 T'` with `∫⁻ s in Set.Icc 0 T', ENNReal.ofReal (w s ^ 4) ≤ ENNReal.ofReal K`, the
  inequality `ENNReal.ofReal (n t) ≤ ENNReal.ofReal A + ENNReal.ofReal C * ∫⁻ s in Set.Ioo 0 t,
  ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (w s) * ENNReal.ofReal (n s)` for all
  `t` in `Set.Icc 0 T'` implies `n t ≤ B` for all `t` in `Set.Icc 0 T'`. Hölder's inequality with
  exponents `4 / 3` and `4` turns the hypothesis into a linear integral inequality for `n ^ 4`, to
  which Gronwall's inequality applies.
* `PDE.Analysis.lintegral_Icc_comp_add_of_periodic`: For `h : ℝ → ℝ≥0∞` of period one and every real
  `τ`, `∫⁻ σ in Icc 0 1, h (σ + τ) = ∫⁻ σ in Icc 0 1, h σ`. Both sides are the integral of `h` over
  the circle `ℝ / ℤ`.
* `PDE.Analysis.lintegral_Ioc_eq_lintegral_Ioc_of_periodic`: For `F : ℝ → ℝ≥0∞` with
  `F (θ + 2 * π) = F θ` for all `θ`, `∫⁻ θ in Ioc 0 (2 * π), F θ = ∫⁻ θ in Ioc (-π) π, F θ`.
* `PDE.Analysis.lintegral_const_mul_add_sum_add`: For a measure `μ` on `ℝ`, a constant `c ≠ ⊤` in
  `ℝ≥0∞`, an almost everywhere measurable `f : ℝ → ℝ≥0∞`, almost everywhere measurable
  `g j : ℝ → ℝ≥0∞` for `j : Fin 3`, and any `t : ℝ → ℝ≥0∞`, `∫⁻ σ, (c * (f σ + ∑ j, g j σ) + t σ) ∂μ
  = c * (∫⁻ σ, f σ ∂μ + ∑ j, ∫⁻ σ, g j σ ∂μ) + ∫⁻ σ, t σ ∂μ`. No measurability of `t` is assumed.
* `PDE.Analysis.lintegral_mul_pow_six_le`: A weighted Hölder inequality with exponents `6 / 5` and
  `6` for lower integrals: for almost everywhere measurable `A B W : X → ℝ≥0∞` with `W x ≠ 0` and
  `W x ≠ ⊤` for all `x`,
  `(∫⁻ x, A x * B x ∂μ) ^ 6 ≤ (∫⁻ x, A x * W x ∂μ) ^ 5 * ∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ`.

There are 40 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology

namespace PDE.Analysis

/-- Every almost everywhere measurable `f : α → ℝ≥0∞` has a measurable majorant with the same lower
integral: there is a measurable `F` with `f x ≤ F x` for all `x` and `∫⁻ x, F x ∂μ = ∫⁻ x, f x ∂μ`.
The proof adds to a measurable representative of `f` the value `⊤` on a measurable null set that
contains the points where the two differ. -/
theorem exists_measurable_ge_lintegral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∃ F : α → ℝ≥0∞, Measurable F ∧ (∀ x, f x ≤ F x) ∧ ∫⁻ x, F x ∂μ = ∫⁻ x, f x ∂μ := by
  set T := toMeasurable μ {x | f x ≠ hf.mk f x} with hTdef
  have hT : μ T = 0 := by
    rw [hTdef, measure_toMeasurable]
    exact ae_iff.1 hf.ae_eq_mk
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  refine ⟨fun x ↦ hf.mk f x + T.indicator (fun _ ↦ ⊤) x,
    hf.measurable_mk.add (measurable_const.indicator hTm), fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ T
    · simp [indicator_of_mem hx]
    · have e : f x = hf.mk f x := by
        by_contra h
        exact hx (subset_toMeasurable _ _ h)
      rw [e]
      exact le_self_add
  · rw [lintegral_add_left hf.measurable_mk, lintegral_indicator hTm,
        setLIntegral_measure_zero _ _ hT, add_zero]
    exact (lintegral_congr_ae hf.ae_eq_mk).symm

/-- For every `g : AddCircle (1 : ℝ) → ℝ≥0∞`, the lower integral of
`σ ↦ g ↑σ` over `Icc 0 1` equals the lower integral of `g` over the circle:
`∫⁻ σ in Icc 0 1, g ↑σ = ∫⁻ t, g t`. No measurability is assumed. -/
theorem lintegral_Icc_coe_addCircle (g : AddCircle (1 : ℝ) → ENNReal) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, g (σ : AddCircle (1 : ℝ)) = ∫⁻ t, g t := by
  have h := AddCircle.lintegral_preimage 1 0 g
  rw [zero_add] at h
  rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- If `k : ℝ → ℝ≥0∞` is periodic with period `2 * π`, then
`∫⁻ φ in Icc 0 (2 * π), k φ = ∫⁻ φ in Ioo (-π) π, k φ`. -/
theorem lintegral_Icc_eq_Ioo_of_periodic {k : ℝ → ℝ≥0∞} (hk : Function.Periodic k (2 * Real.pi)) :
    ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), k φ = ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, k φ := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have h0 := AddCircle.lintegral_preimage (T := 2 * Real.pi) 0 hk.lift
  have h1 := AddCircle.lintegral_preimage (T := 2 * Real.pi) (-Real.pi) hk.lift
  simp only [Function.Periodic.lift_coe] at h0 h1
  rw [zero_add] at h0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, setLIntegral_congr Ioo_ae_eq_Ioc, h0, h1]

/-- For a `1`-periodic `Φ : ℝ → ℝ≥0∞` and every real `σ`, the lower integral over one period is
invariant under translation: `∫⁻ τ in Ioc 0 1, Φ (σ + τ) = ∫⁻ τ in Icc 0 1, Φ τ`. No measurability
of `Φ` is assumed. The proof lifts `Φ` to `AddCircle 1` and uses the translation invariance of the
measure on the circle. -/
theorem lintegral_Ioc_add_left_of_periodic {Φ : ℝ → ℝ≥0∞} (hΦ : Function.Periodic Φ 1) (σ : ℝ) :
    ∫⁻ τ in Set.Ioc (0 : ℝ) 1, Φ (σ + τ) = ∫⁻ τ in Set.Icc (0 : ℝ) 1, Φ τ := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 : ∀ τ : ℝ, Φ (σ + τ) = hΦ.lift ((τ : AddCircle (1 : ℝ)) + (σ : AddCircle (1 : ℝ))) := by
    intro τ
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe, add_comm]
  have h2 : ∀ τ : ℝ, Φ τ = hΦ.lift (τ : AddCircle (1 : ℝ)) :=
      fun τ ↦ (Function.Periodic.lift_coe hΦ τ).symm
  simp_rw [h1]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  simp_rw [h2]
  have a1 := AddCircle.lintegral_preimage 1 0 (fun x ↦ hΦ.lift (x + (σ : AddCircle (1 : ℝ))))
  have a2 := AddCircle.lintegral_preimage 1 0 (fun x ↦ hΦ.lift x)
  rw [zero_add] at a1 a2
  rw [a1, a2, lintegral_add_right_eq_self (fun x ↦ hΦ.lift x) (σ : AddCircle (1 : ℝ))]

/-- Let `q : ℝ → ℝ≥0∞` and `c : ℝ≥0∞` satisfy `∫⁻ σ in Ioc k (k + 1), q σ = c` for every real `k`.
Then `∫⁻ σ in Ioc a (a + n), q σ ≤ n * c` for every real `a` and every natural number `n`. The proof
is by induction on `n`, splitting off the last interval of length one. -/
theorem lintegral_Ioc_add_nat_le_nat_mul (q : ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : ∀ k : ℝ, ∫⁻ σ in Set.Ioc k (k + 1), q σ = c) (a : ℝ) (n : ℕ) :
    ∫⁻ σ in Set.Ioc a (a + n), q σ ≤ n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : Set.Ioc a (a + ((n + 1 : ℕ) : ℝ)) = Set.Ioc a (a + n) ∪
        Set.Ioc (a + n) (a + n + 1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by simp) (by linarith)]
      push_cast
      ring_nf
    rw [hs]
    refine (lintegral_union_le _ _ _).trans ?_
    rw [hc (a + n)]
    calc (∫⁻ σ in Set.Ioc a (a + n), q σ) + c ≤ n * c + c := add_le_add ih le_rfl
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * c := by push_cast; ring

/-- For `F : ℝ → ℝ≥0∞` with `F (θ + 2 * π) = F θ` for all `θ`,
`∫⁻ θ in Ioc 0 (2 * π), F θ = ∫⁻ θ in Ioc (-π) π, F θ`. The proof splits the two intervals at `π`
and at `0` and shifts the piece over `Ioc π (2 * π)` by one period to `Ioc (-π) 0`. -/
theorem lintegral_Ioc_eq_lintegral_Ioc_of_periodic (F : ℝ → ℝ≥0∞)
    (hF : ∀ θ, F (θ + 2 * Real.pi) = F θ) :
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ = ∫⁻ θ in Ioc (-Real.pi) Real.pi, F θ := by
  have hπ := Real.pi_pos
  have e1 : Ioc (0 : ℝ) (2 * Real.pi) = Ioc 0 Real.pi ∪ Ioc Real.pi (2 * Real.pi) :=
    (Ioc_union_Ioc_eq_Ioc hπ.le (by linarith)).symm
  have e2 : Ioc (-Real.pi) Real.pi = Ioc (-Real.pi) 0 ∪ Ioc 0 Real.pi :=
    (Ioc_union_Ioc_eq_Ioc (by linarith) hπ.le).symm
  have hshift : ∫⁻ θ in Ioc Real.pi (2 * Real.pi), F θ = ∫⁻ θ in Ioc (-Real.pi) 0, F θ := by
    have hmp := measurePreserving_add_right (volume : Measure ℝ) (2 * Real.pi)
    have hemb : MeasurableEmbedding (fun x : ℝ ↦ x + 2 * Real.pi) := measurableEmbedding_addRight _
    have h := hmp.setLIntegral_comp_preimage_emb hemb F (Ioc Real.pi (2 * Real.pi))
    rw [Set.preimage_add_const_Ioc, show Real.pi - 2 * Real.pi = -Real.pi by ring, sub_self] at h
    simp only [hF] at h
    exact h.symm
  rw [e1, e2, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), hshift, add_comm]

/-- For `g : ℝ → ℝ≥0∞` with `g (φ + 2 * π) = g φ` for all `φ`,
`∫⁻ φ in Ioc 0 (2 * π), g φ ≤ (∫⁻ φ in Ioo (-π) π, g φ) + ∫⁻ φ in Ioo (-π) π, g φ`. The proof covers
`Ioc 0 (2 * π)` by `Ioo (-π) π` and `Icc π (2 * π)` and shifts the second piece by one period to
`Icc (-π) 0`. -/
theorem lintegral_Ioc_le_add_lintegral_Ioo (g : ℝ → ℝ≥0∞) (hper : ∀ φ, g (φ + 2 * Real.pi) = g φ) :
    ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), g φ
      ≤ (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ) + ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ := by
  have hpi := Real.pi_pos
  have hsub : Set.Ioc (0 : ℝ) (2 * Real.pi) ⊆ Set.Ioo (-Real.pi) Real.pi ∪
      Set.Icc Real.pi (2 * Real.pi) := by
    rintro x ⟨h1, h2⟩
    by_cases hx : x < Real.pi
    · exact Or.inl ⟨by linarith, hx⟩
    · exact Or.inr ⟨le_of_not_gt hx, h2⟩
  have hshift : ∫⁻ φ in Set.Icc Real.pi (2 * Real.pi), g φ = ∫⁻ φ in Set.Icc (-Real.pi) 0, g φ := by
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc,
      ← lintegral_add_right_eq_self (fun x ↦ (Set.Icc Real.pi (2 * Real.pi)).indicator g x)
          (2 * Real.pi)]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ Set.Icc (-Real.pi) 0
    · have hx' : x + 2 * Real.pi ∈ Set.Icc Real.pi (2 * Real.pi) := ⟨by linarith [hx.1], by
        linarith [hx.2]⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', hper]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      exact hx ⟨by linarith, by linarith⟩
  have hlast : ∫⁻ φ in Set.Icc Real.pi (2 * Real.pi), g φ ≤ ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
      g φ := by
    rw [hshift, setLIntegral_congr (Ioc_ae_eq_Icc (a := -Real.pi) (b := 0)).symm]
    exact lintegral_mono_set fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
  calc ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), g φ
      ≤ ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi ∪ Set.Icc Real.pi (2 * Real.pi), g φ :=
          lintegral_mono_set hsub
    _ ≤ (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ) + ∫⁻ φ in Set.Icc Real.pi (2 * Real.pi), g φ :=
        lintegral_union_le _ _ _
    _ ≤ _ := add_le_add le_rfl hlast

/-- For `f : ℝ → ℝ≥0∞` with `f (θ + 2 * π) = f θ` for all `θ`,
`∫⁻ θ in Ioc 0 (2 * π), f θ ≤ 2 * ∫⁻ θ in Ioo (-π) π, f θ`. The proof covers `Ioc 0 (2 * π)` by
`Ioc (-π) π` and `Ioc π (3 * π)`, shifts the second piece by one period, and replaces `Ioc (-π) π`
by `Ioo (-π) π` up to a null set. -/
theorem lintegral_Ioc_le_two_mul_lintegral_Ioo (f : ℝ → ℝ≥0∞)
    (hf : ∀ θ, f (θ + 2 * Real.pi) = f θ) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi), f θ ≤ 2 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, f θ := by
  have hπ := Real.pi_pos
  have hsub : Ioc 0 (2 * Real.pi) ⊆ Ioc (-Real.pi) Real.pi ∪ Ioc Real.pi (3 * Real.pi) := by
    intro x hx
    rcases le_or_gt x Real.pi with h | h
    · exact Or.inl ⟨by linarith [hx.1], h⟩
    · exact Or.inr ⟨h, by linarith [hx.2]⟩
  have hshift : ∫⁻ θ in Ioc Real.pi (3 * Real.pi), f θ = ∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ := by
    have e := (measurePreserving_add_right volume (2 * Real.pi)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight (2 * Real.pi)) f (Ioc Real.pi (3 * Real.pi))
    rw [preimage_add_const_Ioc] at e
    have h1 : Real.pi - 2 * Real.pi = -Real.pi := by ring
    have h2 : 3 * Real.pi - 2 * Real.pi = Real.pi := by ring
    rw [h1, h2] at e
    rw [← e]
    exact setLIntegral_congr_fun (f := fun a ↦ f (a + 2 * Real.pi)) measurableSet_Ioc
        (fun θ _ ↦ hf θ)
  have hIoo : ∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, f θ :=
    setLIntegral_congr Ioo_ae_eq_Ioc.symm
  calc ∫⁻ θ in Ioc 0 (2 * Real.pi), f θ
      ≤ ∫⁻ θ in Ioc (-Real.pi) Real.pi ∪ Ioc Real.pi (3 * Real.pi), f θ := lintegral_mono_set hsub
    _ ≤ (∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ) + ∫⁻ θ in Ioc Real.pi (3 * Real.pi), f θ :=
        lintegral_union_le f _ _
    _ = 2 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, f θ := by rw [hshift, hIoo, two_mul]

/-- If `h : ℝ → ℝ≥0∞` is periodic with period `2 * π`, then
`∫⁻ θ in Ioc (-π) π, h θ = ∫⁻ θ in Ioc 0 (2 * π), h θ`. -/
theorem lintegral_Ioc_neg_pi_pi_of_periodic {h : ℝ → ℝ≥0∞}
    (hh : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Ioc (-Real.pi) Real.pi, h θ = ∫⁻ θ in Ioc 0 (2 * Real.pi), h θ := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hh.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hh.lift
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  exact h1.trans h2.symm

/-- For `F : ℝ → ℝ≥0∞` periodic with period `2 * π`,
`∫⁻ θ in Ioo (-π) π, F θ = ∫⁻ θ in Ioc 0 (2 * π), F θ`. The proof replaces `Ioo (-π) π` by
`Ioc (-π) π` up to a null set and compares two fundamental domains of the translations by integer
multiples of `2 * π`. -/
theorem lintegral_Ioo_eq_lintegral_Ioc_of_periodic (F : ℝ → ℝ≥0∞)
    (hF : Function.Periodic F (2 * Real.pi)) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, F θ = ∫⁻ θ in Ioc 0 (2 * Real.pi), F θ := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [setLIntegral_congr Ioo_ae_eq_Ioc]
  have h1 := isAddFundamentalDomain_Ioc hT (-Real.pi)
  have h2 := isAddFundamentalDomain_Ioc hT 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  refine h1.setLIntegral_eq h2 F fun g x ↦ ?_
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
  change F ((g : ℝ) + x) = F x
  rw [← hn, add_comm]
  exact hF.zsmul n x

/-- For `a ≤ t`, `∫⁻ s in Set.Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4 : ℝ))) ≤
ENNReal.ofReal (4 * (t - a) ^ (1 / 4 : ℝ))`. The domain is enlarged to `Set.Ioc a
t`, where the lower integral equals the Bochner integral `∫ s in a..t, (t - s) ^ (-(3 / 4 : ℝ)) =
4 * (t - a) ^ (1 / 4 : ℝ)`. -/
theorem lintegral_Ioo_sub_rpow_le {a t : ℝ} (hat : a ≤ t) :
    ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) ≤
      ENNReal.ofReal (4 * (t - a) ^ (1 / 4 : ℝ)) := by
  have hr : (-1 : ℝ) < -(3 / 4) := by norm_num
  have hii : IntervalIntegrable (fun s ↦ (t - s) ^ (-(3 / 4) : ℝ)) volume a t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' hr (a := t - a) (b := 0)).comp_sub_left t
    simpa using h
  have hint : IntegrableOn (fun s ↦ (t - s) ^ (-(3 / 4) : ℝ)) (Ioc a t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).1 hii
  have hval : ∫ s in a..t, (t - s) ^ (-(3 / 4) : ℝ) = 4 * (t - a) ^ (1 / 4 : ℝ) := by
    have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x ^ (-(3 / 4) : ℝ))
      (a := a) (b := t) t
    rw [h, sub_self, integral_rpow (Or.inl hr)]
    have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
    rw [e, Real.zero_rpow (by norm_num)]
    ring
  calc ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ))
      ≤ ∫⁻ s in Ioc a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ s in Ioc a t, (t - s) ^ (-(3 / 4) : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦
          Real.rpow_nonneg (by linarith [hs.2]) _
    _ = ENNReal.ofReal (4 * (t - a) ^ (1 / 4 : ℝ)) := by
        rw [← intervalIntegral.integral_of_le hat, hval]

/-- For `p < 1` and `a ≤ t`,
`∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-p)) ≤ ENNReal.ofReal ((t - a) ^ (1 - p) / (1 -
p))`. The proof enlarges the domain to `Ioc a t` and evaluates the interval integral of `(t - s) ^
(-p)` by the substitution `s ↦ t - s`. -/
theorem lintegral_Ioo_sub_rpow_le_of_lt {p : ℝ} (hp : p < 1) {a t : ℝ} (hat : a ≤ t) :
    ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-p)) ≤
      ENNReal.ofReal ((t - a) ^ (1 - p) / (1 - p)) := by
  have hr : (-1 : ℝ) < -p := by linarith
  have hii : IntervalIntegrable (fun s ↦ (t - s) ^ (-p)) volume a t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' hr (a := t - a) (b := 0)).comp_sub_left t
    simpa using h
  have hint : IntegrableOn (fun s ↦ (t - s) ^ (-p)) (Ioc a t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).1 hii
  have hval : ∫ s in a..t, (t - s) ^ (-p) = (t - a) ^ (1 - p) / (1 - p) := by
    have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x ^ (-p))
      (a := a) (b := t) t
    rw [h, sub_self, integral_rpow (Or.inl hr)]
    have e : -p + 1 = 1 - p := by ring
    rw [e, Real.zero_rpow (by linarith), sub_zero]
  calc ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-p))
      ≤ ∫⁻ s in Ioc a t, ENNReal.ofReal ((t - s) ^ (-p)) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ s in Ioc a t, (t - s) ^ (-p)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦
          Real.rpow_nonneg (by linarith [hs.2]) _
    _ = ENNReal.ofReal ((t - a) ^ (1 - p) / (1 - p)) := by
        rw [← intervalIntegral.integral_of_le hat, hval]

/-- For `0 ≤ t`, `∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(2 / 3 : ℝ))) =
ENNReal.ofReal (3 * t ^ (1 / 3 :
ℝ))`. The lower integral of the nonnegative integrable kernel is converted to a Bochner integral,
which is computed with the substitution `s ↦ t - s`. -/
theorem lintegral_Ioo_sub_rpow_neg_two_thirds {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(2 / 3 : ℝ))) =
      ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) := by
  have hii : IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ (-(2 / 3 : ℝ))) volume 0 t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (r := -(2 / 3 : ℝ)) (a := t) (b := 0)
      (by norm_num)).comp_sub_left t
    simpa using h
  have hion : IntegrableOn (fun s : ℝ ↦ (t - s) ^ (-(2 / 3 : ℝ))) (Ioo 0 t) :=
    (hii.1).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hion]
  · congr 1
    rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_sub_left (fun x ↦ x ^ (-(2 / 3 : ℝ))) t]
    simp only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [Real.zero_rpow (by norm_num)]
    norm_num
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact Real.rpow_nonneg (by linarith [hs.2]) _

/-- The lower integral of a sum of four functions `α → ℝ≥0∞` is the sum of the four lower integrals,
`∫⁻ z, (f1 z + f2 z + f3 z + f4 z) ∂μ = ∫⁻ z, f1 z ∂μ + ∫⁻ z, f2 z ∂μ + ∫⁻ z, f3 z ∂μ + ∫⁻ z, f4 z
∂μ`, when `f1`, `f2` and `f3` are almost everywhere measurable. No measurability of `f4` is assumed.
The proof splits off one summand at a time. -/
theorem lintegral_add_four {α : Type*} [MeasurableSpace α] {μ : Measure α} {f1 f2 f3 f4 : α → ℝ≥0∞}
    (h1 : AEMeasurable f1 μ) (h2 : AEMeasurable f2 μ) (h3 : AEMeasurable f3 μ) :
    ∫⁻ z, (f1 z + f2 z + f3 z + f4 z) ∂μ = ∫⁻ z, f1 z ∂μ + ∫⁻ z, f2 z ∂μ + ∫⁻ z, f3 z ∂μ + ∫⁻ z,
        f4 z ∂μ := by
  calc ∫⁻ z, (f1 z + f2 z + f3 z + f4 z) ∂μ = ∫⁻ z, (f1 z + f2 z + f3 z) ∂μ + ∫⁻ z, f4 z ∂μ :=
        lintegral_add_left' (f := fun z ↦ f1 z + f2 z + f3 z) ((h1.add h2).add h3) f4
    _ = ∫⁻ z, (f1 z + f2 z) ∂μ + ∫⁻ z, f3 z ∂μ + ∫⁻ z, f4 z ∂μ := by
        rw [show ∫⁻ z, (f1 z + f2 z + f3 z) ∂μ = ∫⁻ z, (f1 z + f2 z) ∂μ + ∫⁻ z, f3 z ∂μ from
          lintegral_add_left' (f := fun z ↦ f1 z + f2 z) (h1.add h2) f3]
    _ = _ := by
        rw [show ∫⁻ z, (f1 z + f2 z) ∂μ = ∫⁻ z, f1 z ∂μ + ∫⁻ z,
            f2 z ∂μ from lintegral_add_left' h1 f2]

/-- For `f g : α → ℝ≥0∞` with `f` almost everywhere measurable for `μ` and any real `c`,
`∫⁻ a, (f a + ENNReal.ofReal c * g a) ∂μ = ∫⁻ a, f a ∂μ + ENNReal.ofReal c * ∫⁻ a, g a
∂μ`. No measurability of `g` is assumed. -/
theorem lintegral_add_mul_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (c : ℝ) :
    ∫⁻ a, (f a + ENNReal.ofReal c * g a) ∂μ = ∫⁻ a, f a ∂μ + ENNReal.ofReal c * ∫⁻ a, g a ∂μ := by
  rw [lintegral_add_left' hf, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- For a measure `μ` on `ℝ`, a constant `c ≠ ⊤` in `ℝ≥0∞`, an almost everywhere measurable
`f : ℝ → ℝ≥0∞`, almost everywhere measurable `g j : ℝ → ℝ≥0∞` for `j : Fin 3`, and any
`t : ℝ → ℝ≥0∞`, `∫⁻ σ, (c * (f σ + ∑ j, g j σ) + t σ) ∂μ = c * (∫⁻ σ, f σ ∂μ +
∑ j, ∫⁻ σ, g j σ ∂μ) + ∫⁻ σ, t σ ∂μ`. No measurability of `t` is assumed. -/
theorem lintegral_const_mul_add_sum_add {μ : Measure ℝ} {c : ℝ≥0∞} (hc : c ≠ ⊤) {f : ℝ → ℝ≥0∞}
    {g : Fin 3 → ℝ → ℝ≥0∞} (t : ℝ → ℝ≥0∞) (hf : AEMeasurable f μ) (hg : ∀ j, AEMeasurable (g j) μ) :
    ∫⁻ σ, (c * (f σ + ∑ j, g j σ) + t σ) ∂μ = c * (∫⁻ σ, f σ ∂μ + ∑ j, ∫⁻ σ, g j σ ∂μ) + ∫⁻ σ,
        t σ ∂μ := by
  have hm : AEMeasurable (fun σ ↦ c * (f σ + ∑ j, g j σ)) μ :=
    (hf.add (Finset.aemeasurable_fun_sum Finset.univ fun j _ ↦ hg j)).const_mul c
  rw [lintegral_add_left' hm, lintegral_const_mul' _ _ hc, lintegral_add_left' hf,
    lintegral_finsetSum' _ fun j _ ↦ hg j]

/-- Let `u v : ℝ → α → E` be such that, for every `x`, the map `τ ↦ u τ x` has derivative `v σ x`
within `segment ℝ t s` at each `σ` of the segment and `σ ↦ v σ x` is continuous on the segment, and
such that each `v σ` with `σ` in the segment is almost everywhere strongly measurable and satisfies
`∫⁻ x, ‖v σ x - v t x‖ₑ ∂μ ≤ C`. Then
`∫⁻ x, ‖u s x - u t x - (s - t) • v t x‖ₑ ∂μ ≤ ENNReal.ofReal |s - t| * C`. The remainder is the
pointwise limit of sums over uniform partitions of the segment, each with lower integral at most
`ENNReal.ofReal |s - t| * C`, and Fatou's lemma concludes. -/
theorem lintegral_enorm_sub_sub_smul_deriv_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : ℝ → α → E} {t s : ℝ} {C : ℝ≥0∞}
    (hder : ∀ x, ∀ σ ∈ segment ℝ t s, HasDerivWithinAt (fun τ ↦ u τ x) (v σ x)
      (segment ℝ t s) σ)
    (hvc : ∀ x, ContinuousOn (fun σ ↦ v σ x) (segment ℝ t s))
    (hmeas : ∀ σ ∈ segment ℝ t s, AEStronglyMeasurable (v σ) μ)
    (hbd : ∀ σ ∈ segment ℝ t s, ∫⁻ x, ‖v σ x - v t x‖ₑ ∂μ ≤ C) :
    ∫⁻ x, ‖u s x - u t x - (s - t) • v t x‖ₑ ∂μ ≤ ENNReal.ofReal |s - t| * C := by
  set p : ℕ → ℕ → ℝ := fun N k ↦ t + ((k : ℝ) / (N + 1)) * (s - t) with hp
  set B : ℕ → α → E := fun N x ↦ ∑ k ∈ Finset.range (N + 1),
    ((s - t) / (N + 1)) • (v (p N k) x - v t x) with hB
  have hsplit : ∀ N x, B N x = (u s x - u t x - (s - t) • v t x) -
      ∑ k ∈ Finset.range (N + 1), (u (p N (k + 1)) x - u (p N k) x
        - ((s - t) / (N + 1)) • v (p N k) x) := by
    intro N x
    have hNpos : (N : ℝ) + 1 ≠ 0 := by positivity
    have htel : ∑ k ∈ Finset.range (N + 1), (u (p N (k + 1)) x - u (p N k) x) = u s x - u t x := by
      rw [Finset.sum_range_sub (fun k ↦ u (p N k) x)]
      simp only [hp]
      congr 2
      · push_cast; field_simp; ring
      · simp
    have hmul : ((N + 1 : ℕ) : ℝ) * ((s - t) / (N + 1)) = s - t := by push_cast; field_simp
    have hc : (s - t) • v t x = ∑ k ∈ Finset.range (N + 1), ((s - t) / (N + 1)) • v t x := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hmul]
    simp only [hB]
    rw [← htel, hc]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  have hlim : ∀ x, Tendsto (fun N ↦ B N x) atTop (𝓝 (u s x - u t x - (s - t) • v t x)) := by
    intro x
    have h0 := tendsto_sum_partition_sub_smul_deriv_zero (f := fun τ ↦ u τ x) (g := fun σ ↦ v σ x)
      (hder x) (hvc x)
    have := (tendsto_const_nhds (x := u s x - u t x - (s - t) • v t x)).sub h0
    rw [sub_zero] at this
    refine this.congr ?_
    intro N
    rw [hsplit N x]
  have hptw : ∀ x, ‖u s x - u t x - (s - t) • v t x‖ₑ = liminf (fun N ↦ ‖B N x‖ₑ) atTop :=
    fun x ↦ (((continuous_eNorm).tendsto _).comp (hlim x)).liminf_eq.symm
  have hpI : ∀ N k, k ∈ Finset.range (N + 1) → p N k ∈ segment ℝ t s := fun N k hk ↦
    add_div_mul_sub_mem_segment t s N k (by have := Finset.mem_range.1 hk; omega)
  have htI : t ∈ segment ℝ t s := left_mem_segment ℝ t s
  have hBmeas : ∀ N, AEMeasurable (fun x ↦ ‖B N x‖ₑ) μ := by
    intro N
    have : AEStronglyMeasurable (B N) μ := by
      simp only [hB]
      exact Finset.aestronglyMeasurable_fun_sum _ fun k hk ↦
        ((hmeas _ (hpI N k hk)).sub (hmeas t htI)).const_smul _
    exact this.eNorm
  have hBbd : ∀ N, ∫⁻ x, ‖B N x‖ₑ ∂μ ≤ ENNReal.ofReal |s - t| * C := by
    intro N
    have hNpos : (0 : ℝ) < N + 1 := by positivity
    calc ∫⁻ x, ‖B N x‖ₑ ∂μ
        ≤ ∫⁻ x, ∑ k ∈ Finset.range (N + 1),
            ‖((s - t) / (N + 1)) • (v (p N k) x - v t x)‖ₑ ∂μ :=
          lintegral_mono fun x ↦ eNorm_sum_le _ _
      _ = ∑ k ∈ Finset.range (N + 1),
            ∫⁻ x, ‖((s - t) / (N + 1)) • (v (p N k) x - v t x)‖ₑ ∂μ :=
          lintegral_finsetSum' _ fun k hk ↦
            (((hmeas _ (hpI N k hk)).sub (hmeas t htI)).const_smul _).eNorm
      _ = ∑ k ∈ Finset.range (N + 1),
            ‖(s - t) / (N + 1)‖ₑ * ∫⁻ x, ‖v (p N k) x - v t x‖ₑ ∂μ := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          simp only [eNorm_smul]
          exact lintegral_const_mul' _ _ eNorm_ne_top
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖(s - t) / (N + 1)‖ₑ * C :=
          Finset.sum_le_sum fun k hk ↦ by gcongr; exact hbd _ (hpI N k hk)
      _ = ENNReal.ofReal |s - t| * C := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [eNorm_eq_ofReal_abs, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), abs_div, abs_of_pos hNpos]
          congr 1
          push_cast; field_simp
  calc ∫⁻ x, ‖u s x - u t x - (s - t) • v t x‖ₑ ∂μ
      = ∫⁻ x, liminf (fun N ↦ ‖B N x‖ₑ) atTop ∂μ := lintegral_congr fun x ↦ hptw x
    _ ≤ liminf (fun N ↦ ∫⁻ x, ‖B N x‖ₑ ∂μ) atTop := lintegral_liminf_le' hBmeas
    _ ≤ ENNReal.ofReal |s - t| * C :=
        liminf_le_of_frequently_le' (Frequently.of_forall hBbd)

/-- A constant `c : ℝ≥0∞` with `c ≠ ⊤` can be pulled out of the iterated lower integral over
`Icc 0 1` and `Icc 0 (2 * π)`: for every `f : ℝ → ℝ → ℝ≥0∞`,
`∫⁻ τ in Icc 0 1, ∫⁻ φ in Icc 0 (2 * π), c * f τ φ = c * ∫⁻ τ in Icc 0 1, ∫⁻ φ in Icc 0 (2 * π), f τ
φ`. No measurability of `f` is assumed. -/
theorem lintegral_lintegral_const_mul_Icc (c : ℝ≥0∞) (hc : c ≠ ⊤) (f : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), c * f τ φ
      = c * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f τ φ := by
  simp_rw [lintegral_const_mul' _ _ hc]

/-- The iterated lower integral over `Icc 0 1` and `Icc 0 (2 * π)` commutes with a finite sum: if
for every `k` the function `(τ, φ) ↦ f k τ φ` is measurable on `ℝ × ℝ` with values in `ℝ≥0∞`, then
`∫⁻ τ in Icc 0 1, ∫⁻ φ in Icc 0 (2 * π), ∑ k ∈ s, f k τ φ = ∑ k ∈ s, ∫⁻ τ in Icc 0 1, ∫⁻ φ in Icc 0
(2 * π), f k τ φ`. -/
theorem lintegral_lintegral_finset_sum_Icc {κ : Type*} (s : Finset κ) (f : κ → ℝ → ℝ → ℝ≥0∞)
    (hf : ∀ k, Measurable (fun p : ℝ × ℝ ↦ f k p.1 p.2)) :
    ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ∑ k ∈ s, f k τ φ
      = ∑ k ∈ s, ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f k τ φ := by
  have h1 : ∀ τ, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ∑ k ∈ s, f k τ φ
      = ∑ k ∈ s, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f k τ φ := fun τ ↦
    lintegral_finsetSum s fun k _ ↦ (hf k).comp measurable_prodMk_left
  simp_rw [h1]
  exact lintegral_finsetSum s fun k _ ↦ (hf k).lintegral_prod_right'

/-- If `F : ℝ → ℝ≥0∞` is bounded pointwise by a constant `K < ⊤` on `Icc (-2) 2` and by `0`
elsewhere, that is `F s ≤ (Icc (-2) 2).indicator (fun _ ↦ K) s` for all `s`, then `∫⁻ s, F s < ⊤`.
-/
theorem lintegral_lt_top_of_le_indicator_const {F : ℝ → ℝ≥0∞} {K : ℝ≥0∞} (hK : K < ⊤)
    (hF : ∀ s, F s ≤ (Set.Icc (-2 : ℝ) 2).indicator (fun _ ↦ K) s) :
    ∫⁻ s, F s < ⊤ := by
  calc ∫⁻ s, F s ≤ ∫⁻ s, (Set.Icc (-2 : ℝ) 2).indicator (fun _ ↦ K) s := lintegral_mono hF
    _ = K * volume (Set.Icc (-2 : ℝ) 2) := lintegral_indicator_const measurableSet_Icc K
    _ < ⊤ := ENNReal.mul_lt_top hK (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-- A weighted Hölder inequality with exponents `6 / 5` and `6` for lower integrals: for almost
everywhere measurable `A B W : X → ℝ≥0∞` with `W x ≠ 0` and `W x ≠ ⊤` for all `x`,
`(∫⁻ x, A x * B x ∂μ) ^ 6 ≤ (∫⁻ x, A x * W x ∂μ) ^ 5 * ∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6
∂μ`. The proof applies Hölder's inequality to the factors `(A x * W x) ^ (5 / 6)` and
`A x ^ (1 / 6) * (W x)⁻¹ ^ (5 / 6) * B x`. -/
theorem lintegral_mul_pow_six_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B W : X → ℝ≥0∞}
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) (hW : AEMeasurable W μ)
    (hW0 : ∀ x, W x ≠ 0) (hWt : ∀ x, W x ≠ ⊤) :
    (∫⁻ x, A x * B x ∂μ) ^ 6 ≤ (∫⁻ x, A x * W x ∂μ) ^ 5 * ∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ := by
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun x ↦ (A x * W x) ^ (5 / 6 : ℝ))
    (g := fun x ↦ A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x)
    ((hA.mul hW).pow_const _) (((hA.pow_const _).mul (hW.inv.pow_const _)).mul hB)
  have e1 : ∀ x, (A x * W x) ^ (5 / 6 : ℝ) * (A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x) =
      A x * B x := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc A x ^ (5 / 6 : ℝ) * W x ^ (5 / 6 : ℝ) * (A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x)
        = (A x ^ (5 / 6 : ℝ) * A x ^ (1 / 6 : ℝ)) * (W x * (W x)⁻¹) ^ (5 / 6 : ℝ) * B x := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          ring
      _ = A x * B x := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
            ENNReal.mul_inv_cancel (hW0 x) (hWt x)]
          norm_num
  have e2 : ∀ x, ((A x * W x) ^ (5 / 6 : ℝ)) ^ (6 / 5 : ℝ) = A x * W x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x) ^ (6 : ℝ) =
      A x * (W x)⁻¹ ^ 5 * B x ^ 6 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have h5 : (5 / 6 : ℝ) * 6 = ((5 : ℕ) : ℝ) := by norm_num
    have h6 : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [h5, ENNReal.rpow_natCast, h6, ENNReal.rpow_natCast]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x ∂μ) ^ 6
      ≤ ((∫⁻ x, A x * W x ∂μ) ^ (1 / (6 / 5) : ℝ) *
          (∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ) ^ (1 / 6 : ℝ)) ^ 6 := by gcongr
    _ = (∫⁻ x, A x * W x ∂μ) ^ 5 * ∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 6), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        have h5 : (1 / (6 / 5) : ℝ) * ((6 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
        have h1 : (1 / 6 : ℝ) * ((6 : ℕ) : ℝ) = 1 := by norm_num
        rw [h5, h1, ENNReal.rpow_natCast, ENNReal.rpow_one]

/-- Let `f g : ℝ × ℝ → ℝ` be almost everywhere measurable for a measure `μ`, with
`∫⁻ p, ENNReal.ofReal (f p) ∂μ ≠ ⊤` and `∫⁻ p, ENNReal.ofReal (-g p) ∂μ ≠ ⊤`. If
`∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ`, then
`∫⁻ p, ENNReal.ofReal (-f p) ∂μ + ∫⁻ p, ENNReal.ofReal (g p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (f p) ∂μ + ∫⁻
p, ENNReal.ofReal (-g p) ∂μ`. The proof integrates the pointwise identity `ofReal (-f) + ofReal g +
ofReal (f - g) = ofReal f + ofReal (-g) + ofReal (-(f - g))` and cancels the finite term `∫⁻ p,
ENNReal.ofReal (f p - g p) ∂μ`. -/
theorem lintegral_ofReal_neg_add_le_of_sub {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (ho : (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) ≤ (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ))
    (hfp : (∫⁻ p, ENNReal.ofReal (f p) ∂μ) ≠ ⊤) (hgn : (∫⁻ p, ENNReal.ofReal (-g p) ∂μ) ≠ ⊤) :
    (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (g p) ∂μ)
      ≤ (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ) := by
  have mfn : AEMeasurable (fun p ↦ ENNReal.ofReal (-f p)) μ := hf.neg.ennreal_ofReal
  have mgp : AEMeasurable (fun p ↦ ENNReal.ofReal (g p)) μ := hg.ennreal_ofReal
  have mfp : AEMeasurable (fun p ↦ ENNReal.ofReal (f p)) μ := hf.ennreal_ofReal
  have mgn : AEMeasurable (fun p ↦ ENNReal.ofReal (-g p)) μ := hg.neg.ennreal_ofReal
  have hsum : (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (g p) ∂μ)
        + (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ)
      = (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ)
        + (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) := by
    calc (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (g p) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ)
        = (∫⁻ p, (ENNReal.ofReal (-f p) + ENNReal.ofReal (g p)) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ) := by rw [lintegral_add_left' mfn]
      _ = (∫⁻ p, (ENNReal.ofReal (-f p) + ENNReal.ofReal (g p) + ENNReal.ofReal (f p - g p)) ∂μ) :=
          (lintegral_add_left' (mfn.add mgp) _).symm
      _ = (∫⁻ p, (ENNReal.ofReal (f p) + ENNReal.ofReal (-g p) + ENNReal.ofReal (-(f p - g p)))
          ∂μ) :=
          lintegral_congr fun p ↦ ofReal_neg_add_ofReal_add_ofReal_sub (f p) (g p)
      _ = (∫⁻ p, (ENNReal.ofReal (f p) + ENNReal.ofReal (-g p)) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) := lintegral_add_left' (mfp.add mgn) _
      _ = (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) := by rw [lintegral_add_left' mfp]
  have hofin : (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfp, hgn⟩) ?_
    calc (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ)
        ≤ (∫⁻ p, (ENNReal.ofReal (f p) + ENNReal.ofReal (-g p)) ∂μ) := by
          refine lintegral_mono fun p ↦ ?_
          rw [sub_eq_add_neg]
          exact ENNReal.ofReal_add_le
      _ = (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ) :=
          lintegral_add_left' mfp _
  refine (ENNReal.add_le_add_iff_right hofin).1 ?_
  rw [hsum]
  exact add_le_add le_rfl ho

/-- Let `μ` be a measure on `ℝ × ℝ` and let `S`, `V`, `D : ℝ × ℝ → ℝ` satisfy `0 ≤ S p`, `0 ≤ V p`
and `γ * S p - α * V p ≤ D p` for almost every `p`, where `0 ≤ α`, `0 ≤ γ` and `α ≤ γ * c`. If
`fun p ↦ ENNReal.ofReal (V p)` is almost everywhere measurable,
`ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (S p) ∂μ` and
`∫⁻ p, ENNReal.ofReal (S p) ∂μ < ⊤`, then
`∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (D p) ∂μ`. The proof shows that the lower
integral of `ENNReal.ofReal (α * V p - γ * S p)` is at most that of
`ENNReal.ofReal (γ * S p - α * V p)`, by adding the finite lower integral of
`ENNReal.ofReal (γ * S p)` to both sides. -/
theorem lintegral_ofReal_neg_le_lintegral_ofReal {μ : Measure (ℝ × ℝ)} {S V D : ℝ × ℝ → ℝ}
    {α γ c : ℝ} (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hαγ : α ≤ γ * c)
    (hS0 : ∀ᵐ p ∂μ, 0 ≤ S p) (hV0 : ∀ᵐ p ∂μ, 0 ≤ V p) (hD : ∀ᵐ p ∂μ, γ * S p - α * V p ≤ D p)
    (hVm : AEMeasurable (fun p ↦ ENNReal.ofReal (V p)) μ)
    (hinv : ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (S p) ∂μ)
    (hfin : ∫⁻ p, ENNReal.ofReal (S p) ∂μ < ⊤) :
    ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (D p) ∂μ := by
  have hmulS : ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ = ENNReal.ofReal γ * ∫⁻ p,
      ENNReal.ofReal (S p) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun p ↦ ENNReal.ofReal_mul hγ
  have hmulV : ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ = ENNReal.ofReal α * ∫⁻ p,
      ENNReal.ofReal (V p) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun p ↦ ENNReal.ofReal_mul hα
  have hαV : ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ := by
    rw [hmulS, hmulV]
    calc ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ
        ≤ ENNReal.ofReal γ * ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ := by
          rw [← ENNReal.ofReal_mul hγ]
          gcongr
      _ = ENNReal.ofReal γ * (ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ) := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (S p) ∂μ := by gcongr
  have hfinS : ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ ≠ ⊤ := by
    rw [hmulS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hVm' : AEMeasurable (fun p ↦ ENNReal.ofReal (α * V p)) μ := by
    have := hVm.const_mul (ENNReal.ofReal α)
    refine this.congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only
    rw [ENNReal.ofReal_mul hα]
  have hkey : ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ ≤ ∫⁻ p,
      ENNReal.ofReal (γ * S p - α * V p) ∂μ := by
    have hsum : ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ
        ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ := by
      calc ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ
          ≤ ∫⁻ p, (ENNReal.ofReal (α * V p - γ * S p) + ENNReal.ofReal (γ * S p)) ∂μ :=
              le_lintegral_add _ _
        _ = ∫⁻ p, (ENNReal.ofReal (γ * S p - α * V p) + ENNReal.ofReal (α * V p)) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hS0, hV0] with p hs hv
          exact ofReal_sub_add_ofReal_comm (mul_nonneg hα hv) (mul_nonneg hγ hs)
        _ = ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ + ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ :=
          lintegral_add_right' _ hVm'
        _ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ := by
          gcongr
    exact (ENNReal.add_le_add_iff_right hfinS).1 hsum
  calc ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD] with p hp
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ := hkey
    _ ≤ ∫⁻ p, ENNReal.ofReal (D p) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD] with p hp
        exact ENNReal.ofReal_le_ofReal hp

/-- For a measure `μ` on `ℝ`, almost everywhere measurable `f b : ℝ → ℝ≥0∞` with `b x ≠ 0` and
`b x ≠ ⊤` for all `x`, and a real `p > 1`,
`(∫⁻ x, f x ∂μ) ^ p ≤ (∫⁻ x, b x ∂μ) ^ (p - 1) * ∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ`. The proof writes
`f = b ^ r * (b ^ (-r) * f)` with `r = (p - 1) / p` and applies Hölder's inequality with exponents
`p / (p - 1)` and `p`. -/
theorem lintegral_rpow_le_weighted (μ : Measure ℝ) {f b : ℝ → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hb : AEMeasurable b μ)
    (hb0 : ∀ x, b x ≠ 0) (hbt : ∀ x, b x ≠ ⊤) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, f x ∂μ) ^ p ≤ (∫⁻ x, b x ∂μ) ^ (p - 1) * ∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hq : p.conjExponent.HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have hqe : p.conjExponent = p / (p - 1) := rfl
  set r := (p - 1) / p with hr
  have hsplit : ∀ x, f x = b x ^ r * (b x ^ (-r) * f x) := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (hb0 x) (hbt x), add_neg_cancel, ENNReal.rpow_zero,
        one_mul]
  have e1 : ∀ x, (b x ^ r) ^ p.conjExponent = b x := by
    intro x
    rw [← ENNReal.rpow_mul, hqe, hr]
    have : (p - 1) / p * (p / (p - 1)) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  have e2 : ∀ x, (b x ^ (-r) * f x) ^ p = b x ^ (1 - p) * f x ^ p := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hr]
    congr 2
    field_simp
    ring
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hq (hb.pow_const r) ((hb.pow_const (-r)).mul hf)
  have h2 : ∫⁻ x, f x ∂μ ≤ (∫⁻ x, b x ∂μ) ^ (1 / p.conjExponent) *
      (∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ) ^ (1 / p) := by
    calc ∫⁻ x, f x ∂μ = ∫⁻ x, ((fun x ↦ b x ^ r) * fun x ↦ b x ^ (-r) * f x) x ∂μ :=
          lintegral_congr fun x ↦ hsplit x
      _ ≤ _ := h1
      _ = _ := by simp only [Pi.mul_apply, e1, e2]
  calc (∫⁻ x, f x ∂μ) ^ p ≤ ((∫⁻ x, b x ∂μ) ^ (1 / p.conjExponent) *
        (∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ) ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h2 hp0.le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hqe]
      have a1 : 1 / (p / (p - 1)) * p = p - 1 := by field_simp
      have a2 : 1 / p * p = 1 := by field_simp
      rw [a1, a2, ENNReal.rpow_one]

/-- For a measure `μ` and almost everywhere measurable `a b : X → ℝ≥0∞` with `∫⁻ x, a x ∂μ = 1`,
`(∫⁻ x, a x * b x ∂μ) ^ 2 ≤ ∫⁻ x, a x * b x ^ 2 ∂μ`. The proof applies Hölder's inequality with
exponents `2` and `2` to `a ^ (1 / 2)` and `a ^ (1 / 2) * b`. -/
theorem lintegral_sq_le_of_lintegral_eq_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b : X → ℝ≥0∞) (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (h1 : ∫⁻ x, a x ∂μ = 1) :
    (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ ∫⁻ x, a x * b x ^ 2 ∂μ := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x ↦ a x ^ (1 / 2 : ℝ)) (g := fun x ↦ a x ^ (1 / 2 : ℝ) * b x)
    (ha.pow_const _) ((ha.pow_const _).mul hb)
  have e1 : ∀ x, a x ^ (1 / 2 : ℝ) * (a x ^ (1 / 2 : ℝ) * b x) = a x * b x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (a x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (a x ^ (1 / 2 : ℝ) * b x) ^ (2 : ℝ) = a x * b x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ← ENNReal.rpow_natCast]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3, h1, ENNReal.one_rpow, one_mul] at hH
  calc (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ ((∫⁻ x, a x * b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ∫⁻ x, a x * b x ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

/-- For a measure `μ` and almost everywhere measurable `f`, `g : α → ℝ≥0∞`,
`∫⁻ a, f a ^ (1 / 2 : ℝ) * g a ^ (1 / 2 : ℝ) ∂μ ≤ (∫⁻ a, f a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ∂μ) ^ (1
/ 2 : ℝ)`. This is Hölder's inequality with exponents `2` and `2` applied to `f ^ (1 / 2)` and `g ^
(1 / 2)`. -/
theorem lintegral_sqrt_mul_sqrt_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ^ ((1 : ℝ) / 2) * g a ^ ((1 : ℝ) / 2) ∂μ ≤
      (∫⁻ a, f a ∂μ) ^ ((1 : ℝ) / 2) * (∫⁻ a, g a ∂μ) ^ ((1 : ℝ) / 2) := by
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hf.pow_const ((1 : ℝ) / 2)) (hg.pow_const ((1 : ℝ) / 2))
  have e : ∀ x : ENNReal, (x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = x := fun x ↦ by
    rw [← ENNReal.rpow_mul]; norm_num
  simp only [Pi.mul_apply, e] at key
  exact key

/-- For `0 < P` and any `F : ℝ → ℝ≥0∞`,
`∫⁻ s in Icc 0 P, F (P⁻¹ * s) = ENNReal.ofReal P * ∫⁻ σ in Icc 0 1, F σ`. The proof changes
variables with the measurable embedding `s ↦ P⁻¹ * s`. -/
theorem setLIntegral_Icc_inv_mul {P : ℝ} (hP : 0 < P) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Set.Icc 0 P, F (P⁻¹ * s) = ENNReal.ofReal P * ∫⁻ σ in Set.Icc 0 1, F σ := by
  have hP0 : P⁻¹ ≠ 0 := inv_ne_zero hP.ne'
  have he : MeasurableEmbedding (fun s : ℝ ↦ P⁻¹ * s) :=
    (Homeomorph.mulLeft₀ P⁻¹ hP0).toMeasurableEquiv.measurableEmbedding
  have hpre : (fun s : ℝ ↦ P⁻¹ * s) ⁻¹' Set.Icc 0 1 = Set.Icc 0 P := by
    rw [Set.preimage_const_mul_Icc₀ _ _ (inv_pos.2 hP)]
    simp
  rw [← hpre, ← he.lintegral_map, ← he.restrict_map, Real.map_volume_mul_left hP0,
    Measure.restrict_smul, lintegral_smul_measure, inv_inv, abs_of_pos hP, smul_eq_mul]

/-- If `h : ℝ → ℝ≥0∞` is invariant under translation by `c`, that is `h (s + c) = h s` for all `s`,
then `∫⁻ s in Icc c (c + 1), h s = ∫⁻ s in Icc 0 1, h s`. No measurability of `h` is assumed. The
proof changes variables by the translation `x ↦ x + c`, which preserves Lebesgue measure. -/
theorem setLIntegral_Icc_shift_of_add_eq {h : ℝ → ℝ≥0∞} (c : ℝ) (hc : ∀ s, h (s + c) = h s) :
    ∫⁻ s in Set.Icc c (c + 1), h s = ∫⁻ s in Set.Icc (0 : ℝ) 1, h s := by
  have hm : MeasurePreserving (fun x : ℝ ↦ x + c) volume volume :=
    measurePreserving_add_right volume c
  have he : MeasurableEmbedding (fun x : ℝ ↦ x + c) :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  have e := hm.setLIntegral_comp_emb he h (Set.Icc (0 : ℝ) 1)
  rw [Set.image_add_const_Icc, zero_add, add_comm 1 c] at e
  rw [← e]
  simp only [hc]

/-- Let `s` be a measurable set in `ℝ × ℝ` that is almost everywhere contained in a set `t`, and let
`w : ℝ × ℝ → ℝ≥0∞` be almost everywhere measurable on `t`. If `f p ≤ h p + w p` for all `p ∈ s`,
where `f h : ℝ × ℝ → ℝ≥0∞`, then `∫⁻ p in s, f p ≤ (∫⁻ p in s, h p) + ∫⁻ p in t, w p`. -/
theorem setLIntegral_le_add {s t : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hst : s ≤ᵐ[volume] t)
    {f h w : ℝ × ℝ → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict t))
        (hf : ∀ p ∈ s, f p ≤ h p + w p) :
    ∫⁻ p in s, f p ≤ (∫⁻ p in s, h p) + ∫⁻ p in t, w p :=
  calc ∫⁻ p in s, f p ≤ ∫⁻ p in s, (h p + w p) := setLIntegral_mono' hs hf
    _ = (∫⁻ p in s, h p) + ∫⁻ p in s, w p :=
      lintegral_add_right' _ (hw.mono_measure (Measure.restrict_mono_ae hst))
    _ ≤ (∫⁻ p in s, h p) + ∫⁻ p in t, w p := add_le_add le_rfl (lintegral_mono_set' hst)

/-- For `0 ≤ T` and `g : ℝ → ℝ` that is continuous on `Set.Icc 0 T` and nonnegative everywhere,
`∫⁻ s in Set.Icc 0 T, ENNReal.ofReal (g s) = ENNReal.ofReal (∫ s in (0 : ℝ)..T, g s)`. -/
theorem setLIntegral_ofReal_eq_intervalIntegral {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (hg0 : ∀ s, 0 ≤ g s) :
    ∫⁻ s in Icc 0 T, ENNReal.ofReal (g s) = ENNReal.ofReal (∫ s in (0 : ℝ)..T, g s) := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc) (ae_of_all _ hg0)]

/-- If `f : ℝ → ℂ` is almost everywhere strongly measurable on `Ioo (-π) π`, then
`(∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ) ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^
2`. The proof applies Hölder's inequality with exponents `2` and `2` to `‖f
θ‖ₑ` and the constant `1`. -/
theorem sq_lintegral_enorm_le_mul_lintegral_sq {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo (-π) π))) :
    (∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ) ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo (-π) π))
      Real.HolderConjugate.two_two
    hf.eNorm (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioo, one_mul] at h
  have e2 : ∀ x : ENNReal, x ^ (2 : ℝ) = x ^ 2 := fun x ↦ by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [e2] at h
  have hsq : ∀ x : ENNReal, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ) ^ 2
      ≤ ((∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (ENNReal.ofReal (π - -π)) ^ (1 / 2 : ℝ))
          ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
        rw [mul_pow, hsq, hsq, mul_comm]; congr 2; ring

/-- If `f : ℝ → ℝ≥0∞` is almost everywhere measurable on `Icc 0 1`, then
`(∫⁻ τ in Icc 0 1, f τ) ^ 2 ≤ ∫⁻ τ in Icc 0 1, f τ ^ 2`. The proof applies Hölder's inequality with
exponents `2` and `2` to `f` and the constant `1` on this interval of measure `1`. -/
theorem sq_lintegral_Icc_zero_one_le {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (∫⁻ τ in Set.Icc (0 : ℝ) 1, f τ) ^ 2 ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, f τ ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) 1))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hone : (∫⁻ _ in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ^ (2 : ℝ)) = 1 := by
    simp [Real.volume_Icc]
  rw [hone, ENNReal.one_rpow, mul_one] at h
  simp only [Pi.mul_apply, mul_one] at h
  have hsq : (fun a ↦ f a ^ (2 : ℝ)) = fun a ↦ f a ^ 2 := by
    funext a
    exact ENNReal.rpow_two (f a)
  rw [hsq] at h
  calc (∫⁻ τ in Set.Icc (0 : ℝ) 1, f τ) ^ 2
      ≤ ((∫⁻ a in Set.Icc (0 : ℝ) 1, f a ^ 2) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left₀ zero_le h 2
    _ = ∫⁻ a in Set.Icc (0 : ℝ) 1, f a ^ 2 := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-- For `0 ≤ t` and `f g : ℝ → ℝ≥0∞` that are almost everywhere measurable on `Set.Ioo 0 t`,
`∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * f s * g s ≤ ENNReal.ofReal (3 * t
^ (1 / 3 : ℝ)) ^ (3 / 4 : ℝ) * (∫⁻ s in Set.Ioo 0 t, (f s * g s) ^ (4 : ℝ)) ^ (1 / 4 :
ℝ)`. This is Hölder's inequality with exponents `4 / 3` and `4`: the `4 /
3` power of the kernel is `(t - s) ^ (-(2 / 3 : ℝ))`, whose integral is `3 * t ^ (1 / 3 : ℝ)`. -/
theorem lintegral_sub_rpow_neg_half_mul_le {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Ioo 0 t)))
    (hg : AEMeasurable g (volume.restrict (Ioo 0 t))) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * f s * g s ≤
      ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∫⁻ s in Ioo 0 t, (f s * g s) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := (Real.holderConjugate_iff).2 ⟨by norm_num, by
    norm_num⟩
  have hk : AEMeasurable (fun s : ℝ ↦ ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))))
      (volume.restrict (Ioo 0 t)) :=
    ((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal.aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo 0 t)) hpq hk (hf.mul hg)
  have hker : ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ^ (4 / 3 : ℝ) =
      ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) := by
    rw [← lintegral_Ioo_sub_rpow_neg_two_thirds ht]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun s hs ↦ ?_)
    have hts : 0 ≤ t - s := by linarith [hs.2]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hts _) (by norm_num),
      ← Real.rpow_mul hts]
    norm_num
  calc ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * f s * g s
      = ∫⁻ s in Ioo 0 t, ((fun s : ℝ ↦ ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ)))) *
          (fun s ↦ f s * g s)) s := by
        refine lintegral_congr (fun s ↦ ?_)
        simp only [Pi.mul_apply, mul_assoc]
    _ ≤ _ := h
    _ = _ := by
        rw [hker]
        norm_num

/-- If `h : ℝ → ℝ≥0∞` satisfies `h (s + 1) = h s` for all `s`, then
`∫⁻ s in Icc (-2) 2, h s ≤ 4 * ∫⁻ s in Icc 0 1, h s`. No measurability of `h` is assumed. The proof
covers `Icc (-2) 2` by the four intervals `Icc k (k + 1)` with `k = -2, -1, 0, 1` and moves each of
them to `Icc 0 1` by periodicity. -/
theorem setLIntegral_four_periods_le {h : ℝ → ℝ≥0∞} (hh : ∀ s, h (s + 1) = h s) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, h s ≤ 4 * ∫⁻ s in Set.Icc (0 : ℝ) 1, h s := by
  have hm1 : ∀ s, h (s + -1) = h s := fun s ↦ by
    rw [← hh (s + -1)]
    congr 1
    ring
  have hm2 : ∀ s, h (s + -2) = h s := fun s ↦ by
    rw [← hh (s + -2), show s + -2 + 1 = s + -1 by ring, hm1]
  have h0 : ∀ s, h (s + 0) = h s := fun s ↦ by rw [add_zero]
  have cover : Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (-2 : ℝ) (-2 + 1) ∪ Set.Icc (-1 : ℝ) (-1 + 1) ∪
      Set.Icc (0 : ℝ) (0 + 1) ∪ Set.Icc (1 : ℝ) (1 + 1) := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    simp only [Set.mem_union, Set.mem_Icc]
    rcases le_or_gt x (-1) with h1 | h1
    · exact Or.inl (Or.inl (Or.inl ⟨hx1, by linarith⟩))
    rcases le_or_gt x 0 with h2 | h2
    · exact Or.inl (Or.inl (Or.inr ⟨h1.le, by linarith⟩))
    rcases le_or_gt x 1 with h3 | h3
    · exact Or.inl (Or.inr ⟨h2.le, by linarith⟩)
    · exact Or.inr ⟨h3.le, by linarith⟩
  have e1 := lintegral_union_le (μ := volume) h (Set.Icc (-2 : ℝ) (-2 + 1) ∪
      Set.Icc (-1 : ℝ) (-1 + 1) ∪
      Set.Icc (0 : ℝ) (0 + 1)) (Set.Icc (1 : ℝ) (1 + 1))
  have e2 := lintegral_union_le (μ := volume) h (Set.Icc (-2 : ℝ) (-2 + 1) ∪
      Set.Icc (-1 : ℝ) (-1 + 1))
    (Set.Icc (0 : ℝ) (0 + 1))
  have e3 := lintegral_union_le (μ := volume) h (Set.Icc (-2 : ℝ) (-2 + 1))
      (Set.Icc (-1 : ℝ) (-1 + 1))
  rw [setLIntegral_Icc_shift_of_add_eq 1 hh] at e1
  rw [setLIntegral_Icc_shift_of_add_eq 0 h0] at e2
  rw [setLIntegral_Icc_shift_of_add_eq (-2) hm2, setLIntegral_Icc_shift_of_add_eq (-1) hm1] at e3
  exact (lintegral_mono_set cover).trans (e1.trans ((add_le_add (e2.trans
    (add_le_add e3 le_rfl)) le_rfl).trans (le_of_eq (by ring))))

/-- For real `A`, `C`, `K`, `T` there is a bound `B` such that, for every `T'` in `Set.Icc 0 T` and
all `n w : ℝ → ℝ` continuous and nonnegative on `Set.Icc 0 T'` with
`∫⁻ s in Set.Icc 0 T', ENNReal.ofReal (w s ^ 4) ≤ ENNReal.ofReal K`, the inequality
`ENNReal.ofReal (n t) ≤ ENNReal.ofReal A + ENNReal.ofReal C * ∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal
((t - s) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (w s) * ENNReal.ofReal (n s)` for all `t` in `Set.Icc 0
T'` implies `n t ≤ B` for all `t` in `Set.Icc 0 T'`. Hölder's inequality with exponents `4 /
3` and `4` turns the hypothesis into a linear integral inequality for `n ^
4`, to which Gronwall's inequality applies. -/
theorem exists_bound_of_le_add_lintegral_rpow (A C K T : ℝ) : ∃ B : ℝ, ∀ T' ∈ Icc 0 T, ∀ n w : ℝ →
    ℝ,
    ContinuousOn n (Icc 0 T') → ContinuousOn w (Icc 0 T') →
    (∀ t ∈ Icc 0 T', 0 ≤ n t) → (∀ t ∈ Icc 0 T', 0 ≤ w t) →
    ∫⁻ s in Icc 0 T', ENNReal.ofReal (w s ^ 4) ≤ ENNReal.ofReal K →
    (∀ t ∈ Icc 0 T', ENNReal.ofReal (n t) ≤ ENNReal.ofReal A + ENNReal.ofReal C *
      ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (w s) *
        ENNReal.ofReal (n s)) →
    ∀ t ∈ Icc 0 T', n t ≤ B := by
  set A' := max A 0 with hA'
  set C' := max C 0 with hC'
  set K' := max K 0 with hK'
  set c : ℝ := 3 * max T 0 ^ (1 / 3 : ℝ) with hc
  set D : ℝ := 8 * C' ^ 4 * c ^ (3 : ℝ) with hD
  set a : ℝ := 8 * A' ^ 4 with ha
  have hA0 : 0 ≤ A' := le_max_right _ _
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hK0 : 0 ≤ K' := le_max_right _ _
  have hc0 : 0 ≤ c := mul_nonneg (by norm_num) (Real.rpow_nonneg (le_max_right _ _) _)
  have hD0 : 0 ≤ D := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 _))
    (Real.rpow_nonneg hc0 _)
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num) (pow_nonneg hA0 _)
  refine ⟨max 1 (a * Real.exp (D * K')), ?_⟩
  intro T' hT' n w hn hw hn0 hw0 hW hmild
  have hT'0 : 0 ≤ T' := hT'.1
  have hφc : ContinuousOn (fun s ↦ n s ^ 4) (Icc 0 T') := hn.pow 4
  have hbc : ContinuousOn (fun s ↦ D * w s ^ 4) (Icc 0 T') := continuousOn_const.mul (hw.pow 4)
  have hbφc : ContinuousOn (fun s ↦ w s ^ 4 * n s ^ 4) (Icc 0 T') := (hw.pow 4).mul (hn.pow 4)
  have hJ : ∀ t ∈ Icc 0 T', ∫⁻ s in Ioo 0 t, ENNReal.ofReal (w s ^ 4 * n s ^ 4) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..t, w s ^ 4 * n s ^ 4) := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 T' := Icc_subset_Icc le_rfl ht.2
    have hint : IntegrableOn (fun s ↦ w s ^ 4 * n s ^ 4) (Ioo 0 t) :=
      ((hbφc.mono hsub).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs' : s ∈ Icc 0 T' := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    exact mul_nonneg (pow_nonneg (hw0 s hs') _) (pow_nonneg (hn0 s hs') _)
  have hstep : ∀ t ∈ Icc 0 T', n t ^ 4 ≤ a + ∫ s in (0 : ℝ)..t, D * w s ^ 4 * n s ^ 4 := by
    intro t ht
    have hsub : Ioo 0 t ⊆ Icc 0 T' := fun s hs ↦ ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hfm : AEMeasurable (fun s ↦ ENNReal.ofReal (w s)) (volume.restrict (Ioo 0 t)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn (hw.mono hsub)).aemeasurable measurableSet_Ioo
    have hgm : AEMeasurable (fun s ↦ ENNReal.ofReal (n s)) (volume.restrict (Ioo 0 t)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn (hn.mono hsub)).aemeasurable measurableSet_Ioo
    have hH := lintegral_sub_rpow_neg_half_mul_le ht.1 hfm hgm
    have hJeq : ∫⁻ s in Ioo 0 t, (ENNReal.ofReal (w s) * ENNReal.ofReal (n s)) ^ (4 : ℝ) =
        ∫⁻ s in Ioo 0 t, ENNReal.ofReal (w s ^ 4 * n s ^ 4) := by
      refine setLIntegral_congr_fun measurableSet_Ioo (fun s hs ↦ ?_)
      have hs' := hsub hs
      rw [← ENNReal.ofReal_mul (hw0 s hs'), ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (hw0 s hs') (hn0 s hs')) (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow]
    rw [hJeq, hJ t ht] at hH
    set J := ∫ s in (0 : ℝ)..t, w s ^ 4 * n s ^ 4 with hJdef
    have hkc : ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) ≤ ENNReal.ofReal c := by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact Real.rpow_le_rpow ht.1 (ht.2.trans (hT'.2.trans (le_max_left _ _))) (by norm_num)
    have h1 : ENNReal.ofReal (n t) ≤ ENNReal.ofReal A' + ENNReal.ofReal C' *
        (ENNReal.ofReal c ^ (3 / 4 : ℝ) * ENNReal.ofReal J ^ (1 / 4 : ℝ)) := by
      refine (hmild t ht).trans (add_le_add (ENNReal.ofReal_le_ofReal (le_max_left _ _)) ?_)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (hH.trans ?_)
      gcongr
    have h2 : ENNReal.ofReal (n t) ^ 4 ≤ 8 * (ENNReal.ofReal A' ^ 4 + (ENNReal.ofReal C' *
        (ENNReal.ofReal c ^ (3 / 4 : ℝ) * ENNReal.ofReal J ^ (1 / 4 : ℝ))) ^ 4) := by
      have e4 : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ 4 := fun x ↦ by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      have := ENNReal.rpow_add_le_mul_rpow_add_rpow (ENNReal.ofReal A') (ENNReal.ofReal C' *
        (ENNReal.ofReal c ^ (3 / 4 : ℝ) * ENNReal.ofReal J ^ (1 / 4 : ℝ))) (p := 4) (by norm_num)
      rw [e4, e4, e4] at this
      have h8 : (2 : ℝ≥0∞) ^ ((4 : ℝ) - 1) = 8 := by
        rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
        norm_num
      rw [h8] at this
      exact (pow_le_pow_left' h1 4).trans this
    have h3 : ENNReal.ofReal (n t ^ 4) ≤ ENNReal.ofReal (a + D * J) := by
      rw [ENNReal.ofReal_pow (hn0 t ht)]
      refine h2.trans (le_of_eq ?_)
      have hJ0 : 0 ≤ J := by
        rw [hJdef]
        refine intervalIntegral.integral_nonneg ht.1 (fun s hs ↦ ?_)
        have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans ht.2⟩
        exact mul_nonneg (pow_nonneg (hw0 s hs') _) (pow_nonneg (hn0 s hs') _)
      have eA : ENNReal.ofReal a = 8 * ENNReal.ofReal A' ^ 4 := by
        rw [ha, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hA0]
        norm_num
      have eD : ENNReal.ofReal D = 8 * ENNReal.ofReal C' ^ 4 * ENNReal.ofReal c ^ (3 : ℝ) := by
        rw [hD, ENNReal.ofReal_mul (mul_nonneg (by norm_num) (pow_nonneg hC0 _)),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hC0,
          ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num)]
        norm_num
      rw [ENNReal.ofReal_add ha0 (mul_nonneg hD0 hJ0), ENNReal.ofReal_mul hD0, eA, eD, mul_pow,
        mul_pow, rpow_pow_four, rpow_pow_four]
      norm_num
      ring
    have h4 := (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha0 (mul_nonneg hD0 (by
      rw [hJdef]
      refine intervalIntegral.integral_nonneg ht.1 (fun s hs ↦ ?_)
      have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans ht.2⟩
      exact mul_nonneg (pow_nonneg (hw0 s hs') _) (pow_nonneg (hn0 s hs') _))))).1 h3
    refine h4.trans (le_of_eq ?_)
    rw [hJdef, ← intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_congr (fun s _ ↦ by ring)
  have hgr := le_mul_exp_of_le_add_integral (a := a) (φ := fun s ↦ n s ^ 4)
      (b := fun s ↦ D * w s ^ 4) hT'0
    hφc hbc (fun t ht ↦ mul_nonneg hD0 (pow_nonneg (hw0 t ht) _)) hstep
  intro t ht
  have hwint : ∫ s in (0 : ℝ)..t, D * w s ^ 4 ≤ D * K' := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have hsub : Icc 0 t ⊆ Icc 0 T' := Icc_subset_Icc le_rfl ht.2
    have hint : IntegrableOn (fun s ↦ w s ^ 4) (Ioc 0 t) :=
      (((hw.pow 4).mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, w s ^ 4 := intervalIntegral.integral_nonneg ht.1
      (fun s hs ↦ pow_nonneg (hw0 s ⟨hs.1, hs.2.trans ht.2⟩) _)
    have hle : ENNReal.ofReal (∫ s in (0 : ℝ)..t, w s ^ 4) ≤ ENNReal.ofReal K' := by
      rw [intervalIntegral.integral_of_le ht.1, ofReal_integral_eq_lintegral_ofReal hint]
      · calc ∫⁻ s in Ioc 0 t, ENNReal.ofReal (w s ^ 4)
            ≤ ∫⁻ s in Icc 0 T', ENNReal.ofReal (w s ^ 4) :=
              lintegral_mono_set (Ioc_subset_Icc_self.trans hsub)
          _ ≤ ENNReal.ofReal K := hW
          _ ≤ ENNReal.ofReal K' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact pow_nonneg (hw0 s ⟨hs.1.le, hs.2.trans ht.2⟩) _
    exact (ENNReal.ofReal_le_ofReal_iff hK0).1 hle
  have h4 : n t ^ 4 ≤ a * Real.exp (D * K') :=
    (hgr t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hwint) ha0)
  by_cases h1 : n t ≤ 1
  · exact h1.trans (le_max_left _ _)
  · replace h1 := not_le.1 h1
    have : n t ≤ n t ^ 4 := by
      calc n t = n t ^ 1 := (pow_one _).symm
        _ ≤ n t ^ 4 := pow_le_pow_right₀ h1.le (by norm_num)
    exact this.trans (h4.trans (le_max_right _ _))

/-- If `H : ℝ → ℝ≥0∞` satisfies `H (σ + 1) = H σ` for all `σ`, then for every real `m`,
`∫⁻ σ in Icc m (m + 1), H σ = ∫⁻ σ in Icc 0 1, H σ`. Both sides are the integral of `H` over
the circle `ℝ / ℤ`. -/
theorem lintegral_Icc_add_one_eq_of_periodic {H : ℝ → ℝ≥0∞} (hH : ∀ σ, H (σ + 1) = H σ) (m : ℝ) :
    ∫⁻ σ in Icc m (m + 1), H σ = ∫⁻ σ in Icc 0 1, H σ := by
  have hp : Function.Periodic H 1 := hH
  have e : ∀ t : ℝ, ∫⁻ σ in Icc t (t + 1), H σ = ∫⁻ b : AddCircle (1 : ℝ), hp.lift b := by
    intro t
    rw [← AddCircle.lintegral_preimage 1 t, Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact lintegral_congr fun σ ↦ (hp.lift_coe σ).symm
  have e0 := e 0
  rw [zero_add] at e0
  rw [e m, e0]

/-- If `H : ℝ → ℝ≥0∞` satisfies `H (σ + 1) = H σ` for all `σ`, then
`∫⁻ σ in Icc (-(N : ℝ)) N, H σ ≤ 2 * N * ∫⁻ σ in Icc 0 1, H σ` for every natural number `N`. The
proof is by induction on `N`, covering `Icc (-(N + 1)) (N + 1)` by `Icc (-N) N` and two intervals of
length one. -/
theorem lintegral_Icc_nat_le_of_periodic {H : ℝ → ℝ≥0∞} (hH : ∀ σ, H (σ + 1) = H σ) (N : ℕ) :
    ∫⁻ σ in Icc (-(N : ℝ)) N, H σ ≤ 2 * (N : ℝ≥0∞) * ∫⁻ σ in Icc 0 1, H σ := by
  induction N with
  | zero =>
    have h0 : volume (Icc (-((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ)) = 0 := by simp
    rw [setLIntegral_measure_zero _ _ h0]
    positivity
  | succ N ih =>
    have hsub : Icc (-((N + 1 : ℕ) : ℝ)) ((N + 1 : ℕ) : ℝ) ⊆
        Icc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + 1) ∪ (Icc (-(N : ℝ)) N ∪ Icc (N : ℝ) (N + 1)) := by
      intro x hx
      push_cast at hx
      rcases le_or_gt x (-(N : ℝ)) with h | h
      · exact Or.inl ⟨by linarith [hx.1], by linarith⟩
      · rcases le_or_gt x N with h' | h'
        · exact Or.inr (Or.inl ⟨h.le, h'⟩)
        · exact Or.inr (Or.inr ⟨h'.le, by linarith [hx.2]⟩)
    calc ∫⁻ σ in Icc (-((N + 1 : ℕ) : ℝ)) ((N + 1 : ℕ) : ℝ), H σ
        ≤ ∫⁻ σ in Icc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + 1) ∪
            (Icc (-(N : ℝ)) N ∪ Icc (N : ℝ) (N + 1)), H σ := lintegral_mono_set hsub
      _ ≤ (∫⁻ σ in Icc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + 1), H σ) +
            ((∫⁻ σ in Icc (-(N : ℝ)) N, H σ) + ∫⁻ σ in Icc (N : ℝ) (N + 1), H σ) :=
          (lintegral_union_le _ _ _).trans (by
            gcongr
            exact lintegral_union_le _ _ _)
      _ ≤ (∫⁻ σ in Icc 0 1, H σ) + (2 * (N : ℝ≥0∞) * (∫⁻ σ in Icc 0 1, H σ) +
            ∫⁻ σ in Icc 0 1, H σ) := by
          rw [lintegral_Icc_add_one_eq_of_periodic hH (-(N : ℝ) - 1),
              lintegral_Icc_add_one_eq_of_periodic hH (N : ℝ)]
          gcongr
      _ = 2 * ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ σ in Icc 0 1, H σ := by
          push_cast
          ring

/-- If `h : ℝ → ℝ≥0∞` satisfies `h (s + 1) = h s` for all `s` and `∫⁻ s in Icc 0 1, h s < ⊤`, then
`∫⁻ s in Icc (-(M : ℝ)) M, h s < ⊤` for every natural number `M`. The proof covers `Icc (-M) M` by
finitely many intervals `Ioc k (k + 1)` with integer `k`, each carrying the same lower integral as
`Icc 0 1`. -/
theorem lintegral_Icc_nat_lt_top_of_periodic (h : ℝ → ℝ≥0∞) (hp : ∀ s, h (s + 1) = h s)
    (h0 : ∫⁻ s in Icc (0 : ℝ) 1, h s < ⊤) (M : ℕ) : ∫⁻ s in Icc (-(M : ℝ)) M, h s < ⊤ := by
  have hper : Function.Periodic h 1 := hp
  have hpiece : ∀ t : ℝ, ∫⁻ s in Ioc t (t + 1), h s = ∫⁻ s in Icc (0 : ℝ) 1, h s := by
    intro t
    have e1 := AddCircle.lintegral_preimage (T := 1) t (hper.lift)
    have e2 := AddCircle.lintegral_preimage (T := 1) 0 (hper.lift)
    simp only [Function.Periodic.lift_coe, zero_add] at e1 e2
    rw [e1, ← e2]
    exact setLIntegral_congr Ioc_ae_eq_Icc
  set S : Finset ℤ := Finset.Icc (-(M : ℤ) - 1) M
  have hsub : Icc (-(M : ℝ)) M ⊆ ⋃ k ∈ S, Ioc (k : ℝ) (k + 1) := by
    intro s hs
    rw [mem_iUnion₂]
    refine ⟨⌈s⌉ - 1, ?_, ?_⟩
    · have h1 : -(M : ℤ) ≤ ⌈s⌉ := Int.le_ceil_iff.2 (by push_cast; linarith [hs.1])
      have h2 : ⌈s⌉ ≤ (M : ℤ) := Int.ceil_le.2 (by exact_mod_cast hs.2)
      rw [Finset.mem_Icc]
      omega
    · push_cast
      exact ⟨by linarith [Int.ceil_lt_add_one s], by linarith [Int.le_ceil s]⟩
  calc ∫⁻ s in Icc (-(M : ℝ)) M, h s ≤ ∫⁻ s in ⋃ k ∈ S, Ioc (k : ℝ) (k + 1), h s :=
        lintegral_mono_set hsub
    _ = volume.withDensity h (⋃ k ∈ S, Ioc (k : ℝ) (k + 1)) :=
        (withDensity_apply _ (Finset.measurableSet_biUnion _ fun k _ ↦ measurableSet_Ioc)).symm
    _ ≤ ∑ k ∈ S, volume.withDensity h (Ioc (k : ℝ) (k + 1)) := measure_biUnion_finset_le _ _
    _ = ∑ k ∈ S, ∫⁻ s in Icc (0 : ℝ) 1, h s := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [withDensity_apply _ measurableSet_Ioc, hpiece]
    _ < ⊤ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h0

/-- If `q : ℝ → ℝ≥0∞` satisfies `q (σ + 1) = q σ` for all `σ`, then
`∫⁻ σ in Ioc k (k + 1), q σ = ∫⁻ σ in Icc 0 1, q σ` for every real `k`. No measurability of `q` is
assumed. -/
theorem lintegral_Ioc_add_one_eq_of_periodic (q : ℝ → ℝ≥0∞) (hq : ∀ σ, q (σ + 1) = q σ) (k : ℝ) :
    ∫⁻ σ in Set.Ioc k (k + 1), q σ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, q σ := by
  have hl : ∀ σ : ℝ, Function.Periodic.lift (c := (1 : ℝ)) (f := q) hq (σ : AddCircle (1 : ℝ)) =
      q σ :=
    fun σ ↦ Function.Periodic.lift_coe _ _
  have h1 := AddCircle.lintegral_preimage (T := (1 : ℝ)) k
      (Function.Periodic.lift (c := (1 : ℝ)) (f := q) hq)
  have h0 := AddCircle.lintegral_preimage (T := (1 : ℝ)) 0
      (Function.Periodic.lift (c := (1 : ℝ)) (f := q) hq)
  simp only [hl, zero_add] at h1 h0
  rw [h1, ← h0, Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- For a `1`-periodic `Φ : ℝ → ℝ≥0∞` and every real `c`, the lower integral over one period does
not depend on the starting point: `∫⁻ σ in Ioc c (c + 1), Φ σ = ∫⁻ σ in Icc 0 1, Φ σ`. No
measurability of `Φ` is assumed. -/
theorem lintegral_Ioc_periodic (Φ : ℝ → ℝ≥0∞) (hper : Function.Periodic Φ 1) (c : ℝ) :
    ∫⁻ σ in Set.Ioc c (c + 1), Φ σ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, Φ σ := by
  have e1 := AddCircle.lintegral_preimage (T := (1 : ℝ)) c hper.lift
  have e0 := AddCircle.lintegral_preimage (T := (1 : ℝ)) 0 hper.lift
  simp only [Function.Periodic.lift_coe, zero_add] at e1 e0
  rw [e1, ← e0, Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- Let `A Y K : ℝ → ℝ≥0∞` with `Y` and `K` almost everywhere measurable on `Icc 0 1`, let `M`, `X`,
`S` be nonnegative reals, and suppose `A σ ≤ ENNReal.ofReal M * (Y σ ^ (1 / 2 : ℝ) * K σ + Y σ)` for
almost every `σ`. If `∫⁻ σ in Icc 0 1, Y σ ≤ ENNReal.ofReal (X ^ 2)` and
`∫⁻ σ in Icc 0 1, K σ ^ (2 : ℝ) ≤ ENNReal.ofReal ((2 * S) ^ 2)`, then
`∫⁻ σ in Icc 0 1, A σ ≤ ENNReal.ofReal (2 * M * (X * S + X ^ 2))`. The proof integrates the
pointwise bound and applies Hölder's inequality with exponents `2` and `2` to the product
`Y σ ^ (1 / 2 : ℝ) * K σ`. -/
theorem lintegral_le_of_le_rpow_mul_add {A Y K : ℝ → ℝ≥0∞} {M X S : ℝ} (hM : 0 ≤ M) (hX : 0 ≤ X)
    (hS : 0 ≤ S)
    (hYm : AEMeasurable Y (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hKm : AEMeasurable K (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hpt : ∀ᵐ σ : ℝ, A σ ≤ ENNReal.ofReal M * (Y σ ^ (1 / 2 : ℝ) * K σ + Y σ))
    (hY : ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ ≤ ENNReal.ofReal (X ^ 2))
    (hK : ∫⁻ σ in Set.Icc (0 : ℝ) 1, K σ ^ (2 : ℝ) ≤ ENNReal.ofReal ((2 * S) ^ 2)) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, A σ ≤ ENNReal.ofReal (2 * M * (X * S + X ^ 2)) := by
  have hCst := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) 1))
    Real.HolderConjugate.two_two (hYm.pow_const (1 / 2 : ℝ)) hKm
  have hYY : ∫⁻ σ in Set.Icc (0 : ℝ) 1, (Y σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = ∫⁻ σ in Set.Icc (0 : ℝ) 1,
      Y σ :=
    lintegral_congr fun σ ↦ rpow_half_rpow_two (Y σ)
  have hprod : ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ ^ (1 / 2 : ℝ) * K σ ≤
      ENNReal.ofReal X * ENNReal.ofReal (2 * S) := by
    refine hCst.trans ?_
    rw [hYY]
    have h1 := rpow_half_le_of_le_ofReal_sq hX hY
    have h2 := rpow_half_le_of_le_ofReal_sq (by positivity) hK
    norm_num at h1 h2 ⊢
    exact mul_le_mul' h1 h2
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, A σ
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal M * (Y σ ^ (1 / 2 : ℝ) * K σ + Y σ) :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ENNReal.ofReal M * ((∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ ^ (1 / 2 : ℝ) * K σ) +
          ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right' _ hYm]
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal X * ENNReal.ofReal (2 * S) + ENNReal.ofReal (X ^ 2)) :=
        mul_le_mul' le_rfl (add_le_add hprod hY)
    _ ≤ _ := ofReal_mul_ofReal_mul_add_sq_le hM hX hS

/-- Minkowski's integral inequality with exponent `2`: for a sigma-finite measure `ν` on `β`, an
s-finite measure `μ` on `ℝ` and `h : ℝ → β → ℝ≥0∞` with `Function.uncurry h` almost everywhere
measurable for `μ.prod ν`,
`∫⁻ ξ, (∫⁻ s, h s ξ ∂μ) ^ 2 ∂ν ≤ (∫⁻ s, (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2`. The inner
integral is truncated to bounded functions supported on sets of finite measure, each truncation is
estimated with Tonelli's theorem and the Cauchy-Schwarz inequality, and monotone convergence gives
the limit. -/
theorem lintegral_sq_lintegral_le {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SigmaFinite ν] {μ : Measure ℝ} [SFinite μ] {h : ℝ → β → ℝ≥0∞}
    (hh : AEMeasurable (Function.uncurry h) (μ.prod ν)) :
    ∫⁻ ξ, (∫⁻ s, h s ξ ∂μ) ^ 2 ∂ν ≤ (∫⁻ s, (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
  set G : β → ℝ≥0∞ := fun ξ ↦ ∫⁻ s, h s ξ ∂μ with hGdef
  set R := ∫⁻ s, (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ with hRdef
  have hG : AEMeasurable G ν := hh.lintegral_prod_left'
  have hsec : ∀ᵐ s ∂μ, AEMeasurable (h s) ν := by
    filter_upwards [hh.aestronglyMeasurable.prodMk_left] with s hs using hs.aemeasurable
  set Φ : ℕ → β → ℝ≥0∞ := fun n ξ ↦
    (spanningSets ν n).indicator (fun ξ ↦ min (G ξ) (n : ℝ≥0∞)) ξ with hΦdef
  have hΦm : ∀ n, AEMeasurable (Φ n) ν := fun n ↦
    (hG.min aemeasurable_const).indicator (measurableSet_spanningSets ν n)
  have hΦG : ∀ n ξ, Φ n ξ ≤ G ξ := by
    intro n ξ
    by_cases hξ : ξ ∈ spanningSets ν n
    · simp only [hΦdef, Set.indicator_of_mem hξ]
      exact min_le_left _ _
    · simp [hΦdef, Set.indicator_of_notMem hξ]
  have hΦfin : ∀ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top (b := ∫⁻ ξ, (spanningSets ν n).indicator
      (fun _ ↦ ((n : ℝ≥0∞)) ^ 2) ξ ∂ν) ?_ (lintegral_mono fun ξ ↦ ?_)
    · rw [lintegral_indicator_const (measurableSet_spanningSets ν n)]
      exact ENNReal.mul_ne_top (by simp) (measure_spanningSets_lt_top ν n).ne
    · by_cases hξ : ξ ∈ spanningSets ν n
      · simp only [hΦdef, Set.indicator_of_mem hξ]
        gcongr
        exact min_le_right _ _
      · simp [hΦdef, Set.indicator_of_notMem hξ]
  have key : ∀ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≤ (∫⁻ ξ, Φ n ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) * R := by
    intro n
    calc ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≤ ∫⁻ ξ, Φ n ξ * G ξ ∂ν := lintegral_mono fun ξ ↦ by
          rw [sq]
          gcongr
          exact hΦG n ξ
      _ ≤ ∫⁻ ξ, ∫⁻ s, Φ n ξ * h s ξ ∂μ ∂ν := lintegral_mono fun ξ ↦ lintegral_const_mul_le _ _
      _ = ∫⁻ s, ∫⁻ ξ, Φ n ξ * h s ξ ∂ν ∂μ :=
          (lintegral_lintegral_swap (f := fun s ξ ↦ Φ n ξ * h s ξ)
            ((hΦm n).comp_snd.mul hh)).symm
      _ ≤ ∫⁻ s, (∫⁻ ξ, Φ n ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsec] with s hs
          have := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two (hΦm n) hs
          simp only [Pi.mul_apply, ENNReal.rpow_two] at this
          exact this
      _ = (∫⁻ ξ, Φ n ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) * R :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hΦfin n))
  have hle : ∀ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≤ R ^ 2 := by
    intro n
    set X := ∫⁻ ξ, Φ n ξ ^ 2 ∂ν with hXdef
    set y := X ^ (1 / 2 : ℝ) with hy
    have hsq : X = y ^ 2 := (rpow_half_sq X).symm
    have hX : y * y ≤ y * R := by
      rw [← sq, ← hsq]
      exact key n
    by_cases h0 : y = 0
    · rw [hsq, h0]
      simp
    · have htop : y ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hΦfin n)
      have hyR : y ≤ R := (ENNReal.mul_le_mul_iff_right h0 htop).mp hX
      rw [hsq]
      gcongr
  have hsup : ∀ ξ, G ξ ^ 2 = ⨆ n, Φ n ξ ^ 2 := by
    intro ξ
    rw [← ENNReal.iSup_pow]
    congr 1
    refine le_antisymm ?_ (iSup_le fun n ↦ hΦG n ξ)
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    set n := max N (spanningSetsIndex ν ξ)
    have hmem : ξ ∈ spanningSets ν n := mem_spanningSets_of_index_le ν ξ (le_max_right _ _)
    refine lt_iSup_iff.mpr ⟨n, ?_⟩
    simp only [hΦdef, Set.indicator_of_mem hmem]
    refine lt_min hc (hN.trans_le ?_)
    exact_mod_cast le_max_left _ _
  have hmono : ∀ ξ, Monotone fun n ↦ Φ n ξ ^ 2 := by
    intro ξ a b hab
    by_cases ha : ξ ∈ spanningSets ν a
    · have hb := monotone_spanningSets ν hab ha
      simp only [hΦdef, Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      gcongr
    · simp [hΦdef, Set.indicator_of_notMem ha]
  calc ∫⁻ ξ, G ξ ^ 2 ∂ν = ∫⁻ ξ, ⨆ n, Φ n ξ ^ 2 ∂ν := lintegral_congr fun ξ ↦ hsup ξ
    _ = ⨆ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν :=
        lintegral_iSup' (fun n ↦ (hΦm n).pow_const 2) (ae_of_all _ hmono)
    _ ≤ R ^ 2 := iSup_le hle

/-- For a `1`-periodic `Φ : ℝ → ℝ≥0∞`, every real `c` and every natural number `k`, the lower
integral over `k` consecutive periods is at most `k` times the lower integral over one period:
`∫⁻ s in Ioc c (c + k), Φ s ≤ k * ∫⁻ s in Icc 0 1, Φ s`. No measurability of `Φ` is assumed. The
proof is an induction on `k` that adds one period at a time. -/
theorem lintegral_Ioc_add_nat_le_of_periodic (Φ : ℝ → ℝ≥0∞) (hper : Function.Periodic Φ 1) (c : ℝ) :
    ∀ k : ℕ, ∫⁻ s in Set.Ioc c (c + k), Φ s ≤ k * ∫⁻ s in Set.Icc (0 : ℝ) 1, Φ s := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hu : Set.Ioc c (c + ((k + 1 : ℕ) : ℝ)) = Set.Ioc c (c + k) ∪
        Set.Ioc (c + k) (c + k + 1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by simp) (by linarith)]
      push_cast
      ring_nf
    rw [hu]
    refine (lintegral_union_le _ _ _).trans ?_
    rw [lintegral_Ioc_periodic Φ hper (c + k)]
    push_cast
    rw [add_mul, one_mul]
    gcongr

/-- For a sigma-finite measure `ν` on `β`, a set `S` of reals, a measurable weight `w : β → ℝ≥0∞`,
an almost everywhere measurable `a : β → ℝ≥0∞` and `g : ℝ → β → ℝ≥0∞` with `Function.uncurry g`
almost everywhere measurable for `(volume.restrict S).prod ν`,
`(∫⁻ ξ, w ξ * (a ξ + ∫⁻ s in S, g s ξ) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤ (∫⁻ ξ, w ξ * a ξ ^ 2 ∂ν) ^ (1 / 2 :
ℝ) + ∫⁻ s in S, (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ)`. The weight is absorbed as `w ^ (1 / 2 :
ℝ)`, then the triangle inequality in `L²` and Minkowski's integral inequality are applied. -/
theorem lintegral_weighted_add_lintegral_sq_le {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SigmaFinite ν] {S : Set ℝ} {w a : β → ℝ≥0∞}
    {g : ℝ → β → ℝ≥0∞} (hw : Measurable w) (ha : AEMeasurable a ν)
    (hg : AEMeasurable (Function.uncurry g) ((volume.restrict S).prod ν)) :
    (∫⁻ ξ, w ξ * (a ξ + ∫⁻ s in S, g s ξ) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      (∫⁻ ξ, w ξ * a ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) +
        ∫⁻ s in S, (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  set A : β → ℝ≥0∞ := fun ξ ↦ w ξ ^ (1 / 2 : ℝ) * a ξ with hAdef
  set h : ℝ → β → ℝ≥0∞ := fun s ξ ↦ w ξ ^ (1 / 2 : ℝ) * g s ξ with hhdef
  set H : β → ℝ≥0∞ := fun ξ ↦ ∫⁻ s in S, h s ξ with hHdef
  have hwm : Measurable fun ξ ↦ w ξ ^ (1 / 2 : ℝ) := hw.pow_const _
  have hA : AEMeasurable A ν := hwm.aemeasurable.mul ha
  have hh : AEMeasurable (Function.uncurry h) ((volume.restrict S).prod ν) :=
    (hwm.comp measurable_snd).aemeasurable.mul hg
  have hH : AEMeasurable H ν := hh.lintegral_prod_left'
  have hsq : ∀ x y : ℝ≥0∞, (x ^ (1 / 2 : ℝ) * y) ^ 2 = x * y ^ 2 := fun x y ↦ by
    rw [mul_pow, rpow_half_sq]
  have h1 : ∫⁻ ξ, w ξ * (a ξ + ∫⁻ s in S, g s ξ) ^ 2 ∂ν ≤ ∫⁻ ξ, (A ξ + H ξ) ^ 2 ∂ν := by
    refine lintegral_mono fun ξ ↦ ?_
    rw [← hsq, mul_add]
    gcongr
    exact lintegral_const_mul_le _ _
  have h2 := ENNReal.lintegral_Lp_add_le hA hH (p := 2) (by norm_num)
  simp only [Pi.add_apply, ENNReal.rpow_two] at h2
  have h3 : (∫⁻ ξ, H ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤ ∫⁻ s in S,
      (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    have := lintegral_sq_lintegral_le hh
    have e : ∀ s, ∫⁻ ξ, h s ξ ^ 2 ∂ν = ∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν := fun s ↦
      lintegral_congr fun ξ ↦ hsq _ _
    simp only [e] at this
    calc (∫⁻ ξ, H ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
        ((∫⁻ s in S, (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow this (by norm_num)
      _ = _ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  have e2 : ∫⁻ ξ, A ξ ^ 2 ∂ν = ∫⁻ ξ, w ξ * a ξ ^ 2 ∂ν := lintegral_congr fun ξ ↦ hsq _ _
  rw [e2] at h2
  calc _ ≤ (∫⁻ ξ, (A ξ + H ξ) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ ≤ _ := h2.trans (add_le_add le_rfl h3)

/-- If `Φ : ℝ → ℝ≥0∞` satisfies `Φ (σ + 1) = Φ σ` for all `σ`, then
`∫⁻ σ in Icc (-2) 3, Φ σ ≤ 5 * ∫⁻ σ in Icc 0 1, Φ σ`. No measurability of `Φ` is assumed. The proof
covers `Icc (-2) 3` by the five intervals `Icc k (k + 1)` with `k = -2, -1, 0, 1, 2` and moves each
of them to `Icc 0 1` by periodicity. -/
theorem setLIntegral_five_periods_le (Φ : ℝ → ℝ≥0∞) (hΦ : ∀ σ, Φ (σ + 1) = Φ σ) :
    ∫⁻ σ in Set.Icc (-2 : ℝ) 3, Φ σ ≤ 5 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, Φ σ := by
  have hsub : Set.Icc (-2 : ℝ) 3 ⊆ Set.Icc (-2) (-2 + 1) ∪ Set.Icc (-1) (-1 + 1) ∪
      Set.Icc 0 (0 + 1) ∪ Set.Icc 1 (1 + 1) ∪ Set.Icc 2 (2 + 1) := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hσ
    by_cases a : σ ≤ -1
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, by linarith⟩)))
    by_cases b : σ ≤ 0
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith⟩)))
    by_cases c : σ ≤ 1
    · exact Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith⟩))
    by_cases d : σ ≤ 2
    · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
  have e := lintegral_Icc_add_one_eq_of_periodic hΦ
  calc ∫⁻ σ in Set.Icc (-2 : ℝ) 3, Φ σ
      ≤ ∫⁻ σ in Set.Icc (-2) (-2 + 1) ∪ Set.Icc (-1) (-1 + 1) ∪
          Set.Icc 0 (0 + 1) ∪ Set.Icc 1 (1 + 1) ∪ Set.Icc 2 (2 + 1), Φ σ := lintegral_mono_set hsub
    _ ≤ (∫⁻ σ in Set.Icc (-2 : ℝ) (-2 + 1), Φ σ) + (∫⁻ σ in Set.Icc (-1 : ℝ) (-1 + 1), Φ σ) +
          (∫⁻ σ in Set.Icc (0 : ℝ) (0 + 1), Φ σ) + (∫⁻ σ in Set.Icc (1 : ℝ) (1 + 1), Φ σ) +
          (∫⁻ σ in Set.Icc (2 : ℝ) (2 + 1), Φ σ) := by
        refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
        refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
        refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
        exact lintegral_union_le _ _ _
    _ = 5 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, Φ σ := by
        rw [e, e, e, e, e]
        ring

/-- For `h : ℝ → ℝ≥0∞` of period one and every real `τ`,
`∫⁻ σ in Icc 0 1, h (σ + τ) = ∫⁻ σ in Icc 0 1, h σ`. Both sides are the integral of `h` over
the circle `ℝ / ℤ`. -/
theorem lintegral_Icc_comp_add_of_periodic (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h 1) (τ : ℝ) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, h (σ + τ) = ∫⁻ σ in Set.Icc (0 : ℝ) 1, h σ := by
  rw [← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    ← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1))]
  have hpre : (fun σ : ℝ ↦ σ + τ) ⁻¹' Set.Ioc τ (τ + 1) = Set.Ioc 0 1 := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hmp := measurePreserving_add_right (volume : Measure ℝ) τ
  have h1 := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight τ) h
      (Set.Ioc τ (τ + 1))
  rw [hpre] at h1
  rw [h1]
  have hl : ∀ t : ℝ, ∫⁻ σ in Set.Ioc t (t + 1), h σ = ∫⁻ b : UnitAddCircle, hp.lift b := by
    intro t
    rw [← UnitAddCircle.lintegral_preimage t]
    rfl
  have h0 := hl 0
  rw [zero_add] at h0
  rw [hl τ, h0]

/-- For a.e. measurable `A, B : X → ℝ≥0∞` on a measure space with measure `μ`,
`(∫⁻ x, A x * B x ∂μ) ^ 2 ≤ (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ`. By Hölder's inequality
with exponents two for the factors `A ^ (1 / 2)` and `A ^ (1 / 2) * B`. -/
theorem sq_lintegral_mul_le_lintegral_mul_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A B : X → ℝ≥0∞}
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) :
    (∫⁻ x, A x * B x ∂μ) ^ 2 ≤ (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x ↦ A x ^ (1 / 2 : ℝ)) (g := fun x ↦ A x ^ (1 / 2 : ℝ) * B x) (hA.pow_const _)
    ((hA.pow_const _).mul hB)
  have e1 : ∀ x, A x ^ (1 / 2 : ℝ) * (A x ^ (1 / 2 : ℝ) * B x) = A x * B x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (A x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = A x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (A x ^ (1 / 2 : ℝ) * B x) ^ (2 : ℝ) = A x * B x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ENNReal.rpow_two]
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x ∂μ) ^ 2
      ≤ ((∫⁻ x, A x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, A x * B x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- For an a.e. measurable `h : α → ℝ≥0∞` on a measure space with measure `μ`,
`(∫⁻ x, h x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, h x ^ 2 ∂μ`. By Hölder's inequality with exponents two
for the constant function one and `h`. -/
theorem sq_lintegral_le_measure_mul_lintegral_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {h : α → ENNReal}
    (hh : AEMeasurable h μ) :
    (∫⁻ x, h x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, h x ^ 2 ∂μ := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two aemeasurable_const hh
    (f := fun _ ↦ (1 : ENNReal))
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at H
  have H2 := pow_le_pow_left₀ zero_le H 2
  refine H2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast
      (((∫⁻ a, h a ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)))),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

end PDE.Analysis

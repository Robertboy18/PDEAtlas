/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.Analysis.Evolution.Time.Euclidean
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Banach-valued mollification in time

For a Banach space `X` and a locally integrable trajectory `f : ℝ → X`, the mollification
`(η_ε * f)(t) = ∫ η_ε(t - s) f(s) ds` with a standard one-dimensional mollifier `η` is
smooth, converges to `f(t)` at every point of continuity of `f`, and converges to `f` in
`L^p(ℝ; X)` for `1 ≤ p < ∞`. These are the vector-valued versions of the standard facts
about mollifiers (Evans, Appendix C.5, Theorem 7); Evans mollifies Banach-valued functions
of time in the proofs of §5.9.2, Theorems 2 and 3. Here they are
stated for ordinary functions `ℝ → X`: the trajectory is transported to `ℝ^1`, the
Euclidean mollifier `SobolevSpace.Approximation.mollifyVector` is applied, and the result
is transported back, so the statements involve only functions on `ℝ`.

The `L^p` approximate-identity theorem is the regularisation step of the Lions–Magenes
argument: a trajectory `u ∈ L²(ℝ; V)` with weak derivative `u' ∈ L²(ℝ; V*)` is replaced by
smooth `u_ε = η_ε * u` with `u_ε' = η_ε * u'`, the energy identity is proved for `u_ε` by
the classical product rule, and the identity is carried to `u` in the limit. Extracting an
a.e.-convergent subsequence gives a time at which the regularised trajectories converge
in `H`.

## Main results

* `timeMollify`, `regularizeTime`: mollification with an arbitrary one-dimensional
  mollifier `μ`, and with the canonical normalised one.
* `timeMollify_contDiff`, `regularizeTime_contDiff`: smoothness for `ε > 0`.
* `timeMollify_tendsto_of_continuous`, `_of_continuousAt` and the `regularizeTime`
  versions: pointwise convergence along any sequence `ε_m → 0⁺`.
* `timeMollify_memLp`, `timeMollify_converges_Lp`, `regularizeTime_tendsto_toLp`:
  boundedness on `L^p` and the approximate-identity theorem, for `1 ≤ p < ∞`, also in the
  bundled `Lp` space.
* `exists_subsequence_regularizeTime_tendsto_ae`: a subsequence converging a.e.
* `regularizeTime_memLp_monoMeasure`, `regularizeTime_tendsto_toLp_monoMeasure`,
  `regularizeTime_intervalIntegral_tendsto`: the same on restricted measures and after
  integration over finite intervals.
* `map_mollifyVector`, `map_timeMollify`, `map_regularizeTime`: bounded linear maps
  commute with mollification, the naturality needed to mollify `u` and `u'` compatibly
  through the Gelfand-triple maps.

## Implementation notes

The scale is a sequence `ε : ℕ → ℝ` of positive numbers tending to `0`, rather than a
filter statement in `ε`, because the a.e.-subsequence extraction is stated for sequences.
Measurability hypotheses `[MeasurableSpace X] [BorelSpace X]` are needed for the `L^p`
statements only; the pointwise and smoothness results are free of them.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.5, Theorem 7, and §5.9.2, proofs of Theorems 2 and
  3. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

open SobolevSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Convolution in the time variable by a standard one-dimensional
mollifier.  The input and output are ordinary Banach-valued functions on
`ℝ`; no Euclidean-coordinate wrapper appears in the public type. -/
def timeMollify
    (μ : SobolevSpace.Approximation.Mollifier 1) (ε : ℝ)
    (f : ℝ → X) : ℝ → X :=
  fun t ↦
    SobolevSpace.Approximation.mollifyVector μ ε
      (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)))
      ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)

/-- The canonical time regularization used by the parabolic theory.  It uses
LeanPDE's normalized standard one-dimensional mollifier. -/
def regularizeTime (ε : ℝ) (f : ℝ → X) : ℝ → X :=
  timeMollify (SobolevSpace.Approximation.standardMollifier 1) ε f

/-- Positive-scale time mollification is smooth. -/
theorem timeMollify_contDiff
    (μ : SobolevSpace.Approximation.Mollifier 1) {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → X) (hf : LocallyIntegrable f (volume : Measure ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (timeMollify μ ε f) := by
  have hpull := locallyIntegrable_comp_oneDimensionalEquiv_symm f hf
  have hsmooth := SobolevSpace.Approximation.mollifyVector_contDiff_of_pos
    (μ := μ) (ε := ε) hε
    (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) hpull
  change ContDiff ℝ (⊤ : ℕ∞)
    (SobolevSpace.Approximation.mollifyVector μ ε
      (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) ∘
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm)
  exact hsmooth.comp
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.contDiff

/-- Canonical positive-scale time regularization is smooth. -/
theorem regularizeTime_contDiff
    {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → X) (hf : LocallyIntegrable f (volume : Measure ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizeTime ε f) := by
  exact timeMollify_contDiff
    (SobolevSpace.Approximation.standardMollifier 1) hε f hf

/-- Global continuity gives pointwise convergence everywhere. -/
theorem timeMollify_tendsto_of_continuous
    [CompleteSpace X]
    (μ : SobolevSpace.Approximation.Mollifier 1) {f : ℝ → X}
    (hf : Continuous f) (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun m ↦ timeMollify μ (ε m) f t) atTop (𝓝 (f t)) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hpull : Continuous (f ∘ e.symm) := hf.comp e.symm.continuous
  change Tendsto
    (fun m ↦ SobolevSpace.Approximation.mollifyVector μ (ε m)
      (f ∘ e.symm) (e t)) atTop (𝓝 (f t))
  have heval : (f ∘ e.symm) (e t) = f t :=
    congrArg f (e.symm_apply_apply t)
  rw [← heval]
  exact SobolevSpace.Approximation.mollifyVector_tendsto_of_continuous
    (μ := μ) (f := f ∘ e.symm) hpull ε hεpos hε0 (e t)

/-- Canonical time regularization converges pointwise to every continuous
Banach-valued trajectory as its positive scale tends to zero. -/
theorem regularizeTime_tendsto_of_continuous
    [CompleteSpace X] {f : ℝ → X} (hf : Continuous f)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun m ↦ regularizeTime (ε m) f t) atTop (𝓝 (f t)) := by
  exact timeMollify_tendsto_of_continuous
    (SobolevSpace.Approximation.standardMollifier 1) hf ε hεpos hε0 t

/-- Time mollification converges at a single point of continuity; no
continuity away from that point is required. -/
theorem timeMollify_tendsto_of_continuousAt
    [CompleteSpace X]
    (μ : SobolevSpace.Approximation.Mollifier 1) {f : ℝ → X}
    (hf_loc : LocallyIntegrable f (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) {t : ℝ}
    (hf : ContinuousAt f t) :
    Tendsto (fun m ↦ timeMollify μ (ε m) f t) atTop (𝓝 (f t)) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hpull := locallyIntegrable_comp_oneDimensionalEquiv_symm f hf_loc
  have hpullAt : ContinuousAt (f ∘ e.symm) (e t) := by
    simpa [Function.comp_def] using
      hf.comp_of_eq e.symm.continuousAt (e.symm_apply_apply t)
  change Tendsto
    (fun m ↦ SobolevSpace.Approximation.mollifyVector μ (ε m)
      (f ∘ e.symm) (e t)) atTop (𝓝 (f t))
  have heval : (f ∘ e.symm) (e t) = f t :=
    congrArg f (e.symm_apply_apply t)
  rw [← heval]
  exact SobolevSpace.Approximation.mollifyVector_tendsto_of_continuousAt
    (μ := μ) hpull ε hεpos hε0 hpullAt

/-- Canonical time regularization converges at every point of continuity. -/
theorem regularizeTime_tendsto_of_continuousAt
    [CompleteSpace X] {f : ℝ → X}
    (hf_loc : LocallyIntegrable f (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) {t : ℝ}
    (hf : ContinuousAt f t) :
    Tendsto (fun m ↦ regularizeTime (ε m) f t) atTop (𝓝 (f t)) :=
  timeMollify_tendsto_of_continuousAt
    (SobolevSpace.Approximation.standardMollifier 1)
    hf_loc ε hεpos hε0 hf

/-- Banach-valued time mollification is an approximate identity in `L^p(ℝ; X)`
for `1 ≤ p < ∞`.  This is the time-regularization convergence used in the
Lions–Magenes argument; continuity of the original trajectory is not
assumed. -/
theorem timeMollify_converges_Lp
    [MeasurableSpace X] [CompleteSpace X]
    (μ : SobolevSpace.Approximation.Mollifier 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ → X} (hf : MemLp f p (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun m ↦ eLpNorm (fun t ↦ timeMollify μ (ε m) f t - f t) p
        (volume : Measure ℝ))
      atTop (𝓝 0) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hmp : MeasurePreserving e.symm
      (volume : Measure (ℝ^1)) (volume : Measure ℝ) :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  have hpull : MemLp (f ∘ e.symm) p (volume : Measure (ℝ^1)) :=
    hf.comp_measurePreserving hmp
  have hconv := SobolevSpace.Approximation.mollifyVector_converges_Lp
    (μ := μ) (p := p) hp ε hεpos hε0 hpull
  have hf_loc : LocallyIntegrable f (volume : Measure ℝ) :=
    hf.locallyIntegrable (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have heq : ∀ m,
      eLpNorm (fun t ↦ timeMollify μ (ε m) f t - f t) p (volume : Measure ℝ) =
        eLpNorm
          (fun x ↦ SobolevSpace.Approximation.mollifyVector μ (ε m) (f ∘ e.symm) x -
            (f ∘ e.symm) x)
          p (volume : Measure (ℝ^1)) := by
    intro m
    let g : ℝ → X := fun t ↦ timeMollify μ (ε m) f t - f t
    have hg : AEStronglyMeasurable g (volume : Measure ℝ) :=
      (timeMollify_contDiff μ (hεpos m) f hf_loc).continuous.aestronglyMeasurable.sub
        hf.aestronglyMeasurable
    have htransport := eLpNorm_comp_measurePreserving (p := p) hg hmp
    have hfun : g ∘ e.symm =
        fun x ↦ SobolevSpace.Approximation.mollifyVector μ (ε m) (f ∘ e.symm) x -
          (f ∘ e.symm) x := by
      funext x
      change
        SobolevSpace.Approximation.mollifyVector μ (ε m) (f ∘ e.symm)
            (e (e.symm x)) - f (e.symm x) =
          SobolevSpace.Approximation.mollifyVector μ (ε m) (f ∘ e.symm) x -
            f (e.symm x)
      rw [e.apply_symm_apply]
    rw [hfun] at htransport
    exact htransport.symm
  simpa only [heq] using hconv

/-- The canonical time regularization converges in `L^p(ℝ; X)` for every
`1 ≤ p < ∞`. -/
theorem regularizeTime_converges_Lp
    [CompleteSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ → X} (hf : MemLp f p (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun m ↦ eLpNorm (fun t ↦ regularizeTime (ε m) f t - f t) p
        (volume : Measure ℝ))
      atTop (𝓝 0) := by
  -- the statement is topological; the proof uses the Borel structure of `X`
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  exact timeMollify_converges_Lp
    (SobolevSpace.Approximation.standardMollifier 1) p hp hf ε hεpos hε0

/-- Time mollification preserves global `L^p` membership.  The proof
transports the Banach-valued contraction theorem through the canonical
measure-preserving identification `ℝ ≃ ℝ^1`. -/
theorem timeMollify_memLp
    [MeasurableSpace X]
    (μ : SobolevSpace.Approximation.Mollifier 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → X}
    (hf : MemLp f p (volume : Measure ℝ)) :
    MemLp (timeMollify μ ε f) p (volume : Measure ℝ) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hpull : MemLp (f ∘ e.symm) p (volume : Measure (ℝ^1)) :=
    hf.comp_measurePreserving
      (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
        ((PiLp.volume_preserving_toLp (Fin 1)).comp
          ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)))
  have hbound := SobolevSpace.Approximation.MollifyLp.eLpNorm_mollifyVector_le
    (n := 1) (p := p) (μ := μ) hε hp hpull
  have hmollified : MemLp
      (SobolevSpace.Approximation.mollifyVector μ ε (f ∘ e.symm)) p
      (volume : Measure (ℝ^1)) :=
    lt_of_le_of_lt hbound hpull
  have htransport := hmollified.comp_measurePreserving
    ((PiLp.volume_preserving_toLp (Fin 1)).comp
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  change MemLp
    (SobolevSpace.Approximation.mollifyVector μ ε (f ∘ e.symm) ∘ e)
      p (volume : Measure ℝ)
  exact htransport

/-- Canonical time regularization preserves global `L^p` membership. -/
theorem regularizeTime_memLp
    [MeasurableSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → X}
    (hf : MemLp f p (volume : Measure ℝ)) :
    MemLp (regularizeTime ε f) p (volume : Measure ℝ) :=
  timeMollify_memLp (SobolevSpace.Approximation.standardMollifier 1)
    p hp hε hf

/-- The approximate-identity theorem as convergence in the bundled Bochner
`L^p` space.  This is the form consumed by Hilbert-space duality. -/
theorem regularizeTime_tendsto_toLp
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ → X} (hf : MemLp f p (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun m ↦ (regularizeTime_memLp p hp (hεpos m) hf).toLp
        (regularizeTime (ε m) f)) atTop
      (𝓝 (hf.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (f := fun m ↦ regularizeTime (ε m) f)
    (f_ℒp := fun m ↦ regularizeTime_memLp p hp (hεpos m) hf)
    (f_lim := f) (f_lim_ℒp := hf)).2
  exact regularizeTime_converges_Lp p hp hf ε hεpos hε0

/-- Every `L^p`-convergent time-regularization sequence has a subsequence
that converges pointwise almost everywhere to the original representative.

This is the measure-theoretic step of the Lions–Magenes argument:
one may choose an ordinary time at which the regularized trajectories
converge in the ambient Banach space, and then propagate convergence to the
whole compact interval with the energy identity. -/
theorem exists_subsequence_regularizeTime_tendsto_ae
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ → X} (hf : MemLp f p (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ t ∂(volume : Measure ℝ),
        Tendsto (fun m ↦ regularizeTime (ε (ns m)) f t) atTop (𝓝 (f t)) := by
  let F : ℕ → Lp X p (volume : Measure ℝ) := fun m ↦
    (regularizeTime_memLp p hp (hεpos m) hf).toLp
      (regularizeTime (ε m) f)
  let fLp : Lp X p (volume : Measure ℝ) := hf.toLp f
  have hLp : Tendsto F atTop (𝓝 fLp) :=
    regularizeTime_tendsto_toLp p hp hf ε hεpos hε0
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hregularized : ∀ᵐ t ∂(volume : Measure ℝ), ∀ m,
      F m t = regularizeTime (ε m) f t := by
    rw [ae_all_iff]
    intro m
    exact (regularizeTime_memLp p hp (hεpos m) hf).coeFn_toLp
  have horiginal : ∀ᵐ t ∂(volume : Measure ℝ), fLp t = f t :=
    hf.coeFn_toLp
  filter_upwards [hpoint, hregularized, horiginal] with t ht hreg horig
  rw [← horig]
  exact ht.congr' (Filter.Eventually.of_forall fun m ↦ hreg (ns m))

/-- Restricting the time measure preserves membership of every regularized
trajectory. -/
theorem regularizeTime_memLp_monoMeasure
    [MeasurableSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {ν : Measure ℝ} (hν : ν ≤ volume)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → X}
    (hf : MemLp f p (volume : Measure ℝ)) :
    MemLp (regularizeTime ε f) p ν :=
  (regularizeTime_memLp p hp hε hf).mono_measure hν

/-- Global `L^p` convergence of time regularization remains valid for every
smaller measure.  In particular this supplies convergence on arbitrary
finite time intervals without extending interval equivalence classes by
hand. -/
theorem regularizeTime_tendsto_toLp_monoMeasure
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {ν : Measure ℝ} (hν : ν ≤ volume)
    {f : ℝ → X} (hf : MemLp f p (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun m ↦ (regularizeTime_memLp_monoMeasure p hp hν (hεpos m) hf).toLp
        (regularizeTime (ε m) f)) atTop
      (𝓝 ((hf.mono_measure hν).toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (f := fun m ↦ regularizeTime (ε m) f)
    (f_ℒp := fun m ↦
      regularizeTime_memLp_monoMeasure p hp hν (hεpos m) hf)
    (f_lim := f) (f_lim_ℒp := hf.mono_measure hν)).2
  have hglobal := regularizeTime_converges_Lp p hp hf ε hεpos hε0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
    (fun _ ↦ bot_le)
    (fun m ↦
      eLpNorm_mono_measure
        (fun t ↦ regularizeTime (ε m) f t - f t) hν)

/-- Time regularization converges after Bochner integration over every
finite interval.  The proof uses `L²(I) → L¹(I)` on the finite interval and
continuity of the Bochner integral. -/
theorem regularizeTime_intervalIntegral_tendsto
    [MeasurableSpace X] [CompleteSpace X]
    {f : ℝ → X} (hf : MemLp f 2 (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (a b : ℝ) :
    Tendsto (fun m ↦ ∫ t in a..b, regularizeTime (ε m) f t) atTop
      (𝓝 (∫ t in a..b, f t)) := by
  let ν : Measure ℝ := volume.restrict (Set.uIoc a b)
  let : IsFiniteMeasure ν := ⟨by simp [ν]⟩
  have hconv2 : Tendsto
      (fun m ↦ eLpNorm
        (fun t ↦ regularizeTime (ε m) f t - f t) 2 ν)
      atTop (𝓝 0) := by
    have hglobal := regularizeTime_converges_Lp
      2 (by norm_num) hf ε hεpos hε0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
      (fun _ ↦ bot_le)
      (fun m ↦ eLpNorm_mono_measure
        (fun t ↦ regularizeTime (ε m) f t - f t) Measure.restrict_le_self)
  let C : ℝ≥0∞ := ν Set.univ ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hconvBound : Tendsto
      (fun m ↦ eLpNorm
        (fun t ↦ regularizeTime (ε m) f t - f t) 2 ν * C)
      atTop (𝓝 0) := by
    have hCtop : C ≠ ∞ := by
      apply ENNReal.rpow_ne_top_of_nonneg
      · norm_num
      · exact (measure_lt_top ν Set.univ).ne
    simpa using ENNReal.Tendsto.mul_const hconv2 (Or.inr hCtop)
  have hconv1 : Tendsto
      (fun m ↦ eLpNorm
        (fun t ↦ regularizeTime (ε m) f t - f t) 1 ν)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconvBound
    · exact fun _ ↦ bot_le
    · intro m
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
        (((regularizeTime_memLp 2 (by norm_num) (hεpos m) hf).aestronglyMeasurable.sub
          hf.aestronglyMeasurable).mono_measure
          Measure.restrict_le_self)
  have hregInt (m : ℕ) : Integrable (regularizeTime (ε m) f) ν :=
    (regularizeTime_memLp_monoMeasure
      2 (by norm_num) Measure.restrict_le_self (hεpos m) hf).integrable
      (by norm_num)
  have hraw := tendsto_setIntegral_of_L1'
    (μ := ν) (f := f)
    (F := fun m ↦ regularizeTime (ε m) f)
    (Eventually.of_forall hregInt) hconv1 Set.univ
  have hrestricted : Tendsto
      (fun m ↦ ∫ t, regularizeTime (ε m) f t ∂ν) atTop
      (𝓝 (∫ t, f t ∂ν)) := by
    simpa only [Measure.restrict_univ] using hraw
  let c : ℝ := if a ≤ b then 1 else -1
  have hc : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
  have horiented := hc.smul hrestricted
  simpa [c, ν, intervalIntegral.intervalIntegral_eq_integral_uIoc] using horiented

/-! ## Commutation with continuous linear maps -/

/-- Continuous linear maps commute with Banach-valued mollification.  This
is the vector-valued Bochner naturality statement behind all scalarization
and Gelfand-triple applications below. -/
theorem map_mollifyVector
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (μ : SobolevSpace.Approximation.Mollifier 1)
    {ε : ℝ} (hε : 0 < ε) (f : ℝ^1 → X)
    (hf : LocallyIntegrable f (volume : Measure (ℝ^1))) (x : ℝ^1) :
    L (SobolevSpace.Approximation.mollifyVector μ ε f x) =
      SobolevSpace.Approximation.mollifyVector μ ε (L ∘ f) x := by
  have hcs : HasCompactSupport (SobolevSpace.Approximation.scaled μ ε) :=
    SobolevSpace.Approximation.scaled_hasCompactSupport μ hε
  have hcont : Continuous (SobolevSpace.Approximation.scaled μ ε) :=
    (SobolevSpace.Approximation.scaled_contDiff μ).continuous
  have hex := hcs.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (ℝ^1))) hcont hf
  have hint : Integrable
      (fun y : ℝ^1 ↦ SobolevSpace.Approximation.scaled μ ε y • f (x - y))
      (volume : Measure (ℝ^1)) := hex x
  calc
    L (SobolevSpace.Approximation.mollifyVector μ ε f x) =
        L (∫ y : ℝ^1, SobolevSpace.Approximation.scaled μ ε y • f (x - y)
          ∂(volume : Measure (ℝ^1))) := by
            rfl
    _ = ∫ y : ℝ^1,
          L (SobolevSpace.Approximation.scaled μ ε y • f (x - y))
          ∂(volume : Measure (ℝ^1)) := by
            exact (L.integral_comp_comm hint).symm
    _ = SobolevSpace.Approximation.mollifyVector μ ε (L ∘ f) x := by
          simp [SobolevSpace.Approximation.mollifyVector,
            MeasureTheory.convolution]

/-- Continuous linear maps also commute with the public time-coordinate
wrapper. -/
theorem map_timeMollify
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (μ : SobolevSpace.Approximation.Mollifier 1)
    {ε : ℝ} (hε : 0 < ε) (f : ℝ → X)
    (hf : LocallyIntegrable f (volume : Measure ℝ)) (t : ℝ) :
    L (timeMollify μ ε f t) = timeMollify μ ε (L ∘ f) t := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hfE : LocallyIntegrable (f ∘ e.symm)
      (volume : Measure (ℝ^1)) :=
    locallyIntegrable_comp_oneDimensionalEquiv_symm f hf
  simpa [timeMollify, e, Function.comp_def] using
    map_mollifyVector L μ hε (f ∘ e.symm) hfE (e t)

/-- Continuous linear maps commute with canonical time regularization. -/
theorem map_regularizeTime
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℝ] Y) {ε : ℝ} (hε : 0 < ε) (f : ℝ → X)
    (hf : LocallyIntegrable f (volume : Measure ℝ)) (t : ℝ) :
    L (regularizeTime ε f t) = regularizeTime ε (L ∘ f) t := by
  exact map_timeMollify L
    (SobolevSpace.Approximation.standardMollifier 1) hε f hf t

end PDE.Analysis.Evolution

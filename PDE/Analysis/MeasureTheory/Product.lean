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

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option linter.style.header false

/-!
# Product measures and slices

The lemmas write an integral over a product as an iterated integral, exchange the order of
integration, and state measurability and integrability of slices. The proofs use `integral_prod`,
`MeasureTheory.Integrable.prod_left_ae` and Tonelli's theorem as Mathlib states it.

## Main results

* `PDE.Analysis.restrict_Icc_prod_le_restrict_Ioi_prod`: For all real `R`, `Z`, Lebesgue measure on
  `ℝ × ℝ` restricted to `Icc 0 R ×ˢ Icc (-Z) Z` is at most Lebesgue measure restricted to
  `Ioi 0 ×ˢ univ`. The rectangle lies in `Ici 0 ×ˢ univ`, which agrees with `Ioi 0 ×ˢ univ` up to a
  null set.
* `PDE.Analysis.volume_restrict_Icc_prod_Icc_eq_prod`: For all real `a b c d`, Lebesgue measure on
  `ℝ × ℝ` restricted to `Icc a b ×ˢ Icc c d` equals the product of Lebesgue measure restricted to
  `Icc a b` and Lebesgue measure restricted to `Icc c d`.
* `PDE.Analysis.integrableOn_Icc_prod_left_ae`: Let `E` be a normed additive commutative group. If
  `f : ℝ × ℝ → E` is integrable on `Icc a b ×ˢ Icc c d`, then for almost every `z` in `Icc c d` the
  function `fun r ↦ f (r, z)` is integrable on `Icc a b`.
* `PDE.Analysis.setIntegral_Icc_prod_eq_zero_of_contDiff`: Let `Φ : ℝ × ℝ → ℂ` be integrable on
  `Icc lo hi ×ˢ t`. If `∫ p in Icc lo hi ×ˢ t, (χ p.1 : ℂ) * Φ p = 0` for every smooth compactly
  supported `χ : ℝ → ℝ` with `tsupport χ ⊆ Ioo lo hi`, then `∫ p in Icc lo hi ×ˢ t, Φ p = 0`.
* `PDE.Analysis.volume_prod_restrict_right`: For a set `s` of reals, the product of Lebesgue measure
  on `ℝ × ℝ` with Lebesgue measure on `ℝ` restricted to `s` equals the product measure
  `volume.prod volume` on `(ℝ × ℝ) × ℝ` restricted to `univ ×ˢ s`.
* `PDE.Analysis.ae_aemeasurable_slice`: Let `ν` be a measure on `β` and `ρ` an s-finite measure on
  `γ`, and let `g : β → γ → ℝ≥0∞`. If `z ↦ g z.1 z.2` is almost everywhere measurable for
  `ν.prod ρ`, then for `ν`-almost every `s` the slice `g s` is almost everywhere measurable for `ρ`.
* `PDE.Analysis.ae_aemeasurable_slice_real`: Let `ν` be a measure on `β` and `ρ` an s-finite measure
  on `γ`, and let `g : β → γ → ℝ`. If `z ↦ g z.1 z.2` is almost everywhere measurable for
  `ν.prod ρ`, then for `ν`-almost every `s` the slice `g s` is almost everywhere measurable for `ρ`.
* `PDE.Analysis.ae_eq_of_ae_slices`: Let `μ` be a measure on `α`, `ν` an s-finite measure on `β`,
  and `f g : α × β → E` almost everywhere strongly measurable for `μ.prod ν`, with `E` a metrizable
  topological space. If for `μ`-almost every `x` the equality `f (x, y) = g (x, y)` holds for
  `ν`-almost every `y`, then `f z = g z` for `μ.prod ν`-almost every `z`.

There are 14 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace PDE.Analysis

/-- Let `ν` be a measure on `β` and `ρ` an s-finite measure on `γ`, and let `g : β → γ → ℝ≥0∞`. If
`z ↦ g z.1 z.2` is almost everywhere measurable for `ν.prod ρ`, then for `ν`-almost every `s` the
slice `g s` is almost everywhere measurable for `ρ`. -/
theorem ae_aemeasurable_slice {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure β} {ρ : Measure γ} [SFinite ρ] {g : β → γ → ℝ≥0∞}
    (hg : AEMeasurable (fun z : β × γ ↦ g z.1 z.2) (ν.prod ρ)) :
    ∀ᵐ s ∂ν, AEMeasurable (g s) ρ := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  filter_upwards [Measure.ae_ae_of_ae_prod hgg'] with s hs
  exact ⟨fun x ↦ g' (s, x), hg'm.comp measurable_prodMk_left, hs⟩

/-- Let `ν` be a measure on `β` and `ρ` an s-finite measure on `γ`, and let `g : β → γ → ℝ`. If
`z ↦ g z.1 z.2` is almost everywhere measurable for `ν.prod ρ`, then for `ν`-almost every `s` the
slice `g s` is almost everywhere measurable for `ρ`. -/
theorem ae_aemeasurable_slice_real {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure β} {ρ : Measure γ} [SFinite ρ] {g : β → γ → ℝ}
    (hg : AEMeasurable (fun z : β × γ ↦ g z.1 z.2) (ν.prod ρ)) :
    ∀ᵐ s ∂ν, AEMeasurable (g s) ρ := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  filter_upwards [Measure.ae_ae_of_ae_prod hgg'] with s hs
  exact ⟨fun x ↦ g' (s, x), hg'm.comp measurable_prodMk_left, hs⟩

/-- Let `μ` be a measure on `α`, `ν` an s-finite measure on `β`, and `f g : α × β → E` almost
everywhere strongly measurable for `μ.prod ν`, with `E` a metrizable topological space. If for
`μ`-almost every `x` the equality `f (x, y) = g (x, y)` holds for `ν`-almost every `y`, then
`f z = g z` for `μ.prod ν`-almost every `z`. The proof passes to strongly measurable
representatives, whose equality set is measurable, and applies the description of almost everywhere
membership for a product measure. -/
theorem ae_eq_of_ae_slices {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] {μ : Measure α} {ν : Measure β}
    [SFinite ν] {f g : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : AEStronglyMeasurable g (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = g (x, y)) : ∀ᵐ z ∂(μ.prod ν), f z = g z := by
  have hs : MeasurableSet {z | hf.mk f z = hg.mk g z} :=
    hf.stronglyMeasurable_mk.measurableSet_eq_fun hg.stronglyMeasurable_mk
  have key : ∀ᵐ z ∂(μ.prod ν), z ∈ {z | hf.mk f z = hg.mk g z} := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk, Measure.ae_ae_of_ae_prod hg.ae_eq_mk, h]
      with x h1 h2 h3
    filter_upwards [h1, h2, h3] with y e1 e2 e3
    show hf.mk f (x, y) = hg.mk g (x, y)
    rw [← e1, ← e2, e3]
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk, key] with z e1 e2 e3
  rw [e1, e2]
  exact e3

/-- Let `G : (ℝ × ℝ) × ℝ → ℂ`, `z : ℝ`, and let `μ` be the product of Lebesgue measure restricted to
`Icc 0 1` with Lebesgue measure restricted to `Ioo (-π) π`. If `fun v ↦ G (v, z)` is integrable for
`μ`, then `∫ v, G (v, z) ∂μ = ∫ τ in 0..1, ∫ θ in (-π)..π, G ((τ, θ), z)`. -/
theorem integral_prod_restrict_eq_intervalIntegral {G : (ℝ × ℝ) × ℝ → ℂ} {z : ℝ}
    (hG : Integrable (fun v : ℝ × ℝ ↦ G (v, z))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Ioo (-Real.pi) Real.pi)))) :
    ∫ v, G (v, z) ∂((volume.restrict (Icc (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) =
      ∫ τ in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, G ((τ, θ), z) := by
  rw [integral_prod _ hG, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun τ ↦ ?_)
  simp only
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

/-- For `F : ℝ → ℝ → ℂ` such that `fun p : ℝ × ℝ ↦ F p.1 p.2` is integrable on
`Icc 0 1 ×ˢ Icc 0 (2 * π)`,
`∫ τ in 0..1, ∫ ψ in 0..(2 * π), F τ ψ = ∫ p in Icc 0 1 ×ˢ Icc 0 (2 * π), F p.1 p.2`. -/
theorem intervalIntegral_integral_eq_setIntegral (F : ℝ → ℝ → ℂ)
    (hF : IntegrableOn (fun p : ℝ × ℝ ↦ F p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) :
    ∫ τ in (0 : ℝ)..1, ∫ ψ in (0 : ℝ)..(2 * Real.pi), F τ ψ
      = ∫ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi), F p.1 p.2 := by
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [setIntegral_prod (fun p : ℝ × ℝ ↦ F p.1 p.2) hF, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  funext τ
  rw [intervalIntegral.integral_of_le h2, ← integral_Icc_eq_integral_Ioc]

/-- Fubini's theorem for a continuous function on a rectangle: if `(τ, φ) ↦ F τ φ` is continuous on
`ℝ × ℝ` with values in `ℂ`, and `a ≤ b`, `c ≤ d`, then
`∫ τ in a..b, ∫ φ in c..d, F τ φ = ∫ φ in c..d, ∫ τ in a..b, F τ φ`. The function is integrable on
the compact rectangle, so `integral_integral_swap` applies. -/
theorem intervalIntegral_swap_of_continuous (F : ℝ → ℝ → ℂ)
    (hF : Continuous (fun p : ℝ × ℝ ↦ F p.1 p.2)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ τ in a..b, ∫ φ in c..d, F τ φ = ∫ φ in c..d, ∫ τ in a..b, F τ φ := by
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ((hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self))
  exact integral_integral_swap hi

/-- For real `ρ` and `R`, Lebesgue measure on `ℝ × ℝ` restricted to the rectangle
`Icc ρ R ×ˢ Icc (-R) R` is a finite measure. -/
theorem isFiniteMeasure_restrict_Icc_prod_Icc (ρ R : ℝ) :
    IsFiniteMeasure (volume.restrict (Icc ρ R ×ˢ Icc (-R) R)) :=
  isFiniteMeasure_restrict.2 (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne

/-- For `Φ : ℝ → ℝ → ℝ → ℝ≥0∞` such that `fun q : ℝ × ℝ × ℝ ↦ Φ q.1 q.2.1 q.2.2` is measurable, the
two inner integrals can be exchanged: `∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a b c = ∫⁻ a, ∫⁻ c, ∫⁻ b, Φ a b c`. -/
theorem lintegral_lintegral_lintegral_swap_inner (Φ : ℝ → ℝ → ℝ → ENNReal)
    (hΦ : Measurable fun q : ℝ × ℝ × ℝ ↦ Φ q.1 q.2.1 q.2.2) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a b c = ∫⁻ a, ∫⁻ c, ∫⁻ b, Φ a b c := by
  refine lintegral_congr fun a ↦ ?_
  apply lintegral_lintegral_swap
  exact (hΦ.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- For `Φ : ℝ → ℝ → ℝ → ℝ≥0∞` such that `fun q : ℝ × ℝ × ℝ ↦ Φ q.1 q.2.1 q.2.2` is measurable, the
two outer integrals can be exchanged: `∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a b c = ∫⁻ b, ∫⁻ a, ∫⁻ c, Φ a b c`. -/
theorem lintegral_lintegral_lintegral_swap_outer (Φ : ℝ → ℝ → ℝ → ENNReal)
    (hΦ : Measurable fun q : ℝ × ℝ × ℝ ↦ Φ q.1 q.2.1 q.2.2) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a b c = ∫⁻ b, ∫⁻ a, ∫⁻ c, Φ a b c := by
  apply lintegral_lintegral_swap
  have h : Measurable fun p : (ℝ × ℝ) × ℝ ↦ Φ p.1.1 p.1.2 p.2 :=
    hΦ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact h.lintegral_prod_right'.aemeasurable

/-- For every real `c`, the map `Prod.map id (fun t ↦ t - c)`, that is `(p, t) ↦ (p, t - c)` on
`(ℝ × ℝ) × ℝ`, preserves Lebesgue measure. -/
theorem measurePreserving_prodMap_id_sub_right (c : ℝ) :
    MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ) (fun t : ℝ ↦ t - c))
      (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
  (MeasurePreserving.id volume).prod (measurePreserving_sub_right volume c)

/-- For every real `c`, the map `((r, z), t) ↦ ((-r, z), t - c)` on `(ℝ × ℝ) × ℝ`, written with
`Prod.map`, preserves Lebesgue measure. -/
theorem measurePreserving_prodMap_neg_id_sub_right (c : ℝ) :
    MeasurePreserving (Prod.map (Prod.map (fun r : ℝ ↦ -r) (id : ℝ → ℝ)) (fun t : ℝ ↦ t - c))
      (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
  ((Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)).prod
    (measurePreserving_sub_right volume c)

/-- For all real `R`, `Z`, Lebesgue measure on `ℝ × ℝ` restricted to `Icc 0 R ×ˢ Icc (-Z) Z` is at
most Lebesgue measure restricted to `Ioi 0 ×ˢ univ`. The rectangle lies in `Ici 0 ×ˢ univ`, which
agrees with `Ioi 0 ×ˢ univ` up to a null set. -/
theorem restrict_Icc_prod_le_restrict_Ioi_prod (R Z : ℝ) :
    volume.restrict (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) ≤ volume.restrict
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  refine Measure.restrict_mono_ae ?_
  have hsub : Icc (0 : ℝ) R ×ˢ Icc (-Z) Z ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
      fun p hp ↦ ⟨hp.1.1, trivial⟩
  refine hsub.eventuallySubset.trans ?_
  have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    Measure.set_prod_ae_eq Ioi_ae_eq_Ici .rfl
  exact this.symm.subset

/-- Let `Φ : ℝ × ℝ → ℂ` be integrable on `Icc lo hi ×ˢ t`. If
`∫ p in Icc lo hi ×ˢ t, (χ p.1 : ℂ) * Φ p = 0` for every smooth compactly supported `χ : ℝ → ℝ` with
`tsupport χ ⊆ Ioo lo hi`, then `∫ p in Icc lo hi ×ˢ t, Φ p = 0`. The proof shows by Fubini and the
fundamental lemma of the calculus of variations that `∫ y in t, Φ (x, y) = 0` for almost every `x`
in `Ioo lo hi`. -/
theorem setIntegral_Icc_prod_eq_zero_of_contDiff {Φ : ℝ × ℝ → ℂ} {lo hi : ℝ} {t : Set ℝ}
    (hI : IntegrableOn Φ (Icc lo hi ×ˢ t))
    (hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo lo hi →
      ∫ p in Icc lo hi ×ˢ t, (χ p.1 : ℂ) * Φ p = 0) :
    ∫ p in Icc lo hi ×ˢ t, Φ p = 0 := by
  have hIp : Integrable Φ ((volume.restrict (Icc lo hi)).prod (volume.restrict t)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hI
  have hk : IntegrableOn (fun x ↦ ∫ y in t, Φ (x, y)) (Icc lo hi) := hIp.integral_prod_left
  have hz : ∀ᵐ x, x ∈ Ioo lo hi → (∫ y in t, Φ (x, y)) = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hk.mono_set Ioo_subset_Icc_self).locallyIntegrableOn ?_
    intro χ hχs hχc hχt
    obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχs.continuous
    have e1 : ∫ x, χ x • ∫ y in t, Φ (x, y) = ∫ x in Icc lo hi, χ x • ∫ y in t, Φ (x, y) := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hm ↦ hx (Ioo_subset_Icc_self (hχt hm))), zero_smul]
    have hIχ : Integrable (fun p : ℝ × ℝ ↦ (χ p.1 : ℂ) * Φ p)
        ((volume.restrict (Icc lo hi)).prod (volume.restrict t)) := by
      refine hIp.bdd_mul (c := C)
        (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_fst)).aestronglyMeasurable
        (Eventually.of_forall fun p ↦ ?_)
      rw [Complex.norm_real]; exact hC _
    have e2 : ∫ x in Icc lo hi, χ x • ∫ y in t, Φ (x, y) = ∫ p in Icc lo hi ×ˢ t,
        (χ p.1 : ℂ) * Φ p := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hIχ]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      change χ x • ∫ y in t, Φ (x, y) = ∫ y in t, (χ x : ℂ) * Φ (x, y)
      rw [← integral_smul]
      simp only [Complex.real_smul]
    rw [e1, e2]
    exact hχ χ hχs hχc hχt
  have e3 : ∫ p in Icc lo hi ×ˢ t, Φ p = ∫ x in Icc lo hi, ∫ y in t, Φ (x, y) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hIp]
  rw [e3, integral_Icc_eq_integral_Ioo]
  exact setIntegral_eq_zero_of_ae_eq_zero hz

/-- For a set `s` of reals, the product of Lebesgue measure on `ℝ × ℝ` with Lebesgue measure on `ℝ`
restricted to `s` equals the product measure `volume.prod volume` on `(ℝ × ℝ) × ℝ` restricted to
`univ ×ˢ s`. -/
theorem volume_prod_restrict_right (s : Set ℝ) :
    ((volume : Measure (ℝ × ℝ)).prod (volume.restrict s)) =
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).restrict (univ ×ˢ s) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- For `a ≤ b` and `c ≤ d`, the Lebesgue measure of the rectangle `Icc a b ×ˢ Icc c d` in `ℝ × ℝ`,
as a real number (`Measure.real`), is `(b - a) * (d - c)`. -/
theorem volume_real_Icc_prod_Icc (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (volume : Measure (ℝ × ℝ)).real (Set.Icc a b ×ˢ Set.Icc c d) = (b - a) * (d - c) := by
  rw [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal (by nlinarith)]

/-- For sets `A`, `B` of real numbers, Lebesgue measure on `ℝ × ℝ` restricted to `A ×ˢ B` is the
product of Lebesgue measure restricted to `A` and Lebesgue measure restricted to `B`. -/
theorem volume_restrict_prod_eq_prod (A B : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (A ×ˢ B) = (volume.restrict A).prod (volume.restrict B) :=
        by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

/-- For all real `a b c d`, Lebesgue measure on `ℝ × ℝ` restricted to `Icc a b ×ˢ Icc c d` equals
the product of Lebesgue measure restricted to `Icc a b` and Lebesgue measure restricted to
`Icc c d`. -/
theorem volume_restrict_Icc_prod_Icc_eq_prod (a b c d : ℝ) :
    volume.restrict (Icc a b ×ˢ Icc c d) =
      (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) :=
          volume_restrict_prod_eq_prod _ _

/-- Let `F : ℝ × ℝ → ℂ` be integrable on `Icc a b ×ˢ Icc c d`. If
`∫ p in Icc a b ×ˢ Icc c d, F p * (t p.2 : ℂ) = 0` for every continuous `t : ℝ → ℝ`, then
`∫ r in Icc a b, F (r, z) = 0` for almost every `z` in `Icc c d`. The proof applies Fubini and the
fundamental lemma of the calculus of variations to `fun z ↦ ∫ r in Icc a b, F (r, z)`. -/
theorem ae_setIntegral_slice_eq_zero_of_continuous {a b c d : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F (Icc a b ×ˢ Icc c d))
    (h : ∀ t : ℝ → ℝ, Continuous t → ∫ p in Icc a b ×ˢ Icc c d, F p * ((t p.2 : ℝ) : ℂ) = 0) :
    ∀ᵐ z ∂(volume.restrict (Icc c d)), ∫ r in Icc a b, F (r, z) = 0 := by
  rw [IntegrableOn, volume_restrict_Icc_prod_Icc_eq_prod] at hF
  have hΦ : Integrable (fun z ↦ ∫ r in Icc a b, F (r, z)) (volume.restrict (Icc c d)) :=
    hF.integral_prod_right
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hΦ.locallyIntegrable ?_
  intro φ hφ hφc
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hi : Integrable (fun p : ℝ × ℝ ↦ F p * ((φ p.2 : ℝ) : ℂ))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    refine hF.mul_bdd (c := C) ?_ (Eventually.of_forall fun p ↦ ?_)
    · exact (Complex.continuous_ofReal.comp (hφ.continuous.comp
          continuous_snd)).aestronglyMeasurable
    · change ‖((φ p.2 : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real]; exact hC _
  have h1 := h φ hφ.continuous
  rw [volume_restrict_Icc_prod_Icc_eq_prod, integral_prod_symm _ hi] at h1
  rw [← h1]
  congr 1
  funext z
  rw [← integral_smul]
  congr 1
  funext r
  rw [Complex.real_smul]
  ring

/-- Let `E` be a normed additive commutative group. If `f : ℝ × ℝ → E` is integrable on
`Icc a b ×ˢ Icc c d`, then for almost every `z` in `Icc c d` the function `fun r ↦ f (r, z)` is
integrable on `Icc a b`. -/
theorem integrableOn_Icc_prod_left_ae {E : Type*} [NormedAddCommGroup E] {a b c d : ℝ}
    {f : ℝ × ℝ → E}
    (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ z ∂(volume.restrict (Icc c d)), IntegrableOn (fun r ↦ f (r, z)) (Icc a b) := by
  rw [IntegrableOn, volume_restrict_Icc_prod_Icc_eq_prod] at hf
  exact hf.prod_left_ae

/-- If `G : ℝ × ℝ → ℂ` is integrable on `s₁ ×ˢ s₂` for sets `s₁`, `s₂` of real numbers, its integral
over `s₁ ×ˢ s₂` is the iterated integral `∫ x in s₁, ∫ y in s₂, G (x, y)`, with the first variable
outside. This is Mathlib's `MeasureTheory.setIntegral_prod` for Lebesgue measure on `ℝ × ℝ`. -/
theorem setIntegral_prod_eq_integral_integral {G : ℝ × ℝ → ℂ} {s₁ s₂ : Set ℝ}
    (hG : IntegrableOn G (s₁ ×ˢ s₂)) :
    ∫ p in s₁ ×ˢ s₂, G p = ∫ x in s₁, ∫ y in s₂, G (x, y) := MeasureTheory.setIntegral_prod G hG

/-- If `f : ℝ × ℝ → ℂ` is integrable on the rectangle `[a, b] × [c, d]`, then for almost every `r`
in `[a, b]` the slice `z ↦ f (r, z)` is integrable on `[c, d]`. -/
theorem integrableOn_Icc_prod_right_ae {f : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ r ∂(volume.restrict (Icc a b)), IntegrableOn (fun z ↦ f (r, z)) (Icc c d) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.prod_right_ae

/-- If `f : ℝ × ℝ → ℂ` is integrable on `A ×ˢ B` for sets `A`, `B` of real numbers, its integral
over `A ×ˢ B` is the iterated integral `∫ z in B, ∫ r in A, f (r, z)`, with the second variable
outside. -/
theorem setIntegral_prod_eq_integral_integral_symm {f : ℝ × ℝ → ℂ} {A B : Set ℝ}
    (hf : IntegrableOn f (A ×ˢ B)) :
    ∫ p in A ×ˢ B, f p = ∫ z in B, ∫ r in A, f (r, z) := by
  unfold IntegrableOn at hf
  rw [volume_restrict_prod_eq_prod] at hf ⊢
  exact integral_prod_symm f hf

end PDE.Analysis

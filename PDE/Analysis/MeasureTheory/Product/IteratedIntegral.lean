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
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Uniformizable
public import PDE.Analysis.ENNReal.Basic
public import PDE.Analysis.MeasureTheory.Integrability
public import PDE.Analysis.MeasureTheory.Integral
public import PDE.Analysis.MeasureTheory.IntervalIntegral
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Basic
public import PDE.Analysis.MeasureTheory.Product
public import PDE.Analysis.Topology.Compactness
public import PDE.Analysis.Topology.Series

set_option linter.style.header false

/-!
# Iterated integrals and joint representatives on product measures

The lemmas write an integral over a product as an iterated integral, exchange the order of
integration, and state measurability and integrability of slices. The proofs use
`MeasureTheory.Integrable.prod_left_ae` and Tonelli's theorem as Mathlib states it.

## Main results

* `PDE.Analysis.ae_slice_weak_deriv_integral_eq_zero`: Let `Fw`, `Dw : ℝ × ℝ → ℂ` be integrable on
  every rectangle `Icc 0 R ×ˢ Icc (-Z) Z`, and suppose
  `∫ p, (φ p.1 * deriv χ p.2) * Fw p = -∫ p, (φ p.1 * χ p.2) * Dw p` for all smooth compactly
  supported `φ`, `χ : ℝ → ℝ` with `tsupport φ ⊆ Ioi 0`. Then for `z₁ ≤ z₂` and every `C^1` function
  `s : ℝ → ℝ` with `s z₁ = 0` and `s z₂ = 0`, almost every `r` satisfies: if `r ∈ Ioi 0` then
  `∫ z in Icc z₁ z₂, (s z * Dw (r, z) + deriv s z * Fw (r, z)) = 0`.
* `PDE.Analysis.setIntegral_Icc_prod_Icc_of_hasDerivAt_fst`: Let `F`, `dF : ℝ × ℝ → ℂ` with `dF`
  continuous, and suppose that for every `p` the function `fun r ↦ F (r, p.2)` has derivative `dF p`
  at `p.1`. If `a ≤ b`, then
  `∫ p in Icc a b ×ˢ Icc c d, dF p = ∫ z in Icc c d, (F (b, z) - F (a, z))`.
* `PDE.Analysis.ae_integrableOn_prod_left`: If `f : ℝ × ℝ → ℂ` is integrable on `S ×ˢ T` and `T` is
  measurable, then for almost every real `s`, `s ∈ T` implies that `fun x ↦ f (x, s)` is integrable
  on `S`.
* `PDE.Analysis.exists_stronglyMeasurable_joint_repr_Lp`: Let `μ`, `ν` be s-finite measures on `α`,
  `β`, let `F` be a complete normed group and `1 ≤ p`. If `c : α → Lp F p ν` satisfies
  `MemLp c 1 μ`, then there is a strongly measurable `h : α × β → F` such that for almost every `a`
  the slice `y ↦ h (a, y)` represents `c a`, that is `c a =ᵐ[ν] fun y ↦ h (a, y)`.
* `PDE.Analysis.integral_mul_mul_eq_integral_setIntegral_fst`: Let `θ : ℝ → ℝ` be continuous and
  zero outside `Icc c d`, let `χ : ℝ → ℝ` be zero outside `Icc (-R) R`, and let
  `fun p => (χ p.1 : ℂ) * H p` be integrable on `Icc (-R) R ×ˢ Icc c d`. Then
  `∫ p, ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p = ∫ z, (θ z : ℂ) * ∫ r in Icc (-R) R, (χ r : ℂ) * H (r, z)`.
* `PDE.Analysis.integral_mul_mul_eq_integral_setIntegral_snd`: Let `θ`, `χ : ℝ → ℝ` be continuous,
  with `θ` zero outside `Icc c d` and `χ` zero outside `Icc (-Z) Z`, and let `H : ℝ × ℝ → ℂ` be
  integrable on `Icc c d ×ˢ Icc (-Z) Z`. Then
  `∫ p, ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p = ∫ r, (θ r : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * H (r, z)`.
* `PDE.Analysis.exists_joint_repr_Lp_of_stronglyMeasurable`: Let `μ`, `ν` be s-finite measures on
  `α`, `β`, let `F` be a complete normed group and `1 ≤ p`. If `c : α → Lp F p ν` is strongly
  measurable and `MemLp c 1 μ`, then there is a strongly measurable `h : α × β → F` such that for
  almost every `a` the slice `y ↦ h (a, y)` represents `c a`, that is `c a =ᵐ[ν] fun y => h (a, y)`.

There are 2 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace PDE.Analysis

/-- If `f : ℝ × ℝ → ℂ` is integrable on `S ×ˢ T` and `T` is measurable, then for almost every real
`s`, `s ∈ T` implies that `fun x ↦ f (x, s)` is integrable on `S`. -/
theorem ae_integrableOn_prod_left {f : ℝ × ℝ → ℂ} {S T : Set ℝ} (hT : MeasurableSet T)
    (hf : IntegrableOn f (S ×ˢ T)) : ∀ᵐ s, s ∈ T → IntegrableOn (fun x ↦ f (x, s)) S := by
  have h : Integrable f ((volume.restrict S).prod (volume.restrict T)) := by
    rw [← volume_restrict_prod_eq_prod]
    exact hf
  exact (ae_restrict_iff' hT).1 h.prod_left_ae

/-- Let `μ`, `ν` be s-finite measures on `α`, `β`, let `F` be a complete normed group and `1 ≤ p`.
If `c : α → Lp F p ν` is strongly measurable and `MemLp c 1 μ`, then there is a strongly measurable
`h : α × β → F` such that for almost every `a` the slice `y ↦ h (a, y)` represents `c a`, that is
`c a =ᵐ[ν] fun y ↦ h (a, y)`. The proof approximates `c` in `L¹` by simple functions with errors
below `4⁻¹ ^ k`, shows that for almost every `a` their slices converge almost everywhere, and takes
for `h` a strongly measurable limit on the product. -/
theorem exists_joint_repr_Lp_of_stronglyMeasurable {α : Type*} {β : Type*} {F : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup F] [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {c : α → Lp F p ν} (hcm : StronglyMeasurable c)
    (hc : MemLp c 1 μ) :
    ∃ h : α × β → F, StronglyMeasurable h ∧ ∀ᵐ a ∂μ, (c a : β → F) =ᵐ[ν] fun y ↦ h (a, y) := by
  have hq : ∀ k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k ≠ 0 := fun k ↦
    pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  choose g hg _ using fun k : ℕ ↦ hc.exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top (hq k)
  let ε : ℕ → α → ℝ≥0∞ := fun k a ↦ ‖c a - g k a‖ₑ
  have hεm : ∀ k, Measurable (ε k) := fun k ↦ (hcm.sub (g k).stronglyMeasurable).eNorm
  have hε : ∀ k, ∫⁻ a, ε k a ∂μ < 4⁻¹ ^ k := fun k ↦ by
    have := hg k
    rwa [eLpNorm_one_eq_lintegral_eNorm (hcm.sub (g k).stronglyMeasurable).aestronglyMeasurable] at
        this
  have hT : ∫⁻ a, ∑' k, 2 ^ k * ε k a ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun k ↦ ((hεm k).const_mul _).aemeasurable]
    refine ne_top_of_le_ne_top tsum_inv_two_pow_ne_top (tsum_le_tsum fun k ↦ ?_)
    rw [lintegral_const_mul _ (hεm k)]
    calc 2 ^ k * ∫⁻ a, ε k a ∂μ ≤ 2 ^ k * 4⁻¹ ^ k := by gcongr; exact (hε k).le
      _ = 2⁻¹ ^ k := by rw [← mul_pow, two_mul_inv_four]
  have hTae : ∀ᵐ a ∂μ, ∑' k, 2 ^ k * ε k a < ⊤ :=
    ae_lt_top (Measurable.tsum fun k ↦ (hεm k).const_mul _) hT
  let G : ℕ → α × β → F := fun k z ↦ (g k z.1 : β → F) z.2
  have hG : ∀ k, StronglyMeasurable (G k) := fun k ↦
    MeasureTheory.SimpleFunc.stronglyMeasurable_uncurry_Lp (g k)
  have hbound : ∀ a, ∑' k, 2 ^ k * ε k a < ⊤ → ∀ k, ε k a ≤ (∑' k, 2 ^ k * ε k a) * 2⁻¹ ^ k :=
    fun a _ k ↦ le_mul_inv_two_pow k (le_tsum (fun k ↦ 2 ^ k * ε k a) k)
  have hslice : ∀ᵐ a ∂μ, ∀ᵐ y ∂ν, ∃ l : F, Tendsto (fun n ↦ G n (a, y)) atTop (𝓝 l) := by
    filter_upwards [hTae] with a ha
    set S := ∑' k, 2 ^ k * ε k a
    refine Lp.ae_tendsto_of_cauchy_eLpNorm (f := fun n ↦ (g n a : β → F))
      (fun n ↦ Lp.aestronglyMeasurable _) (Fact.out : 1 ≤ p)
      (B := fun N ↦ (2 * S + 1) * 2⁻¹ ^ N) ?_ ?_
    · rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) ha.ne,
        ENNReal.one_ne_top⟩) tsum_inv_two_pow_ne_top
    · intro N n m hn hm
      have hx0 : (2⁻¹ : ℝ≥0∞) ^ N ≠ 0 := pow_ne_zero _ (by simp)
      have hS : 2 * S * 2⁻¹ ^ N ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ha.ne) (by simp)
      calc eLpNorm ((g n a : β → F) - (g m a : β → F)) p ν = edist (g n a) (g m a) :=
            (Lp.edist_def _ _).symm
        _ ≤ edist (c a) (g n a) + edist (c a) (g m a) := edist_triangle_left _ _ _
        _ = ε n a + ε m a := by rw [eDist_eq_eNorm_sub, eDist_eq_eNorm_sub]
        _ ≤ S * 2⁻¹ ^ n + S * 2⁻¹ ^ m := add_le_add (hbound a ha n) (hbound a ha m)
        _ ≤ S * 2⁻¹ ^ N + S * 2⁻¹ ^ N :=
            add_le_add (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one'
                (ENNReal.inv_le_one.2 one_le_two) hn))
              (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one'
                  (ENNReal.inv_le_one.2 one_le_two) hm))
        _ = 2 * S * 2⁻¹ ^ N := by ring
        _ < 2 * S * 2⁻¹ ^ N + 2⁻¹ ^ N := ENNReal.lt_add_right hS hx0
        _ = (2 * S + 1) * 2⁻¹ ^ N := by ring
  have hconv : MeasurableSet {z : α × β | ∃ l : F, Tendsto (fun n ↦ G n z) atTop (𝓝 l)} :=
    StronglyMeasurable.measurableSet_exists_tendsto hG
  have hprod : ∀ᵐ z ∂μ.prod ν, ∃ l : F, Tendsto (fun n ↦ G n z) atTop (𝓝 l) :=
    (Measure.ae_prod_iff_ae_ae hconv).2 hslice
  obtain ⟨h, hh, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n ↦ (hG n).aestronglyMeasurable) hprod
  refine ⟨h, hh, ?_⟩
  filter_upwards [hTae, Measure.ae_ae_of_ae_prod hlim] with a ha hay
  have h0 : Tendsto (fun n ↦ ε n a) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ bot_le)
      (fun n ↦ ?_)
    exact le_mul_of_one_le_left' (one_le_pow₀ (by norm_num))
  have hm : AEStronglyMeasurable (fun y ↦ h (a, y) - (c a : β → F) y) ν :=
    (hh.comp_measurable measurable_prodMk_left).aestronglyMeasurable.sub (Lp.aestronglyMeasurable _)
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) (μ := ν)
    (f := fun n y ↦ (g n a : β → F) y - (c a : β → F) y)
    (fun n ↦ (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
    (fun y ↦ h (a, y) - (c a : β → F) y) hm (hay.mono fun y hy ↦ hy.sub_const _)
  have heq : ∀ n, eLpNorm (fun y ↦ (g n a : β → F) y - (c a : β → F) y) p ν = ε n a := by
    intro n
    change _ = ‖c a - g n a‖ₑ
    rw [← eDist_eq_eNorm_sub, edist_comm, Lp.edist_def]
    rfl
  simp_rw [heq] at hle
  rw [h0.liminf_eq, nonpos_iff_eq_zero] at hle
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  filter_upwards [(eLpNorm_eq_zero_iff hp0).1 hle] with y hy
  exact (sub_eq_zero.1 hy).symm

/-- If `f : ℝ × ℝ → ℂ` is integrable on `A ×ˢ B` for sets `A`, `B ⊆ ℝ`, then
`fun r ↦ ∫ z in B, f (r, z)` is integrable on `A`. -/
theorem integrableOn_integral_prod_left {f : ℝ × ℝ → ℂ} {A B : Set ℝ}
    (hf : IntegrableOn f (A ×ˢ B)) :
    IntegrableOn (fun r ↦ ∫ z in B, f (r, z)) A := by
  unfold IntegrableOn at hf
  rw [volume_restrict_prod_eq_prod] at hf
  exact hf.integral_prod_left

/-- If `f : ℝ × ℝ → ℂ` is integrable on `A ×ˢ B` for sets `A`, `B ⊆ ℝ`, then
`fun z ↦ ∫ r in A, f (r, z)` is integrable on `B`. -/
theorem integrableOn_integral_prod_right {f : ℝ × ℝ → ℂ} {A B : Set ℝ}
    (hf : IntegrableOn f (A ×ˢ B)) :
    IntegrableOn (fun z ↦ ∫ r in A, f (r, z)) B := by
  unfold IntegrableOn at hf
  rw [volume_restrict_prod_eq_prod] at hf
  exact hf.integral_prod_right

/-- Let `θ : ℝ → ℝ` be continuous and zero outside `Icc c d`, let `χ : ℝ → ℝ` be zero outside
`Icc (-R) R`, and let `fun p ↦ (χ p.1 : ℂ) * H p` be integrable on `Icc (-R) R ×ˢ Icc c d`. Then
`∫ p, ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p = ∫ z, (θ z : ℂ) * ∫ r in Icc (-R) R, (χ r : ℂ) * H (r,
z)`. The proof restricts both integrals to the rectangle and applies Fubini with the inner integral
in the first variable. -/
theorem integral_mul_mul_eq_integral_setIntegral_fst {H : ℝ × ℝ → ℂ} {θ χ : ℝ → ℝ} {c d R : ℝ}
    (hH : IntegrableOn (fun p : ℝ × ℝ ↦ (χ p.1 : ℂ) * H p) (Icc (-R) R ×ˢ Icc c d))
    (hθ : Continuous θ) (hθs : ∀ x, x ∉ Icc c d → θ x = 0) (hχs : ∀ r, r ∉ Icc (-R) R → χ r = 0) :
    ∫ p, ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p = ∫ z, (θ z : ℂ) * ∫ r in Icc (-R) R,
        (χ r : ℂ) * H (r, z) := by
  have hz1 : ∀ p ∉ Icc (-R) R ×ˢ Icc c d, ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p = 0 := by
    intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc (-R) R ∧ p.2 ∈ Icc c d) from hp) with h | h
    · simp [hχs _ h]
    · simp [hθs _ h]
  have hz2 : ∀ z ∉ Icc c d, (θ z : ℂ) * ∫ r in Icc (-R) R, (χ r : ℂ) * H (r, z) = 0 := by
    intro z hz
    simp [hθs _ hz]
  have hint : IntegrableOn (fun p : ℝ × ℝ ↦ ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p)
      (Icc (-R) R ×ˢ Icc c d) := by
    refine IntegrableOn.congr_fun (hH.continuousOn_mul (Complex.continuous_ofReal.comp
        (hθ.comp continuous_snd)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)) (fun p _ ↦ ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2,
    setIntegral_prod_eq_integral_integral_symm hint]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  simp only
  rw [← integral_const_mul]
  congr 1
  funext r
  push_cast
  ring

/-- Let `θ`, `χ : ℝ → ℝ` be continuous, with `θ` zero outside `Icc c d` and `χ` zero outside
`Icc (-Z) Z`, and let `H : ℝ × ℝ → ℂ` be integrable on `Icc c d ×ˢ Icc (-Z) Z`. Then
`∫ p, ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p = ∫ r, (θ r : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * H (r,
z)`. The proof restricts both integrals to the rectangle and applies Fubini with the inner integral
in the second variable. -/
theorem integral_mul_mul_eq_integral_setIntegral_snd {H : ℝ × ℝ → ℂ} {θ χ : ℝ → ℝ} {c d Z : ℝ}
    (hH : IntegrableOn H (Icc c d ×ˢ Icc (-Z) Z))
    (hθ : Continuous θ) (hχ : Continuous χ) (hθs : ∀ x, x ∉ Icc c d → θ x = 0)
    (hχs : ∀ z, z ∉ Icc (-Z) Z → χ z = 0) :
    ∫ p, ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p = ∫ r, (θ r : ℂ) * ∫ z in Icc (-Z) Z,
        (χ z : ℂ) * H (r, z) := by
  have hz1 : ∀ p ∉ Icc c d ×ˢ Icc (-Z) Z, ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p = 0 := by
    intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc c d ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · simp [hθs _ h]
    · simp [hχs _ h]
  have hz2 : ∀ r ∉ Icc c d, (θ r : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * H (r, z) = 0 := by
    intro r hr
    simp [hθs _ hr]
  have hint : IntegrableOn (fun p : ℝ × ℝ ↦ ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p)
      (Icc c d ×ˢ Icc (-Z) Z) :=
    hH.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2,
    setIntegral_prod_eq_integral_integral hint]
  refine integral_congr_ae (Eventually.of_forall fun r ↦ ?_)
  simp only
  rw [← integral_const_mul]
  congr 1
  funext z
  push_cast
  ring

/-- Let `Fw`, `Dw : ℝ × ℝ → ℂ` be integrable on every rectangle `Icc 0 R ×ˢ Icc (-Z) Z`, and suppose
`∫ p, (φ p.1 * deriv χ p.2) * Fw p = -∫ p, (φ p.1 * χ p.2) * Dw p` for all smooth compactly
supported `φ`, `χ : ℝ → ℝ` with `tsupport φ ⊆ Ioi 0`. Then for `z₁ ≤ z₂` and every `C^1` function
`s : ℝ → ℝ` with `s z₁ = 0` and `s z₂ = 0`, almost every `r` satisfies: if `r ∈ Ioi 0` then
`∫ z in Icc z₁ z₂, (s z * Dw (r, z) + deriv s z * Fw (r, z)) = 0`. The proof tests the slice
integral against smooth functions of `r` supported in `Ioi 0`, exchanges the order of integration,
and applies the one-variable statement to the resulting functions of `z`. -/
theorem ae_slice_weak_deriv_integral_eq_zero {Fw Dw : ℝ × ℝ → ℂ}
    (hF : ∀ R Z : ℝ, IntegrableOn Fw (Icc 0 R ×ˢ Icc (-Z) Z))
    (hD : ∀ R Z : ℝ, IntegrableOn Dw (Icc 0 R ×ˢ Icc (-Z) Z))
    (hw : ∀ φ χ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ p, ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = -∫ p, ((φ p.1 * χ p.2 : ℝ) : ℂ) * Dw p)
    {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) (s : ℝ → ℝ) (hs : ContDiff ℝ 1 s) (hs1 : s z₁ = 0) (hs2 : s z₂ = 0) :
    ∀ᵐ r, r ∈ Ioi (0 : ℝ) →
      ∫ z in Icc z₁ z₂, (((s z : ℝ) : ℂ) * Dw (r, z) + ((deriv s z : ℝ) : ℂ) * Fw (r, z)) = 0 := by
  have hsc : Continuous s := hs.continuous
  have hdsc : Continuous (deriv s) := hs.continuous_deriv le_rfl
  set Z₀ : ℝ := |z₁| + |z₂| with hZ₀
  have hI : Icc z₁ z₂ ⊆ Icc (-Z₀) Z₀ := fun z hz' ↦ by
    constructor <;> linarith [hz'.1, hz'.2, abs_nonneg z₁, abs_nonneg z₂, neg_abs_le z₁,
        le_abs_self z₂]
  set Gf : ℝ × ℝ → ℂ := fun p ↦ ((s p.2 : ℝ) : ℂ) * Dw p + ((deriv s p.2 : ℝ) : ℂ) * Fw p with hGf
  have hGbox : ∀ R, IntegrableOn Gf (Icc 0 R ×ˢ Icc z₁ z₂) := by
    intro R
    have hsub : Icc 0 R ×ˢ Icc z₁ z₂ ⊆ Icc 0 R ×ˢ Icc (-Z₀) Z₀ := prod_mono le_rfl hI
    exact (integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc
        ((hD R Z₀).mono_set hsub) (hsc.comp continuous_snd)).add
      (integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc
          ((hF R Z₀).mono_set hsub) (hdsc.comp continuous_snd))
  set Φ : ℝ → ℂ := fun r ↦ ∫ z in Icc z₁ z₂, Gf (r, z) with hΦ
  have hΦint : ∀ R, IntegrableOn Φ (Icc 0 R) := fun R ↦ integrableOn_integral_prod_left (hGbox R)
  have hloc : LocallyIntegrableOn Φ (Ioi 0) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun k hk hkc ↦ ?_
    obtain ⟨R, _, hR⟩ := exists_pos_subset_Icc_neg_of_isCompact hkc
    exact (hΦint R).mono_set fun r hr ↦ ⟨le_of_lt (hk hr), (hR hr).2⟩
  have := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · exact this
  intro g hg hgc hgs
  obtain ⟨R, _, hR⟩ := exists_pos_subset_Icc_neg_of_isCompact hgc.isCompact
  have hg0 : ∀ r, r ∉ Icc 0 R → g r = 0 := fun r hr ↦ image_eq_zero_of_notMem_tsupport (fun h' ↦
    hr ⟨le_of_lt (hgs h'), (hR h').2⟩)
  have hgcC : Continuous (fun r ↦ ((g r : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hg.continuous
  set Cg : ℝ → ℂ := fun z ↦ ∫ r in Icc 0 R, ((g r : ℝ) : ℂ) * Fw (r, z) with hCg
  set Bg : ℝ → ℂ := fun z ↦ ∫ r in Icc 0 R, ((g r : ℝ) : ℂ) * Dw (r, z) with hBg
  have hCl : LocallyIntegrable Cg volume := by
    refine (locallyIntegrable_iff).2 fun k hk ↦ ?_
    obtain ⟨Z, _, hZ⟩ := exists_pos_subset_Icc_neg_of_isCompact hk
    exact (integrableOn_integral_prod_right (f := fun p ↦ ((g p.1 : ℝ) : ℂ) * Fw p)
      (integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc (hF R Z)
          (hg.continuous.comp continuous_fst))).mono_set hZ
  have hBl : LocallyIntegrable Bg volume := by
    refine (locallyIntegrable_iff).2 fun k hk ↦ ?_
    obtain ⟨Z, _, hZ⟩ := exists_pos_subset_Icc_neg_of_isCompact hk
    exact (integrableOn_integral_prod_right (f := fun p ↦ ((g p.1 : ℝ) : ℂ) * Dw p)
      (integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc (hD R Z)
          (hg.continuous.comp continuous_fst))).mono_set hZ
  have hyp : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ z, deriv χ z • Cg z = -∫ z, χ z • Bg z := by
    intro χ hχ hχc
    obtain ⟨Z, _, hZ⟩ := exists_pos_subset_Icc_neg_of_isCompact hχc.isCompact
    have hχ0 : ∀ z, z ∉ Icc (-Z) Z → χ z = 0 := fun z hz' ↦
        image_eq_zero_of_notMem_tsupport (fun h' ↦ hz' (hZ h'))
    have hd0 : ∀ z, z ∉ Icc (-Z) Z → deriv χ z = 0 := fun z hz' ↦
      image_eq_zero_of_notMem_tsupport (fun h' ↦ hz' (hZ (tsupport_deriv_subset h')))
    have hdχ : Continuous (deriv χ) := hχ.continuous_deriv (by exact_mod_cast le_top)
    have key := hw g χ hg hgc hgs hχ hχc
    have e1 : ∫ p, ((g p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = ∫ z, deriv χ z • Cg z := by
      have hout : ∀ p, p ∉ Icc 0 R ×ˢ Icc (-Z) Z → ((g p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = 0 := by
        intro p hp
        rcases not_and_or.1 hp with h' | h'
        · simp [hg0 _ h']
        · simp [hd0 _ h']
      have hint : IntegrableOn (fun p ↦ ((g p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p)
          (Icc 0 R ×ˢ Icc (-Z) Z) :=
        integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc (hF R Z)
            ((hg.continuous.comp continuous_fst).mul (hdχ.comp continuous_snd))
      have L : ∫ z, deriv χ z • Cg z = ∫ z in Icc (-Z) Z, deriv χ z • Cg z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz' ↦ by simp [hd0 z hz'])).symm
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
          setIntegral_prod_eq_integral_integral_symm hint, L]
      refine setIntegral_congr_fun measurableSet_Icc fun z _ ↦ ?_
      simp only [hCg, Complex.real_smul]
      rw [← integral_const_mul]
      congr 1
      funext r
      push_cast
      ring
    have e2 : ∫ p, ((g p.1 * χ p.2 : ℝ) : ℂ) * Dw p = ∫ z, χ z • Bg z := by
      have hout : ∀ p, p ∉ Icc 0 R ×ˢ Icc (-Z) Z → ((g p.1 * χ p.2 : ℝ) : ℂ) * Dw p = 0 := by
        intro p hp
        rcases not_and_or.1 hp with h' | h'
        · simp [hg0 _ h']
        · simp [hχ0 _ h']
      have hint : IntegrableOn (fun p ↦ ((g p.1 * χ p.2 : ℝ) : ℂ) * Dw p)
          (Icc 0 R ×ˢ Icc (-Z) Z) :=
        integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc (hD R Z)
            ((hg.continuous.comp continuous_fst).mul (hχ.continuous.comp continuous_snd))
      have L : ∫ z, χ z • Bg z = ∫ z in Icc (-Z) Z, χ z • Bg z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz' ↦ by simp [hχ0 z hz'])).symm
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
          setIntegral_prod_eq_integral_integral_symm hint, L]
      refine setIntegral_congr_fun measurableSet_Icc fun z _ ↦ ?_
      simp only [hBg, Complex.real_smul]
      rw [← integral_const_mul]
      congr 1
      funext r
      push_cast
      ring
    rw [← e1, ← e2]
    exact key
  have h1 := setIntegral_smul_add_deriv_smul_eq_zero hBl hCl hyp hz s hs hs1 hs2
  have hout : ∀ r, r ∉ Icc 0 R → g r • Φ r = 0 := fun r hr ↦ by simp [hg0 r hr]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  have hsub : Icc 0 R ×ˢ Icc z₁ z₂ ⊆ Icc 0 R ×ˢ Icc (-Z₀) Z₀ := prod_mono le_rfl hI
  have iD : IntegrableOn (fun p ↦ ((g p.1 * s p.2 : ℝ) : ℂ) * Dw p) (Icc 0 R ×ˢ Icc z₁ z₂) :=
    integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc
        ((hD R Z₀).mono_set hsub) ((hg.continuous.comp continuous_fst).mul
            (hsc.comp continuous_snd))
  have iF : IntegrableOn (fun p ↦ ((g p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) (Icc 0 R ×ˢ Icc z₁ z₂) :=
    integrableOn_prod_ofReal_mul_of_continuous isCompact_Icc isCompact_Icc
        ((hF R Z₀).mono_set hsub) ((hg.continuous.comp continuous_fst).mul
            (hdsc.comp continuous_snd))
  have e3 : ∫ r in Icc 0 R, g r • Φ r =
      ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (((g p.1 * s p.2 : ℝ) : ℂ) * Dw p +
          ((g p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) := by
    have iDF : IntegrableOn (fun p ↦ ((g p.1 * s p.2 : ℝ) : ℂ) * Dw p +
        ((g p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p)
        (Icc 0 R ×ˢ Icc z₁ z₂) := iD.add iF
    rw [setIntegral_prod_eq_integral_integral iDF]
    refine setIntegral_congr_fun measurableSet_Icc fun r _ ↦ ?_
    simp only [hΦ, hGf, Complex.real_smul]
    rw [← integral_const_mul]
    congr 1
    funext z
    push_cast
    ring
  rw [e3, integral_add iD iF, setIntegral_prod_eq_integral_integral_symm iD,
      setIntegral_prod_eq_integral_integral_symm iF, ← h1, ← integral_add]
  · refine setIntegral_congr_fun measurableSet_Icc fun z _ ↦ ?_
    simp only [hBg, hCg, Complex.real_smul]
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1 <;> (congr 1; funext r; push_cast; ring)
  · exact integrableOn_integral_prod_right iD
  · exact integrableOn_integral_prod_right iF

/-- Let `μ`, `ν` be s-finite measures on `α`, `β`, let `F` be a complete normed group and `1 ≤ p`.
If `c : α → Lp F p ν` satisfies `MemLp c 1 μ`, then there is a strongly measurable `h : α × β → F`
such that for almost every `a` the slice `y ↦ h (a, y)` represents `c a`, that is
`c a =ᵐ[ν] fun y ↦ h (a, y)`. The proof replaces `c` by a strongly measurable function that equals
it almost everywhere. -/
theorem exists_stronglyMeasurable_joint_repr_Lp {α : Type*} {β : Type*} {F : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup F] [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {c : α → Lp F p ν} (hc : MemLp c 1 μ) :
    ∃ h : α × β → F, StronglyMeasurable h ∧ ∀ᵐ a ∂μ, (c a : β → F) =ᵐ[ν] fun y ↦ h (a, y) := by
  obtain ⟨h, hh, hae⟩ := exists_joint_repr_Lp_of_stronglyMeasurable
      hc.aestronglyMeasurable.stronglyMeasurable_mk
    (hc.ae_eq hc.aestronglyMeasurable.ae_eq_mk)
  refine ⟨h, hh, ?_⟩
  filter_upwards [hae, hc.aestronglyMeasurable.ae_eq_mk] with a h1 h2
  rw [h2]
  exact h1

/-- Let `F`, `dF : ℝ × ℝ → ℂ` with `dF` continuous, and suppose that for every `p` the function
`fun r ↦ F (r, p.2)` has derivative `dF p` at `p.1`. If `a ≤ b`, then
`∫ p in Icc a b ×ˢ Icc c d, dF p = ∫ z in Icc c d, (F (b, z) - F (a, z))`. -/
theorem setIntegral_Icc_prod_Icc_of_hasDerivAt_fst {F dF : ℝ × ℝ → ℂ} (hdF : Continuous dF)
    (hF : ∀ p : ℝ × ℝ, HasDerivAt (fun r ↦ F (r, p.2)) (dF p) p.1) {a b c d : ℝ} (hab : a ≤ b) :
    ∫ p in Icc a b ×ˢ Icc c d, dF p = ∫ z in Icc c d, (F (b, z) - F (a, z)) := by
  rw [setIntegral_prod_eq_integral_integral_symm (integrableOn_Icc_prod_Icc_of_continuous hdF a b c
      d)]
  refine setIntegral_congr_fun measurableSet_Icc (fun z _ ↦ ?_)
  exact integral_Icc_eq_sub_of_hasDerivAt (u := fun r ↦ F (r, z))
      (hdF.comp (continuous_id.prodMk continuous_const))
    (fun x ↦ hF (x, z)) hab

end PDE.Analysis

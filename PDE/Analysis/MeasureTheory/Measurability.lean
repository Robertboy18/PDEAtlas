/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file, except aestronglyMeasurable_pi_pi_of_forall, come from modules of the
Lean package of the paper "Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
The lemma aestronglyMeasurable_pi_pi_of_forall was written for this library, for the two lemmas of
the package that it replaces.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.CompletePartialOrder
public import PDE.Analysis.ENNReal.Basic
public import PDE.Analysis.Topology.Continuity

set_option linter.style.header false

/-!
# Measurable functions and sets

The lemmas state measurability, almost everywhere measurability and strong measurability for
products, compositions and restrictions of particular shapes. The proofs use the closure properties
of Mathlib (`aemeasurable_pi_iff`, `Measurable.comp_aemeasurable`).

## Main results

* `PDE.Analysis.aestronglyMeasurable_clm_apply`: If `A : α → E →L[ℝ] F` and `b : α → E` are almost
  everywhere strongly measurable, where `E` and `F` are real normed spaces, then so is the pointwise
  application `x ↦ A x (b x)`.
* `PDE.Analysis.aestronglyMeasurable_pi_of_forall`: Let `β` be a finite type and `μ` a measure on a
  measurable space `α`. If `fun p ↦ f p b` is almost everywhere strongly measurable for every
  `b : β`, then `f : α → β → ℂ` is almost everywhere strongly measurable.
* `PDE.Analysis.measurePreserving_equivIoc_val`: The map `AddCircle (1 : ℝ) → ℝ` that sends a point
  of the circle to its representative in `Ioc 0 1`, namely `t ↦ ↑(AddCircle.equivIoc 1 0 t)`, is
  measure preserving from the volume of the circle to Lebesgue measure restricted to
  `Ioc 0 (0 + 1)`.
* `PDE.Analysis.aemeasurable_quadratic_form_sqrt`: For a measure `μ` on `ℝ × ℝ`, a real constant
  `k`, and almost everywhere measurable real functions `st cc gc vc mg wg len xo x1 x0`, the
  function `p ↦ (st p + cc p) * Real.sqrt (xo p) ^ 2 + (k * wg p * len p / 2 + gc p) * Real.sqrt (x1
  p) ^ 2 + (k * wg p * (len p)⁻¹ / 2 + vc p) * Real.sqrt (x0 p) ^ 2 + k * mg p * (Real.sqrt (x1 p) *
  Real.sqrt (x0 p))` is almost everywhere measurable.
* `PDE.Analysis.aestronglyMeasurable_Ioi_apply_comp_sub_div`: Let `T τ` be continuous linear maps on
  a real Hilbert space `E` with `‖T τ‖ ≤ Real.exp (-(τ / 4))` for all `τ ≥ 0` and with `τ ↦ T τ y`
  continuous on `Ici 0` for every `y`, and let `G : ℝ → E` be continuous. Then for all real `σ` and
  `P`, the function `τ ↦ T τ (G (σ - τ / P))` is almost everywhere strongly measurable for Lebesgue
  measure restricted to `Ioi 0`.
* `PDE.Analysis.exists_ae_greatest_measurable_le`: For a σ-finite measure `μ` and any function
  `c : α → ℝ≥0∞`, measurable or not, there is a measurable `c' ≤ c` such that every measurable
  `h ≤ c` satisfies `h ≤ᵐ[μ] c'`.

There are 8 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
  The lemma `aestronglyMeasurable_pi_pi_of_forall` is not from the package: it was written for
  this library, for the two lemmas of the package that it replaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis

/-- For a measure `μ` on `ℝ × ℝ`, a real constant `k`, and almost everywhere measurable real
functions `st cc gc vc mg wg len xo x1 x0`, the function
`p ↦ (st p + cc p) * Real.sqrt (xo p) ^ 2 + (k * wg p * len p / 2 + gc p) * Real.sqrt (x1 p) ^ 2 +
(k * wg p * (len p)⁻¹ / 2 + vc p) * Real.sqrt (x0 p) ^ 2 + k * mg p * (Real.sqrt (x1 p) * Real.sqrt
(x0 p))` is almost everywhere measurable. The proof combines the closure of almost everywhere
measurability under sums, products, inverses and the continuous square root. -/
theorem aemeasurable_quadratic_form_sqrt {μ : Measure (ℝ × ℝ)}
    {st cc gc vc mg wg len xo x1 x0 : ℝ × ℝ → ℝ} (k : ℝ)
    (hst : AEMeasurable st μ) (hcc : AEMeasurable cc μ) (hgc : AEMeasurable gc μ)
        (hvc : AEMeasurable vc μ)
    (hmg : AEMeasurable mg μ) (hwg : AEMeasurable wg μ) (hlen : AEMeasurable len μ)
    (hxo : AEMeasurable xo μ) (hx1 : AEMeasurable x1 μ) (hx0 : AEMeasurable x0 μ) :
    AEMeasurable (fun p ↦ (st p + cc p) * Real.sqrt (xo p) ^ 2
      + (k * wg p * len p / 2 + gc p) * Real.sqrt (x1 p) ^ 2
      + (k * wg p * (len p)⁻¹ / 2 + vc p) * Real.sqrt (x0 p) ^ 2
      + k * mg p * (Real.sqrt (x1 p) * Real.sqrt (x0 p))) μ := by
  have hs : ∀ {u : ℝ × ℝ → ℝ}, AEMeasurable u μ → AEMeasurable (fun p ↦ Real.sqrt (u p)) μ :=
    fun h ↦ Real.continuous_sqrt.measurable.comp_aemeasurable h
  have so := hs hxo
  have s1 := hs hx1
  have s0 := hs hx0
  refine (((hst.add hcc).mul (so.pow_const 2)).add ?_).add ?_ |>.add ?_
  · exact ((((aemeasurable_const.mul hwg).mul hlen).div_const 2).add hgc).mul (s1.pow_const 2)
  · exact ((((aemeasurable_const.mul hwg).mul hlen.inv).div_const 2).add hvc).mul (s0.pow_const 2)
  · exact (aemeasurable_const.mul hmg).mul (s1.mul s0)

/-- Let `T τ` be continuous linear maps on a real Hilbert space `E` with
`‖T τ‖ ≤ Real.exp (-(τ / 4))` for all `τ ≥ 0` and with `τ ↦ T τ y` continuous on `Ici 0` for every
`y`, and let `G : ℝ → E` be continuous. Then for all real `σ` and `P`, the function
`τ ↦ T τ (G (σ - τ / P))` is almost everywhere strongly measurable for Lebesgue measure restricted
to `Ioi 0`. -/
theorem aestronglyMeasurable_Ioi_apply_comp_sub_div {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ ↦ T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) {P : ℝ} (σ : ℝ) :
    AEStronglyMeasurable (fun τ ↦ T τ (G (σ - τ / P))) (volume.restrict (Ioi (0 : ℝ))) :=
  ((continuousOn_apply_of_norm_le_exp_neg T hnorm hcont (fun τ ↦ G (σ - τ / P))
    (hG.comp (continuous_const.sub (continuous_id.div_const P)))).mono
    Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi

/-- If `A : α → E →L[ℝ] F` and `b : α → E` are almost everywhere strongly measurable, where `E` and
`F` are real normed spaces, then so is the pointwise application `x ↦ A x (b x)`. The proof composes
the pair `(A, b)` with the continuous bilinear evaluation map. -/
theorem aestronglyMeasurable_clm_apply {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : α → E →L[ℝ] F} {b : α → E} (hA : AEStronglyMeasurable A μ)
    (hb : AEStronglyMeasurable b μ) : AEStronglyMeasurable (fun x ↦ A x (b x)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable
    (hA.prodMk hb)

/-- Let `β` be a finite type and `μ` a measure on a measurable space `α`. If `fun p ↦ f p b` is
almost everywhere strongly measurable for every `b : β`, then `f : α → β → ℂ` is almost everywhere
strongly measurable. -/
theorem aestronglyMeasurable_pi_of_forall {α β : Type*} [MeasurableSpace α] [Finite β]
    {f : α → β → ℂ} {μ : Measure α}
    (h : ∀ b, AEStronglyMeasurable (fun p ↦ f p b) μ) : AEStronglyMeasurable f μ :=
  (aemeasurable_pi_iff.2 fun b ↦ (h b).aemeasurable).aestronglyMeasurable

/-- Let `β`, `γ` be finite types and `μ` a measure on a measurable space `α`. If
`fun p ↦ f p a b` is almost everywhere strongly measurable for all `a : β` and `b : γ`, then
`f : α → β → γ → ℂ` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_pi_pi_of_forall {α β γ : Type*} [MeasurableSpace α] [Finite β]
    [Finite γ] {f : α → β → γ → ℂ} {μ : Measure α}
    (h : ∀ a b, AEStronglyMeasurable (fun p ↦ f p a b) μ) : AEStronglyMeasurable f μ :=
  (aemeasurable_pi_iff.2 fun a ↦ aemeasurable_pi_iff.2 fun b ↦
      (h a b).aemeasurable).aestronglyMeasurable

/-- For a σ-finite measure `μ` and a function `c : α → ℝ≥0∞` with `c x ≤ n` for all `x`, where
`n ≠ ⊤`, there is a measurable `c' ≤ c` such that every measurable `h ≤ c` satisfies `h ≤ᵐ[μ] c'`;
no measurability of `c` is assumed. The proof takes a positive measurable weight `ω` with finite
integral, picks a measurable `e ≤ c * ω` with the same lower integral, sets `c' = e / ω`, and
compares the lower integrals of `max h c' * ω` and `e`. -/
theorem exists_ae_greatest_measurable_le_of_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (c : α → ℝ≥0∞) {n : ℝ≥0∞}
    (hn : n ≠ ⊤) (hc : ∀ x, c x ≤ n) :
    ∃ c' : α → ℝ≥0∞, Measurable c' ∧ c' ≤ c ∧
      ∀ h : α → ℝ≥0∞, Measurable h → h ≤ c → h ≤ᵐ[μ] c' := by
  obtain ⟨ω, hω0, hωm, hωi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  set ωe : α → ℝ≥0∞ := fun x ↦ (ω x : ℝ≥0∞) with hωe
  have hωem : Measurable ωe := hωm.coe_nnreal_ennreal
  have hωe0 : ∀ x, ωe x ≠ 0 := fun x ↦ ENNReal.coe_ne_zero.2 (hω0 x).ne'
  have hωeT : ∀ x, ωe x ≠ ⊤ := fun x ↦ ENNReal.coe_ne_top
  obtain ⟨e, hem, heF, hint⟩ := exists_measurable_le_lintegral_eq μ (fun x ↦ c x * ωe x)
  have hfin : ∫⁻ x, e x ∂μ ≠ ⊤ := by
    rw [← hint]
    refine ne_top_of_le_ne_top (b := ∫⁻ x, n * ωe x ∂μ) ?_
      (lintegral_mono fun x ↦ mul_le_mul_left (hc x) _)
    rw [lintegral_const_mul _ hωem]
    exact ENNReal.mul_ne_top hn (hωi.trans ENNReal.one_lt_top).ne
  set c' : α → ℝ≥0∞ := fun x ↦ e x / ωe x with hc'def
  have hc'm : Measurable c' := hem.div hωem
  have hc'c : c' ≤ c := fun x ↦ ENNReal.div_le_of_le_mul (heF x)
  have hee : ∀ x, c' x * ωe x = e x := fun x ↦ ENNReal.div_mul_cancel (hωe0 x) (hωeT x)
  refine ⟨c', hc'm, hc'c, fun h hh hhc ↦ ?_⟩
  set e' : α → ℝ≥0∞ := fun x ↦ max (h x) (c' x) * ωe x with he'def
  have he'm : Measurable e' := (hh.max hc'm).mul hωem
  have hle : e ≤ᵐ[μ] e' := Filter.Eventually.of_forall fun x ↦ by
    rw [← hee x]
    exact mul_le_mul_left (le_max_right _ _) _
  have hle2 : ∫⁻ x, e' x ∂μ ≤ ∫⁻ x, e x ∂μ := by
    rw [← hint]
    exact lintegral_mono fun x ↦ mul_le_mul_left (max_le (hhc x) (hc'c x)) _
  have hae := ae_eq_of_ae_le_of_lintegral_le hle hfin he'm.aemeasurable hle2
  filter_upwards [hae] with x hx
  rw [← hee x] at hx
  have hx' : c' x = max (h x) (c' x) := (ENNReal.mul_left_inj (hωe0 x) (hωeT x)).1 hx
  rw [hx']
  exact le_max_left _ _

/-- If `f : α → ℝ≥0∞` is almost everywhere measurable for a measure `μ`, there is a measurable
`g : α → ℝ≥0∞` with `f ≤ g` pointwise and `g =ᵐ[μ] f`. The proof takes the measurable version of `f`
and replaces it by `∞` on a measurable null set that contains the points where the two differ. -/
theorem exists_measurable_ge_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ g =ᵐ[μ] f := by
  classical
  set S := toMeasurable μ {x | f x ≠ hf.mk f x}
  have hS0 : μ S = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hf.ae_eq_mk
  refine ⟨S.piecewise (fun _ ↦ ∞) (hf.mk f),
    Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const hf.measurable_mk, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S
    · simp [Set.piecewise, hx]
    · have hx' : f x = hf.mk f x := by
        by_contra hc
        exact hx (subset_toMeasurable _ _ hc)
      simp only [Set.piecewise, hx, ite_false]
      exact hx'.le
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS0, hf.ae_eq_mk] with x hx hx'
    simp only [Set.piecewise, hx, ite_false]
    exact hx'.symm

/-- The map `AddCircle (1 : ℝ) → ℝ` that sends a point of the circle to its representative in
`Ioc 0 1`, namely `t ↦ ↑(AddCircle.equivIoc 1 0 t)`, is measure preserving from the volume of the
circle to Lebesgue measure restricted to `Ioc 0 (0 + 1)`. -/
theorem measurePreserving_equivIoc_val :
    MeasurePreserving (fun t : AddCircle (1 : ℝ) ↦ ((AddCircle.equivIoc 1 0 t : Ioc (0 : ℝ)
        (0 + 1)) : ℝ))
      volume (volume.restrict (Ioc (0 : ℝ) (0 + 1))) :=
  (measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc 1)

/-- For a σ-finite measure `μ` and any function `c : α → ℝ≥0∞`, measurable or not, there is a
measurable `c' ≤ c` such that every measurable `h ≤ c` satisfies `h ≤ᵐ[μ] c'`. The proof applies the
bounded case to the truncations `x ↦ min (c x) n` for `n : ℕ` and takes the supremum over `n`. -/
theorem exists_ae_greatest_measurable_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (c : α → ℝ≥0∞) :
    ∃ c' : α → ℝ≥0∞, Measurable c' ∧ c' ≤ c ∧
      ∀ h : α → ℝ≥0∞, Measurable h → h ≤ c → h ≤ᵐ[μ] c' := by
  have hk : ∀ n : ℕ, ∃ c' : α → ℝ≥0∞, Measurable c' ∧ c' ≤ (fun x ↦ min (c x) (n : ℝ≥0∞)) ∧
      ∀ h : α → ℝ≥0∞, Measurable h → h ≤ (fun x ↦ min (c x) (n : ℝ≥0∞)) → h ≤ᵐ[μ] c' :=
    fun n ↦ exists_ae_greatest_measurable_le_of_bounded μ _ (ENNReal.natCast_ne_top n) fun x ↦
        min_le_right _ _
  choose k hkm hkc hkk using hk
  refine ⟨fun x ↦ ⨆ n, k n x, Measurable.iSup hkm, fun x ↦ iSup_le fun n ↦ (hkc n x).trans
    (min_le_left _ _), fun h hh hhc ↦ ?_⟩
  have hall : ∀ n : ℕ, (fun x ↦ min (h x) (n : ℝ≥0∞)) ≤ᵐ[μ] k n := fun n ↦
    hkk n _ (hh.min measurable_const) fun x ↦ min_le_min_right _ (hhc x)
  filter_upwards [ae_all_iff.2 hall] with x hx
  rw [← iSup_min_natCast (h x)]
  exact iSup_mono hx

/-- For an s-finite measure `ν` on `β` and a strongly measurable `H : α × β → F` with values in a
normed group, the `L²` seminorm of the slices, `a ↦ eLpNorm (fun y ↦ H (a, y)) 2 ν`, is a
measurable function of `a`. The proof writes the seminorm as `(∫⁻ y, ‖H (a, y)‖ₑ ^ 2 ∂ν) ^ (1 / 2)`
and uses the measurability of lower integrals of slices. -/
theorem measurable_eLpNorm_two_slice {α : Type*} {β : Type*} {F : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup F] {ν : Measure β} [SFinite ν] {H : α × β → F}
    (hH : StronglyMeasurable H) : Measurable fun a ↦ eLpNorm (fun y ↦ H (a, y)) 2 ν := by
  have h : (fun a ↦ eLpNorm (fun y ↦ H (a, y)) 2 ν) =
      fun a ↦ (∫⁻ y, ‖H (a, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    funext a
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (f := fun y ↦ H (a, y)) (by norm_num) (by norm_num)
      (hH.comp_measurable measurable_prodMk_left).aestronglyMeasurable]
    norm_num
  rw [h]
  exact ((hH.eNorm.pow_const _).lintegral_prod_right').pow_const _

/-- Let `X` be a pseudometric space with its Borel σ-algebra, `D : ℕ → X` a sequence with dense
range, and `u : α → X` a map from a measurable space. If `a ↦ dist (u a) (D k)` is measurable for
every `k`, then `u` is measurable. The proof writes the preimage of an open set `U` as the countable
union, over `k` and rational `q` with `Metric.ball (D k) q ⊆ U`, of the sets
`{a | dist (u a) (D k) < q}`. -/
theorem measurable_of_dist_dense {α : Type*} [MeasurableSpace α] {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X]
    [BorelSpace X] {u : α → X} {D : ℕ → X} (hD : DenseRange D)
    (h : ∀ k, Measurable fun a ↦ dist (u a) (D k)) : Measurable u := by
  refine measurable_of_isOpen fun U hU ↦ ?_
  have hU' : u ⁻¹' U = ⋃ k : ℕ, ⋃ q : ℚ,
      {a | dist (u a) (D k) < q} ∩ {_a | Metric.ball (D k) q ⊆ U} := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro ha
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (u a) ha
      obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hD (u a) q hq0
      refine ⟨k, q, hk, fun w hw ↦ hball ?_⟩
      rw [Metric.mem_ball] at hw ⊢
      calc dist w (u a) ≤ dist w (D k) + dist (D k) (u a) := dist_triangle _ _ _
        _ < q + q := add_lt_add hw (by rw [dist_comm]; exact hk)
        _ < ε := by linarith
    · rintro ⟨k, q, hk, hsub⟩
      exact hsub (Metric.mem_ball.2 hk)
  rw [hU']
  exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun q ↦
    (measurableSet_lt (h k) measurable_const).inter (MeasurableSet.const _)

/-- Let `μ` be a measure on a measurable space `α`, `β` a finite type and `V : α → β → ℂ`. If every
component `p ↦ V p j` is a.e. strongly measurable for `μ` and `f : (β → ℂ) → ℝ` is continuous, then
`p ↦ f (V p)` is a.e. strongly measurable for `μ`. -/
theorem aestronglyMeasurable_continuous_comp_pi_of_forall {α β : Type*} [MeasurableSpace α]
    [Finite β]
    {μ : Measure α} {V : α → β → ℂ}
    (hV : ∀ j, AEStronglyMeasurable (fun p ↦ V p j) μ) {f : (β → ℂ) → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable (fun p ↦ f (V p)) μ :=
  (hf.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 fun j ↦
      (hV j).aemeasurable)).aestronglyMeasurable

/-- Let `μ` be a measure on a measurable space `α`, `β` a finite type and `Y : α → β → ℂ`. If every
component `p ↦ Y p j` is a.e. strongly measurable for `μ`, then `Y` is a.e. measurable for `μ`. -/
theorem aemeasurable_pi_of_forall_aestronglyMeasurable {α β : Type*} [MeasurableSpace α]
    [Finite β] (μ : Measure α) (Y : α → β → ℂ)
    (hY : ∀ j, AEStronglyMeasurable (fun p ↦ Y p j) μ) : AEMeasurable Y μ :=
  aemeasurable_pi_iff.2 (fun j ↦ (hY j).aemeasurable)

/-- For every index `i`, the map `r ↦ EuclideanSpace.single i r` from `ℝ` to `ℝ³`, which puts `r` in
coordinate `i` and zero elsewhere, is measurable. It equals `r ↦ r • EuclideanSpace.single i 1`. -/
theorem measurable_euclideanSpace_single (i : Fin 3) : Measurable
    (fun r : ℝ ↦ EuclideanSpace.single i r) := by
  have e : (fun r : ℝ ↦ EuclideanSpace.single i r) = fun r ↦ r •
      EuclideanSpace.single i (1 : ℝ) := by
    funext r
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  exact measurable_id.smul_const _

end PDE.Analysis

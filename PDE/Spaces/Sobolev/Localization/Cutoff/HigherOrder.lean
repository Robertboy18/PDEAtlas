/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Higher-order compactly supported localization

Applying the arbitrary-word transport of `Cutoff.CompactSupport` to every row
of the finite weak Leibniz expansion constructs a localized `W^{k,p}` field
with its exact representatives and quantitative bounds.

The support-extension construction needs no boundary regularity of the larger
domain: all representatives vanish before reaching the boundary of the smaller
open set. The intersection construction instead localizes inside the physical
domain, using the test function's support to avoid crossing its boundary.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.CompactSupportLocalization

open MeasureTheory Set Function ENNReal
open scoped Topology

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace HigherOrderLocalizedCutoff

open SobolevSpace.GraphSpace

omit [Fact (1 ≤ p)] in
private theorem memLp_list_sum {V : Set (ℝ^n)}
    (fs : List (ℝ^n → ℝ))
    (hfs : ∀ f ∈ fs, MemLp f p (domainMeasure n V)) :
    MemLp (fun x ↦ (fs.map fun f ↦ f x).sum) p (domainMeasure n V) := by
  induction fs with
  | nil => simp
  | cons f rest ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_def] using
      (hfs f (by simp)).add (ih fun g hg ↦ hfs g (by simp [hg]))

private theorem eLpNorm_list_sum_le {V : Set (ℝ^n)}
    (fs : List (ℝ^n → ℝ))
    (hfs : ∀ f ∈ fs, MemLp f p (domainMeasure n V)) :
    eLpNorm (fun x ↦ (fs.map fun f ↦ f x).sum) p (domainMeasure n V) ≤
      (fs.map fun f ↦ eLpNorm f p (domainMeasure n V)).sum := by
  induction fs with
  | nil => simp
  | cons f rest ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_def] using
      (eLpNorm_add_le (f := f) (g := fun x ↦ (rest.map fun g ↦ g x).sum) Fact.out).trans
        (add_le_add le_rfl (ih fun g hg ↦ hfs g (by simp [hg])))

private theorem ennreal_list_sum_ne_top {ι : Type*}
    (xs : List ι) (f : ι → ENNReal) (hf : ∀ x ∈ xs, f x ≠ ∞) :
    (xs.map f).sum ≠ ∞ := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.map_cons, List.sum_cons, ENNReal.add_ne_top]
      exact ⟨hf x (by simp), ih (fun y hy ↦ hf y (by simp [hy]))⟩

private theorem memLp_top_iteratedPartialDeriv (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (beta : List (Fin n)) (V : Set (ℝ^n)) :
    MemLp (iteratedPartialDeriv (n := n) beta psi.toFun) ∞ (domainMeasure n V) :=
  (PDE.contDiff_top_iteratedPartialDeriv (n := n) psi.contDiff beta).continuous
    |>.memLp_top_of_hasCompactSupport (iteratedPartialDeriv_hasCompactSupport (n := n) psi beta) _

omit [Fact (1 ≤ p)] in
private theorem leibnizTerm_memLp {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {alpha : List (Fin n)} (halpha : alpha.length ≤ k)
    {q : List (Fin n) × List (Fin n)} (hq : q ∈ derivativeSplits alpha) :
    MemLp (fun x ↦ iteratedPartialDeriv (n := n) q.1 psi.toFun x * wkpWordRepresentative U q.2 x)
      p (domainMeasure n V) :=
  (memLp_top_iteratedPartialDeriv psi q.1 V).fun_mul
    (wkpWordRepresentative_memLp U q.2 (by have := derivativeSplits_length hq; omega))

omit [Fact (1 ≤ p)] in
private theorem expansion_memLp
    {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : List (Fin n))
    (halpha : alpha.length ≤ k) :
    MemLp (weakLeibnizExpansion psi.toFun (wkpWordRepresentative U) alpha)
      p (domainMeasure n V) := by
  unfold weakLeibnizExpansion
  simpa [List.map_map, Function.comp_def] using
    memLp_list_sum ((derivativeSplits alpha).map fun q x ↦
      iteratedPartialDeriv (n := n) q.1 psi.toFun x * wkpWordRepresentative U q.2 x)
      (List.forall_mem_map.2 fun q hq ↦ leibnizTerm_memLp U psi halpha hq)

omit [Fact (1 ≤ p)] in
/-- Every weak Leibniz row of a cutoff product is supported in the cutoff. -/
theorem weakLeibnizExpansion_support
    {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : List (Fin n)) :
    Function.support
        (weakLeibnizExpansion psi.toFun (wkpWordRepresentative U) alpha) ⊆
      tsupport psi.toFun := by
  classical
  intro x hx
  by_contra hxK
  refine hx (List.sum_eq_zero fun term hterm ↦ ?_)
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hterm
  rw [image_eq_zero_of_notMem_tsupport fun h ↦
    hxK (tsupport_iteratedPartialDeriv_subset_tsupport (n := n) q.1 psi.toFun h), zero_mul]

omit [Fact (1 ≤ p)] in
/--
An almost-everywhere representative of a weak cutoff Leibniz row vanishes
outside the cutoff support.
-/
theorem indicator_eq_self_of_ae_eq_weakLeibnizExpansion
    {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : List (Fin n))
    (f : ℝ^n → ℝ)
    (hf : f =ᵐ[domainMeasure n V]
      weakLeibnizExpansion psi.toFun (wkpWordRepresentative U) alpha) :
    (tsupport psi.toFun).indicator f =ᵐ[domainMeasure n V] f := by
  filter_upwards [hf] with x hx
  by_cases hxK : x ∈ tsupport psi.toFun
  · exact indicator_of_mem hxK f
  · rw [indicator_of_notMem hxK, hx, notMem_support.1 fun h ↦
      hxK (weakLeibnizExpansion_support U psi alpha h)]

/-- The explicit finite `Lᵖ` bound associated with the weak Leibniz
expansion for a cutoff derivative word. -/
noncomputable def cutoffLeibnizENormBound
    {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : List (Fin n)) : ENNReal :=
  ((derivativeSplits alpha).map fun split ↦
    eLpNorm (iteratedPartialDeriv (n := n) split.1 psi.toFun) ∞
        (domainMeasure n V) *
      eLpNorm (wkpWordRepresentative U split.2) p
        (domainMeasure n V)).sum

/-- Triangle and `L∞ × Lᵖ` multiplier estimate for the exact finite weak
Leibniz expansion. -/
theorem eLpNorm_weakLeibnizExpansion_le
    {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : List (Fin n))
    (halpha : alpha.length ≤ k) :
    eLpNorm (weakLeibnizExpansion psi.toFun (wkpWordRepresentative U) alpha)
        p (domainMeasure n V) ≤
      cutoffLeibnizENormBound U psi alpha := by
  classical
  let fs : List (ℝ^n → ℝ) := (derivativeSplits alpha).map fun q x ↦
    iteratedPartialDeriv (n := n) q.1 psi.toFun x * wkpWordRepresentative U q.2 x
  have htriangle := eLpNorm_list_sum_le fs
    (List.forall_mem_map.2 fun q hq ↦ leibnizTerm_memLp U psi halpha hq)
  simp only [fs, List.map_map, Function.comp_def] at htriangle
  refine htriangle.trans (List.sum_le_sum fun split _ ↦ ?_)
  simpa only [ENNReal.coe_one, one_mul] using
    eLpNorm_le_eLpNorm_top_mul_eLpNorm_of_pos
      (μ := domainMeasure n V)
      (f := iteratedPartialDeriv (n := n) split.1 psi.toFun)
      (g := wkpWordRepresentative U split.2) p
      (fun x y : ℝ ↦ x * y) 1 continuous_mul
      (Filter.Eventually.of_forall fun _ ↦ by simp [nnnorm_mul])
      (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))

omit [Fact (1 ≤ p)] in
/-- Every term in the finite cutoff Leibniz bound has finite extended `L^p` norm. -/
theorem cutoffLeibnizENormBound_ne_top
    {V : Set (ℝ^n)} (U : W^{k,p}(V))
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (alpha : List (Fin n))
    (halpha : alpha.length ≤ k) :
    cutoffLeibnizENormBound U psi alpha ≠ ∞ := by
  classical
  exact ennreal_list_sum_ne_top _ _ fun q hq ↦ ENNReal.mul_ne_top
    (memLp_top_iteratedPartialDeriv psi q.1 V).eLpNorm_ne_top
    (wkpWordRepresentative_memLp U q.2
      (by have := derivativeSplits_length hq; omega)).eLpNorm_ne_top

omit [Fact (1 ≤ p)] in
/-- The `W^{k,p}(Ω)` field with base coordinate `psi * u` and the weak Leibniz rows of `psi * U`,
once these rows lie in `Lᵖ(Ω)` and are the weak derivatives of `psi * u` on `Ω`. -/
private theorem exists_of_leibnizRows {V Ω : Set (ℝ^n)} (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,p}(V))
    (hmem : ∀ a : DerivIndex n k, MemLp (weakLeibnizExpansion psi.toFun
      (wkpWordRepresentative U) a.toList.reverse) p (domainMeasure n Ω))
    (hweak : ∀ a : DerivIndex n k, HasWeakDerivativeOn (n := n) Ω a.toList
      (fun x ↦ psi.toFun x * ((U : WkpAmbientOn n k p V) (baseIndex n k) : ℝ^n → ℝ) x)
      (weakLeibnizExpansion psi.toFun (wkpWordRepresentative U) a.toList.reverse)) :
    ∃ W : W^{k,p}(Ω),
      (((((W : WkpAmbientOn n k p Ω) (baseIndex n k) :
          DerivLp n p Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x) ∧
      ∀ a : DerivIndex n k,
        ((((W : WkpAmbientOn n k p Ω) a :
            DerivLp n p Ω) : ℝ^n → ℝ))
          =ᵐ[domainMeasure n Ω]
            weakLeibnizExpansion psi.toFun (wkpWordRepresentative U)
              a.toList.reverse := by
  have hbase : weakLeibnizExpansion psi.toFun (wkpWordRepresentative U)
      (baseIndex n k).toList.reverse =
        fun x ↦ psi.toFun x * ((U : WkpAmbientOn n k p V) (baseIndex n k) : ℝ^n → ℝ) x := by
    simp [weakLeibnizExpansion_nil]
  let d (a : DerivIndex n k) : ℝ^n → ℝ :=
    weakLeibnizExpansion psi.toFun (wkpWordRepresentative U) a.toList.reverse
  exact ⟨_, (mkWkpSpaceOnOfWeakDerivatives_apply_ae _ d hbase hmem hweak _).trans (.of_eq hbase),
    mkWkpSpaceOnOfWeakDerivatives_apply_ae _ d hbase hmem hweak⟩

/--
Multiplication by a smooth compactly supported function preserves
`W^{k,p}` on the same domain, with every weak-derivative row represented by
the finite Leibniz formula. No support relation between the multiplier and
the domain is needed because no extension across the domain boundary occurs.
-/
theorem exists_wkpSpaceOn_mul_testFunction_sameDomain_with_rows
    {V : Set (ℝ^n)} (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,p}(V)) :
    ∃ W : W^{k,p}(V),
      (((((W : WkpAmbientOn n k p V) (baseIndex n k) :
          DerivLp n p V) : ℝ^n → ℝ)) =ᵐ[domainMeasure n V]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x) ∧
      ∀ a : DerivIndex n k,
        ((((W : WkpAmbientOn n k p V) a :
            DerivLp n p V) : ℝ^n → ℝ))
          =ᵐ[domainMeasure n V]
            weakLeibnizExpansion psi.toFun (wkpWordRepresentative U)
              a.toList.reverse := by
  classical
  exact exists_of_leibnizRows psi U
    (fun a ↦ expansion_memLp U psi _ (by simpa using a.toList_length_le))
    (fun a ↦ U.hasWeakDerivativeOn_mul_smooth psi.toFun psi.contDiff
      (fun beta _ ↦ memLp_top_iteratedPartialDeriv psi beta V) a.toList a.toList_length_le)

/-- Base-coordinate form of same-domain multiplication by a test function. -/
theorem exists_wkpSpaceOn_mul_testFunction_sameDomain
    {V : Set (ℝ^n)} (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,p}(V)) :
    ∃ W : W^{k,p}(V),
      ((((W : WkpAmbientOn n k p V) (baseIndex n k) :
          DerivLp n p V) : ℝ^n → ℝ)) =ᵐ[domainMeasure n V]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x := by
  obtain ⟨W, hWbase, _hWrows⟩ :=
    exists_wkpSpaceOn_mul_testFunction_sameDomain_with_rows
      (n := n) (k := k) (p := p) psi U
  exact ⟨W, hWbase⟩

/-- A smooth compactly supported multiplier extends a local `W^{k,p}` field
to every larger domain, with every weak-derivative row represented by the
exact finite Leibniz formula.

The first conclusion records the base coordinate as `psi * u`; the second
exposes all higher rows for quantitative estimates and subsequent coordinate
changes.
-/
theorem exists_wkpSpaceOn_mul_testFunction_with_rows
    {V OmegaBig : Set (ℝ^n)} (hV : IsOpen V) (hVbig : V ⊆ OmegaBig)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    ∃ W : W^{k,p}(OmegaBig),
      (((((W : WkpAmbientOn n k p OmegaBig) (baseIndex n k) :
          DerivLp n p OmegaBig) : ℝ^n → ℝ)) =ᵐ[domainMeasure n OmegaBig]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x) ∧
      ∀ a : DerivIndex n k,
        ((((W : WkpAmbientOn n k p OmegaBig) a :
            DerivLp n p OmegaBig) : ℝ^n → ℝ))
          =ᵐ[domainMeasure n OmegaBig]
            weakLeibnizExpansion psi.toFun (wkpWordRepresentative U)
              a.toList.reverse := by
  classical
  obtain ⟨chi, hchiV, -, hchiNhds, -⟩ :=
    TestFunction.exists_eq_one_on_compact hV psi.hasCompactSupport hpsiV
  refine exists_of_leibnizRows psi U (fun a ↦ ?_) fun a ↦ ?_
  · exact memLp_of_support_subset_of_subset hV.measurableSet hVbig
      ((weakLeibnizExpansion_support U psi _).trans hpsiV)
      (expansion_memLp U psi _ (by simpa using a.toList_length_le))
  · exact hasWeakDerivativeOn_word_of_support_subset_of_cutoff_one_nhds hV hVbig hpsiV a.toList
      ((support_mul_subset_left _ _).trans (subset_tsupport _))
      (weakLeibnizExpansion_support U psi _) chi hchiV hchiNhds
      (U.hasWeakDerivativeOn_mul_smooth psi.toFun psi.contDiff
        (fun beta _ ↦ memLp_top_iteratedPartialDeriv psi beta V) a.toList a.toList_length_le)

/-- Base-coordinate form of compactly supported higher-order localization. -/
theorem exists_wkpSpaceOn_mul_testFunction
    {V OmegaBig : Set (ℝ^n)} (hV : IsOpen V) (hVbig : V ⊆ OmegaBig)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    ∃ W : W^{k,p}(OmegaBig),
      ((((W : WkpAmbientOn n k p OmegaBig) (baseIndex n k) :
          DerivLp n p OmegaBig) : ℝ^n → ℝ)) =ᵐ[domainMeasure n OmegaBig]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x := by
  obtain ⟨W, hWbase, _hWrows⟩ :=
    exists_wkpSpaceOn_mul_testFunction_with_rows hV hVbig psi hpsiV U
  exact ⟨W, hWbase⟩

/-- Boundary-relative higher-order localization with its exact weak Leibniz rows.

If `U` is defined on `V ∩ Ω` and the smooth multiplier is supported in
the chart neighborhood `V`, then `psi * U` defines a Sobolev field on
`Ω`. No extension through the boundary of `Ω` is performed. -/
theorem exists_wkpSpaceOn_mul_testFunction_inter_with_rows
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hOmega : IsOpen Ω)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    ∃ W : W^{k,p}(Ω),
      (((((W : WkpAmbientOn n k p Ω) (baseIndex n k) :
          DerivLp n p Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p (V ∩ Ω)) (baseIndex n k) :
            DerivLp n p (V ∩ Ω)) : ℝ^n → ℝ) x) ∧
      ∀ a : DerivIndex n k,
        ((((W : WkpAmbientOn n k p Ω) a :
            DerivLp n p Ω) : ℝ^n → ℝ))
          =ᵐ[domainMeasure n Ω]
            weakLeibnizExpansion psi.toFun (wkpWordRepresentative U)
              a.toList.reverse := by
  classical
  obtain ⟨chi, hchiV, -, hchiNhds, -⟩ :=
    TestFunction.exists_eq_one_on_compact hV psi.hasCompactSupport hpsiV
  -- the rows vanish off `tsupport psi ⊆ V`, so integrability on `V ∩ Ω` transfers to `Ω`
  have hmem (a : DerivIndex n k) : MemLp (weakLeibnizExpansion psi.toFun
      (wkpWordRepresentative U) a.toList.reverse) p (domainMeasure n Ω) := by
    rw [← indicator_eq_self.2 ((weakLeibnizExpansion_support U psi _).trans hpsiV),
      memLp_indicator_iff_restrict hV.measurableSet.nullMeasurableSet, domainMeasure,
      Measure.restrict_restrict hV.measurableSet]
    exact expansion_memLp U psi _ (by simpa using a.toList_length_le)
  refine exists_of_leibnizRows psi U hmem fun a ↦ ?_
  exact hasWeakDerivativeOn_word_of_inter_of_cutoff_one_nhds hV hOmega a.toList
    ((support_mul_subset_left _ _).trans (subset_tsupport _))
    (weakLeibnizExpansion_support U psi _) chi hchiV hchiNhds
    (by simpa using hmem (baseIndex n k)) (hmem a)
    (U.hasWeakDerivativeOn_mul_smooth psi.toFun psi.contDiff
      (fun beta _ ↦ memLp_top_iteratedPartialDeriv psi beta (V ∩ Ω)) a.toList
      a.toList_length_le)

/-- Base-coordinate form of boundary-relative higher-order localization. -/
theorem exists_wkpSpaceOn_mul_testFunction_inter
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hOmega : IsOpen Ω)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    ∃ W : W^{k,p}(Ω),
      ((((W : WkpAmbientOn n k p Ω) (baseIndex n k) :
          DerivLp n p Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p (V ∩ Ω)) (baseIndex n k) :
            DerivLp n p (V ∩ Ω)) : ℝ^n → ℝ) x := by
  obtain ⟨W, hWbase, _hWrows⟩ :=
    exists_wkpSpaceOn_mul_testFunction_inter_with_rows
      (n := n) (k := k) (p := p) hV hOmega psi hpsiV U
  exact ⟨W, hWbase⟩

/-- Norm-level form of compactly supported higher-order localization. Each
coordinate norm is exactly the concrete `Lᵖ` seminorm of its finite weak
Leibniz representative on the larger domain. -/
theorem exists_wkpSpaceOn_mul_testFunction_with_row_norms
    {V OmegaBig : Set (ℝ^n)} (hV : IsOpen V) (hVbig : V ⊆ OmegaBig)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    ∃ W : W^{k,p}(OmegaBig),
      (((((W : WkpAmbientOn n k p OmegaBig) (baseIndex n k) :
          DerivLp n p OmegaBig) : ℝ^n → ℝ)) =ᵐ[domainMeasure n OmegaBig]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x) ∧
      ∀ a : DerivIndex n k,
        ‖((W : WkpAmbientOn n k p OmegaBig) a :
          DerivLp n p OmegaBig)‖ =
          ENNReal.toReal (eLpNorm
            (weakLeibnizExpansion psi.toFun (wkpWordRepresentative U)
              a.toList.reverse)
            p (domainMeasure n OmegaBig)) := by
  obtain ⟨W, hWbase, hWrows⟩ :=
    exists_wkpSpaceOn_mul_testFunction_with_rows hV hVbig psi hpsiV U
  refine ⟨W, hWbase, ?_⟩
  intro a
  rw [MeasureTheory.Lp.norm_def]
  congr 1
  exact eLpNorm_congr_ae (hWrows a)

/-- Fully quantitative compact-support localization. The norm of every
derivative row is bounded by the explicit finite sum of
`L∞` cutoff-derivative norms times the corresponding local `Lᵖ` Sobolev-row
norms. -/
theorem exists_wkpSpaceOn_mul_testFunction_with_norm_bounds
    {V OmegaBig : Set (ℝ^n)} (hV : IsOpen V) (hVbig : V ⊆ OmegaBig)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    ∃ W : W^{k,p}(OmegaBig),
      (((((W : WkpAmbientOn n k p OmegaBig) (baseIndex n k) :
          DerivLp n p OmegaBig) : ℝ^n → ℝ)) =ᵐ[domainMeasure n OmegaBig]
        fun x ↦ psi.toFun x *
          (((U : WkpAmbientOn n k p V) (baseIndex n k) :
            DerivLp n p V) : ℝ^n → ℝ) x) ∧
      ∀ a : DerivIndex n k,
        ‖((W : WkpAmbientOn n k p OmegaBig) a :
          DerivLp n p OmegaBig)‖ ≤
          (cutoffLeibnizENormBound U psi a.toList.reverse).toReal := by
  obtain ⟨W, hWbase, hWnorm⟩ :=
    exists_wkpSpaceOn_mul_testFunction_with_row_norms hV hVbig psi hpsiV U
  refine ⟨W, hWbase, fun a ↦ ?_⟩
  have halpha : a.toList.reverse.length ≤ k := by simpa using a.toList_length_le
  have hsupp := (weakLeibnizExpansion_support U psi a.toList.reverse).trans hpsiV
  rw [hWnorm a, ← eLpNorm_restrict_eq_of_support_subset (memLp_of_support_subset_of_subset
      hV.measurableSet hVbig hsupp (expansion_memLp U psi _ halpha)).aestronglyMeasurable hsupp,
    domainMeasure, Measure.restrict_restrict_of_subset hVbig]
  exact ENNReal.toReal_mono (cutoffLeibnizENormBound_ne_top U psi _ halpha)
    (eLpNorm_weakLeibnizExpansion_le U psi _ halpha)

end HigherOrderLocalizedCutoff
end SobolevSpace.CompactSupportLocalization

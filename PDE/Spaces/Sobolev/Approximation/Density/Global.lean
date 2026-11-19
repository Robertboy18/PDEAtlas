/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge

/-!
# Global density in Sobolev graph spaces

Smooth compactly supported functions are dense in `W^{k,p}(ℝ^n)` for `1 ≤ p < ∞`. We
state that theorem for the graph-space encoding `WkpSpace n k p`, in which an element is the
finite `PiLp` tuple of its weak derivatives up to order `k`, each stored as an `Lᵖ` class. The
analytic work (mollification plus an expanding cutoff) is done in
`Approximation.globalApproximation_Wkp`; here we transport it to the graph norm and draw the
standard consequences.

Convergence in the graph norm is checked coordinate by coordinate. For a fixed multi-index `a`
the classical derivative `∂^a f_m` of a smooth approximant agrees a.e. with the `a`-th coordinate
of `mkWkpSpaceOnOfContDiff f_m`, and uniqueness of weak derivatives on an open set identifies the
limit supplied by the approximation theorem with the stored coordinate of the target. The
finiteness of `p` is needed by the underlying approximation theorem and again to write the
`PiLp` norm as a `p`-th power sum of coordinate norms.

## Main results

* `globalApproximation_WkpSpace`: for `p ≠ ∞`, every `U : WkpSpace n k p` is the limit in norm of
  `mkWkpSpaceOnOfContDiff f_m` for a sequence of smooth compactly supported `f_m`.
* `WkpSpaceOn.ext_of_base_ae`: on an open domain a graph-space element is determined by the a.e.
  class of its base coordinate, by uniqueness of weak derivatives.
* `exists_boundedLift_of_smoothCore`, `exists_boundedRepresentative_of_smoothCore`: a map defined
  on the smooth compactly supported core with a Lipschitz bound in the `W^{k,p}` norm extends to
  all of `WkpSpace n k p` with values in a complete normed space, preserving continuous
  observations (resp. continuous point evaluations). This is the abstract completion principle
  behind bounded embeddings into Banach function spaces.
* `mollify_tendsto_globalH1Space_of_base_ae`: for a compactly supported `H¹(ℝ^n)` element, plain
  mollification already converges in the full `H¹` norm; no cutoff is needed.

## Implementation notes

The finite-exponent hypothesis `hp : p ≠ ∞` is explicit throughout. Density on a domain through
an extension operator is proved separately in `Approximation.Density.ExtensionDomain`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.1, Theorem 1, pp. 264-265, for the local approximation
  `η_ε * u → u` in `W^{k,p}_loc(U)`, `1 ≤ p < ∞`.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for the density of `C_c^∞(ℝ^N)` in `W^{1,p}(ℝ^N)`.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace GraphSpace

section Density

open scoped Topology

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- In a finite `PiLp p` product with `p < ∞`, a sequence tends to zero in norm as soon as each
coordinate does. This is the elementary step that reduces graph-space convergence to coordinatewise
`Lᵖ` convergence. -/
theorem tendsto_piLp_norm_of_forall {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {x : ℕ → PiLp p β}
    (h : ∀ i, Filter.Tendsto (fun m ↦ ‖x m i‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m ↦ ‖x m‖) Filter.atTop (𝓝 0) := by
  have hp0 : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 hp
  have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ (h i).rpow_const (Or.inr hp0.le)
  simpa [PiLp.norm_eq_sum hp0, Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')] using
    hsum.rpow_const (p := p.toReal⁻¹) (Or.inr (by positivity))

omit [Fact (1 ≤ p)] in
/-- Coordinate convergence for smooth approximants. If the classical derivatives `∂^a f_m`
converge to `g` in `eLpNorm`, then the `a`-th coordinate of the graph-space element
`mkWkpSpaceOnOfContDiff (f_m m)` converges to `g` in the `Lᵖ` norm. The point is that this
coordinate agrees a.e. with the classical derivative, so nothing beyond
`Lp.norm_def` is involved. -/
theorem tendsto_coord_from_eLpNorm {Ω : Set (ℝ^n)} (a : DerivIndex n k)
    {f_m : ℕ → ℝ^n → ℝ} {g : MeasureTheory.Lp ℝ p (domainMeasure n Ω)}
    (hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m)) (hcs_m : ∀ m, HasCompactSupport (f_m m))
    (h :
      Filter.Tendsto
        (fun m ↦
          MeasureTheory.eLpNorm (fun x ↦ iteratedPartialDeriv (n := n) a.toList (f_m m) x - g x) p
            (domainMeasure n Ω))
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun m ↦
        ‖((mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p) (Ω := Ω)
              (f := f_m m) (hf_m m) (hcs_m m) :
              WkpAmbientOn n k p Ω) a -
            g)‖)
      Filter.atTop (𝓝 0) := by
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h'
  refine h'.congr fun m ↦ ?_
  -- the approximant coordinate agrees a.e. with its classical derivative
  rw [Function.comp_apply, Lp.norm_def]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
    ((mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := k) (p := p) (Ω := Ω) (f := f_m m)
      (hf := hf_m m) (hcs := hcs_m m) a).sub (ae_eq_refl _))).symm)

omit [Fact (1 ≤ p)] in
/-- On an open domain, a Sobolev graph-space element is determined by its
base `Lᵖ` representative. All derivative coordinates then agree by
uniqueness of weak derivatives. -/
theorem WkpSpaceOn.ext_of_base_ae
    {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω)
    (U V : W^{k,p}(Ω))
    (hbase :
      (((U : WkpAmbientOn n k p Ω) (baseIndex n k) :
          DerivLp n p Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        (((V : WkpAmbientOn n k p Ω) (baseIndex n k) :
          DerivLp n p Ω) : ℝ^n → ℝ)) :
    U = V := by
  refine Subtype.ext (PiLp.ext fun a ↦ Lp.ext ?_)
  have hU : HasWeakDerivativeOn (n := n) Ω a.toList
      ((U : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω)
      ((U : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) := by simpa using U.property a
  have hV : HasWeakDerivativeOn (n := n) Ω a.toList
      ((V : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω)
      ((V : WkpAmbientOn n k p Ω) a : DerivLp n p Ω) := by simpa using V.property a
  exact hU.unique_ae hΩopen ((hasWeakDerivativeOn_congr_ae hbase (ae_eq_refl _)).2 hV)

/-- Whole-space Sobolev density in the graph-space representative norm:
smooth compactly supported representatives are dense in `WkpSpace n k p` on
`ℝ^n`.

This is `Approximation.globalApproximation_Wkp` restated as convergence in the finite `PiLp`
norm used by `WkpSpace`. -/
theorem globalApproximation_WkpSpace (μ : Approximation.Mollifier n) (hp : p ≠ ∞) (k : ℕ) :
    ∀ U : W^{k,p}(ℝ^n),
      ∃ f_m : ℕ → (ℝ^n → ℝ),
      ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
      ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
        Filter.Tendsto
          (fun m ↦
            ‖(mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p)
                  (Ω := (Set.univ : Set (ℝ^n)))
                  (f := f_m m) (hf := hf_m m) (hcs := hcs_m m) - U)‖)
          Filter.atTop (𝓝 0) := by
  intro U
  let u : SobolevSpaceOn n k p Set.univ :=
    toRepresentative (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n))) U
  obtain ⟨u_m, hsmooth, hcs, -, hDeriv⟩ :=
    Approximation.globalApproximation_Wkp (n := n) (μ := μ) (p := p) hp k u
  refine ⟨u_m, hsmooth, hcs, ?_⟩
  -- It suffices to prove convergence in every coordinate of the finite `PiLp` product.
  have hcoord (a : DerivIndex n k) :
      Filter.Tendsto
        (fun m ↦
          ‖((mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n)))
                (f := u_m m) (hsmooth m) (hcs m) : WkpAmbientOn n k p Set.univ) a -
              (U : WkpAmbientOn n k p Set.univ) a)‖)
        Filter.atTop (𝓝 0) := by
    obtain ⟨g, -, hweak, htend⟩ := hDeriv a.toList a.toList_length_le
    -- Uniqueness identifies the derivative supplied by approximation with the stored coordinate.
    have hUweak : HasWeakDerivativeOn (n := n) Set.univ a.toList u.toFun
        ((U : WkpAmbientOn n k p Set.univ) a) := by
      simpa [u, toRepresentative] using U.property a
    have hg : g =ᵐ[volume] ((U : WkpAmbientOn n k p Set.univ) a : ℝ^n → ℝ) := by
      simpa using hweak.unique_ae isOpen_univ hUweak
    refine tendsto_coord_from_eLpNorm a hsmooth hcs (htend.congr fun m ↦ ?_)
    simp only [domainMeasure, Measure.restrict_univ]
    exact eLpNorm_congr_ae (by filter_upwards [hg] with x hx; rw [hx])
  -- The Sobolev subtype inherits its norm from the ambient `PiLp` space.
  simpa using tendsto_piLp_norm_of_forall hp (x := fun m ↦
    (mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n)))
      (f := u_m m) (hsmooth m) (hcs m) : WkpAmbientOn n k p Set.univ) -
        (U : WkpAmbientOn n k p Set.univ)) fun a ↦ by simpa using hcoord a

/-- If the distances and norms of `v` are controlled by `C` times those of a convergent sequence
`u → U`, then `v` converges in a complete space to some `F` with `‖F‖ ≤ C ‖U‖`. -/
private theorem exists_tendsto_of_dist_le_mul {X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {u : ℕ → X} {U : X} {v : ℕ → Y} {C : ℝ}
    (hC : 0 ≤ C) (hu : Filter.Tendsto u Filter.atTop (𝓝 U))
    (hdist : ∀ m j, dist (v m) (v j) ≤ C * dist (u m) (u j)) (hnorm : ∀ m, ‖v m‖ ≤ C * ‖u m‖) :
    ∃ F, Filter.Tendsto v Filter.atTop (𝓝 F) ∧ ‖F‖ ≤ C * ‖U‖ := by
  have hv : CauchySeq v := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm j hj ↦ (hdist m j).trans_lt ?_⟩
    calc C * dist (u m) (u j) ≤ C * (ε / (C + 1)) := by gcongr; exact (hN m hm j hj).le
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; linarith
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hv
  exact ⟨F, hF, le_of_tendsto_of_tendsto' hF.norm (tendsto_const_nhds.mul hu.norm) hnorm⟩

/-- A bounded lift of the smooth compactly supported core into a complete
normed space extends to every global Sobolev element, while preserving any
compatible continuous observation.

This is the Banach-valued completion principle behind the more concrete
pointwise representative theorem below. -/
theorem exists_boundedLift_of_smoothCore
    {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (μ : Approximation.Mollifier n) (hp : p ≠ ∞) (k : ℕ)
    (lift :
      (f : ℝ^n → ℝ) →
        ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → Y)
    (source : W^{k,p}(ℝ^n) →L[ℝ] Z)
    (observe : Y →L[ℝ] Z)
    (C : ℝ) (hC : 0 ≤ C)
    (hlift_observe :
      ∀ (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hcs : HasCompactSupport f),
        observe (lift f hf hcs) =
          source (mkWkpSpaceOnOfContDiff
            (n := n) (k := k) (p := p)
            (Ω := (Set.univ : Set (ℝ^n))) f hf hcs))
    (hlift_dist :
      ∀ (f g : ℝ^n → ℝ)
        (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hg : ContDiff ℝ (⊤ : ℕ∞) g)
        (hfcs : HasCompactSupport f)
        (hgcs : HasCompactSupport g),
        dist (lift f hf hfcs) (lift g hg hgcs) ≤
          C * dist
            (mkWkpSpaceOnOfContDiff
              (n := n) (k := k) (p := p)
              (Ω := (Set.univ : Set (ℝ^n))) f hf hfcs)
            (mkWkpSpaceOnOfContDiff
              (n := n) (k := k) (p := p)
              (Ω := (Set.univ : Set (ℝ^n))) g hg hgcs))
    (hlift_norm :
      ∀ (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hcs : HasCompactSupport f),
        ‖lift f hf hcs‖ ≤
          C * ‖mkWkpSpaceOnOfContDiff
            (n := n) (k := k) (p := p)
            (Ω := (Set.univ : Set (ℝ^n))) f hf hcs‖)
    (U : W^{k,p}(ℝ^n)) :
    ∃ F : Y, observe F = source U ∧ ‖F‖ ≤ C * ‖U‖ := by
  obtain ⟨f_m, hf_m, hcs_m, hU_norm⟩ := globalApproximation_WkpSpace μ hp k U
  have hU := tendsto_iff_norm_sub_tendsto_zero.mpr hU_norm
  obtain ⟨F, hF, hbound⟩ := exists_tendsto_of_dist_le_mul hC hU
    (fun m j ↦ hlift_dist _ _ _ _ _ _) fun m ↦ hlift_norm _ _ _
  refine ⟨F, tendsto_nhds_unique ?_ ((source.continuous.tendsto U).comp hU), hbound⟩
  exact ((observe.continuous.tendsto F).comp hF).congr fun m ↦ hlift_observe _ _ _

/-- A bounded lift of the smooth compactly supported core into a complete
function space extends to every global Sobolev element.

The target is kept abstract: it only needs continuous point evaluations.
Consequently, the same density argument applies to Hölder spaces, bounded
continuous functions, and other Banach function spaces. -/
theorem exists_boundedRepresentative_of_smoothCore
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Approximation.Mollifier n) (hp : p ≠ ∞) (k : ℕ)
    (lift :
      (f : ℝ^n → ℝ) →
        ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → Y)
    (eval : ℝ^n → Y →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hlift_apply :
      ∀ (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hcs : HasCompactSupport f) (x : ℝ^n),
        eval x (lift f hf hcs) = f x)
    (hlift_dist :
      ∀ (f g : ℝ^n → ℝ)
        (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hg : ContDiff ℝ (⊤ : ℕ∞) g)
        (hfcs : HasCompactSupport f)
        (hgcs : HasCompactSupport g),
        dist (lift f hf hfcs) (lift g hg hgcs) ≤
          C * dist
            (mkWkpSpaceOnOfContDiff
              (n := n) (k := k) (p := p)
              (Ω := (Set.univ : Set (ℝ^n))) f hf hfcs)
            (mkWkpSpaceOnOfContDiff
              (n := n) (k := k) (p := p)
              (Ω := (Set.univ : Set (ℝ^n))) g hg hgcs))
    (hlift_norm :
      ∀ (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hcs : HasCompactSupport f),
        ‖lift f hf hcs‖ ≤
          C * ‖mkWkpSpaceOnOfContDiff
            (n := n) (k := k) (p := p)
            (Ω := (Set.univ : Set (ℝ^n))) f hf hcs‖)
    (U : W^{k,p}(ℝ^n)) :
    ∃ F : Y,
      (fun x ↦ eval x F) =ᵐ[MeasureTheory.volume]
        (((U : WkpAmbientOn n k p Set.univ) (baseIndex n k) :
          DerivLp n p Set.univ) : ℝ^n → ℝ) ∧
      ‖F‖ ≤ C * ‖U‖ := by
  obtain ⟨f_m, hf_m, hcs_m, hU_norm⟩ := globalApproximation_WkpSpace μ hp k U
  have hU := tendsto_iff_norm_sub_tendsto_zero.mpr hU_norm
  obtain ⟨F, hF, hbound⟩ := exists_tendsto_of_dist_le_mul hC hU
    (fun m j ↦ hlift_dist _ _ _ _ _ _) fun m ↦ hlift_norm _ _ _
  refine ⟨F, ?_, hbound⟩
  let baseProj : W^{k,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
    (PiLp.proj (𝕜 := ℝ) (p := p) (β := fun _ : DerivIndex n k ↦ DerivLp n p Set.univ)
      (baseIndex n k)).comp (wkpSubmoduleOn n k p Set.univ).subtypeL
  -- The base coordinates converge in `Lᵖ`, hence almost everywhere along a subsequence.
  obtain ⟨ns, hns, hbase⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((baseProj.continuous.tendsto U).comp hU)).exists_seq_tendsto_ae
  simp only [domainMeasure, Measure.restrict_univ] at hbase
  -- The base coordinate of a smooth approximant is the approximant itself.
  have hsmooth (m : ℕ) : (baseProj (mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p)
      (Ω := (Set.univ : Set (ℝ^n))) (f_m m) (hf_m m) (hcs_m m)) : ℝ^n → ℝ) =ᵐ[volume] f_m m := by
    simpa [baseProj, domainMeasure, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n)))
        (f_m m) (hf_m m) (hcs_m m) (baseIndex n k)
  filter_upwards [hbase, ae_all_iff.2 hsmooth] with x hx hxm
  refine tendsto_nhds_unique ?_ (hx.congr fun i ↦ hxm (ns i))
  exact (((eval x).continuous.tendsto F).comp (hF.comp hns.tendsto_atTop)).congr fun i ↦
    hlift_apply _ _ _ x

/-- Direct mollification of a compactly supported global `H¹(ℝ^n)` function
converges in the full `H¹` norm.  Unlike the general global density theorem,
no expanding cutoff is needed, so the support remains in an arbitrarily small
collar of the original support. -/
theorem mollify_tendsto_globalH1Space_of_base_ae
    (μ : Approximation.Mollifier n) (U : W^{1,2}(ℝ^n))
    (f : ℝ^n → ℝ)
    (hUbase :
      ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f)
    (hUcs : HasCompactSupport f)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    ∃ (f_m : ℕ → ℝ^n → ℝ)
      (hf_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m))
      (hf_cs : ∀ m, HasCompactSupport (f_m m)),
      (∀ m, f_m m = Approximation.mollify μ (ε m) f) ∧
      Filter.Tendsto
        (fun m ↦ mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2)
          (Ω := (Set.univ : Set (ℝ^n)))
          (f_m m) (hf_smooth m) (hf_cs m))
        Filter.atTop (𝓝 U) := by
  let f_m : ℕ → ℝ^n → ℝ := fun m ↦ Approximation.mollify μ (ε m) f
  have hfLp : MemLp f 2 (volume : Measure (ℝ^n)) := (memLp_congr_ae hUbase).mp <| by
    simpa [domainMeasure] using Lp.memLp ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))
  have hfLoc : LocallyIntegrable f (volume : Measure (ℝ^n)) := hfLp.locallyIntegrable (by norm_num)
  have hf_smooth (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f_m m) :=
    Approximation.mollify_contDiff_of_pos μ (hεpos m) f hfLoc
  have hf_cs (m : ℕ) : HasCompactSupport (f_m m) := by
    simpa [f_m, Approximation.mollify] using
      (Approximation.scaled_hasCompactSupport μ (hεpos m)).convolution
        (ContinuousLinearMap.lsmul ℝ ℝ) hUcs
  refine ⟨f_m, hf_smooth, hf_cs, fun m ↦ rfl, ?_⟩
  have hcoord (a : DerivIndex n 1) :
      Filter.Tendsto
        (fun m ↦
          ‖((mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := (Set.univ : Set (ℝ^n)))
                (f_m m) (hf_smooth m) (hf_cs m) : WkpAmbientOn n 1 2 Set.univ) a -
              (U : WkpAmbientOn n 1 2 Set.univ) a)‖)
        Filter.atTop (𝓝 0) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · refine tendsto_coord_from_eLpNorm (baseIndex n 1) hf_smooth hf_cs
        ((Approximation.mollify_converges_Lp μ 2 (by norm_num) ε hεpos hε0 hfLp).congr fun m ↦ ?_)
      simp only [baseIndex_toList, iteratedPartialDeriv, f_m, domainMeasure,
        Measure.restrict_univ]
      exact eLpNorm_congr_ae (by filter_upwards [hUbase] with x hx; rw [hx])
    · let g : ℝ^n → ℝ :=
        ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i) : DerivLp n 2 Set.univ)
      have hgLp : MemLp g 2 (volume : Measure (ℝ^n)) := by
        simpa [g, domainMeasure] using
          Lp.memLp ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))
      -- The weak derivative of `f` is the stored coordinate `g`, so it commutes with mollification.
      have hfweak : HasWeakDerivativeOn (n := n) Set.univ [i] f g :=
        (hasWeakDerivativeOn_congr_ae (n := n) (Ω := Set.univ) (α := [i])
          (by simpa [domainMeasure] using hUbase) (ae_eq_refl _)).1
            (by simpa [g, firstDerivIndex_one] using
              U.property.hasWeakDerivativeOn_first (by norm_num) i)
      have hcomm (m : ℕ) :
          (fun x ↦ iteratedPartialDeriv (n := n) [i] (f_m m) x) =
            Approximation.mollify μ (ε m) g :=
        Approximation.iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
          μ (hεpos m) (by simp) hfLoc hfweak
      refine tendsto_coord_from_eLpNorm (singleDerivIndex n i) hf_smooth hf_cs ?_
      simpa [singleDerivIndex_toList, hcomm, g, domainMeasure] using
        Approximation.mollify_converges_Lp μ 2 (by norm_num) ε hεpos hε0 hgLp
  exact tendsto_iff_norm_sub_tendsto_zero.mpr <| tendsto_piLp_norm_of_forall
    (p := (2 : ℝ≥0∞)) (by norm_num) (x := fun m ↦
      (mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := (Set.univ : Set (ℝ^n)))
        (f_m m) (hf_smooth m) (hf_cs m) : WkpAmbientOn n 1 2 Set.univ) -
      (U : WkpAmbientOn n 1 2 Set.univ)) fun a ↦ by simpa using hcoord a

end Density

end GraphSpace

end SobolevSpace

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.MixedSobolevIntegral
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Reflexivity
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.ZeroBoundaryFiniteExponent
import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent
import PDE.Analysis.Operator.CompactConvergence

/-!
# Finite-power mixed energies with prescribed Sobolev boundary data

For every finite `p > 1`, the energy `∫ F(x, u, Du)` attains its minimum on
`g + W¹ᵖ₀` on every bounded measurable domain of positive dimension.
The density is convex only in the gradient. Its lower bound
`c |Du|ᵖ - b(x)`, with `c > 0`, is uniform in the value of `u`.

Absolute `p` growth of the density and conjugate growth of its continuous
gradient derivative give finite integrals and the mixed lower semicontinuity
argument. Poincaré bounds energy sublevels in the supported-core Sobolev
space. Reflexivity makes their weak closures compact, while Rellich
turns bounded weak Sobolev convergence into strong convergence of the values.
The direct method then constructs a minimizer in the nonempty affine class.

Densities without an upper growth bound are treated in the
`ExtendedMixedIntegralEnergy` modules. Dimension one is included, and on open sets
the supported-core closure is the usual zero-boundary Sobolev space.

Compare Evans, §8.2.2, Theorem 2, with `q = p`: there the Lagrangian is smooth with no upper
growth bound, and the constant `β` of the coercivity inequality (4) plays the role of `b`. The
Remark before that theorem explains why no convexity in the value is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Remark and Theorem 2 (Existence of minimizer),
  p. 470.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal Topology

namespace PDE.CalculusOfVariations

/-- A finite-power energy convex only in its gradient variable has a minimizer
in every affine class `g + W¹ᵖ₀` on a bounded measurable domain of positive
dimension. Both the energy and its supporting derivative are
constructed from the density, and their integrability and limit properties
are proved.

The lower bound is uniform in the scalar value. Absolute `p` growth and a
continuous gradient derivative with `p - 1` growth are additional sufficient
hypotheses for this finite-energy result. The boundary condition is membership
of `u - g` in the closure of the supported smooth core. -/
theorem exists_minimizer_mixedWkpIntegral_prescribed_boundary
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate (p : ℝ≥0∞) q]
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → ℝ × ℝ^n → ℝ^n}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D))
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, Continuous (F x))
    (hDcont : ∀ᵐ x ∂domainMeasure n Ω, Continuous (D x))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ,
      ConvexOn ℝ univ (fun z : ℝ^n ↦ F x (s, z)))
    (hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      HasFDerivAt (fun y : ℝ^n ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z)
    {a b d : ℝ^n → ℝ} {c C L : ℝ}
    (ha : Integrable a (domainMeasure n Ω))
    (hb : Integrable b (domainMeasure n Ω))
    (hd : MemLp d q (domainMeasure n Ω)) (hc : 0 < c)
    (hFgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ z,
      |F x z| ≤ a x + C * ‖z‖ ^ (p : ℝ))
    (hDgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ z,
      ‖D x z‖ ≤ d x + L * ‖z‖ ^ ((p : ℝ) - 1))
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : W^{1,p}(Ω)) :
    ∃ u : W^{1,p}(Ω),
      u - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) ∧
      ∀ v : W^{1,p}(Ω),
        v - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) →
        (∫ x, F x
          (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) u x,
            ∇ u x) ∂domainMeasure n Ω) ≤
        ∫ x, F x
          (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) v x,
            ∇ v x) ∂domainMeasure n Ω := by
  let W := W^{1,p}(Ω)
  let V := W₀^{1,(p : ℝ≥0∞)}(Ω)
  let μ := domainMeasure n Ω
  have : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let _ : NormedAddCommGroup W :=
    Submodule.normedAddCommGroup (wkpSubmoduleOn n 1 (p : ℝ≥0∞) Ω)
  let _ : NormedSpace ℝ W := Submodule.normedSpace (wkpSubmoduleOn n 1 (p : ℝ≥0∞) Ω)
  let _ : NormedAddCommGroup V := Submodule.normedAddCommGroup
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  let _ : NormedSpace ℝ V := Submodule.normedSpace
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hpE).ne'
  let B : W →L[ℝ] Lp ℝ p μ := wkpBaseCoordinateCLM
  let G : W →L[ℝ] Lp (ℝ^n) p μ := wkpGradientCLM
  let incl : V →L[ℝ] W :=
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule.subtypeL
  let I (u : W) : ℝ := ∫ x, F x (B u x, G u x) ∂μ
  let J (w : V) : ℝ := I (g + incl w)
  have hIint (u : W) : Integrable (fun x ↦ F x (B u x, G u x)) μ := by
    have hpair : MemLp (fun x ↦ (B u x, G u x)) (p : ℝ≥0∞) μ := by
      refine ((Lp.memLp (B u)).norm.add (Lp.memLp (G u)).norm).mono'
        ((Lp.memLp (B u)).aestronglyMeasurable.prodMk
          (Lp.memLp (G u)).aestronglyMeasurable) ?_
      filter_upwards [] with x
      change max ‖B u x‖ ‖G u x‖ ≤ ‖B u x‖ + ‖G u x‖
      exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _))
    apply hpair.integrable_comp_of_norm_rpow_le hp0 ENNReal.coe_ne_top hF ha
    simpa only [Real.norm_eq_abs, ENNReal.coe_toReal] using hFgrowth
  have hIlower (u : W) : c * ‖G u‖ ^ (p : ℝ) - (∫ x, b x ∂μ) ≤ I u := by
    have hint : Integrable (fun x ↦ ‖G u x‖ ^ (p : ℝ)) μ := by
      simpa only [ENNReal.coe_toReal] using
        (Lp.memLp (G u)).integrable_norm_rpow hp0 ENNReal.coe_ne_top
    have hnorm : ‖G u‖ ^ (p : ℝ) = ∫ x, ‖G u x‖ ^ (p : ℝ) ∂μ := by
      simpa only [ENNReal.coe_toReal] using
        Lp.norm_rpow_eq_integral hp0 ENNReal.coe_ne_top (G u)
    calc
      _ = ∫ x, c * ‖G u x‖ ^ (p : ℝ) - b x ∂μ := by
        rw [integral_sub (hint.const_mul c) hb, integral_const_mul, hnorm]
      _ ≤ I u := integral_mono_ae ((hint.const_mul c).sub hb) (hIint u)
        (hlower.mono fun x hx ↦ hx (B u x) (G u x))
  obtain ⟨P, hP⟩ := exists_norm_le_wkpGradientCLM
    (show 0 < n from Fact.out) hbounded hp.le
  have hJbounded (r : ℝ) : Bornology.IsBounded {w : V | J w ≤ r} := by
    let R : ℝ := max 1 ((r + ∫ x, b x ∂μ) / c)
    refine isBounded_iff_forall_norm_le.mpr ⟨(P : ℝ) * (R + ‖G g‖), fun w hw ↦ ?_⟩
    have hgrad : ‖G (g + incl w)‖ ≤ R := by
      by_contra h
      have hlt : R < ‖G (g + incl w)‖ := lt_of_not_ge h
      have hone : 1 ≤ ‖G (g + incl w)‖ := (le_max_left _ _).trans hlt.le
      have hquot : (r + ∫ x, b x ∂μ) / c < ‖G (g + incl w)‖ :=
        (le_max_right _ _).trans_lt hlt
      have hlarge := (div_lt_iff₀ hc).mp hquot
      have hpow := mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_one_le hone hpR.le) hc.le
      have hlow := hIlower (g + incl w)
      change I (g + incl w) ≤ r at hw
      nlinarith
    have hdiff : G (incl w) = G (g + incl w) - G g := by
      rw [map_add, add_sub_cancel_left]
    have hbound : ‖G (incl w)‖ ≤ R + ‖G g‖ := by
      rw [hdiff]
      exact (norm_sub_le _ _).trans (add_le_add hgrad le_rfl)
    exact (hP w).trans (mul_le_mul_of_nonneg_left hbound P.coe_nonneg)
  have hcompact : IsCompactOperator (B.comp incl) :=
    RellichKondrachov.wkp0BaseCoordinate_isCompactOperator_of_bounded
      hΩ hbounded ENNReal.coe_ne_top
  have hJclosed (r : ℝ) :
      IsClosed {w : WeakSpace ℝ V | J ((toWeakSpace ℝ V).symm w) ≤ r} := by
    let S : Set (WeakSpace ℝ V) := {w | J ((toWeakSpace ℝ V).symm w) ≤ r}
    apply closure_subset_iff_isClosed.mp
    intro w hw
    let l : Filter S := comap (Subtype.val : S → WeakSpace ℝ V) (𝓝 w)
    have : l.NeBot := mem_closure_iff_comap_neBot.mp hw
    let family (v : S) : V := (toWeakSpace ℝ V).symm v.1
    let w₀ : V := (toWeakSpace ℝ V).symm w
    have hfamily : Bornology.IsBounded (range family) :=
      (hJbounded r).subset (by
        rintro _ ⟨v, rfl⟩
        exact v.property)
    have hweak : Tendsto (fun v : S ↦ toWeakSpace ℝ V (family v)) l
        (𝓝 (toWeakSpace ℝ V w₀)) := tendsto_comap
    have hbase : Tendsto (fun v : S ↦ B (incl (family v))) l (𝓝 (B (incl w₀))) :=
      PDE.Analysis.tendsto_compactOperator_of_tendsto_weak_of_bounded
        (X := V) (Y := Lp ℝ (p : ℝ≥0∞) μ)
        (B.comp incl) hcompact hfamily hweak
    have hweakW : Tendsto (fun v : S ↦ toWeakSpace ℝ W (incl (family v))) l
        (𝓝 (toWeakSpace ℝ W (incl w₀))) :=
      (WeakSpace.map incl).continuous.continuousAt.tendsto.comp hweak
    have hweakAffine : Tendsto (fun v : S ↦ toWeakSpace ℝ W (g + incl (family v))) l
        (𝓝 (toWeakSpace ℝ W (g + incl w₀))) := by
      simpa only [map_add] using
        (tendsto_const_nhds.add hweakW :
          Tendsto (fun v : S ↦ toWeakSpace ℝ W g + toWeakSpace ℝ W (incl (family v))) l
            (𝓝 (toWeakSpace ℝ W g + toWeakSpace ℝ W (incl w₀))))
    have hbaseAffine : Tendsto (fun v : S ↦ B (g + incl (family v))) l
        (𝓝 (B (g + incl w₀))) := by
      simpa only [map_add] using (tendsto_const_nhds.add hbase :
        Tendsto (fun v : S ↦ B g + B (incl (family v))) l (𝓝 (B g + B (incl w₀))))
    obtain ⟨R, hR⟩ := hfamily.exists_norm_le
    have hnorm (v : S) : ‖g + incl (family v)‖ ≤ ‖g‖ + R := by
      apply (norm_add_le _ _).trans
      have hincl : ‖incl (family v)‖ ≤ R := by
        change ‖family v‖ ≤ R
        exact hR _ (mem_range_self v)
      exact add_le_add le_rfl hincl
    exact integral_le_of_tendsto_weak_wkp_of_tendsto_base hpE ENNReal.coe_ne_top
      hF hD hFcont hDcont hconvex hderiv ha hd
      (by simpa only [ENNReal.coe_toReal] using hFgrowth)
      (by simpa only [ENNReal.coe_toReal] using hDgrowth)
      hweakAffine hbaseAffine (‖g‖ + R) hnorm
      (Eventually.of_forall fun v : S ↦ v.property)
  have hJlsc : LowerSemicontinuous
      (fun w : WeakSpace ℝ V ↦ J ((toWeakSpace ℝ V).symm w)) :=
    lowerSemicontinuous_iff_isClosed_preimage.mpr hJclosed
  have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V) :=
    Wkp0SpaceOn.surjective_inclusionInDoubleDual hpE ENNReal.coe_ne_top
  have hAdmissible : IsClosed ((toWeakSpace ℝ V) '' (univ : Set V)) := by
    rw [image_univ_of_surjective (toWeakSpace ℝ V).surjective]
    exact isClosed_univ
  obtain ⟨w, _, hw⟩ :=
    exists_isMinOn_of_weak_lowerSemicontinuousOn_of_bounded_sublevel
      (E := V) hreflexive J (A := univ) hAdmissible
      (hJlsc.lowerSemicontinuousOn _) (mem_univ (0 : V))
      ((hJbounded (J 0)).subset (by intro v hv; exact hv.2))
  refine ⟨g + incl w, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    change (w : W) ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
    exact w.property
  · intro v hv
    let z : V := ⟨v - g, hv⟩
    have hz : g + incl z = v := by
      change g + (v - g) = v
      rw [add_comm, sub_add_cancel]
    have hmin : I (g + incl w) ≤ I (g + incl z) := hw (mem_univ z)
    rw [hz] at hmin
    exact hmin

end PDE.CalculusOfVariations

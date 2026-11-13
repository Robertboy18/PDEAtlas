/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedDirectMethod
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Coercivity
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.LowerSemicontinuity
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Reflexivity
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.ZeroBoundaryFiniteExponent
import PDE.Analysis.Operator.CompactConvergence
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Extended mixed-energy minimization with prescribed boundary values

A density convex in the gradient and bounded below by a positive gradient power has a
finite-energy minimizer whenever its prescribed affine Sobolev class contains a finite
competitor. The energy is a nonnegative Lebesgue integral after adding the spatial lower
bound, so no upper growth bound or finiteness at every Sobolev function is required.

Poincaré bounds the affine sublevel, reflexivity supplies weak compactness, and finite-`p`
Sobolev separability gives a weakly convergent subsequence. Compactness of the zero-boundary
corrections supplies strong convergence of their values. Adding the fixed boundary field
preserves this convergence. The truncated supporting-field argument then proves the
lower-semicontinuity needed to pass to the limit.

Boundedness and measurability of the domain suffice in every positive dimension, including
one. On open domains the boundary condition is membership of the difference in `W¹ᵖ₀`.
For measurable sets it means the same supported smooth-core closure in the Sobolev graph
space.

The main theorem, `exists_minimizer_mixedWkpLIntegral_prescribed_boundary`, is a form of
Evans, §8.2.2, Theorem 2, with the coercivity (4) of §8.2.1 replaced by a spatially varying
lower bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.1 and §8.2.2, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal Topology

namespace PDE.CalculusOfVariations

/-- A mixed density with positive `p`-coercivity and no upper growth bound attains a
finite extended-energy minimum in every prescribed affine `W¹ᵖ` class containing one
finite-energy competitor. Here `1 < p < ∞`, the domain is bounded and measurable, and
its dimension is positive. On open domains this is the usual affine `W¹ᵖ₀` boundary class;
on measurable sets the condition means the supported smooth-core closure.

Convexity and differentiability concern only the gradient. The density and gradient
supporting field are measurable and continuous in the value variable almost everywhere.
The displayed functional adds the spatial lower bound `b`; if `b` is integrable, this is
a finite constant shift of the original energy. Uniform constant lower bounds are a
special case on these bounded domains. -/
theorem exists_minimizer_mixedWkpLIntegral_prescribed_boundary
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → ℝ × ℝ^n → ℝ^n} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ F x (s, z)))
    (hDcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^n,
      Continuous (fun s : ℝ ↦ D x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ,
      ConvexOn ℝ univ (fun z : ℝ^n ↦ F x (s, z)))
    (hderiv : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      HasFDerivAt (fun y : ℝ^n ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ) (z : ℝ^n),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : W^{1,p}(Ω)) (w₀ : W₀^{1,(p : ℝ≥0∞)}(Ω))
    (hfinite : (∫⁻ x, ENNReal.ofReal (F x
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞))
          (g + (w₀ : W^{1,p}(Ω))) x,
        ∇ (g + (w₀ : W^{1,p}(Ω))) x) + b x)
      ∂domainMeasure n Ω) ≠ ∞) :
    ∃ u : W^{1,p}(Ω),
      u - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) ∧
      (∫⁻ x, ENNReal.ofReal (F x
        (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) u x,
          ∇ u x) + b x) ∂domainMeasure n Ω) ≠ ∞ ∧
      ∀ v : W^{1,p}(Ω),
        v - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) →
        (∫⁻ x, ENNReal.ofReal (F x
          (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) u x,
            ∇ u x) + b x) ∂domainMeasure n Ω) ≤
        ∫⁻ x, ENNReal.ofReal (F x
          (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) v x,
            ∇ v x) + b x) ∂domainMeasure n Ω := by
  let W := W^{1,p}(Ω)
  let V := W₀^{1,(p : ℝ≥0∞)}(Ω)
  let μ := domainMeasure n Ω
  have : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hΩbounded
  let _ : NormedAddCommGroup W :=
    Submodule.normedAddCommGroup (wkpSubmoduleOn n 1 (p : ℝ≥0∞) Ω)
  let _ : NormedSpace ℝ W := Submodule.normedSpace (wkpSubmoduleOn n 1 (p : ℝ≥0∞) Ω)
  let _ : NormedAddCommGroup V := Submodule.normedAddCommGroup
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  let _ : NormedSpace ℝ V := Submodule.normedSpace
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  have : Fact ((p : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.coe_ne_top⟩
  have : SecondCountableTopology V := inferInstance
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  have : Fact (1 ≤ ENNReal.conjExponent (p : ℝ≥0∞)) :=
    ⟨ENNReal.HolderConjugate.one_le _ (p : ℝ≥0∞)⟩
  have hq_top : ENNReal.conjExponent (p : ℝ≥0∞) ≠ ∞ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt
      (ENNReal.conjExponent (p : ℝ≥0∞)) (p : ℝ≥0∞)).mpr hpE).ne
  let B : W →L[ℝ] Lp ℝ p μ := wkpBaseCoordinateCLM
  let G : W →L[ℝ] Lp (ℝ^n) p μ := wkpGradientCLM
  let incl : V →L[ℝ] W :=
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule.subtypeL
  let I (u : W) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (F x (B u x, G u x) + b x) ∂μ
  let J (w : V) : ℝ≥0∞ := I (g + incl w)
  have hcompact : IsCompactOperator (B.comp incl) :=
    RellichKondrachov.wkp0BaseCoordinate_isCompactOperator_of_bounded
      hΩmeas hΩbounded ENNReal.coe_ne_top
  have hlower' : ∀ᵐ x ∂μ, ∀ z : ℝ × ℝ^n, -b x ≤ F x z := by
    filter_upwards [hlower] with x hx
    intro z
    have hnonneg := mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg z.2) (p : ℝ))
    have h := hx z.1 z.2
    linarith
  have hseq (u : ℕ → V) (uLimit : V) (_hu : ∀ j, u j ∈ (univ : Set V))
      (hubounded : Bornology.IsBounded (range u))
      (hu : Tendsto (fun j ↦ toWeakSpace ℝ V (u j)) atTop
        (𝓝 (toWeakSpace ℝ V uLimit))) : J uLimit ≤ liminf (fun j ↦ J (u j)) atTop := by
    have hweakW : Tendsto (fun j ↦ toWeakSpace ℝ W (incl (u j))) atTop
        (𝓝 (toWeakSpace ℝ W (incl uLimit))) :=
      (WeakSpace.map incl).continuous.continuousAt.tendsto.comp hu
    have hweakAffine : Tendsto (fun j ↦ toWeakSpace ℝ W (g + incl (u j))) atTop
        (𝓝 (toWeakSpace ℝ W (g + incl uLimit))) := by
      simpa only [map_add] using
        (tendsto_const_nhds.add hweakW : Tendsto
          (fun j ↦ toWeakSpace ℝ W g + toWeakSpace ℝ W (incl (u j))) atTop
          (𝓝 (toWeakSpace ℝ W g + toWeakSpace ℝ W (incl uLimit))))
    obtain ⟨R, hR⟩ := hubounded.exists_norm_le
    have hnorm (j : ℕ) : ‖g + incl (u j)‖ ≤ ‖g‖ + R := by
      apply (norm_add_le _ _).trans
      have hincl : ‖incl (u j)‖ ≤ R := by
        change ‖u j‖ ≤ R
        exact hR _ (mem_range_self j)
      exact add_le_add le_rfl hincl
    -- Compactness applies to the corrections; the fixed boundary field is then added.
    have hbase : Tendsto (fun j ↦ B (incl (u j))) atTop
        (𝓝 (B (incl uLimit))) :=
      PDE.Analysis.tendsto_compactOperator_of_tendsto_weak_of_bounded
        (B.comp incl) hcompact hubounded hu
    have hbaseAffine : Tendsto (fun j ↦ B (g + incl (u j))) atTop
        (𝓝 (B (g + incl uLimit))) := by
      simpa only [map_add] using (tendsto_const_nhds.add hbase :
        Tendsto (fun j ↦ B g + B (incl (u j))) atTop (𝓝 (B g + B (incl uLimit))))
    have hgradient : Tendsto
        (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) p μ) (G (g + incl (u j)))) atTop
        (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) p μ) (G (g + incl uLimit)))) :=
      (WeakSpace.map G).continuous.continuousAt.tendsto.comp hweakAffine
    have hgradient_bound (j : ℕ) : ‖G (g + incl (u j))‖ ≤ ‖G‖ * (‖g‖ + R) :=
      (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hnorm j) (norm_nonneg G))
    simpa only [Pi.neg_apply, sub_neg_eq_add] using
      (lintegral_le_liminf_of_tendsto_strong_weak_of_convex_gradient
        (p := (p : ℝ≥0∞)) (q := ENNReal.conjExponent (p : ℝ≥0∞))
        (r := (p : ℝ≥0∞)) hq_top hF hD hb.neg hFcont hDcont hconvex hderiv
        hbaseAffine hgradient (hlower'.mono fun x hx ↦ hx _)
        (‖G‖ * (‖g‖ + R)) hgradient_bound)
  have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V) :=
    Wkp0SpaceOn.surjective_inclusionInDoubleDual hpE ENNReal.coe_ne_top
  have hAdmissible : IsClosed ((toWeakSpace ℝ V) '' (univ : Set V)) := by
    rw [image_univ_of_surjective (toWeakSpace ℝ V).surjective]
    exact isClosed_univ
  have hJbounded : Bornology.IsBounded {w : V | w ∈ (univ : Set V) ∧ J w ≤ J w₀} := by
    have hbounded := isBounded_sublevel_mixedWkpLIntegral_prescribed_boundary
      (show 0 < n from Fact.out) hΩbounded hp.le hc hlower g hfinite
    exact hbounded.subset (by intro w hw; exact hw.2)
  obtain ⟨w, _, hwfinite, hw⟩ :=
    exists_isMinOn_of_weak_seq_lowerSemicontinuity_of_bounded_sublevel
      (E := V) hreflexive J hAdmissible.isSeqClosed hseq (mem_univ w₀) hfinite hJbounded
  refine ⟨g + incl w, ?_, hwfinite, ?_⟩
  · rw [add_sub_cancel_left]
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

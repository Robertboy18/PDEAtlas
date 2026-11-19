/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Uniqueness
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Centering

/-!
# Scalar uniqueness below quadratic Sobolev exponent

For the signed density `‖P‖² - 1`, the constant one is the unique minimizer
in its own geometric trace class in W¹˒³ᐟ². Its trace is nonzero on a nonempty
bounded open `C¹` domain. Other competitors need not have square-integrable
gradients: the energy is allowed to be positive infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.CalculusOfVariations PDE.Analysis
open scoped ENNReal NNReal Sobolev

namespace PDE.Examples.VariationalScalar

/-- The constant `1` has nonzero trace and is the unique minimizer in `W^{1,3/2}` of the
energy of `‖∇u‖² - 1` among maps with the same trace. -/
theorem constant_one_unique_minimizer {d : ℕ} {Ω : Set (ℝ^(d + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hnonempty : Ω.Nonempty) :
    letI : Fact (1 ≤ ENNReal.ofReal (3 / 2)) := ⟨by norm_num⟩
    letI : Boundary.C1ExtensionAtlas (d + 1) Ω := hgraph.c1ExtensionAtlas hopen hbounded
    letI := isFiniteMeasure_domainMeasure_of_isBounded hbounded
    let c : W^{1,ENNReal.ofReal (3 / 2)}(Ω) := wkpConstant 1
    let T := Trace.C1.traceLp (3 / 2)
    let A := {u | T u = T c}
    let I := fun u : W^{1,ENNReal.ofReal (3 / 2)}(Ω) ↦
      lowerBoundedIntegral (domainMeasure (d + 1) Ω)
        (fun x ↦ ‖∇ u x‖ ^ 2 - 1)
    T c ≠ 0 ∧ ∃! u, u ∈ A ∧ IsMinOn I A u := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2)) := ⟨by norm_num⟩
  let : Boundary.C1ExtensionAtlas (d + 1) Ω := hgraph.c1ExtensionAtlas hopen hbounded
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  intro c T A I
  have hmeas (u : W^{1,ENNReal.ofReal (3 / 2)}(Ω)) :
      AEStronglyMeasurable (fun x ↦ ‖∇ u x‖ ^ 2 - 1)
        (domainMeasure (d + 1) Ω) :=
    ((Lp.aestronglyMeasurable _).norm.pow 2).sub aestronglyMeasurable_const
  have hlower (u : W^{1,ENNReal.ofReal (3 / 2)}(Ω)) :
      ∀ᵐ x ∂domainMeasure (d + 1) Ω, -(1 : ℝ) ≤ ‖∇ u x‖ ^ 2 - 1 :=
    Filter.Eventually.of_forall fun x ↦ by linarith [sq_nonneg ‖∇ u x‖]
  have hc : (fun x ↦ ‖∇ c x‖ ^ 2 - 1) =ᵐ[domainMeasure (d + 1) Ω]
      fun _ ↦ (-1 : ℝ) := by
    filter_upwards [Lp.coeFn_zero (ℝ^(d + 1)) (ENNReal.ofReal (3 / 2))
      (domainMeasure (d + 1) Ω)] with x hx
    simp only [c, wkpGradientCLM_constant, hx, Pi.zero_apply, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_sub]
  have hci : Integrable (fun x ↦ ‖∇ c x‖ ^ 2 - 1)
      (domainMeasure (d + 1) Ω) := (integrable_const (-1 : ℝ)).congr hc.symm
  have hfinite : I c ≠ ⊤ := by
    change lowerBoundedIntegral _ _ ≠ ⊤
    rw [lowerBoundedIntegral_eq_integral hci]
    exact EReal.coe_ne_top _
  have hmin : IsMinOn I A c := by
    intro v _
    apply (lowerBoundedIntegral_le_iff hci.aestronglyMeasurable (hmeas v)
      (integrable_const 1) (hlower c) (hlower v)).mpr
    apply lintegral_mono_ae
    filter_upwards [hc] with x hx
    rw [hx]
    simp only [neg_add_cancel, ENNReal.ofReal_zero]
    exact zero_le
  have hn : StrictConvexOn ℝ univ (fun P : ℝ^(d + 1) ↦ ‖P‖ ^ 2) := by
    apply StrongConvexOn.strictConvexOn (m := 2) _ (by norm_num)
    rw [strongConvexOn_iff_convex]
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul, sub_self] using
      (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set (ℝ^(d + 1)))))
  have hunique (v : W^{1,ENNReal.ofReal (3 / 2)}(Ω))
      (hv : v ∈ A ∧ IsMinOn I A v) : v = c := by
    symm
    refine eq_of_isMinOn_wkpIntegral hopen hbounded hgraph
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
      (L := fun t ↦ ‖t.2‖ ^ 2 - 1)
      ((continuous_snd.norm.pow 2).sub continuous_const).continuousOn
      (β := 1) (fun _ _ _ P ↦ by linarith [sq_nonneg ‖P‖])
      ?_ ?_ (T c) c v rfl hv.1 hmin hv.2 hfinite
    · intro _ _
      refine ⟨convex_univ, fun z _ w _ a b ha hb hab ↦ ?_⟩
      exact (hn.convexOn.add_const (-1)).2 (mem_univ z.2) (mem_univ w.2) ha hb hab
    · intro _ _ z w hne
      have h := (hn.add_const (-1)).2 (mem_univ z.2) (mem_univ w.2) hne
        (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num)
      simpa only [Pi.add_apply, sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv, add_mul,
        mul_comm (2 : ℝ)⁻¹] using h
  refine ⟨?_, ⟨c, ⟨rfl, hmin⟩, hunique⟩⟩
  intro htrace
  have henergy : I 0 = I c := by
    dsimp only [I]
    simp only [c, wkpGradientCLM_constant, map_zero]
  have hz : c = 0 := by
    symm
    apply hunique 0
    refine ⟨?_, fun v hv ↦ ?_⟩
    · change T 0 = T c
      rw [map_zero, htrace]
    · change I 0 ≤ I v
      rw [henergy]
      exact hmin hv
  have hbase := wkpConstant_base_ae (n := d + 1) (p := ENNReal.ofReal (3 / 2))
    (Ω := Ω) 1
  change wkpBaseCoordinateCLM c =ᵐ[domainMeasure (d + 1) Ω] fun _ ↦ (1 : ℝ) at hbase
  rw [hz, map_zero] at hbase
  have hfalse : ∀ᵐ x ∂domainMeasure (d + 1) Ω, False := by
    filter_upwards [hbase, Lp.coeFn_zero ℝ (ENNReal.ofReal (3 / 2))
      (domainMeasure (d + 1) Ω)] with x hx hx0
    simp only [hx0, Pi.zero_apply, zero_ne_one] at hx
  have hzero : (domainMeasure (d + 1) Ω) univ = 0 := by
    simpa only [ae_iff, not_false_eq_true, ofPred_true] using hfalse
  exact (hopen.measure_pos volume hnonempty).ne'
    (by simpa only [domainMeasure, Measure.restrict_apply_univ] using hzero)

end PDE.Examples.VariationalScalar

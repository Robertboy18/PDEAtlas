/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.DirichletIntegral
public import PDE.CalculusOfVariations.MixedIntegralEnergy
public import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension
import PDE.Analysis.Operator.CompactConvergence

/-!
# Minimizers of convex-gradient energies depending on the value

For `J(u) = ∫_Ω F(x, u, Du)`, convexity is required only in the gradient.
Quadratic growth gives finite energies, and the lower bound
`c |p|² - b(x) ≤ F(x, s, p)`, uniform in `s` with `c > 0`, gives coercivity
on every affine class `g + H¹₀(Ω)`.

On bounded measurable sets, Rellich makes the base coordinate compact.
Thus bounded weak convergence in `H¹₀` gives strong convergence of the
values and weak convergence of the gradients. The supporting-field
argument in `MixedIntegralEnergy` then proves weak lower semicontinuity
on every energy sublevel. The Hilbert direct method supplies a minimizer.

The density is jointly measurable and continuous in `(s, p)` almost
everywhere. Its gradient derivative is continuous with linear growth.
No convexity in `s` or boundary regularity is assumed. The prescribed
boundary condition means `u - g ∈ H¹₀`, with `H¹₀` defined as the closure
of test functions. On open domains this is the usual Sobolev condition;
on general measurable sets the statement concerns these graph spaces.

Compare Evans, §8.2.2, Theorem 2, for `q = 2`: there the Lagrangian is smooth with no upper
growth bound, and the constant `β` of the coercivity inequality (4) plays the role of `b`. The
Remark before that theorem explains why no convexity in the value is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Remark and Theorem 2 (Existence of minimizer),
  p. 470.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology InnerProductSpace

namespace PDE.CalculusOfVariations

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

private theorem exists_pos_mul_norm_sq_le_gradient_norm_sq
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ k : ℝ, 0 < k ∧ ∀ u : H¹₀(Ω),
      k * ‖u‖ ^ 2 ≤ ‖∇ (u : H¹(Ω))‖ ^ 2 := by
  have hint (u : H¹₀(Ω)) :
      Integrable (fun x ↦ ‖∇ (u : H¹(Ω)) x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ)
        (∇ (u : H¹(Ω))) (∇ (u : H¹(Ω))))
  obtain ⟨k, hk, hbound⟩ :=
    exists_pos_quadratic_lower_bound_dirichletGradientIntegralEnergy
      (F := fun _ z ↦ ‖z‖ ^ 2) (b := fun _ ↦ 0) (c := 1)
      hn hΩbounded (by norm_num) (by simp) hint (by simp)
  refine ⟨k, hk, fun u ↦ ?_⟩
  have hnorm :
      (∫ x, ‖∇ (u : H¹(Ω)) x‖ ^ 2 ∂μ) =
        ‖∇ (u : H¹(Ω))‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.inner_def (𝕜 := ℝ)
        (∇ (u : H¹(Ω))) (∇ (u : H¹(Ω)))).symm
  simpa only [dirichletGradientIntegralEnergy, integral_zero, sub_zero, hnorm] using
    hbound u

/-- A quadratic-growth energy convex only in the gradient attains a
minimum with prescribed Sobolev boundary data on a bounded measurable
domain of positive dimension.

The density `F x (s, p)` and its gradient derivative `D x (s, p)` are
jointly measurable and almost everywhere continuous in `(s, p)`. The
derivative is represented by the Euclidean inner product and has linear
growth with an `L²` offset. The density has an absolute quadratic bound
with an `L¹` offset and a positive quadratic lower bound in `p`, uniform
in `s`. These assumptions give integrability, coercivity, and weak lower
semicontinuity of the energy.

The admissible class is `g + H¹₀`. Convexity in `s` and boundary
smoothness are not required. -/
theorem exists_minimizer_mixedIntegralEnergy_prescribed_boundary
    (hn : 0 < n) (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {D : ℝ^n → ℝ × ℝ^n → ℝ^n}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D))
    (hFcont : ∀ᵐ x ∂μ, Continuous (F x))
    (hDcont : ∀ᵐ x ∂μ, Continuous (D x))
    (hconvex : ∀ᵐ x ∂μ, ∀ s : ℝ, ConvexOn ℝ univ (fun p : ℝ^n ↦ F x (s, p)))
    (hderiv : ∀ᵐ x ∂μ, ∀ (s : ℝ) (p : ℝ^n),
      HasFDerivAt (fun q : ℝ^n ↦ F x (s, q)) (innerSL ℝ (D x (s, p))) p)
    {a b d : ℝ^n → ℝ} {c C L : ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hd : MemLp d 2 μ)
    (hc : 0 < c)
    (hFgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ 2)
    (hDgrowth : ∀ᵐ x ∂μ, ∀ z, ‖D x z‖ ≤ d x + L * ‖z‖)
    (hlower : ∀ᵐ x ∂μ, ∀ (s : ℝ) (p : ℝ^n), c * ‖p‖ ^ 2 - b x ≤ F x (s, p))
    (g : H¹(Ω)) :
    ∃ u : H¹(Ω), u - g ∈ h10Submodule (n := n) (Ω := Ω) ∧
      ∀ v : H¹(Ω), v - g ∈ h10Submodule (n := n) (Ω := Ω) →
        firstOrderSobolevIntegralEnergy F u ≤ firstOrderSobolevIntegralEnergy F v := by
  let B := baseCoordCLM (n := n) (Ω := Ω)
  let G := gradientCLM (n := n) (Ω := Ω)
  let s₀ := wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) g
  let p₀ := ∇ g
  let J (w : H¹₀(Ω)) : ℝ := ∫ x, F x ((s₀ + B w) x, (p₀ + G w) x) ∂μ
  have hJint (w : H¹₀(Ω)) :
      Integrable (fun x ↦ F x ((s₀ + B w) x, (p₀ + G w) x)) μ :=
    integrable_mixed_L2_density_of_quadratic_growth hF ha hFgrowth (s₀ + B w) (p₀ + G w)
  have hJenergy (w : H¹₀(Ω)) :
      firstOrderSobolevIntegralEnergy F (g + (w : H¹(Ω))) = J w := by
    rw [firstOrderSobolevIntegralEnergy_eq_integral_base_gradient, map_add, map_add]
    rfl
  obtain ⟨k, hk, hkbound⟩ :=
    exists_pos_mul_norm_sq_le_gradient_norm_sq (Ω := Ω) hn hΩbounded
  let K := (c / 2) * k
  let A := c * ‖p₀‖ ^ 2 + ∫ x, b x ∂μ
  have hK : 0 < K := mul_pos (half_pos hc) hk
  have hJlower (w : H¹₀(Ω)) : K * ‖w‖ ^ 2 - A ≤ J w := by
    have hint : Integrable (fun x ↦ ‖(p₀ + G w) x‖ ^ 2) μ := by
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.integrable_inner (𝕜 := ℝ) (p₀ + G w) (p₀ + G w))
    have hnorm : (∫ x, ‖(p₀ + G w) x‖ ^ 2 ∂μ) = ‖p₀ + G w‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.inner_def (𝕜 := ℝ) (p₀ + G w) (p₀ + G w)).symm
    have hlower' : c * ‖p₀ + G w‖ ^ 2 - (∫ x, b x ∂μ) ≤ J w := by
      calc
        c * ‖p₀ + G w‖ ^ 2 - (∫ x, b x ∂μ) =
            ∫ x, c * ‖(p₀ + G w) x‖ ^ 2 - b x ∂μ := by
          rw [integral_sub (hint.const_mul c) hb, integral_const_mul, hnorm]
        _ ≤ J w :=
          integral_mono_ae ((hint.const_mul c).sub hb) (hJint w)
            (hlower.mono fun x hx ↦ hx ((s₀ + B w) x) ((p₀ + G w) x))
    have hn : ‖G w‖ ≤ ‖p₀ + G w‖ + ‖p₀‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (p₀ + G w) p₀
    have hsq := (sq_le_sq₀ (norm_nonneg (G w))
      (add_nonneg (norm_nonneg (p₀ + G w)) (norm_nonneg p₀))).2 hn
    have hsq' : ‖G w‖ ^ 2 ≤ 2 * (‖p₀ + G w‖ ^ 2 + ‖p₀‖ ^ 2) := by
      nlinarith [sq_nonneg (‖p₀ + G w‖ - ‖p₀‖)]
    have hkg := mul_le_mul_of_nonneg_left (hkbound w) (half_pos hc).le
    have hcg := mul_le_mul_of_nonneg_left hsq' (half_pos hc).le
    dsimp only [K, A]
    change (c / 2) * (k * ‖w‖ ^ 2) ≤ (c / 2) * ‖G w‖ ^ 2 at hkg
    nlinarith
  have hJbounded (r : ℝ) : Bornology.IsBounded {w : H¹₀(Ω) | J w ≤ r} := by
    refine isBounded_iff_forall_norm_le.mpr ⟨max 1 ((r + A) / K), fun w hw ↦ ?_⟩
    by_contra h
    have hlt := lt_of_not_ge h
    have hone : 1 < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hlt
    have hr : (r + A) / K < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hlt
    have hr' : r + A < K * ‖w‖ := by
      have := (div_lt_iff₀ hK).mp hr
      simpa only [mul_comm] using this
    have hsq : ‖w‖ ≤ ‖w‖ ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hK.le
    have hlow := hJlower w
    change J w ≤ r at hw
    linarith
  have hJclosed (r : ℝ) :
      IsClosed {w : WeakSpace ℝ H¹₀(Ω) | J ((toWeakSpace ℝ H¹₀(Ω)).symm w) ≤ r} := by
    let S : Set (WeakSpace ℝ H¹₀(Ω)) :=
      {w | J ((toWeakSpace ℝ H¹₀(Ω)).symm w) ≤ r}
    apply closure_subset_iff_isClosed.mp
    intro w hw
    let l : Filter S := comap (Subtype.val : S → WeakSpace ℝ H¹₀(Ω)) (𝓝 w)
    have : l.NeBot := mem_closure_iff_comap_neBot.mp hw
    let family (v : S) : H¹₀(Ω) := (toWeakSpace ℝ H¹₀(Ω)).symm v.1
    let w₀ : H¹₀(Ω) := (toWeakSpace ℝ H¹₀(Ω)).symm w
    have hfamily : Bornology.IsBounded (range family) :=
      (hJbounded r).subset (by
        rintro _ ⟨v, rfl⟩
        exact v.property)
    have hweak : Tendsto (fun v : S ↦ toWeakSpace ℝ H¹₀(Ω) (family v)) l
        (𝓝 (toWeakSpace ℝ H¹₀(Ω) w₀)) := by
      exact tendsto_comap
    have hbase : Tendsto (fun v : S ↦ B (family v)) l (𝓝 (B w₀)) :=
      @PDE.Analysis.tendsto_compactOperator_of_tendsto_weak_of_bounded
        H¹₀(Ω) (Lp ℝ 2 μ) S inferInstance
        (Submodule.normedSpace (h10Submodule (n := n) (Ω := Ω)))
        inferInstance inferInstance B
        (baseCoordCLM.isCompactOperator_of_bounded hΩmeas hΩbounded)
        l family w₀ hfamily hweak
    have hvalues : Tendsto (fun v : S ↦ s₀ + B (family v)) l (𝓝 (s₀ + B w₀)) :=
      tendsto_const_nhds.add hbase
    have hgradient :
        Tendsto (fun v : S ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 μ) (G (family v))) l
          (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 μ) (G w₀))) :=
      (WeakSpace.map G).continuous.continuousAt.tendsto.comp hweak
    have hgradients :
        Tendsto (fun v : S ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 μ) (p₀ + G (family v))) l
          (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 μ) (p₀ + G w₀))) := by
      simpa only [map_add] using
        (tendsto_const_nhds.add hgradient :
          Tendsto (fun v : S ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 μ) p₀ +
            toWeakSpace ℝ (Lp (ℝ^n) 2 μ) (G (family v))) l
            (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 μ) p₀ +
              toWeakSpace ℝ (Lp (ℝ^n) 2 μ) (G w₀))))
    obtain ⟨R, hR⟩ := hfamily.exists_norm_le
    have hgradbound (v : S) : ‖p₀ + G (family v)‖ ≤ ‖p₀‖ + R := by
      exact (norm_add_le _ _).trans (add_le_add_right
        ((gradientCLM_norm_le (family v)).trans (hR _ (mem_range_self v))) _)
    exact integral_le_of_tendsto_strong_weak_of_convex_gradient
      (p := 2) (q := 2) (by norm_num) (by simp)
      hF hD hFcont hDcont hconvex hderiv ha hd
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hFgrowth)
      (by simpa only [ENNReal.toReal_ofNat, show (2 : ℝ) - 1 = 1 by norm_num,
        Real.rpow_one] using hDgrowth)
      hvalues hgradients (‖p₀‖ + R) hgradbound
      (Eventually.of_forall fun v : S ↦ v.property)
  have hJlsc : LowerSemicontinuous
      (fun w : WeakSpace ℝ H¹₀(Ω) ↦ J ((toWeakSpace ℝ H¹₀(Ω)).symm w)) :=
    lowerSemicontinuous_iff_isClosed_preimage.mpr hJclosed
  obtain ⟨w, hw⟩ :=
    @exists_global_minimizer_of_weak_lowerSemicontinuous_of_bounded_sublevel
      H¹₀(Ω) inferInstance inferInstance inferInstance J hJlsc 0 (hJbounded (J 0))
  refine ⟨g + (w : H¹(Ω)), ?_, ?_⟩
  · simpa only [add_sub_cancel_left, h10Submodule, h10SubmoduleOn] using w.property
  · intro v hv
    let z : H¹₀(Ω) := ⟨v - g, hv⟩
    have hv' : g + (z : H¹(Ω)) = v := by
      change g + (v - g) = v
      rw [add_comm, sub_add_cancel]
    rw [hJenergy, ← hv', hJenergy]
    exact hw z

end PDE.CalculusOfVariations

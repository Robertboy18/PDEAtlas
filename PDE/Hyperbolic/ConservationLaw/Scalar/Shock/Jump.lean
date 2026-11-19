/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Interface
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
import PDE.DistributionTheory.TestFunction
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import CAS.ExactTactic

/-!
# Distributional derivatives of a moving shock

Two varying classical fields are joined across `x = s(t)`. The left trace is
assigned on the interface. Each side is represented by a C¹ field on spacetime;
the equations are imposed only on the side where that field is used.

The tested derivative is the negative tested bulk derivative plus the jump
weighted by the outward conormal of the right-hand region. Both local
integrability and the interface contribution are proved from the fields. This is the
computation (8)-(9) of Evans, §3.4.1(a), without the equation on either side.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1(a), equations (8)-(9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.DistributionTheory TopologicalSpace
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Shock

/-- Join two fields across a moving graph, taking the left trace on the graph. -/
def profile (s : ℝ → ℝ) (uL uR : ℝ^2 → ℝ) (p : ℝ^2) : ℝ :=
  if s (p 0) < p 1 then uR p else uL p

/-- Strictly to the right, the profile agrees with the right field. -/
@[simp] theorem profile_of_right {s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} {p : ℝ^2}
    (hp : s (p 0) < p 1) : profile s uL uR p = uR p := ite_eq_left hp

/-- On and to the left of the graph, the profile agrees with the left field. -/
@[simp] theorem profile_of_left {s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} {p : ℝ^2}
    (hp : p 1 ≤ s (p 0)) : profile s uL uR p = uL p := ite_eq_right (not_lt.mpr hp)

/-- The left classical field evaluated on the graph is the left trace
of the joined field at each fixed time. -/
theorem tendsto_profile_left {s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hL : Continuous uL) (t : ℝ) :
    Tendsto (fun x ↦ profile s uL uR !₂[t, x]) (𝓝[<] s t) (𝓝 (uL (interface s t))) := by
  have hc : Continuous (fun x ↦ uL !₂[t, x]) := by fun_prop
  apply Tendsto.congr' _ hc.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with x hx
  symm
  apply profile_of_left
  exact hx.le

/-- The right classical field evaluated on the graph is the right trace
of the joined field at each fixed time. -/
theorem tendsto_profile_right {s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hR : Continuous uR) (t : ℝ) :
    Tendsto (fun x ↦ profile s uL uR !₂[t, x]) (𝓝[>] s t) (𝓝 (uR (interface s t))) := by
  have hc : Continuous (fun x ↦ uR !₂[t, x]) := by fun_prop
  apply Tendsto.congr' _ hc.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with x hx
  symm
  exact profile_of_right hx

/-- Composition acts on the two fields separately. -/
theorem comp_profile (G : ℝ → ℝ) (s : ℝ → ℝ) (uL uR : ℝ^2 → ℝ) :
    (fun p ↦ G (profile s uL uR p)) = profile s (fun p ↦ G (uL p)) (fun p ↦ G (uR p)) := by
  funext p
  by_cases hp : s (p 0) < p 1 <;> simp [profile, hp]

/-- Multiplication by a common field commutes with joining across the interface. -/
theorem profile_mul_right (s : ℝ → ℝ) (uL uR a : ℝ^2 → ℝ) :
    (fun p ↦ profile s uL uR p * a p) = profile s (fun p ↦ uL p * a p) (fun p ↦ uR p * a p) := by
  funext p
  by_cases hp : s (p 0) < p 1 <;> simp [profile, hp]

private theorem profile_eq_add_indicator (s : ℝ → ℝ) (uL uR : ℝ^2 → ℝ) :
    profile s uL uR = fun p ↦ uL p + (rightRegion s).indicator (fun q ↦ uR q - uL q) p := by
  funext p
  by_cases hp : s (p 0) < p 1 <;> simp [profile, rightRegion, hp]

/-- Local integrability on both sides gives local integrability of the joined field. -/
theorem locallyIntegrable_profile {s : ℝ → ℝ} (hs : Continuous s)
    {uL uR : ℝ^2 → ℝ} (hL : LocallyIntegrable uL) (hR : LocallyIntegrable uR) :
    LocallyIntegrable (profile s uL uR) := by
  rw [profile_eq_add_indicator]
  exact hL.add ((hR.sub hL).indicator (isOpen_rightRegion hs).measurableSet)

/-- Integrable fields remain integrable after joining across the graph. -/
theorem integrable_profile {s : ℝ → ℝ} (hs : Continuous s)
    {uL uR : ℝ^2 → ℝ} (hL : Integrable uL) (hR : Integrable uR) :
    Integrable (profile s uL uR) := by
  rw [profile_eq_add_indicator]
  exact hL.add ((hR.sub hL).indicator (isOpen_rightRegion hs).measurableSet)

/-- The integral is the left bulk integral plus the difference on the right. -/
theorem integral_profile {s : ℝ → ℝ} (hs : Continuous s)
    {uL uR : ℝ^2 → ℝ} (hL : Integrable uL) (hR : Integrable uR) :
    (∫ p, profile s uL uR p) = (∫ p, uL p) + ∫ p in rightRegion s, uR p - uL p := by
  have hi : Integrable (fun p ↦ (rightRegion s).indicator (fun q ↦ uR q - uL q) p) :=
    (hR.sub hL).indicator (isOpen_rightRegion hs).measurableSet
  rw [profile_eq_add_indicator, integral_add hL hi,
    integral_indicator (isOpen_rightRegion hs).measurableSet]

/-- The unnormalized outward conormal of the right-hand region, parametrized by time. -/
def conormal (s : ℝ → ℝ) (t : ℝ) : ℝ^2 := !₂[deriv s t, -1]

/-- Integrating the classical derivatives of two compactly supported fields
leaves only their jump on the moving interface. -/
theorem integral_profile_partialDeriv {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s)
    {fL fR : ℝ^2 → ℝ} (hL : ContDiff ℝ 1 fL) (hR : ContDiff ℝ 1 fR)
    (hcL : HasCompactSupport fL) (hcR : HasCompactSupport fR) (i : Fin 2) :
    (∫ p, profile s (∂[i] fL) (∂[i] fR) p) =
      ∫ t, conormal s t i * (fR (interface s t) - fL (interface s t)) := by
  rw [integral_profile hs.continuous (integrable_partialDeriv_of_hasCompactSupport i hL hcL)
    (integrable_partialDeriv_of_hasCompactSupport i hR hcR),
    integral_partialDeriv_eq_zero_of_hasCompactSupport i hL hcL, zero_add]
  have hd : (fun p ↦ (∂[i] fR) p - (∂[i] fL) p) =
      (∂[i] (fun p ↦ fR p - fL p)) := by
    funext p
    exact (partialDeriv_sub (hR.differentiable_one p) (hL.differentiable_one p)).symm
  rw [hd]
  fin_cases i
  · simpa [conormal] using integral_rightRegion_partialDeriv_time hs (hR.sub hL) (hcR.sub hcL)
  · change _ = ∫ t, (-1 : ℝ) * (fR (interface s t) - fL (interface s t))
    calc
      _ = -∫ t, fR (interface s t) - fL (interface s t) :=
        integral_rightRegion_partialDeriv_space hs (hR.sub hL) (hcR.sub hcL)
      _ = _ := by simp_rw [neg_one_mul, integral_neg]

/-- Integration by parts for a shock with varying C¹ fields retains the bulk
derivatives and derives the singular jump term from the moving graph. -/
theorem integral_profile_mul_partialDeriv {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s) {uL uR : ℝ^2 → ℝ}
    (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) (i : Fin 2) :
    (∫ p, profile s uL uR p * (∂[i] (φ : ℝ^2 → ℝ)) p) = (∫ t,
      conormal s t i * (uR (interface s t) - uL (interface s t)) * φ (interface s t)) - ∫ p,
      profile s (∂[i] uL) (∂[i] uR) p * φ p := by
  have hint : Integrable (fun p ↦ profile s uL uR p * (∂[i] (φ : ℝ^2 → ℝ)) p) :=
    φ.integrable_mul_partialDeriv
      ((locallyIntegrable_profile hs.continuous hL.continuous.locallyIntegrable
        hR.continuous.locallyIntegrable).locallyIntegrableOn univ) i
  have hbulk : Integrable (fun p ↦ profile s (∂[i] uL) (∂[i] uR) p * φ p) := by
    rw [profile_mul_right]
    have hdL := (contDiff_partialDeriv_of_succ (m := 0) (i := i) hL).continuous
    have hdR := (contDiff_partialDeriv_of_succ (m := 0) (i := i) hR).continuous
    exact integrable_profile hs.continuous
      ((hdL.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left)
      ((hdR.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left)
  have hjump := integral_profile_partialDeriv hs (hL.mul φ.contDiff) (hR.mul φ.contDiff)
    φ.hasCompactSupport.mul_left φ.hasCompactSupport.mul_left i
  have hprod (p : ℝ^2) : profile s (∂[i] (fun q ↦ uL q * φ q)) (∂[i] (fun q ↦ uR q * φ q)) p =
        profile s (∂[i] uL) (∂[i] uR) p * φ p +
          profile s uL uR p * (∂[i] (φ : ℝ^2 → ℝ)) p := by
    by_cases hp : s (p 0) < p 1
    · simp only [profile, ite_eq_left hp]
      exact partialDeriv_mul (hR.differentiable_one p) (φ.contDiff.differentiable_one p)
    · simp only [profile, ite_eq_right hp]
      exact partialDeriv_mul (hL.differentiable_one p) (φ.contDiff.differentiable_one p)
  simp_rw [hprod] at hjump
  rw [integral_add hbulk hint] at hjump
  have htrace : (∫ t, conormal s t i * (uR (interface s t) * φ (interface s t) -
          uL (interface s t) * φ (interface s t))) =
      ∫ t, conormal s t i * (uR (interface s t) - uL (interface s t)) *
        φ (interface s t) := by
    apply integral_congr_ae
    filter_upwards [] with t
    cas
  rw [htrace] at hjump
  linarith

/-- A continuous bulk equation on the open left side also holds at its trace.
Thus equations on the two open sides suffice to annihilate the joined residual. -/
theorem profile_eq_zero_of_bulk_eq_zero {s : ℝ → ℝ} {rL rR : ℝ^2 → ℝ} (hL : Continuous rL)
    (hPL : ∀ p, p 1 < s (p 0) → rL p = 0) (hPR : ∀ p, s (p 0) < p 1 → rR p = 0) :
    ∀ p, profile s rL rR p = 0 := by
  intro p
  by_cases hp : s (p 0) < p 1
  · rw [profile_of_right hp, hPR p hp]
  rw [profile_of_left (le_of_not_gt hp)]
  have he : EqOn (fun x ↦ rL !₂[p 0, x]) (fun _ ↦ 0) (Iio (s (p 0))) := by
    intro x hx
    apply hPL
    simpa using hx
  have hc : Continuous (fun x ↦ rL !₂[p 0, x]) := by fun_prop
  have hmem : p 1 ∈ closure (Iio (s (p 0))) := by
    rw [closure_Iio]
    exact le_of_not_gt hp
  have hpair : !₂[p 0, p 1] = p := by
    ext i
    fin_cases i <;> simp
  simpa only [hpair] using he.closure hc continuous_const hmem

private theorem integrable_profile_mul_testFunction {s : ℝ → ℝ} (hs : Continuous s)
    {aL aR : ℝ^2 → ℝ} (hL : Continuous aL) (hR : Continuous aR) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    Integrable (fun p ↦ profile s aL aR p * φ p) := by
  rw [profile_mul_right]
  exact integrable_profile hs
    ((hL.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left)
    ((hR.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left)

/-- The weak divergence of varying C¹ fields solving their respective bulk
equations is exactly the jump on the moving interface. The bulk equations are
required only on the open sides of the graph. -/
theorem integral_profile_divergence_of_bulk_eq_zero {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s)
    {aL aR bL bR : ℝ^2 → ℝ} (haL : ContDiff ℝ 1 aL) (haR : ContDiff ℝ 1 aR) (hbL : ContDiff ℝ 1 bL)
    (hbR : ContDiff ℝ 1 bR) (hPL : ∀ p, p 1 < s (p 0) → (∂[0] aL) p + (∂[1] bL) p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → (∂[0] aR) p + (∂[1] bR) p = 0) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p, profile s aL aR p * (∂[0] (φ : ℝ^2 → ℝ)) p + profile s bL bR p * (∂[1] (φ : ℝ^2 → ℝ)) p) =
      ∫ t, (deriv s t * (aR (interface s t) - aL (interface s t)) -
      (bR (interface s t) - bL (interface s t))) * φ (interface s t) := by
  have hdaL := (contDiff_partialDeriv_of_succ (m := 0) (i := 0) haL).continuous
  have hdaR := (contDiff_partialDeriv_of_succ (m := 0) (i := 0) haR).continuous
  have hdbL := (contDiff_partialDeriv_of_succ (m := 0) (i := 1) hbL).continuous
  have hdbR := (contDiff_partialDeriv_of_succ (m := 0) (i := 1) hbR).continuous
  have hzero : ∀ p, profile s (fun q ↦ (∂[0] aL) q + (∂[1] bL) q)
      (fun q ↦ (∂[0] aR) q + (∂[1] bR) q) p = 0 :=
    profile_eq_zero_of_bulk_eq_zero (hdaL.add hdbL) hPL hPR
  have hbulk : (∫ p, profile s (∂[0] aL) (∂[0] aR) p * φ p) +
      (∫ p, profile s (∂[1] bL) (∂[1] bR) p * φ p) = 0 := by
    rw [← integral_add (integrable_profile_mul_testFunction hs.continuous hdaL hdaR φ)
      (integrable_profile_mul_testFunction hs.continuous hdbL hdbR φ)]
    apply integral_eq_zero_of_ae
    filter_upwards [] with p
    have hz := hzero p
    by_cases hp : s (p 0) < p 1
    · simp only [profile, ite_eq_left hp] at hz ⊢
      calc
        _ = ((∂[0] aR) p + (∂[1] bR) p) * φ p := by cas
        _ = 0 := by rw [hz, zero_mul]
    · simp only [profile, ite_eq_right hp] at hz ⊢
      calc
        _ = ((∂[0] aL) p + (∂[1] bL) p) * φ p := by cas
        _ = 0 := by rw [hz, zero_mul]
  have hta := φ.integrable_mul_partialDeriv
    ((locallyIntegrable_profile hs.continuous haL.continuous.locallyIntegrable
      haR.continuous.locallyIntegrable).locallyIntegrableOn univ) 0
  have htb := φ.integrable_mul_partialDeriv
    ((locallyIntegrable_profile hs.continuous hbL.continuous.locallyIntegrable
      hbR.continuous.locallyIntegrable).locallyIntegrableOn univ) 1
  rw [integral_add hta htb, integral_profile_mul_partialDeriv hs haL haR φ 0,
    integral_profile_mul_partialDeriv hs hbL hbR φ 1]
  have hc := continuous_interface hs.continuous
  have hia : Integrable (fun t ↦ deriv s t *
      (aR (interface s t) - aL (interface s t)) * φ (interface s t)) :=
    integrable_mul_interface_comp hs.continuous
      (hs.continuous_deriv_one.mul ((haR.continuous.comp hc).sub (haL.continuous.comp hc)))
      φ.continuous φ.hasCompactSupport
  have hib : Integrable (fun t ↦ (bR (interface s t) - bL (interface s t)) * φ (interface s t)) :=
    integrable_mul_interface_comp hs.continuous
      ((hbR.continuous.comp hc).sub (hbL.continuous.comp hc)) φ.continuous φ.hasCompactSupport
  have htrace : (∫ t, conormal s t 0 * (aR (interface s t) - aL (interface s t)) *
        φ (interface s t)) + (∫ t, conormal s t 1 * (bR (interface s t) - bL (interface s t)) *
        φ (interface s t)) = ∫ t, (deriv s t * (aR (interface s t) - aL (interface s t)) -
        (bR (interface s t) - bL (interface s t))) * φ (interface s t) := by
    change (∫ t, deriv s t * (aR (interface s t) - aL (interface s t)) *
      φ (interface s t)) + (∫ t, -1 * (bR (interface s t) - bL (interface s t)) *
      φ (interface s t)) = _
    simp_rw [neg_one_mul, neg_mul, integral_neg]
    rw [← sub_eq_add_neg, ← integral_sub hia hib]
    apply integral_congr_ae
    filter_upwards [] with t
    cas
  linarith

end PDE.Hyperbolic.ConservationLaw.Scalar.Shock

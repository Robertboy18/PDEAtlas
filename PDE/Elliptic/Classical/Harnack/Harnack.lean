/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harnack.Compact
public import PDE.Elliptic.Classical.Harnack.Coefficients
public import PDE.Analysis.Order.SupInfComparison

/-!
# Harnack's inequality for variable-coefficient elliptic operators

Evans's §6.4.3, Theorem 5 (Harnack's inequality) holds for the nondivergence operator
`EllipticMaximum.matrixOperator a b c` (his (2) in §6.4) on a bounded open set `U`. The coefficients
are bounded and continuous, the principal matrix is symmetric and uniformly elliptic, and the
potential may have either sign. For every connected set `V` whose closure lies in `U` there is
`C > 0`, chosen before the solution, with `sup_V u ≤ C inf_V u` for every nonnegative `C²` solution
of `Lu = 0` in `U`. Only `V` needs to be connected.

Ellipticity and the coefficient bounds may be stated almost everywhere; continuity extends them to
every point of `U`.

## Main results

* `exists_harnack_constant`: Evans's Theorem 5, (18), for bounded continuous coefficients and
  almost-everywhere ellipticity.
* `exists_harnack_constant_of_ae_bounds`: the same with essential bounds on the coefficients in
  place of bounded ranges.

## How it works

Evans proves (18) only when `b = c = 0` and the `aᵢⱼ` are smooth, and refers to Gilbarg and
Trudinger for bounded measurable coefficients. For `v = log u` he derives the differential
inequality (27) for `w = ∑ aᵢⱼ ∂ᵢv ∂ⱼv` by differentiating the equation, which puts derivatives on
the coefficients, bounds `ζ⁴w` at its maximum to get `|Dv| ≤ C` on a ball (34), and covers `V` by
balls. We never differentiate a coefficient. Paraboloids of fixed opening, slid from below with
vertices near a point where `u ≤ 1`, touch `u` at points of the sublevel set `{u ≤ 5/4}`; the
contact map covers a ball of vertices, and at each contact point the equation bounds its Jacobian.
`measure_vertexBall_le_mul_measure_sublevel` in `Local.Density` combines these facts with the area
estimate of `PDE.Analysis.MeasureTheory.Contact.Image` into a lower bound on the measure of the
sublevel set. `Local.LevelDecay` iterates this bound over subcubes into geometric decay of
superlevel sets, and `Local.UpperBound` and `Local.ZeroPotential` turn the decay into a local
comparison for zero potential. `Local.SignedPotential` removes the potential by passing to
`exp(s) u(x)` in one more dimension, and `Compact` chains the local comparisons along interior balls
covering `closure V`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4, the nondivergence form (2), p. 344, and §6.4.3,
  Theorem 5 (Harnack's inequality), (18), and its proof, (19)-(34), pp. 351-354.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum MeasureTheory Set
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

/-- Full variable-coefficient Harnack inequality with essentially bounded
continuous coefficients and almost-everywhere ellipticity.
The potential is signed and the solution is nonnegative, including its zeros.
There is no boundary or coefficient differentiability assumption. -/
theorem exists_harnack_constant_of_ae_bounds
    {U V : Set (ℝ^n)} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hV : IsPreconnected V) (hVU : closure V ⊆ U)
    {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {b : ℝ^n → ℝ^n} {c : ℝ^n → ℝ}
    (ha : ContinuousOn a U) (hb : ContinuousOn b U) (hc : ContinuousOn c U)
    (hsymm : ∀ x ∈ U, (a x).IsSymm)
    (hell : ∃ α : ℝ, 0 < α ∧ ∀ᵐ x ∂volume.restrict U, ∀ v : ℝ^n,
      α * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j)
    (habound : ∃ A : ℝ, ∀ᵐ x ∂volume.restrict U, ‖a x‖ ≤ A)
    (hbbound : ∃ B : ℝ, ∀ᵐ x ∂volume.restrict U, ‖b x‖ ≤ B)
    (hcbound : ∃ K : ℝ, ∀ᵐ x ∂volume.restrict U, |c x| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ^n → ℝ, ContDiffOn ℝ 2 u U →
      (∀ x ∈ U, 0 ≤ u x) → (∀ x ∈ U, matrixOperator a b c u x = 0) →
      sSup (u '' V) ≤ C * sInf (u '' V) := by
  obtain ⟨α, hα, hellae⟩ := hell
  obtain ⟨A, hA⟩ := habound
  obtain ⟨B, hB⟩ := hbbound
  obtain ⟨K, hK⟩ := hcbound
  have ha_bound := leOn_open_of_ae_le hU ha.norm continuousOn_const
    (hA.mono fun _ hx ↦ hx.trans (le_max_left A 0))
  have hb_bound := leOn_open_of_ae_le hU hb.norm continuousOn_const
    (hB.mono fun _ hx ↦ hx.trans (le_max_left B 0))
  have hc_bound := leOn_open_of_ae_le hU hc.abs continuousOn_const
    (hK.mono fun _ hx ↦ hx.trans (le_max_left K 0))
  have hellpoint := elliptic_on_open_of_ae hU ha hellae
  have hcompact : IsCompact (closure V) :=
    (hbounded.subset (subset_closure.trans hVU)).isCompact_closure
  obtain ⟨C, hC, hcompare⟩ := exists_harnack_comparison_on_closure hU hV hcompact hVU
    (τ := (n : ℝ) * max A 0) (B := max B 0) (K := max K 0)
    hα (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro u hreg hnonneg hsol
  have hpair := hcompare a b c
    (fun x hx ↦ posSemidef_of_elliptic (hsymm x hx) hα.le (hellpoint x hx))
    hellpoint (fun x hx ↦ trace_le_dim_mul_of_norm_le (ha_bound x hx))
    hb_bound hc_bound u (fun x hx ↦ (hreg x hx).contDiffAt (hU.mem_nhds hx))
    hnonneg hsol
  exact sSup_image_le_mul_sInf_image_of_pairwise hC
    (fun x hx y hy ↦ hpair x (subset_closure hx) y (subset_closure hy))

/-- Evans's §6.4.3, Theorem 5 (Harnack's inequality) for bounded continuous coefficients.
Boundedness means bounded coefficient ranges on `U`; ellipticity is allowed almost everywhere.
The constant `C` is chosen before the solution and serves every nonnegative `C²(U)` solution,
for a potential of either sign. -/
theorem exists_harnack_constant
    {U V : Set (ℝ^n)} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hV : IsPreconnected V) (hVU : closure V ⊆ U)
    {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {b : ℝ^n → ℝ^n} {c : ℝ^n → ℝ}
    (ha : ContinuousOn a U) (hb : ContinuousOn b U) (hc : ContinuousOn c U)
    (habound : Bornology.IsBounded (a '' U))
    (hbbound : Bornology.IsBounded (b '' U))
    (hcbound : Bornology.IsBounded (c '' U))
    (hsymm : ∀ x ∈ U, (a x).IsSymm)
    (hell : ∃ α : ℝ, 0 < α ∧ ∀ᵐ x ∂volume.restrict U, ∀ v : ℝ^n,
      α * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ^n → ℝ, ContDiffOn ℝ 2 u U →
      (∀ x ∈ U, 0 ≤ u x) → (∀ x ∈ U, matrixOperator a b c u x = 0) →
      sSup (u '' V) ≤ C * sInf (u '' V) := by
  obtain ⟨A, hA⟩ := habound.exists_norm_le
  obtain ⟨B, hB⟩ := hbbound.exists_norm_le
  obtain ⟨K, hK⟩ := hcbound.exists_norm_le
  apply exists_harnack_constant_of_ae_bounds hU hbounded hV hVU ha hb hc hsymm hell
  · exact ⟨A, (ae_restrict_mem hU.measurableSet).mono
      fun x hx ↦ hA _ (mem_image_of_mem a hx)⟩
  · exact ⟨B, (ae_restrict_mem hU.measurableSet).mono
      fun x hx ↦ hB _ (mem_image_of_mem b hx)⟩
  · exact ⟨K, (ae_restrict_mem hU.measurableSet).mono
      fun x hx ↦ hK _ (mem_image_of_mem c hx)⟩

end EllipticHarnack

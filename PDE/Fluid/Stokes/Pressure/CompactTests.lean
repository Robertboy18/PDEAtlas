/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Pressure.Potential
import PDE.Spaces.Sobolev.Calculus.Divergence.LocalFunctional
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactPairing
import PDE.DistributionTheory.TestFunction

/-!
# Stokes pressure tested against compactly supported native H¹ fields

The pressure obtained from the raw constrained minimum is only locally L². It satisfies the
weak equation against every compactly supported native H¹ test
(`exists_pressure_of_minimizes_energy`). Each integral is integrable, and no boundary trace or
global pressure norm is used.

This is the weak pressure identity (39) of Evans (§8.4.4(a), Theorem 6), which is stated for a
bounded, simply connected open set in `ℝ^3`. The construction works in every positive dimension
on arbitrary open sets.

## How it works

Evans mollifies the minimizer, uses simple connectedness to write the mollified residual, which is
curl free, as a gradient on subdomains, and then exhausts `U`. We avoid this topological step. The
first variation of the energy vanishes on all divergence-free fields, so it factors through the
divergence and gives a scalar functional on tests whose derivatives are minus the residual. The
vorticity has locally L² first weak derivatives
(`exists_vorticity_weak_derivatives_of_minimizes_energy`), so the residual `Δu + f` is locally L²
(`exists_locally_memLp_residual_of_minimizes_energy`). Local potentials of the residual on balls,
with their constants fixed by the scalar functional, glue to a locally L² pressure with
`Dp = Δu + f` (`exists_pressure_distribution_of_minimizes_energy`, through
`exists_weak_potential_of_linearMap_partialDeriv`). Localizing the stress `Du - p Id` passes the
identity from smooth tests to compactly supported H¹ tests
(`exists_pressure_compact_test_identity_of_minimizes_energy`), and
`exists_pressure_of_minimizes_energy` collects the integrability of each term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.4(a), Theorem 6 (Pressure as Lagrange multiplier) and
  its proof, pp. 497-499.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal Distributions

namespace IncompressibleFlow.Stokes

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)}

/-- The pressure reconstructed from a raw divergence-free energy minimizer
satisfies the component weak equation on every compactly supported native H¹
test, with the sign `-Δu = f - Dp`. -/
theorem exists_pressure_compact_test_identity_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp p 2 (domainMeasure n K)) ∧
      ∀ (j : Fin n) (v : H¹(Ω)) (K : Set (ℝ^n)),
        IsCompact K → K ⊆ Ω →
        (∀ᵐ x ∂domainMeasure n Ω, x ∉ K →
          baseRepresentative v x = 0) →
        (∑ k : Fin n, ∫ x in (Ω : Set (ℝ^n)), derivCoordCLM k (u j) x *
          v.val (singleDerivIndex n k) x) =
          (∫ x in (Ω : Set (ℝ^n)), p x *
            v.val (singleDerivIndex n j) x) +
          ∫ x in (Ω : Set (ℝ^n)), f x j *
            baseRepresentative v x := by
  classical
  obtain ⟨p, hp, hpLp, htest⟩ :=
    exists_pressure_test_identity_of_minimizes_energy f u hu hmin
  have hplocal : LocallyIntegrableOn p (Ω : Set (ℝ^n)) volume :=
    (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).mpr fun K hKΩ hK ↦
      haveI : IsFiniteMeasure (domainMeasure n K) :=
        isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
      (hpLp K hK hKΩ).integrable (by norm_num)
  refine ⟨p, hp, hpLp, fun j v K hK hKΩ hv ↦ ?_⟩
  let q (k : Fin n) (x : ℝ^n) : ℝ :=
    derivCoordCLM k (u j) x - if k = j then p x else 0
  have hdLp (k : Fin n) (A : Set (ℝ^n)) (hAΩ : A ⊆ Ω) :
      MemLp (derivCoordCLM k (u j) : ℝ^n → ℝ) 2 (domainMeasure n A) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hAΩ le_rfl)
  have hqLp (k : Fin n) (A : Set (ℝ^n)) (hA : IsCompact A) (hAΩ : A ⊆ Ω) :
      MemLp (q k) 2 (domainMeasure n A) := by
    by_cases hkj : k = j
    · have hs : MemLp (fun x ↦ derivCoordCLM j (u j) x - p x) 2 (domainMeasure n A) :=
        (hdLp j A hAΩ).sub (hpLp A hA hAΩ)
      simpa only [q, hkj, ite_true] using hs
    · simpa only [q, hkj, ite_false, sub_zero] using hdLp k A hAΩ
  have hfLp : MemLp (fun x ↦ f x j) 2 (domainMeasure n Ω) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (Lp.memLp f)
  -- pairing `q` with a family `g` splits off the pressure term of the `j`-th coordinate
  have hsplit (g : Fin n → ℝ^n → ℝ)
      (hd : ∀ k, Integrable (fun x ↦ derivCoordCLM k (u j) x * g k x) (domainMeasure n Ω))
      (hpg : Integrable (fun x ↦ p x * g j x) (domainMeasure n Ω)) :
      ∑ k, ∫ x, q k x * g k x ∂domainMeasure n Ω =
        (∑ k, ∫ x, derivCoordCLM k (u j) x * g k x ∂domainMeasure n Ω) -
          ∫ x, p x * g j x ∂domainMeasure n Ω := by
    have hpi (k : Fin n) :
        Integrable (fun x ↦ (if k = j then p x else 0) * g k x) (domainMeasure n Ω) := by
      split_ifs with hkj
      · exact hkj ▸ hpg
      · simp
    simp only [q, sub_mul, integral_sub (hd _) (hpi _), Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single j (fun k _ hkj ↦ by simp [hkj]) (by simp)]
    simp
  have hsmooth (φ : TestFunctionOn n (Ω : Set (ℝ^n))) :
      (∑ k, ∫ x, q k x * (∂[k] φ.1.toFun) x ∂domainMeasure n Ω) =
        ∫ x, f x j * φ.1.toFun x ∂domainMeasure n Ω := by
    let ψ : 𝓓^{1}(Ω, ℝ) :=
      ⟨φ.1, φ.1.contDiff.of_le (by simp), φ.1.hasCompactSupport, φ.2⟩
    rw [hsplit (fun k ↦ ∂[k] φ.1.toFun) (fun k ↦ (ψ.integrable_mul_partialDeriv
        (memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num)) k).integrableOn)
      (ψ.integrable_mul_partialDeriv hplocal j).integrableOn]
    exact sub_eq_iff_eq_add.mpr ((htest j φ).trans (add_comm _ _))
  have heq := weakDivergence_integral_of_compact_base_support Ω.isOpen q
    (fun x ↦ f x j) hqLp
    (fun A _ hAΩ ↦ hfLp.mono_measure (Measure.restrict_mono hAΩ le_rfl))
    hsmooth v hK hKΩ hv
  rw [hsplit (fun k ↦ v.val (singleDerivIndex n k))
    (fun k ↦ (Lp.memLp _).integrable_mul (Lp.memLp _))
    (integrable_mul_coordinate_of_compact_base_support Ω.isOpen p hpLp v hK hKΩ hv
      (singleDerivIndex n j))] at heq
  exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)

/-- A raw constrained Stokes minimum has a locally L² scalar pressure, and
the full matrix weak equation holds on every compactly supported native H¹
vector test. Both sides are integrable functions. The domain need
only be open; in particular the bounded, simply connected three-dimensional
domains of Evans's pressure theorem are included. -/
theorem exists_pressure_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp p 2 (domainMeasure n K)) ∧
      ∀ (v : Fin n → H¹(Ω)) (K : Set (ℝ^n)),
        IsCompact K → K ⊆ Ω →
        (∀ j, ∀ᵐ x ∂domainMeasure n Ω, x ∉ K →
          baseRepresentative (v j) x = 0) →
        Integrable (fun x ↦ ∑ j : Fin n, ∑ k : Fin n,
          derivCoordCLM k (u j) x *
            (v j).val (singleDerivIndex n k) x)
          (domainMeasure n Ω) ∧
        Integrable (fun x ↦ p x * (∑ j : Fin n,
          (v j).val (singleDerivIndex n j) x) +
          ∑ j : Fin n, f x j * baseRepresentative (v j) x)
          (domainMeasure n Ω) ∧
        (∫ x in (Ω : Set (ℝ^n)), ∑ j : Fin n, ∑ k : Fin n,
          derivCoordCLM k (u j) x *
            (v j).val (singleDerivIndex n k) x) =
        ∫ x in (Ω : Set (ℝ^n)), p x * (∑ j : Fin n,
          (v j).val (singleDerivIndex n j) x) +
          ∑ j : Fin n, f x j * baseRepresentative (v j) x := by
  obtain ⟨p, hp, hpLp, hcomponent⟩ :=
    exists_pressure_compact_test_identity_of_minimizes_energy f u hu hmin
  refine ⟨p, hp, hpLp, fun v K hK hKΩ hv ↦ ?_⟩
  let a (j k : Fin n) (x : ℝ^n) := derivCoordCLM k (u j) x * (v j).val (singleDerivIndex n k) x
  let b (j : Fin n) (x : ℝ^n) := p x * (v j).val (singleDerivIndex n j) x
  let c (j : Fin n) (x : ℝ^n) := f x j * baseRepresentative (v j) x
  have ha (j k : Fin n) : Integrable (a j k) (domainMeasure n Ω) :=
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hb (j : Fin n) : Integrable (b j) (domainMeasure n Ω) :=
    integrable_mul_coordinate_of_compact_base_support Ω.isOpen p hpLp (v j) hK hKΩ (hv j)
      (singleDerivIndex n j)
  have hc (j : Fin n) : Integrable (c j) (domainMeasure n Ω) := by
    have hf : MemLp (fun x ↦ f x j) 2 (domainMeasure n Ω) := by
      simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
        (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (Lp.memLp f)
    exact hf.integrable_mul (Lp.memLp _)
  have haSum (j : Fin n) : Integrable (fun x ↦ ∑ k, a j k x) (domainMeasure n Ω) :=
    integrable_finsetSum _ fun k _ ↦ ha j k
  have hbSum : Integrable (fun x ↦ ∑ j, b j x) (domainMeasure n Ω) :=
    integrable_finsetSum _ fun j _ ↦ hb j
  have hcSum : Integrable (fun x ↦ ∑ j, c j x) (domainMeasure n Ω) :=
    integrable_finsetSum _ fun j _ ↦ hc j
  simp only [Finset.mul_sum]
  change Integrable (fun x ↦ ∑ j, ∑ k, a j k x) (domainMeasure n Ω) ∧
    Integrable (fun x ↦ (∑ j, b j x) + ∑ j, c j x) (domainMeasure n Ω) ∧
    (∫ x, ∑ j, ∑ k, a j k x ∂domainMeasure n Ω) =
      ∫ x, (∑ j, b j x) + ∑ j, c j x ∂domainMeasure n Ω
  refine ⟨integrable_finsetSum _ fun j _ ↦ haSum j, hbSum.add hcSum, ?_⟩
  rw [integral_finsetSum _ (fun j _ ↦ haSum j), integral_add hbSum hcSum,
    integral_finsetSum _ (fun j _ ↦ hb j), integral_finsetSum _ (fun j _ ↦ hc j),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ (integral_finsetSum _ fun k _ ↦ ha j k).trans
    (hcomponent j (v j) K hK hKΩ (hv j))

end IncompressibleFlow.Stokes

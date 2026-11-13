/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.PhysicalEnergyLimit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.SecondOrderExistence
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.VelocityTrace
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak wave solutions with the original Cauchy traces

Sign-preserving truncations construct a weakly continuous displacement and velocity on the forward
half-line. The displacement equation holds as an L² Bochner integral, while compact spatial testing
gives the velocity equation with the original arbitrary-growth reaction. Both initial values are
attained. The full H¹ bound is finite-time; the gradient and velocity bounds are global.

The original potential is integrable at every time and the full physical energy is bounded by the
original initial energy.

This is Theorem 1 of Evans, §12.3.1, for a C¹ reaction in place of a smooth one, with two changes to
its conclusion. The H¹ bound holds on each finite time interval, as (7) of Evans's proof gives;
`not_memLp_lpNorm_freeWave` shows that the bound for all time fails for a free wave. The reaction is
locally integrable, as in (9), and is tested against bounded compactly supported H¹ functions;
`exists_energyDatum_no_seventh_power_trajectory` shows that for some finite-energy data it is not in
the class `L²(0,T; L²_loc)` of the weak solutions of §12.2.

## How it works

We follow Evans's proof. Sign-preserving Lipschitz truncations of the reaction (step 1) have energy
solutions with uniform energy bounds (step 2). The displacement-velocity identity bounds the
reaction product `u f(u)` (step 3), which gives uniform integrability and L¹ convergence of the
truncated reactions (steps 4-5). Local compactness of the displacements then passes the equation and
the energy inequality to the limit (step 6).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, definition of a weak solution; §12.3.1, Theorem 1 and
  its proof, equations (2)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Sign-condition data admit a global weak wave solution with both
Cauchy traces, a finite-time H¹ bound, and globally bounded L² velocity and
gradient. The original potential is integrable and the full physical energy
never exceeds the initial energy. Local reaction integrability follows from the
truncated equations.
The reaction is tested against bounded compactly supported H¹ representatives. -/
theorem exists_weak_solution_with_traces {n : ℕ} {m : ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ m f)
    (hm : m ≠ 0) (hs : ∀ z, 0 ≤ z * f z) (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (hF : Integrable (fun y ↦ primitive f ((energyTriple n).inclusion x.1 y))
      (domainMeasure n univ)) :
    ∃ q : Ici (0 : ℝ) → H¹(ℝ^n), ∃ v : Ici (0 : ℝ) → DerivLp n 2 univ,
      q ⟨0, le_rfl⟩ = x.1 ∧ v ⟨0, le_rfl⟩ = x.2 ∧
      Continuous (fun t ↦ toWeakSpace ℝ H¹(ℝ^n) (q t)) ∧
      Continuous (fun t ↦ toWeakSpace ℝ (DerivLp n 2 univ) (v t)) ∧
      LipschitzWith ⟨Real.sqrt (2 * physicalEnergy f x), Real.sqrt_nonneg _⟩
        (fun t ↦ (energyTriple n).inclusion (q t)) ∧
      (∀ t, ‖q t‖ ≤ ‖(energyTriple n).inclusion x.1‖ +
        (t.val + 1) * Real.sqrt (2 * physicalEnergy f x)) ∧
      (∀ t, gradientForm n (q t) (q t) ≤ 2 * physicalEnergy f x) ∧
      (∀ t, ‖v t‖ ≤ Real.sqrt (2 * physicalEnergy f x)) ∧
      (∀ t, Integrable (fun y ↦ primitive f ((energyTriple n).inclusion (q t) y))
        (domainMeasure n univ) ∧ physicalEnergy f (q t, v t) ≤ physicalEnergy f x) ∧
      (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (IciExtend v) volume 0 T ∧
        (∫ t in (0 : ℝ)..T, IciExtend v t) =
          (energyTriple n).inclusion (IciExtend q T) - (energyTriple n).inclusion x.1) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ V : ℝ × (ℝ^n) → ℝ,
        StronglyMeasurable V ∧
        MemLp V 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ∧
        (∀ᵐ t ∂volume.restrict (Ioc 0 T),
          (fun y ↦ V (t, y)) =ᵐ[domainMeasure n univ]
            (energyTriple n).inclusion (IciExtend q t)) ∧
        (∀ s : Set (ℝ^n), IsCompact s → Integrable (fun z ↦ f (V z))
          ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s))) ∧
        ∀ s : Set (ℝ^n), IsCompact s → ∀ w : H¹(ℝ^n), ∀ ψ : (ℝ^n) → ℝ,
          StronglyMeasurable ψ → ∀ C : NNReal, (∀ y, ‖ψ y‖ ≤ C) →
          (∀ y, y ∉ s → ψ y = 0) →
          (((energyTriple n).inclusion w : (ℝ^n) → ℝ) =ᵐ[domainMeasure n univ] ψ) →
          ∀ t ∈ Icc 0 T,
          ⟪IciExtend v t, (energyTriple n).inclusion w⟫_ℝ =
            ⟪x.2, (energyTriple n).inclusion w⟫_ℝ -
              (∫ r in (0 : ℝ)..t, gradientForm n (IciExtend q r) w) -
              ∫ r in (0 : ℝ)..t, ∫ y, f (V (r, y)) * ψ y ∂domainMeasure n univ := by
  obtain ⟨g, K, hg, hg0, u, htr, hu, _, _, he, _, _⟩ := exists_energy_approximations hf hm hs x hF
  have hr : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨q, φ, hφ, hq0, hqc, hqlip, hqb, hqg, hweak, hcut, hlocal⟩ :=
    exists_energy_displacement_reaction_limit
      (g := g) (K := K) (E := physicalEnergy f x) hf.continuous hg
      (fun k ↦ (htr k).2.2.2.1) (fun k ↦ (htr k).2.2.2.2.1) (fun k ↦ (htr k).2.2.1) hr x u hu he
  have hqd (T : ℝ) (ell : StrongDual ℝ H¹(ℝ^n)) := tendstoUniformlyOn_dual_IciExtend
      (u := fun i t ↦ (u (φ i) t).1) (q := q) hweak T ell
  obtain ⟨v, η, hη, hv0, hvb, hvc, hv⟩ := exists_weak_velocity_limit_of_local_reaction_convergence
      (g := fun i ↦ g (φ i)) (K := fun i ↦ K (φ i))
      (hg := fun i ↦ hg (φ i)) (hg0 := fun i ↦ hg0 (φ i)) (x := x)
      (u := fun i ↦ u (φ i)) (q := IciExtend q) (fun i ↦ hu (φ i)) (fun k ↦ hqd k)
      (fun i t ht ↦ norm_velocity_le_of_energy_le (hg (φ i)) (htr (φ i)).2.2.2.1 (he (φ i) t ht))
      (fun k ↦ by
        obtain ⟨U, V, _, _, hU, _, hUsec, _, hlim⟩ := hlocal k (Nat.cast_nonneg k)
        exact ⟨U, fun z ↦ f (V z), hU, hUsec, fun s hs ↦ (hlim s hs).2⟩)
  have hqn (T : ℝ) (ell : StrongDual ℝ H¹(ℝ^n)) :=
    (hqd T ell).seq_tendstoUniformlyOn η hη.tendsto_atTop
  have hvn (T : ℝ) (w : DerivLp n 2 univ) := tendstoUniformlyOn_dual_IciExtend
      (u := fun i t ↦ (u (φ (η i)) t).2) (q := v) hv T (innerSL ℝ w)
  have hfull (t : Ici (0 : ℝ)) :
      Integrable (fun y ↦ primitive f ((energyTriple n).inclusion (q t) y))
        (domainMeasure n univ) ∧ physicalEnergy f (q t, v t) ≤ physicalEnergy f x := by
    apply physicalEnergy_le_of_truncated_weak_local_limit
      (g := fun i ↦ g (φ (η i))) (K := fun i ↦ K (φ (η i)))
      (u := fun i ↦ u (φ (η i)) t) (z := (q t, v t)) hf.continuous hs
      (fun i ↦ hg (φ (η i))) (fun i ↦ (htr (φ (η i))).2.2.2.1) (fun i ↦ (htr (φ (η i))).2.2.1)
      ((hr.comp hφ.tendsto_atTop).comp hη.tendsto_atTop)
    · intro ell
      simpa only [IciExtend_coe] using
        (hqn t.val ell).tendsto_at (show t.val ∈ Icc 0 t.val from ⟨t.property, le_rfl⟩)
    · intro ell
      have h := tendstoUniformlyOn_dual_IciExtend
        (u := fun i r ↦ (u (φ (η i)) r).2) (q := v) hv t.val ell
      simpa only [IciExtend_coe] using
        h.tendsto_at (show t.val ∈ Icc 0 t.val from ⟨t.property, le_rfl⟩)
    · intro χ
      obtain ⟨k, hk⟩ := exists_nat_ge t.val
      exact ((hcut k χ).tendsto_at ⟨t.val, t.property, hk⟩).comp hη.tendsto_atTop
    · intro i
      exact he (φ (η i)) t t.property
  refine ⟨q, v, hq0, hv0, hqc, hvc, hqlip, hqb, hqg, hvb, hfull, ?_, ?_⟩
  · intro T hT
    have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
    have : SecondCountableTopology (DerivLp n 2 univ) := Lp.SecondCountableTopology
    have hvi := intervalIntegrable_IciExtend_of_weakly_continuous hvc hvb hT
    refine ⟨hvi, ?_⟩
    exact displacement_integral_eq_of_weak_limits
      (g := fun i ↦ g (φ (η i))) (K := fun i ↦ K (φ (η i)))
      (hg := fun i ↦ hg (φ (η i))) (hg0 := fun i ↦ hg0 (φ (η i))) (x := x)
      (u := fun i ↦ u (φ (η i))) (q := IciExtend q) (v := IciExtend v)
      (fun i ↦ hu (φ (η i))) hT (hqn T) (hvn T) hvi
  · intro T hT
    obtain ⟨U, V, _, hV, hU, hVm, hUsec, hVsec, hlim⟩ := hlocal T hT
    refine ⟨V, hV, hVm, hVsec, fun s hs ↦ (hlim s hs).2.1, ?_⟩
    intro s hs w ψ hψ C hb hsupp hw t ht
    have : IsFiniteMeasure ((domainMeasure n univ).restrict s) :=
      isFiniteMeasure_restrict.mpr hs.measure_ne_top
    obtain ⟨hR, hRlim⟩ := tendsto_L1_reaction_pairing_of_joint_convergence
      (fun i ↦ hg (φ i)) (fun i ↦ hg0 (φ i)) hU hUsec
      (hlim s hs).2.1 (hlim s hs).2.2 ((energyTriple n).inclusion w) hψ hb hsupp hw
    exact velocity_pairing_eq_of_weak_limits (g := fun i ↦ g (φ (η i))) (K := fun i ↦ K (φ (η i)))
      (hg := fun i ↦ hg (φ (η i))) (hg0 := fun i ↦ hg0 (φ (η i))) (x := x)
      (u := fun i ↦ u (φ (η i))) (q := IciExtend q) (v := IciExtend v)
      (fun i ↦ hu (φ (η i))) (hqn T) (hvn T) w hR (hRlim.comp hη.tendsto_atTop) ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

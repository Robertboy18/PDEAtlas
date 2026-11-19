/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.ClassicalEnergy.WeakSolution
public import PDE.Fluid.NavierStokes.LocalEnergy.Testing
import PDE.Analysis.MeasureTheory.Lp.SliceCurve
import PDE.Fluid.NavierStokes.ClassicalEnergy.EnergyEquality

/-!
# Classical solutions in the energy class are suitable Leray–Hopf solutions

A velocity and pressure that are smooth on the open slab `(0,T) × ℝ^3`, solve the unforced
Navier–Stokes equations there, lie in `ClassicalEnergyClass` and take an `L²` initial trace
form a suitable Leray–Hopf solution (`suitableLerayHopf_of_classical`).

## How it works

The velocity slices are continuous into `L²` on `[0,T]`
(`ClassicalSolutionData.continuousOn_velocityL2Slice`): on `(0,T]` by the energy class and at time
zero by the trace. This gives the `L∞(0,T; L²)` bound and weak continuity. The slice gradient is in
`L²(0,T; L²)` by the Pettis theorem in `L²` (`ClassicalSolutionData.gradient_memLp_two`). The energy
equality on `[s,t] ⊂ (0,T)` (`kineticEnergy_add_integral_weakGradientDissipation_eq`) makes
`½ ‖u(t)‖² + ν ∫₀ᵗ ‖∇u‖²` constant on `(0,T)`; by continuity it equals `½ ‖u₀‖²` on `[0,T]`
(`ClassicalSolutionData.kineticEnergy_add_dissipation_eq`), which is the energy inequality with
equality. Smoothness on the open slab gives the local energy inequality
(`PressureRepresentativeLerayHopfSolution.toSuitableOfPositiveTimeRegular`).
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory Filter IncompressibleFlow PDE PDE.Common
open scoped Topology ENNReal

set_option linter.missingDocs true

variable {n : ℕ}

/-- The hypotheses of the classical construction: zero forcing, a `C²` velocity and `C¹`
pressure solving the equations on the open slab, the energy class, the initial values and the
`L²` initial trace. -/
structure ClassicalSolutionData (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (T : ℝ) : Prop where
  /-- The forcing vanishes. -/
  forcing_eq_zero : nse.forcing = 0
  /-- The velocity is `C²` on the open slab. -/
  velocity_contDiffAt : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z
  /-- The pressure is `C¹` on the open slab. -/
  pressure_contDiffAt : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z
  /-- The velocity is divergence free on the open slab. -/
  divergenceFreeAt : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z
  /-- The momentum equation holds on the open slab. -/
  momentum : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z
  /-- The energy-class bounds. -/
  energyClass : ClassicalEnergyClass u p T
  /-- The time-zero slice is the initial velocity. -/
  initial : ∀ x, u (timeSpaceCons 0 x) = nse.initialVelocity x
  /-- The velocity slices converge to the initial velocity in `L²`. -/
  trace : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - nse.initialVelocity) 2 volume)
    (𝓝[>] 0) (𝓝 0)

namespace ClassicalSolutionData

variable {nse : Problem n} {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}

/-- The classical solution as a pressure-retaining weak solution. -/
def toPressureWeakSolution (h : ClassicalSolutionData nse u p T) : PressureWeakSolution nse :=
  classicalPressureWeakSolution nse h.forcing_eq_zero u p T h.velocity_contDiffAt
    h.pressure_contDiffAt h.divergenceFreeAt h.momentum h.energyClass h.initial h.trace

/-- The time-zero velocity slice is the initial velocity. -/
theorem velocitySlice_zero (h : ClassicalSolutionData nse u p T) :
    velocitySlice u 0 = nse.initialVelocity :=
  funext h.initial

/-- The `L²` velocity slices of the classical weak solution are at distance
`‖u(s) - u(t)‖₂`. -/
theorem dist_velocityL2Slice (h : ClassicalSolutionData nse u p T) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) :
    dist (h.toPressureWeakSolution.toWeakSolution.velocityL2Slice s)
        (h.toPressureWeakSolution.toWeakSolution.velocityL2Slice t) =
      (eLpNorm (velocitySlice u s - velocitySlice u t) 2 volume).toReal :=
  dist_velocityL2SliceOn h.toPressureWeakSolution.toWeakSolution.velocity_memLp_at hs ht

/-- The `L²` velocity slices of the classical weak solution are continuous on `[0,T]`. -/
theorem continuousOn_velocityL2Slice (h : ClassicalSolutionData nse u p T) :
    ContinuousOn h.toPressureWeakSolution.toWeakSolution.velocityL2Slice (Set.Icc 0 T) := by
  have hT := h.energyClass.time_pos
  intro t ht
  rcases ht.1.eq_or_lt with h0 | h0
  · subst h0
    apply ContinuousWithinAt.mono _ Set.Icc_subset_Ici_self
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.trace
    rw [ENNReal.toReal_zero, ← h.velocitySlice_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hT] with s hs
    exact (h.dist_velocityL2Slice ⟨hs.1.le, hs.2⟩ ⟨le_rfl, hT.le⟩).symm
  · have hset : Set.Icc 0 T ∩ Set.Ioi 0 = Set.Ioc 0 T := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.le, h2⟩, h1⟩
    rw [← continuousWithinAt_inter (Ioi_mem_nhds h0), hset, ContinuousWithinAt,
      tendsto_iff_dist_tendsto_zero]
    have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (h.energyClass.tendsto_velocity t ⟨h0, ht.2⟩)
    rw [ENNReal.toReal_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (h.dist_velocityL2Slice ⟨hs.1.le, hs.2⟩ ht).symm

/-- The velocity of the classical weak solution is in `L∞(0,T; L²)`. -/
theorem velocity_memLp_top (h : ClassicalSolutionData nse u p T) :
    MemLp h.toPressureWeakSolution.toWeakSolution.velocityL2Slice ⊤
      (volume.restrict (Set.Icc 0 T)) := by
  obtain ⟨C, hC⟩ := h.energyClass.velocity_bounded
  refine memLp_top_of_bound ((h.continuousOn_velocityL2Slice).aestronglyMeasurable
    measurableSet_Icc) (max (max C 0)
      ‖h.toPressureWeakSolution.toWeakSolution.velocityL2Slice 0‖) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rcases ht.1.eq_or_lt with h0 | h0
  · subst h0
    exact le_max_right _ _
  · refine le_max_of_le_left ?_
    rw [show ‖h.toPressureWeakSolution.toWeakSolution.velocityL2Slice t‖ =
        (eLpNorm (velocitySlice u t) 2 volume).toReal from
      norm_velocityL2SliceOn h.toPressureWeakSolution.toWeakSolution.velocity_memLp_at ht]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC t ⟨h0, ht.2⟩)).trans
      (by rw [ENNReal.toReal_ofReal'])

/-- The slice gradient of the classical weak solution is in `L²(0,T; L²)`. -/
theorem gradient_memLp_two (h : ClassicalSolutionData nse u p T) :
    MemLp h.toPressureWeakSolution.toWeakSolution.gradientL2Slice 2
      (volume.restrict (Set.Icc 0 T)) := by
  have hcont : ContinuousOn (sliceGradient u) {z | 0 < z 0 ∧ z 0 < T} := fun z hz ↦
    (continuousAt_sliceGradient h.velocity_contDiffAt hz).continuousWithinAt
  exact PDE.Analysis.memLp_two_sliceCurve
    (D := sliceGradient u) h.toPressureWeakSolution.toWeakSolution.gradient_memLp_at hcont
    (h.energyClass.gradient_sq_integrableOn.const_mul n) fun t ht ↦ by
      have hle := toReal_eLpNorm_sliceGradient_le h.energyClass ht
      have h0 : 0 ≤ (eLpNorm (spatialGradientSlice (sliceGradient u) t) 2 volume).toReal :=
        ENNReal.toReal_nonneg
      calc (eLpNorm (fun x ↦ sliceGradient u (timeSpaceCons t x)) 2 volume).toReal ^ 2
          ≤ (√n * (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal) ^ 2 :=
            pow_le_pow_left₀ h0 hle 2
        _ = n * (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The initial `L²` class of the classical weak solution is the trace at time zero. -/
theorem velocityL2Slice_zero_eq_initial (h : ClassicalSolutionData nse u p T) :
    h.toPressureWeakSolution.toWeakSolution.velocityL2Slice 0 =
      h.toPressureWeakSolution.toWeakSolution.initialVelocityL2 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, h.energyClass.time_pos.le⟩
  exact velocityL2SliceOn_eq_toLp h.toPressureWeakSolution.toWeakSolution.velocity_memLp_at h0
    _ (Eventually.of_forall fun x ↦ h.initial x)

/-- Zero forcing does no work. -/
theorem forceWork_eq_zero (h : ClassicalSolutionData nse u p T) (t : ℝ) :
    forceWork nse u t = 0 := by
  simp [forceWork, forcePowerDensity, h.forcing_eq_zero]

/-- The force work of zero forcing is integrable. -/
theorem forceWorkTimeIntegrableOn (h : ClassicalSolutionData nse u p T) :
    ForceWorkTimeIntegrableOn nse u T := by
  have hz : (fun s ↦ ∫ x : ℝ^n, forcePowerDensity nse u s x) = 0 := by
    funext s
    simp [forcePowerDensity, h.forcing_eq_zero]
  unfold ForceWorkTimeIntegrableOn
  rw [hz]
  exact integrableOn_zero

/-- The hypotheses of `suitableLerayHopf_of_classical`, smoothness on the open slab, the
unforced equations, the energy class, the initial values and the `L²` trace, give the classical
solution data of the unforced problem. -/
theorem of_unforced {u₀ : ℝ^n → ℝ^n} (hu₀ : DistributionallyDivergenceFree u₀)
    (hreg : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ (⊤ : ℕ∞) u z ∧ ContDiffAt ℝ (⊤ : ℕ∞) p z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt (unforcedProblem u₀ hu₀) u p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hclass : ClassicalEnergyClass u p T) (hinit : ∀ x, u (timeSpaceCons 0 x) = u₀ x)
    (htrace : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - u₀) 2 volume) (𝓝[>] 0) (𝓝 0)) :
    ClassicalSolutionData (unforcedProblem u₀ hu₀) u p T where
  forcing_eq_zero := rfl
  velocity_contDiffAt := fun z hz ↦ (hreg z hz).1.of_le (WithTop.coe_le_coe.mpr le_top)
  pressure_contDiffAt := fun z hz ↦ (hreg z hz).2.of_le (WithTop.coe_le_coe.mpr le_top)
  divergenceFreeAt := hdiv
  momentum := hmom
  energyClass := hclass
  initial := hinit
  trace := htrace

end ClassicalSolutionData

namespace ClassicalSolutionData

variable {nse : Problem 3} {u : ℝ^(3 + 1) → ℝ^3} {p : ℝ^(3 + 1) → ℝ} {T : ℝ}

/-- The energy equality of a classical three-dimensional solution, measured from the initial
datum. -/
theorem kineticEnergy_add_dissipation_eq (h : ClassicalSolutionData nse u p T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    kineticEnergy u t + nse.kinematicViscosity *
        ∫ s in Set.Icc 0 t, weakGradientDissipation (sliceGradient u) s =
      initialKineticEnergy nse := by
  have hT := h.energyClass.time_pos
  set ws := h.toPressureWeakSolution.toWeakSolution
  have hDint : IntegrableOn (weakGradientDissipation (sliceGradient u)) (Set.Icc 0 T) :=
    ws.weakGradientDissipation_integrableOn_of_gradient_memLp h.gradient_memLp_two
  have hE : ∀ s ∈ Set.Icc 0 T, kineticEnergy u s = (1 / 2 : ℝ) * ‖ws.velocityL2Slice s‖ ^ 2 :=
    fun s hs ↦ ws.kineticEnergy_eq_velocityL2Slice_norm_sq hs
  have hEcont : ContinuousOn (kineticEnergy u) (Set.Icc 0 T) :=
    (continuousOn_const.mul (h.continuousOn_velocityL2Slice.norm.pow 2)).congr hE
  have hIcont : ContinuousOn (fun s ↦ ∫ τ in (0 : ℝ)..s, weakGradientDissipation
      (sliceGradient u) τ) (Set.Icc 0 T) := by
    have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := weakGradientDissipation (sliceGradient u)) (by rwa [Set.uIcc_of_le hT.le])
    rwa [Set.uIcc_of_le hT.le] at hc
  set H : ℝ → ℝ := fun s ↦ kineticEnergy u s + nse.kinematicViscosity *
    ∫ τ in (0 : ℝ)..s, weakGradientDissipation (sliceGradient u) τ
  have hHcont : ContinuousOn H (Set.Icc 0 T) := hEcont.add (continuousOn_const.mul hIcont)
  have hH0 : H 0 = initialKineticEnergy nse := by
    simp only [H, intervalIntegral.integral_same, mul_zero, add_zero]
    unfold kineticEnergy initialKineticEnergy
    congr 1
    funext x
    simp [kineticEnergyDensity, initialKineticEnergyDensity, h.initial,
      IncompressibleFlow.specificKineticEnergy]
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
      IntervalIntegrable (weakGradientDissipation (sliceGradient u)) volume a b := by
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hDint.mono_set (Set.Icc_subset_Icc ha hb)
  have hconst : ∀ s t, 0 < s → s ≤ t → t < T → H t = H s := by
    intro s t hs hst ht
    have heq := kineticEnergy_add_integral_weakGradientDissipation_eq h.forcing_eq_zero
      h.velocity_contDiffAt h.pressure_contDiffAt h.divergenceFreeAt h.momentum h.energyClass
      hs hst ht
    rw [← intervalIntegral.integral_interval_sub_left (hint 0 t le_rfl (hs.le.trans hst) ht.le)
      (hint 0 s le_rfl hs.le (hst.trans ht.le))] at heq
    simp only [H]
    linarith
  have hlim0 : Tendsto H (𝓝[>] 0) (𝓝 (H 0)) := by
    have hc := (hHcont 0 ⟨le_rfl, hT.le⟩).tendsto
    rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
    exact hc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
  have hIoo : ∀ t ∈ Set.Ioo 0 T, H t = H 0 := by
    intro t ht
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim0
    filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
    exact hconst s t hs.1 hs.2.le ht.2
  have hall : H t = H 0 := by
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0]
    rcases ht.2.lt_or_eq with h1 | h1
    · exact hIoo t ⟨h0, h1⟩
    have hc : Tendsto H (𝓝[<] T) (𝓝 (H T)) := by
      have hc' := (hHcont T ⟨hT.le, le_rfl⟩).tendsto
      rw [← nhdsWithin_Ioo_eq_nhdsLT hT]
      exact hc'.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hc2 : Tendsto H (𝓝[<] T) (𝓝 (H 0)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hT] with s hs
      exact (hIoo s hs).symm
    rw [h1]
    exact tendsto_nhds_unique hc hc2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1, ← hH0, ← hall]

/-- The classical solution as a pressure-retaining Leray–Hopf solution. -/
def toPressureRepresentativeLerayHopfSolution (h : ClassicalSolutionData nse u p T) :
    PressureRepresentativeLerayHopfSolution nse where
  toPressureWeakSolution := h.toPressureWeakSolution
  velocity_memLp_top := h.velocity_memLp_top
  gradient_memLp_two := h.gradient_memLp_two
  velocityWeakL2Slice_continuousOn :=
    (toWeakSpaceCLM ℝ _).continuous.comp_continuousOn h.continuousOn_velocityL2Slice
  velocityL2Slice_zero_eq_initial := h.velocityL2Slice_zero_eq_initial
  forceWorkTimeIntegrableOn := h.forceWorkTimeIntegrableOn
  energy_inequality := fun {t} ht ↦ by
    change kineticEnergy u t + nse.kinematicViscosity *
        ∫ s in Set.Icc 0 t, weakGradientDissipation (sliceGradient u) s ≤
      initialKineticEnergy nse + forceWork nse u t
    rw [h.forceWork_eq_zero, add_zero]
    exact (h.kineticEnergy_add_dissipation_eq ht).le

/-- The classical solution as a suitable Leray–Hopf solution, with the slice gradient as weak
gradient. -/
def toSuitableLerayHopfSolution (h : ClassicalSolutionData nse u p T) :
    SuitableLerayHopfSolution nse :=
  h.toPressureRepresentativeLerayHopfSolution.toSuitableOfPositiveTimeRegular
    h.forcing_eq_zero h.velocity_contDiffAt h.pressure_contDiffAt h.divergenceFreeAt h.momentum
    (Eventually.of_forall fun z hz ↦ (sliceGradient_eq_spatialVelocityGradient hz.1
      ((h.velocity_contDiffAt z hz).differentiableAt (by norm_num))).symm)

/-- The velocity of the suitable solution is the classical velocity. -/
@[simp]
theorem toSuitableLerayHopfSolution_u (h : ClassicalSolutionData nse u p T) :
    h.toSuitableLerayHopfSolution.u = u :=
  rfl

/-- The pressure of the suitable solution is the classical pressure. -/
@[simp]
theorem toSuitableLerayHopfSolution_p (h : ClassicalSolutionData nse u p T) :
    h.toSuitableLerayHopfSolution.p = p :=
  rfl

/-- The horizon of the suitable solution is `T`. -/
@[simp]
theorem toSuitableLerayHopfSolution_T (h : ClassicalSolutionData nse u p T) :
    (h.toSuitableLerayHopfSolution.T : ℝ) = T :=
  rfl

/-- The weak gradient of the suitable solution is the slice gradient. -/
@[simp]
theorem toSuitableLerayHopfSolution_Du (h : ClassicalSolutionData nse u p T) :
    h.toSuitableLerayHopfSolution.Du = sliceGradient u :=
  rfl

end ClassicalSolutionData

/-- A velocity and pressure smooth on the open slab `(0,T) × ℝ^3` that solve the unforced
Navier–Stokes equations there, lie in the energy class and take the `L²` initial trace `u₀`
form a suitable Leray–Hopf solution of the unforced problem with datum `u₀`. The witness is
`ClassicalSolutionData.toSuitableLerayHopfSolution` of `ClassicalSolutionData.of_unforced`; its
weak gradient is the slice gradient, and the energy inequality holds with equality.

Smoothness is `ContDiffAt ℝ (⊤ : ℕ∞)`, infinite differentiability, as in
`NonuniquenessConclusion`; the top element of `WithTop ℕ∞` would mean analyticity. Only two
derivatives of the velocity and one of the pressure are used. -/
theorem suitableLerayHopf_of_classical {u₀ : ℝ^3 → ℝ^3}
    (hu₀ : DistributionallyDivergenceFree u₀) (u : ℝ^(3 + 1) → ℝ^3) (p : ℝ^(3 + 1) → ℝ) (T : ℝ)
    (hreg : ∀ z ∈ finiteTimeDomain 3 T, ContDiffAt ℝ (⊤ : ℕ∞) u z ∧ ContDiffAt ℝ (⊤ : ℕ∞) p z)
    (hmom : ∀ z ∈ finiteTimeDomain 3 T, MomentumEquationAt (unforcedProblem u₀ hu₀) u p z)
    (hdiv : ∀ z ∈ finiteTimeDomain 3 T, DivergenceFreeAt u z)
    (hclass : ClassicalEnergyClass u p T) (hinit : ∀ x, u (timeSpaceCons 0 x) = u₀ x)
    (htrace : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - u₀) 2 volume) (𝓝[>] 0) (𝓝 0)) :
    ∃ sol : SuitableLerayHopfSolution (unforcedProblem u₀ hu₀),
      sol.u = u ∧ sol.p = p ∧ (sol.T : ℝ) = T :=
  ⟨(ClassicalSolutionData.of_unforced hu₀ hreg hmom hdiv hclass hinit
    htrace).toSuitableLerayHopfSolution, rfl, rfl, rfl⟩

end NavierStokes

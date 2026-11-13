/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletSeries
public import PDE.Parabolic.Heat.Spectral.DirichletTime

/-!
# Strong initial attainment for the classical Dirichlet heat series

At positive time the classical eigenfunction sum represents the Hilbert heat
evolution. At time zero we use the chosen representative of the initial `L²` class.
The resulting trajectory is continuous in `L²`, with its prescribed strong initial
trace.
-/

@[expose] public section

noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace HolderSpace MeasureTheory Set Filter
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- The positive-time classical sum belongs to the initial pivot space. -/
theorem memLp_classicalPower (m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    MemLp (S.classicalPower hopen hbounded hgraph hγ m f t) 2 (domainMeasure n Ω) :=
  (Lp.memLp (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg m f t)).ae_eq
    (S.classicalPower_ae hopen hbounded hgraph hγ m f ht).symm

/-- The closed-time heat representative uses the prescribed `L²` representative at
zero, and the classical eigenfunction sum at positive times. Negative times are
assigned the initial representative as an auxiliary extension. -/
def dirichletHeat (f : DerivLp n 2 Ω) (t : ℝ) : ℝ^n → ℝ :=
  if 0 < t then S.classicalPower hopen hbounded hgraph hγ 0 f t else f

/-- The closed-time representative agrees with the classical series at positive time. -/
theorem dirichletHeat_of_pos (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    S.dirichletHeat hopen hbounded hgraph hγ f t =
      S.classicalPower hopen hbounded hgraph hγ 0 f t := ite_eq_left ht

/-- The assigned time-zero function is the chosen representative of the initial class. -/
@[simp] theorem dirichletHeat_zero (f : DerivLp n 2 Ω) :
    S.dirichletHeat hopen hbounded hgraph hγ f 0 = f := ite_eq_right (lt_irrefl 0)

/-- Every time slice of the closed-time representative is square integrable. -/
theorem memLp_dirichletHeat (f : DerivLp n 2 Ω) (t : ℝ) :
    MemLp (S.dirichletHeat hopen hbounded hgraph hγ f t) 2 (domainMeasure n Ω) := by
  unfold dirichletHeat
  split_ifs with ht
  · exact S.memLp_classicalPower hopen hbounded hgraph hγ 0 f ht
  · exact Lp.memLp f

/-- The pivot-space trajectory of the constructed classical representative. -/
def dirichletHeatL2 (f : DerivLp n 2 Ω) (t : ℝ) : DerivLp n 2 Ω :=
  (S.memLp_dirichletHeat hopen hbounded hgraph hγ f t).toLp
    (S.dirichletHeat hopen hbounded hgraph hγ f t)

/-- The classical trajectory is exactly the spectral Hilbert evolution in `L²`. -/
theorem dirichletHeatL2_eq_spectralHeatEvolution (f : DerivLp n 2 Ω) (t : ℝ) :
    S.dirichletHeatL2 hopen hbounded hgraph hγ f t =
      spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg f t.toNNReal := by
  apply Lp.ext
  apply (S.memLp_dirichletHeat hopen hbounded hgraph hγ f t).coeFn_toLp.trans
  by_cases ht : 0 < t
  · rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht]
    have h := S.classicalPower_ae hopen hbounded hgraph hγ 0 f ht
    rw [spectralHeatPower_zero_order S.basis S.eigenvalue S.eigenvalue_nonneg f ht] at h
    have heq : t.toNNReal = ⟨t, ht.le⟩ := NNReal.eq (Real.coe_toNNReal t ht.le)
    simpa only [heq] using h
  · rw [dirichletHeat, ite_eq_right ht, Real.toNNReal_of_nonpos (le_of_not_gt ht),
      spectralHeatEvolution_zero]

/-- The classical trajectory is strongly continuous through the prescribed initial class. -/
theorem continuous_dirichletHeatL2 (f : DerivLp n 2 Ω) :
    Continuous (S.dirichletHeatL2 hopen hbounded hgraph hγ f) := by
  have heq : S.dirichletHeatL2 hopen hbounded hgraph hγ f =
      fun t ↦ spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg f t.toNNReal :=
    funext (S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ f)
  rw [heq]
  exact (continuous_spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg f).comp
    continuous_real_toNNReal

/-- The initial data are attained strongly in `L²` as positive time tends to zero. -/
theorem tendsto_dirichletHeatL2_zero (f : DerivLp n 2 Ω) :
    Tendsto (S.dirichletHeatL2 hopen hbounded hgraph hγ f) (𝓝[>] 0) (𝓝 f) := by
  have hz : S.dirichletHeatL2 hopen hbounded hgraph hγ f 0 = f := by
    rw [S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ,
      Real.toNNReal_zero, spectralHeatEvolution_zero]
  exact ((S.continuous_dirichletHeatL2 hopen hbounded hgraph hγ f).tendsto' 0 f hz).mono_left
    nhdsWithin_le_nhds

/-- The closed-time representative satisfies the heat equation at every positive time
and interior point, with its scalar time derivative. -/
theorem hasDerivAt_dirichletHeat_laplacian (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : x ∈ Ω) :
    HasDerivAt (fun s ↦ S.dirichletHeat hopen hbounded hgraph hγ f s x)
      (PDE.laplacian (S.dirichletHeat hopen hbounded hgraph hγ f t) x) t := by
  rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f ht]
  apply (S.hasDerivAt_classicalPower_laplacian hopen hbounded hgraph hγ
    0 f ht hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  rw [S.dirichletHeat_of_pos hopen hbounded hgraph hγ f hs]

end HeatEquation.DirichletHeatSpectrum

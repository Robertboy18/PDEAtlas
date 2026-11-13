/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.Smoothing
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Core.Uniqueness
import PDE.Analysis.Evolution.Gelfand.Uniqueness
import PDE.Analysis.Evolution.LionsMagenes.Regularity.CrossEnergy
import PDE.Analysis.Evolution.Hilbert.Riesz
import PDE.Analysis.Evolution.Gelfand.Energy

/-!
# Weak evolution foundations

The smooth Hilbert-space equation, its energy law, and the Gelfand-triple
formulation used for time regularity and Galerkin approximation.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Weak Evolution Foundations" =>

# Smooth weak evolution and its energy law

:::definition "parabolic.smooth_weak_evolution" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.SatisfiesWeakEvolutionAt, PDE.Analysis.Evolution.SatisfiesWeakEvolutionOn")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "373-377"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

In a real Hilbert energy space $`V`, the pointwise predicate takes a state
$`u(t)\in V` and a supplied vector $`d(t)\in V` and records

$$`(d(t),v)_V+B(t)(u(t),v)=\ell(t)(v)\qquad(v\in V).`

The interval predicate imposes this identity at every time in a chosen set.
The energy and uniqueness theorems separately assume that $`d(t)` is the
strong time derivative of $`u`. This is the Hilbert-space precursor of the
Gelfand-triple and integrated formulations, in which the derivative $`u'(t)`
lies in $`V^*`.
:::

The identity in this definition holds for every test vector, and its first
consequence comes from the single choice $`v=u(t)`.

:::theorem "parabolic.smooth_weak_energy" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.weakEvolution_energy_identity, PDE.Analysis.Evolution.weakEvolution_coercive_energy_inequality, PDE.Analysis.Evolution.weakEvolution_energy_bound") (uses := "parabolic.smooth_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "376-378"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a differentiable trajectory satisfying the smooth weak equation, testing
by $`u(t)` gives

$$`\frac{d}{dt}\frac12\lVert u(t)\rVert_V^2
  =\ell(t)(u(t))-B(t)(u(t),u(t)).`

Under $`B(t)(u(t),u(t))\ge C\lVert u(t)\rVert_V^2` with $`C>0`, duality and
Young's inequality give the coercive differential inequality.

On $`[a,b]` with $`a\le b`, assume the equation and coercivity hold at every
time and the specified derivative exists within the interval at every time.
If $`\lVert\ell(t)\rVert_{V^*}\le M` throughout $`[a,b]`, with $`M\ge0`, then

$$`\frac12\lVert u(t)\rVert_V^2\le
\frac12\lVert u(a)\rVert_V^2+\frac{M^2}{2C}(t-a)
\qquad(t\in[a,b]).`

The same calculation reappears in the pivot norm for Galerkin trajectories.
The finite-interval bound controls the energy at each time and carries no
integrated coercive term.
:::

:::proof "parabolic.smooth_weak_energy"
Set the test vector equal to $`u(t)`. The Hilbert-space chain rule identifies
$`(u'(t),u(t))_V` with
$`\frac12\frac d{dt}\|u(t)\|_V^2`, giving the exact identity. Coercivity
bounds the form term below, while duality and Young's inequality bound
$`\ell(t)(u(t))` by a multiple of $`\|\ell(t)\|_{V^*}^2` plus half the
coercive energy. The uniform forcing bound gives
$`E'(t)\le M^2/(2C)` for $`E(t)=\tfrac12\lVert u(t)\rVert_V^2`. The
mean-value inequality then gives the finite-interval estimate.
:::

Applied to the difference of two solutions with the same forcing, the same
calculation needs less than coercivity. The forcing cancels, so nonnegativity
$`B(t)(w,w)\ge0` already makes the energy of the difference nonincreasing,
and that monotonicity is the whole uniqueness argument.

:::theorem "parabolic.smooth_weak_uniqueness" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.weakEvolution_unique, PDE.Analysis.Evolution.weakEvolution_zero_of_initial") (uses := "parabolic.smooth_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`V` be a real inner product space, let $`a\le b`, and let
$`B(t):V\to V^*` be bounded bilinear forms with

$$`B(t)(w,w)\ge0\qquad(w\in V,\ t\in[a,b]).`

Suppose $`u,v:\mathbb R\to V` are differentiable within $`[a,b]` at every
$`t\in[a,b]`, with derivatives $`u'(t)` and $`v'(t)`, and that both satisfy
the smooth weak equation with the same forcing $`\ell(t)\in V^*`:

$$`
(u'(t),w)_V+B(t)(u(t),w)=\ell(t)(w)
\qquad(w\in V,\ t\in[a,b]).
`

If $`u(a)=v(a)`, then $`u(t)=v(t)` for every $`t\in[a,b]`. A
time-independent form is the case $`B(t)=B`. The homogeneous kernel
statement says that a solution with
$`\ell=0` and $`u(a)=0` vanishes on $`[a,b]`; it needs nonnegativity only
along the trajectory.

This is Evans's uniqueness argument for weak solutions, for the smooth
Hilbert-space model with a strong time derivative. The case with a lower-order
term controlled by a Gårding inequality is the
{bpref "parabolic.integrated_garding_uniqueness"}[integrated Gårding-uniqueness theorem].
:::

:::proof "parabolic.smooth_weak_uniqueness" (uses := "parabolic.smooth_weak_energy")
The difference $`w=u-v` satisfies the homogeneous equation with derivative
$`u'-v'` and $`w(a)=0`. Testing it with $`w(t)` gives
$`(w'(t),w(t))_V=-B(t)(w(t),w(t))\le0`, so the energy
$`E(t)=\tfrac12\lVert w(t)\rVert_V^2`, whose one-sided derivative within
$`[a,b]` is exactly $`(w'(t),w(t))_V`, is nonincreasing on the interval.
Since $`E(a)=0` and $`E\ge0`, the energy vanishes identically and so does
$`w`.
:::

Neither the energy law nor uniqueness uses completeness of $`V`; existence
does. On a complete space, Riesz representation turns the functional
$`\ell(t)` and the partial form $`B(u(t),\cdot)` into vectors of $`V`, and
the weak equation, so far a family of scalar identities indexed by $`v`,
collapses to a single vector-valued ordinary differential equation.

:::theorem "parabolic.hilbert_riesz_ode" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.satisfiesWeakEvolutionAt_iff_ode, InnerProductSpace.toDual, InnerProductSpace.continuousLinearMapOfBilin") (uses := "parabolic.smooth_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a complete real Hilbert space, Riesz representation converts the smooth
weak equation into the ordinary differential equation

$$`u'(t)=R\ell(t)-A_Bu(t),`

where $`R\ell` is the Riesz vector of the functional and $`A_B` is the
bounded operator represented by the bilinear form. This is the Riesz step of
the Galerkin argument (Evans §7.1.2); the theorem is valid on any complete
Hilbert space.
:::

:::proof "parabolic.hilbert_riesz_ode"
Riesz representation gives vectors $`R\ell(t)` and $`A_Bu(t)` satisfying
$`(R\ell(t),v)_V=\ell(t)(v)` and
$`(A_Bu(t),v)_V=B(t)(u(t),v)` for every $`v`. Substituting these into the
weak equation shows that
$`(u'(t)-R\ell(t)+A_Bu(t),v)_V=0` for all $`v`. Nondegeneracy of the inner
product gives the vector ODE, and pairing that ODE with arbitrary $`v` gives
the converse.
:::

For a time-independent form the equation $`u'=R\ell(t)-A_Bu` is affine
linear with a bounded constant operator, so variation of constants solves it
in closed form on the whole line, with no Lipschitz ball or short-time
restriction. The Riesz equivalence then carries the classical solution back
to a pointwise weak evolution.

:::theorem "parabolic.hilbert_affine_evolution" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.exists_weakEvolution_global, PDE.Analysis.Evolution.affineLinearEvolutionSolution, PDE.Analysis.Evolution.hasDerivAt_affineLinearEvolutionSolution, PDE.Analysis.Evolution.exists_weakEvolutionOn_Icc") (uses := "parabolic.hilbert_riesz_ode")
For a time-independent bounded form and continuous dual forcing, the
variation-of-constants formula produces a global classical solution of the
Riesz-reduced affine equation

$$`
  u'(t)=R\ell(t)-A_Bu(t),\qquad u(t_0)=u_0,
`

namely

$$`
  u(t)=e^{-(t-t_0)A_B}
  \left(u_0+\int_{t_0}^t e^{(s-t_0)A_B}R\ell(s)\,ds\right).
`

A closed-interval theorem gives the same trajectory with its pointwise
weak equation.
:::

:::proof "parabolic.hilbert_affine_evolution"
Differentiate the variation-of-constants formula. The derivative of the
operator exponential contributes $`-A_Bu(t)`, while the Banach-valued
fundamental theorem of calculus contributes the endpoint value
$`R\ell(t)`. At $`t=t_0`, the exponential is the identity and the integral
vanishes, so the initial value is $`u_0`. The Riesz equivalence then converts
the affine ODE back into the pointwise weak equation on the chosen interval.
:::

# The Gelfand-triple equation

:::definition "parabolic.gelfand_triple" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.GelfandTriple, PDE.Analysis.Evolution.GelfandTriple.pivotToDual, PDE.Analysis.Evolution.GelfandTriple.energyToDual")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "299-304"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "373-375"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%

A Gelfand triple begins with a continuous injective map $`J:V\to H` having
dense range.  The pivot inner product then defines the canonical maps

$$`H\longrightarrow V^*,\qquad h\longmapsto \bigl(v\mapsto (h,Jv)_H\bigr),`

and $`V\to V^*` by composition with $`J`.  The Lean structure stores exactly
the embedding data.  Completeness and reflexivity are hypotheses of the
theorems that need them. The concrete Sobolev triple
$`H_0^1\hookrightarrow L^2\hookrightarrow H^{-1}` is an instance.
:::

The pivot pairing $`(Ju(t),Jv)_H` supplied by the triple is what makes a
time derivative meaningful for a trajectory that is only a Bochner class in
$`L^2(a,b;V)`. The derivative is characterized by integrating this pairing
against scalar test functions, and its values are allowed to lie in $`V^*`
rather than in $`V` or $`H`.

:::definition "parabolic.gelfand_weak_time_derivative" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn, PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn.congr_ae_iff") (uses := "parabolic.gelfand_triple")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "299-304"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "374-379"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%

For Bochner classes $`u\in L^2(a,b;V)` and
$`g\in L^2(a,b;V^*)`, the statement that $`g=u_t` is encoded by

$$`\int_a^b g(t)[v]\,\tau(t)\,dt
  =-\int_a^b (Ju(t),Jv)_H\,\tau'(t)\,dt`

for every $`v\in V` and every admissible endpoint-vanishing time test
$`\tau`.  Both sides are unchanged when either Bochner representative is
modified on a null set. The definition involves no pointwise time
derivative or endpoint trace; continuous representatives and endpoint traces
come from the Lions–Magenes theorem.
:::

As written, the definition is a relation between $`u` and a candidate $`g`,
so one must check that a trajectory cannot have two different derivatives.

:::theorem "parabolic.gelfand_weak_time_derivative_uniqueness" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn.hasWeakTimeDerivativeOn, PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn.eq") (uses := "parabolic.gelfand_weak_time_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "299-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

The Gelfand test identity induces the ordinary local Banach-valued weak
derivative relation for the $`V^*`-valued trajectory $`J^*Ju`.  Completeness
of $`V` and separation by continuous linear functionals then imply that two
$`L^2(a,b;V^*)` weak derivatives of the same trajectory are equal as
Bochner classes.  Thus the derivative appearing in the weak evolution
equation is determined by the trajectory.
:::

:::proof "parabolic.gelfand_weak_time_derivative_uniqueness"
The scalar test identity for each $`v\in V` is exactly the distributional
derivative relation for the $`V^*`-valued trajectory $`J^*Ju`. If $`g_1`
and $`g_2` both satisfy it, their difference pairs to zero against every
spatial test vector and every compactly supported time test. Uniqueness of
Banach-valued weak derivatives gives $`g_1=g_2` almost everywhere, hence the
same Bochner $`L^2(V^*)` class.
:::

With the derivative intrinsic, the evolution equation itself can be posed in
the triple. Two levels must be kept apart: a pointwise identity, imposed at
every time of a set for a trajectory $`u:\mathbb R\to V` with a supplied dual
vector $`d(t)\in V^*`, and the integrated identity for Bochner classes. The
smooth energy and uniqueness arguments run on the pointwise form.

:::definition "parabolic.gelfand_weak_evolution" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.SatisfiesGelfandWeakEvolutionOn, PDE.Analysis.Evolution.RepresentsPivotDerivative") (uses := "parabolic.gelfand_triple")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "373-375"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For $`B(t):V\to V^*`, forcing $`\ell(t)\in V^*`, trajectory $`u(t)\in V`, and
supplied dual vector $`d(t)\in V^*`, the pointwise weak equation is

$$`\langle d(t),v\rangle+\langle B(t)u(t),v\rangle
  =\langle \ell(t),v\rangle\qquad(v\in V).`

For a supplied pivot-space vector $`d_H(t)`, the
separate predicate the pivot derivative condition records
$`d(t)=J^*d_H(t)`. Identifying $`d_H(t)` with the actual derivative of $`Ju`
is a separate hypothesis of the smooth energy and uniqueness theorems.
:::

Testing the pointwise equation with $`v=u(t)` produces the pairing
$`\langle d(t),u(t)\rangle`, which the chain rule identifies with the
derivative of $`\tfrac12\lVert Ju(t)\rVert_H^2` when $`d(t)` is represented
by the derivative of $`Ju`. The differentiated quantity uses the pivot norm
while coercivity acts on the energy norm.

:::theorem "parabolic.gelfand_smooth_energy_bound" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.gelfandWeakEvolution_energy_bound") (uses := "parabolic.gelfand_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "376-377"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a\le b` and let $`u` satisfy the pointwise weak equation on $`[a,b]`.
Suppose $`Ju` is differentiable within the interval at every time, with
derivative $`d_H(t)` representing the supplied dual vector $`d(t)`.
Assume throughout $`[a,b]` that
$`B(t)(u(t),u(t))\ge C\lVert u(t)\rVert_V^2` with $`C>0`, and
$`\lVert\ell(t)\rVert_{V^*}\le M` with $`M\ge0`. Then

$$`\frac12\lVert Ju(t)\rVert_H^2\le
\frac12\lVert Ju(a)\rVert_H^2+
\frac{M^2}{2C}(t-a)\qquad(t\in[a,b]).`

The integrated $`L^2(a,b;V)` estimate is a separate conclusion, proved for
Galerkin approximations and for integrated weak solutions.
:::

:::proof "parabolic.gelfand_smooth_energy_bound" (uses := "parabolic.gelfand_weak_evolution")
Test the weak equation with the solution, identify the derivative term with
one half of the derivative of $`\lVert Ju\rVert_H^2`, use coercivity on the
form term, and absorb the forcing by Young's inequality. The uniform forcing
bound and the mean-value inequality give the stated estimate.
:::

For the difference of two such evolutions the forcing cancels, so the pivot
energy identity gives uniqueness under nonnegativity of the form alone,
exactly as in the Hilbert case. Injectivity of $`J` converts the vanishing
of $`\lVert J(u-v)\rVert_H` into equality in $`V`.

:::theorem "parabolic.gelfand_smooth_uniqueness" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.gelfandWeakEvolution_unique") (uses := "parabolic.gelfand_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a\le b`. Suppose two pointwise weak evolutions have the same forcing
and initial datum, their included trajectories are differentiable at every
time of $`[a,b]`, and those derivatives represent the supplied dual vectors.
If $`B(t)(z,z)\ge0` for every $`z\in V` and $`t\in[a,b]`, the trajectories
agree throughout the interval.
:::

:::proof "parabolic.gelfand_smooth_uniqueness" (uses := "parabolic.gelfand_weak_evolution")
Subtract the equations, apply the pivot energy identity to the difference,
and use injectivity of the dense inclusion after its pivot norm is forced to
vanish.
:::

/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.FiniteTime

/-!
# Parabolic theory scope

Coverage of the classical, weak, regularity, and finite-time parabolic theory.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Classical and Weak Heat Flow" =>

# Whole-space formulas

The Gaussian kernel is treated in every dimension. Its convolution with bounded
continuous data solves the heat equation at positive time and attains the datum
locally uniformly, and Duhamel's formula solves the forced problem for globally
$`C^2`, compactly supported sources. The weak maximum and comparison principles
hold for classical solutions on compact parabolic cylinders. The strong maximum
principle and the Harnack inequality of Evans §7.1.4 hold for uniformly
elliptic nondivergence operators with continuous coefficients ({bpref "parabolic.strong_maximum_principle"}[] and
{bpref "parabolic.harnack"}[]). For measure data, the porous-medium
{bpref "methods.similarity.barenblatt"}[Barenblatt profile] has prescribed
positive mass and a Dirac initial trace.

# Variational evolution

Galerkin existence, the Lions–Magenes representative, the energy estimate, and
uniqueness hold for the Dirichlet heat equation on any bounded open set
({bpref "parabolic.dirichlet_existence_energy"}[]); boundary smoothness enters
only when elliptic regularity is applied to almost every spatial slice. For
time-dependent divergence-form operators with a uniformly elliptic principal
part and bounded lower-order terms, the same conclusions hold after a Gårding
shift, provided the form $`B(t):V\to V^*` is almost everywhere strongly
measurable and uniformly bounded in operator norm
({bpref "parabolic.divergence_existence_energy"}[]). On $`L^2(\Omega)` for any
open set $`\Omega`, the Dirichlet heat semigroup is constructed by
Hille–Yosida ({bpref "parabolic.dirichlet_semigroup"}[]).

# Nonlinear diffusion and reaction

Convex gradient diffusion ({bpref "parabolic.gradient_diffusion"}[]) has a
global weak Dirichlet solution from $`H^2\cap H^1_0` data on bounded $`C^2`
graph domains, for $`C^2` uniformly convex densities with bounded Hessian.
Turing instability ({bpref "parabolic.turing_instability"}[]) is proved for
the linear two-species system from the raw coefficient inequalities. For a
convex reaction dominating a superlinear power, the weak nonlinear heat
equation on a bounded connected domain has no nonnegative solution up to a
prescribed time once the initial eigenfunction moment exceeds an explicit
sufficient threshold ({bpref "parabolic.nonlinear_heat_large_data"}[]).

# Improved regularity

The $`H^2` theorems take an autonomous symmetric, uniformly elliptic principal
part without lower-order terms, with $`W^{1,\infty}(\Omega)` coefficients
admitting global $`C^1` representatives, on a domain $`\Omega\subseteq\mathbb R^n`,
$`n>0`, carrying a twice differentiable boundary atlas. Data $`f\in L^2_tL^2_x` and
$`u_0\in H^1_{0,x}` give $`u\in L^\infty_tH^1_{0,x}\cap L^2_tH^2_x` and
$`u_t\in L^2_tL^2_x` ({bpref "parabolic.autonomous_h2_bootstrap"}[]). Forcing in
$`H^1_tL^2_x` and compatible initial data in $`H^2_x\cap H^1_{0,x}` give the
principal-part case of Evans's Section 7.1.3, Theorem 5(ii), with data-only
bounds ({bpref "parabolic.improved_spatial_regularity"}[]). Regularity of every
order and a unique classical solution smooth up to the boundary, Theorems 6
and 7, hold for smooth time-independent coefficients, lower-order terms
included, on bounded domains whose boundary is $`C^r` for every $`r`
({bpref "parabolic.all_order_regularity"}[] and
{bpref "parabolic.smooth_classical_solution"}[]). The open directions closest
to these results are general measure-valued initial data, nonhomogeneous and
mixed boundary conditions, and $`H^2` estimates for time-dependent
coefficients.

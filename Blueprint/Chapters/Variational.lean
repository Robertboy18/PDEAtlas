/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Variational.FixedPoint
import Blueprint.Chapters.Variational.SecondVariation
import Blueprint.Chapters.Variational.Constraints

/-!
# Representation formulas, variational principles, and fixed points

Explicit representations, asymptotic and spectral methods, direct
minimization, first and second variations, semilinear energies, and
fixed-point arguments.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Representation Formulas, Variational Principles, and Fixed Points" =>
%%%
htmlSplit := .never
shortTitle := "Variational Methods"
%%%

To find a harmonic function with prescribed boundary values, Dirichlet's
principle suggests minimizing its gradient energy. We can choose admissible
functions with energies approaching the infimum, but we still need a limiting
function that attains it. Compactness supplies a candidate; closedness keeps
its boundary constraint; lower semicontinuity compares its energy with the
energies of the approximating functions.

This argument applies beyond harmonic functions. The
{bpref "methods.direct_method.coercive"}[direct-method existence theorem]
produces a minimizer for every coercive weakly lower semicontinuous
functional on a Hilbert space: coercivity keeps a minimizing sequence
bounded, reflexivity extracts a weak limit, and lower semicontinuity compares
the energy of the limit with the limiting energies. Alongside it, the
{bpref "methods.euler_lagrange.fundamental_lemma"}[fundamental lemma of the calculus of variations]
turns a vanishing first variation into an equation that holds almost everywhere.

Evans's second edition
{Informal.citet "evans-2010"}[] is the main reference:
Chapter 4 for separation, transforms, similarity, and asymptotics, Chapter 8
for minimization and first and second variations, and Chapter 9 for nonlinear
functional methods. Morrey's *Multiple Integrals in the Calculus of
Variations* and Brezis's functional-analysis treatment supply broader context
for integral functionals, weak compactness, and monotone operators.

# Poisson's energy

Variational methods begin from the observation that some weak equations are
stationarity conditions for an energy. For Poisson's equation with
homogeneous Dirichlet data, the energy is

$$`
J(v)=\frac12\int_\Omega|\nabla v|^2\,dx-\int_\Omega fv\,dx.
`

For $`f\in L^2(\Omega)`, take $`u,\varphi\in H^1_0(\Omega)`, so that
perturbing $`u` by $`\varepsilon\varphi` preserves the boundary condition.
Expanding the square gives the exact identity

$$`
J(u+\varepsilon\varphi)
=J(u)+\varepsilon\left(
\int_\Omega\nabla u\cdot\nabla\varphi-\int_\Omega f\varphi\right)
+\frac{\varepsilon^2}{2}\int_\Omega|\nabla\varphi|^2.
`

At a minimum, the coefficient of $`\varepsilon` must vanish: otherwise
choosing the opposite sign of a sufficiently small $`\varepsilon` lowers
the energy. That coefficient is the first variation,

$$`
DJ(u)[\varphi]
=\int_\Omega\nabla u\mathbin{\cdot}\nabla\varphi\,dx
-\int_\Omega f\varphi\,dx.
`

Thus a minimizer is a weak solution, once differentiability along admissible
directions has been proved. Existence of that minimizer is the separate
question that the direct method answers. The second variation then asks what
kind of critical point has been found; for a quadratic energy built from a
symmetric bilinear form the Hessian is that form, so coercivity controls
existence, uniqueness, and stability at once.

## Worked example: a Poisson minimizer on an interval

Take $`\Omega=(0,1)`, $`f=1`, and zero boundary values. The candidate

$$`u(x)=\frac{x(1-x)}2`

satisfies $`u(0)=u(1)=0` and $`-u''=1`. We can check minimization directly,
without guessing the sign of its energy. For a smooth perturbation $`w`
with $`w(0)=w(1)=0`, expand the square:

$$`
J(u+w)-J(u)=\int_0^1u'w'\,dx-\int_0^1w\,dx
+\frac12\int_0^1|w'|^2\,dx.
`

Integration by parts gives $`\int_0^1u'w'=\int_0^1w`: the boundary
term vanishes and $`u''=-1`. Consequently,

$$`J(u+w)-J(u)=\frac12\int_0^1|w'|^2\,dx\geq0.`

The energy gap is half the squared $`L^2` norm of the gradient error. If it is zero, $`w` is
constant, and its boundary values force $`w=0`. This calculation shows why
the weak equation and the boundary condition together yield both minimization
and uniqueness. The Sobolev theorems below make the same argument without
assuming smoothness and prove existence when no explicit candidate is known.

The fluid chapter supplies a useful warning about which energy is being
minimized. Its {bpref "fluid.euler.rotation_zero_strain"}[rigid rotation]
has a nonzero velocity gradient but zero symmetric gradient. The
{bpref "symbolic.rigid_rotation_energy"}[checked energy calculation] therefore
gives zero strain energy for that field on every integration domain. This
is a different functional from the scalar Dirichlet energy $`J`: it does
not detect rigid rotations. A coercivity argument must account for such
undetected motions through the admissible class or constraints. Computing an
integrand exactly helps identify that issue; compactness and coercivity remain
analytic questions.

Fixed-point arguments offer another way to construct a solution. Suppose the
linear part of a semilinear equation has solution operator $`S` and the
nonlinearity is $`N`. The equation can often be rewritten as

$$`
u=T(u),\qquad T(u)=S(f-N(u)).
`

If $`T` preserves a nonempty complete metric space and is a contraction there
with constant $`q<1`, the theorem of
{Informal.citet "banach-1922"}[] gives a unique fixed point. This approach
does not require the nonlinearity to be the derivative of a potential and can
handle non-self-adjoint linear terms. Its price is quantitative: the Lipschitz
constant of the nonlinearity must be small compared with the coercivity of the
linear inverse.

# Representing Solutions

{include 2 Blueprint.Chapters.Variational.Representations}

# Minimization and Variations

{include 2 Blueprint.Chapters.Variational.DirectMethod}
{include 2 Blueprint.Chapters.Variational.SecondVariation}
{include 2 Blueprint.Chapters.Variational.Constraints}

# Semilinear Existence and Stability

{include 2 Blueprint.Chapters.Variational.Semilinear}

# Fixed Points and Convex Regularization

{include 2 Blueprint.Chapters.Variational.FixedPoint}

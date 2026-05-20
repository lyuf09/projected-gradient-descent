# First-Order Methods for Smooth Convex Optimization in Isabelle/HOL

This repository contains an Isabelle/HOL formalization of reusable infrastructure for smooth convex first-order optimization methods.

The development is centered around gradient descent and projected gradient descent, but the intended contribution is broader than a single algorithmic convergence proof.  The goal is to build an AFP-style library layer for smooth convex optimization: gradients, first-order certificates, smooth upper bounds, descent estimates, projection inequalities, telescoping arguments, convergence rates, and eventually strong convexity and concrete examples.

The current development already formalizes the standard O(1 / N) function-value convergence theorem for projected gradient descent over a closed convex feasible set.  The next development stage is to extend the library with projected-gradient mappings, optimality characterizations, strong convexity, linear convergence, and basic examples.

## Overview

The project develops the following proof pipeline.

```text
gradient infrastructure
+ convex first-order lower bounds
+ smooth quadratic upper bounds
+ descent estimates
+ telescoping lemmas
+ projection variational inequalities
= convergence guarantees for first-order methods
```

The main algorithmic target is projected gradient descent.

```text
x_{n+1} = P_C (x_n - alpha * G x_n)
```

Here:

* `C` is a closed convex feasible set;
* `P_C` is Euclidean projection onto `C`;
* `f` is a smooth convex objective;
* `G` is a named gradient field for `f`;
* `alpha` is a fixed step size.

The main projected-gradient convergence theorem has the usual form.

```text
f (x N) - f xstar
  <= norm (x 0 - xstar)^2 / (2 * alpha * real N)
```

under the standard assumptions: smooth convexity, closedness and convexity of the feasible set, projected-gradient recurrence, feasible initial point, positive step size, step-size upper bound, existence of a global minimizer, and `N > 0`.

## Current status

The current session contains the following theory files.

```text
Gradient_Preliminaries.thy
Convex_Differentiable.thy
Smooth_Convex.thy
Gradient_Descent.thy
Gradient_Descent_Rates.thy
Gradient_Descent_Convergence.thy
Projection_Optimization.thy
Projected_Gradient_Descent_Convergence.thy
```

The completed core currently includes:

* optimization-oriented gradient predicates and named gradient fields;
* uniqueness and basic rules for gradients;
* first-order convex lower-bound certificates;
* sufficient first-order conditions for global optimality;
* smooth quadratic upper-bound interfaces;
* one-step descent estimates for gradient steps;
* gradient descent recurrences and objective monotonicity;
* finite-sum and small-gradient consequences for gradient descent;
* O(1 / N) function-value convergence for gradient descent;
* Euclidean projection packaged for optimization;
* projection variational inequalities;
* projected gradient descent iterates and feasibility;
* one-step projected distance estimates;
* O(1 / N) function-value convergence for projected gradient descent.

The next intended components are:

* projected-gradient mappings;
* fixed-point and variational-inequality optimality characterizations;
* strong convexity;
* linear convergence under strong convexity;
* concrete quadratic examples;
* AFP document setup.

## Main contributions

The intended contribution of this development is not merely a formal proof of projected gradient descent.  Instead, the project aims to provide a reusable Isabelle/HOL layer for first-order methods in smooth convex optimization.

The main reusable components are:

* a gradient interface built on Isabelle/HOL's derivative infrastructure;
* convex first-order lower-bound certificates;
* smooth upper-bound assumptions in descent-lemma form;
* sequence-level descent and telescoping templates;
* optimization-facing projection lemmas;
* convergence proofs for gradient descent and projected gradient descent;
* locale-based versions of the main assumptions and conclusions.

The development is designed so that future first-order algorithms can reuse the same building blocks rather than reproving the same convexity, smoothness, projection, and telescoping facts from scratch.

## Theory structure

### `Gradient_Preliminaries.thy`

This file introduces an optimization-oriented wrapper around Isabelle/HOL's derivative infrastructure.

Main components include:

* pointwise gradients, via `has_gradient`;
* gradients within a set, via `has_gradient_within`;
* named gradient fields on sets, via `has_gradient_on`;
* uniqueness of gradients;
* the choice-style gradient operator `gradient`;
* elementary gradient rules;
* affine-line restrictions;
* directional derivative facts;
* inner-product and squared-norm algebra used later in descent proofs.

This theory is independent of convexity, smoothness, and algorithms.  Its role is to make later optimization statements readable in terms of gradients, inner products, and norm identities, rather than repeatedly unfolding low-level derivative maps.

### `Convex_Differentiable.thy`

This file develops the first-order language of convex differentiable optimization.

Main components include:

* global minimizers on feasible sets, via `global_min_on`;
* first-order variational inequalities, via `first_order_condition_at`;
* supporting affine lower bounds, via `supports_at` and `supports_on`;
* gradient lower bounds, via `gradient_lower_bound_on`;
* convex differentiability with a named gradient field, via `convex_differentiable_on`;
* a locale form for convex differentiable functions.

The central mathematical result is the supporting-hyperplane property for convex differentiable functions.

```text
convex_on S f
has_gradient f x g
x in S
y in S
==> f x + inner g (y - x) <= f y
```

This is formalized as:

```text
convex_has_gradient_supports
```

and then packaged into reusable consequences such as:

```text
convex_differentiable_on_supporting_hyperplanes
convex_differentiable_on_first_order_sufficient
```

This layer is useful not only for gradient descent and projected gradient descent, but also for future formalizations of constrained first-order methods.

### `Smooth_Convex.thy`

This file introduces the smoothness interface used in descent arguments.

The central assumption is the quadratic upper-bound property.

```text
f y <= f x + inner (G x) (y - x) + (L / 2) * norm (y - x)^2
```

This is the standard descent-lemma form of smoothness.  The file packages this property as:

```text
smooth_upper_bound_on L S f G
```

Main components include:

* Lipschitz-gradient fields, via `lipschitz_gradient_on`;
* quadratic smooth upper bounds, via `smooth_upper_bound_on`;
* smooth convex functions, via `smooth_convex_on`;
* the explicit gradient step map `gradient_step`;
* algebraic identities for gradient steps;
* one-step descent estimates from smooth upper bounds;
* a locale form for smooth convex functions.

The main one-step estimate has the form:

```text
f (gradient_step alpha G x)
<= f x - alpha * norm (G x)^2
   + (L / 2) * alpha^2 * norm (G x)^2
```

Under the step-size condition `alpha * L <= 1`, this gives the cleaner decrease estimate:

```text
f (gradient_step alpha G x)
<= f x - (alpha / 2) * norm (G x)^2
```

This file provides the basic descent mechanism used by the algorithmic layers.

### `Gradient_Descent.thy`

This file lifts one-step gradient-step estimates to gradient descent sequences.

Main components include:

* the gradient descent recurrence, via `gradient_descent_iterates`;
* feasible iterates, via `feasible_iterates`;
* objective values along a sequence, via `objective_values`;
* one-step descent for gradient descent iterates;
* nonincreasing objective values;
* a locale form for gradient descent.

The recurrence has the form:

```text
x (Suc n) = gradient_step alpha G (x n)
```

The main conclusion of this file is that, under suitable smoothness and step-size assumptions, the objective values along feasible gradient descent iterates are nonincreasing.

### `Gradient_Descent_Rates.thy`

This file collects rate-style consequences of the one-step descent estimate.

Main components include:

* abstract telescoping lemmas;
* bounded sums of weighted squared gradient norms;
* bounded sums of squared gradient norms;
* average squared-gradient bounds;
* small-gradient consequences among the first `N` iterates;
* locale-level versions of these results.

The basic finite-sum estimate has the form:

```text
sum (lambda n. (alpha / 2) * norm (G (x n))^2) {..<N}
  <= f (x 0) - f (x N)
```

When `alpha > 0`, this yields:

```text
sum (lambda n. norm (G (x n))^2) {..<N}
  <= (2 / alpha) * (f (x 0) - f (x N))
```

This file provides reusable telescoping infrastructure for later convergence proofs.

### `Gradient_Descent_Convergence.thy`

This file proves the standard O(1 / N) function-value convergence theorem for fixed-step gradient descent on a smooth convex objective.

The proof is based on the usual distance-to-comparator estimate: each gradient step decreases the squared distance potential enough to pay for the next function-value gap.  This estimate is then telescoped.

The main theorem is:

```text
gradient_descent_function_value_gap_bound
```

with conclusion:

```text
f (x N) - f xstar
  <= norm (x 0 - xstar)^2 / (2 * alpha * real N)
```

under smooth convexity, the gradient descent recurrence, feasibility, positive step size, the step-size condition, existence of a global minimizer, and `N > 0`.

The file also provides locale-level versions of the one-step distance estimate, summed gap estimates, and the final convergence bound.

### `Projection_Optimization.thy`

This file introduces the projection layer needed for projected gradient descent.

Main components include:

* the projected gradient step, via `projected_gradient_step`;
* membership of projected points in closed nonempty feasible sets;
* the projection variational inequality;
* algebraic three-point identities;
* one-step projected distance estimates;
* projected gradient descent iterates;
* feasibility of projected gradient descent from an initially feasible point.

The projected gradient step is defined as:

```text
projected_gradient_step C alpha G x
  = closest_point C (gradient_step alpha G x)
```

The key projection inequality used in the proof is the variational inequality for Euclidean projection onto a closed convex set.

```text
inner (gradient_step alpha G x - projected_gradient_step C alpha G x)
      (u - projected_gradient_step C alpha G x)
  <= 0
```

The main one-step estimate has the form:

```text
f p - f u
  <= (norm (x - u)^2 - norm (p - u)^2) / (2 * alpha)
```

where `p = projected_gradient_step C alpha G x`.

This is the projected analogue of the distance-potential inequality used in the unconstrained gradient descent convergence proof.

### `Projected_Gradient_Descent_Convergence.thy`

This file proves the standard O(1 / N) function-value convergence theorem for projected gradient descent on a closed convex feasible set.

The proof follows the same telescoping pattern as the unconstrained gradient descent proof, but replaces the plain gradient-step distance identity with the projected one-step distance inequality.

Main components include:

* monotonicity of objective values along projected gradient descent;
* summed function-value gap bounds;
* distance-potential telescoping;
* O(1 / N) function-value convergence;
* a locale form for projected gradient descent.

The main theorem is:

```text
projected_gradient_descent_function_value_gap_bound
```

with conclusion:

```text
f (x N) - f xstar
  <= norm (x 0 - xstar)^2 / (2 * alpha * real N)
```

under the assumptions:

* `smooth_convex_on L C f G`;
* `closed C`;
* `convex C`;
* `projected_gradient_descent_iterates C alpha G x`;
* `x 0 in C`;
* `0 < alpha`;
* `alpha * L <= 1`;
* `global_min_on C f xstar`;
* `N > 0`.

This theorem is currently the main algorithmic result of the development.

## Planned extensions before AFP submission

The current development already contains the main projected-gradient convergence theorem, but the intended AFP entry is larger than this single result.  The planned extensions are meant to turn the repository into a broader smooth convex optimization library.

### 1. Projected-gradient mappings

The next planned theory is:

```text
Projected_Gradient_Mapping.thy
```

The intended definition is the projected-gradient mapping:

```text
G_C,alpha x = (1 / alpha) * (x - projected_gradient_step C alpha G x)
```

Planned results include:

* zero projected-gradient mapping iff projected fixed point;
* projected fixed point implies the first-order variational inequality;
* the first-order variational inequality implies projected fixed point;
* fixed-point and first-order optimality equivalence;
* convex differentiable projected fixed points are global minimizers.

This layer will connect the algorithmic update rule with the usual optimality language for constrained convex minimization.

### 2. Strong convexity

A later theory should introduce strong convexity in a form compatible with the existing first-order infrastructure.

A natural interface is the first-order strong convexity lower bound:

```text
f y >= f x + inner (G x) (y - x) + (mu / 2) * norm (y - x)^2
```

Planned components include:

* `strong_convex_lower_bound_on`;
* strong convexity implies ordinary gradient lower bounds;
* uniqueness of global minimizers under strong convexity;
* function-value gap lower bounds by squared distance to the minimizer;
* preparation for linear convergence proofs.

### 3. Linear convergence

After strong convexity is available, the development should prove linear convergence for gradient descent and projected gradient descent under suitable assumptions.

A robust target for projected gradient descent is a distance contraction of the form:

```text
norm (x N - xstar)^2
  <= (1 / (1 + alpha * mu))^N * norm (x 0 - xstar)^2
```

This rate is not necessarily the sharpest textbook contraction, but it follows naturally from the existing projected one-step inequality and a strong-convexity lower bound.  It should be well suited to a stable Isabelle development.

### 4. Smoothness from Lipschitz gradients

The current algorithmic proofs use `smooth_upper_bound_on` directly.  A later analytic bridge may prove that Lipschitz gradient fields imply the quadratic smooth upper-bound property under suitable assumptions.

The intended theorem has the form:

```text
lipschitz_gradient_on L S G
+ has_gradient_on f S G
+ suitable segment assumptions
==> smooth_upper_bound_on L S f G
```

This would connect the current descent-lemma interface to a more primitive Lipschitz-gradient assumption.

### 5. Concrete examples

The entry should eventually include basic examples showing that the abstract assumptions can be instantiated.

Possible examples include:

* one-dimensional quadratic objectives;
* Euclidean quadratic objectives;
* least-squares objectives;
* simple box constraints;
* Euclidean ball constraints.

A minimal first example could use:

```text
f x = (1 / 2) * norm x^2
G x = x
L = 1
```

and prove that it satisfies the smooth convex interface.

## Intended final structure

A possible final AFP-oriented structure is:

```text
Projected_Gradient_Descent/
  ROOT
  README.md
  document/
    root.tex
    root.bib

  Gradient_Preliminaries.thy
  Convex_Differentiable.thy
  Smooth_Convex.thy

  Gradient_Descent.thy
  Gradient_Descent_Rates.thy
  Gradient_Descent_Convergence.thy

  Projection_Optimization.thy
  Projected_Gradient_Descent_Convergence.thy
  Projected_Gradient_Mapping.thy

  Strong_Convex.thy
  Gradient_Descent_Linear_Rate.thy
  Projected_Gradient_Descent_Linear_Rate.thy

  Examples_Quadratic.thy
```

The current repository still uses a flat theory layout.  This is acceptable for now.  The structure above describes the intended mathematical organization of the final entry.

## Relation to existing work

This development is intended to complement, not replace, existing Isabelle/HOL optimization developments.

In particular, Isabelle/HOL and HOL-Analysis already provide substantial infrastructure for derivatives, convexity, topology, Euclidean spaces, and closest points.  This project builds on that infrastructure and packages the pieces needed for smooth convex first-order methods.

The AFP entry `Unconstrained_Optimization` develops minimizers and first- and second-order optimality conditions for unconstrained optimization.  The present development has a different emphasis: smooth convex first-order methods, descent estimates, projection-based constrained optimization, and convergence-rate proofs for gradient-type algorithms.

Other theorem provers also contain formalizations of gradient descent and convex optimization.  This repository does not claim priority over the general topic of formalizing first-order methods.  Its intended contribution is an Isabelle/HOL and AFP-compatible reusable library layer for smooth convex optimization and projected first-order methods.

A conservative summary of the contribution is:

```text
This development provides reusable Isabelle/HOL infrastructure for smooth convex first-order methods,
building on HOL-Analysis and culminating in formal convergence proofs for gradient descent and projected gradient descent.
```

## Design principles

### Reusable interfaces

Core mathematical assumptions are packaged as reusable predicates and locales, such as:

```text
has_gradient_on
convex_differentiable_on
smooth_upper_bound_on
smooth_convex_on
gradient_descent_iterates
projected_gradient_descent_iterates
```

The goal is to make theorem statements stable, readable, and reusable.

### Named gradient fields

The project consistently allows the use of a named gradient field `G`.

This keeps theorem statements cleaner and avoids unnecessary dependence on choice-style gradient definitions.  The choice-style operator `gradient` is still available, but the algorithmic development is mostly phrased using explicit gradient fields.

### Separation of analytic and algorithmic layers

The smoothness upper-bound property is currently treated as a direct interface.

This allows the convergence proofs for gradient descent and projected gradient descent to proceed independently of the more delicate analytic proof that Lipschitz gradients imply the descent lemma.

A later theory may connect `lipschitz_gradient_on` to `smooth_upper_bound_on`.

### Projection as an optimization interface

Projection theory is exposed through optimization-oriented lemmas rather than raw metric geometry alone.

The development packages the facts needed for projected methods:

* projected points belong to the feasible set;
* projection satisfies a variational inequality;
* this variational inequality yields the projected one-step distance estimate;
* the one-step estimate can be telescoped to prove convergence.

### Abstract telescoping patterns

The development separates algorithm-specific one-step inequalities from general telescoping arguments.

The intended pattern is:

```text
algorithm-specific one-step inequality
+ general telescoping lemma
==> convergence rate
```

This pattern is used for both gradient descent and projected gradient descent, and it should be reusable for future first-order methods.

### Conservative AFP claims

The project avoids overly broad novelty claims.

It does not claim to be the first formalization of gradient descent in any theorem prover.  Instead, it emphasizes its Isabelle/HOL setting, its AFP-compatible organization, its reusable smooth convex optimization interfaces, and its projected-gradient convergence development.

## Build instructions

From the repository root, run:

```bash
isabelle build -D .
```

For AFP-style document checking, the intended final command is:

```bash
isabelle build -v -o browser_info -o "document=pdf" \
  -o "document_variants=document:outline=/proof,/ML" -D .
```

Before AFP submission, the repository should also be checked for forbidden or unfinished proof commands, such as `sorry`, `sledgehammer`, `smt_oracle`, and `back`.

## Current next steps

The immediate next goal is not to shrink the scope, but to extend the current projected-gradient development into a larger first-order optimization library.

Suggested next milestones:

1. add `Projected_Gradient_Mapping.thy`;
2. prove fixed-point and first-order optimality characterizations for projected gradient steps;
3. add `Strong_Convex.thy`;
4. prove uniqueness of minimizers and distance-gap lower bounds under strong convexity;
5. add linear convergence results for gradient descent and projected gradient descent;
6. add at least one concrete quadratic example;
7. add AFP document files under `document/`;
8. polish theorem names and locale interfaces;
9. run AFP-style document build;
10. prepare the final AFP submission.

## Repository status

This repository is under active development.

The current core already contains the main O(1 / N) convergence theorem for projected gradient descent.  The remaining work is to extend the library so that the final AFP entry is a medium-to-large reusable development for smooth convex first-order optimization, rather than only a compact proof of one algorithm.
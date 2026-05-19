# First-Order Methods for Smooth Convex Optimization in Isabelle/HOL

This repository is a work-in-progress Isabelle/HOL formalization project for first-order methods in smooth convex optimization.

The project originally started from projected gradient descent, but its broader goal is to develop reusable Isabelle/HOL infrastructure for smooth convex optimization. The intended contribution is not only a formal proof of one algorithm, but a collection of definitions, lemmas, locales, and proof templates that can support future formalizations of first-order optimization methods.

Projected gradient descent is treated as a central application of the framework.

## Project vision

The long-term goal is to provide an AFP-style reusable library for first-order methods in smooth convex optimization.

The intended scope includes:

1. optimization-oriented gradient infrastructure;
2. first-order certificates for convex differentiable functions;
3. smoothness assumptions and descent-lemma-style upper bounds;
4. abstract descent estimates and telescoping proof patterns;
5. gradient descent and its convergence guarantees;
6. Euclidean projection onto closed convex feasible sets;
7. projection variational inequalities and fixed-point characterizations;
8. projected gradient descent for constrained smooth convex minimization;
9. projected-gradient mappings and optimality characterizations;
10. optional extensions to strong convexity, linear convergence, and concrete examples.

The central mathematical idea is that many first-order convergence proofs can be decomposed into a small number of reusable ingredients:

```text
convex first-order lower bounds
+ smooth upper bounds
+ geometric projection inequalities
+ norm algebra
+ telescoping estimates
= convergence guarantees for first-order methods
```

The repository is therefore organized around reusable proof infrastructure rather than a single isolated theorem.

## Motivation

First-order methods are among the basic tools of convex optimization. Their convergence analyses usually rely on a recurring collection of elementary but delicate ingredients:

* differentiability and gradients;
* convex first-order lower bounds;
* smoothness upper bounds;
* descent inequalities;
* projection inequalities;
* telescoping sums;
* fixed-point and optimality equivalences.

In informal mathematics, these ingredients are often reused across gradient descent, projected gradient descent, proximal gradient methods, and related algorithms. The aim of this project is to make a clean Isabelle/HOL version of this infrastructure.

The project is intended to be useful for later Isabelle developments in optimization, especially developments that need smooth convex analysis and gradient-type convergence proofs.

## Main algorithmic target

The motivating constrained algorithm is projected gradient descent:

```text
x_{k+1} = P_C (x_k - alpha * grad f x_k)
```

Here:

* `C` is a feasible set;
* `P_C` is Euclidean projection onto `C`;
* `f` is a convex differentiable function;
* `grad f` is the gradient of `f`;
* `alpha` is a step size.

A typical target convergence theorem is the standard O(1 / N) rate for smooth convex minimization over a closed convex feasible set:

```text
f (x_N) - f x_star <= norm (x_0 - x_star)^2 / (2 * alpha * N)
```

under suitable assumptions on convexity, smoothness, feasibility, existence of a minimizer, and the step size.

The projected-gradient part is not yet complete.

## Current status

The current development contains the following theory files:

```text
Gradient_Preliminaries.thy
Convex_Differentiable.thy
Smooth_Convex.thy
Gradient_Descent.thy
```

Together, these files provide the first layer of the formal infrastructure needed for gradient descent and projected gradient descent.

Currently completed or partially completed components include:

* gradient predicates and named gradient fields;
* uniqueness and basic rules for gradients;
* affine-line restrictions and directional derivatives;
* first-order convex lower-bound certificates;
* sufficient first-order conditions for global optimality in convex problems;
* smooth upper-bound interfaces;
* explicit gradient-step maps;
* one-step descent estimates for gradient steps;
* gradient descent recurrences;
* monotonicity of objective values along gradient descent iterates.

The following components are not yet complete:

* convergence-rate theorems for gradient descent;
* Euclidean projection theory packaged for optimization;
* projected gradient descent;
* projected-gradient convergence rates;
* strong convexity and linear convergence;
* concrete examples and instantiations;
* AFP document setup.

## Theory overview

### `Gradient_Preliminaries.thy`

This file introduces an optimization-oriented wrapper around Isabelle/HOL's derivative infrastructure.

Main components include:

* pointwise gradients, via `has_gradient`;
* gradients within a set, via `has_gradient_within`;
* named gradient fields on sets, via `has_gradient_on`;
* uniqueness of gradients;
* the gradient operator `gradient`;
* elementary gradient rules;
* affine-line restrictions;
* directional derivatives along lines;
* inner-product and squared-norm algebra used later in descent proofs.

This theory is intentionally independent of convexity, smoothness, and algorithms.

Its role is to make later optimization statements readable in terms of gradients and inner products, instead of repeatedly unfolding low-level derivative maps.

### `Convex_Differentiable.thy`

This file develops the first-order language of convex differentiable optimization.

Main components include:

* global minimizers on feasible sets, via `global_min_on`;
* first-order variational inequalities, via `first_order_condition_at`;
* supporting affine lower bounds, via `supports_at` and `supports_on`;
* gradient lower bounds, via `gradient_lower_bound_on`;
* convex differentiability with a named gradient field, via `convex_differentiable_on`;
* a locale form for convex differentiable functions.

The central theorem is the first-order supporting-hyperplane property for convex differentiable functions:

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

This layer is meant to be reused by projected gradient descent, constrained optimality conditions, Frank-Wolfe-style methods, and other first-order convex optimization developments.

### `Smooth_Convex.thy`

This file introduces the smoothness interface used for descent arguments.

The central assumption is the quadratic upper-bound property:

```text
f y <= f x + inner (G x) (y - x) + (L / 2) * norm (y - x)^2
```

This is the standard descent-lemma form of smoothness. The file packages this property as:

```text
smooth_upper_bound_on L S f G
```

so that algorithmic proofs can use it directly.

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
* objective values along a sequence;
* one-step descent for gradient descent iterates;
* nonincreasing objective values;
* a locale form for gradient descent.

The recurrence has the form:

```text
x (Suc n) = gradient_step alpha G (x n)
```

The current main conclusion is that, under suitable smoothness and step-size assumptions, the objective values along gradient descent iterates are nonincreasing.

This file is the first algorithmic layer of the project. It is structured so that later convergence-rate proofs can reuse the recurrence and descent results.

## Planned development

The intended final development is broader than a single projected-gradient theorem.

A possible final structure is:

```text
Projected_Gradient_Descent/
  ROOT
  README.md

  Gradient_Preliminaries.thy
  Convex_Differentiable.thy
  Smooth_Convex.thy
  Gradient_Descent.thy

  Gradient_Descent_Rates.thy

  Projection_Optimization.thy
  Projected_Gradient_Descent.thy
  Projected_Gradient_Descent_Rates.thy

  Strong_Convex.thy
  Strong_Convex_Rates.thy

  Examples_Quadratic.thy
  Examples_Least_Squares.thy
```

The current repository still uses a flat theory layout. The structure above describes the intended mathematical organization, not necessarily the current physical directory layout.

## Mathematical roadmap

### 1. Gradient infrastructure

The first layer packages derivatives into optimization-style gradient statements.

The goal is to make later proofs state assumptions and conclusions in the language of gradients, inner products, and norm identities.

### 2. First-order convex certificates

The second layer proves that convex differentiability implies supporting affine lower bounds.

The intended proof pipeline is:

```text
convex differentiability
==> supporting affine lower bounds
==> first-order optimality certificates
==> global minimizers
```

This layer is useful beyond gradient descent. It provides a reusable first-order optimality interface for differentiable convex optimization.

### 3. Smooth upper bounds

The third layer packages the smoothness upper-bound inequality used in descent proofs.

The current interface treats the quadratic upper-bound property as an explicit assumption. This keeps algorithmic proofs independent of the more analytic proof that Lipschitz gradients imply the descent lemma.

A later extension may connect `lipschitz_gradient_on` to `smooth_upper_bound_on`.

### 4. Abstract descent templates

A major goal is to avoid reproving every convergence theorem from scratch.

The project should eventually include abstract proof templates of the following form:

```text
one-step progress inequality
+ telescoping
==> convergence rate
```

This would make the development reusable for future formalizations of other first-order methods.

### 5. Gradient descent rates

The next algorithmic milestone is to strengthen `Gradient_Descent.thy` with convergence-rate estimates.

Planned results include:

* bounded sums of squared gradient norms;
* minimum-gradient-norm bounds;
* O(1 / N) function-value convergence under convexity;
* reusable telescoping lemmas for descent methods.

A typical target statement is:

```text
f (x N) - f x_star <= norm (x 0 - x_star)^2 / (2 * alpha * N)
```

under the usual smooth convex assumptions.

### 6. Projection theory for optimization

The next major layer is a projection-facing optimization interface.

HOL-Analysis already contains substantial convex-geometric infrastructure. The purpose of this project is not to duplicate low-level geometry unnecessarily, but to package the relevant facts in an optimization-oriented form.

Planned components include:

* projection belongs to the feasible set;
* projection minimizes distance to the original point;
* projection variational inequality;
* nonexpansiveness of projection;
* fixed-point characterizations of projected steps;
* projected gradient mapping.

The key inequality for projected methods has the form:

```text
inner (x - P_C x) (y - P_C x) <= 0
```

for every feasible point `y`.

### 7. Projected gradient descent

The projected-gradient layer will combine:

* smooth upper-bound inequalities;
* projection variational inequalities;
* convex first-order lower bounds;
* squared-norm algebra;
* telescoping estimates.

The target update is:

```text
x (Suc n) = P_C (x n - alpha * grad f (x n))
```

The intended milestones are:

* feasibility of all iterates;
* one-step projected descent estimates;
* monotonicity of objective values, where applicable;
* fixed-point characterization of projected-gradient steps;
* O(1 / N) convergence for smooth convex constrained minimization.

### 8. Strong convexity and linear convergence

A later extension may add strong convexity.

Planned components include:

* `strongly_convex_on`;
* lower-bound formulations of strong convexity;
* uniqueness of minimizers under strong convexity;
* linear convergence of gradient descent;
* linear convergence of projected gradient descent under suitable assumptions.

This layer is not required for the first complete version, but it would make the library substantially more useful.

### 9. Concrete examples

The final development should include examples showing that the framework can be instantiated.

Possible examples include:

* quadratic objectives;
* least-squares objectives;
* simple box constraints;
* Euclidean ball constraints;
* affine subspace constraints.

The purpose of the examples is to demonstrate that the abstract assumptions are usable in concrete optimization problems.

## Relation to existing work

This project is intended to complement, not replace, existing Isabelle/HOL optimization developments.

In particular, the AFP entry `Unconstrained_Optimization` develops minimizers and first-/second-order optimality conditions for unconstrained optimization. The present project has a different emphasis: smooth convex first-order methods, descent estimates, projection-based constrained optimization, and convergence-rate proofs for gradient-type algorithms.

The AFP entry `Simplex` formalizes an incremental simplex algorithm for linear constraints and SMT-style applications. That development is algorithmic, but its mathematical setting is different from smooth convex first-order methods.

There are also formalizations of convex optimization algorithms in other theorem provers, including Lean developments of first-order methods and convergence rates. This repository does not claim priority over the general topic of formalizing gradient descent. Its intended contribution is an Isabelle/HOL and AFP-compatible reusable library layer for smooth convex optimization and projected first-order methods.

A safe summary of the intended contribution is:

```text
This development provides reusable Isabelle/HOL infrastructure for smooth convex first-order methods,
building on HOL-Analysis and complementing existing Isabelle optimization entries.
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
```

The goal is to make later theorem statements stable and easy to reuse.

### Named gradient fields

The project consistently allows the use of a named gradient field `G`.

This keeps theorem statements cleaner and avoids unnecessary dependence on choice-style definitions of gradients.

### Separation of analytic and algorithmic layers

The smoothness upper-bound property is currently treated as an explicit interface.

This allows gradient descent and projected gradient descent proofs to proceed independently of the more delicate analytic proof that Lipschitz gradients imply the descent lemma.

### Projection as an optimization interface

Projection theory should be exposed through optimization-oriented lemmas, rather than only through raw metric geometry statements.

The intended interface should make it easy to prove projected-method results from projection variational inequalities.

### Abstract convergence templates

The project should eventually contain reusable convergence templates.

The intended pattern is:

```text
algorithm-specific one-step inequality
+ general telescoping theorem
==> convergence rate
```

This is meant to reduce duplication in future formalizations of first-order methods.

### Conservative AFP claims

The project should avoid overly broad novelty claims.

It should not claim to be the first formalization of gradient descent in any theorem prover. Instead, it should emphasize its Isabelle/HOL setting, its AFP-compatible organization, and its reusable smooth convex optimization interfaces.

## Build instructions

From the repository root, run:

```bash
isabelle build -D .
```

For AFP-style document checking, the intended final command will be close to:

```bash
isabelle build -v -o browser_info -o "document=pdf" \
  -o "document_variants=document:outline=/proof,/ML" -D .
```

The document-generation setup may require additional AFP-style files before submission.

## Current next steps

The immediate next step is to strengthen the current gradient descent layer and then move toward projection.

Suggested next milestones:

1. add `Gradient_Descent_Rates.thy`;
2. prove finite-sum and telescoping estimates for gradient descent;
3. introduce `Projection_Optimization.thy`;
4. package projection facts in an optimization-facing form;
5. define projected gradient descent iterates;
6. prove feasibility of projected-gradient iterates;
7. prove one-step projected descent estimates;
8. prove the basic O(1 / N) projected-gradient convergence theorem;
9. add concrete examples;
10. prepare the AFP document setup.

A minimal next milestone is:

```text
Gradient_Descent_Rates.thy
```

with results such as:

```text
bounded sum of squared gradient norms
minimum gradient norm bound
basic function-value convergence rate
```

After that, the project should move to projection theory.

## Repository status

This repository is currently under active development.

Completed or partially completed layers:

* gradient preliminaries;
* first-order convex optimality certificates;
* smooth upper-bound interfaces;
* one-step descent estimates for gradient steps;
* gradient descent recurrence;
* monotonicity of objective values for gradient descent iterates.

Not yet complete:

* convergence-rate theorems for gradient descent;
* Euclidean projection theory packaged for optimization;
* projected gradient descent;
* projected-gradient convergence rates;
* strong convexity and linear rates;
* concrete examples;
* AFP document setup.

The projected-gradient convergence theorem is not yet complete.

## Intended contribution

The intended contribution is a reusable Isabelle/HOL development for smooth convex optimization and first-order methods.

The project aims to be useful not only as a formalization of projected gradient descent, but also as infrastructure for future Isabelle/HOL formalizations of optimization algorithms.

The most reusable components are expected to be:

* optimization-oriented gradient interfaces;
* first-order convexity certificates;
* smooth upper-bound descent lemmas;
* abstract descent and telescoping patterns;
* projection inequalities for constrained optimization;
* projected-gradient optimality characterizations;
* convergence proofs for gradient-type methods.

The long-term goal is that future Isabelle/HOL developments in convex optimization can import this project instead of rebuilding these foundations from scratch.
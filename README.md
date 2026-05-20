# Projected Gradient Descent in Isabelle/HOL

This repository contains an Isabelle/HOL formalization of basic first-order methods for smooth convex optimization, with projected gradient descent as the central application.

The development is intended as a reusable library for formal reasoning about gradient-based optimization methods. It provides abstract interfaces for gradients, convexity, smooth upper bounds, descent estimates, projection geometry, convergence rates, projected-gradient mappings, strong convexity, and basic quadratic examples.

The long-term goal is to prepare this development for submission to the Archive of Formal Proofs.

## Overview

The entry formalizes a small but reusable fragment of smooth convex optimization theory.

The main development includes:

* gradient interfaces for functions on real inner-product spaces;
* first-order characterizations of convex differentiable functions;
* quadratic smooth upper-bound assumptions;
* descent lemmas for gradient descent;
* sublinear O(1/N) convergence estimates for gradient descent;
* projection geometry for closed convex sets;
* projected gradient descent and its basic feasibility properties;
* sublinear O(1/N) convergence estimates for projected gradient descent;
* projected-gradient mappings and their relation to first-order optimality;
* strong convexity assumptions;
* a linear-rate estimate for projected gradient descent under strong convexity;
* a Lipschitz-smoothness interface;
* simple quadratic examples.

The formalization is deliberately structured around reusable assumptions rather than a single concrete algorithm. In particular, the main convergence proofs use abstract smooth upper-bound and convexity interfaces, so that future methods can reuse the same proof infrastructure.

## Main entry point

The main entry point is:

```isabelle
theory Projected_Gradient_Descent
  imports
    Examples_Quadratic
begin

end
```

After installation as an AFP entry, client theories should be able to import the development through the main theory of the entry.

For local development inside this repository, the theories can be built directly using the Isabelle session defined in `ROOT`.

## Repository structure

The current theory files are organized as follows.

* `Gradient_Preliminaries.thy`

  Basic gradient-related definitions and elementary facts used throughout the development.

* `Convex_Differentiable.thy`

  First-order reasoning for convex differentiable functions, including reusable first-order convexity inequalities.

* `Smooth_Convex.thy`

  Smooth convex interfaces based on quadratic upper bounds.

* `Gradient_Descent.thy`

  Definitions and one-step estimates for gradient descent.

* `Gradient_Descent_Rates.thy`

  Abstract rate lemmas and finite-sum estimates used in convergence proofs.

* `Gradient_Descent_Convergence.thy`

  Sublinear convergence results for gradient descent.

* `Projection_Optimization.thy`

  Projection geometry and projected-gradient one-step estimates.

* `Projected_Gradient_Descent_Convergence.thy`

  Feasibility and O(1/N)-type convergence results for projected gradient descent.

* `Projected_Gradient_Mapping.thy`

  Projected-gradient mappings and their connection with first-order optimality.

* `Strong_Convex.thy`

  Strong convexity definitions and basic consequences.

* `Projected_Gradient_Descent_Linear_Rate.thy`

  Linear-rate convergence estimates for projected gradient descent under strong convexity.

* `Lipschitz_Smoothness.thy`

  A Lipschitz-gradient interface and its relation to the smooth upper-bound framework.

* `Examples_Quadratic.thy`

  Basic quadratic examples illustrating the abstract interfaces.

* `Projected_Gradient_Descent.thy`

  Umbrella theory collecting the full development.

## Mathematical content

The development is centered around the following standard first-order optimization scheme.

For unconstrained gradient descent, the update is:

```text
x_{n+1} = x_n - alpha * G x_n
```

For projected gradient descent over a closed convex set C, the update is:

```text
x_{n+1} = P_C (x_n - alpha * G x_n)
```

where `P_C` is the metric projection onto `C`.

The formalization proves convergence results under assumptions of the following form:

* `f` is convex on a feasible set;
* `G` is a gradient-like map for `f`;
* `f` satisfies a quadratic smooth upper bound with constant `L`;
* the step size `alpha` is positive and satisfies the usual smoothness restriction;
* in the projected case, the feasible set is closed and convex;
* for linear convergence, `f` additionally satisfies a strong convexity condition.

The projected-gradient mapping is used as a reusable optimality certificate. Informally, it measures the failure of a point to be fixed by one projected-gradient step. A zero projected-gradient mapping corresponds to the usual first-order optimality condition for the constrained problem.

## Design goals

This project is designed around the following principles.

### Reusable interfaces

The theory avoids hard-coding a specific Euclidean space or a specific objective function whenever possible. Most statements are formulated over real inner-product spaces and abstract feasible sets.

### Separation between assumptions and algorithms

Smoothness, convexity, projection geometry, descent estimates, and convergence-rate arguments are separated into different theory files. This makes it easier to reuse parts of the development for other first-order methods.

### AFP-oriented structure

The repository is structured as an Isabelle session with a `ROOT` file and an umbrella theory. The goal is to make the formalization suitable for AFP submission after final polishing, documentation, and style cleanup.

### Stability for future extensions

The current theory names and theorem interfaces are intended to be kept stable as much as possible. Future extensions should preferably add new lemmas and theories without breaking existing imports.

## Building the project

To build the Isabelle session from the root of the repository, run:

```bash
isabelle build -D .
```

To build with document generation enabled, run:

```bash
isabelle build -v -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -D .
```

The session depends on `HOL-Analysis`, so the first build may spend most of its time building Isabelle's analysis library. Once the dependency is cached, the project session itself should build quickly.

## Current status

The current development already contains:

* the basic gradient and convexity infrastructure;
* smooth upper-bound interfaces;
* gradient descent convergence;
* projected gradient descent convergence;
* projected-gradient mapping optimality results;
* strong convexity;
* a linear-rate result for projected gradient descent;
* Lipschitz-smoothness interfaces;
* quadratic examples;
* an umbrella theory for the whole entry.

The next polishing stage should focus on library organization, documentation, theorem naming, and AFP-readiness rather than adding many unrelated results.

## Suggested next steps before AFP submission

The main remaining tasks are:

1. factor purely abstract descent and telescoping lemmas into a separate reusable theory;
2. separate pure projection geometry from projected-gradient optimization estimates;
3. add a short AFP document explaining the mathematical structure of the entry;
4. add a bibliography citing standard references on first-order convex optimization;
5. check that all main theorem names form a stable public interface;
6. remove or rewrite any temporary comments, TODOs, or development-only notes;
7. check for `sorry`, `sledgehammer`, `smt_oracle`, and `back`;
8. check for unnamed `[simp]` rules;
9. run the full Isabelle build and document build before submission.

## Possible future extensions

The current entry focuses on reusable infrastructure for smooth convex first-order methods and the convergence theory of gradient descent and projected gradient descent.

Possible future extensions include:

* a full theorem showing that Lipschitz continuity of the gradient implies the quadratic smooth upper-bound interface under suitable segment assumptions;
* concrete constrained examples such as interval, box, or ball constraints;
* least-squares examples;
* proximal gradient methods;
* conditional gradient methods;
* projected methods for more specialized feasible sets;
* additional convergence criteria based on projected-gradient mappings.

These extensions are not required for the current AFP-oriented core, but they would naturally build on the existing interfaces.

## References

The mathematical development follows standard material from convex optimization and first-order methods. Suitable references for the AFP document include:

* Yurii Nesterov, `Lectures on Convex Optimization`;
* Amir Beck, `First-Order Methods in Optimization`;
* Dimitri P. Bertsekas, `Nonlinear Programming`.

## License

This project is intended for academic and formalization purposes. A suitable open-source license should be added before public AFP submission if one is not already present.
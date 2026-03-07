# Cao-Cerenzia-Kazaras 2014

https://arxiv.org/abs/1406.7033v1

## Axiomatized Facts

Currently, the following are injected as local axioms or abstract classes.

### Analytic & Calculus Rules
- **`ESEExponentialSmooth`**: Logarithmic exponentiation rules mapping $E = e^{(p-1)u}$, binding its gradient, Laplacian, and time derivative directly to derivatives of $u$.

### Geometric Evolution Equations
- **`EndangeredSpeciesEquation`**: The "endangered species equation" under the logarithmic transformation $u = \log f$: $\partial_t u = \Delta u + |\nabla u|^2 + E$.

### Commutators & Properties
- **`RicciFlat`**: The assumption that the underlying manifold is Ricci flat, i.e., $Rc = 0$.(Since we are in $\mathbb{R}^n$)

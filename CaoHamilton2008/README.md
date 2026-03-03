# Cao-Hamilton 2008

https://arxiv.org/abs/0807.0568

## Axiomatized Facts

Currently, the following are injected as axioms.

### Analytic & Calculus Rules
- **`LogSmooth`**: Logarithmic transformation rules ($f = e^{-u}$), binding gradient and time derivative relations.
- **`SpatialCalculusRules`**: Linearity of gradient and Laplacian, product rules, and vanishing spatial derivatives for constants.
- **`ScalarTimeDerivRules`**: Standard single-variable calculus rules for scalar time derivatives $\partial_t$.
- **`TimeWeight`**: Existence, positivity ($t^{-1} \ge 0$), and time derivative ($\partial_t t^{-1} = -t^{-2}$) of the inverse time parameter.

### Geometric Evolution Equations
- **`ScalarCurvatureEvolution`**: Evolution of scalar curvature under Ricci flow: $\partial_t R = \Delta R + 2|Rc|^2$.
- **`GradientSquaredEvolution`**: Evolution of gradient norm squared: $\partial_t |\nabla u|^2 = 2Rc(\nabla u, \nabla u) + 2g(\nabla u, \nabla(\partial_t u))$.
- **`LaplacianEvolution`**: Evolution of the Laplacian: $\partial_t (\Delta u) = \Delta (\partial_t u) + 2 \langle Rc, Hess(u) \rangle$.
- **`RicciFlowEquation1D`**: Heat-type equation under Ricci flow: $\partial_t f = \Delta f - c R f$.

### Commutators & Properties
- **`LaplacianGradientCommutator`**: Commutation of Laplacian and gradient: $\Delta(\nabla u) = \nabla(\Delta u) + Rc(\nabla u, \cdot)$.
- **`NormSquaredNonneg`**: Non-negativity of squared tensor norms and gradient norms: $0 \le |T|^2$, $0 \le |\nabla f|^2$.

### Principles & Inequalities
- **`TraceHarnackInequality`**: Hamilton's Trace Harnack Inequality: $\partial_t R + R/t + 2\langle \nabla R, \nabla u \rangle + 2Rc(\nabla u, \nabla u) \ge 0$.
- **`ParabolicMaximumPrinciple`**: If $\partial_t H \le \Delta H - 2\langle \nabla H, \nabla u \rangle - \frac{2}{t}H$, then $H \le 0$ globally.

import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Time
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Operators.Bochner
import DifferentialGeometry.Flows.RicciFlow
import DifferentialGeometry.Analysis.TraceRankOne
import DifferentialGeometry.Analysis.TensorInnerProduct
import DifferentialGeometry.Operators.CovariantDerivative
import DifferentialGeometry.Operators.SpatialConstant
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

namespace CaoHamilton2008

variable {Time R V : Type}
variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [DerivationRules R V] [TraceOperator R V]
variable [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V]
variable [ActionTimeDerivativeRules Time R V] [Invertible (2:R)]

/-- Logarithmic transformation rules axiomatizing `f = e^{-u}` -/
class LogSmooth
  (metric : MetricDuality R V)
  (u f inv_f : Time → R) where
  f_eq : ∀ t, f t * inv_f t = 1
  grad_eq : ∀ t, grad metric (f t) = - ((f t) • grad metric (u t))
  dt_eq : ∀ t, TimeDerivative.partial_t f t = - (f t) * TimeDerivative.partial_t u t

open DerivationAction

/-- $X(f) = -f X(u)$ -/
lemma action_eq
  (metric : MetricDuality R V)
  (u f inv_f : Time → R)
  [log_smooth : LogSmooth metric u f inv_f]
  (t : Time) (X : V) :
  action X (f t) = - (f t) * action X (u t) := by
  have h1 : action X (f t) = metric.g (grad metric (f t)) X := (g_grad metric (f t) X).symm
  have h2 : grad metric (f t) = - ((f t) • grad metric (u t)) := log_smooth.grad_eq t
  rw [h1, h2]
  have h3 : metric.g (- ((f t) • grad metric (u t))) X = - (f t) * metric.g (grad metric (u t)) X := by
    calc metric.g (- ((f t) • grad metric (u t))) X
      _ = metric.g (((-1:R) * f t) • grad metric (u t)) X := by
        have this1 : - ((f t) • grad metric (u t)) = (-1:R) • ((f t) • grad metric (u t)) := by rw [neg_one_smul]
        have this2 : (-1:R) • ((f t) • grad metric (u t)) = ((-1:R) * f t) • grad metric (u t) := by rw [smul_smul]
        rw [this1, this2]
      _ = ((-1:R) * f t) * metric.g (grad metric (u t)) X := metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left _ _ _
      _ = - (f t) * metric.g (grad metric (u t)) X := by ring
  rw [h3]
  have h4 : metric.g (grad metric (u t)) X = action X (u t) := g_grad metric (u t) X
  rw [h4]

/-- $Hess(f) = -f Hess(u) + f du \otimes du$ -/
lemma hess_eq
  (metric : MetricDuality R V)
  (conn : AffineConnection R V)
  (u f inv_f : Time → R)
  [log_smooth : LogSmooth metric u f inv_f]
  (t : Time) (X Y : V) :
  Hess conn (f t) X Y = - f t * Hess conn (u t) X Y + f t * action X (u t) * action Y (u t) := by
  dsimp [Hess]
  have h1 : action Y (f t) = - (f t) * action Y (u t) := action_eq metric u f inv_f t Y
  have h2 : action X (action Y (f t)) = action X (- (f t) * action Y (u t)) := by rw [h1]
  rw [h2]
  have h3 : action X (- (f t) * action Y (u t)) = action X (- (f t)) * action Y (u t) + (- (f t)) * action X (action Y (u t)) := DerivationRules.action_smul_right X (- (f t)) (action Y (u t))
  rw [h3]
  have h4 : action X (- (f t)) = - action X (f t) := action_neg X (f t)
  rw [h4]
  have h5 : action X (f t) = - (f t) * action X (u t) := action_eq metric u f inv_f t X
  rw [h5]
  have h6 : action (conn.nabla X Y) (f t) = - (f t) * action (conn.nabla X Y) (u t) := action_eq metric u f inv_f t (conn.nabla X Y)
  rw [h6]
  ring

/-- $\Delta f = f|\nabla u|^2 - f\Delta u$ -/
lemma laplacian_eq
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u f inv_f : Time → R)
  [log_smooth : LogSmooth metric u f inv_f]
  (t : Time) :
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) =
  f t * metric.g (grad metric (u t)) (grad metric (u t)) - f t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) := by
  dsimp [laplacian]
  have h1 : Hess conn (f t) =
            (fun X Y => - f t * Hess conn (u t) X Y + f t * (action X (u t) * action Y (u t))) := by
    funext X Y
    have he : Hess conn (f t) X Y = - f t * Hess conn (u t) X Y + f t * action X (u t) * action Y (u t) := hess_eq metric conn u f inv_f t X Y
    have he2 : f t * action X (u t) * action Y (u t) = f t * (action X (u t) * action Y (u t)) := by ring
    rw [he, he2]
  rw [h1]
  have hx : (fun X Y => - f t * Hess conn (u t) X Y + f t * (action X (u t) * action Y (u t))) = (fun X Y => (- f t) * Hess conn (u t) X Y) + (fun X Y => f t * (action X (u t) * action Y (u t))) := rfl
  rw [hx]
  have ht : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor ((fun X Y => (- f t) * Hess conn (u t) X Y) + (fun X Y => f t * (action X (u t) * action Y (u t)))) =
            MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => (- f t) * Hess conn (u t) X Y) +
            MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => f t * (action X (u t) * action Y (u t))) := by
    exact MetricTraceRules.trace_add (metric := metric.toNonDegenerateMetric.toMetricTensor) (fun X Y => (- f t) * Hess conn (u t) X Y) (fun X Y => f t * (action X (u t) * action Y (u t)))
  rw [ht]
  have h3 : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => (- f t) * Hess conn (u t) X Y) =
            (- f t) * MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => Hess conn (u t) X Y) := by
    exact MetricTraceRules.trace_smul (metric := metric.toNonDegenerateMetric.toMetricTensor) (- f t) _
  rw [h3]
  have h4 : (fun X Y => f t * (action X (u t) * action Y (u t))) =
            (fun X Y => f t * (metric.g (grad metric (u t)) X * metric.g (grad metric (u t)) Y)) := by
    funext X Y
    have gX : action X (u t) = metric.g (grad metric (u t)) X := (g_grad metric (u t) X).symm
    have gY : action Y (u t) = metric.g (grad metric (u t)) Y := (g_grad metric (u t) Y).symm
    rw [gX, gY]
  rw [h4]
  have h5 : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => f t * (metric.g (grad metric (u t)) X * metric.g (grad metric (u t)) Y)) =
            f t * MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => metric.g (grad metric (u t)) X * metric.g (grad metric (u t)) Y) := by
    exact MetricTraceRules.trace_smul (metric := metric.toNonDegenerateMetric.toMetricTensor) (f t) _
  rw [h5]
  have h6 : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toMetricTensor (fun X Y => metric.g (grad metric (u t)) X * metric.g (grad metric (u t)) Y) =
            metric.g (grad metric (u t)) (grad metric (u t)) := by
    exact MetricTraceRankOneRules.trace_rank_one (metric := metric.toNonDegenerateMetric.toMetricTensor) (grad metric (u t)) (grad metric (u t))
  rw [h6]
  ring

class RicciFlowEquation1D
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (f : Time → R)
  (c : R)
  (R_scalar : Time → R) where
  heat_eq : ∀ t, TimeDerivative.partial_t f t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - c * R_scalar t * f t

/-! AXIOMIZED FACT: Evolution of Scalar Curvature under Ricci Flow.
This will be rigorously derived from the library's tensor calculus (Palatini identity, etc.) in the future.
Equation: ∂_t R = ΔR + 2|Rc|^2 -/
class ScalarCurvatureEvolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  (conn : AffineConnection R V)
  (Rc_form : SmoothBilinearForm R V)
  (R_scalar : Time → R) where
  rc_eq : ∀ X Y, Rc_form.val X Y = Rc conn X Y
  dt_R : ∀ t, TimeDerivative.partial_t (fun t => R_scalar t) t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form

/-! AXIOMIZED FACT: Evolution of Gradient Squared under Ricci Flow.
This will be rigorously derived from the library's tensor calculus (Palatini identity, etc.) in the future.
Equation: ∂_t |∇u|^2 = 2Rc(∇u, ∇u) + 2g(∇u, ∇(∂_t u)) -/
class GradientSquaredEvolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u : Time → R)
  (R_scalar : Time → R) where
  dt_grad_sq : ∀ t, TimeDerivative.partial_t (fun t => metric.g (grad metric (u t)) (grad metric (u t))) t =
    (2:R) * Rc conn (grad metric (u t)) (grad metric (u t)) + (2:R) * metric.g (grad metric (u t)) (grad metric (TimeDerivative.partial_t (fun t => u t) t))

class LaplacianEvolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u : Time → R)
  (Rc_form : SmoothBilinearForm R V) where
  dt_laplacian : ∀ t, TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u s)) t =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (TimeDerivative.partial_t u t) + (2:R) * tensorInnerProduct metric Rc_form (hessianForm conn (u t))

/-- Equation (2.1) (page 4, middle) -/
theorem eq_2_1
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u f inv_f : Time → R)
  (c : R) (R_scalar : Time → R)
  [log_smooth : LogSmooth metric u f inv_f]
  [flow : RicciFlowEquation1D metric conn f c R_scalar]
  (t : Time) :
  TimeDerivative.partial_t u t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - metric.g (grad metric (u t)) (grad metric (u t)) + c * R_scalar t := by
  have heq : TimeDerivative.partial_t f t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - c * R_scalar t * f t := flow.heat_eq t
  have hdt : TimeDerivative.partial_t f t = - (f t) * TimeDerivative.partial_t u t := log_smooth.dt_eq t
  have hlap : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) = f t * metric.g (grad metric (u t)) (grad metric (u t)) - f t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) := laplacian_eq metric conn u f inv_f t
  rw [hdt, hlap] at heq
  have halg1 : - (f t) * TimeDerivative.partial_t u t = f t * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t) := by
    calc - (f t) * TimeDerivative.partial_t u t
      _ = f t * metric.g (grad metric (u t)) (grad metric (u t)) - f t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t * f t := heq
      _ = f t * metric.g (grad metric (u t)) (grad metric (u t)) - f t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - f t * (c * R_scalar t) := by ring
      _ = f t * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t) := by ring
  have h_mul_inv : inv_f t * (- (f t) * TimeDerivative.partial_t u t) = inv_f t * (f t * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t)) := by rw [halg1]
  have id1 : inv_f t * (- (f t) * TimeDerivative.partial_t u t) = - TimeDerivative.partial_t u t := by
    calc inv_f t * (- (f t) * TimeDerivative.partial_t u t)
      _ = - (inv_f t * f t) * TimeDerivative.partial_t u t := by ring
      _ = - (f t * inv_f t) * TimeDerivative.partial_t u t := by ring
      _ = - (1:R) * TimeDerivative.partial_t u t := by rw [log_smooth.f_eq t]
      _ = - TimeDerivative.partial_t u t := by ring
  have id2 : inv_f t * (f t * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t)) = metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t := by
    calc inv_f t * (f t * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t))
      _ = (inv_f t * f t) * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t) := by ring
      _ = (f t * inv_f t) * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t) := by ring
      _ = 1 * (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t) := by rw [log_smooth.f_eq t]
      _ = metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t := by ring
  rw [id1, id2] at h_mul_inv
  calc TimeDerivative.partial_t u t
    _ = - (- TimeDerivative.partial_t u t) := by ring
    _ = - (metric.g (grad metric (u t)) (grad metric (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - c * R_scalar t) := by rw [h_mul_inv]
    _ = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - metric.g (grad metric (u t)) (grad metric (u t)) + c * R_scalar t := by ring

/-- $\Delta(f+g) = \Delta f + \Delta g$ -/
lemma laplacian_add
  (metric : MetricTensor R V)
  [MetricTraceOperator R V metric]
  [MetricTraceRules R V metric]
  (conn : AffineConnection R V)
  (f g : R) :
  laplacian metric conn (f + g) = laplacian metric conn f + laplacian metric conn g := by
  dsimp [laplacian]
  have hessian_add : Hess conn (f + g) = (fun X Y => Hess conn f X Y + Hess conn g X Y) := by
    funext X Y
    dsimp [Hess]
    have h1 : action Y (f + g) = action Y f + action Y g := DerivationRules.action_add_right Y f g
    rw [h1]
    have h2 : action X (action Y f + action Y g) = action X (action Y f) + action X (action Y g) := DerivationRules.action_add_right X (action Y f) (action Y g)
    rw [h2]
    have h3 : action (conn.nabla X Y) (f + g) = action (conn.nabla X Y) f + action (conn.nabla X Y) g := DerivationRules.action_add_right (conn.nabla X Y) f g
    rw [h3]
    ring
  rw [hessian_add]
  exact MetricTraceRules.trace_add (metric := metric) (fun X Y => Hess conn f X Y) (fun X Y => Hess conn g X Y)

/-- $\Delta(f-g) = \Delta f - \Delta g$ -/
lemma laplacian_sub
  (metric : MetricTensor R V)
  [MetricTraceOperator R V metric]
  [MetricTraceRules R V metric]
  (conn : AffineConnection R V)
  (f g : R) :
  laplacian metric conn (f - g) = laplacian metric conn f - laplacian metric conn g := by
  dsimp [laplacian]
  have action_sub : ∀ (X : V) (f g : R), action X (f - g) = action X f - action X g := by
    intro X f g
    have hz : f - g = f + -g := sub_eq_add_neg f g
    rw [hz]
    have h1 : action X (f + -g) = action X f + action X (-g) := DerivationRules.action_add_right X f (-g)
    rw [h1]
    have hz2 : g + -g = 0 := by abel
    have hz3 : action X (g + -g) = action X g + action X (-g) := DerivationRules.action_add_right X g (-g)
    have hz4 : action X (0:R) = 0 := by
      have h := DerivationRules.action_add_right X (0:R) (0:R)
      rw [add_zero] at h
      calc action X (0:R) = action X (0:R) + action X (0:R) - action X (0:R) := by abel
        _ = action X (0:R) - action X (0:R) := by rw [← h]
        _ = 0 := by abel
    rw [hz2, hz4] at hz3
    have hneg : action X (-g) = - action X g := by
      calc action X (-g) = action X g + action X (-g) - action X g := by abel
        _ = 0 - action X g := by rw [← hz3]
        _ = - action X g := by abel
    rw [hneg]
    abel
  have hessian_sub : Hess conn (f - g) = (fun X Y => Hess conn f X Y - Hess conn g X Y) := by
    funext X Y
    dsimp [Hess]
    have h1 : action Y (f - g) = action Y f - action Y g := action_sub Y f g
    rw [h1]
    have h2 : action X (action Y f - action Y g) = action X (action Y f) - action X (action Y g) := action_sub X (action Y f) (action Y g)
    rw [h2]
    have h3 : action (conn.nabla X Y) (f - g) = action (conn.nabla X Y) f - action (conn.nabla X Y) g := action_sub (conn.nabla X Y) f g
    rw [h3]
    ring
  rw [hessian_sub]
  have h_sub : (fun X Y => Hess conn f X Y - Hess conn g X Y) = ((fun X Y => Hess conn f X Y) + (fun X Y => (-1:R) * Hess conn g X Y)) := by
    funext X Y
    calc Hess conn f X Y - Hess conn g X Y = Hess conn f X Y - 1 * Hess conn g X Y := by ring
      _ = Hess conn f X Y + (-1:R) * Hess conn g X Y := by ring
  rw [h_sub]
  have t1 : MetricTraceOperator.metric_trace metric ((fun X Y => Hess conn f X Y) + (fun X Y => (-1:R) * Hess conn g X Y)) = MetricTraceOperator.metric_trace metric (fun X Y => Hess conn f X Y) + MetricTraceOperator.metric_trace metric (fun X Y => (-1:R) * Hess conn g X Y) := MetricTraceRules.trace_add (metric := metric) (fun X Y => Hess conn f X Y) (fun X Y => (-1:R) * Hess conn g X Y)
  rw [t1]
  have t2 : MetricTraceOperator.metric_trace metric (fun X Y => (-1:R) * Hess conn g X Y) = (-1:R) * MetricTraceOperator.metric_trace metric (fun X Y => Hess conn g X Y) := MetricTraceRules.trace_smul (metric := metric) (-1:R) (fun X Y => Hess conn g X Y)
  rw [t2]
  ring



/-- $\partial_t(\Delta u)$ evolution -/
theorem dt_laplacian_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u f inv_f : Time → R)
  (Rc_form : SmoothBilinearForm R V)
  (c : R) (R_scalar : Time → R)
  [h_const_c : IsSpatialConstant R V c]
  [log_smooth : LogSmooth metric u f inv_f]
  [flow : RicciFlowEquation1D metric conn f c R_scalar]
  [lap_evol : LaplacianEvolution metric conn u Rc_form]
  (t : Time) :
  TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u s)) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) -
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) +
  c * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t) +
  (2:R) * tensorInnerProduct metric Rc_form (hessianForm conn (u t)) := by
  have dt_lap := lap_evol.dt_laplacian t
  have heq := eq_2_1 metric conn u f inv_f c R_scalar t
  rw [dt_lap]
  rw [heq]
  have h1 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - metric.g (grad metric (u t)) (grad metric (u t)) + c * R_scalar t) =
            laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - metric.g (grad metric (u t)) (grad metric (u t))) + laplacian metric.toNonDegenerateMetric.toMetricTensor conn (c * R_scalar t) := laplacian_add metric.toNonDegenerateMetric.toMetricTensor conn _ _
  rw [h1]
  have h2 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - metric.g (grad metric (u t)) (grad metric (u t))) =
            laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) := laplacian_sub metric.toNonDegenerateMetric.toMetricTensor conn _ _
  rw [h2]
  have h3 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (c * R_scalar t) = c * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t) := laplacian_smul metric conn c (R_scalar t)
  rw [h3]

/-! AXIOMIZED FACT: Time inversion calculus for abstract rings.
This axiomatizes the existence of 1/t, its derivative rule ∂_t (1/t) = -1/t^2, and its positivity. -/
class TimeWeight (R : Type) [CommRing R] [PartialOrder R] (Time : Type) [TimeDerivative Time R] where
  inv_t : Time → R
  dt_inv_t : ∀ t, TimeDerivative.partial_t inv_t t = - (inv_t t)^2
  inv_t_nonneg : ∀ t, (0:R) ≤ inv_t t

/-! AXIOMIZED FACT: Single-variable calculus rules for scalar time derivatives. -/
class ScalarTimeDerivRules (R : Type) [CommRing R] (Time : Type) [TimeDerivative Time R] where
  dt_add : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s + g s) t = TimeDerivative.partial_t f t + TimeDerivative.partial_t g t
  dt_sub : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s - g s) t = TimeDerivative.partial_t f t - TimeDerivative.partial_t g t
  dt_smul : ∀ (c : R) (f : Time → R) t, TimeDerivative.partial_t (fun s => c * f s) t = c * TimeDerivative.partial_t f t
  dt_mul : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s * g s) t = TimeDerivative.partial_t f t * g t + f t * TimeDerivative.partial_t g t

/-- $H$ definition in Lemma 2.1 (page 4, bottom) -/
def H_def
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  [time_weight : TimeWeight R Time]
  (α β a b d n : R)
  (u R_scalar : Time → R)
  (t : Time) : R :=
  α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) -
  β * metric.g (grad metric (u t)) (grad metric (u t)) +
  a * R_scalar t -
  b * u t * time_weight.inv_t t -
  d * n * time_weight.inv_t t

/-- Lemma 2.1 evolution equation (page 4, bottom) -/
theorem lemma_2_1_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  (conn : AffineConnection R V)
  [time_weight : TimeWeight R Time]
  [scalar_deriv_rules : ScalarTimeDerivRules R Time]
  (α β a b d n c : R)
  [h_const_c : IsSpatialConstant R V c]
  (u f inv_f R_scalar : Time → R)
  (Rc_form : SmoothBilinearForm R V)
  [log_smooth : LogSmooth metric u f inv_f]
  [flow : RicciFlowEquation1D metric conn f c R_scalar]
  [lap_evol : LaplacianEvolution metric conn u Rc_form]
  [grad_sq_evol : GradientSquaredEvolution metric conn u R_scalar]
  [R_evol : ScalarCurvatureEvolution metric conn Rc_form R_scalar]
  (t : Time) :
  TimeDerivative.partial_t (fun s => H_def metric conn α β a b d n u R_scalar s) t =
  α * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) -
       laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) +
       c * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t) +
       (2:R) * tensorInnerProduct metric Rc_form (hessianForm conn (u t))) -
  β * ((2:R) * Rc conn (grad metric (u t)) (grad metric (u t)) + (2:R) * metric.g (grad metric (u t)) (grad metric (TimeDerivative.partial_t u t))) +
  a * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form) -
  b * (TimeDerivative.partial_t u t * time_weight.inv_t t + u t * (- (time_weight.inv_t t)^2)) -
  d * n * (- (time_weight.inv_t t)^2) := by
  dsimp [H_def]
  rw [scalar_deriv_rules.dt_sub]
  rw [scalar_deriv_rules.dt_sub]
  rw [scalar_deriv_rules.dt_add]
  rw [scalar_deriv_rules.dt_sub]
  rw [scalar_deriv_rules.dt_smul]
  rw [scalar_deriv_rules.dt_smul]
  rw [scalar_deriv_rules.dt_smul]
  rw [scalar_deriv_rules.dt_mul]
  rw [scalar_deriv_rules.dt_smul]
  rw [scalar_deriv_rules.dt_smul]
  rw [time_weight.dt_inv_t t]
  rw [dt_laplacian_evolution metric conn u f inv_f Rc_form c R_scalar t]
  rw [grad_sq_evol.dt_grad_sq t]
  rw [R_evol.dt_R t]
  ring
end CaoHamilton2008

namespace CaoHamilton2008

variable {Time R V : Type}
variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [DerivationRules R V] [TraceOperator R V]
variable [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V]
variable [ActionTimeDerivativeRules Time R V] [Invertible (2:R)]

/-- $|T + aS + bW|^2$ expansion -/
lemma expand_norm_sq_add3
  (metric : MetricDuality R V)
  [TraceLinearityRules R V]
  (T S W : SmoothBilinearForm R V)
  (a b : R) :
  tensorNormSq metric (T + a • S + b • W) =
  tensorNormSq metric T +
  a^2 * tensorNormSq metric S +
  b^2 * tensorNormSq metric W +
  (2:R) * a * tensorInnerProduct metric T S +
  (2:R) * b * tensorInnerProduct metric T W +
  (2:R) * a * b * tensorInnerProduct metric S W := by
  dsimp [tensorNormSq]
  simp only [inner_add_left metric, inner_add_right metric,
             inner_smul_left metric, inner_smul_right metric,
             inner_symm metric S T, inner_symm metric W T, inner_symm metric W S]
  ring

/-- $|A - bB - cC|^2$ expansion -/
lemma expand_norm_sq_sub3
  (metric : MetricDuality R V)
  [TraceLinearityRules R V]
  (A B C : SmoothBilinearForm R V)
  (b c : R) :
  tensorNormSq metric (A - b • B - c • C) =
  tensorNormSq metric A +
  b^2 * tensorNormSq metric B +
  c^2 * tensorNormSq metric C -
  (2:R) * b * tensorInnerProduct metric A B -
  (2:R) * c * tensorInnerProduct metric A C +
  (2:R) * b * c * tensorInnerProduct metric B C := by
  dsimp [tensorNormSq]
  have h1 : A - b • B - c • C = A + (-b) • B + (-c) • C := by
    ext X Y
    change (A - b • B - c • C) X Y = (A + (-b) • B + (-c) • C) X Y
    change A X Y - b * B X Y - c * C X Y = A X Y + (-b) * B X Y + (-c) * C X Y
    ring
  rw [h1]
  simp only [inner_add_left metric, inner_add_right metric,
             inner_smul_left metric, inner_smul_right metric,
             inner_symm metric B A, inner_symm metric C A, inner_symm metric C B]
  ring


/-- Algebraic identity for Lemma 2.1 -/
lemma lemma_2_1_algebraic_identity
  (α β a b d n c L inv_alpha inv_two inv_t half : R)
  (h_inv_alpha : inv_alpha * α = 1)
  (h_inv_two : inv_two * ((2:R) * α - (2:R) * β) = 1)
  (h_half : half * (2:R) = 1)
  (LapLapU Hess_sq Rc_GradU GradU_LapU LapR Rc_Hess GradU_GradU_sq GradU_R Rc_sq LapU GradU_sq U_val R_scal : R) :
  -- LHS
  α * (LapLapU - ((2:R) * Hess_sq + (2:R) * Rc_GradU + (2:R) * GradU_LapU) + c * LapR + (2:R) * Rc_Hess) -
  β * ((2:R) * Rc_GradU + (2:R) * (GradU_LapU - GradU_GradU_sq + c * GradU_R)) +
  a * (LapR + (2:R) * Rc_sq) -
  b * ((LapU - GradU_sq + c * R_scal) * inv_t + U_val * -inv_t^2) -
  d * n * -inv_t^2
  =
  -- RHS
  α * LapLapU -
  β * ((2:R) * Hess_sq + (2:R) * Rc_GradU + (2:R) * GradU_LapU) +
  a * LapR -
  b * inv_t * LapU -
  (2:R) * (α * GradU_LapU - β * GradU_GradU_sq + a * GradU_R - b * inv_t * GradU_sq) +
  (2:R) * (a - β * c) * GradU_R -
  (2:R) * (α - β) * (
    Hess_sq +
    (α * inv_two)^2 * Rc_sq +
    (L * half * inv_t)^2 * n -
    (2:R) * (α * inv_two) * Rc_Hess -
    (2:R) * (L * half * inv_t) * LapU +
    (2:R) * (α * inv_two) * (L * half * inv_t) * R_scal
  ) -
  (2:R) * (α - β) * inv_alpha * L * inv_t * (
    α * LapU - β * GradU_sq + a * R_scal - b * inv_t * U_val - d * n * inv_t
  ) +
  (α * L + a * (2:R) * (α - β) * inv_alpha * L - b * c) * R_scal * inv_t +
  (α - β) * n * L^2 * half * inv_t^2 +
  ((2:R) * a + α^2 * inv_two) * Rc_sq -
  (b + (2:R) * (α - β) * inv_alpha * L * β) * GradU_sq * inv_t -
  (2:R) * α * Rc_GradU +
  (1 - (2:R) * (α - β) * inv_alpha * L) * b * U_val * inv_t^2 +
  (1 - (2:R) * (α - β) * inv_alpha * L) * d * n * inv_t^2 +
  α * c * LapR := by
  have tr1 :
    (α * (LapLapU - ((2:R) * Hess_sq + (2:R) * Rc_GradU + (2:R) * GradU_LapU) + c * LapR + (2:R) * Rc_Hess) -
     β * ((2:R) * Rc_GradU + (2:R) * (GradU_LapU - GradU_GradU_sq + c * GradU_R)) +
     a * (LapR + (2:R) * Rc_sq) -
     b * ((LapU - GradU_sq + c * R_scal) * inv_t + U_val * -inv_t^2) -
     d * n * -inv_t^2) -
    (α * LapLapU -
     β * ((2:R) * Hess_sq + (2:R) * Rc_GradU + (2:R) * GradU_LapU) +
     a * LapR -
     b * inv_t * LapU -
     (2:R) * (α * GradU_LapU - β * GradU_GradU_sq + a * GradU_R - b * inv_t * GradU_sq) +
     (2:R) * (a - β * c) * GradU_R -
     (2:R) * (α - β) * (
       Hess_sq +
       (α * inv_two)^2 * Rc_sq +
       (L * half * inv_t)^2 * n -
       (2:R) * (α * inv_two) * Rc_Hess -
       (2:R) * (L * half * inv_t) * LapU +
       (2:R) * (α * inv_two) * (L * half * inv_t) * R_scal
     ) -
     (2:R) * (α - β) * inv_alpha * L * inv_t * (
       α * LapU - β * GradU_sq + a * R_scal - b * inv_t * U_val - d * n * inv_t
     ) +
     (α * L + a * (2:R) * (α - β) * inv_alpha * L - b * c) * R_scal * inv_t +
     (α - β) * n * L^2 * half * inv_t^2 +
     ((2:R) * a + α^2 * inv_two) * Rc_sq -
     (b + (2:R) * (α - β) * inv_alpha * L * β) * GradU_sq * inv_t -
     (2:R) * α * Rc_GradU +
     (1 - (2:R) * (α - β) * inv_alpha * L) * b * U_val * inv_t^2 +
     (1 - (2:R) * (α - β) * inv_alpha * L) * d * n * inv_t^2 +
     α * c * LapR)
      =
      (2:R) * (α - β) * L * inv_t * LapU * ((inv_alpha * α - 1) - (half * (2:R) - 1)) +
      (α^2 * inv_two * Rc_sq - (2:R) * α * Rc_Hess) * (inv_two * ((2:R) * α - (2:R) * β) - 1) +
      α * L * inv_t * R_scal * (half * (2:R) * (inv_two * ((2:R) * α - (2:R) * β) - 1) + (half * (2:R) - 1)) +
      n * L^2 * inv_t^2 * (α - β) * half * (half * (2:R) - 1)
      := by ring

  have tr2 :
      (2:R) * (α - β) * L * inv_t * LapU * ((inv_alpha * α - 1) - (half * (2:R) - 1)) +
      (α^2 * inv_two * Rc_sq - (2:R) * α * Rc_Hess) * (inv_two * ((2:R) * α - (2:R) * β) - 1) +
      α * L * inv_t * R_scal * (half * (2:R) * (inv_two * ((2:R) * α - (2:R) * β) - 1) + (half * (2:R) - 1)) +
      n * L^2 * inv_t^2 * (α - β) * half * (half * (2:R) - 1) = 0 := by
    rw [h_inv_alpha, h_inv_two, h_half]
    ring

  exact sub_eq_zero.mp (Eq.trans tr1 tr2)

/-- Lemma 2.1 final form (page 5, middle) -/
theorem lemma_2_1_final
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor] [TorsionFree conn]
  [time_weight : TimeWeight R Time]
  [scalar_deriv_rules : ScalarTimeDerivRules R Time]
  [bochner_rules : BochnerTraceRules metric conn]
  [Invertible (2:R)]
    (α β a b d n c L : R)
  [h_const_alpha : IsSpatialConstant R V α]
  [h_const_beta : IsSpatialConstant R V β]
  [h_const_a : IsSpatialConstant R V a]
  [h_const_b : IsSpatialConstant R V b]
  [h_const_d : IsSpatialConstant R V d]
  [h_const_n : IsSpatialConstant R V n]
  [h_const_c : IsSpatialConstant R V c]
  [h_const_inv_t : ∀ t, IsSpatialConstant R V (time_weight.inv_t t)]
  (inv_alpha inv_two_alpha_minus_beta : R) -- Rigorous inverses for CommRing
  (h_inv_alpha : inv_alpha * α = 1)
  (h_inv_two : inv_two_alpha_minus_beta * ((2:R) * (α - β)) = 1)
  (u f inv_f R_scalar : Time → R)
  (Rc_form : SmoothBilinearForm R V)
  (h_trace_Rc : ∀ t, tensorInnerProduct metric Rc_form (metricToForm metric.toMetricTensor) = R_scalar t)
  (h_trace_Hess : ∀ t, tensorInnerProduct metric (hessianForm conn (u t)) (metricToForm metric.toMetricTensor) = laplacian metric.toMetricTensor conn (u t))
  (h_trace_g : tensorNormSq metric (metricToForm metric.toMetricTensor) = n)
  [log_smooth : LogSmooth metric u f inv_f]
  [flow : RicciFlowEquation1D metric conn f c R_scalar]
  [lap_evol : LaplacianEvolution metric conn u Rc_form]
  [grad_sq_evol : GradientSquaredEvolution metric conn u R_scalar]
  [R_evol : ScalarCurvatureEvolution metric conn Rc_form R_scalar]
  (t : Time) :
  TimeDerivative.partial_t (fun s => H_def metric conn α β a b d n u R_scalar s) t =
  -- ΔH
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (H_def metric conn α β a b d n u R_scalar t)
  -- - 2∇H·∇u
  - (2:R) * metric.g (grad metric (H_def metric conn α β a b d n u R_scalar t)) (grad metric (u t))
  -- + 2(a - βc)∇R·∇u
  + (2:R) * (a - β * c) * metric.g (grad metric (R_scalar t)) (grad metric (u t))
  -- - 2(α-β)|u_{ij} - (α/(2(α-β)))R_{ij} - (λ/2t)g_{ij}|^2
  - (2:R) * (α - β) * tensorNormSq metric (
      hessianForm conn (u t)
      - (α * inv_two_alpha_minus_beta) • Rc_form
      - (L * ⅟(2:R) * time_weight.inv_t t) • metricToForm metric.toNonDegenerateMetric.toMetricTensor
    )
  -- - (2(α-β)λ / αt) H
  - (2:R) * (α - β) * inv_alpha * L * time_weight.inv_t t * H_def metric conn α β a b d n u R_scalar t
  -- + (αλ + a(2(α-β)/α)λ - bc)(R/t)
  + (α * L + a * (2:R) * (α - β) * inv_alpha * L - b * c) * R_scalar t * time_weight.inv_t t
  -- + (α-β)(nλ^2 / 2t^2)
  + (α - β) * n * L^2 * ⅟(2:R) * (time_weight.inv_t t)^2
  -- + (2a + α^2 / (2(α-β)))|Rc|^2
  + ((2:R) * a + α^2 * inv_two_alpha_minus_beta) * tensorNormSq metric Rc_form
  -- - (b + (2(α-β)/α)λβ) (|∇u|^2 / t)
  - (b + (2:R) * (α - β) * inv_alpha * L * β) * metric.g (grad metric (u t)) (grad metric (u t)) * time_weight.inv_t t
  -- - 2α R_{ij}u_i u_j
  - (2:R) * α * Rc conn (grad metric (u t)) (grad metric (u t))
  -- + (1 - (2(α-β)/α)λ) b(u / t^2)
  + (1 - (2:R) * (α - β) * inv_alpha * L) * b * u t * (time_weight.inv_t t)^2
  -- + (1 - (2(α-β)/α)λ) d(n / t^2)
  + (1 - (2:R) * (α - β) * inv_alpha * L) * d * n * (time_weight.inv_t t)^2
  -- + αcΔR
  + α * c * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t)
  := by
  rw [lemma_2_1_evolution metric conn α β a b d n c u f inv_f R_scalar Rc_form t]
  have h_H_def : H_def metric conn α β a b d n u R_scalar t =
    α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) -
    β * metric.g (grad metric (u t)) (grad metric (u t)) +
    a * R_scalar t -
    b * u t * time_weight.inv_t t -
    d * n * time_weight.inv_t t := rfl
  rw [h_H_def]

  -- Expand the Laplacian
  have l1 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t)) + a * R_scalar t - b * u t * time_weight.inv_t t - d * n * time_weight.inv_t t) =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t)) + a * R_scalar t - b * u t * time_weight.inv_t t) -
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (d * n * time_weight.inv_t t) := laplacian_sub _ _ _ _
  rw [l1]
  have l2 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t)) + a * R_scalar t - b * u t * time_weight.inv_t t) =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t)) + a * R_scalar t) -
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (b * u t * time_weight.inv_t t) := laplacian_sub _ _ _ _
  rw [l2]
  have l3 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t)) + a * R_scalar t) =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t))) +
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (a * R_scalar t) := laplacian_add _ _ _ _
  rw [l3]
  have l4 : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - β * metric.g (grad metric (u t)) (grad metric (u t))) =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) -
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (β * metric.g (grad metric (u t)) (grad metric (u t))) := laplacian_sub _ _ _ _
  rw [l4]

  rw [laplacian_smul metric conn α (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))]
  rw [laplacian_smul metric conn a (R_scalar t)]
  rw [laplacian_smul metric conn β (metric.g (grad metric (u t)) (grad metric (u t)))]

  have hz1 : b * u t * time_weight.inv_t t = b * (time_weight.inv_t t * u t) := by ring
  rw [hz1]
  rw [laplacian_smul metric conn b (time_weight.inv_t t * u t)]
  rw [laplacian_smul metric conn (time_weight.inv_t t) (u t)]

  have hz2 : d * n * time_weight.inv_t t = d * (n * time_weight.inv_t t) := by ring
  rw [hz2]
  rw [laplacian_smul metric conn d (n * time_weight.inv_t t)]
  rw [laplacian_smul metric conn n (time_weight.inv_t t)]
  rw [laplacian_zero metric conn (time_weight.inv_t t)]
  simp only [mul_zero, sub_zero]

  -- Just use eq_2_1 directly
  rw [eq_2_1 metric conn u f inv_f c R_scalar t]

  simp only [grad_sub metric, grad_add metric]

  rw [grad_smul metric α (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))]
  rw [grad_smul metric β (metric.g (grad metric (u t)) (grad metric (u t)))]
  rw [grad_smul metric a (R_scalar t)]
  rw [grad_smul metric c (R_scalar t)]

  rw [grad_smul metric b (time_weight.inv_t t * u t)]
  rw [grad_smul metric (time_weight.inv_t t) (u t)]

  rw [grad_smul metric d (n * time_weight.inv_t t)]
  rw [grad_smul metric n (time_weight.inv_t t)]
  rw [grad_zero metric (time_weight.inv_t t)]
  simp only [smul_zero, sub_zero]

  -- Distribute tensor inner product
  have g_eval : metric.g (α • grad metric (laplacian metric.toMetricTensor conn (u t)) - β • grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + a • grad metric (R_scalar t) - b • time_weight.inv_t t • grad metric (u t)) (grad metric (u t)) =
    α * metric.g (grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)) -
    β * metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) +
    a * metric.g (grad metric (R_scalar t)) (grad metric (u t)) -
    b * time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t)) := by
    calc metric.g (α • grad metric (laplacian metric.toMetricTensor conn (u t)) - β • grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + a • grad metric (R_scalar t) - b • time_weight.inv_t t • grad metric (u t)) (grad metric (u t))
      = metric.g (α • grad metric (laplacian metric.toMetricTensor conn (u t)) - β • grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + a • grad metric (R_scalar t)) (grad metric (u t)) - metric.g (b • time_weight.inv_t t • grad metric (u t)) (grad metric (u t)) := by rw [metric_sub_left _ _ _ _]
      _ = metric.g (α • grad metric (laplacian metric.toMetricTensor conn (u t)) - β • grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + metric.g (a • grad metric (R_scalar t)) (grad metric (u t)) - metric.g (b • time_weight.inv_t t • grad metric (u t)) (grad metric (u t)) := by rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
      _ = metric.g (α • grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)) - metric.g (β • grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + metric.g (a • grad metric (R_scalar t)) (grad metric (u t)) - metric.g (b • time_weight.inv_t t • grad metric (u t)) (grad metric (u t)) := by rw [metric_sub_left _ _ _ _]
      _ = α * metric.g (grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)) - β * metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + a * metric.g (grad metric (R_scalar t)) (grad metric (u t)) - b * time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t)) := by
        rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
        rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
        rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
        have hs : metric.g (b • time_weight.inv_t t • grad metric (u t)) (grad metric (u t)) = b * time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t)) := by
          rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left, metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
          ring
        rw [hs]
  rw [g_eval]

  -- Second metric distribution for eq_2_1 term
  have g2 : metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t)) - grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + c • grad metric (R_scalar t)) =
    metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t))) -
    metric.g (grad metric (u t)) (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) +
    c * metric.g (grad metric (u t)) (grad metric (R_scalar t)) := by
    have symm1 : metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t)) - grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + c • grad metric (R_scalar t)) = metric.g (grad metric (laplacian metric.toMetricTensor conn (u t)) - grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + c • grad metric (R_scalar t)) (grad metric (u t)) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
    rw [symm1]
    calc metric.g (grad metric (laplacian metric.toMetricTensor conn (u t)) - grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + c • grad metric (R_scalar t)) (grad metric (u t))
      = metric.g (grad metric (laplacian metric.toMetricTensor conn (u t)) - grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + metric.g (c • grad metric (R_scalar t)) (grad metric (u t)) := by rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
      _ = metric.g (grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)) - metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + metric.g (c • grad metric (R_scalar t)) (grad metric (u t)) := by rw [metric_sub_left _ _ _ _]
      _ = metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t))) - metric.g (grad metric (u t)) (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) + metric.g (c • grad metric (R_scalar t)) (grad metric (u t)) := by
        have s1 : metric.g (grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)) = metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t))) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
        have s2 : metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) = metric.g (grad metric (u t)) (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
        rw [s1, s2]
      _ = metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t))) - metric.g (grad metric (u t)) (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) + c * metric.g (grad metric (u t)) (grad metric (R_scalar t)) := by
        rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
        have s3 : metric.g (grad metric (R_scalar t)) (grad metric (u t)) = metric.g (grad metric (u t)) (grad metric (R_scalar t)) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
        rw [s3]

  -- Align symmetry
  have g_symm1 : metric.g (grad metric (u t)) (grad metric (laplacian metric.toMetricTensor conn (u t))) = metric.g (grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)) := metric.toMetricTensor.symm _ _
  have g_symm2 : metric.g (grad metric (u t)) (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) = metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) := metric.toMetricTensor.symm _ _
  have g_symm3 : metric.g (grad metric (u t)) (grad metric (R_scalar t)) = metric.g (grad metric (R_scalar t)) (grad metric (u t)) := metric.toMetricTensor.symm _ _

  simp only [bochner_identity]

  simp only [g2, g_symm1, g_symm2, g_symm3]

  -- Expand the tensor norm sq
  rw [expand_norm_sq_sub3 metric (hessianForm conn (u t)) Rc_form (metricToForm metric.toNonDegenerateMetric.toMetricTensor) (α * inv_two_alpha_minus_beta) (L * ⅟(2:R) * time_weight.inv_t t)]

  have t_symm : tensorInnerProduct metric (hessianForm conn (u t)) Rc_form = tensorInnerProduct metric Rc_form (hessianForm conn (u t)) := inner_symm metric _ _
  rw [t_symm]

  -- Apply trace identities
  rw [h_trace_Rc t]
  rw [h_trace_Hess t]
  rw [h_trace_g]

  -- Apply fractional inverse scalar normalization
  have c_inv_1 : inv_alpha * α = 1 := h_inv_alpha
  have c_inv_2 : α * inv_alpha = 1 := mul_comm inv_alpha α ▸ h_inv_alpha
  have c_inv_3 : inv_two_alpha_minus_beta * ((2:R) * (α - β)) = 1 := h_inv_two
  have c_inv_4 : ((2:R) * (α - β)) * inv_two_alpha_minus_beta = 1 := mul_comm inv_two_alpha_minus_beta ((2:R) * (α - β)) ▸ h_inv_two
  have c_inv_5 : inv_two_alpha_minus_beta * ((2:R) * α - (2:R) * β) = 1 := by
    calc inv_two_alpha_minus_beta * ((2:R) * α - (2:R) * β) = inv_two_alpha_minus_beta * ((2:R) * (α - β)) := by ring
      _ = 1 := h_inv_two

  have h_alg := lemma_2_1_algebraic_identity α β a b d n c L inv_alpha inv_two_alpha_minus_beta (time_weight.inv_t t) (⅟(2:R))
    h_inv_alpha c_inv_5 (invOf_mul_self (2:R))
    (laplacian metric.toMetricTensor conn (laplacian metric.toMetricTensor conn (u t)))
    (tensorNormSq metric (hessianForm conn (u t)))
    (Rc conn (grad metric (u t)) (grad metric (u t)))
    (metric.g (grad metric (laplacian metric.toMetricTensor conn (u t))) (grad metric (u t)))
    (laplacian metric.toMetricTensor conn (R_scalar t))
    (tensorInnerProduct metric Rc_form (hessianForm conn (u t)))
    (metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)))
    (metric.g (grad metric (R_scalar t)) (grad metric (u t)))
    (tensorNormSq metric Rc_form)
    (laplacian metric.toMetricTensor conn (u t))
    (metric.g (grad metric (u t)) (grad metric (u t)))
    (u t)
    (R_scalar t)

  have h_assoc1 : b * (time_weight.inv_t t * laplacian metric.toMetricTensor conn (u t)) = b * time_weight.inv_t t * laplacian metric.toMetricTensor conn (u t) := by ring
  rw [h_assoc1]

  have h_assoc2 : b * (time_weight.inv_t t * u t) = b * time_weight.inv_t t * u t := by ring
  rw [h_assoc2]

  have h_assoc3 : d * (n * time_weight.inv_t t) = d * n * time_weight.inv_t t := by ring
  rw [h_assoc3]

  exact h_alg

/-- $H$ definition for Theorem 1.1 (page 3, top) -/
def H_thm1_1
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  [time_weight : TimeWeight R Time]
  (n : R) (u R_scalar : Time → R) (t : Time) : R :=
  (2:R) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) -
  metric.g (grad metric (u t)) (grad metric (u t)) -
  (3:R) * R_scalar t -
  (2:R) * n * time_weight.inv_t t

/-- $H$ definition equivalence -/
lemma H_thm1_1_eq_H_def
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  [time_weight : TimeWeight R Time]
  (n : R) (u R_scalar : Time → R) (t : Time) :
  H_thm1_1 metric conn n u R_scalar t =
  H_def metric conn (2:R) (1:R) (-3:R) (0:R) (2:R) n u R_scalar t := by
  dsimp [H_thm1_1, H_def]
  ring

/-- Simplification of tensor constants -/
lemma tensor_term_simplify
  (metric : MetricDuality R V)
  (conn : AffineConnection R V)
  [time_weight : TimeWeight R Time]
  [Invertible (2:R)]
  (u : Time → R)
  (Rc_form : SmoothBilinearForm R V)
  (t : Time) :
  hessianForm conn (u t) - ((2:R) * ⅟(2:R)) • Rc_form - ((2:R) * ⅟(2:R) * time_weight.inv_t t) • metricToForm metric.toNonDegenerateMetric.toMetricTensor =
  hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toNonDegenerateMetric.toMetricTensor := by
  have h1 : (2:R) * ⅟(2:R) = 1 := mul_invOf_self (2:R)
  have h2 : (1:R) • Rc_form = Rc_form := by ext X Y; exact one_smul R (Rc_form X Y)
  rw [h1, h2]
  simp only [one_mul]

/-- Corollary 2.2 evolution equation (page 6, top) -/
theorem corollary_2_2_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor] [TorsionFree conn]
  [time_weight : TimeWeight R Time]
  [scalar_deriv_rules : ScalarTimeDerivRules R Time]
  [bochner_rules : BochnerTraceRules metric conn]
  [Invertible (2:R)]
    (n : R)
  [h_const_n : IsSpatialConstant R V n]
  [h_const_inv_t : ∀ t, IsSpatialConstant R V (time_weight.inv_t t)]
  [h_const_two : IsSpatialConstant R V (2:R)]
  [h_const_one : IsSpatialConstant R V (1:R)]
  [h_const_m3 : IsSpatialConstant R V (-3:R)]
  [h_const_0 : IsSpatialConstant R V (0:R)]
  [h_const_m1 : IsSpatialConstant R V (-1:R)]
  (u f inv_f R_scalar : Time → R)
  (Rc_form : SmoothBilinearForm R V)
  (h_trace_Rc : ∀ t, tensorInnerProduct metric Rc_form (metricToForm metric.toMetricTensor) = R_scalar t)
  (h_trace_Hess : ∀ t, tensorInnerProduct metric (hessianForm conn (u t)) (metricToForm metric.toMetricTensor) = laplacian metric.toMetricTensor conn (u t))
  (h_trace_g : tensorNormSq metric (metricToForm metric.toMetricTensor) = n)
  [log_smooth : LogSmooth metric u f inv_f]
  [flow : RicciFlowEquation1D metric conn f (-1:R) R_scalar]
  [lap_evol : LaplacianEvolution metric conn u Rc_form]
  [grad_sq_evol : GradientSquaredEvolution metric conn u R_scalar]
  [R_evol : ScalarCurvatureEvolution metric conn Rc_form R_scalar]
  (t : Time) :
  TimeDerivative.partial_t (fun s => H_thm1_1 metric conn n u R_scalar s) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t)
  - (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t))
  - (2:R) * tensorNormSq metric (
      hessianForm conn (u t)
      - Rc_form
      - (time_weight.inv_t t) • metricToForm metric.toNonDegenerateMetric.toMetricTensor
    )
  - (2:R) * time_weight.inv_t t * H_thm1_1 metric conn n u R_scalar t
  - (2:R) * time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))
  - (2:R) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t)
  - (4:R) * tensorNormSq metric Rc_form
  - (2:R) * R_scalar t * time_weight.inv_t t
  - (4:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t))
  - (4:R) * Rc conn (grad metric (u t)) (grad metric (u t))
  := by
  have h_eq : (fun s => H_thm1_1 metric conn n u R_scalar s) = (fun s => H_def metric conn (2:R) (1:R) (-3:R) (0:R) (2:R) n u R_scalar s) := by
    funext s
    exact H_thm1_1_eq_H_def metric conn n u R_scalar s
  rw [h_eq]
  have h_inv_alpha : ⅟(2:R) * (2:R) = 1 := invOf_mul_self (2:R)
  have h_inv_two : ⅟(2:R) * ((2:R) * ((2:R) - (1:R))) = 1 := by
    calc ⅟(2:R) * ((2:R) * ((2:R) - (1:R))) = ⅟(2:R) * ((2:R) * (1:R)) := by ring
      _ = ⅟(2:R) * (2:R) := by ring
      _ = 1 := invOf_mul_self (2:R)
  rw [lemma_2_1_final metric conn (2:R) (1:R) (-3:R) (0:R) (2:R) n (-1:R) (2:R) (⅟(2:R)) (⅟(2:R)) h_inv_alpha h_inv_two u f inv_f R_scalar Rc_form h_trace_Rc h_trace_Hess h_trace_g t]
  have h_H_def_rev : ∀ s, H_def metric conn (2:R) (1:R) (-3:R) (0:R) (2:R) n u R_scalar s = H_thm1_1 metric conn n u R_scalar s := fun s => (H_thm1_1_eq_H_def metric conn n u R_scalar s).symm
  rw [h_H_def_rev t]
  rw [tensor_term_simplify metric conn u Rc_form t]

  have h_inv1 : ⅟(2:R) * (2:R) = 1 := invOf_mul_self (2:R)
  have h_inv2 : (2:R) * ⅟(2:R) = 1 := mul_invOf_self (2:R)

  calc laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) +
      (2:R) * (- (3:R) - (1:R) * (- (1:R))) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) -
      (2:R) * ((2:R) - (1:R)) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - TimeWeight.inv_t t • metricToForm metric.toMetricTensor) -
      (2:R) * ((2:R) - (1:R)) * ⅟(2:R) * (2:R) * TimeWeight.inv_t t * H_thm1_1 metric conn n u R_scalar t +
      ((2:R) * (2:R) + (- (3:R)) * (2:R) * ((2:R) - (1:R)) * ⅟(2:R) * (2:R) - (0:R) * (- (1:R))) * R_scalar t * TimeWeight.inv_t t +
      ((2:R) - (1:R)) * n * (2:R)^2 * ⅟(2:R) * (TimeWeight.inv_t t)^2 +
      ((2:R) * (- (3:R)) + (2:R)^2 * ⅟(2:R)) * tensorNormSq metric Rc_form -
      ((0:R) + (2:R) * ((2:R) - (1:R)) * ⅟(2:R) * (2:R) * (1:R)) * metric.g (grad metric (u t)) (grad metric (u t)) * TimeWeight.inv_t t -
      (2:R) * (2:R) * Rc conn (grad metric (u t)) (grad metric (u t)) +
      (1 - (2:R) * ((2:R) - (1:R)) * ⅟(2:R) * (2:R)) * (0:R) * u t * (TimeWeight.inv_t t)^2 +
      (1 - (2:R) * ((2:R) - (1:R)) * ⅟(2:R) * (2:R)) * (2:R) * n * (TimeWeight.inv_t t)^2 +
      (2:R) * (- (1:R)) * laplacian metric.toMetricTensor conn (R_scalar t)
    = laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) + (- (4:R)) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) -
      (2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - TimeWeight.inv_t t • metricToForm metric.toMetricTensor) -
      (2:R) * (⅟(2:R) * (2:R)) * TimeWeight.inv_t t * H_thm1_1 metric conn n u R_scalar t +
      ((4:R) - (6:R) * (⅟(2:R) * (2:R))) * R_scalar t * TimeWeight.inv_t t +
      n * (2:R) * ((2:R) * ⅟(2:R)) * (TimeWeight.inv_t t)^2 +
      (- (6:R) + (2:R) * ((2:R) * ⅟(2:R))) * tensorNormSq metric Rc_form -
      ((2:R) * (⅟(2:R) * (2:R))) * metric.g (grad metric (u t)) (grad metric (u t)) * TimeWeight.inv_t t -
      (4:R) * Rc conn (grad metric (u t)) (grad metric (u t)) +
      (1 - (2:R) * (⅟(2:R) * (2:R))) * (0:R) * H_thm1_1 metric conn n u R_scalar t * (TimeWeight.inv_t t)^2 +
      (1 - (2:R) * (⅟(2:R) * (2:R))) * (2:R) * n * (TimeWeight.inv_t t)^2 +
      (- (2:R)) * laplacian metric.toMetricTensor conn (R_scalar t) := by ring
    _ = laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) + (- (4:R)) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) -
      (2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - TimeWeight.inv_t t • metricToForm metric.toMetricTensor) -
      (2:R) * 1 * TimeWeight.inv_t t * H_thm1_1 metric conn n u R_scalar t +
      ((4:R) - (6:R) * 1) * R_scalar t * TimeWeight.inv_t t +
      n * (2:R) * 1 * (TimeWeight.inv_t t)^2 +
      (- (6:R) + (2:R) * 1) * tensorNormSq metric Rc_form -
      ((2:R) * 1) * metric.g (grad metric (u t)) (grad metric (u t)) * TimeWeight.inv_t t -
      (4:R) * Rc conn (grad metric (u t)) (grad metric (u t)) +
      (1 - (2:R) * 1) * (0:R) * H_thm1_1 metric conn n u R_scalar t * (TimeWeight.inv_t t)^2 +
      (1 - (2:R) * 1) * (2:R) * n * (TimeWeight.inv_t t)^2 +
      (- (2:R)) * laplacian metric.toMetricTensor conn (R_scalar t) := by rw [h_inv1, h_inv2]
    _ = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) -
      (2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - TimeWeight.inv_t t • metricToForm metric.toNonDegenerateMetric.toMetricTensor) -
      (2:R) * TimeWeight.inv_t t * H_thm1_1 metric conn n u R_scalar t -
      (2:R) * TimeWeight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t)) -
      (2:R) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (R_scalar t) -
      (4:R) * tensorNormSq metric Rc_form -
      (2:R) * R_scalar t * TimeWeight.inv_t t -
      (4:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) -
      (4:R) * Rc conn (grad metric (u t)) (grad metric (u t)) := by ring

/-! AXIOMIZED FACT: Non-negativity of squared norms in Riemannian geometry. -/
class NormSquaredNonneg (metric : MetricDuality R V) where
  tensor_sq_nonneg : ∀ (T : SmoothBilinearForm R V), (0:R) ≤ tensorNormSq metric T
  grad_sq_nonneg : ∀ (f : R), (0:R) ≤ metric.g (grad metric f) (grad metric f)

/-! AXIOMIZED FACT: Hamilton's Trace Harnack Inequality for Ricci Flow.
States that ∂_t R + R/t + 2∇R·∇u + 2Rc(∇u, ∇u) ≥ 0 for weakly positive curvature operator. -/
class TraceHarnackInequality [time_weight : TimeWeight R Time]
  (metric : MetricDuality R V) (conn : AffineConnection R V)
  (u R_scalar : Time → R) where
  trace_harnack : ∀ t,
    (0:R) ≤ TimeDerivative.partial_t R_scalar t +
            R_scalar t * time_weight.inv_t t +
            (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) +
            (2:R) * Rc conn (grad metric (u t)) (grad metric (u t))

/-! AXIOMIZED FACT: Parabolic Maximum Principle.
If a function H satisfies ∂_t H ≤ ΔH - 2∇H·∇u - (2/t)H (with H < 0 for small t), then H ≤ 0 globally. -/
class ParabolicMaximumPrinciple [time_weight : TimeWeight R Time]
  (metric : MetricDuality R V) [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) (u R_scalar : Time → R) (n : R) where
  max_principle : ∀ t,
    (TimeDerivative.partial_t (fun s => H_thm1_1 metric conn n u R_scalar s) t ≤
     laplacian metric.toNonDegenerateMetric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
     (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) -
     (2:R) * time_weight.inv_t t * H_thm1_1 metric conn n u R_scalar t) →
    H_thm1_1 metric conn n u R_scalar t ≤ (0:R)


/-- Theorem 1.1 (page 2-3) -/
theorem theorem_1_1
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor] [TorsionFree conn]
  [time_weight : TimeWeight R Time]
  [scalar_deriv_rules : ScalarTimeDerivRules R Time]
  [bochner_rules : BochnerTraceRules metric conn]
  [Invertible (2:R)]
    [norm_nonneg : NormSquaredNonneg metric]
  (n : R)
  [h_const_n : IsSpatialConstant R V n]
  [h_const_inv_t : ∀ t, IsSpatialConstant R V (time_weight.inv_t t)]
  [h_const_two : IsSpatialConstant R V (2:R)]
  [h_const_one : IsSpatialConstant R V (1:R)]
  [h_const_m3 : IsSpatialConstant R V (-3:R)]
  [h_const_0 : IsSpatialConstant R V (0:R)]
  [h_const_m1 : IsSpatialConstant R V (-1:R)]
  (u f inv_f R_scalar : Time → R)
  (Rc_form : SmoothBilinearForm R V)
  [trace_harnack_ineq : TraceHarnackInequality metric conn u R_scalar]
  [max_principle_axiom : ParabolicMaximumPrinciple metric conn u R_scalar n]
  (h_trace_Rc : ∀ t, tensorInnerProduct metric Rc_form (metricToForm metric.toMetricTensor) = R_scalar t)
  (h_trace_Hess : ∀ t, tensorInnerProduct metric (hessianForm conn (u t)) (metricToForm metric.toMetricTensor) = laplacian metric.toMetricTensor conn (u t))
  (h_trace_g : tensorNormSq metric (metricToForm metric.toMetricTensor) = n)
  [log_smooth : LogSmooth metric u f inv_f]
  [flow : RicciFlowEquation1D metric conn f (-1:R) R_scalar]
  [lap_evol : LaplacianEvolution metric conn u Rc_form]
  [grad_sq_evol : GradientSquaredEvolution metric conn u R_scalar]
  [R_evol : ScalarCurvatureEvolution metric conn Rc_form R_scalar]
  (t : Time) :
  H_thm1_1 metric conn n u R_scalar t ≤ (0:R) := by
  apply max_principle_axiom.max_principle t
  have eq1 := corollary_2_2_evolution metric conn n u f inv_f R_scalar Rc_form h_trace_Rc h_trace_Hess h_trace_g t
  have h_norm := norm_nonneg.tensor_sq_nonneg (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toNonDegenerateMetric.toMetricTensor)
  have h_grad := norm_nonneg.grad_sq_nonneg (u t)
  have h_harnack := trace_harnack_ineq.trace_harnack t
  have h_R_dt := R_evol.dt_R t
  rw [h_R_dt] at h_harnack
  have h_Rc_sq : tensorNormSq metric Rc_form = tensorInnerProduct metric Rc_form Rc_form := rfl
  rw [h_Rc_sq] at eq1
  have h_inv_t := time_weight.inv_t_nonneg t
  have h_grad_sq := norm_nonneg.grad_sq_nonneg (u t)
  have h_dt_R_sub := sub_eq_zero.mp (sub_eq_zero_of_eq h_R_dt.symm)

  -- Isolate the needed terms for the difference
  have h_inv_grad : (0:R) ≤ time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t)) :=
    mul_nonneg h_inv_t h_grad_sq

  have h_sum_nonneg : (0:R) ≤
    (2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) +
    (2:R) * (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) +
    (2:R) * (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t))) := by
    have h1 : (0:R) ≤ (2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) := by
      calc (0:R) ≤ tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) + tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) := add_nonneg h_norm h_norm
        _ = (2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) := by ring
    have h2 : (0:R) ≤ (2:R) * (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) := by
      calc (0:R) ≤ (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) + (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) := add_nonneg h_inv_grad h_inv_grad
        _ = (2:R) * (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) := by ring
    have h3 : (0:R) ≤ (2:R) * (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t))) := by
      calc (0:R) ≤ (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t))) + (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t))) := add_nonneg h_harnack h_harnack
        _ = (2:R) * (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t))) := by ring
    exact add_nonneg (add_nonneg h1 h2) h3

  have h_alg : laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
                      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) -
                    (2:R) *
                      tensorNormSq metric
                        (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) -
                  (2:R) * time_weight.inv_t t * H_thm1_1 metric conn n u R_scalar t -
                (2:R) * time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t)) -
              (2:R) * laplacian metric.toMetricTensor conn (R_scalar t) -
            (4:R) * tensorInnerProduct metric Rc_form Rc_form -
          (2:R) * R_scalar t * time_weight.inv_t t -
        (4:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) -
      (4:R) * Rc conn (grad metric (u t)) (grad metric (u t)) =
      (laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) -
      (2:R) * time_weight.inv_t t * H_thm1_1 metric conn n u R_scalar t) -
      ((2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) +
      (2:R) * (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) +
      (2:R) * (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t)))) := by ring

  rw [h_alg] at eq1
  calc TimeDerivative.partial_t (fun s => H_thm1_1 metric conn n u R_scalar s) t
    _ = (laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) -
      (2:R) * time_weight.inv_t t * H_thm1_1 metric conn n u R_scalar t) -
      ((2:R) * tensorNormSq metric (hessianForm conn (u t) - Rc_form - (time_weight.inv_t t) • metricToForm metric.toMetricTensor) +
      (2:R) * (time_weight.inv_t t * metric.g (grad metric (u t)) (grad metric (u t))) +
      (2:R) * (laplacian metric.toMetricTensor conn (R_scalar t) + (2:R) * tensorInnerProduct metric Rc_form Rc_form + R_scalar t * time_weight.inv_t t + (2:R) * metric.g (grad metric (R_scalar t)) (grad metric (u t)) + (2:R) * Rc conn (grad metric (u t)) (grad metric (u t)))) := eq1
    _ ≤ laplacian metric.toMetricTensor conn (H_thm1_1 metric conn n u R_scalar t) -
      (2:R) * metric.g (grad metric (H_thm1_1 metric conn n u R_scalar t)) (grad metric (u t)) -
      (2:R) * time_weight.inv_t t * H_thm1_1 metric conn n u R_scalar t := sub_le_self _ h_sum_nonneg

end CaoHamilton2008

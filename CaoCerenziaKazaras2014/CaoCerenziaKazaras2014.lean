import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Operators.Bochner
import DifferentialGeometry.Flows.RicciFlow
import DifferentialGeometry.Analysis.TraceRankOne
import DifferentialGeometry.Analysis.TensorInnerProduct
import DifferentialGeometry.Operators.CovariantDerivative
import DifferentialGeometry.Operators.SpatialConstant
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

namespace CaoCerenziaKazaras2014

variable {Time R V : Type}
variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [DerivationRules R V] [TraceOperator R V]
variable [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V]
variable [ActionTimeDerivativeRules Time R V] [Invertible (2:R)]

class RicciFlat (conn : AffineConnection R V) : Prop where
  rc_zero : ∀ X Y, Rc conn X Y = 0

theorem flat_bochner_identity
  [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor] [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor] [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  [ricci_flat : RicciFlat conn]
  (f : R) :
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric f) (grad metric f)) =
  (2:R) * metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn f)) +
  (2:R) * tensorNormSq metric (hessianForm conn f) := by
  have h := bochner_identity metric conn f
  have h_rc : Rc conn (grad metric f) (grad metric f) = 0 := ricci_flat.rc_zero _ _
  rw [h_rc] at h
  calc laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric f) (grad metric f))
    = (2:R) * tensorNormSq metric (hessianForm conn f) + (2:R) * 0 + (2:R) * metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn f)) := h
    _ = (2:R) * metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn f)) + (2:R) * tensorNormSq metric (hessianForm conn f) := by ring


class ESEExponentialSmooth
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R) (p : R) where
  dt_eq : ∀ t, TimeDerivative.partial_t E t = (p - 1) * E t * TimeDerivative.partial_t u t
  grad_eq : ∀ t, grad metric (E t) = ((p - 1) * E t) • grad metric (u t)
  laplacian_eq : ∀ t,
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (E t) =
      (p - 1) * E t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
      (p - 1)^2 * E t * metric.g (grad metric (u t)) (grad metric (u t))


/--
Endangered Species Equation (ESE) under logarithmic transformation `u = log f`.
Equation: `u_t = Δu + |∇u|^2 + e^{u(p-1)}`
We represent `e^{u(p-1)}` as an abstract smooth function `E t`.
-/
class EndangeredSpeciesEquation
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R) where
  eq : ∀ t, TimeDerivative.partial_t u t =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
    metric.g (grad metric (u t)) (grad metric (u t)) +
    E t

class StaticMetricTimeRules
  (Time : Type)
  [TimeDerivative Time R]
  [TimeDerivative Time V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) where
  dt_laplacian : ∀ (f : Time → R) t,
    TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (TimeDerivative.partial_t f t)
  dt_grad : ∀ (f : Time → R) t,
    TimeDerivative.partial_t (fun s => grad metric (f s)) t = grad metric (TimeDerivative.partial_t f t)
  dt_metric_g : ∀ (X : Time → V) t,
    TimeDerivative.partial_t (fun s => metric.g (X s) (X s)) t =
    (2:R) * metric.g (X t) (TimeDerivative.partial_t X t)

/--
Harnack Quantity `H` from Cao-Cerenzia-Kazaras (2014) Lemma 2.1.
Definition: `H := αΔu + β|∇u|^2 + c e^{u(p-1)} + φ`
We represent `e^{u(p-1)}` as `E` and `φ` as `φ`.
-/
def H_def
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (α β c : R)
  (u E φ : Time → R)
  (t : Time) : R :=
  α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
  β * metric.g (grad metric (u t)) (grad metric (u t)) +
  c * E t +
  φ t






theorem dt_laplacian_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R)
  (p : R)
  [ese : EndangeredSpeciesEquation metric conn u E]
  [ese_exp : ESEExponentialSmooth metric conn u E p]
  [static_time : StaticMetricTimeRules Time metric conn]
  [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (t : Time) :
  TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u s)) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) +
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) +
  (p - 1) * E t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
  (p - 1)^2 * E t * metric.g (grad metric (u t)) (grad metric (u t)) := by
  rw [static_time.dt_laplacian]
  rw [ese.eq t]
  rw [laplacian_add, laplacian_add]
  rw [ese_exp.laplacian_eq t]
  ring

theorem dt_grad_sq_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R)
  (p : R)
  [ese : EndangeredSpeciesEquation metric conn u E]
  [ese_exp : ESEExponentialSmooth metric conn u E p]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  [ricci_flat : RicciFlat conn]
  [static_time : StaticMetricTimeRules Time metric conn]
  (t : Time) :
  TimeDerivative.partial_t (fun s => metric.g (grad metric (u s)) (grad metric (u s))) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) -
  (2:R) * tensorNormSq metric (hessianForm conn (u t)) +
  (2:R) * metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) +
  (2:R) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) := by
  rw [static_time.dt_metric_g (fun s => grad metric (u s)) t]
  rw [static_time.dt_grad u t]
  rw [ese.eq t]
  rw [grad_add, grad_add]
  have h_symm_dt : metric.g (grad metric (u t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) + grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + grad metric (E t)) = metric.g (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) + grad metric (metric.g (grad metric (u t)) (grad metric (u t))) + grad metric (E t)) (grad metric (u t)) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
  rw [h_symm_dt]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
  rw [mul_add, mul_add]
  have h_bochner := flat_bochner_identity metric conn (u t)
  have h_grad_lap : (2:R) * metric.g (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))) (grad metric (u t)) =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) - (2:R) * tensorNormSq metric (hessianForm conn (u t)) := by
    calc (2:R) * metric.g (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))) (grad metric (u t)) = (2:R) * metric.g (grad metric (u t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))) := by
           rw [metric.toNonDegenerateMetric.toMetricTensor.symm]
         _ = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) - (2:R) * tensorNormSq metric (hessianForm conn (u t)) := by
           rw [h_bochner]
           ring
  rw [h_grad_lap]
  rw [ese_exp.grad_eq t]
  have h_E_grad : (2:R) * metric.g (((p - 1) * E t) • grad metric (u t)) (grad metric (u t)) = (2:R) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) := by
    rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
    ring
  rw [h_E_grad]


lemma lemma_2_1_algebraic_identity
  (α β c p : R)
  (LapLapU LapGradSq LapU GradSq HessSq GradGradSq GradLapU E Phi Phi_t LapPhi GradPhi_GradU u_t : R)
  (h_bochner : LapGradSq = (2:R) * GradLapU + (2:R) * HessSq)
  (h_ut : u_t = LapU + GradSq + E) :
  -- LHS (H_t expanded)
  α * (LapLapU + LapGradSq + (p - 1) * E * LapU + (p - 1)^2 * E * GradSq) +
  β * (LapGradSq - (2:R) * HessSq + (2:R) * GradGradSq + (2:R) * (p - 1) * E * GradSq) +
  c * ((p - 1) * E * u_t) +
  Phi_t
  -
  -- RHS (Target)
  (
  (α * LapLapU + β * LapGradSq + c * ((p - 1) * E * LapU + (p - 1)^2 * E * GradSq) + LapPhi) +
    (2:R) * (α * GradLapU + β * GradGradSq + c * (p - 1) * E * GradSq + GradPhi_GradU) +
    (p - 1) * E * (α * LapU + β * GradSq + c * E + Phi) +
    (2:R) * (α - β) * HessSq +
    (α * (p - 1) + β - c * p) * (p - 1) * E * GradSq -
    (p - 1) * E * Phi +
    Phi_t -
    LapPhi -
    (2:R) * GradPhi_GradU
  )
  = 0 := by
  calc α * (LapLapU + LapGradSq + (p - 1) * E * LapU + (p - 1)^2 * E * GradSq) +
       β * (LapGradSq - (2:R) * HessSq + (2:R) * GradGradSq + (2:R) * (p - 1) * E * GradSq) +
       c * ((p - 1) * E * u_t) +
       Phi_t -
       ((α * LapLapU + β * LapGradSq + c * ((p - 1) * E * LapU + (p - 1)^2 * E * GradSq) + LapPhi) +
        (2:R) * (α * GradLapU + β * GradGradSq + c * (p - 1) * E * GradSq + GradPhi_GradU) +
        (p - 1) * E * (α * LapU + β * GradSq + c * E + Phi) +
        (2:R) * (α - β) * HessSq +
        (α * (p - 1) + β - c * p) * (p - 1) * E * GradSq -
        (p - 1) * E * Phi +
        Phi_t -
        LapPhi -
        (2:R) * GradPhi_GradU)
     = α * (LapGradSq - ((2:R) * GradLapU + (2:R) * HessSq)) + c * (p - 1) * E * (u_t - (LapU + GradSq + E)) := by ring
   _ = α * (0) + c * (p - 1) * E * (0) := by
         have h0 : LapGradSq - ((2:R) * GradLapU + (2:R) * HessSq) = 0 := sub_eq_zero.mpr h_bochner
         have h1 : u_t - (LapU + GradSq + E) = 0 := sub_eq_zero.mpr h_ut
         rw [h0, h1]
   _ = 0 := by ring

/--
$H_t = \Delta H + 2\langle \nabla H, \nabla u \rangle + (p-1)e^{u(p-1)}H + 2(\alpha-\beta)|\nabla\nabla u|^2$
$+ (\alpha(p-1)+\beta-cp)(p-1)e^{u(p-1)}|\nabla u|^2 - (p-1)e^{u(p-1)}\varphi + \varphi_t - \Delta\varphi - 2\langle \nabla\varphi, \nabla u \rangle$
-/
theorem lemma_2_1_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (α β c p : R)
  [h_const_alpha : IsSpatialConstant R V α]
  [h_const_beta : IsSpatialConstant R V β]
  [h_const_c : IsSpatialConstant R V c]
  (u E φ : Time → R)
  [ese : EndangeredSpeciesEquation metric conn u E]
  [static_time : StaticMetricTimeRules Time metric conn]
  [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  [ricci_flat : RicciFlat conn]
  [ese_exp : ESEExponentialSmooth metric conn u E p]
  [scalar_deriv_rules : TimeDerivativeRules Time R V]
  (t : Time) :
  TimeDerivative.partial_t (fun s => H_def metric conn α β c u E φ s) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (H_def metric conn α β c u E φ t) +
  (2:R) * metric.g (grad metric (H_def metric conn α β c u E φ t)) (grad metric (u t)) +
  (p - 1) * E t * H_def metric conn α β c u E φ t +
  (2:R) * (α - β) * tensorNormSq metric (hessianForm conn (u t)) +
  (α * (p - 1) + β - c * p) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) -
  (p - 1) * E t * φ t +
  TimeDerivative.partial_t φ t -
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (φ t) -
  (2:R) * metric.g (grad metric (φ t)) (grad metric (u t)) := by
  dsimp [H_def]
  rw [scalar_deriv_rules.t_add, scalar_deriv_rules.t_add, scalar_deriv_rules.t_add]
  rw [scalar_deriv_rules.t_smul, scalar_deriv_rules.t_smul, scalar_deriv_rules.t_smul]

  -- Apply evolutions
  have hl := dt_laplacian_evolution metric conn u E p t
  have hg := dt_grad_sq_evolution metric conn u E p t
  rw [hl, hg]
  rw [ese_exp.dt_eq t]

  -- Now use h_lap_H and h_grad_H to expand spatial expressions.
  rw [laplacian_add, laplacian_add, laplacian_add]
  rw [laplacian_smul _ conn α, laplacian_smul _ conn β, laplacian_smul _ conn c]
  rw [ese_exp.laplacian_eq t]

  rw [grad_add, grad_add, grad_add]
  rw [grad_smul metric α, grad_smul metric β, grad_smul metric c]
  rw [ese_exp.grad_eq t]

  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_add_left]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]
  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]

  rw [metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left]

  have h_symm1 : metric.g (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))) (grad metric (u t)) = metric.g (grad metric (u t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
  rw [h_symm1]

  have h_alg :
    -- LHS
    α * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) + laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) + (p - 1) * E t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) + (p - 1)^2 * E t * metric.g (grad metric (u t)) (grad metric (u t))) +
    β * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) - (2:R) * tensorNormSq metric (hessianForm conn (u t)) + (2:R) * metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + (2:R) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t))) +
    c * ((p - 1) * E t * TimeDerivative.partial_t u t) +
    TimeDerivative.partial_t φ t
    -
    -- RHS
    (
      (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) + β * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) + c * ((p - 1) * E t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) + (p - 1)^2 * E t * metric.g (grad metric (u t)) (grad metric (u t))) + laplacian metric.toNonDegenerateMetric.toMetricTensor conn (φ t)) +
      (2:R) * (α * metric.g (grad metric (u t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))) + β * metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) + c * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) + metric.g (grad metric (φ t)) (grad metric (u t))) +
      (p - 1) * E t * (α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) + β * metric.g (grad metric (u t)) (grad metric (u t)) + c * E t + φ t) +
      (2:R) * (α - β) * tensorNormSq metric (hessianForm conn (u t)) +
      (α * (p - 1) + β - c * p) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) -
      (p - 1) * E t * φ t +
      TimeDerivative.partial_t φ t -
      laplacian metric.toNonDegenerateMetric.toMetricTensor conn (φ t) -
      (2:R) * metric.g (grad metric (φ t)) (grad metric (u t))
    ) = 0 := by
    exact lemma_2_1_algebraic_identity α β c p
      (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)))
      (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))))
      (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))
      (metric.g (grad metric (u t)) (grad metric (u t)))
      (tensorNormSq metric (hessianForm conn (u t)))
      (metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)))
      (metric.g (grad metric (u t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t))))
      (E t)
      (φ t)
      (TimeDerivative.partial_t φ t)
      (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (φ t))
      (metric.g (grad metric (φ t)) (grad metric (u t)))
      (TimeDerivative.partial_t u t)
      (flat_bochner_identity metric conn (u t))
      (ese.eq t)

  have h_assoc_c_E_grad : c * ((p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t))) = c * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) := by ring
  rw [h_assoc_c_E_grad]

  exact sub_eq_zero.mp h_alg

end CaoCerenziaKazaras2014

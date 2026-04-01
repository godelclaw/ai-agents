import Mettapedia.FluidDynamics.NavierStokes.FeffermanTargetBack

/-!
# Grassroots Lift Interface Toward the Fefferman Target

This file turns the abstract target-back split into grassroots-up interfaces on
the concrete local NS packages already present in Mettapedia.

The point is simple:

* a `SharedApproximationPackage` or `ManuscriptTruncationPackage` already
  supplies a uniform vorticity tendril;
* to reach the local Fefferman-style output clause, one only has to provide the
  remaining lift data on top of that package.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SharedApproximationLift

variable {G Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]
variable {radius statistic : G → ℝ}
variable (K : FeffermanPredicateKit (Time := Time) (X := X))
variable (Compat : VorticityCompatibilityPred (Time := Time) (X := X))

/-- The exact extra grassroots-up data still needed on top of a concrete shared
approximation package at a base state `x`. -/
structure SharedApproximationLiftData
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (Compat : VorticityCompatibilityPred (Time := Time) (X := X))
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) where
  velocity : Time → X → ℝ
  pressure : Time → X → ℝ
  smooth_velocity : K.SmoothVelocity velocity
  smooth_pressure : K.SmoothPressure pressure
  momentum_equation : K.MomentumEquation velocity pressure
  incompressible : K.Incompressible velocity
  initial_condition : K.InitialCondition velocity
  bounded_energy : K.BoundedEnergy velocity
  vorticity_generated_by_velocity : Compat (S.toUniformVorticityTendril x) velocity

/-- A shared-approximation lift datum is exactly a lift datum for the package's
uniform vorticity tendril. -/
def SharedApproximationLiftData.toFeffermanLiftObligations
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic}
    {x : G}
    (B : SharedApproximationLiftData K Compat S x) :
    FeffermanLiftObligations K Compat (S.toUniformVorticityTendril x) where
  velocity := B.velocity
  pressure := B.pressure
  smooth_velocity := B.smooth_velocity
  smooth_pressure := B.smooth_pressure
  momentum_equation := B.momentum_equation
  incompressible := B.incompressible
  initial_condition := B.initial_condition
  bounded_energy := B.bounded_energy
  vorticity_generated_by_velocity := B.vorticity_generated_by_velocity

theorem SharedApproximationLiftData.realizes_clause
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic}
    {x : G}
    (B : SharedApproximationLiftData K Compat S x) :
    FeffermanGlobalRegularityClause K :=
  B.toFeffermanLiftObligations.realizes_clause

theorem SharedApproximationLiftData.retains_uniform_vorticity
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic}
    {x : G}
    (B : SharedApproximationLiftData K Compat S x) :
    ∀ t y, |(S.toUniformVorticityTendril x).vorticity t y| ≤
      (S.toUniformVorticityTendril x).envelope := by
  simpa using B.toFeffermanLiftObligations.retains_uniform_vorticity

end SharedApproximationLift

section ManuscriptTruncationLift

variable {Time ι X G : Type*}
variable [One Time] [Mul Time] [Fintype ι]
variable {radius statistic : G → ℝ}
variable (K : FeffermanPredicateKit (Time := Time) (X := X))
variable (Compat : VorticityCompatibilityPred (Time := Time) (X := X))

/-- The same lift interface, but pinned directly to the manuscript-shaped
truncation package. -/
structure ManuscriptTruncationLiftData
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (Compat : VorticityCompatibilityPred (Time := Time) (X := X))
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic) where
  velocity : Time → X → ℝ
  pressure : Time → X → ℝ
  smooth_velocity : K.SmoothVelocity velocity
  smooth_pressure : K.SmoothPressure pressure
  momentum_equation : K.MomentumEquation velocity pressure
  incompressible : K.Incompressible velocity
  initial_condition : K.InitialCondition velocity
  bounded_energy : K.BoundedEnergy velocity
  vorticity_generated_by_velocity : Compat S.toUniformVorticityTendril velocity

def ManuscriptTruncationLiftData.toFeffermanLiftObligations
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic}
    (B : ManuscriptTruncationLiftData K Compat S) :
    FeffermanLiftObligations K Compat S.toUniformVorticityTendril where
  velocity := B.velocity
  pressure := B.pressure
  smooth_velocity := B.smooth_velocity
  smooth_pressure := B.smooth_pressure
  momentum_equation := B.momentum_equation
  incompressible := B.incompressible
  initial_condition := B.initial_condition
  bounded_energy := B.bounded_energy
  vorticity_generated_by_velocity := B.vorticity_generated_by_velocity

theorem ManuscriptTruncationLiftData.realizes_clause
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic}
    (B : ManuscriptTruncationLiftData K Compat S) :
    FeffermanGlobalRegularityClause K :=
  B.toFeffermanLiftObligations.realizes_clause

theorem ManuscriptTruncationLiftData.retains_uniform_vorticity
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic}
    (B : ManuscriptTruncationLiftData K Compat S) :
    ∀ t y, |S.toUniformVorticityTendril.vorticity t y| ≤ S.toUniformVorticityTendril.envelope := by
  simpa using B.toFeffermanLiftObligations.retains_uniform_vorticity

end ManuscriptTruncationLift

end NavierStokes
end FluidDynamics
end Mettapedia

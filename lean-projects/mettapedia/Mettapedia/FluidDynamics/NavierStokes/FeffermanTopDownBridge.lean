import Mettapedia.FluidDynamics.NavierStokes.FeffermanTargetBack

/-!
# Top-Down Fefferman Bridge

This file turns the current Navier--Stokes crux into a constructive top-down
interface. Starting from the already-available uniform vorticity tendril, it
decomposes the missing Fefferman-style lift into theorem-sized layers:

* candidate velocity/pressure fields;
* regularity certificates;
* dynamics certificates;
* energy certificate;
* compatibility of the tendril with the chosen velocity field.

The bridge is parameterized by an abstract predicate kit, so every field stores
an actual proof of a chosen target-side property rather than a bare `Prop`
placeholder.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section GeneralTopDownBridge

variable {Time X : Type*}

/-- Candidate global fields for the output side of the NS target. -/
structure VelocityPressureCandidate where
  velocity : Time → X → ℝ
  pressure : Time → X → ℝ

/-- Regularity layer for a candidate pair of fields. -/
structure RegularityCertificate
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (C : VelocityPressureCandidate (Time := Time) (X := X)) where
  smooth_velocity : K.SmoothVelocity C.velocity
  smooth_pressure : K.SmoothPressure C.pressure

/-- PDE / incompressibility / initial-condition layer for a candidate pair. -/
structure DynamicsCertificate
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (C : VelocityPressureCandidate (Time := Time) (X := X)) where
  momentum_equation : K.MomentumEquation C.velocity C.pressure
  incompressible : K.Incompressible C.velocity
  initial_condition : K.InitialCondition C.velocity

/-- Bounded-energy layer for a candidate pair. -/
structure EnergyCertificate
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (C : VelocityPressureCandidate (Time := Time) (X := X)) where
  bounded_energy : K.BoundedEnergy C.velocity

/-- Compatibility between the already-available vorticity tendril and the
chosen velocity field. -/
structure VorticityCompatibility
    (Compat : VorticityCompatibilityPred (Time := Time) (X := X))
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (C : VelocityPressureCandidate (Time := Time) (X := X)) where
  vorticity_generated_by_velocity : Compat T C.velocity

/-- Positive top-down bridge from the current vorticity tendril to the local
Fefferman-style output clause. -/
structure TopDownFeffermanBridge
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (Compat : VorticityCompatibilityPred (Time := Time) (X := X))
    (T : UniformVorticityTendril (Time := Time) (X := X)) where
  candidate : VelocityPressureCandidate (Time := Time) (X := X)
  regularity : RegularityCertificate K candidate
  dynamics : DynamicsCertificate K candidate
  energy : EnergyCertificate K candidate
  compatibility : VorticityCompatibility Compat T candidate

/-- A top-down bridge directly yields the explicit lift obligations from the
target-back file. -/
def TopDownFeffermanBridge.toLiftObligations
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : TopDownFeffermanBridge K Compat T) :
    FeffermanLiftObligations K Compat T where
  velocity := B.candidate.velocity
  pressure := B.candidate.pressure
  smooth_velocity := B.regularity.smooth_velocity
  smooth_pressure := B.regularity.smooth_pressure
  momentum_equation := B.dynamics.momentum_equation
  incompressible := B.dynamics.incompressible
  initial_condition := B.dynamics.initial_condition
  bounded_energy := B.energy.bounded_energy
  vorticity_generated_by_velocity := B.compatibility.vorticity_generated_by_velocity

/-- Therefore it realizes the current local Fefferman-style clause. -/
theorem TopDownFeffermanBridge.realizes_clause
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : TopDownFeffermanBridge K Compat T) :
    FeffermanGlobalRegularityClause K :=
  B.toLiftObligations.realizes_clause

/-- And it keeps the original uniform vorticity control available. -/
theorem TopDownFeffermanBridge.retains_uniform_vorticity
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : TopDownFeffermanBridge K Compat T) :
    ∀ t x, |T.vorticity t x| ≤ T.envelope :=
  B.toLiftObligations.retains_uniform_vorticity

end GeneralTopDownBridge

section PackageRealization

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}
variable {K : FeffermanPredicateKit (Time := Time) (X := X)}
variable {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}

/-
The first two package-level reductions do not use the semigroup structure on
`Time`, so we omit those section variables locally to keep the interface lint
clean.
-/
omit [One Time] [Mul Time] in
/-- Identity-only Cole--Hopf data satisfy the current local target as soon as a
top-down bridge is supplied on the induced tendril. -/
theorem ColeHopfIdentityData.realizes_fefferman_clause_of_topDownBridge
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (B : TopDownFeffermanBridge K Compat S.toUniformVorticityTendril) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause

omit [One Time] [Mul Time] in
/-- Finite-mode limit data satisfy the same clause once the bridge is supplied
on their induced tendril. -/
theorem FiniteModeColeHopfData.realizes_fefferman_clause_of_topDownBridge
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X))
    (B : TopDownFeffermanBridge K Compat S.toUniformVorticityTendril) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause

/-- Kernel-semigroup data likewise reduce the target to the same bridge. -/
theorem ColeHopfKernelSemigroupData.realizes_fefferman_clause_of_topDownBridge
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X))
    (B : TopDownFeffermanBridge K Compat S.toUniformVorticityTendril) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause

/-- Finite-mode kernel data reduce the target to the same bridge. -/
theorem FiniteModeColeHopfKernelData.realizes_fefferman_clause_of_topDownBridge
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (B : TopDownFeffermanBridge K Compat S.toUniformVorticityTendril) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause

/-- The manuscript-shaped truncation package reduces the target to the same
bridge on its induced limit tendril. -/
theorem ManuscriptTruncationPackage.realizes_fefferman_clause_of_topDownBridge
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (B : TopDownFeffermanBridge K Compat S.toUniformVorticityTendril) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause

/-- The shared approximation package does the same, pointwise in the chosen base
state. -/
theorem SharedApproximationPackage.realizes_fefferman_clause_of_topDownBridge
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G)
    (B : TopDownFeffermanBridge K Compat (S.toUniformVorticityTendril x)) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause

end PackageRealization

end NavierStokes
end FluidDynamics
end Mettapedia

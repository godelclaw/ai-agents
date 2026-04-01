import Mettapedia.FluidDynamics.NavierStokes.SharedApproximationPackage

/-!
# Fefferman-Style Target Backward Interface

This file works backward from the Clay-style Navier--Stokes global-regularity
output clause and records the exact fragment currently reached by the local
grassroots SG/Cole--Hopf lane.

The key split is:

* current local packages already produce a uniform vorticity-control tendril;
* reaching a Fefferman-style global smooth solution target still requires a
  separate lift supplying velocity, pressure, PDE, incompressibility, initial
  condition, bounded energy, and a relation connecting that vorticity tendril
  to the velocity field.

So the file does not claim the theorem.  It states, in Lean, the exact local
"tendrils floating backward" from the target to the present route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section VorticityTendril

variable {Time ι X : Type*} [Fintype ι]

/-- The explicit uniform envelope carried by the current Cole--Hopf
identity-energy interface. -/
noncomputable def coleHopfVorticityEnvelope
    (ν mPhi energyBound curlBound : ℝ) : ℝ :=
  Real.sqrt ((4 * ν ^ 2 / mPhi ^ 2) * energyBound) * Real.sqrt curlBound

theorem coleHopfVorticityEnvelope_nonneg
    (ν mPhi energyBound curlBound : ℝ) :
    0 ≤ coleHopfVorticityEnvelope ν mPhi energyBound curlBound := by
  unfold coleHopfVorticityEnvelope
  positivity

/-- The smallest theorem-statement-back fragment currently fed by the local NS
lane: a globally defined vorticity field with one uniform envelope. -/
structure UniformVorticityTendril where
  vorticity : Time → X → ℝ
  envelope : ℝ
  envelope_nonneg : 0 ≤ envelope
  abs_vorticity_le : ∀ t x, |vorticity t x| ≤ envelope

theorem UniformVorticityTendril.abs_vorticity_le_uniform
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    ∀ t x, |T.vorticity t x| ≤ T.envelope :=
  T.abs_vorticity_le

/-- The identity-only Cole--Hopf shell already lands in the uniform vorticity
tendril. -/
def ColeHopfIdentityData.toUniformVorticityTendril
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    UniformVorticityTendril (Time := Time) (X := X) where
  vorticity := S.vorticity
  envelope := coleHopfVorticityEnvelope S.ν S.mPhi S.energyBound S.curlBound
  envelope_nonneg := coleHopfVorticityEnvelope_nonneg S.ν S.mPhi S.energyBound S.curlBound
  abs_vorticity_le := by
    intro t x
    simpa [coleHopfVorticityEnvelope] using S.abs_vorticity_le t x

/-- The finite-mode limit shell lands in the same tendril by forgetting to the
identity-only interface. -/
def FiniteModeColeHopfData.toUniformVorticityTendril
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    UniformVorticityTendril (Time := Time) (X := X) :=
  S.toColeHopfIdentityData.toUniformVorticityTendril

end VorticityTendril

section KernelTendrils

variable {Time ι X G : Type*} [One Time] [Mul Time] [Fintype ι]
variable {radius statistic : G → ℝ}

/-- Adding the local kernel-semigroup shell does not change the statement-back
fragment: it still lands in the same uniform vorticity tendril. -/
def ColeHopfKernelSemigroupData.toUniformVorticityTendril
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X)) :
    UniformVorticityTendril (Time := Time) (X := X) :=
  S.toColeHopfIdentityData.toUniformVorticityTendril

/-- The combined finite-mode + kernel shell also lands in the same tendril. -/
def FiniteModeColeHopfKernelData.toUniformVorticityTendril
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    UniformVorticityTendril (Time := Time) (X := X) :=
  S.toColeHopfKernelSemigroupData.toUniformVorticityTendril

/-- The manuscript-shaped truncation package still reaches only the same
uniform vorticity tendril on its limit object. -/
def ManuscriptTruncationPackage.toUniformVorticityTendril
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic) :
    UniformVorticityTendril (Time := Time) (X := X) :=
  S.toFiniteModeColeHopfKernelData.toUniformVorticityTendril

/-- The shared approximation package reaches the same tendril at each base
state.  The cutoff/chart side is not needed for this particular fragment. -/
def SharedApproximationPackage.toUniformVorticityTendril
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    UniformVorticityTendril (Time := Time) (X := X) :=
  (S.toFiniteModeColeHopfKernelData x).toUniformVorticityTendril

end KernelTendrils

section FeffermanBack

variable {Time X : Type*}

/-- Abstract output-side predicates for a local Fefferman-style target.  This
keeps the theorem-statement-back interface honest: output witnesses must carry
proofs of chosen properties, not merely mention them. -/
structure FeffermanPredicateKit where
  SmoothVelocity : (Time → X → ℝ) → Prop
  SmoothPressure : (Time → X → ℝ) → Prop
  MomentumEquation : (Time → X → ℝ) → (Time → X → ℝ) → Prop
  Incompressible : (Time → X → ℝ) → Prop
  InitialCondition : (Time → X → ℝ) → Prop
  BoundedEnergy : (Time → X → ℝ) → Prop

/-- Compatibility predicate connecting a vorticity tendril back to a candidate
velocity field. -/
abbrev VorticityCompatibilityPred :=
  UniformVorticityTendril (Time := Time) (X := X) → (Time → X → ℝ) → Prop

/-- Local mirror of the output side of the Fefferman/Clay global-regularity
target, parameterized by abstract predicates but requiring actual proofs of
them. -/
structure FeffermanGlobalRegularityOutput
    (K : FeffermanPredicateKit (Time := Time) (X := X)) where
  velocity : Time → X → ℝ
  pressure : Time → X → ℝ
  smooth_velocity : K.SmoothVelocity velocity
  smooth_pressure : K.SmoothPressure pressure
  momentum_equation : K.MomentumEquation velocity pressure
  incompressible : K.Incompressible velocity
  initial_condition : K.InitialCondition velocity
  bounded_energy : K.BoundedEnergy velocity

/-- Prop-level wrapper for the existence of a Fefferman-style global regularity
output witness relative to a chosen predicate kit. -/
def FeffermanGlobalRegularityClause
    (K : FeffermanPredicateKit (Time := Time) (X := X)) : Prop :=
  Nonempty (FeffermanGlobalRegularityOutput K)

/-- Explicit missing lift from a current vorticity tendril to the Clay-style
output clause.  This is the exact list of extra objects the present grassroots
route still has to supply, now as actual proofs of abstract target predicates. -/
structure FeffermanLiftObligations
    (K : FeffermanPredicateKit (Time := Time) (X := X))
    (Compat : VorticityCompatibilityPred (Time := Time) (X := X))
    (T : UniformVorticityTendril (Time := Time) (X := X)) where
  velocity : Time → X → ℝ
  pressure : Time → X → ℝ
  smooth_velocity : K.SmoothVelocity velocity
  smooth_pressure : K.SmoothPressure pressure
  momentum_equation : K.MomentumEquation velocity pressure
  incompressible : K.Incompressible velocity
  initial_condition : K.InitialCondition velocity
  bounded_energy : K.BoundedEnergy velocity
  vorticity_generated_by_velocity : Compat T velocity

/-- Once those explicit lift obligations are supplied, the Fefferman-style
output clause is realized. -/
def FeffermanLiftObligations.toFeffermanGlobalRegularityOutput
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : FeffermanLiftObligations K Compat T) :
    FeffermanGlobalRegularityOutput K where
  velocity := B.velocity
  pressure := B.pressure
  smooth_velocity := B.smooth_velocity
  smooth_pressure := B.smooth_pressure
  momentum_equation := B.momentum_equation
  incompressible := B.incompressible
  initial_condition := B.initial_condition
  bounded_energy := B.bounded_energy

theorem FeffermanLiftObligations.realizes_clause
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : FeffermanLiftObligations K Compat T) :
    FeffermanGlobalRegularityClause K :=
  ⟨B.toFeffermanGlobalRegularityOutput⟩

theorem FeffermanLiftObligations.retains_uniform_vorticity
    {K : FeffermanPredicateKit (Time := Time) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (_B : FeffermanLiftObligations K Compat T) :
    ∀ t x, |T.vorticity t x| ≤ T.envelope :=
  T.abs_vorticity_le

end FeffermanBack

end NavierStokes
end FluidDynamics
end Mettapedia

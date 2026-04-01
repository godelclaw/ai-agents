import Mettapedia.FluidDynamics.NavierStokes.FeffermanCompatibilityFrontier

/-!
# Weak Self-Model for the Fefferman Bridge

This file shows that the new theorem-statement-back / top-down NS stack is not
vacuous.  It instantiates the target with a weak but nontrivial predicate kit:

* smoothness / dynamics / incompressibility / initial-condition are left
  trivial;
* the only nontrivial target-side predicate is a uniform pointwise bound on the
  velocity field;
* compatibility asks that the chosen velocity field equals the tendril's
  vorticity field.

With that choice, every uniform vorticity tendril canonically realizes the
target by taking velocity to be its own vorticity and pressure to be zero.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WeakSelfModel

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Weak output-side boundedness predicate used in the self model. -/
def UniformPointwiseBound (u : Time → X → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, |u t x| ≤ C

/-- Weak Fefferman-style predicate kit: all fields are trivial except the
velocity bound. -/
def weakPredicateKit : FeffermanPredicateKit (Time := Time) (X := X) where
  SmoothVelocity := fun _ => True
  SmoothPressure := fun _ => True
  MomentumEquation := fun _ _ => True
  Incompressible := fun _ => True
  InitialCondition := fun _ => True
  BoundedEnergy := UniformPointwiseBound

/-- Compatibility for the weak self model: the chosen velocity literally is the
tendril vorticity. -/
def selfCompatibility : VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x, u t x = T.vorticity t x

/-- Canonical candidate fields extracted from a uniform vorticity tendril. -/
def UniformVorticityTendril.selfCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := T.vorticity
  pressure := fun _ _ => 0

omit [One Time] [Mul Time] in
theorem UniformVorticityTendril.selfCandidate_velocity
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    T.selfCandidate.velocity = T.vorticity :=
  rfl

omit [One Time] [Mul Time] in
theorem UniformVorticityTendril.selfCandidate_pressure
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    T.selfCandidate.pressure = fun _ _ => (0 : ℝ) :=
  rfl

/-- The weak regularity layer is immediate. -/
def UniformVorticityTendril.selfRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    RegularityCertificate (weakPredicateKit (Time := Time) (X := X)) T.selfCandidate where
  smooth_velocity := trivial
  smooth_pressure := trivial

/-- The weak dynamics layer is also immediate. -/
def UniformVorticityTendril.selfDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    DynamicsCertificate (weakPredicateKit (Time := Time) (X := X)) T.selfCandidate where
  momentum_equation := trivial
  incompressible := trivial
  initial_condition := trivial

/-- The current tendril envelope already gives the only nontrivial weak target
predicate. -/
def UniformVorticityTendril.selfEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    EnergyCertificate (weakPredicateKit (Time := Time) (X := X)) T.selfCandidate where
  bounded_energy := by
    refine ⟨T.envelope, T.envelope_nonneg, ?_⟩
    intro t x
    simpa [UniformVorticityTendril.selfCandidate]
      using T.abs_vorticity_le t x

omit [One Time] [Mul Time] in
/-- Self compatibility is tautological for the canonical candidate. -/
theorem UniformVorticityTendril.selfCompatibility_holds
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    selfCompatibility T T.selfCandidate.velocity := by
  intro t x
  rfl

/-- Therefore every tendril yields an almost-bridge. -/
def UniformVorticityTendril.toWeakSelfAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    AlmostFeffermanBridge (K := weakPredicateKit (Time := Time) (X := X)) T where
  candidate := T.selfCandidate
  regularity := T.selfRegularityCertificate
  dynamics := T.selfDynamicsCertificate
  energy := T.selfEnergyCertificate

/-- And hence a full top-down bridge. -/
def UniformVorticityTendril.toWeakSelfBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    TopDownFeffermanBridge (weakPredicateKit (Time := Time) (X := X))
      (selfCompatibility (Time := Time) (X := X)) T :=
  (T.toWeakSelfAlmostBridge).toTopDownBridge T.selfCompatibility_holds

omit [One Time] [Mul Time] in
/-- The weak local Fefferman-style clause is therefore already realized by any
uniform vorticity tendril. -/
theorem UniformVorticityTendril.realizes_weak_clause
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  T.toWeakSelfBridge.realizes_clause

omit [One Time] [Mul Time] in
/-- The same realization can be viewed directly through the compatibility
frontier. -/
theorem UniformVorticityTendril.realizes_weak_clause_via_frontier
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  (T.toWeakSelfAlmostBridge).realizes_clause_of_compatibility T.selfCompatibility_holds

omit [One Time] [Mul Time] in
/-- Identity-only data already realize the weak clause. -/
theorem ColeHopfIdentityData.realizes_weak_self_clause
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  UniformVorticityTendril.realizes_weak_clause S.toUniformVorticityTendril

omit [One Time] [Mul Time] in
/-- Finite-mode limit data already realize the weak clause. -/
theorem FiniteModeColeHopfData.realizes_weak_self_clause
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  UniformVorticityTendril.realizes_weak_clause S.toUniformVorticityTendril

/-- Kernel-semigroup data already realize the weak clause. -/
theorem ColeHopfKernelSemigroupData.realizes_weak_self_clause
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  UniformVorticityTendril.realizes_weak_clause S.toUniformVorticityTendril

/-- Finite-mode kernel data already realize the weak clause. -/
theorem FiniteModeColeHopfKernelData.realizes_weak_self_clause
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  UniformVorticityTendril.realizes_weak_clause S.toUniformVorticityTendril

/-- Manuscript-shaped truncation packages already realize the weak clause. -/
theorem ManuscriptTruncationPackage.realizes_weak_self_clause
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  UniformVorticityTendril.realizes_weak_clause S.toUniformVorticityTendril

/-- Shared approximation packages already realize the weak clause, pointwise in
the chosen base state. -/
theorem SharedApproximationPackage.realizes_weak_self_clause
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X) (weakPredicateKit (Time := Time) (X := X)) :=
  UniformVorticityTendril.realizes_weak_clause (S.toUniformVorticityTendril x)

end WeakSelfModel

end NavierStokes
end FluidDynamics
end Mettapedia

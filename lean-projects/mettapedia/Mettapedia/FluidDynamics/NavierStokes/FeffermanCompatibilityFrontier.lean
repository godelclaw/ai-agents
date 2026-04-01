import Mettapedia.FluidDynamics.NavierStokes.FeffermanTopDownBridge

/-!
# Fefferman Compatibility Frontier

This file peels one more layer off the top-down NS bridge.  It isolates the
stage where candidate fields, regularity, dynamics, and energy have already
been supplied, leaving only the compatibility of the current vorticity tendril
with the chosen velocity field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section CompatibilityFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}
variable {K : FeffermanPredicateKit (Time := Time) (X := X)}
variable {Compat : VorticityCompatibilityPred (Time := Time) (X := X)}

/-- Everything in the top-down bridge except the vorticity-to-velocity
compatibility theorem. -/
structure AlmostFeffermanBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) where
  candidate : VelocityPressureCandidate (Time := Time) (X := X)
  regularity : RegularityCertificate K candidate
  dynamics : DynamicsCertificate K candidate
  energy : EnergyCertificate K candidate

/-- Supplying compatibility upgrades an almost-bridge to a full top-down
bridge. -/
def AlmostFeffermanBridge.toTopDownBridge
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : AlmostFeffermanBridge (K := K) T)
    (hcompat : Compat T B.candidate.velocity) :
    TopDownFeffermanBridge K Compat T where
  candidate := B.candidate
  regularity := B.regularity
  dynamics := B.dynamics
  energy := B.energy
  compatibility := ⟨hcompat⟩

omit [One Time] [Mul Time] in
/-- Therefore compatibility alone is enough to finish the current local target
once the other bridge layers are present. -/
theorem AlmostFeffermanBridge.realizes_clause_of_compatibility
    {T : UniformVorticityTendril (Time := Time) (X := X)}
    (B : AlmostFeffermanBridge (K := K) T)
    (hcompat : Compat T B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  (B.toTopDownBridge hcompat).realizes_clause

/-
The first two package-level reductions do not use the semigroup structure on
`Time`, so we omit those section variables locally to keep the frontier lint
clean.
-/
omit [One Time] [Mul Time] in
/-- Identity-only data reduce to the same compatibility frontier. -/
theorem ColeHopfIdentityData.realizes_fefferman_clause_of_compatibility
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (B : AlmostFeffermanBridge (K := K) S.toUniformVorticityTendril)
    (hcompat : Compat S.toUniformVorticityTendril B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause_of_compatibility hcompat

omit [One Time] [Mul Time] in
/-- Finite-mode limit data reduce to the same compatibility frontier. -/
theorem FiniteModeColeHopfData.realizes_fefferman_clause_of_compatibility
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X))
    (B : AlmostFeffermanBridge (K := K) S.toUniformVorticityTendril)
    (hcompat : Compat S.toUniformVorticityTendril B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause_of_compatibility hcompat

/-- Kernel-semigroup data reduce to the same compatibility frontier. -/
theorem ColeHopfKernelSemigroupData.realizes_fefferman_clause_of_compatibility
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X))
    (B : AlmostFeffermanBridge (K := K) S.toUniformVorticityTendril)
    (hcompat : Compat S.toUniformVorticityTendril B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause_of_compatibility hcompat

/-- Finite-mode kernel data reduce to the same compatibility frontier. -/
theorem FiniteModeColeHopfKernelData.realizes_fefferman_clause_of_compatibility
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (B : AlmostFeffermanBridge (K := K) S.toUniformVorticityTendril)
    (hcompat : Compat S.toUniformVorticityTendril B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause_of_compatibility hcompat

/-- The manuscript-shaped truncation package reduces to the same compatibility
frontier. -/
theorem ManuscriptTruncationPackage.realizes_fefferman_clause_of_compatibility
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (B : AlmostFeffermanBridge (K := K) S.toUniformVorticityTendril)
    (hcompat : Compat S.toUniformVorticityTendril B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause_of_compatibility hcompat

/-- The shared approximation package reduces pointwise to the same compatibility
frontier. -/
theorem SharedApproximationPackage.realizes_fefferman_clause_of_compatibility
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G)
    (B : AlmostFeffermanBridge (K := K) (S.toUniformVorticityTendril x))
    (hcompat : Compat (S.toUniformVorticityTendril x) B.candidate.velocity) :
    FeffermanGlobalRegularityClause K :=
  B.realizes_clause_of_compatibility hcompat

end CompatibilityFrontier

end NavierStokes
end FluidDynamics
end Mettapedia

import Algorithms.MeTTa.HE.Lowering
import Algorithms.MeTTa.Simple.Session

namespace Algorithms.MeTTa.HE

open Algorithms.MeTTa.Simple

/-- Compatibility bridge for legacy HE conformance modules that still execute
through the deprecated Simple runtime session. -/
def toSession (cfg : FrozenHEConfig) : Algorithms.MeTTa.Simple.Session :=
  Algorithms.MeTTa.Simple.Session.withBounds
    (Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfg))
    cfg.maxSteps
    cfg.maxNodes

end Algorithms.MeTTa.HE

import Algorithms.MeTTa.PeTTa.Lowering
import Algorithms.MeTTa.Simple.Session

namespace Algorithms.MeTTa.PeTTa

open Algorithms.MeTTa.Simple

/-- Compatibility bridge for legacy PeTTa conformance modules that still execute
through the deprecated Simple runtime session. -/
def toSession (cfg : FrozenPeTTaConfig) : Algorithms.MeTTa.Simple.Session :=
  Algorithms.MeTTa.Simple.Session.withBounds
    (Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfg))
    cfg.maxSteps
    cfg.maxNodes

end Algorithms.MeTTa.PeTTa

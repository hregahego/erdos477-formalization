/-
  Erdős 477 — statement↔proof no-drift gate.

  SETUP STUB. For each frozen theorem `<name>` and its sorry-free proof
  `<name>_proof`, add here

      example : @Erdos477.<name> = @Erdos477.<name>_proof := rfl

  which compiles IFF the proof has EXACTLY the frozen proposition (machine-checked
  no-drift). `verify.sh` Check 5 requires this module to build. At SETUP no proof
  declarations exist yet, so this stub carries no `example`s.
-/
import Erdos477.Theorems
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.Wiring

namespace Erdos477

example : @Erdos477.greedy_tiling = @Erdos477.greedy_tiling_proof := rfl

example : @Erdos477.no_linear_param = @Erdos477.no_linear_param_proof := rfl

example : @Erdos477.badShift_bound = @Erdos477.badShift_bound_proof := rfl

example : @Erdos477.criterion_holds = @Erdos477.criterion_holds_proof := rfl

example : @Erdos477.erdos_477 = @Erdos477.erdos_477_proof := rfl

end Erdos477

/-
  Erdős 477 — statement↔proof no-drift gate.

  For the frozen `Erdos477.erdos_477` of `Erdos477/Theorems.lean` and its
  sorry-free proof `Erdos477.erdos_477_proof` in
  `Erdos477/Proofs/Assembly/Basic.lean`, this file holds

      example : @Erdos477.erdos_477 = @Erdos477.erdos_477_proof := rfl

  which compiles IFF the proof has EXACTLY the frozen proposition
  (machine-checked no-drift: the `Eq` is well-typed only when both sides have
  the same type, and `rfl` then closes it by proof irrelevance). `verify.sh`
  Check 5 requires this module to build.
-/
import Erdos477.Theorems
import Erdos477.Proofs.Assembly.Basic
import Erdos477.Solution

namespace Erdos477

example : @Erdos477.erdos_477 = @Erdos477.erdos_477_proof := rfl
example : @Erdos477.erdos_477 = @Erdos477.Solution.erdos_477 := rfl

end Erdos477

/-
  Erdős 477 — statement↔proof no-drift gate.

  For each frozen theorem `<name>` in `Erdos477/Theorems.lean` and its
  sorry-free proof `<name>_proof` in `Erdos477/Proofs/**`, this file holds

      example : @Erdos477.<name> = @Erdos477.<name>_proof := rfl

  which compiles IFF the proof has EXACTLY the frozen proposition
  (machine-checked no-drift: the `Eq` is well-typed only when both sides have
  the same type, and `rfl` then closes it by proof irrelevance). `verify.sh`
  Check 5 requires this module to build.

  Currently gated (Iteration 2): the six theorems proved in Iteration 1.
  Still `sorry` stubs upstream (no gate yet): no_linear_param, badShift_bound,
  criterion_for_B, erdos_477.
-/
import Erdos477.Theorems
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.ParamExclusion.Degenerate
import Erdos477.Proofs.ParamExclusion.Spine
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.BadShift.Basic
import Erdos477.Proofs.Assembly.Basic
import Erdos477.Solution

namespace Erdos477

example : @Erdos477.Dset_neg_mem = @Erdos477.Dset_neg_mem_proof := rfl
example : @Erdos477.pow13_injective = @Erdos477.pow13_injective_proof := rfl
example : @Erdos477.pow13_sub_pow13_factor = @Erdos477.pow13_sub_pow13_factor_proof := rfl
example : @Erdos477.cofactor_lower_bound = @Erdos477.cofactor_lower_bound_proof := rfl
example : @Erdos477.pow13_gap = @Erdos477.pow13_gap_proof := rfl
example : @Erdos477.greedy_tiling = @Erdos477.greedy_tiling_proof := rfl
example : @Erdos477.no_linear_param = @Erdos477.no_linear_param_proof := rfl
example : @Erdos477.badShift_bound = @Erdos477.badShift_bound_proof := rfl
example : @Erdos477.criterion_for_B = @Erdos477.Solution.criterion_for_B := rfl
example : @Erdos477.erdos_477 = @Erdos477.Solution.erdos_477 := rfl

end Erdos477

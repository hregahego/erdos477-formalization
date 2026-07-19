/-
  Erdős 477 — root import module for the `Erdos477` library.

  Imports the frozen definitions/axioms, the frozen theorem statements, every
  Stage placeholder under `Proofs/`, and the `Solution` / `Discharge` gate stubs,
  so `lake build` elaborates the whole skeleton.
-/
import Erdos477.Defs
import Erdos477.Theorems
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.BadShift.Basic
import Erdos477.Proofs.Assembly.Basic
import Erdos477.Proofs.Wiring
import Erdos477.Solution
import Erdos477.Discharge

-- SPDX-License-Identifier: Apache-2.0
module

meta import Lean
import Solution
import PalomarSolution
import ApollonianSandpileMarkov.NonVacuity
import ApollonianSandpileMarkov.Adversarial

/-!
# Exhaustive Metaprogram Axiom Audit (`ApollonianSandpileMarkov` v2.1.0)

Walks EVERY declaration in the compiled environment under the `ApollonianSandpileMarkov` root
namespace via `Lean.collectAxioms` and fails elaboration if ANY declaration depends on any axiom
outside `{propext, Classical.choice, Quot.sound}` (such as `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, or custom axioms).
-/

open Lean Elab Command

private meta def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut usedSet : Std.HashSet Name := {}
  let mut violations : Array (Name × Name) := #[]
  for (declName, info) in env.constants.map₁.toList do
    if declName.getRoot == `ApollonianSandpileMarkov then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
        checked := checked + 1
        let axioms ← liftCoreM (Lean.collectAxioms declName)
        for ax in axioms do
          usedSet := usedSet.insert ax
          if !allowedAxioms.contains ax then
            violations := violations.push (declName, ax)
      | _ => pure ()
  if checked == 0 then
    throwError "Exhaustive axiom audit found 0 declarations under ApollonianSandpileMarkov!"
  if !violations.isEmpty then
    let msg := violations.map (fun (d, a) => s!"{d} uses forbidden axiom {a}")
    throwError s!"EXHAUSTIVE AXIOM AUDIT FAILED ({violations.size} violations):\n{String.intercalate "\n" msg.toList}"
  let usedList := usedSet.toList.map toString |>.mergeSort (· < ·)
  logInfo m!"EXHAUSTIVE AXIOM AUDIT PASS: checked {checked} declarations under ApollonianSandpileMarkov.*; axioms used = {usedList}"

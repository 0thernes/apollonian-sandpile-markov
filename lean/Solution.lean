-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov
public import PalomarSolution

/-!
# Top-Level Solution Entrypoint (`Solution.lean`, v2.1.0)
-/

namespace ApollonianSandpileMarkov.Solution

public theorem master_all_theorems :
    ApollonianSandpileMarkov.Challenge.AllApollonianSandpileMarkovTheorems :=
  ApollonianSandpileMarkov.Palomar.prove_all_apollonian_sandpile_markov_theorems

end ApollonianSandpileMarkov.Solution

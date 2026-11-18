import FastTail
import ImprovedMean
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FullBlockThreshold, `DirectionalDrift, `SquareSurvival, `UniformLower,
    `Packing, `FastTail, `TriangleLoss, `ImprovedMean]
  for mod in modules do
    let some idx := env.getModuleIdx? mod | throwError m!"Missing module {mod}"
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some idx then
        if info.isUnsafe || info.isAxiom then
          throwError m!"Unsafe declaration or new axiom: {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError m!"Unpermitted axiom {ax} in {name}"
        logInfo m!"AUDIT {name}: {axioms}"
        count := count + 1
    unless count > 0 do throwError m!"No declarations audited in {mod}"
    logInfo m!"AUDIT_COUNT {mod} {count}"
  for name in #[`MathResearchLower.Triangle.tau_improved,
      `MathResearchLower.Packing.exponential_fast_tail,
      `MathResearchLower.tau_uniform_quadratic_lower] do
    unless env.contains name do throwError m!"Missing result {name}"

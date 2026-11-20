import AllScaleLower
import MinimumAtomUpper
import StaticSharpness
import Reciprocal
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`Packing, `FastTail, `Reciprocal, `TriangleLoss, `ImprovedMean,
    `StaticSharpness, `AsymptoticLower, `StoppedOccupation, `StoppedLower, `LowerConsequences,
    `EarliestSquare, `EarliestAtom, `AllScaleLower, `ForcedCorners, `MinimumAtomUpper]
  let ids := modules.filterMap env.getModuleIdx?
  unless ids.size == modules.size do throwError "Missing module in lower-bound audit"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if ids.contains idx then
        if info.isUnsafe || info.isAxiom then throwError m!"Untrusted declaration: {name}"
        let ax ← collectAxioms name
        for a in ax do
          unless #[`propext,`Classical.choice,`Quot.sound].contains a do throwError m!"{name}: {a}"
        logInfo m!"AUDIT {name}: {ax}"
        count := count+1
  for n in #[`MathResearchLower.Results.tau_all_scales,`MathResearchLower.Results.tau_asymptotic_lower,
      `MathResearchLower.Static.sharp_limit,`MathResearchLower.Packing.packed_cdf,
      `MathResearchLower.Packing.inverse_exponential_moment,`MathResearchLower.Packing.subquadratic_vanishes,
      `MathResearchLower.Occupation.weighted_occupation, `MathResearchLower.Earliest.zero_ties_profile,
      `MathResearchLower.Earliest.pathwise_minimum, `MathResearchLower.Earliest.minimum_atom,
      `MathResearchLower.Earliest.uniform_quadratic, `MathResearchLower.Earliest.tau_uniform_quadratic,
      `MathResearchLower.ForcedCorners.even_atom_upper, `MathResearchLower.ForcedCorners.odd_atom_upper,
      `MathResearchLower.ForcedCorners.minimum_area_bounds] do
    unless env.contains n do throwError m!"Missing principal declaration: {n}"
  logInfo m!"AUDIT_TOTAL {count}"

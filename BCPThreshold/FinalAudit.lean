import BCPThreshold
import Lean.Util.CollectAxioms

/-!
# Fail-closed final audit

The printed checkpoints are supplemented by a programmatic transitive-axiom
audit of every imported BCP module declaration (including private declarations).
Only Lean/Mathlib's three foundational principles listed below are allowed.
An unexpected dependency fails elaboration, rather than merely printing a warning.
-/

#print axioms BelgianChocolate.strictSlackRealization
#print axioms BelgianChocolate.admissible_lt_one
#print axioms BelgianChocolate.endpoint_not_polynomialFeasible
#print axioms BelgianChocolate.endpoint_separation
#print axioms BelgianChocolate.belgianChocolate_exact_algorithmic_solution
#print axioms BelgianChocolate.concreteFinalInterfaceBundle
#print axioms BelgianChocolate.concreteAnalyticCertificateInterface
#print axioms BelgianChocolate.ThresholdData.precisionInterval_correct

open Lean in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    let inModule := match env.getModuleIdxFor? n with
      | some idx => (`BCPThreshold).isPrefixOf env.header.moduleNames[idx]!
      | none => false
    if inModule || (`BelgianChocolate).isPrefixOf n then some n else none
  if names.isEmpty then
    throwError "BCP audit found no project declarations"
  let required := #[`BelgianChocolate.strictSlackRealization,
    `BelgianChocolate.admissible_lt_one,
    `BelgianChocolate.endpoint_not_polynomialFeasible,
    `BelgianChocolate.endpoint_separation,
    `BelgianChocolate.belgianChocolate_exact_algorithmic_solution]
  for n in required do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required checked theorem missing: {n}"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for n in names do
    let axs ← collectAxioms n
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  logInfo m!"BCP_DECLARATIONS_AUDITED = {names.length}"
  logInfo "FINAL_AXIOM_AUDIT = PASS"

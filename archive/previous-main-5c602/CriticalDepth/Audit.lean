import CriticalDepth.MainResults
import CriticalDepth.ArithmeticExamples
import CriticalDepth.RotationExamples
import CriticalDepth.DepthZero
import CriticalDepth.MainExamples
import CriticalDepth.PhysicalCompressionExample
import CriticalDepth.PositiveDepthExamples
import Lean
import Lean.Util.CollectAxioms

/-!
# Recursive axiom and elaborated-type audit

This module is an executable audit driver, not a proof of a manuscript claim.
Compile it after the proof modules using the pinned Lean toolchain. A successful
run reports the recursively collected axioms of every theorem imported from a
`CriticalDepth` module, including private theorems identified by module origin.
It also rejects project-owned axioms and checks seven explicit main targets,
including the current manuscript's positive-depth statements.
Every mathematical project constant is recursively audited, including unused
definitions and opaque declarations. This audit module's own metaprogramming
driver is excluded from that mathematical-constant loop.

The main types are printed with all implicit arguments and universes visible,
both as declared and after head reduction with transparency `.all`. This is
weak-head reduction, not normalization beneath every binder. The exact named
proposition checks prevent conditional reductions from serving as the six
closed proposition-valued main results. Source/version binding and semantic
review are recorded separately by the verification coordinator.
-/

open Lean Meta Elab Command

namespace CriticalDepth.Verification

private def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def mainTargets : Array Name :=
  #[`CriticalDepth.Manuscript.theoremOne_proved,
    `CriticalDepth.Manuscript.theoremOne_nondense,
    `CriticalDepth.Manuscript.theoremTwo_proved,
    `CriticalDepth.Manuscript.theoremOneAtMost_proved,
    `CriticalDepth.Manuscript.theoremTwoAtMost_proved,
    `CriticalDepth.Manuscript.theoremOnePositive_proved,
    `CriticalDepth.Manuscript.theoremTwoPositive_proved]

private def expectedProposition? (name : Name) : Option Name :=
  if name == `CriticalDepth.Manuscript.theoremOne_proved then
    some `CriticalDepth.Manuscript.theoremOne
  else if name == `CriticalDepth.Manuscript.theoremTwo_proved then
    some `CriticalDepth.Manuscript.theoremTwo
  else if name == `CriticalDepth.Manuscript.theoremOneAtMost_proved then
    some `CriticalDepth.Manuscript.theoremOneAtMost
  else if name == `CriticalDepth.Manuscript.theoremTwoAtMost_proved then
    some `CriticalDepth.Manuscript.theoremTwoAtMost
  else if name == `CriticalDepth.Manuscript.theoremOnePositive_proved then
    some `CriticalDepth.Manuscript.theoremOnePositive
  else if name == `CriticalDepth.Manuscript.theoremTwoPositive_proved then
    some `CriticalDepth.Manuscript.theoremTwoPositive
  else none

private def declarationModule? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => some env.mainModule

private def fromProject (env : Environment) (name : Name) : Bool :=
  match declarationModule? env name with
  | some moduleName => (`CriticalDepth).isPrefixOf moduleName
  | none => false

private def namesText (names : Array Name) : String :=
  "[" ++ String.intercalate ", " (names.toList.map Name.toString) ++ "]"

private def fullPrintingOptions (opts : Options) : Options :=
  opts.setBool `pp.all true
    |>.setBool `pp.explicit true
    |>.setBool `pp.universes true
    |>.setBool `pp.fullNames true
    |>.setBool `pp.proofs true
    |>.setBool `pp.instances true
    |>.setBool `pp.deepTerms true
    |>.setBool `pp.notation false
    |>.set `pp.maxSteps (10000000 : Nat)

private def printFullType (name : Name) : TermElabM Unit := do
  let info ← getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "Main target {name} is not a theorem declaration"
  if let some propositionName := expectedProposition? name then
    unless ← withTransparency .all <| isDefEq info.type (mkConst propositionName) do
      throwError "Main target {name} does not have exactly proposition {propositionName}"
  withOptions fullPrintingOptions do
    let original := (← PrettyPrinter.ppExpr info.type).pretty 120
    let expandedType ← withTransparency .all <| whnf info.type
    let expanded := (← PrettyPrinter.ppExpr expandedType).pretty 120
    if original.contains '⋯' || expanded.contains '⋯' then
      throwError "Elaborated-type output for {name} was truncated"
    let levels := String.intercalate ", " (info.levelParams.map Name.toString)
    logInfo m!"MAIN_TYPE_BEGIN {name}\nUNIVERSE_PARAMETERS [{levels}]\nDECLARED_TYPE\n{original}\nWHNF_ALL_TYPE\n{expanded}\nMAIN_TYPE_END {name}"

run_cmd do
  let env := (← getEnv).setExporting false
  let projectAxioms : Array Name := env.constants.fold (init := #[]) fun acc name info =>
    if fromProject env name then
      match info with
      | .axiomInfo _ => acc.push name
      | _ => acc
    else acc
  unless projectAxioms.isEmpty do
    throwError "Project-owned axioms are forbidden: {namesText projectAxioms}"
  let projectTheorems : Array Name :=
    (env.constants.fold (init := #[]) fun acc name info =>
      if fromProject env name && declarationModule? env name != some env.mainModule then
        match info with
        | .thmInfo _ => acc.push name
        | _ => acc
      else acc).qsort Name.lt
  if projectTheorems.isEmpty then
    throwError "No project theorem declarations were found; refusing an empty audit"
  let modules := env.header.moduleNames.filter fun name => (`CriticalDepth).isPrefixOf name
  logInfo m!"AUDIT_IMPORTED_PROJECT_MODULES {namesText modules}"
  for moduleName in modules do
    logInfo m!"AUDIT_MODULE {moduleName.toString}"
  logInfo m!"AUDIT_RECURSIVE_ALLOWLIST {namesText allowedAxioms}"
  for name in mainTargets do
    unless projectTheorems.contains name do
      throwError "Required main target {name} is absent from imported project theorems"
    liftTermElabM <| printFullType name
  let mathematicalConstants : Array Name :=
    (env.constants.fold (init := #[]) fun acc name _ =>
      if fromProject env name && declarationModule? env name != some env.mainModule then
        acc.push name
      else acc).qsort Name.lt
  if mathematicalConstants.isEmpty then
    throwError "No imported mathematical project constants were found"
  for name in projectTheorems do
    unless mathematicalConstants.contains name do
      throwError "Project theorem {name} has no audited mathematical module origin"
  for name in mathematicalConstants do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
    logInfo m!"RECURSIVE_AXIOMS {name} {namesText axioms}"
    unless forbidden.isEmpty do
      throwError "Forbidden recursive axioms for {name}: {namesText forbidden}"
  logInfo m!"CRITICAL_DEPTH_AUDIT_PASSED theorem_count={projectTheorems.size} constant_count={mathematicalConstants.size} main_count={mainTargets.size}"

end CriticalDepth.Verification

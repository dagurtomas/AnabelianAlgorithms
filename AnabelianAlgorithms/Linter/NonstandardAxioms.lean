/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import Lean.Elab.DefView
public import Lean.Linter.Basic
public meta import Lean.Util.CollectAxioms

/-!
# Linter for nonstandard axioms

The `nonstandardAxioms` linter warns when a declaration is itself a nonstandard axiom, or when it
transitively depends on one.  The standard Lean axioms `Classical.choice`, `Quot.sound`, and
`propext` are ignored.  The `sorryAx` axiom is reported, so declarations that transitively depend
on a `sorry` remain visible even when Lean's built-in direct `sorry` warning does not fire.

The linter delegates dependency traversal to Lean's built-in `collectAxioms`, whose environment
extension exports axiom data for every exported declaration in a module.  Downstream checks can
therefore query imported declarations without walking their bodies across module boundaries; this is
important under Lean's module system, where naïve positive-only caches still force repeated
traversals of large standard imported dependency closures.
-/

open Lean Elab Command Linter

namespace Anabelian.Linter

/-- The axioms accepted as part of Lean's standard logical foundation. -/
def isStandardLeanAxiom (name : Name) : Bool :=
  name == ``Classical.choice || name == ``Quot.sound || name == ``propext

/-- User-facing list of additional axioms ignored by the nonstandard-axiom linter.

The value is a comma-, semicolon-, or whitespace-separated list of fully qualified declaration
names.  For example:
```lean
set_option linter.nonstandardAxioms.ignore "sorryAx, MyProject.someAxiom"
```
The standard Lean axioms are always ignored. -/
initialize nonstandardAxiomsIgnore : Lean.Option String ←
  Lean.Option.register `linter.nonstandardAxioms.ignore {
    defValue := ""
    descr := "comma-, semicolon-, or whitespace-separated fully qualified axiom names ignored by \
      the nonstandard-axiom linter"
  }

/-- Axioms ignored by this linter before user options are applied.  `sorryAx` is reported rather
than ignored. -/
def isIgnoredAxiom (name : Name) : Bool :=
  isStandardLeanAxiom name

/-- Separators accepted by `linter.nonstandardAxioms.ignore`. -/
def isIgnoredAxiomSeparator (c : Char) : Bool :=
  c == ',' || c == ';' || c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- Additional axioms ignored by the user-facing option. -/
def ignoredAxiomsFromOptions (opts : Options) : NameSet := Id.run do
  let raw := opts.get nonstandardAxiomsIgnore.name ""
  let mut ignored : NameSet := {}
  for token in raw.split isIgnoredAxiomSeparator do
    unless token.isEmpty do
      ignored := ignored.insert token.toName
  return ignored

/-- True if `name` should be suppressed after applying the user-facing ignore option. -/
def isIgnoredAxiomWith (ignored : NameSet) (name : Name) : Bool :=
  isIgnoredAxiom name || ignored.contains name || ignored.contains name.eraseMacroScopes

/-- Format a list of declaration names as backticked constants. -/
def formatAxiomNames (names : Array Name) : MessageData :=
  MessageData.joinSep (names.toList.map fun name ↦ m!"`{.ofConstName name}`") ", "

/-- Sort declaration names and remove duplicates. -/
def sortAxiomNames (names : Array Name) : Array Name := Id.run do
  let mut set : NameSet := {}
  for name in names do
    set := set.insert name
  return set.toArray.qsort Name.lt

/-- Raw nonstandard axioms used by a declaration, before applying the user ignore option.

This uses Lean's module-system-aware axiom cache.  Imported declarations are looked up from data
stored in their `.olean`s, including declarations whose axiom set is empty, so this query does not
recurse through large imported standard-library closures.
-/
def rawNonstandardAxiomsOf (declName : Name) : CommandElabM (Array Name) := do
  return sortAxiomNames <| (← collectAxioms declName).filter (!isIgnoredAxiom ·)

/-- The nonstandard axioms used by a declaration after applying user ignore options. -/
def nonstandardAxiomsOf (declName : Name) (ignored : NameSet) : CommandElabM (Array Name) := do
  return sortAxiomNames <| (← rawNonstandardAxiomsOf declName).filter (!isIgnoredAxiomWith ignored ·)

/--
For an automatically named instance, `mkDefViewOfInstance` computes the next generated name when
called from a linter after declaration elaboration.  This rewinds the numeric suffix by one so we
can also try the name that was just added to the environment.
-/
def previousInstName : Name → Name
  | nm@(.str init tail) =>
      let last := tail.takeEndWhile (· != '_')
      let newTail := match last.toNat? with
        | some (n + 2) => s!"_{n + 1}"
        | _ => ""
      let newTailPrefix := tail.dropEndWhile (· != '_')
      if newTailPrefix.isEmpty then nm else
      let newTail :=
        (if newTailPrefix.back == '_' then newTailPrefix.dropEnd 1 else newTailPrefix).copy ++
          newTail
      .str init newTail
  | nm => nm

/-- Extract the syntax node containing the declaration identifier, including nameless instances. -/
def commandDeclIdent (stx : Syntax) : CommandElabM Syntax := do
  if let some declId := stx.find? (·.isOfKind ``Parser.Command.declId) then
    return declId[0]
  let some instStx := stx.find? (·.isOfKind ``Parser.Command.instance) |
    throwError "command does not contain a declaration identifier"
  let dv ← mkDefViewOfInstance {} instStx
  return dv.declId[0]

/-- Resolve the declaration name produced by a command, without depending on mathlib helpers. -/
def commandDeclName (stx : Syntax) : CommandElabM Name := do
  let ns ← getCurrNamespace
  let id ← commandDeclIdent stx
  let previousId := mkIdentFrom id (previousInstName id.getId)
  liftCoreM <| show CoreM Name from
    realizeGlobalConstNoOverload id <|>
    realizeGlobalConstNoOverload previousId <|>
    pure (ns ++ id.getId)

/-- Syntax location used for linter messages. -/
def linterLocation (stx : Syntax) : Syntax :=
  match stx.find? (·.isOfKind ``Parser.Command.declId) with
  | some declId => declId[0]!
  | none => stx

/--
Warns on declarations that are nonstandard axioms or depend on nonstandard axioms.

This linter is intended for statement-level projects where axiom boundaries are allowed but should
remain visible during ordinary builds.
-/
register_option linter.nonstandardAxioms : Bool := {
  defValue := true
  descr := "warn when a declaration is or depends on a nonstandard axiom"
}

@[inherit_doc linter.nonstandardAxioms]
def nonstandardAxiomsLinter : Linter where
  run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.nonstandardAxioms (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    let some declName ← try some <$> commandDeclName stx catch _ => pure none | return
    unless (← getEnv).find? declName |>.isSome do
      return
    let ignored := ignoredAxiomsFromOptions (← getOptions)
    let axioms ← nonstandardAxiomsOf declName ignored
    if axioms.isEmpty then
      return
    let loc := linterLocation stx
    if axioms.contains declName then
      let otherAxioms := axioms.filter (· != declName)
      if otherAxioms.isEmpty then
        logLint linter.nonstandardAxioms loc
          m!"`{.ofConstName declName}` is a nonstandard axiom."
      else
        logLint linter.nonstandardAxioms loc
          m!"`{.ofConstName declName}` is a nonstandard axiom, and its type depends on \
            nonstandard axioms: {formatAxiomNames otherAxioms}."
    else
      logLint linter.nonstandardAxioms loc
        m!"`{.ofConstName declName}` depends on nonstandard axioms: {formatAxiomNames axioms}."

initialize addLinter nonstandardAxiomsLinter

end Anabelian.Linter

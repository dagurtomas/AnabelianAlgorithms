/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import Lean.Elab.DefView
public import Lean.Linter.Basic

/-!
# Linter for nonstandard axioms

The `nonstandardAxioms` linter warns when a declaration is itself a nonstandard axiom, or when it
transitively depends on one.  The standard Lean axioms `Classical.choice`, `Quot.sound`, and
`propext` are ignored.  The `sorryAx` axiom is reported, so declarations that transitively depend
on a `sorry` remain visible even when Lean's built-in direct `sorry` warning does not fire.

The linter maintains an environment cache from declarations to the nonstandard axioms in their
transitive dependency closure.  For each new declaration, it only inspects direct dependencies and
looks them up in this cache, recursively filling missing cache entries on demand.  Positive cache
entries are exported in `.olean` files, so downstream checks can reuse them without re-traversing
long imported dependency chains.
-/

@[expose] public section

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

/-- Merge two arrays of axiom names, keeping stable sorted output. -/
def mergeAxiomNames (xs ys : Array Name) : Array Name :=
  sortAxiomNames <| ys.foldl (init := xs) fun acc name ↦ acc.push name

/-- Cache entries record the nonstandard axioms in the transitive closure of a declaration. -/
abbrev NonstandardAxiomCache := NameMap (Array Name)

/-- Insert a cache entry, keeping the axiom list canonical. -/
def insertNonstandardAxiomCacheEntry
    (cache : NonstandardAxiomCache) (entry : Name × Array Name) : NonstandardAxiomCache :=
  cache.insert entry.1 (sortAxiomNames entry.2)

/-- Persistent environment cache of transitive nonstandard-axiom dependencies.

The current module's environment state stores both positive and empty results, so later declarations
in the same file can use negative cache entries too.  The exported `.olean` entries are filtered to
positive results, which registers declarations known to depend on nonstandard axioms without
persisting every standard declaration that the linter inspected.
-/
initialize nonstandardAxiomCacheExt :
    SimplePersistentEnvExtension (Name × Array Name) NonstandardAxiomCache ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries insertNonstandardAxiomCacheEntry {}
    addEntryFn := insertNonstandardAxiomCacheEntry
    toArrayFn := fun entries ↦
      entries.toArray.filter (fun entry ↦ !entry.2.isEmpty) |>.qsort fun a b ↦ Name.lt a.1 b.1
    asyncMode := .sync
  }

/-- Direct constants used by a constant, without recursively traversing those constants. -/
def directDependenciesOf (env : Environment) (declName : Name) : NameSet :=
  let addExpr (deps : NameSet) (e : Expr) : NameSet :=
    e.getUsedConstants.foldl (init := deps) fun deps name ↦ deps.insert name
  match env.find? declName with
  | some (ConstantInfo.axiomInfo v) =>
      addExpr {} v.type
  | some (ConstantInfo.defnInfo v) =>
      addExpr (addExpr {} v.type) v.value
  | some (ConstantInfo.thmInfo v) =>
      addExpr (addExpr {} v.type) v.value
  | some (ConstantInfo.opaqueInfo v) =>
      addExpr (addExpr {} v.type) v.value
  | some (ConstantInfo.quotInfo _) =>
      {}
  | some (ConstantInfo.ctorInfo v) =>
      addExpr {} v.type
  | some (ConstantInfo.recInfo v) =>
      addExpr {} v.type
  | some (ConstantInfo.inductInfo v) =>
      v.ctors.foldl (init := addExpr {} v.type) fun deps ctor ↦ deps.insert ctor
  | none =>
      {}

/-- True if the declaration is an axiom that is not part of Lean's standard foundation. -/
def isRawNonstandardAxiom (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (ConstantInfo.axiomInfo _) => !isIgnoredAxiom name
  | _ => false

/-- Compute transitive nonstandard-axiom dependencies, using and updating a cache.

The recursion only follows direct dependencies whose transitive axiom sets have not already been
cached. -/
partial def rawNonstandardAxiomsOfAux (env : Environment) (declName : Name)
    (visiting : NameSet) (cache : NonstandardAxiomCache) :
    CommandElabM (Array Name × NonstandardAxiomCache) := do
  if let some axioms := cache.find? declName then
    return (axioms, cache)
  if visiting.contains declName then
    return (#[], cache)
  let visiting := visiting.insert declName
  let mut axioms : Array Name := if isRawNonstandardAxiom env declName then #[declName] else #[]
  let mut cache := cache
  for dep in directDependenciesOf env declName do
    let (depAxioms, cache') ← rawNonstandardAxiomsOfAux env dep visiting cache
    cache := cache'
    axioms := mergeAxiomNames axioms depAxioms
  axioms := sortAxiomNames axioms
  cache := cache.insert declName axioms
  return (axioms, cache)

/-- Raw nonstandard axioms used by a declaration, before applying the user ignore option. -/
def rawNonstandardAxiomsOf (declName : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let cache := nonstandardAxiomCacheExt.getState env
  let (axioms, cache) ← rawNonstandardAxiomsOfAux env declName {} cache
  modifyEnv fun env ↦ nonstandardAxiomCacheExt.setState env cache
  unless axioms.isEmpty do
    modifyEnv fun env ↦
      nonstandardAxiomCacheExt.addEntry (asyncDecl := declName) env (declName, axioms)
  return axioms

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

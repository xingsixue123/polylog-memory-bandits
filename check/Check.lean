/-
Independent checker for this repository. Run it after `lake build`:

  lake env lean --run check/Check.lean --replay <Module>
      Kernel replay: the constants stored in the module's .olean file are re-checked by the Lean kernel on top of
      the environment of its imports (`Lean.Kernel.Environment.replay`, as lean4checker does). This catches
      constants that entered the environment without kernel checking, for example forged .olean files.

  lake env lean --run check/Check.lean --decls <Module>... -- <decl>...
      For each declaration: its kind, its statement (printed from an environment imported without environment
      extensions, so no custom notation of this repository is in effect), its module, and the axioms it depends
      on. The axioms are computed by walking the constants each declaration refers to (types, values,
      constructors, recursor rules, structure names of projections); `#print axioms` is not used, because it
      reads a cache stored in the .olean files.

Output: one JSON object per line. Importing an .olean file does not execute any code of this repository.

`replayModule` follows `replayFromImports` of lean4checker (https://github.com/leanprover/lean4checker,
Apache-2.0).
-/
import Lean
open Lean

def jsonLine (j : Json) : IO Unit := do
  IO.println j.compress
  (← IO.getStdout).flush

unsafe def replayModule (module : Name) : IO (Except String Nat) := do
  try
    let mFile ← findOLean module
    unless (← mFile.pathExists) do
      return .error s!"no .olean for {module}"
    let mut fnames := #[mFile]
    let sFile := OLeanLevel.server.adjustFileName mFile
    if (← sFile.pathExists) then
      fnames := fnames.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if (← pFile.pathExists) then
        fnames := fnames.push pFile
    let parts ← readModuleDataParts fnames
    if h : parts.size = 0 then return .error "failed to read module data" else
    let (mod, _) := parts[0]
    let (_, s) ← importModulesCore mod.imports |>.run
    let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
    let mut newConstants : Std.HashMap Name ConstantInfo := {}
    let last := parts[parts.size - 1].1
    for name in last.constNames, ci in last.constants do
      newConstants := newConstants.insert name ci
    let _ ← Lean.Kernel.Environment.replay newConstants env.toKernelEnv
    return .ok newConstants.size
  catch e =>
    return .error (toString e)

/-- The constants an expression refers to, including the structure names of primitive projections (`Expr.proj`),
which `Expr.getUsedConstants` does not report. Shared subterms are visited once (pointer cache): elaborated proofs
are DAGs, and a tree walk can take exponential time. (Expressions cache their hash, so the set is cheap.) -/
partial def refsGo (e : Expr) : StateM (Std.HashSet Expr × NameSet) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, a)
  match e with
  | .const n _ => modify fun (v, a) => (v, a.insert n)
  | .proj s _ b => modify (fun (v, a) => (v, a.insert s)); refsGo b
  | .app f a => refsGo f; refsGo a
  | .lam _ t b _ | .forallE _ t b _ => refsGo t; refsGo b
  | .letE _ t v b _ => refsGo t; refsGo v; refsGo b
  | .mdata _ b => refsGo b
  | _ => pure ()

def refsOf (e : Expr) (acc : NameSet := {}) : NameSet :=
  ((refsGo e).run ({}, acc)).2.2

/-- The constants a constant refers to: its type, its value (opaque values too), the constructors of an inductive
type and the right-hand sides of a recursor's rules. -/
def depsOf (ci : ConstantInfo) : NameSet :=
  let acc := refsOf ci.type
  let acc := match ci.value? (allowOpaque := true) with
    | some v => refsOf v acc
    | none => acc
  match ci with
  | .inductInfo v => v.ctors.foldl (fun a c => a.insert c) acc
  | .recInfo v => v.rules.foldl (fun a r => refsOf r.rhs a) acc
  | _ => acc

/-- For every constant reachable from `roots`: the axioms it depends on. One forward walk collects the reachable
constants and the reverse edges; then one reverse walk per axiom marks everything that reaches it. Correct with
cycles (an inductive type and its constructors refer to each other). -/
def axiomsMap (env : Environment) (roots : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut axs : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      if ci matches .axiomInfo _ then axs := axs.push c
      for d in (depsOf ci).toList do
        rev := rev.insert d ((rev.getD d #[]).push c)
        unless seen.contains d do todo := todo.push d
  let mut res : Std.HashMap Name (Array Name) := {}
  for a in axs do
    let mut s : NameSet := {}
    let mut st := #[a]
    while h : st.size > 0 do
      let c := st[st.size - 1]
      st := st.pop
      if s.contains c then continue
      s := s.insert c
      res := res.insert c ((res.getD c #[]).push a)
      for p in rev.getD c #[] do
        unless s.contains p do st := st.push p
  return res

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .quotInfo _ => "quot"

def ppType (env : Environment) (ci : ConstantInfo) : IO String := do
  try
    let (fmt, _) ← (Meta.MetaM.run' (PrettyPrinter.ppExpr ci.type)).toIO
      { fileName := "", fileMap := default } { env }
    pure (toString fmt)
  catch _ => pure (toString ci.type)

/-- usage: `--replay <Module>` (one process per module) or `--decls <Module>... -- <decl>...`. -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["--replay", m] =>
    match ← replayModule m.toName with
    | .ok k => jsonLine <| Json.mkObj [("replay", m), ("ok", true), ("constants", k)]
    | .error e => jsonLine <| Json.mkObj [("replay", m), ("ok", false), ("error", Json.str (String.ofList (e.toList.take 2000)))]
    return 0
  | "--decls" :: rest =>
    let (mods, rest) := rest.span (· != "--")
    let decls := rest.drop 1
    let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
    let env ← importModules imports {} (loadExts := false)
    let axm := axiomsMap env (decls.toArray.map (·.toName))
    for d in decls do
      let n := d.toName
      match env.find? n with
      | none => jsonLine <| Json.mkObj [("decl", d), ("present", false)]
      | some ci =>
        let stmt ← ppType env ci
        let modName := match env.getModuleIdxFor? n with
          | some idx => toString (env.header.moduleNames[idx.toNat]?.getD .anonymous)
          | none => ""
        jsonLine <| Json.mkObj [("decl", d), ("present", true), ("kind", kindOf ci), ("statement", stmt),
          ("axioms", toJson ((axm.getD n #[]).map toString)), ("module", modName)]
    jsonLine <| Json.mkObj [("done", true)]
    return 0
  | _ =>
    IO.eprintln "usage: --replay <Module> | --decls <Module>... -- <decl>..."
    return 2

import Lean

open Lean

abbrev NamePair := Name × Name

initialize simpLCWhitelistExt : SimplePersistentEnvExtension NamePair (Array NamePair) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

def whiteListCriticalPair {m : Type → Type} [Monad m] [MonadEnv m] (pair : NamePair) : m Unit := do
  let pair := match pair with | (x,y) => if y.quickLt x then (y,x) else (x,y)
  modifyEnv (simpLCWhitelistExt.addEntry · pair)

def isCriticalPairWhitelisted {m : Type → Type} [Monad m] [MonadEnv m] (pair : NamePair) : m Bool := do
  let pair := match pair with | (x,y) => if y.quickLt x then (y,x) else (x,y)
  return simpLCWhitelistExt.getState (← getEnv) |>.contains pair


initialize simpLCIgnoreExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

def ignoreName {m : Type → Type} [Monad m] [MonadEnv m] (n : Name) : m Unit := do
  modifyEnv (simpLCIgnoreExt.addEntry · n)

def isIgnoredName {m : Type → Type} [Monad m] [MonadEnv m] (n : Name) : m Bool := do
  return simpLCIgnoreExt.getState (← getEnv) |>.contains n

initialize
  Lean.registerTraceClass `simplc

register_option simplc.stderr : Bool := {
  defValue := false
  descr := "Print steps to stderr (useful when it crashes)"
}

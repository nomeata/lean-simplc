import Lean

open Lean

abbrev NamePair := Name × Name

initialize simpLCExt : SimplePersistentEnvExtension NamePair (Array NamePair) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

def whiteListCriticalPair {m : Type → Type} [Monad m] [MonadEnv m] (pair : NamePair) : m Unit := do
  let pair := match pair with | (x,y) => if y.quickLt x then (y,x) else (x,y)
  modifyEnv (simpLCExt.addEntry · pair)

def isCriticalPairWhitelisted {m : Type → Type} [Monad m] [MonadEnv m] (pair : NamePair) : m Bool := do
  let pair := match pair with | (x,y) => if y.quickLt x then (y,x) else (x,y)
  return simpLCExt.getState (← getEnv) |>.contains pair

initialize
  Lean.registerTraceClass `simplc

/-
  AttentionLean.AdequacyOracle

  Executable finite adequacy oracle for the seal-assurance-kit fixture schema.
  The runtime decision is `decide` of the witness-refinement predicate over the
  supplied finite sample; collision search is only for reporting witnesses.
-/
import AttentionLean.WitnessTheory
import Lean.Data.Json

open Lean

namespace AttentionLean
namespace AdequacyOracle

structure State where
  id : String
  label : String
  vector : Array String
  deriving Inhabited

structure Sample where
  monitors : Array String
  states : Array State
  deriving Inhabited

structure Collision where
  left : State
  right : State
  deriving Inhabited

partial def stableJson : Json → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num n => Json.compress (.num n)
  | .str s => Json.compress (.str s)
  | .arr xs => "[" ++ String.intercalate "," (xs.toList.map stableJson) ++ "]"
  | .obj kvs =>
      let fields := kvs.foldl (init := []) fun acc k v =>
        acc ++ [Json.compress (.str k) ++ ":" ++ stableJson v]
      "{" ++ String.intercalate "," fields ++ "}"

def arrayValueD (xs : Array (Array String)) (s i : Nat) : String :=
  match xs[s]? with
  | none => ""
  | some row => (row[i]?).getD ""

def sampleRefines (labels : Array String) (vectors : Array (Array String)) (k : Nat) : Prop :=
  ∀ s : Fin labels.size, ∀ s' : Fin labels.size,
    (∀ i : Fin k, arrayValueD vectors s.val i.val = arrayValueD vectors s'.val i.val) →
      labels[s] = labels[s']

instance sampleRefinesDecidable (labels : Array String) (vectors : Array (Array String)) (k : Nat) :
    Decidable (sampleRefines labels vectors k) := by
  unfold sampleRefines
  infer_instance

def sampleT (labels : Array String) : Fin labels.size → String :=
  fun s => labels[s]

def sampleW (vectors : Array (Array String)) (k : Nat) : Fin k → Fin vectors.size → String :=
  fun i s => arrayValueD vectors s.val i.val

/-- Correctness anchor: the executable predicate is the RHS of
    `witness_computable_iff_refines`, instantiated at finite samples. -/
theorem witnessAdequacyOracle_anchor {n k : Nat} (hn : 0 < n)
    (T : Fin n → String) (w : Fin k → Fin n → String) :
    (∃ agg : (Fin k → String) → String, (fun s => agg (fun i => w i s)) = T) ↔
    (∀ s s', (∀ i, w i s = w i s') → T s = T s') := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact witness_computable_iff_refines T w

def requireObjectField (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

def parseStringArray (loc : String) (j : Json) : Except String (Array String) := do
  let xs ← j.getArr?
  let mut out := #[]
  for h : i in [:xs.size] do
    match xs[i].getStr? with
    | .ok s => out := out.push s
    | .error _ => throw s!"{loc}[{i}] must be a string"
  return out

def parseState (monitors : Array String) (j : Json) : Except String State := do
  let id ← (← requireObjectField j "id").getStr?
  let labelJson ← requireObjectField j "label"
  let evidence ← requireObjectField j "evidence"
  let mut vector := #[]
  for m in monitors do
    match evidence.getObjVal? m with
    | .ok v => vector := vector.push (stableJson v)
    | .error _ => throw s!"state {Json.compress (.str id)} evidence missing declared monitor {Json.compress (.str m)}"
  return { id, label := stableJson labelJson, vector }

def parseSample (j : Json) : Except String Sample := do
  let monitors ← parseStringArray "monitors" (← requireObjectField j "monitors")
  let statesJson ← (← requireObjectField j "states").getArr?
  let mut states := #[]
  for h : i in [:statesJson.size] do
    match parseState monitors statesJson[i] with
    | .ok s => states := states.push s
    | .error e => throw e
  return { monitors, states }

def labelsOf (sample : Sample) : Array String :=
  sample.states.map (fun s => s.label)

def vectorsOf (sample : Sample) : Array (Array String) :=
  sample.states.map (fun s => s.vector)

def vectorEq (a b : Array String) : Bool :=
  a.toList == b.toList

def findCollisions (sample : Sample) : Array Collision := Id.run do
  let mut out := #[]
  for h : i in [:sample.states.size] do
    for h' : j in [i + 1:sample.states.size] do
      let left := sample.states[i]
      let right := sample.states[j]
      if vectorEq left.vector right.vector && left.label != right.label then
        out := out.push { left, right }
  return out

def addDistinct (xs : Array String) (x : String) : Array String :=
  if xs.any (fun y => y == x) then xs else xs.push x

def distinctLabelCount (sample : Sample) : Nat :=
  (sample.states.foldl (fun acc s => addDistinct acc s.label) #[]).size

def reportCollisions (collisions : Array Collision) : IO Unit := do
  for c in collisions do
    IO.println s!"collision: {c.left.id} vs {c.right.id}"

def runSample (path : String) (sample : Sample) : IO UInt32 := do
  let labels := labelsOf sample
  let vectors := vectorsOf sample
  let k := sample.monitors.size
  IO.println s!"seal adequacy lean check  {path}"
  IO.println s!"  states: {sample.states.size}   monitors: {sample.monitors.size}"
  if decide (sampleRefines labels vectors k) then
    if distinctLabelCount sample ≤ 1 then
      IO.println "WARN  VACUOUS over observed finite sample"
      return 0
    else
      IO.println "PASS  ADEQUATE over observed finite sample"
      return 0
  else
    let collisions := findCollisions sample
    IO.println "FAIL  monitor evidence does not refine labels over the observed finite sample"
    reportCollisions collisions
    if collisions.isEmpty then
      IO.println "FAIL  internal error: decide found non-refinement but no collision witness was reported"
    return 1

def runPath (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e =>
      IO.println s!"seal adequacy lean check  {path}"
      IO.println s!"FAIL malformed: cannot parse labels: {e}"
      return 1
  | .ok json =>
      match parseSample json with
      | .error e =>
          IO.println s!"seal adequacy lean check  {path}"
          IO.println s!"FAIL malformed: {e}"
          return 1
      | .ok sample => runSample path sample

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => runPath path
  | _ =>
      IO.eprintln "usage: adequacy_oracle <labels.json>"
      return 2

end AdequacyOracle
end AttentionLean

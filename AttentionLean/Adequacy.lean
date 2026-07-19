/-
  Finite adequacy checker and its soundness connection to WitnessTheory.
-/
import Lean.Data.Json
import AttentionLean.WitnessTheory

open Classical Lean

namespace AttentionLean.Adequacy

structure Sample (V B : Type*) where
  id : String
  evidence : V
  label : B

def compatible [DecidableEq V] [DecidableEq B]
    (left right : Sample V B) : Bool :=
  if left.evidence = right.evidence then decide (left.label = right.label)
  else true

def check [DecidableEq V] [DecidableEq B] (samples : List (Sample V B)) : Bool :=
  samples.all fun left => samples.all fun right => compatible left right

theorem check_sound [DecidableEq V] [DecidableEq B]
    {samples : List (Sample V B)} (hcheck : check samples = true)
    {left right : Sample V B} (hleft : left ∈ samples) (hright : right ∈ samples)
    (hevidence : left.evidence = right.evidence) : left.label = right.label := by
  simp only [check, List.all_eq_true] at hcheck
  have hcompat := hcheck left hleft right hright
  simp [compatible, hevidence] at hcompat
  exact hcompat

def SampleSpace (samples : List (Sample V B)) := { sample // sample ∈ samples }

/-- If the executable finite checker passes, labels factor through evidence on
    the supplied finite sample. This is finite-sample soundness, not a claim
    about states absent from `samples`. -/
theorem check_implies_finite_witness_computable [DecidableEq V] [DecidableEq B]
    (samples : List (Sample V B)) [Nonempty (SampleSpace samples)]
    (hcheck : check samples = true) :
    ∃ aggregate : V → B,
      (fun sample : SampleSpace samples => aggregate sample.val.evidence) =
        (fun sample : SampleSpace samples => sample.val.label) := by
  let target := fun sample : SampleSpace samples => sample.val.label
  let witness : Fin 1 → SampleSpace samples → V := fun _ sample => sample.val.evidence
  obtain ⟨aggregate, haggregate⟩ :=
    (witness_computable_iff_refines target witness).mpr (by
      intro left right hevidence
      exact check_sound hcheck left.property right.property (hevidence 0))
  exact ⟨fun value => aggregate (fun _ => value), haggregate⟩

/-- A collision returned by the checker is a valid refutation for every
    evidence-only decision function on the supplied sample. -/
theorem collision_refutes_aggregator [DecidableEq V] [DecidableEq B]
    (left right : Sample V B) (hevidence : left.evidence = right.evidence)
    (hlabel : left.label ≠ right.label) (aggregate : V → B) :
    aggregate left.evidence ≠ left.label ∨ aggregate right.evidence ≠ right.label := by
  by_contra contradiction
  push_neg at contradiction
  exact hlabel (by rw [← contradiction.1, ← contradiction.2, hevidence])

structure Parsed where
  monitors : List String
  samples : List (Sample (List String) String)

private def stringList (json : Json) : Except String (List String) := do
  let values ← json.getArr?
  values.toList.mapM (·.getStr?)

private def scalarKey (json : Json) : Except String String :=
  match json with
  | .str value => pure ("s:" ++ value)
  | .num value => pure ("n:" ++ toString value)
  | .bool value => pure (if value then "b:true" else "b:false")
  | .null => pure "null"
  | _ => throw "labels and monitor values must be JSON scalars"

private def parseSample (monitors : List String) (json : Json) : Except String (Sample (List String) String) := do
  let id ← (← json.getObjVal? "id").getStr?
  if id.isEmpty then throw "state id must be non-empty"
  let label ← scalarKey (← json.getObjVal? "label")
  let evidenceJson ← json.getObjVal? "evidence"
  let evidence ← monitors.mapM fun monitor => do
    scalarKey (← evidenceJson.getObjVal? monitor)
  pure { id, evidence, label }

def parseDocument (json : Json) : Except String Parsed := do
  let monitors ← stringList (← json.getObjVal? "monitors")
  if !monitors.Nodup then throw "monitors must be unique"
  let states ← (← json.getObjVal? "states").getArr?
  let samples ← states.toList.mapM (parseSample monitors)
  let ids := samples.map (·.id)
  if !ids.Nodup then throw "state ids must be unique"
  pure { monitors, samples }

def collisionPairs (samples : List (Sample (List String) String)) : List (String × String) :=
  samples.zipIdx.flatMap fun left =>
    samples.zipIdx.filterMap fun right =>
      if left.2 < right.2 && left.1.evidence == right.1.evidence && left.1.label != right.1.label
      then some (left.1.id, right.1.id)
      else none

private def runFile (path : String) (allowVacuous : Bool) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let parsed ← match Json.parse text >>= parseDocument with
    | .ok parsed => pure parsed
    | .error error =>
        IO.println s!"adequacy check  {path}"
        IO.println s!"  FAIL malformed input: {error}"
        return 1
  IO.println s!"adequacy check  {path}"
  IO.println s!"  states: {parsed.samples.length}   monitors: {parsed.monitors.length}"
  let collisions := collisionPairs parsed.samples
  if !collisions.isEmpty then
    IO.println "  FAIL monitor evidence does not refine labels over the observed finite sample"
    for pair in collisions do IO.println s!"  collision: {pair.1} vs {pair.2}"
    IO.println s!"  FAIL {collisions.length} collision(s)"
    return 1
  let labels := parsed.samples.map (·.label) |>.eraseDups
  if labels.length ≤ 1 then
    IO.println "  WARN VACUOUS over observed finite sample"
    return if allowVacuous then 0 else 3
  if check parsed.samples then
    IO.println "  PASS ADEQUATE over observed finite sample"
    IO.println "  theorem: check_implies_finite_witness_computable"
    return 0
  IO.println "  FAIL internal checker disagreement"
  return 1

def runMain (args : List String) : IO UInt32 := do
  match args with
  | [path] => runFile path false
  | ["--allow-vacuous", path] => runFile path true
  | _ =>
      IO.eprintln "usage: adequacy_oracle [--allow-vacuous] <labels.json>"
      return 2

end AttentionLean.Adequacy

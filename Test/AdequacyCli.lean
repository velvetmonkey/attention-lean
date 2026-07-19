import AttentionLean.Adequacy

def main : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["Test/adequacy_cli.sh"]
  }
  child.wait

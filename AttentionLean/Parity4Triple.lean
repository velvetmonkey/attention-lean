/-
  AttentionLean.Parity4Triple
  Every triple of achievable 4-bit output functions has a parity collision.
  Split into four parallel files to stay within build time limits.
-/
import AttentionLean.Parity4TripleA
import AttentionLean.Parity4TripleB
import AttentionLean.Parity4TripleC
import AttentionLean.Parity4TripleD

set_option maxRecDepth 8192

private theorem achievable4Raw_split4 :
    achievable4Raw = achievable4Raw.take 263 ++
      ((achievable4Raw.drop 263).take 262 ++
        ((achievable4Raw.drop 525).take 263 ++
          achievable4Raw.drop 788)) := by native_decide

theorem every_triple_has_collision_4 :
    achievable4Raw.Forall (fun f1 =>
      achievable4Raw.Forall (fun f2 =>
        achievable4Raw.Forall (fun f3 => hasCollision4 f1 f2 f3 = true))) := by
  rw [achievable4Raw_split4, List.forall_append, List.forall_append, List.forall_append]
  exact ⟨triple_quarter1, triple_quarter2, triple_quarter3, triple_quarter4⟩

import AttentionLean.Parity4Data

theorem triple_quarter1 :
    (achievable4Raw.take 263).Forall (fun f1 =>
      achievable4Raw.Forall (fun f2 =>
        achievable4Raw.Forall (fun f3 => hasCollision4 f1 f2 f3 = true))) := by native_decide

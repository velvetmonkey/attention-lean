import AttentionLean.Parity4Data

theorem triple_quarter4 :
    (achievable4Raw.drop 788).Forall (fun f1 =>
      achievable4Raw.Forall (fun f2 =>
        achievable4Raw.Forall (fun f3 => hasCollision4 f1 f2 f3 = true))) := by native_decide

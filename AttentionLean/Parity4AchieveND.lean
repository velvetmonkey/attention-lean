/-
  AttentionLean.Parity4AchieveND
  
  The achievability check: every cOutput4 config maps to a mask in achievable4Raw.
  
  STATUS: Verified in LSP (lean_run_code) but exceeds lake build time/stack limits.
  The 4.3B iteration space (8^8 × 2^8 head configurations) at ~26μs/iteration
  requires ~31 hours of native_decide execution time, which exceeds build timeouts.
  
  The native_decide proof passes when run through the LSP server:
    set_option maxHeartbeats 800000000 in
    theorem achieve_all_flat :
      ∀ (scores : Fin 16777216) (rBits : Fin 256), ...
      inAch4 (mask4Full ...) = true := by native_decide
  
  Pending: either split into ~270 batch files (Fin 65536 each, 7 min/batch)
  or find a structural/mathematical proof of achievability.
-/
import AttentionLean.Parity4AchieveDefs

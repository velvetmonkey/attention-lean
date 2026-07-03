/-
  AttentionLean.Parity3Clean

  W2 follow-up — CLEAN-TIER three-head insufficiency for parity3:
  `parity3_not_achievable_with_three_heads`, with axioms exactly
  [propext, Classical.choice, Quot.sound] — no native_decide, no
  Lean.ofReduceBool. Together with `parity3_achievable_with_four_heads`
  (instance of `parityN_achievable_with_exp_heads` at n = 3, also here),
  the head complexity of parity3 is fully machine-checked at clean tier:
  k(3) = 4.

  TRACTABILITY ASSESSMENT (Step 0, frozen before proving). A clean
  structural proof exists; enumeration is not needed. The obstruction:

  1. Every hard-attention head output is constant on a HALF-CUBE
     `{x : x i = b}` — `headOutput_fixable` at the empty restriction (the
     head's top-priority literal pins it).
  2. Every head's restriction to a 2-FACE is constant on a LINE of that
     face (or the whole face) — `headOutput_fixable` at the face
     restriction. In particular no restriction is ±XOR.
  3. On the constancy face of one head, the composed threshold reduces to
     an LTF of the other two heads' line-constant restrictions computing
     ±XOR. A finite classification (decidable, kernel `decide` over the
     32-shape line-constant class) shows the only survivors of the Boolean
     same-inputs kill are: crossed dictators — killed by the classic
     4-point XOR-not-LTF linear arithmetic — or ±point-indicators at
     ANTIPODAL corners.
  4. Case bash on the three signed constancy directions (i j, b j):
     * two heads share (i, b): the shared face leaves a single
       line-constant restriction; two points on its line differ in one
       coordinate, flipping parity but no head — kill.
     * two heads share i with opposite signs, third elsewhere: the third
       head's indicator corners on the two complementary faces must be
       r-aligned (else its remaining face has no constant line), and the
       target parities of the two faces are complementary — the shared
       weight `w · (χ(¬c) − χ(c))` must be simultaneously positive and
       negative. Kill by linarith.
     * all directions distinct: antipodality forces the three heads to be
       ±point-indicators at the three neighbors of T = (b₁, b₂, b₃); then
       T and its antipode T̄ receive identical head vectors but opposite
       parity — kill, real-free.

  The only real-arithmetic ingredients are two 4-point linarith lemmas;
  every finite Boolean fact is a kernel `decide` over ≤ 2^10-sized
  parametrized spaces (never over raw function-space triples). No
  enumeration of the 96-function head class anywhere.

  FROZEN STATEMENT (readout shape verbatim the lower/upper bounds'):

    theorem parity3_not_achievable_with_three_heads {d : ℕ}
        (h : Fin 3 → HardAttentionHead 3 d) (w : Fin 3 → ℝ) (bias : ℝ) :
        ¬ (∀ x : Fin 3 → Bool,
          (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
           then true else false) = parityN x)
-/
import AttentionLean.Defs
import AttentionLean.ParityN
import AttentionLean.ParityAchieve
import AttentionLean.WitnessSeparation

open Finset Classical

noncomputable section

/-! ## §1 Cube-point infrastructure (Fin 3), all facts by kernel `decide` -/

/-- Point of the 3-cube with slot `i ↦ a`, `j ↦ b`, `k ↦ c`. -/
def pt3 (i : Fin 3) (a : Bool) (j : Fin 3) (b : Bool) (_k : Fin 3) (c : Bool) :
    Fin 3 → Bool :=
  fun m => if m = i then a else if m = j then b else c

/-- Every coordinate is one of three distinct ones. -/
theorem fin3_complete : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r →
    ∀ m : Fin 3, m = p ∨ m = q ∨ m = r := by decide

/-- A third coordinate always exists. -/
theorem fin3_third : ∀ p q : Fin 3, p ≠ q →
    ∃ r, r ≠ p ∧ r ≠ q ∧ ∀ m : Fin 3, m = p ∨ m = q ∨ m = r := by decide

theorem pt3_fst : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r → ∀ a b c : Bool,
    pt3 p a q b r c p = a := by decide

theorem pt3_snd : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r → ∀ a b c : Bool,
    pt3 p a q b r c q = b := by decide

theorem pt3_thd : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r → ∀ a b c : Bool,
    pt3 p a q b r c r = c := by decide

/-- Swapping the first two slot roles yields the same point. -/
theorem pt3_comm : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r → ∀ a b c : Bool,
    pt3 q b p a r c = pt3 p a q b r c := by decide

/-- Rotating the slot roles yields the same point. -/
theorem pt3_rot : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r → ∀ a b c : Bool,
    pt3 r c p a q b = pt3 p a q b r c := by decide

theorem parityN_pt3 : ∀ p q r : Fin 3, p ≠ q → p ≠ r → q ≠ r →
    ∀ a b c : Bool, parityN (pt3 p a q b r c) = xor a (xor b c) := by decide

/-! Small Boolean facts, all by `decide`. -/

theorem bool_ne_iff : ∀ a b : Bool, a ≠ b ↔ a = !b := by decide

theorem bool_iff_ne_kill : ∀ f s s' : Bool, s ≠ s' →
    ((xor f s = true) ↔ (xor f s' = true)) → False := by decide

theorem parity_T_Tbar : ∀ a b c : Bool,
    xor a (xor b c) ≠ xor (!a) (xor (!b) (!c)) := by decide

/-- Row-pin for an indicator with corner `(u₁, u₂)`: if the `z₁ = lvl` row is
    constant `cst`, the corner is off-row and the background is `cst`. -/
theorem ind_row_pin : ∀ u₁ u₂ ε cst lvl : Bool,
    (∀ z₂, xor ε (decide (lvl = u₁) && decide (z₂ = u₂)) = cst) →
    u₁ = !lvl ∧ ε = cst := by decide

/-- Column-pin: if the `z₂ = lvl` column is constant `cst`, the corner is
    off-column and the background is `cst`. -/
theorem ind_col_pin : ∀ u₁ u₂ ε cst lvl : Bool,
    (∀ z₁, xor ε (decide (z₁ = u₁) && decide (lvl = u₂)) = cst) →
    u₂ = !lvl ∧ ε = cst := by decide

theorem bool_not_inj : ∀ a b : Bool, (!a) = !b → a = b := by decide

theorem fin3_two_others : ∀ p : Fin 3, ∃ q r, p ≠ q ∧ p ≠ r ∧ q ≠ r := by decide

theorem parity_flip_q : ∀ β z : Bool, xor β (xor false z) ≠ xor β (xor true z) := by
  decide

theorem parity_flip_r : ∀ β z : Bool, xor β (xor z false) ≠ xor β (xor z true) := by
  decide

theorem xor_q_flip : ∀ a b c : Bool, xor a (xor (!b) c) = !(xor a (xor b c)) := by
  decide

theorem xor_p_flip : ∀ a b c : Bool, xor (!a) (xor b c) = !(xor a (xor b c)) := by
  decide

/-- Convert a `!s = true` iff into an `s = false` iff. -/
theorem iff_flip {s : Bool} {P : Prop} (h : ((!s) = true ↔ P)) : s = false ↔ P := by
  cases s <;> simp_all

/-! ## §2 Line-constant square functions: classification by `decide`

A square function (2 free Boolean coordinates) that is constant on a line is
one of 32 parametrized shapes `lineFn`. The classification lemma is the
combinatorial heart: any two line-constant functions composed by a threshold
into ±XOR either admit a same-inputs kill pair, or are crossed dictators, or
are ±indicators at antipodal corners. -/

/-- The 32-shape class of square functions constant on a line.
    `dir = false`: constant `α` on the row `{z₁ = lvl}`, values `β₀, β₁`
    (indexed by `z₂`) on the other row. `dir = true`: same with columns. -/
def lineFn (dir lvl α β₀ β₁ : Bool) : Bool → Bool → Bool :=
  fun z₁ z₂ =>
    if dir then (if z₂ = lvl then α else (if z₁ then β₁ else β₀))
    else (if z₁ = lvl then α else (if z₂ then β₁ else β₀))

/-- **Face classification.** For any two line-constant square functions,
    one of: (1) a same-inputs pair with opposite parity — the Boolean kill;
    (2)/(3) crossed dictators (both orientations) — the LP kill;
    (4) ±indicators at antipodal corners — the only genuine survivor. -/
theorem face_classify : ∀ d₁ l₁ a₁ p₁ q₁ d₂ l₂ a₂ p₂ q₂ : Bool,
    (∃ z₁ z₂ z₁' z₂', xor z₁ z₂ ≠ xor z₁' z₂' ∧
      lineFn d₁ l₁ a₁ p₁ q₁ z₁ z₂ = lineFn d₁ l₁ a₁ p₁ q₁ z₁' z₂' ∧
      lineFn d₂ l₂ a₂ p₂ q₂ z₁ z₂ = lineFn d₂ l₂ a₂ p₂ q₂ z₁' z₂') ∨
    (∃ ε₁ ε₂, (∀ z₁ z₂, lineFn d₁ l₁ a₁ p₁ q₁ z₁ z₂ = xor ε₁ z₁) ∧
      (∀ z₁ z₂, lineFn d₂ l₂ a₂ p₂ q₂ z₁ z₂ = xor ε₂ z₂)) ∨
    (∃ ε₁ ε₂, (∀ z₁ z₂, lineFn d₁ l₁ a₁ p₁ q₁ z₁ z₂ = xor ε₁ z₂) ∧
      (∀ z₁ z₂, lineFn d₂ l₂ a₂ p₂ q₂ z₁ z₂ = xor ε₂ z₁)) ∨
    (∃ u₁ u₂ ε₁ ε₂,
      (∀ z₁ z₂, lineFn d₁ l₁ a₁ p₁ q₁ z₁ z₂
        = xor ε₁ (decide (z₁ = u₁) && decide (z₂ = u₂))) ∧
      (∀ z₁ z₂, lineFn d₂ l₂ a₂ p₂ q₂ z₁ z₂
        = xor ε₂ (decide (z₁ = !u₁) && decide (z₂ = !u₂)))) := by
  decide

/-- **Fourth point.** A line-constant square function taking value `!g` at
    one corner and `g` at both neighbors takes `g` at the antipode. -/
theorem lineFn_fourth : ∀ d l a p q l₁ l₂ g : Bool,
    lineFn d l a p q l₁ l₂ = !g → lineFn d l a p q l₁ (!l₂) = g →
    lineFn d l a p q (!l₁) l₂ = g → lineFn d l a p q (!l₁) (!l₂) = g := by
  decide

/-- **Row alignment.** A line-constant square function whose two rows are
    single-flip patterns must have the flips in the same column. -/
theorem lineFn_align : ∀ d l a p q ρ ρ' g β : Bool,
    (∀ z, lineFn d l a p q β z = xor g (decide (z = ρ))) →
    (∀ z, lineFn d l a p q (!β) z = xor g (decide (z = ρ'))) → ρ = ρ' := by
  decide

/-! ## §3 The two real-arithmetic kills -/

/-- 4-point clash on one face: equal-parity corners must agree in sign, the
    cross-sums coincide, contradiction. Kills crossed dictators. -/
theorem four_point_clash (L : Bool) (X00 X01 X10 X11 : ℝ)
    (hsum : X00 + X11 = X01 + X10)
    (h00 : L = true ↔ 0 < X00) (h11 : L = true ↔ 0 < X11)
    (h01 : L = false ↔ 0 < X01) (h10 : L = false ↔ 0 < X10) : False := by
  cases L with
  | true =>
      have hx00 := h00.mp rfl
      have hx11 := h11.mp rfl
      have hx01 : ¬ 0 < X01 := fun h => by simpa using h01.mpr h
      have hx10 : ¬ 0 < X10 := fun h => by simpa using h10.mpr h
      push_neg at hx01 hx10
      linarith
  | false =>
      have hx01 := h01.mp rfl
      have hx10 := h10.mp rfl
      have hx00 : ¬ 0 < X00 := fun h => by simpa using h00.mpr h
      have hx11 : ¬ 0 < X11 := fun h => by simpa using h11.mpr h
      push_neg at hx00 hx11
      linarith

/-- 2-face sign clash: the same weighted flip must point both ways across
    complementary faces carrying complementary parities. Kills case 2b. -/
theorem two_face_clash (π : Bool) (X Y X' Y' : ℝ) (hdiff : Y - X = Y' - X')
    (hX : π = true ↔ 0 < X) (hY : π = false ↔ 0 < Y)
    (hX' : π = false ↔ 0 < X') (hY' : π = true ↔ 0 < Y') : False := by
  cases π with
  | true =>
      have h1 := hX.mp rfl
      have h4 := hY'.mp rfl
      have h2 : ¬ 0 < Y := fun h => by simpa using hY.mpr h
      have h3 : ¬ 0 < X' := fun h => by simpa using hX'.mpr h
      push_neg at h2 h3
      linarith
  | false =>
      have h2 := hY.mp rfl
      have h3 := hX'.mp rfl
      have h1 : ¬ 0 < X := fun h => by simpa using hX.mpr h
      have h4 : ¬ 0 < Y' := fun h => by simpa using hY'.mpr h
      push_neg at h1 h4
      linarith

/-! ## §4 Extraction from `headOutput_fixable` -/

/-- Every head output is constant on a half-cube (top-priority literal). -/
theorem head_const_halfcube {d : ℕ} (h : HardAttentionHead 3 d) :
    ∃ i b c, ∀ x : Fin 3 → Bool, x i = b → headOutput h x = c := by
  obtain ⟨i, b, -, c, hc⟩ := headOutput_fixable h (fun _ => none)
  exact ⟨i, b, c, fun x hx => hc x (fun _ _ hmem => nomatch hmem) hx⟩

/-- Every head output restricted to a 2-face is constant on a line of the
    face — or on the whole face when the pinned literal is the face's own
    coordinate (`i = d → v = b`). -/
theorem head_face_line {d : ℕ} (h : HardAttentionHead 3 d) (dd : Fin 3)
    (v : Bool) :
    ∃ i b c, (i = dd → v = b) ∧
      ∀ x : Fin 3 → Bool, x dd = v → x i = b → headOutput h x = c := by
  obtain ⟨i, b, hexcl, c, hc⟩ :=
    headOutput_fixable h (fun m => if m = dd then some v else none)
  refine ⟨i, b, c, ?_, ?_⟩
  · intro hid
    subst hid
    by_contra hne
    apply hexcl
    rw [if_pos rfl]
    cases v <;> cases b <;> simp_all
  · intro x hxd hxi
    refine hc x ?_ hxi
    intro m bm hm
    have hm' : (if m = dd then some v else none) = some bm := hm
    by_cases hmd : m = dd
    · subst hmd
      rw [if_pos rfl] at hm'
      cases hm'
      exact hxd
    · rw [if_neg hmd] at hm'
      cases hm'

/-! ## §5 The face workhorse

On a face carrying ±XOR through a two-summand threshold, two line-constant
restrictions must be ±indicators at antipodal corners: the Boolean kill and
both crossed-dictator branches of `face_classify` are discharged here. -/

theorem face_resolve (fβ : Bool) (K wP wQ : ℝ)
    (dP lP aP uP vP dQ lQ aQ uQ vQ : Bool)
    (hypF : ∀ z₁ z₂, (xor fβ (xor z₁ z₂) = true ↔
      0 < K + wP * (if lineFn dP lP aP uP vP z₁ z₂ then (1 : ℝ) else 0)
            + wQ * (if lineFn dQ lQ aQ uQ vQ z₁ z₂ then (1 : ℝ) else 0))) :
    ∃ u₁ u₂ εP εQ,
      (∀ z₁ z₂, lineFn dP lP aP uP vP z₁ z₂
        = xor εP (decide (z₁ = u₁) && decide (z₂ = u₂))) ∧
      (∀ z₁ z₂, lineFn dQ lQ aQ uQ vQ z₁ z₂
        = xor εQ (decide (z₁ = !u₁) && decide (z₂ = !u₂))) := by
  rcases face_classify dP lP aP uP vP dQ lQ aQ uQ vQ with
    ⟨z₁, z₂, z₁', z₂', hne, hP, hQ⟩ | ⟨ε₁, ε₂, hP, hQ⟩ | ⟨ε₁, ε₂, hP, hQ⟩ | hInd
  · -- Boolean same-inputs kill
    exfalso
    have h1 := hypF z₁ z₂
    have h2 := hypF z₁' z₂'
    rw [hP, hQ] at h1
    exact bool_iff_ne_kill fβ _ _ hne (h1.trans h2.symm)
  · -- crossed dictators, orientation P ~ z₁, Q ~ z₂
    exfalso
    have h00 := hypF false false
    have h01 := hypF false true
    have h10 := hypF true false
    have h11 := hypF true true
    rw [hP, hQ] at h00 h01 h10 h11
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false] at h00 h01 h10 h11
    refine four_point_clash fβ
      (K + wP * (if ε₁ then (1 : ℝ) else 0) + wQ * (if ε₂ then (1 : ℝ) else 0))
      (K + wP * (if ε₁ then (1 : ℝ) else 0) + wQ * (if !ε₂ then (1 : ℝ) else 0))
      (K + wP * (if !ε₁ then (1 : ℝ) else 0) + wQ * (if ε₂ then (1 : ℝ) else 0))
      (K + wP * (if !ε₁ then (1 : ℝ) else 0) + wQ * (if !ε₂ then (1 : ℝ) else 0))
      (by ring) h00 h11 ?_ ?_
    · simpa using h01
    · simpa using h10
  · -- crossed dictators, orientation P ~ z₂, Q ~ z₁
    exfalso
    have h00 := hypF false false
    have h01 := hypF false true
    have h10 := hypF true false
    have h11 := hypF true true
    rw [hP, hQ] at h00 h01 h10 h11
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false] at h00 h01 h10 h11
    refine four_point_clash fβ
      (K + wP * (if ε₁ then (1 : ℝ) else 0) + wQ * (if ε₂ then (1 : ℝ) else 0))
      (K + wP * (if !ε₁ then (1 : ℝ) else 0) + wQ * (if ε₂ then (1 : ℝ) else 0))
      (K + wP * (if ε₁ then (1 : ℝ) else 0) + wQ * (if !ε₂ then (1 : ℝ) else 0))
      (K + wP * (if !ε₁ then (1 : ℝ) else 0) + wQ * (if !ε₂ then (1 : ℝ) else 0))
      (by ring) h00 h11 ?_ ?_
    · simpa using h01
    · simpa using h10
  · exact hInd

/-! ## §6 Hypothesis plumbing and the same-inputs kill -/

/-- Convert the frozen if-then-else form into the working iff form. -/
theorem hyp_iff_of_ite {S : (Fin 3 → Bool) → ℝ}
    (h : ∀ x, (if S x > 0 then true else false) = parityN x) :
    ∀ x, parityN x = true ↔ 0 < S x := by
  intro x
  have hx := h x
  by_cases hs : S x > 0
  · rw [if_pos hs] at hx
    exact ⟨fun _ => hs, fun _ => hx.symm⟩
  · rw [if_neg hs] at hx
    constructor
    · intro hp
      rw [← hx] at hp
      cases hp
    · intro h0
      exact absurd h0 hs

/-- **Same-inputs kill.** Two points with identical head vectors but
    different parity refute the threshold hypothesis. -/
theorem kill3 {A B C : (Fin 3 → Bool) → Bool} {wa wb wc bias : ℝ}
    (hyp : ∀ x, parityN x = true ↔
      0 < wa * (if A x then (1 : ℝ) else 0) + wb * (if B x then (1 : ℝ) else 0)
        + wc * (if C x then (1 : ℝ) else 0) + bias)
    (x y : Fin 3 → Bool) (hA : A x = A y) (hB : B x = B y) (hC : C x = C y)
    (hpar : parityN x ≠ parityN y) : False := by
  -- the collision ⇒ non-computation kernel, instantiated at the heads'
  -- Boolean shadows and the thresholded affine readout
  apply witness_separation_fails parityN (fun i => ![A, B, C] i)
    (fun v => if 0 < wa * (if v 0 then (1 : ℝ) else 0)
      + wb * (if v 1 then (1 : ℝ) else 0)
      + wc * (if v 2 then (1 : ℝ) else 0) + bias then true else false)
    x y ?_ hpar
  · -- the threshold computes parityN, pointwise from the iff hypothesis
    funext s
    show (if 0 < wa * (if A s then (1 : ℝ) else 0)
      + wb * (if B s then (1 : ℝ) else 0)
      + wc * (if C s then (1 : ℝ) else 0) + bias then true else false)
      = parityN s
    by_cases hs : 0 < wa * (if A s then (1 : ℝ) else 0)
        + wb * (if B s then (1 : ℝ) else 0)
        + wc * (if C s then (1 : ℝ) else 0) + bias
    · rw [if_pos hs]
      exact ((hyp s).mpr hs).symm
    · rw [if_neg hs]
      cases hp : parityN s
      · rfl
      · exact absurd ((hyp s).mp hp) hs
  · -- the witness collision
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hC

/-- Package a face restriction as one of the 32 `lineFn` shapes, from the
    face-line extraction data. -/
theorem restr_lineFn (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (G : (Fin 3 → Bool) → Bool) (β : Bool)
    (i : Fin 3) (b c : Bool) (hib : i = p → β = b)
    (hline : ∀ x, x p = β → x i = b → G x = c) :
    ∃ d l a v₀ v₁, ∀ z₁ z₂,
      G (pt3 p β q z₁ r z₂) = lineFn d l a v₀ v₁ z₁ z₂ := by
  rcases fin3_complete p q r hpq hpr hqr i with hi | hi | hi
  · -- pinned literal is the face coordinate: constant on the whole face
    subst hi
    have hb : β = b := hib rfl
    refine ⟨false, false, c, c, c, fun z₁ z₂ => ?_⟩
    have hG : G (pt3 i β q z₁ r z₂) = c :=
      hline _ (pt3_fst i q r hpq hpr hqr β z₁ z₂)
        (by rw [pt3_fst i q r hpq hpr hqr, ← hb])
    rw [hG]
    simp [lineFn]
  · -- pinned literal is the first free coordinate: row-constant
    subst hi
    refine ⟨false, b, c, G (pt3 p β i (!b) r false), G (pt3 p β i (!b) r true),
      fun z₁ z₂ => ?_⟩
    by_cases hz : z₁ = b
    · subst hz
      rw [hline _ (pt3_fst p i r hpq hpr hqr β z₁ z₂)
        (pt3_snd p i r hpq hpr hqr β z₁ z₂)]
      simp [lineFn]
    · have hz' : z₁ = !b := (bool_ne_iff z₁ b).mp hz
      subst hz'
      cases z₂ <;> simp [lineFn, hz]
  · -- pinned literal is the second free coordinate: column-constant
    subst hi
    refine ⟨true, b, c, G (pt3 p β q false i (!b)), G (pt3 p β q true i (!b)),
      fun z₁ z₂ => ?_⟩
    by_cases hz : z₂ = b
    · subst hz
      rw [hline _ (pt3_fst p q i hpq hpr hqr β z₁ z₂)
        (pt3_thd p q i hpq hpr hqr β z₁ z₂)]
      simp [lineFn]
    · have hz' : z₂ = !b := (bool_ne_iff z₂ b).mp hz
      subst hz'
      cases z₁ <;> simp [lineFn, hz]

/-! ## §7 The three cases -/

section Cases

variable {A B C : (Fin 3 → Bool) → Bool} {wa wb wc bias : ℝ}

/-- **Case 1 — two heads share a signed constancy direction.** On the shared
    face only the third head can vary, and it is constant on a line: the
    line's two points differ in one coordinate, flipping parity but no head. -/
theorem case_shared
    (hyp : ∀ x, parityN x = true ↔
      0 < wa * (if A x then (1 : ℝ) else 0) + wb * (if B x then (1 : ℝ) else 0)
        + wc * (if C x then (1 : ℝ) else 0) + bias)
    (p : Fin 3) (β : Bool) (ca cb : Bool)
    (hA : ∀ x, x p = β → A x = ca) (hB : ∀ x, x p = β → B x = cb)
    (hlineC : ∃ i b c, (i = p → β = b) ∧ ∀ x, x p = β → x i = b → C x = c) :
    False := by
  obtain ⟨q, r, hpq, hpr, hqr⟩ := fin3_two_others p
  obtain ⟨i, b, c, hib, hC⟩ := hlineC
  rcases fin3_complete p q r hpq hpr hqr i with hi | hi | hi
  · -- whole-face constant: flip along q
    subst hi
    have hb : β = b := hib rfl
    have h₁ : (pt3 i β q false r false) i = β := pt3_fst i q r hpq hpr hqr _ _ _
    have h₂ : (pt3 i β q true r false) i = β := pt3_fst i q r hpq hpr hqr _ _ _
    refine kill3 hyp (pt3 i β q false r false) (pt3 i β q true r false)
      ?_ ?_ ?_ ?_
    · rw [hA _ h₁, hA _ h₂]
    · rw [hB _ h₁, hB _ h₂]
    · rw [hC _ h₁ (hb ▸ h₁), hC _ h₂ (hb ▸ h₂)]
    · rw [parityN_pt3 i q r hpq hpr hqr, parityN_pt3 i q r hpq hpr hqr]
      exact parity_flip_q β false
  · -- line along the q-coordinate: flip along r
    subst hi
    have h₁ : (pt3 p β i b r false) p = β := pt3_fst p i r hpq hpr hqr _ _ _
    have h₂ : (pt3 p β i b r true) p = β := pt3_fst p i r hpq hpr hqr _ _ _
    refine kill3 hyp (pt3 p β i b r false) (pt3 p β i b r true) ?_ ?_ ?_ ?_
    · rw [hA _ h₁, hA _ h₂]
    · rw [hB _ h₁, hB _ h₂]
    · rw [hC _ h₁ (pt3_snd p i r hpq hpr hqr _ _ _),
        hC _ h₂ (pt3_snd p i r hpq hpr hqr _ _ _)]
    · rw [parityN_pt3 p i r hpq hpr hqr, parityN_pt3 p i r hpq hpr hqr]
      exact parity_flip_r β b
  · -- line along the r-coordinate: flip along q
    subst hi
    have h₁ : (pt3 p β q false i b) p = β := pt3_fst p q i hpq hpr hqr _ _ _
    have h₂ : (pt3 p β q true i b) p = β := pt3_fst p q i hpq hpr hqr _ _ _
    refine kill3 hyp (pt3 p β q false i b) (pt3 p β q true i b) ?_ ?_ ?_ ?_
    · rw [hA _ h₁, hA _ h₂]
    · rw [hB _ h₁, hB _ h₂]
    · rw [hC _ h₁ (pt3_thd p q i hpq hpr hqr _ _ _),
        hC _ h₂ (pt3_thd p q i hpq hpr hqr _ _ _)]
    · rw [parityN_pt3 p q i hpq hpr hqr, parityN_pt3 p q i hpq hpr hqr]
      exact parity_flip_q β b

/-- **Case 2b — two heads share a direction with opposite signs, the third
    sits elsewhere.** The third head's indicator corners on the two
    complementary faces must be aligned, and the complementary target
    parities force its weighted flip to point both ways. -/
theorem case_2b
    (hyp : ∀ x, parityN x = true ↔
      0 < wa * (if A x then (1 : ℝ) else 0) + wb * (if B x then (1 : ℝ) else 0)
        + wc * (if C x then (1 : ℝ) else 0) + bias)
    (p q : Fin 3) (hpq : p ≠ q) (β γ : Bool) (ca cb cc : Bool)
    (hA : ∀ x, x p = β → A x = ca)
    (hB : ∀ x, x p = !β → B x = cb)
    (hC : ∀ x, x q = γ → C x = cc)
    (hlineA : ∀ dd v, ∃ i b c, (i = dd → v = b) ∧
      ∀ x, x dd = v → x i = b → A x = c)
    (hlineB : ∀ dd v, ∃ i b c, (i = dd → v = b) ∧
      ∀ x, x dd = v → x i = b → B x = c)
    (hlineC : ∀ dd v, ∃ i b c, (i = dd → v = b) ∧
      ∀ x, x dd = v → x i = b → C x = c) :
    False := by
  obtain ⟨r, hrp, hrq, -⟩ := fin3_third p q hpq
  have hpr : p ≠ r := hrp.symm
  have hqr : q ≠ r := hrq.symm
  -- Φ_A = face (p, β): restrictions of B and C
  obtain ⟨i₁, b₁, c₁, hib₁, hl₁⟩ := hlineB p β
  obtain ⟨dB, lB, aB, uBp, vBp, hRB⟩ :=
    restr_lineFn p q r hpq hpr hqr B β i₁ b₁ c₁ hib₁ hl₁
  have hCA : ∀ x, x p = β → x q = γ → C x = cc := fun x _ h => hC x h
  obtain ⟨dC, lC, aC, uCp, vCp, hRC⟩ :=
    restr_lineFn p q r hpq hpr hqr C β q γ cc (fun h => absurd h.symm hpq) hCA
  have hypFA : ∀ z₁ z₂, (xor β (xor z₁ z₂) = true ↔
      0 < (wa * (if ca then (1 : ℝ) else 0) + bias)
        + wb * (if lineFn dB lB aB uBp vBp z₁ z₂ then (1 : ℝ) else 0)
        + wc * (if lineFn dC lC aC uCp vCp z₁ z₂ then (1 : ℝ) else 0)) := by
    intro z₁ z₂
    have h := hyp (pt3 p β q z₁ r z₂)
    rw [parityN_pt3 p q r hpq hpr hqr] at h
    rw [hA _ (pt3_fst p q r hpq hpr hqr _ _ _), hRB z₁ z₂, hRC z₁ z₂] at h
    exact h.trans (by constructor <;> intro <;> linarith)
  obtain ⟨u₁, u₂, εB, εC, hiB, hiC⟩ :=
    face_resolve β _ wb wc _ _ _ _ _ _ _ _ _ _ hypFA
  -- pin C's corner on Φ_A: the z₁ = γ row is constant cc
  obtain ⟨hu₁, hεC⟩ : (!u₁) = !γ ∧ εC = cc := by
    apply ind_row_pin
    intro z₂
    rw [← hiC γ z₂, ← hRC γ z₂]
    exact hCA _ (pt3_fst p q r hpq hpr hqr _ _ _)
      (pt3_snd p q r hpq hpr hqr _ _ _)
  have hu₁' : u₁ = γ := bool_not_inj _ _ hu₁
  -- Φ_B = face (p, !β): restrictions of A and C
  obtain ⟨i₂, b₂, c₂, hib₂, hl₂⟩ := hlineA p (!β)
  obtain ⟨dA, lA, aA, uAp, vAp, hRA⟩ :=
    restr_lineFn p q r hpq hpr hqr A (!β) i₂ b₂ c₂ hib₂ hl₂
  have hCB : ∀ x, x p = !β → x q = γ → C x = cc := fun x _ h => hC x h
  obtain ⟨dC', lC', aC', uCp', vCp', hRC'⟩ :=
    restr_lineFn p q r hpq hpr hqr C (!β) q γ cc (fun h => absurd h.symm hpq) hCB
  have hypFB : ∀ z₁ z₂, (xor (!β) (xor z₁ z₂) = true ↔
      0 < (wb * (if cb then (1 : ℝ) else 0) + bias)
        + wa * (if lineFn dA lA aA uAp vAp z₁ z₂ then (1 : ℝ) else 0)
        + wc * (if lineFn dC' lC' aC' uCp' vCp' z₁ z₂ then (1 : ℝ) else 0)) := by
    intro z₁ z₂
    have h := hyp (pt3 p (!β) q z₁ r z₂)
    rw [parityN_pt3 p q r hpq hpr hqr] at h
    rw [hB _ (pt3_fst p q r hpq hpr hqr _ _ _), hRA z₁ z₂, hRC' z₁ z₂] at h
    exact h.trans (by constructor <;> intro <;> linarith)
  obtain ⟨u₁', u₂', εA, εC', hiA, hiC'⟩ :=
    face_resolve (!β) _ wa wc _ _ _ _ _ _ _ _ _ _ hypFB
  obtain ⟨hu₁c, hεC'⟩ : (!u₁') = !γ ∧ εC' = cc := by
    apply ind_row_pin
    intro z₂
    rw [← hiC' γ z₂, ← hRC' γ z₂]
    exact hCB _ (pt3_fst p q r hpq hpr hqr _ _ _)
      (pt3_snd p q r hpq hpr hqr _ _ _)
  have hu₁c' : u₁' = γ := bool_not_inj _ _ hu₁c
  -- alignment through C's remaining face (q, !γ)
  obtain ⟨i₃, b₃, c₃, hib₃, hl₃⟩ := hlineC q (!γ)
  obtain ⟨dX, lX, aX, uX, vX, hRX⟩ :=
    restr_lineFn q p r hpq.symm hqr hpr C (!γ) i₃ b₃ c₃ hib₃ hl₃
  have hrow₁ : ∀ z, lineFn dX lX aX uX vX β z = xor cc (decide (z = !u₂)) := by
    intro z
    rw [← hRX β z, pt3_comm p q r hpq hpr hqr β (!γ) z, hRC (!γ) z, hiC (!γ) z,
      hu₁, hεC]
    simp
  have hrow₂ : ∀ z, lineFn dX lX aX uX vX (!β) z = xor cc (decide (z = !u₂')) := by
    intro z
    rw [← hRX (!β) z, pt3_comm p q r hpq hpr hqr (!β) (!γ) z, hRC' (!γ) z,
      hiC' (!γ) z, hu₁c, hεC']
    simp
  have hρ : (!u₂) = !u₂' := lineFn_align dX lX aX uX vX (!u₂) (!u₂') cc β hrow₁ hrow₂
  have hu₂eq : u₂ = u₂' := bool_not_inj _ _ hρ
  -- the four points of the sign clash, all at z₂ = !u₂
  have hBX : B (pt3 p β q γ r (!u₂)) = εB := by
    rw [hRB, hiB, hu₁']
    simp
  have hBY : B (pt3 p β q (!γ) r (!u₂)) = εB := by
    rw [hRB, hiB, hu₁']
    simp
  have hAX : A (pt3 p (!β) q γ r (!u₂)) = εA := by
    rw [hRA, hiA, hu₁c', ← hu₂eq]
    simp
  have hAY : A (pt3 p (!β) q (!γ) r (!u₂)) = εA := by
    rw [hRA, hiA, hu₁c', ← hu₂eq]
    simp
  have hCX : C (pt3 p β q γ r (!u₂)) = cc :=
    hC _ (pt3_snd p q r hpq hpr hqr _ _ _)
  have hCY : C (pt3 p β q (!γ) r (!u₂)) = !cc := by
    rw [hRC, hiC, hu₁, hεC]
    simp
  have hCX' : C (pt3 p (!β) q γ r (!u₂)) = cc :=
    hC _ (pt3_snd p q r hpq hpr hqr _ _ _)
  have hCY' : C (pt3 p (!β) q (!γ) r (!u₂)) = !cc := by
    rw [hRC', hiC', hu₁c, hεC', ← hρ]
    simp
  -- hypothesis instances at the four points
  have hX := hyp (pt3 p β q γ r (!u₂))
  have hY := hyp (pt3 p β q (!γ) r (!u₂))
  have hX' := hyp (pt3 p (!β) q γ r (!u₂))
  have hY' := hyp (pt3 p (!β) q (!γ) r (!u₂))
  rw [parityN_pt3 p q r hpq hpr hqr,
    hA _ (pt3_fst p q r hpq hpr hqr _ _ _), hBX, hCX] at hX
  rw [parityN_pt3 p q r hpq hpr hqr,
    hA _ (pt3_fst p q r hpq hpr hqr _ _ _), hBY, hCY, xor_q_flip] at hY
  rw [parityN_pt3 p q r hpq hpr hqr,
    hB _ (pt3_fst p q r hpq hpr hqr _ _ _), hAX, hCX', xor_p_flip] at hX'
  rw [parityN_pt3 p q r hpq hpr hqr,
    hB _ (pt3_fst p q r hpq hpr hqr _ _ _), hAY, hCY', xor_q_flip,
    xor_p_flip, Bool.not_not] at hY'
  exact two_face_clash (xor β (xor γ (!u₂))) _ _ _ _ (by ring)
    hX (iff_flip hY) (iff_flip hX') hY'

/-- **Case 3 — all three constancy directions distinct.** Antipodality on the
    three constancy faces forces every head to be a ±point-indicator at a
    neighbor of `T = (βa, βb, βc)`; then `T` and its antipode carry identical
    head vectors but opposite parity. -/
theorem case_3
    (hyp : ∀ x, parityN x = true ↔
      0 < wa * (if A x then (1 : ℝ) else 0) + wb * (if B x then (1 : ℝ) else 0)
        + wc * (if C x then (1 : ℝ) else 0) + bias)
    (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (βa βb βc ca cb cc : Bool)
    (hA : ∀ x, x p = βa → A x = ca)
    (hB : ∀ x, x q = βb → B x = cb)
    (hC : ∀ x, x r = βc → C x = cc)
    (hlineA : ∀ dd v, ∃ i b c, (i = dd → v = b) ∧
      ∀ x, x dd = v → x i = b → A x = c)
    (hlineB : ∀ dd v, ∃ i b c, (i = dd → v = b) ∧
      ∀ x, x dd = v → x i = b → B x = c)
    (hlineC : ∀ dd v, ∃ i b c, (i = dd → v = b) ∧
      ∀ x, x dd = v → x i = b → C x = c) :
    False := by
  -- Φ_A = face (p, βa), coords (z₁, z₂) = (x q, x r); P := B|, Q := C|
  have hBA : ∀ x, x p = βa → x q = βb → B x = cb := fun x _ h => hB x h
  obtain ⟨dB, lB, aB, uBp, vBp, hRB⟩ :=
    restr_lineFn p q r hpq hpr hqr B βa q βb cb (fun h => absurd h.symm hpq) hBA
  have hCA : ∀ x, x p = βa → x r = βc → C x = cc := fun x _ h => hC x h
  obtain ⟨dC, lC, aC, uCp, vCp, hRC⟩ :=
    restr_lineFn p q r hpq hpr hqr C βa r βc cc (fun h => absurd h.symm hpr) hCA
  have hypFA : ∀ z₁ z₂, (xor βa (xor z₁ z₂) = true ↔
      0 < (wa * (if ca then (1 : ℝ) else 0) + bias)
        + wb * (if lineFn dB lB aB uBp vBp z₁ z₂ then (1 : ℝ) else 0)
        + wc * (if lineFn dC lC aC uCp vCp z₁ z₂ then (1 : ℝ) else 0)) := by
    intro z₁ z₂
    have h := hyp (pt3 p βa q z₁ r z₂)
    rw [parityN_pt3 p q r hpq hpr hqr] at h
    rw [hA _ (pt3_fst p q r hpq hpr hqr _ _ _), hRB z₁ z₂, hRC z₁ z₂] at h
    exact h.trans (by constructor <;> intro <;> linarith)
  obtain ⟨u₁, u₂, εB, εC, hiB, hiC⟩ :=
    face_resolve βa _ wb wc _ _ _ _ _ _ _ _ _ _ hypFA
  obtain ⟨hBu₁, hεB⟩ : u₁ = !βb ∧ εB = cb := by
    apply ind_row_pin
    intro z₂
    rw [← hiB βb z₂, ← hRB βb z₂]
    exact hBA _ (pt3_fst p q r hpq hpr hqr _ _ _)
      (pt3_snd p q r hpq hpr hqr _ _ _)
  obtain ⟨hCu₂, hεC⟩ : (!u₂) = !βc ∧ εC = cc := by
    apply ind_col_pin
    intro z₁
    rw [← hiC z₁ βc, ← hRC z₁ βc]
    exact hCA _ (pt3_fst p q r hpq hpr hqr _ _ _)
      (pt3_thd p q r hpq hpr hqr _ _ _)
  have hu₂ : u₂ = βc := bool_not_inj _ _ hCu₂
  -- Φ_B = face (q, βb), coords (z₁, z₂) = (x p, x r); P := A|, Q := C|
  have hAB : ∀ x, x q = βb → x p = βa → A x = ca := fun x _ h => hA x h
  obtain ⟨dA2, lA2, aA2, uA2, vA2, hRA2⟩ :=
    restr_lineFn q p r hpq.symm hqr hpr A βb p βa ca (fun h => absurd h hpq) hAB
  have hCB : ∀ x, x q = βb → x r = βc → C x = cc := fun x _ h => hC x h
  obtain ⟨dC2, lC2, aC2, uC2, vC2, hRC2⟩ :=
    restr_lineFn q p r hpq.symm hqr hpr C βb r βc cc
      (fun h => absurd h.symm hqr) hCB
  have hypFB : ∀ z₁ z₂, (xor βb (xor z₁ z₂) = true ↔
      0 < (wb * (if cb then (1 : ℝ) else 0) + bias)
        + wa * (if lineFn dA2 lA2 aA2 uA2 vA2 z₁ z₂ then (1 : ℝ) else 0)
        + wc * (if lineFn dC2 lC2 aC2 uC2 vC2 z₁ z₂ then (1 : ℝ) else 0)) := by
    intro z₁ z₂
    have h := hyp (pt3 q βb p z₁ r z₂)
    rw [parityN_pt3 q p r hpq.symm hqr hpr] at h
    rw [hB _ (pt3_fst q p r hpq.symm hqr hpr _ _ _), hRA2 z₁ z₂, hRC2 z₁ z₂] at h
    exact h.trans (by constructor <;> intro <;> linarith)
  obtain ⟨u₁', u₂', εA2, εC2, hiA2, hiC2⟩ :=
    face_resolve βb _ wa wc _ _ _ _ _ _ _ _ _ _ hypFB
  obtain ⟨hAu₁', hεA2⟩ : u₁' = !βa ∧ εA2 = ca := by
    apply ind_row_pin
    intro z₂
    rw [← hiA2 βa z₂, ← hRA2 βa z₂]
    exact hAB _ (pt3_fst q p r hpq.symm hqr hpr _ _ _)
      (pt3_snd q p r hpq.symm hqr hpr _ _ _)
  obtain ⟨hCu₂', hεC2⟩ : (!u₂') = !βc ∧ εC2 = cc := by
    apply ind_col_pin
    intro z₁
    rw [← hiC2 z₁ βc, ← hRC2 z₁ βc]
    exact hCB _ (pt3_fst q p r hpq.symm hqr hpr _ _ _)
      (pt3_thd q p r hpq.symm hqr hpr _ _ _)
  have hu₂' : u₂' = βc := bool_not_inj _ _ hCu₂'
  -- Φ_C = face (r, βc), coords (z₁, z₂) = (x p, x q); P := A|, Q := B|
  have hAC : ∀ x, x r = βc → x p = βa → A x = ca := fun x _ h => hA x h
  obtain ⟨dA3, lA3, aA3, uA3, vA3, hRA3⟩ :=
    restr_lineFn r p q hpr.symm hqr.symm hpq A βc p βa ca
      (fun h => absurd h hpr) hAC
  have hBC : ∀ x, x r = βc → x q = βb → B x = cb := fun x _ h => hB x h
  obtain ⟨dB3, lB3, aB3, uB3, vB3, hRB3⟩ :=
    restr_lineFn r p q hpr.symm hqr.symm hpq B βc q βb cb
      (fun h => absurd h hqr) hBC
  have hypFC : ∀ z₁ z₂, (xor βc (xor z₁ z₂) = true ↔
      0 < (wc * (if cc then (1 : ℝ) else 0) + bias)
        + wa * (if lineFn dA3 lA3 aA3 uA3 vA3 z₁ z₂ then (1 : ℝ) else 0)
        + wb * (if lineFn dB3 lB3 aB3 uB3 vB3 z₁ z₂ then (1 : ℝ) else 0)) := by
    intro z₁ z₂
    have h := hyp (pt3 r βc p z₁ q z₂)
    rw [parityN_pt3 r p q hpr.symm hqr.symm hpq] at h
    rw [hC _ (pt3_fst r p q hpr.symm hqr.symm hpq _ _ _), hRA3 z₁ z₂,
      hRB3 z₁ z₂] at h
    exact h.trans (by constructor <;> intro <;> linarith)
  obtain ⟨u₁'', u₂'', εA3, εB3, hiA3, hiB3⟩ :=
    face_resolve βc _ wa wb _ _ _ _ _ _ _ _ _ _ hypFC
  obtain ⟨hAu₁'', hεA3⟩ : u₁'' = !βa ∧ εA3 = ca := by
    apply ind_row_pin
    intro z₂
    rw [← hiA3 βa z₂, ← hRA3 βa z₂]
    exact hAC _ (pt3_fst r p q hpr.symm hqr.symm hpq _ _ _)
      (pt3_snd r p q hpr.symm hqr.symm hpq _ _ _)
  obtain ⟨hBu₂'', hεB3⟩ : (!u₂'') = !βb ∧ εB3 = cb := by
    apply ind_col_pin
    intro z₁
    rw [← hiB3 z₁ βb, ← hRB3 z₁ βb]
    exact hBC _ (pt3_fst r p q hpr.symm hqr.symm hpq _ _ _)
      (pt3_thd r p q hpr.symm hqr.symm hpq _ _ _)
  have hu₂'' : u₂'' = βb := bool_not_inj _ _ hBu₂''
  -- A's values on its opposite face (p, !βa), then the fourth point
  have hA1 : A (pt3 p (!βa) q βb r βc) = !ca := by
    rw [← pt3_comm p q r hpq hpr hqr (!βa) βb βc, hRA2 (!βa) βc,
      hiA2 (!βa) βc, hAu₁', hu₂']
    simp [hεA2]
  have hA2v : A (pt3 p (!βa) q βb r (!βc)) = ca := by
    rw [← pt3_comm p q r hpq hpr hqr (!βa) βb (!βc), hRA2 (!βa) (!βc),
      hiA2 (!βa) (!βc), hAu₁', hu₂']
    simp [hεA2]
  have hA3v : A (pt3 p (!βa) q (!βb) r βc) = ca := by
    rw [← pt3_rot p q r hpq hpr hqr (!βa) (!βb) βc, hRA3 (!βa) (!βb),
      hiA3 (!βa) (!βb), hAu₁'', hu₂'']
    simp [hεA3]
  obtain ⟨iA, bA, cA4, hibA, hlA⟩ := hlineA p (!βa)
  obtain ⟨dA4, lA4, aA4, uA4, vA4, hRA4⟩ :=
    restr_lineFn p q r hpq hpr hqr A (!βa) iA bA cA4 hibA hlA
  have hA4 : A (pt3 p (!βa) q (!βb) r (!βc)) = ca := by
    have k1 : lineFn dA4 lA4 aA4 uA4 vA4 βb βc = !ca := by
      rw [← hRA4 βb βc]; exact hA1
    have k2 : lineFn dA4 lA4 aA4 uA4 vA4 βb (!βc) = ca := by
      rw [← hRA4 βb (!βc)]; exact hA2v
    have k3 : lineFn dA4 lA4 aA4 uA4 vA4 (!βb) βc = ca := by
      rw [← hRA4 (!βb) βc]; exact hA3v
    rw [hRA4 (!βb) (!βc)]
    exact lineFn_fourth dA4 lA4 aA4 uA4 vA4 βb βc ca k1 k2 k3
  -- B's values on its opposite face (q, !βb), then the fourth point
  have hB1 : B (pt3 q (!βb) p βa r βc) = !cb := by
    rw [pt3_comm p q r hpq hpr hqr βa (!βb) βc, hRB (!βb) βc, hiB (!βb) βc,
      hBu₁, hu₂]
    simp [hεB]
  have hB2v : B (pt3 q (!βb) p βa r (!βc)) = cb := by
    rw [pt3_comm p q r hpq hpr hqr βa (!βb) (!βc), hRB (!βb) (!βc),
      hiB (!βb) (!βc), hBu₁, hu₂]
    simp [hεB]
  have hB3v : B (pt3 q (!βb) p (!βa) r βc) = cb := by
    rw [pt3_comm p q r hpq hpr hqr (!βa) (!βb) βc,
      ← pt3_rot p q r hpq hpr hqr (!βa) (!βb) βc, hRB3 (!βa) (!βb),
      hiB3 (!βa) (!βb), hAu₁'', hu₂'']
    simp [hεB3]
  obtain ⟨iB, bB, cB4, hibB, hlB⟩ := hlineB q (!βb)
  obtain ⟨dB4, lB4, aB4, uB4, vB4, hRB4⟩ :=
    restr_lineFn q p r hpq.symm hqr hpr B (!βb) iB bB cB4 hibB hlB
  have hB4 : B (pt3 q (!βb) p (!βa) r (!βc)) = cb := by
    have k1 : lineFn dB4 lB4 aB4 uB4 vB4 βa βc = !cb := by
      rw [← hRB4 βa βc]; exact hB1
    have k2 : lineFn dB4 lB4 aB4 uB4 vB4 βa (!βc) = cb := by
      rw [← hRB4 βa (!βc)]; exact hB2v
    have k3 : lineFn dB4 lB4 aB4 uB4 vB4 (!βa) βc = cb := by
      rw [← hRB4 (!βa) βc]; exact hB3v
    rw [hRB4 (!βa) (!βc)]
    exact lineFn_fourth dB4 lB4 aB4 uB4 vB4 βa βc cb k1 k2 k3
  -- C's values on its opposite face (r, !βc), then the fourth point
  have hC1 : C (pt3 r (!βc) p βa q βb) = !cc := by
    rw [pt3_rot p q r hpq hpr hqr βa βb (!βc), hRC βb (!βc), hiC βb (!βc),
      hBu₁, hu₂]
    simp [hεC]
  have hC2v : C (pt3 r (!βc) p βa q (!βb)) = cc := by
    rw [pt3_rot p q r hpq hpr hqr βa (!βb) (!βc), hRC (!βb) (!βc),
      hiC (!βb) (!βc), hBu₁, hu₂]
    simp [hεC]
  have hC3v : C (pt3 r (!βc) p (!βa) q βb) = cc := by
    rw [pt3_rot p q r hpq hpr hqr (!βa) βb (!βc),
      ← pt3_comm p q r hpq hpr hqr (!βa) βb (!βc), hRC2 (!βa) (!βc),
      hiC2 (!βa) (!βc), hAu₁', hu₂']
    simp [hεC2]
  obtain ⟨iC, bC, cC4, hibC, hlC⟩ := hlineC r (!βc)
  obtain ⟨dC4, lC4, aC4, uC4, vC4, hRC4⟩ :=
    restr_lineFn r p q hpr.symm hqr.symm hpq C (!βc) iC bC cC4 hibC hlC
  have hC4 : C (pt3 r (!βc) p (!βa) q (!βb)) = cc := by
    have k1 : lineFn dC4 lC4 aC4 uC4 vC4 βa βb = !cc := by
      rw [← hRC4 βa βb]; exact hC1
    have k2 : lineFn dC4 lC4 aC4 uC4 vC4 βa (!βb) = cc := by
      rw [← hRC4 βa (!βb)]; exact hC2v
    have k3 : lineFn dC4 lC4 aC4 uC4 vC4 (!βa) βb = cc := by
      rw [← hRC4 (!βa) βb]; exact hC3v
    rw [hRC4 (!βa) (!βb)]
    exact lineFn_fourth dC4 lC4 aC4 uC4 vC4 βa βb cc k1 k2 k3
  -- the final kill: T versus its antipode
  refine kill3 hyp (pt3 p βa q βb r βc) (pt3 p (!βa) q (!βb) r (!βc))
    ?_ ?_ ?_ ?_
  · rw [hA _ (pt3_fst p q r hpq hpr hqr _ _ _), hA4]
  · rw [hB _ (pt3_snd p q r hpq hpr hqr _ _ _),
      ← pt3_comm p q r hpq hpr hqr (!βa) (!βb) (!βc), hB4]
  · rw [hC _ (pt3_thd p q r hpq hpr hqr _ _ _),
      ← pt3_rot p q r hpq hpr hqr (!βa) (!βb) (!βc), hC4]
  · rw [parityN_pt3 p q r hpq hpr hqr, parityN_pt3 p q r hpq hpr hqr]
    exact parity_T_Tbar βa βb βc

end Cases

/-! ## §8 The frozen theorems -/

/-- **THREE HEADS CANNOT COMPUTE PARITY3 (clean tier).** No 3-head
    hard-attention configuration of any internal dimension, through a
    thresholded affine readout, computes parity on 3 bits. The readout shape
    is verbatim the lower/upper bounds'. Axioms:
    `propext, Classical.choice, Quot.sound` — no `native_decide`. -/
theorem parity3_not_achievable_with_three_heads {d : ℕ}
    (h : Fin 3 → HardAttentionHead 3 d) (w : Fin 3 → ℝ) (bias : ℝ) :
    ¬ (∀ x : Fin 3 → Bool,
      (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
       then true else false) = parityN x) := by
  intro hyp0
  have hyp1 : ∀ x, parityN x = true ↔
      0 < w 0 * (if headOutput (h 0) x then (1 : ℝ) else 0)
        + w 1 * (if headOutput (h 1) x then (1 : ℝ) else 0)
        + w 2 * (if headOutput (h 2) x then (1 : ℝ) else 0) + bias := by
    intro x
    have hx := hyp_iff_of_ite
      (S := fun x => (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0))
        + bias) hyp0 x
    rwa [Fin.sum_univ_three] at hx
  obtain ⟨i₀, b₀, c₀, h₀⟩ := head_const_halfcube (h 0)
  obtain ⟨i₁, b₁, c₁, h₁⟩ := head_const_halfcube (h 1)
  obtain ⟨i₂, b₂, c₂, h₂⟩ := head_const_halfcube (h 2)
  have hl₀ := head_face_line (h 0)
  have hl₁ := head_face_line (h 1)
  have hl₂ := head_face_line (h 2)
  have hyp021 : ∀ x, parityN x = true ↔
      0 < w 0 * (if headOutput (h 0) x then (1 : ℝ) else 0)
        + w 2 * (if headOutput (h 2) x then (1 : ℝ) else 0)
        + w 1 * (if headOutput (h 1) x then (1 : ℝ) else 0) + bias :=
    fun x => (hyp1 x).trans (by constructor <;> intro <;> linarith)
  have hyp120 : ∀ x, parityN x = true ↔
      0 < w 1 * (if headOutput (h 1) x then (1 : ℝ) else 0)
        + w 2 * (if headOutput (h 2) x then (1 : ℝ) else 0)
        + w 0 * (if headOutput (h 0) x then (1 : ℝ) else 0) + bias :=
    fun x => (hyp1 x).trans (by constructor <;> intro <;> linarith)
  by_cases e01 : i₀ = i₁
  · by_cases f01 : b₀ = b₁
    · -- heads 0 and 1 share (i, b); third head 2
      exact case_shared hyp1 i₀ b₀ c₀ c₁ h₀
        (fun x hx => h₁ x (by rw [← e01, ← f01]; exact hx)) (hl₂ i₀ b₀)
    · have f01' : b₁ = !b₀ := (bool_ne_iff b₁ b₀).mp (Ne.symm f01)
      by_cases e02 : i₀ = i₂
      · by_cases f02 : b₂ = b₀
        · -- heads 0 and 2 share; third head 1
          exact case_shared hyp021 i₀ b₀ c₀ c₂ h₀
            (fun x hx => h₂ x (by rw [← e02, f02]; exact hx)) (hl₁ i₀ b₀)
        · -- heads 1 and 2 share (i₀, !b₀); third head 0
          have f02' : b₂ = !b₀ := (bool_ne_iff b₂ b₀).mp f02
          exact case_shared hyp120 i₁ b₁ c₁ c₂
            (fun x hx => h₁ x hx)
            (fun x hx => h₂ x
              (by rw [← (e01.symm.trans e02), f02'.trans f01'.symm]; exact hx))
            (hl₀ i₁ b₁)
      · -- 2b: pair (0,1) on i₀ with opposite signs, head 2 on i₂ ≠ i₀
        exact case_2b hyp1 i₀ i₂ e02 b₀ b₂ c₀ c₁ c₂ h₀
          (fun x hx => h₁ x (by rw [← e01, f01']; exact hx)) h₂ hl₀ hl₁ hl₂
  · by_cases e02 : i₀ = i₂
    · by_cases f02 : b₀ = b₂
      · -- heads 0 and 2 share; third head 1
        exact case_shared hyp021 i₀ b₀ c₀ c₂ h₀
          (fun x hx => h₂ x (by rw [← e02, ← f02]; exact hx)) (hl₁ i₀ b₀)
      · -- 2b: pair (0,2) on i₀ opposite signs, head 1 on i₁ ≠ i₀
        have f02' : b₂ = !b₀ := (bool_ne_iff b₂ b₀).mp (Ne.symm f02)
        exact case_2b hyp021 i₀ i₁ e01 b₀ b₁ c₀ c₂ c₁ h₀
          (fun x hx => h₂ x (by rw [← e02, f02']; exact hx)) h₁ hl₀ hl₂ hl₁
    · by_cases e12 : i₁ = i₂
      · by_cases f12 : b₁ = b₂
        · -- heads 1 and 2 share; third head 0
          exact case_shared hyp120 i₁ b₁ c₁ c₂
            (fun x hx => h₁ x hx)
            (fun x hx => h₂ x (by rw [← e12, ← f12]; exact hx)) (hl₀ i₁ b₁)
        · -- 2b: pair (1,2) on i₁ opposite signs, head 0 on i₀ ≠ i₁
          have f12' : b₂ = !b₁ := (bool_ne_iff b₂ b₁).mp (Ne.symm f12)
          exact case_2b hyp120 i₁ i₀ (Ne.symm e01) b₁ b₀ c₁ c₂ c₀ h₁
            (fun x hx => h₂ x (by rw [← e12, f12']; exact hx)) h₀ hl₁ hl₂ hl₀
      · -- all three directions distinct
        exact case_3 hyp1 i₀ i₁ i₂ e01 e02 e12 b₀ b₁ b₂ c₀ c₁ c₂ h₀ h₁ h₂
          hl₀ hl₁ hl₂

/-- Achievability at `n = 3`: four heads compute parity3 —
    `parityN_achievable_with_exp_heads` at `n = 3`, `2^(3-1) = 4`. -/
theorem parity3_achievable_with_four_heads :
    ∃ (h : Fin 4 → HardAttentionHead 3 2) (w : Fin 4 → ℝ) (bias : ℝ),
      ∀ x : Fin 3 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
         then true else false) = parityN x := by
  simpa using parityN_achievable_with_exp_heads (n := 3)

/-- **k(3) = 4, fully machine-checked at clean tier.** Three heads cannot
    compute parity3; four heads can. Both halves `native_decide`-free, on
    `propext, Classical.choice, Quot.sound`. Non-vacuity of the model class
    is carried by the achievability half's explicit witness. -/
theorem parity3_head_complexity_four :
    (∀ {d : ℕ} (h : Fin 3 → HardAttentionHead 3 d) (w : Fin 3 → ℝ) (bias : ℝ),
      ¬ (∀ x : Fin 3 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
         then true else false) = parityN x)) ∧
    (∃ (h : Fin 4 → HardAttentionHead 3 2) (w : Fin 4 → ℝ) (bias : ℝ),
      ∀ x : Fin 3 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
         then true else false) = parityN x) :=
  ⟨fun h w bias => parity3_not_achievable_with_three_heads h w bias,
   parity3_achievable_with_four_heads⟩

end

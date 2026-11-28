import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51202_aux

open PEqualNP.CircuitLowerBounds

abbrev Mask := BitVec 6

def initial : List Mask := [62, 60, 56, 48, 32, 0, 63]
def targets : List Mask := [8, 34, 44]

def choices (known : List Mask) : List (Mask × Nat) :=
  (known.flatMap fun a =>
    (~~~a, 1) :: known.flatMap (fun b => [(a &&& b, 0), (a ||| b, 0)])).eraseDups

def missing (known : List Mask) : Nat :=
  (targets.filter fun a => !known.contains a).length

def viable (k b : Nat) (known : List Mask) : List (Mask × Nat) :=
  (choices known).filter fun (a, c) =>
    decide (c ≤ b) && !known.contains a && decide (missing (a :: known) ≤ k)

def search : Nat → Nat → List Mask → Bool
  | 0, _, known => targets.all known.contains
  | k+1, b, known =>
    if targets.all known.contains then true
    else if missing known > k+1 then false
    else search k b known || (viable k b known).any fun (a, c) =>
      search k (b - c) (a :: known)

def maskOp (op : GateOp) (args : List Mask) : Mask :=
  match op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes 6)
  | .or => args.foldr (· ||| ·) 0
  | .not => ~~~(args.headD 0)
  | _ => 0

def cost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0
def result (w : List Mask) (g : Gate) : Mask :=
  maskOp g.op (g.inputs.map fun i => w.getD i 0)
def step (w : List Mask) (g : Gate) : List Mask := w ++ [result w g]

def good (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem getD_mem_or_zero (w : List Mask) (i : Nat) :
    w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_of_getElem? h)

theorem available (w known : List Mask) (bound : w ⊆ known) (zero : 0 ∈ known)
    (i : Nat) : w.getD i 0 ∈ known := by
  rcases getD_mem_or_zero w i with h | h
  · exact bound h
  · rw [h]
    exact zero

theorem result_known_or_choice (w known : List Mask) (g : Gate)
    (bound : w ⊆ known) (zero : 0 ∈ known) (ones : 63 ∈ known) (hg : good g) :
    result w g ∈ known ∨ (result w g, cost g) ∈ choices known := by
  have andChoice (a b : Mask) (ha : a ∈ known) (hb : b ∈ known) :
      (a &&& b, 0) ∈ choices known := by
    unfold choices
    rw [List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_cons.mpr (Or.inr
      (List.mem_flatMap.mpr ⟨b, hb, by simp⟩))⟩
  have orChoice (a b : Mask) (ha : a ∈ known) (hb : b ∈ known) :
      (a ||| b, 0) ∈ choices known := by
    unfold choices
    rw [List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_cons.mpr (Or.inr
      (List.mem_flatMap.mpr ⟨b, hb, by simp⟩))⟩
  have notChoice (a : Mask) (ha : a ∈ known) : (~~~a, 1) ∈ choices known := by
    unfold choices
    rw [List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨a, ha, by simp⟩
  have av := available w known bound zero
  obtain ⟨op, arity⟩ := hg
  rcases g with ⟨op', ins⟩
  dsimp at op arity
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases op with rfl | rfl | rfl
    · exact Or.inl ones
    · exact Or.inl zero
    · exact Or.inl (by simpa [result, maskOp] using (show BitVec.allOnes 6 ∈ known from ones))
  · rcases op with rfl | rfl | rfl
    · exact Or.inr (by simpa [result, maskOp, cost] using andChoice _ (BitVec.allOnes 6) (av i) ones)
    · exact Or.inr (by simpa [result, maskOp, cost] using orChoice _ 0 (av i) zero)
    · exact Or.inr (by simpa [result, maskOp, cost] using notChoice _ (av i))
  · rcases op with rfl | rfl | rfl
    · refine Or.inr ?_
      simp only [result, maskOp, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, BitVec.and_allOnes, cost]
      exact andChoice _ _ (av i) (av j)
    · exact Or.inr (by simpa [result, maskOp, cost] using orChoice _ _ (av i) (av j))
    · exact Or.inr (by simpa [result, maskOp, cost] using notChoice _ (av i))
  · simp at arity

theorem extend (gs : List Gate) (w : List Mask) :
    ∃ extra, gs.foldl step w = w ++ extra ∧ extra.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨extra, hp, hl⟩ := ih (step w g)
    refine ⟨result w g :: extra, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hp]
    simp [step]

theorem missing_bound (gs : List Gate) (w known : List Mask) (sub : w ⊆ known)
    (target : targets ⊆ gs.foldl step w) :
    (targets.filter fun a => !known.contains a).length ≤ gs.length := by
  obtain ⟨extra, hp, hl⟩ := extend gs w
  rw [hp] at target
  have nd : targets.Nodup := by decide
  rw [← hl]
  apply (nd.filter _).length_le_of_subset
  intro a ha
  obtain ⟨hat, hnot⟩ := List.mem_filter.mp ha
  have ha' : a ∉ known := by simpa [List.contains_iff_mem] using hnot
  exact (List.mem_append.mp (target hat)).resolve_left (fun hw => ha' (sub hw))

theorem search_complete (fuel budget : Nat) (gs : List Gate) (w known : List Mask)
    (length : gs.length ≤ fuel) (costs : (gs.map cost).sum ≤ budget)
    (allowed : ∀ g ∈ gs, good g) (sub : w ⊆ known)
    (zero : 0 ∈ known) (ones : 63 ∈ known)
    (target : targets ⊆ gs.foldl step w) :
    search fuel budget known = true := by
  induction fuel generalizing budget gs w known with
  | zero =>
    have hnil : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    change targets.all known.contains = true
    exact List.all_eq_true.mpr
      fun _ h => List.contains_iff_mem.mpr (sub (target h))
  | succ fuel ih =>
    cases gs with
    | nil =>
      have hpass : targets.all known.contains = true := by
        exact List.all_eq_true.mpr fun a ha => List.contains_iff_mem.mpr (sub (target ha))
      simp [search, hpass]
    | cons g gs =>
      have hg := allowed g (by simp)
      have tailGood : ∀ h ∈ gs, good h := fun h hh => allowed h (by simp [hh])
      have tailLen : gs.length ≤ fuel := by simpa using length
      have tailBudget : (gs.map cost).sum ≤ budget - cost g := by
        simp at costs
        omega
      have costFits : cost g ≤ budget := by simp at costs; omega
      have hskip : ¬ fuel + 1 < missing known :=
        Nat.not_lt_of_ge ((missing_bound (g :: gs) w known sub target).trans length)
      have tailTarget : targets ⊆ gs.foldl step (step w g) := target
      by_cases present : result w g ∈ known
      · have sub' : step w g ⊆ known := by
          intro a ha
          rcases List.mem_append.mp ha with h | h
          · exact sub h
          · simpa using (List.mem_singleton.mp h ▸ present)
        have hrec := ih budget gs (step w g) known tailLen
          (tailBudget.trans (Nat.sub_le ..)) tailGood sub' zero ones tailTarget
        by_cases htarget : targets.all known.contains = true
        · simp [search, htarget]
        ·

          simp only [search, htarget, if_neg hskip, hrec, Bool.true_or, Bool.false_eq_true, if_false]
      · have sub' : step w g ⊆ result w g :: known := by
          intro a ha
          rcases List.mem_append.mp ha with h | h
          · exact List.mem_cons.mpr (Or.inr (sub h))
          · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
        have hrec := ih (budget - cost g) gs (step w g) _ tailLen tailBudget tailGood sub'
          (List.mem_cons.mpr (Or.inr zero)) (List.mem_cons.mpr (Or.inr ones)) tailTarget
        have choice := (result_known_or_choice w known g sub zero ones hg).resolve_left present
        by_cases htarget : targets.all known.contains = true
        · simp [search, htarget]
        · simp only [search, htarget, if_false, hskip]
          apply Bool.or_eq_true_iff.mpr
          right
          apply List.any_eq_true.mpr
          have room : missing (result w g :: known) ≤ fuel :=
            (missing_bound gs (step w g) _ sub' tailTarget).trans tailLen
          refine ⟨(result w g, cost g), List.mem_filter.mpr ⟨choice, ?_⟩, hrec⟩
          simp [costFits, present, room]

theorem map_getD (w : List Mask) (t : Nat) (i : Nat) :
    (w.map fun a => a.getLsbD t).getD i false = (w.getD i 0).getLsbD t := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

theorem maskOp_bits (op : GateOp) (args : List Mask) (t : Nat) (ht : t < 6)
    (legal : op = .and ∨ op = .or ∨ op = .not) :
    (maskOp op args).getLsbD t = op.eval (args.map fun a => a.getLsbD t) := by
  rcases legal with rfl | rfl | rfl
  · induction args with
    | nil =>
      change (BitVec.allOnes 6).getLsbD t = true
      rw [BitVec.getLsbD_allOnes]
      exact decide_eq_true ht
    | cons a args ih => simpa [maskOp, GateOp.eval] using congrArg (fun b => a.getLsbD t && b) ih
  · induction args with
    | nil => simp [maskOp, GateOp.eval]
    | cons a args ih => simpa [maskOp, GateOp.eval] using congrArg (fun b => a.getLsbD t || b) ih
  · cases args with
    | nil =>
      change (BitVec.allOnes 6).getLsbD t = true
      rw [BitVec.getLsbD_allOnes]
      exact decide_eq_true ht
    | cons a args => simp [maskOp, GateOp.eval, ht]

theorem fold_bits (gs : List Gate) (w : List Mask) (t : Nat) (ht : t < 6)
    (allowed : ∀ g ∈ gs, good g) :
    (gs.foldl step w).map (fun a => a.getLsbD t) =
      gs.foldl (fun row g => row ++ [g.op.eval (g.inputs.map fun i => row.getD i false)])
        (w.map fun a => a.getLsbD t) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (step w g) (fun a ha => allowed a (by simp [ha]))]
    simp only [step, List.map_append, List.map_cons, List.map_nil,
      result, maskOp_bits _ _ _ ht (allowed g (by simp)).1, List.map_map]
    simp only [Function.comp_def, map_getD]

theorem cost_eq (gs : List Gate) :
    (gs.map cost).sum = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change cost g + (gs.map cost).sum =
      ((g :: gs).filter fun h => decide (h.op = GateOp.not)).length
    change (gs.map cost).sum = (gs.filter fun h => decide (h.op = GateOp.not)).length at ih
    rw [ih]
    cases g with
    | mk op ins => cases op <;> simp [cost, Nat.add_comm]

theorem initial_bits (t : Fin 6) :
    initial.map (fun a => a.getLsbD t.val) =
      (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] := by
  fin_cases t <;> decide

theorem mask_at (D : Circuit) (i : Nat) (m : Mask)
    (allowed : ∀ g ∈ D.gates, good g)
    (bits : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++ [false,true])).getD
        i false = m.getLsbD t.val) :
    (D.gates.foldl step initial).getD i 0 = m := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [← map_getD]
  rw [fold_bits _ _ t ht allowed, initial_bits ⟨t, ht⟩]
  exact bits ⟨t, ht⟩

def ins (s a : Nat) : Nat := s ||| (1 <<< a)
def initialCode : Nat := (initial.map BitVec.toNat).foldl ins 0
def goalCode : Nat := (targets.map BitVec.toNat).foldl ins 0

def missingBits (s : Nat) : Nat := ((targets.map BitVec.toNat).filter fun a => !s.testBit a).length

def addNormal (xs : List Nat) (a m : Nat) : Nat :=
  xs.foldl (fun z b => ins (ins z (a &&& b)) (a ||| b)) m

def initialNormal : Nat := (initial.map BitVec.toNat).foldl (fun m a => addNormal (initial.map BitVec.toNat) a m) 0
def initialNegative : Nat := (initial.map BitVec.toNat).foldl (fun m a => ins m (63 ^^^ a)) 0

def packedSearch : Nat → Nat → Nat → Nat → Nat → List Nat → Bool
  | 0, _, s, _, _, _ => missingBits s == 0
  | k+1, b, s, normal, negative, xs =>
    let miss := missingBits s
    if miss == 0 then true
    else if miss > k+1 then false
    else
      let flags := if b = 0 then normal else normal ||| negative
      let usable := (if miss = k+1 then flags &&& goalCode else flags)
      packedSearch k b s normal negative xs || (List.range 64).any fun a =>
        !s.testBit a && usable.testBit a &&
          let ss := ins s a
          let nn := addNormal xs a normal
          let nn' := ins negative (63 ^^^ a)
          ((normal.testBit a && packedSearch k b ss nn nn' (a :: xs)) ||
            (b != 0 && negative.testBit a && packedSearch k (b-1) ss nn nn' (a :: xs)))

theorem ins_spec (s a x : Nat) :
    (ins s a).testBit x = true ↔ s.testBit x = true ∨ x = a := by
  have shift : ((1 : Nat) <<< a).testBit x = true ↔ x = a := by
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true_iff, decide_eq_true_eq,
      Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega
  rw [ins, Nat.testBit_or, Bool.or_eq_true_iff, shift]

theorem foldIns_spec (xs : List Nat) (s x : Nat) :
    (xs.foldl ins s).testBit x = true ↔ s.testBit x = true ∨ x ∈ xs := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons, ih, ins_spec, List.mem_cons]
    tauto

theorem addNormal_spec (xs : List Nat) (a s x : Nat) :
    (addNormal xs a s).testBit x = true ↔ s.testBit x = true ∨
      ∃ b ∈ xs, x = a &&& b ∨ x = a ||| b := by
  induction xs generalizing s with
  | nil => simp [addNormal]
  | cons b xs ih =>
    change (addNormal xs a (ins (ins s (a &&& b)) (a ||| b))).testBit x = true ↔ _
    rw [ih, ins_spec, ins_spec]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem foldNormal_has (xs ys : List Nat) (s a b : Nat) (ha : a ∈ xs) (hb : b ∈ ys) :
    let flags := xs.foldl (fun m v => addNormal ys v m) s
    flags.testBit (a &&& b) = true ∧ flags.testBit (a ||| b) = true := by

  have spec : ∀ x, (xs.foldl (fun m v => addNormal ys v m) s).testBit x = true ↔
        s.testBit x = true ∨ ∃ u ∈ xs, ∃ v ∈ ys, x = u &&& v ∨ x = u ||| v := by
    intro x
    clear ha hb
    induction xs generalizing s with
    | nil => simp
    | cons u xs ih =>
      rw [List.foldl_cons, ih, addNormal_spec]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]
  have : ∀ x, a ∈ xs → b ∈ ys → x = a &&& b ∨ x = a ||| b →
      (xs.foldl (fun m v => addNormal ys v m) s).testBit x = true :=
    fun x ha hb h => (spec x).mpr (Or.inr ⟨a, ha, b, hb, h⟩)
  exact ⟨this _ ‹a ∈ xs› ‹b ∈ ys› (Or.inl rfl),
    this _ ‹a ∈ xs› ‹b ∈ ys› (Or.inr rfl)⟩

theorem neg_toNat (a : Mask) : (~~~a).toNat = 63 ^^^ a.toNat := by
  rw [← BitVec.allOnes_xor, BitVec.toNat_xor]
  rfl

def coherent (known : List Mask) (s pos neg : Nat) : Prop :=
  (∀ a : Mask, s.testBit a.toNat = true ↔ a ∈ known) ∧
  (∀ a ∈ known, ∀ b ∈ known, a ≠ b → pos.testBit (a &&& b : Mask).toNat = true ∧
      pos.testBit (a ||| b : Mask).toNat = true) ∧
  (∀ a ∈ known, neg.testBit (~~~a : Mask).toNat = true)

theorem initial_coherent : coherent initial initialCode initialNormal initialNegative := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp only [initialCode, foldIns_spec, Nat.zero_testBit, Bool.false_eq_true, false_or,
      List.mem_map]
    constructor
    · rintro ⟨b, hb, h⟩
      exact (BitVec.eq_of_toNat_eq h) ▸ hb
    · intro h
      exact ⟨a, h, rfl⟩
  · intro a ha b hb _
    simpa only [initialNormal, BitVec.toNat_and, BitVec.toNat_or] using
      foldNormal_has (initial.map BitVec.toNat) (initial.map BitVec.toNat) 0 a.toNat b.toNat
        (List.mem_map_of_mem ha) (List.mem_map_of_mem hb)
  · intro a ha
    rw [neg_toNat]
    change ((initial.map (fun a => 63 ^^^ a.toNat)).foldl ins 0).testBit
      (63 ^^^ a.toNat) = true
    exact (foldIns_spec _ _ _).mpr (Or.inr (List.mem_map_of_mem ha))

theorem coherent_cons (known : List Mask) (s pos neg : Nat) (a : Mask)
    (old : coherent known s pos neg) :
    coherent (a :: known) (ins s a.toNat)
      (addNormal (known.map BitVec.toNat) a.toNat pos) (ins neg (63 ^^^ a.toNat)) := by
  obtain ⟨code, normal, negative⟩ := old
  refine ⟨?_, ?_, ?_⟩
  · intro b
    rw [ins_spec, code, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · rintro (h | h)
      · exact Or.inr (congrArg BitVec.toNat h)
      · exact Or.inl h
  · intro b hb c hc diff
    rw [BitVec.toNat_and, BitVec.toNat_or, addNormal_spec, addNormal_spec]
    rcases List.mem_cons.mp hb with e | hb
    · subst b
      rcases List.mem_cons.mp hc with e | hc
      · exact (diff e.symm).elim
      · exact ⟨Or.inr ⟨c.toNat, List.mem_map_of_mem hc, Or.inl rfl⟩,
          Or.inr ⟨c.toNat, List.mem_map_of_mem hc, Or.inr rfl⟩⟩
    · rcases List.mem_cons.mp hc with e | hc
      · subst c
        exact ⟨Or.inr ⟨b.toNat, List.mem_map_of_mem hb, Or.inl (Nat.and_comm _ _)⟩,
          Or.inr ⟨b.toNat, List.mem_map_of_mem hb, Or.inr (Nat.or_comm _ _)⟩⟩
      · exact ⟨Or.inl (by simpa only [BitVec.toNat_and] using (normal b hb c hc diff).1),
          Or.inl (by simpa only [BitVec.toNat_or] using (normal b hb c hc diff).2)⟩
  · intro b hb
    rw [ins_spec]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inr (neg_toNat _)
    · exact Or.inl (negative b hb)

theorem agrees (known : List Mask) (s pos neg : Nat) (state : coherent known s pos neg) :
    missingBits s = missing known := by
  have bit (a : Mask) : s.testBit a.toNat = known.contains a := by
    apply Bool.eq_iff_iff.mpr
    rw [state.1, List.contains_iff_mem]
  simp only [missingBits, missing, List.filter_map, List.length_map, Function.comp_def, bit]

theorem empty_iff (known : List Mask) :
    (missing known == 0) = targets.all known.contains := by
  unfold missing targets
  cases h8 : known.contains 8#6 <;> cases h34 : known.contains 34#6 <;>
    cases h44 : known.contains 44#6 <;> simp [-List.contains_eq_mem, h8, h34, h44]

theorem missing_cons_equal (known : List Mask) (a : Mask) (outside : a ∉ targets) :
    missing (a :: known) = missing known := by
  unfold missing
  congr 1
  apply List.filter_congr
  intro t ht
  have unequal : t ≠ a := fun e => outside (e ▸ ht)
  simp [List.contains_cons, unequal, Ne.symm unequal]

theorem choice_flags (known : List Mask) (s pos neg : Nat) (a : Mask) (c : Nat)
    (state : coherent known s pos neg) (choice : (a,c) ∈ choices known) (new : a ∉ known) :
    (c = 0 ∧ pos.testBit a.toNat = true) ∨ (c = 1 ∧ neg.testBit a.toNat = true) := by
  unfold choices at choice
  rw [List.mem_eraseDups, List.mem_flatMap] at choice
  obtain ⟨x, hx, h⟩ := choice
  rcases List.mem_cons.mp h with eq | h
  · cases eq
    exact Or.inr ⟨rfl, state.2.2 x hx⟩
  · obtain ⟨y, hy, hh⟩ := List.mem_flatMap.mp h
    have unequal : x ≠ y := by
      intro same
      subst y
      simp at hh
      obtain ⟨eq, _⟩ := hh
      exact new (eq.symm ▸ hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with eq | eq
    · cases eq
      exact Or.inl ⟨rfl, (state.2.1 x hx y hy unequal).1⟩
    · cases eq
      exact Or.inl ⟨rfl, (state.2.1 x hx y hy unequal).2⟩

theorem packed_complete (k b : Nat) (known : List Mask) (s pos neg : Nat)
    (state : coherent known s pos neg) (old : search k b known = true) :
    packedSearch k b s pos neg (known.map BitVec.toNat) = true := by
  have same := agrees known s pos neg state
  have ready : (missingBits s == 0) = targets.all known.contains := by rw [same, empty_iff]
  induction k generalizing b known s pos neg with
  | zero => simpa only [packedSearch, ready, search] using old
  | succ k ih =>
    by_cases found : targets.all known.contains = true
    · simp only [packedSearch, ready, found, if_true]
    · have enough : ¬ k+1 < missing known := by
        intro bad
        rw [search, if_neg found, if_pos bad] at old
        cases old
      have pass : ¬ k+1 < missingBits s := by rw [same]; exact enough
      rw [search, if_neg found, if_neg enough] at old
      rw [packedSearch, if_neg (by rw [ready]; exact found), if_neg pass]
      apply Bool.or_eq_true_iff.mpr
      rcases Bool.or_eq_true_iff.mp old with skipped | moved
      · exact Or.inl (ih b known s pos neg state skipped
          (agrees known s pos neg state) ready)
      · right
        obtain ⟨⟨a,c⟩, ha, recurse⟩ := List.any_eq_true.mp moved
        obtain ⟨move, legal⟩ := List.mem_filter.mp ha
        have lim : c ≤ b := by
          exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp legal).1).1
        have new : a ∉ known := by
          intro old
          have no := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp legal).1).2
          have hmem : known.contains a = true := List.contains_iff_mem.mpr old
          rw [hmem] at no
          cases no
        have space : missing (a :: known) ≤ k :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp legal).2
        have added := coherent_cons known s pos neg a state
        have next := ih (b-c) (a :: known) (ins s a.toNat)
          (addNormal (known.map BitVec.toNat) a.toNat pos) (ins neg (63 ^^^ a.toNat))
          added recurse (agrees _ _ _ _ added) (by rw [agrees _ _ _ _ added, empty_iff])
        simp only [List.map_cons] at next
        have hbit : s.testBit a.toNat = false := by
          cases h : s.testBit a.toNat
          · rfl
          · exact (new ((state.1 a).mp h)).elim
        have targetFlag (tight : missingBits s = k+1) : goalCode.testBit a.toNat = true := by
          have mem : a ∈ targets := by
            by_contra hm
            rw [missing_cons_equal known a hm, ← same, tight] at space
            omega
          exact (foldIns_spec _ _ _).mpr (Or.inr (List.mem_map_of_mem mem))
        have range : a.toNat ∈ List.range 64 := List.mem_range.mpr a.isLt
        apply List.any_eq_true.mpr
        refine ⟨a.toNat, range, ?_⟩
        rcases choice_flags known s pos neg a c state move new with ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
        · simp only [Nat.sub_zero] at next
          have flag : (if b = 0 then pos else pos ||| neg).testBit a.toNat = true := by
            by_cases e : b = 0 <;> simp [e, hpos]
          by_cases tight : missingBits s = k+1
          · simp [hbit, tight, Nat.testBit_and, flag, targetFlag tight, hpos, next]
          · simp [hbit, tight, flag, hpos, next]
        · have bn : b ≠ 0 := by omega
          have flag : (if b = 0 then pos else pos ||| neg).testBit a.toNat = true := by
            simp [bn, hneg]
          by_cases tight : missingBits s = k+1
          · simp [hbit, tight, Nat.testBit_and, flag, targetFlag tight, bn, hneg, next]
          · simp [hbit, tight, flag, bn, hneg, next]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem exhaustive : packedSearch 6 2 initialCode initialNormal initialNegative
    (initial.map BitVec.toNat) = false := by
  decide +kernel

theorem impossible : ¬ (∃ (D : Circuit) (p q r : Fin (7+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
    PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
    ∀ t : Fin 6,
      let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (8 : Nat).testBit t.val ∧
      w.getD q.val false = (34 : Nat).testBit t.val ∧
      w.getD r.val false = (44 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, model, _, neg, length, outputs⟩
  have allowed (g : Gate) (hg : g ∈ D.gates) : good g := by
    simpa [good] using model g hg
  have costs : (D.gates.map cost).sum ≤ 2 := by
    rw [cost_eq]
    exact neg
  have hp : (D.gates.foldl step initial).getD p.val 0 = 8 :=
    mask_at D _ _ allowed fun t => by
      exact (outputs t).1
  have hq : (D.gates.foldl step initial).getD q.val 0 = 34 :=
    mask_at D _ _ allowed fun t => by
      exact (outputs t).2.1
  have hr : (D.gates.foldl step initial).getD r.val 0 = 44 :=
    mask_at D _ _ allowed fun t => by
      exact (outputs t).2.2
  have hit (i : Nat) (m : Mask) (nz : m ≠ 0)
      (h : (D.gates.foldl step initial).getD i 0 = m) :
      m ∈ D.gates.foldl step initial := by
    rw [← h]
    exact (getD_mem_or_zero _ _).resolve_right fun z => nz (h.symm.trans z)
  have all : targets ⊆ D.gates.foldl step initial := by
    intro a ha
    simp [targets] at ha
    rcases ha with rfl | rfl | rfl
    · exact hit _ _ (by decide) hp
    · exact hit _ _ (by decide) hq
    · exact hit _ _ (by decide) hr
  have success := search_complete 6 2 D.gates initial initial length costs allowed
    (fun _ h => h) (by decide) (by decide) all
  have checked := packed_complete 6 2 initial initialCode initialNormal initialNegative
    initial_coherent success
  rw [exhaustive] at checked
  cases checked

end PEqualNP.Outside.L_meta_51202_aux
theorem PEqualNP.Outside.L_meta_51202 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (34 : Nat).testBit t.val ∧
    w.getD r.val false = (44 : Nat).testBit t.val)) := by
  exact PEqualNP.Outside.L_meta_51202_aux.impossible


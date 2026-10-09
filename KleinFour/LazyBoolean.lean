import KleinFour.LazyCheck
import Mathlib.Tactic.FinCases

namespace KleinFour.LazyCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def compSmall (c : Bool → Bool) (a b : Small) : Small :=
  if b.1 then if a.1 then (true, xor a.2 b.2) else (false, a.2)
  else (false, c b.2)

def compose (a b : Table) : Table :=
  { lower := { c := fun i => a.lower.c (b.lower.c i),
               p := fun s => compSmall a.lower.c (a.lower.p s) (b.lower.p s) },
    free := fun i => a.run (b.free i) }

theorem compSmall_run : ∀ (s : Fin 3) (c : Bool → Bool) (p : Fin 3 → Small) d b,
    smallRun s (compSmall c (p s) d) b =
      match smallRun s d b with
      | .c a => .c (c a)
      | .p t a => smallRun t (p t) a
      | .f j g => .f j g := by decide

theorem compose_ca (a b : Table) : (compose a b).ca = a.ca * b.ca := by
  ext x
  cases x with
  | c i => rfl
  | p s i =>
    change smallRun s (compSmall a.lower.c (a.lower.p s) (b.lower.p s)) i =
      a.run (smallRun s (b.lower.p s) i)
    have h := compSmall_run s a.lower.c a.lower.p (b.lower.p s) i
    cases hb : (b.lower.p s).1 <;> simpa [smallRun, hb, Table.run] using h
  | f i g => exact (equiv a.ca g (b.free i)).symm

def tableEqb (a b : Table) : Bool :=
  (a.lower.c false == b.lower.c false) && (a.lower.c true == b.lower.c true) &&
  (a.lower.p 0 == b.lower.p 0) && (a.lower.p 1 == b.lower.p 1) &&
  (a.lower.p 2 == b.lower.p 2) && decide (a.free false = b.free false) &&
  decide (a.free true = b.free true)

theorem tableEqb_agrees {a b : Table} (h : tableEqb a b = true) : Agrees a b := by
  simp only [tableEqb, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hc0, hc1⟩, hp0⟩, hp1⟩, hp2⟩, hf0⟩, hf1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i; cases i <;> assumption
  · intro s; fin_cases s <;> assumption
  · intro i; cases i <;> assumption

def booleanEdge (i : Fin 4007) (g : Fin 54) : Bool :=
  let t := compose (unpack generatorCodes[g.val]!) (unpack (codesAt i.val))
  tableEqb (unpack (codesAt (lookup t).val)) t

theorem boolean_sample : ∀ i : Fin 8, ∀ g : Fin 54,
    booleanEdge ⟨i.val, by omega⟩ g = true := by decide

end KleinFour.LazyCertificate

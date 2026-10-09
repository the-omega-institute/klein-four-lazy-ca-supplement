import KleinFour.Main

namespace KleinFour

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def LowerWitness (l : Lower) : Prop :=
  ∃ s b, l.c false = b ∧ l.c true = b ∧ l.p s = (false, b)

instance (l : Lower) : Decidable (LowerWitness l) := inferInstanceAs (Decidable (∃ s b, _))

theorem table_merges (t : Table) : Merges t.ca ↔ FreeMerges t.free := by
  simp only [Merges, FreeMerges, Table.ca, Table.run, act_e]

theorem table_witness (t : Table) : Witness t.ca ↔ LowerWitness t.lower := by
  change (∃ s b, X.c (t.lower.c false) = X.c b ∧ X.c (t.lower.c true) = X.c b ∧
    smallRun s (t.lower.p s) false = X.c b ∧ smallRun s (t.lower.p s) true = X.c b) ↔ _
  exact (by decide : ∀ l : Lower,
    (∃ s b, X.c (l.c false) = X.c b ∧ X.c (l.c true) = X.c b ∧
      smallRun s (l.p s) false = X.c b ∧ smallRun s (l.p s) true = X.c b) ↔ LowerWitness l) t.lower

theorem table_criterion (t : Table) : Criterion t.ca ↔ (FreeMerges t.free → LowerWitness t.lower) := by
  unfold Criterion
  rw [table_merges, table_witness]

instance : DecidablePred (fun t : Table => Criterion t.ca) := fun t =>
  decidable_of_iff (FreeMerges t.free → LowerWitness t.lower) (table_criterion t).symm

abbrev GoodTable := {t : Table // Criterion t.ca}
abbrev GoodParts := (Lower × {f : Free // ¬ FreeMerges f}) ⊕
  ({l : Lower // LowerWitness l} × {f : Free // FreeMerges f})

def goodParts : GoodTable ≃ GoodParts where
  toFun t := if h : FreeMerges t.val.free then
    Sum.inr (⟨t.val.lower, (table_criterion t.val).mp t.property h⟩, ⟨t.val.free, h⟩)
    else Sum.inl (t.val.lower, ⟨t.val.free, h⟩)
  invFun t := match t with
    | .inl (l, f) => ⟨⟨l, f.val⟩, (table_criterion _).mpr (fun h => False.elim (f.property h))⟩
    | .inr (l, f) => ⟨⟨l.val, f.val⟩, (table_criterion _).mpr (fun _ => l.property)⟩
  left_inv t := by
    by_cases h : FreeMerges t.val.free
    · simp only [dif_pos h]
    · simp only [dif_neg h]
  right_inv t := by
    cases t with
    | inl t => simp [t.2.property]
    | inr t => simp [t.2.property]

noncomputable def membersToTables : M ≃ GoodTable where
  toFun T := ⟨tableOf T.val, by rw [ca_tableOf]; exact (membership_iff T.val).mp T.property⟩
  invFun t := ⟨t.val.ca, (membership_iff _).mpr t.property⟩
  left_inv T := Subtype.ext (ca_tableOf T.val)
  right_inv t := Subtype.ext (tableOf_ca t.val)

theorem nonmerge_free_count : Fintype.card {f : Free // ¬ FreeMerges f} = 224 := by decide
theorem merge_free_count : Fintype.card {f : Free // FreeMerges f} = 32 := by decide
theorem lower_witness_count : Fintype.card {l : Lower // LowerWitness l} = 74 := by decide

theorem good_table_card : Fintype.card GoodTable = 59712 := by
  rw [Fintype.card_congr goodParts, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    lower_card, nonmerge_free_count, merge_free_count, lower_witness_count]

/-- Theorem 1.1 / Proposition 4.1: the generated submonoid has 59,712 elements. -/
theorem membership_card : Nat.card M = 59712 := by
  rw [Nat.card_congr membersToTables, Nat.card_eq_fintype_card, good_table_card]

end KleinFour

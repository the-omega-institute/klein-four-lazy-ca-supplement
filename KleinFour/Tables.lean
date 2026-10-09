import KleinFour.Model

namespace KleinFour

abbrev Small := Bool × Bool

def smallRun (s : Fin 3) (d : Small) (b : Bool) : X :=
  if d.1 then .p s (xor d.2 b) else .c d.2

theorem smallRun_equiv : ∀ s d b g,
    smallRun s d (xor b (character s g)) = act g (smallRun s d b) := by decide

structure Lower where
  c : Bool → Bool
  p : Fin 3 → Small
  deriving DecidableEq, Fintype

abbrev Free := Bool → X

structure Table where
  lower : Lower
  free : Free
  deriving DecidableEq, Fintype

def Table.run (t : Table) : X → X
  | .c b => .c (t.lower.c b)
  | .p s b => smallRun s (t.lower.p s) b
  | .f b g => act g (t.free b)

def Table.ca (t : Table) : CA := ⟨t.run, by
  intro g x
  cases x with
  | c b => rfl
  | p s b => exact smallRun_equiv s (t.lower.p s) b g
  | f b h =>
    change act (gm h g) (t.free b) = act g (act h (t.free b))
    rw [act_act, gm_comm]⟩

theorem fixed_iff_constant : ∀ y : X, (∀ g, act g y = y) ↔ ∃ b, y = .c b := by decide

theorem fixed_character_iff : ∀ s y,
    (∀ g, character s g = false → act g y = y) ↔ ∃ d, y = smallRun s d false := by decide

theorem constant_image (T : CA) (b : Bool) : ∃ a, T (.c b) = .c a := by
  apply (fixed_iff_constant _).mp
  intro g
  symm
  exact equiv T g (.c b)

theorem pair_image (T : CA) (s : Fin 3) : ∃ d, T (.p s false) = smallRun s d false := by
  apply (fixed_character_iff _ _).mp
  intro g hg
  rw [← equiv]
  simp [act, hg]

def constantValue : X → Bool
  | .c b => b
  | _ => false

def pairValue : X → Small
  | .c b => (false, b)
  | .p _ b => (true, b)
  | _ => (false, false)

def tableOf (T : CA) : Table :=
  { lower := { c := fun b => constantValue (T (.c b)),
               p := fun s => pairValue (T (.p s false)) },
    free := fun b => T (.f b e) }

theorem pair_rep : ∀ s b, act (shift s b) (.p s false) = .p s b := by decide
theorem free_rep : ∀ b g, act g (.f b e) = .f b g := by decide
theorem smallRun_shift : ∀ s d b,
    act (shift s b) (smallRun s d false) = smallRun s d b := by decide
theorem smallRun_pairValue : ∀ s d, pairValue (smallRun s d false) = d := by decide

theorem ca_tableOf (T : CA) : (tableOf T).ca = T := by
  ext x
  cases x with
  | c b =>
    obtain ⟨a, ha⟩ := constant_image T b
    change X.c (constantValue (T (.c b))) = T (.c b)
    rw [ha]; rfl
  | p s b =>
    obtain ⟨d, hd⟩ := pair_image T s
    change smallRun s (pairValue (T (.p s false))) b = T (.p s b)
    rw [hd, smallRun_pairValue]
    rw [← pair_rep s b, equiv, hd, smallRun_shift]
  | f b g =>
    change act g (T (.f b e)) = T (.f b g)
    rw [← free_rep b g, equiv]

theorem tableOf_ca (t : Table) : tableOf t.ca = t := by
  cases t with
  | mk l f =>
    cases l with
    | mk c p =>
      simp only [tableOf, Table.ca, Table.run, constantValue, smallRun_pairValue, act_e]

def tables : CA ≃ Table :=
  { toFun := tableOf, invFun := Table.ca, left_inv := ca_tableOf, right_inv := tableOf_ca }

instance : Fintype CA := Fintype.ofEquiv Table tables.symm

instance : DecidableEq CA := fun A B => decidable_of_iff (tableOf A = tableOf B) tables.injective.eq_iff

def tableParts : Table ≃ Lower × Free where
  toFun t := (t.lower, t.free)
  invFun t := ⟨t.1, t.2⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

def lowerParts : Lower ≃ (Bool → Bool) × (Fin 3 → Small) where
  toFun l := (l.c, l.p)
  invFun l := ⟨l.1, l.2⟩
  left_inv l := by cases l; rfl
  right_inv l := by cases l; rfl

theorem lower_card : Fintype.card Lower = 256 := by
  rw [Fintype.card_congr lowerParts, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun]
  norm_num [Small, Fintype.card_prod]
theorem x_card : Fintype.card X = 16 := by decide

theorem ca_card : Fintype.card CA = 65536 := by
  rw [Fintype.card_congr tables, Fintype.card_congr tableParts, Fintype.card_prod,
    lower_card, Fintype.card_fun, x_card]
  norm_num

end KleinFour

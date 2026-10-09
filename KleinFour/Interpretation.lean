import KleinFour.Main

namespace KleinFour

def localRules : CA ≃ (X → Bool) where
  toFun T x := encode (T x) e
  invFun := ofRule
  left_inv := rule_reconstruction
  right_inv r := by
    funext x
    change encode (decode _) e = r x
    rw [encode_decode, act_e]

def weight (x : Bits) : Nat := (Finset.univ.filter (fun g => x g = true)).card

theorem weight_constants : ∀ b, weight (encode (.c b)) = if b then 4 else 0 := by decide
theorem weight_pairs : ∀ s b, weight (encode (.p s b)) = 2 := by decide
theorem weight_free : ∀ b g, weight (encode (.f b g)) = if b then 3 else 1 := by decide

/-- Translation on actual binary configurations: `(g • x)(h) = x(hg)`. -/
def translate (g : G) (x : Bits) : Bits := fun h => x (gm h g)

def global (T : CA) (x : Bits) : Bits := encode (T (decode x))

theorem global_equivariant (T : CA) (g : G) (x : Bits) :
    global T (translate g x) = translate g (global T x) := by
  have hd : decode (translate g x) = act g (decode x) := by
    apply configurations.injective
    funext h
    simp only [configurations, Equiv.coe_fn_mk, encode_decode, encode_act, translate]
  funext h
  simp only [global, hd, equiv, encode_act, translate]

/-- Definition 2.1, expressed coordinate by coordinate on actual configurations. -/
theorem global_lazy (S : Finset G) (p x : Bits) (g : G) :
    global (lazyMap S p) x g =
      if ∀ h ∈ S, x (gm h g) = p h then !(x g) else x g := by
  change encode (decode _) g = _
  rw [encode_decode]
  simp only [encode_act, encode_decode, e_gm]

def freeSet (b : Bool) : Set X := {x | freeOrbit x = some b}
def pairSet (s : Fin 3) : Set X := {x | ∃ b, x = .p s b}
def constantSet : Set X := {x | ∃ b, x = .c b}

theorem freeSet_param : ∀ b x, x ∈ freeSet b ↔ ∃ g, x = .f b g := by
  change ∀ b x, freeOrbit x = some b ↔ ∃ g, x = .f b g
  decide

theorem freeSet_weight : ∀ b x, x ∈ freeSet b ↔ weight (encode x) = if b then 3 else 1 := by
  change ∀ b x, freeOrbit x = some b ↔ weight (encode x) = if b then 3 else 1
  decide

theorem image_freeSet (T : CA) (b : Bool) :
    T '' freeSet b = Set.range (fun g => act g (T (.f b e))) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := (freeSet_param b x).mp hx
    exact ⟨g, (equiv T g (.f b e)).symm.trans (congrArg T (free_rep b g))⟩
  · rintro ⟨g, rfl⟩
    refine ⟨.f b g, (freeSet_param b _).mpr ⟨g, rfl⟩, ?_⟩
    rw [← free_rep b g, equiv]

theorem orbit_eq_freeSet (x : X) (b : Bool) :
    Set.range (fun g => act g x) = freeSet b ↔ freeOrbit x = some b := by
  have h : ∀ x b,
      (∀ y, (∃ g, act g x = y) ↔ freeOrbit y = some b) ↔ freeOrbit x = some b := by decide
  rw [Set.ext_iff]
  exact h x b

/-- The representative definition is exactly the note's orbit-image merger. -/
theorem merges_iff_orbit_images (T : CA) : Merges T ↔
    ∃ b, T '' freeSet false = freeSet b ∧ T '' freeSet true = freeSet b := by
  simp only [image_freeSet, orbit_eq_freeSet, Merges]

theorem witness_iff_sets (T : X → X) : Witness T ↔
    ∃ s b, ∀ x ∈ constantSet ∪ pairSet s, T x = .c b := by
  constructor
  · rintro ⟨s, b, h0, h1, hp0, hp1⟩
    refine ⟨s, b, ?_⟩
    intro x hx
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> cases a <;> assumption
  · rintro ⟨s, b, h⟩
    exact ⟨s, b, h _ (Or.inl ⟨false, rfl⟩), h _ (Or.inl ⟨true, rfl⟩),
      h _ (Or.inr ⟨false, rfl⟩), h _ (Or.inr ⟨true, rfl⟩)⟩

/-- The main result in the literal orbit language of Theorem 1.1. -/
theorem membership_iff_orbits (T : CA) : T ∈ M ↔
    ((∃ b, T '' freeSet false = freeSet b ∧ T '' freeSet true = freeSet b) →
      ∃ s b, ∀ x ∈ constantSet ∪ pairSet s, T x = .c b) := by
  rw [membership_iff]
  unfold Criterion
  rw [merges_iff_orbit_images]
  exact imp_congr Iff.rfl (witness_iff_sets (fun x => T x))

end KleinFour

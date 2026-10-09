import KleinFour.Generators

namespace KleinFour

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def freeOffset : X → G
  | .f _ g => g
  | _ => e

def normalizeSwap (f : Free) : Bool :=
  match freeOrbit (f false), freeOrbit (f true) with
  | some j, _ => j
  | none, some j => !j
  | none, none => false

def normalizer (f : Free) : CA :=
  unit false (fun _ => false) (normalizeSwap f) (fun b => freeOffset (f b))

def residual (f : Free) (b : Bool) : CA :=
  if freeOrbit (f b) = none then freeCollapse (xor b (normalizeSwap f)) (f b) else 1

def FreeMerges (f : Free) : Prop :=
  ∃ b, freeOrbit (f false) = some b ∧ freeOrbit (f true) = some b

instance (f : Free) : Decidable (FreeMerges f) := inferInstanceAs (Decidable (∃ b, _))

theorem residual_mem (f b) : residual f b ∈ M := by
  unfold residual
  split
  · exact freeCollapse_mem _ _ ‹_›
  · exact M.one_mem

theorem normalizer_lower : ∀ f x, freeOrbit x = none → normalizer f x = x := by
  dsimp only [normalizer, unit, Table.ca]
  decide
theorem residual_lower : ∀ f b x, freeOrbit x = none → residual f b x = x := by
  intro f b x hx
  unfold residual
  split
  · change (freeCollapse (xor b (normalizeSwap f)) (f b)) x = x
    exact (by
      dsimp only [freeCollapse, Table.ca]
      decide : ∀ j y x, freeOrbit x = none → freeCollapse j y x = x)
        _ _ x hx
  · rfl

theorem lowerMap_free (l : Lower) (b : Bool) (g : G) : lowerMap l (.f b g) = .f b g := by
  change act g (.f b e) = .f b g
  exact free_rep b g

theorem normalizer_free : ∀ f b g, ∃ j h, normalizer f (.f b g) = .f j h := by
  dsimp only [normalizer, unit, Table.ca]
  decide

/-- Proposition 2.5: a partial permutation extends to a unit. The check has
only the two free representative images as parameters (16² possibilities). -/
theorem nonmerge_free_factor : ∀ f,
    ¬ FreeMerges f → ∀ b g,
    (residual f true * residual f false * normalizer f) (.f b g) = act g (f b) := by
  simp only [mul_apply]
  dsimp only [residual, normalizer, unit, freeCollapse, Table.ca]
  decide

theorem nonmerge_factor (t : Table) (h : ¬ Merges t.ca) :
    t.ca = residual t.free true * residual t.free false * lowerMap t.lower * normalizer t.free := by
  ext x
  cases x with
  | c b =>
    change X.c (t.lower.c b) = residual t.free true
      (residual t.free false (lowerMap t.lower (normalizer t.free (.c b))))
    rw [normalizer_lower _ _ rfl]
    change X.c (t.lower.c b) = residual t.free true (residual t.free false (.c (t.lower.c b)))
    rw [residual_lower t.free false _ rfl, residual_lower t.free true _ rfl]
  | p s b =>
    change smallRun s (t.lower.p s) b = residual t.free true
      (residual t.free false (lowerMap t.lower (normalizer t.free (.p s b))))
    rw [normalizer_lower _ _ rfl]
    change smallRun s (t.lower.p s) b = residual t.free true
      (residual t.free false (smallRun s (t.lower.p s) b))
    have hp : freeOrbit (smallRun s (t.lower.p s) b) = none :=
      (by decide : ∀ s d b, freeOrbit (smallRun s d b) = none) _ _ _
    rw [residual_lower _ _ _ hp, residual_lower _ _ _ hp]
  | f b g =>
    change act g (t.free b) = residual t.free true
      (residual t.free false (lowerMap t.lower (normalizer t.free (.f b g))))
    obtain ⟨j, a, ha⟩ := normalizer_free t.free b g
    rw [ha, lowerMap_free, ← ha]
    have h' : ¬ FreeMerges t.free := by
      simpa only [Merges, FreeMerges, Table.ca, Table.run, act_e] using h
    exact (nonmerge_free_factor t.free h' b g).symm

theorem nonmerge_mem (T : CA) (h : ¬ Merges T) : T ∈ M := by
  have h' : ¬ Merges (tableOf T).ca := by rwa [ca_tableOf]
  rw [← ca_tableOf T, nonmerge_factor _ h']
  exact M.mul_mem (M.mul_mem (M.mul_mem (residual_mem _ _) (residual_mem _ _))
    (lowerMap_mem _)) (unit_mem _ _ _ _)

/-- Equation (3.1): B_s flips a central one whose s-neighbor is also one. -/
def B (s : Fin 3) : CA := lazyMap {e, kernelCell s} (fun _ => true)

theorem B_mem (s) : B s ∈ M := lazy_mem _ _ (by simp)

theorem B_lower : ∀ s x, freeOrbit x = none →
    B s x = match x with
      | .c _ => .c false
      | .p t b => if t = s then .c false else .p t b
      | _ => x := by
  dsimp only [B, lazyMap, ofRule]
  decide

theorem B_free : ∀ s b g, B s (.f b g) = .f false (gm (if b then kernelCell s else e) g) := by
  dsimp only [B, lazyMap, ofRule]
  decide

def mergeNormalizer (s : Fin 3) (f : Free) : CA :=
  unit false (fun _ => false) false
    (fun b => gm (if b then kernelCell s else e) (freeOffset (f b)))

theorem mergeNormalizer_free (s : Fin 3) (f : Free) (b : Bool) (g : G) :
    mergeNormalizer s f (.f b g) =
      .f b (gm (gm (if b then kernelCell s else e) (freeOffset (f b))) g) := by
  cases b <;> rfl

def mergeR (l : Lower) (q : Bool) : CA :=
  ({ lower := l, free := fun b => .f (xor b q) e } : Table).ca

theorem mergeR_first (l : Lower) (q : Bool) (g : G) :
    mergeR l q (.f false g) = act g (.f q e) := by
  cases q <;> rfl

theorem mergeR_not_merges : ∀ l q, ¬ Merges (mergeR l q) := by
  intro l q
  exact (by decide : ∀ q, ¬ FreeMerges (fun b => X.f (xor b q) e)) q

theorem merge_free_factor (l : Lower) : ∀ s f q,
    freeOrbit (f false) = some q → freeOrbit (f true) = some q → ∀ b g,
    act g (f b) = mergeR l q (B s (mergeNormalizer s f (.f b g))) := by
  intro s f q h0 h1 b g
  rw [mergeNormalizer_free, B_free, mergeR_first]
  exact (by decide : ∀ s f q,
    freeOrbit (f false) = some q → freeOrbit (f true) = some q → ∀ b g,
    act g (f b) = act
      (gm (if b then kernelCell s else e)
        (gm (gm (if b then kernelCell s else e) (freeOffset (f b))) g)) (.f q e))
      s f q h0 h1 b g

/-- Proposition 3.3: the three-factor construction for a merging member. -/
theorem merge_factor (t : Table) (s : Fin 3) (a q : Bool)
    (h0 : t.ca (.c false) = .c a) (h1 : t.ca (.c true) = .c a)
    (hp0 : t.ca (.p s false) = .c a) (hp1 : t.ca (.p s true) = .c a)
    (hf0 : freeOrbit (t.free false) = some q) (hf1 : freeOrbit (t.free true) = some q) :
    t.ca = mergeR t.lower q * B s * mergeNormalizer s t.free := by
  ext x
  cases x with
  | c b =>
    have hc : ∀ b, t.ca (.c b) = .c a := by intro b; cases b <;> assumption
    change t.ca (.c b) = mergeR t.lower q (B s (mergeNormalizer s t.free (.c b)))
    have hn : mergeNormalizer s t.free (.c b) = .c b := by
      change .c (xor b false) = X.c b
      cases b <;> rfl
    rw [hn, B_lower _ _ rfl]
    exact (hc b).trans (hc false).symm
  | p r b =>
    change t.ca (.p r b) = mergeR t.lower q (B s (mergeNormalizer s t.free (.p r b)))
    have hn : mergeNormalizer s t.free (.p r b) = .p r b := by
      change smallRun r (true, false) b = .p r b
      cases b <;> rfl
    rw [hn, B_lower _ _ rfl]
    by_cases hr : r = s
    · subst r
      simp only [if_pos rfl]
      have hp : t.ca (.p s b) = .c a := by cases b <;> assumption
      exact hp.trans h0.symm
    · simp only [if_neg hr]
      rfl
  | f b g => exact merge_free_factor t.lower s t.free q hf0 hf1 b g

theorem criterion_implies_membership (T : CA) (h : Criterion T) : T ∈ M := by
  by_cases hm : Merges T
  · obtain ⟨q, hf0, hf1⟩ := hm
    obtain ⟨s, a, h0, h1, hp0, hp1⟩ := h ⟨q, hf0, hf1⟩
    let t := tableOf T
    have ht : t.ca = T := ca_tableOf T
    have heq := merge_factor t s a q (ht.symm ▸ h0) (ht.symm ▸ h1)
      (ht.symm ▸ hp0) (ht.symm ▸ hp1) hf0 hf1
    rw [← ht, heq]
    exact M.mul_mem (M.mul_mem (nonmerge_mem _ (mergeR_not_merges _ _)) (B_mem _))
      (unit_mem _ _ _ _)
  · exact nonmerge_mem T hm

end KleinFour

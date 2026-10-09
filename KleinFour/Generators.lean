import KleinFour.Tables

namespace KleinFour

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def unit (cflip : Bool) (pflip : Fin 3 → Bool) (swap : Bool) (offset : Bool → G) : CA :=
  ({ lower := { c := fun b => xor b cflip, p := fun s => (true, pflip s) },
     free := fun b => .f (xor b swap) (offset b) } : Table).ca

def unitInv (cflip : Bool) (pflip : Fin 3 → Bool) (swap : Bool) (offset : Bool → G) : CA :=
  unit cflip pflip swap (fun b => offset (xor b swap))

theorem unit_left (c p s o) : unitInv c p s o * unit c p s o = 1 := by
  ext x
  cases x with
  | c b => exact (by decide : ∀ c b : Bool, X.c (xor (xor b c) c) = X.c b) c b
  | p t b => exact (by decide : ∀ (t : Fin 3) (a b : Bool), X.p t (xor a (xor a b)) = X.p t b) t (p t) b
  | f b g =>
    change X.f (xor (xor b s) s) (gm (o (xor (xor b s) s)) (gm (o b) g)) = X.f b g
    exact (by decide : ∀ s (o : Bool → G) b g,
      X.f (xor (xor b s) s) (gm (o (xor (xor b s) s)) (gm (o b) g)) = X.f b g) s o b g

theorem unit_right (c p s o) : unit c p s o * unitInv c p s o = 1 := by
  ext x
  cases x with
  | c b => exact (by decide : ∀ c b : Bool, X.c (xor (xor b c) c) = X.c b) c b
  | p t b => exact (by decide : ∀ (t : Fin 3) (a b : Bool), X.p t (xor a (xor a b)) = X.p t b) t (p t) b
  | f b g =>
    change X.f (xor (xor b s) s) (gm (o (xor b s)) (gm (o (xor b s)) g)) = X.f b g
    exact (by decide : ∀ s (o : Bool → G) b g,
      X.f (xor (xor b s) s) (gm (o (xor b s)) (gm (o (xor b s)) g)) = X.f b g) s o b g

theorem unit_ICA (c p s o) : unit c p s o ∈ ICA := by
  constructor
  · intro x y h
    have h' := congrArg (unitInv c p s o) h
    simpa only [← mul_apply, unit_left, one_apply] using h'
  · intro y
    refine ⟨unitInv c p s o y, ?_⟩
    simpa only [← mul_apply, unit_right, one_apply]

theorem ICA_mem {T : CA} (h : T ∈ ICA) : T ∈ M := Submonoid.subset_closure (Or.inl h)
theorem lazy_mem (S : Finset G) (p : Bits) (h : e ∈ S) : lazyMap S p ∈ M :=
  Submonoid.subset_closure (Or.inr ⟨S, p, h, rfl⟩)
theorem fullLazy_mem (x : X) : lazyMap Finset.univ (encode x) ∈ M :=
  lazy_mem _ _ (Finset.mem_univ _)
theorem unit_mem (c p s o) : unit c p s o ∈ M := ICA_mem (unit_ICA c p s o)
theorem unitInv_mem (c p s o) : unitInv c p s o ∈ M := unit_mem _ _ _ _

def constantCollapse (b : Bool) : CA :=
  ({ lower := { c := fun _ => b, p := fun _ => (true, false) },
     free := fun j => .f j e } : Table).ca

def pairCollapse (s : Fin 3) (b : Bool) : CA :=
  ({ lower := { c := id, p := fun t => if t = s then (false, b) else (true, false) },
     free := fun j => .f j e } : Table).ca

def freeCollapse (j : Bool) (y : X) : CA :=
  ({ lower := { c := id, p := fun _ => (true, false) },
     free := fun k => if k = j then y else .f k e } : Table).ca

/-- Lemma 2.4: fixed-point and two-point collapses are full-neighborhood lazy. -/
theorem constantCollapse_lazy : ∀ b x,
    constantCollapse b x = lazyMap Finset.univ (encode (.c (!b))) x := by
  dsimp only [constantCollapse, Table.ca, lazyMap, ofRule]
  decide
theorem pairCollapse_lazy : ∀ s b x,
    pairCollapse s b x = lazyMap Finset.univ (encode (.p s (!b))) x := by
  dsimp only [pairCollapse, Table.ca, lazyMap, ofRule]
  decide

theorem constantCollapse_mem (b) : constantCollapse b ∈ M := by
  have h : constantCollapse b = lazyMap Finset.univ (encode (.c (!b))) := CA.ext (constantCollapse_lazy b)
  rw [h]; exact fullLazy_mem _

theorem pairCollapse_mem (s b) : pairCollapse s b ∈ M := by
  have h : pairCollapse s b = lazyMap Finset.univ (encode (.p s (!b))) := CA.ext (pairCollapse_lazy s b)
  rw [h]; exact fullLazy_mem _

def kernelCell (s : Fin 3) : G :=
  if s = 0 then (false, true) else if s = 1 then (true, false) else (true, true)

def freeToPairUnit (j : Bool) (s : Fin 3) (b : Bool) : CA :=
  unit false (fun t => if t = s then !b else false) j (fun _ => kernelCell s)

def freeToPairUnitInv (j : Bool) (s : Fin 3) (b : Bool) : CA :=
  unitInv false (fun t => if t = s then !b else false) j (fun _ => kernelCell s)

/-- Lemma 2.4's conjugation, checked only on the elementary collapses. -/
theorem freeToConstant_factor : ∀ j b x,
    freeCollapse j (.c b) x =
      (unit b (fun _ => false) j (fun _ => e) *
        lazyMap Finset.univ (encode (.f false e)) *
        unitInv b (fun _ => false) j (fun _ => e)) x := by
  simp only [mul_apply]
  dsimp only [freeCollapse, unit, unitInv, Table.ca, lazyMap, ofRule]
  decide

theorem freeToPair_factor : ∀ j s b x,
    freeCollapse j (.p s b) x =
      (freeToPairUnit j s b * lazyMap Finset.univ (encode (.f false (kernelCell s))) *
        freeToPairUnitInv j s b) x := by
  simp only [mul_apply]
  dsimp only [freeCollapse, freeToPairUnit, freeToPairUnitInv, unit, unitInv, Table.ca, lazyMap, ofRule]
  decide

theorem freeCollapse_mem (j : Bool) (y : X) (hy : freeOrbit y = none) : freeCollapse j y ∈ M := by
  cases y with
  | c b =>
    rw [CA.ext (freeToConstant_factor j b)]
    exact M.mul_mem (M.mul_mem (unit_mem _ _ _ _) (fullLazy_mem _)) (unitInv_mem _ _ _ _)
  | p s b =>
    rw [CA.ext (freeToPair_factor j s b)]
    exact M.mul_mem (M.mul_mem (unit_mem _ _ _ _) (fullLazy_mem _)) (unitInv_mem _ _ _ _)
  | f b g => simp [freeOrbit] at hy

def lowerMap (l : Lower) : CA :=
  ({ lower := l, free := fun j => .f j e } : Table).ca

def constantPart (c : Bool → Bool) : CA :=
  if c false = c true then constantCollapse (c false)
  else unit (c false) (fun _ => false) false (fun _ => e)

def pairPart (s : Fin 3) (d : Small) : CA :=
  if d.1 then unit false (fun t => if t = s then d.2 else false) false (fun _ => e)
  else pairCollapse s d.2

theorem constantPart_mem (c) : constantPart c ∈ M := by
  unfold constantPart
  split
  · exact constantCollapse_mem _
  · exact unit_mem _ _ _ _

theorem pairPart_mem (s d) : pairPart s d ∈ M := by
  unfold pairPart
  split
  · exact unit_mem _ _ _ _
  · exact pairCollapse_mem _ _

theorem lower_factor : ∀ l x,
    lowerMap l x = (pairPart 2 (l.p 2) * pairPart 1 (l.p 1) * pairPart 0 (l.p 0) *
      constantPart l.c) x := by
  simp only [mul_apply]
  dsimp only [lowerMap, pairPart, constantPart, pairCollapse, constantCollapse, unit, Table.ca]
  decide

/-- Proposition 2.5: the lower stratum is generated independently. -/
theorem lowerMap_mem (l) : lowerMap l ∈ M := by
  rw [CA.ext (lower_factor l)]
  exact M.mul_mem (M.mul_mem (M.mul_mem (pairPart_mem _ _) (pairPart_mem _ _))
    (pairPart_mem _ _)) (constantPart_mem _)

end KleinFour

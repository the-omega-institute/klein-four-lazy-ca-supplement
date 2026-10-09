import KleinFour.LazyBoolean

namespace KleinFour.LazyCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem agrees_eq {a b : Table} (h : Agrees a b) : a = b := by
  cases a with
  | mk al af =>
    cases b with
    | mk bl bf =>
      cases al with
      | mk ac ap =>
        cases bl with
        | mk bc bp =>
          obtain ⟨hc, hp, hf⟩ := h
          have hc' : ac = bc := funext hc
          have hp' : ap = bp := funext hp
          have hf' : af = bf := funext hf
          cases hc'; cases hp'; cases hf'; rfl

def neighborhood (g : Fin 54) : Finset G :=
  Finset.univ.filter (fun h => bits neighborhoods[g.val]! h = true)
def pattern (g : Fin 54) : Bits := bits patterns[g.val]!

theorem generators_checked : ∀ g : Fin 54,
    e ∈ neighborhood g ∧ Agrees (tableOf (generator g)) (tableOf (lazyMap (neighborhood g) (pattern g))) := by
  dsimp only [Agrees, tableOf, generator, Table.ca, Table.run, lazyMap, ofRule]
  decide

theorem lazy_covered_check : ∀ (S : Finset G) (p : Bits), e ∈ S →
    ∃ g : Fin 54, Agrees (tableOf (lazyMap S p)) (tableOf (generator g)) := by
  dsimp only [Agrees, tableOf, generator, Table.ca, Table.run, lazyMap, ofRule]
  decide

theorem generator_in_L (g : Fin 54) : generator g ∈ L := by
  refine ⟨neighborhood g, pattern g, (generators_checked g).1, ?_⟩
  exact tables.injective (agrees_eq (generators_checked g).2)

theorem lazy_covered (T : CA) (h : T ∈ L) : ∃ g, T = generator g := by
  obtain ⟨S, p, hS, rfl⟩ := h
  obtain ⟨g, hg⟩ := lazy_covered_check S p hS
  exact ⟨g, tables.injective (agrees_eq hg)⟩

theorem root_check : ∀ x, member 0 x = x := by
  dsimp only [member, Table.ca, Table.run]
  decide

end KleinFour.LazyCertificate

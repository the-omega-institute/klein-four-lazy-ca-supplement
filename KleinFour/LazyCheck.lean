import KleinFour.LazyData

namespace KleinFour.LazyCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def bit (n k : Nat) : Bool := decide (n / 2^k % 2 = 1)
def bits (n : Nat) (g : G) : Bool := bit n (g.1.toNat + 2 * g.2.toNat)
def unpack (n : Nat) : Table :=
  { lower := { c := fun b => bit n b.toNat,
               p := fun s => (bit n (3 + 2*s.val), bit n (2 + 2*s.val)) },
    free := fun b => decode (bits (n / (if b then 4096 else 256) % 16)) }

def pack (t : Table) : Nat :=
  (t.lower.c false).toNat + 2 * (t.lower.c true).toNat +
  4 * ((t.lower.p 0).2.toNat + 2 * (t.lower.p 0).1.toNat) +
  16 * ((t.lower.p 1).2.toNat + 2 * (t.lower.p 1).1.toNat) +
  64 * ((t.lower.p 2).2.toNat + 2 * (t.lower.p 2).1.toNat) +
  256 * bitNumber (encode (t.free false)) + 4096 * bitNumber (encode (t.free true))

def member (i : Fin 4007) : CA := (unpack (codesAt i.val)).ca
def generator (g : Fin 54) : CA := (unpack (generatorCodes[g.val]!)).ca
def lookup (t : Table) : Fin 4007 := ⟨searchFind (pack t) % 4007, Nat.mod_lt _ (by decide)⟩

def Agrees (a b : Table) : Prop :=
  (∀ i, a.lower.c i = b.lower.c i) ∧ (∀ s, a.lower.p s = b.lower.p s) ∧
    (∀ i, a.free i = b.free i)

instance (a b : Table) : Decidable (Agrees a b) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ _ ∧ _))

def edge (i : Fin 4007) (g : Fin 54) : Prop :=
  let t := tableOf (generator g * member i)
  Agrees (tableOf (member (lookup t))) t

instance (i : Fin 4007) (g : Fin 54) : Decidable (edge i g) :=
  inferInstanceAs (Decidable (Agrees (tableOf (member (lookup (tableOf (generator g * member i))))) _))

theorem sample_edges : ∀ i : Fin 8, ∀ g : Fin 54,
    edge ⟨i.val, by omega⟩ g := by
  dsimp only [edge, Agrees, tableOf, member, generator, Table.ca, Table.run]
  decide

end KleinFour.LazyCertificate

import KleinFour.LazyBoolean

namespace KleinFour.LazyCertificate

set_option maxRecDepth 100000

def parent (i : Fin 4007) : Fin 4007 := ⟨parentsAt i.val % 4007, Nat.mod_lt _ (by decide)⟩
def finalGenerator (i : Fin 4007) : Fin 54 := ⟨lastGeneratorAt i.val % 54, Nat.mod_lt _ (by decide)⟩

def parentBoolean (i : Fin 4007) : Bool :=
  if i.val = 0 then true else decide ((parent i).val < i.val) &&
    tableEqb (unpack (codesAt i.val)) (compose
      (unpack generatorCodes[(finalGenerator i).val]!) (unpack (codesAt (parent i).val)))

def indexBoolean (i : Fin 4007) : Bool :=
  (lookup (unpack (codesAt i.val))).val == i.val

def blockIndex (b : Nat) (i : Fin 64) : Fin 4007 :=
  ⟨(64*b + i.val) % 4007, Nat.mod_lt _ (by decide)⟩

def CheckBlock (b : Nat) : Prop :=
  (∀ i : Fin 64, parentBoolean (blockIndex b i) = true ∧ indexBoolean (blockIndex b i) = true) ∧
    (∀ i : Fin 64, ∀ g : Fin 54, booleanEdge (blockIndex b i) g = true)

end KleinFour.LazyCertificate

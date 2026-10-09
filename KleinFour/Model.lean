import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum

/-!
# The binary Klein-four shift (note §2, Lemma 2.2)

The seven-orbit model is equivalent to the actual binary configuration space.
All the small finite verifications in this file use kernel reduction (`decide`).
-/

namespace KleinFour

abbrev G := Bool × Bool

def gm (g h : G) : G := (xor g.1 h.1, xor g.2 h.2)
def e : G := (false, false)

theorem gm_assoc : ∀ a b c : G, gm (gm a b) c = gm a (gm b c) := by decide
theorem gm_comm : ∀ a b : G, gm a b = gm b a := by decide
theorem gm_self : ∀ a : G, gm a a = e := by decide
theorem gm_e : ∀ a : G, gm a e = a := by decide
theorem e_gm : ∀ a : G, gm e a = a := by decide

def character (s : Fin 3) (g : G) : Bool :=
  if s = 0 then g.1 else if s = 1 then g.2 else xor g.1 g.2

def shift (s : Fin 3) (b : Bool) : G :=
  if s = 1 then (false, b) else (b, false)

theorem character_gm : ∀ s g h, character s (gm g h) = xor (character s g) (character s h) := by decide
theorem character_shift : ∀ s b, character s (shift s b) = b := by decide

inductive X
  | c : Bool → X
  | p : Fin 3 → Bool → X
  | f : Bool → G → X
  deriving DecidableEq, Fintype

def act (g : G) : X → X
  | .c b => .c b
  | .p s b => .p s (xor b (character s g))
  | .f b h => .f b (gm h g)

theorem act_e : ∀ x, act e x = x := by decide
theorem act_act : ∀ g h x, act g (act h x) = act (gm g h) x := by decide
theorem act_self : ∀ g x, act g (act g x) = x := by decide

abbrev Bits := G → Bool

/-- The constants, three complementary pairs, and weight-one/weight-three orbits. -/
def encode : X → Bits
  | .c b => fun _ => b
  | .p s b => fun h => xor b (character s h)
  | .f b g => fun h => xor b (decide (h = g))

def bitNumber (x : Bits) : Nat :=
  (x (false, false)).toNat + 2 * (x (true, false)).toNat +
    4 * (x (false, true)).toNat + 8 * (x (true, true)).toNat

/-- Explicit inverse, so local-rule and lazy-map computations remain reducible. -/
def decode (x : Bits) : X :=
  match bitNumber x with
  | 0 => .c false
  | 15 => .c true
  | 1 => .f false (false, false)
  | 2 => .f false (true, false)
  | 4 => .f false (false, true)
  | 8 => .f false (true, true)
  | 14 => .f true (false, false)
  | 13 => .f true (true, false)
  | 11 => .f true (false, true)
  | 7 => .f true (true, true)
  | 10 => .p 0 false
  | 5 => .p 0 true
  | 12 => .p 1 false
  | 3 => .p 1 true
  | 6 => .p 2 false
  | _ => .p 2 true

theorem decode_encode : ∀ x, decode (encode x) = x := by decide
theorem encode_decode : ∀ x, encode (decode x) = x := by decide

def configurations : X ≃ Bits :=
  { toFun := encode, invFun := decode, left_inv := decode_encode, right_inv := encode_decode }

theorem encode_act : ∀ g x h, encode (act g x) h = encode x (gm h g) := by decide

def Equivariant (T : X → X) : Prop := ∀ g x, T (act g x) = act g (T x)

def equivariantSubmonoid : Submonoid (Function.End X) where
  carrier := {T | Equivariant T}
  one_mem' := by intro g x; rfl
  mul_mem' := by
    intro A B hA hB g x
    change A (B (act g x)) = act g (A (B x))
    rw [hB, hA]

abbrev CA := equivariantSubmonoid

instance : CoeFun CA (fun _ => X → X) := ⟨fun T => T.val⟩

@[ext] theorem CA.ext {A B : CA} (h : ∀ x, A x = B x) : A = B :=
  Subtype.ext (funext h)

theorem equiv (T : CA) (g : G) (x : X) : T (act g x) = act g (T x) := T.property g x

@[simp] theorem mul_apply (A B : CA) (x : X) : (A * B) x = A (B x) := rfl
@[simp] theorem one_apply (x : X) : (1 : CA) x = x := rfl

/-- §2: every local rule gives a cellular automaton. -/
def ofRule (r : X → Bool) : CA :=
  ⟨fun x => decode (fun g => r (act g x)), by
    intro g x
    apply configurations.injective
    funext h
    simp only [configurations, Equiv.coe_fn_mk, encode_decode, encode_act]
    rw [act_act, gm_comm]⟩

theorem rule_reconstruction (T : CA) : ofRule (fun x => encode (T x) e) = T := by
  ext x
  apply configurations.injective
  funext g
  simp only [ofRule, configurations, Equiv.coe_fn_mk, encode_decode]
  rw [equiv, encode_act, e_gm]

/-- Definition 2.1: identity except at occurrences of one pattern on a
neighborhood containing the identity; there the binary central symbol flips. -/
def lazyMap (S : Finset G) (p : Bits) : CA :=
  ofRule (fun x => if ∀ h ∈ S, encode x h = p h then !(encode x e) else encode x e)

def ICA : Set CA := {T | Function.Bijective T}
def L : Set CA := {T | ∃ S p, e ∈ S ∧ T = lazyMap S p}
def M : Submonoid CA := Submonoid.closure (ICA ∪ L)

def freeOrbit : X → Option Bool
  | .f b _ => some b
  | _ => none

/-- Equation (2.3): the two free orbits have the same free image. -/
def Merges (T : X → X) : Prop :=
  ∃ b, freeOrbit (T (.f false e)) = some b ∧ freeOrbit (T (.f true e)) = some b

/-- Equation (3.2), Theorem 1.1: constants and one pair share a constant image. -/
def Witness (T : X → X) : Prop :=
  ∃ s b, T (.c false) = .c b ∧ T (.c true) = .c b ∧
    T (.p s false) = .c b ∧ T (.p s true) = .c b

def Criterion (T : X → X) : Prop := Merges T → Witness T

instance (T : X → X) : Decidable (Merges T) := inferInstanceAs (Decidable (∃ b, _))
instance (T : X → X) : Decidable (Witness T) := inferInstanceAs (Decidable (∃ s b, _))
instance (T : X → X) : Decidable (Criterion T) := inferInstanceAs (Decidable (_ → _))

end KleinFour

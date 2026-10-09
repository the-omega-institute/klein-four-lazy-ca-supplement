import KleinFour.LazyBounded
import KleinFour.LazyFamilies

namespace KleinFour

def D : Submonoid CA := Submonoid.closure L

namespace LazyCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

abbrev ParentCertificate := ∀ i : Fin 4007, parentBoolean i = true ∧ indexBoolean i = true

abbrev EdgeCertificate := ∀ i : Fin 4007, ∀ g : Fin 54, booleanEdge i g = true

theorem parent_check (hcertificate : ParentCertificate) (i : Fin 4007) : i.val = 0 ∨
    (parent i).val < i.val ∧ member i = generator (finalGenerator i) * member (parent i) := by
  have h := (hcertificate i).1
  unfold parentBoolean at h
  split at h
  · exact Or.inl ‹_›
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hlt, heq⟩ := h
    have hc : member i = (compose (unpack generatorCodes[(finalGenerator i).val]!)
        (unpack (codesAt (parent i).val))).ca :=
      congrArg Table.ca (agrees_eq (tableEqb_agrees heq))
    exact Or.inr ⟨of_decide_eq_true hlt, hc.trans (compose_ca _ _)⟩

theorem index_check (hcertificate : ParentCertificate) (i : Fin 4007) : lookup (tableOf (member i)) = i := by
  have h := (hcertificate i).2
  change lookup (tableOf (unpack (codesAt i.val)).ca) = i
  rw [tableOf_ca]
  apply Fin.ext
  simpa only [indexBoolean, beq_iff_eq] using h

theorem member_zero : member 0 = 1 := CA.ext root_check

theorem member_reachable (hcertificate : ParentCertificate) (i : Fin 4007) : member i ∈ D := by
  have all : ∀ n (hn : n < 4007), member ⟨n, hn⟩ ∈ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases parent_check hcertificate ⟨n, hn⟩ with hzero | ⟨hlt, heq⟩
      · have hi : (⟨n, hn⟩ : Fin 4007) = 0 := Fin.ext hzero
        rw [hi, member_zero]
        exact D.one_mem
      · have hp := ih (parent ⟨n, hn⟩).val hlt (parent ⟨n, hn⟩).isLt
        rw [heq]
        exact D.mul_mem (Submonoid.subset_closure (generator_in_L _)) hp
  exact all i.val i.isLt

theorem edge_eq (hedges : EdgeCertificate) (i : Fin 4007) (g : Fin 54) :
    generator g * member i = member (lookup (compose
      (unpack generatorCodes[g.val]!) (unpack (codesAt i.val)))) := by
  let t := compose (unpack generatorCodes[g.val]!) (unpack (codesAt i.val))
  have hb : tableEqb (unpack (codesAt (lookup t).val)) t = true := hedges i g
  have heq := congrArg Table.ca (agrees_eq (tableEqb_agrees hb))
  exact (compose_ca _ _).symm.trans heq.symm

theorem D_in_range (hedges : EdgeCertificate) (T : CA) (hT : T ∈ D) : ∃ i, T = member i := by
  change T ∈ Submonoid.closure L at hT
  have action : ∀ i, ∃ j, T * member i = member j := by
    induction hT using Submonoid.closure_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := lazy_covered A hA
      intro i
      exact ⟨_, edge_eq hedges i g⟩
    | one => intro i; exact ⟨i, one_mul _⟩
    | mul A B hA hB ihA ihB =>
      intro i
      obtain ⟨j, hj⟩ := ihB i
      obtain ⟨k, hk⟩ := ihA j
      exact ⟨k, by rw [mul_assoc, hj, hk]⟩
  obtain ⟨i, hi⟩ := action 0
  exact ⟨i, by simpa only [member_zero, mul_one] using hi⟩

noncomputable def enumeration (hparents : ParentCertificate) (hedges : EdgeCertificate) : Fin 4007 ≃ D := Equiv.ofBijective
  (fun i => ⟨member i, member_reachable hparents i⟩) (by
    constructor
    · intro i j hij
      have h := congrArg (fun T : D => lookup (tableOf T.val)) hij
      simpa only [index_check hparents] using h
    · intro T
      obtain ⟨i, hi⟩ := D_in_range hedges T.val T.property
      exact ⟨i, Subtype.ext hi.symm⟩)

theorem card_if_certificate (hparents : ParentCertificate) (hedges : EdgeCertificate) : Nat.card D = 4007 := by
  rw [← Nat.card_congr (enumeration hparents hedges), Nat.card_eq_fintype_card, Fintype.card_fin]

end LazyCertificate
end KleinFour

import KleinFour.LazyEdges
import KleinFour.LazyReachable

namespace KleinFour

/-- Exact lazy-only cardinality, certified by the Lean kernel. -/
theorem lazy_membership_card : Nat.card D = 4007 :=
  LazyCertificate.card_if_certificate LazyCertificate.all_parent_indices
    LazyCertificate.all_boolean_edges

end KleinFour

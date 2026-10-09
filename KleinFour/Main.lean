import KleinFour.Closure
import KleinFour.Factorization

namespace KleinFour

/-- Theorem 1.1 of `klein_four_generation_v4.tex`, membership part. -/
theorem membership_iff (T : CA) : T ∈ M ↔ Criterion T :=
  ⟨membership_implies_criterion T, criterion_implies_membership T⟩

theorem generated_eq_criterion : (M : Set CA) = {T : CA | Criterion T} := by
  ext T
  exact membership_iff T

end KleinFour

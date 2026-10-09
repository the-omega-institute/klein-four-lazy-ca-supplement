import KleinFour.Tables

namespace KleinFour

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem freeOrbit_act : ∀ g x, freeOrbit (act g x) = freeOrbit x := by decide
theorem freeOrbit_some : ∀ x b, freeOrbit x = some b ↔ ∃ g, x = .f b g := by decide
theorem constantValue_c : ∀ b, constantValue (.c b) = b := by decide

theorem lower_no_free (T : CA) (x : X) (hx : freeOrbit x = none) : freeOrbit (T x) = none := by
  rw [← ca_tableOf T]
  cases x with
  | c b => rfl
  | p s b =>
    change freeOrbit (smallRun s ((tableOf T).lower.p s) b) = none
    exact (by decide : ∀ s d b, freeOrbit (smallRun s d b) = none) s _ b
  | f b g => simp [freeOrbit] at hx

theorem image_free_source (T : CA) (x : X) (b : Bool)
    (h : freeOrbit (T x) = some b) : ∃ j g, x = .f j g := by
  cases x with
  | c a => have := lower_no_free T (.c a) rfl; rw [h] at this; contradiction
  | p s a => have := lower_no_free T (.p s a) rfl; rw [h] at this; contradiction
  | f j g => exact ⟨j, g, rfl⟩

theorem same_free_translate : ∀ x y b,
    freeOrbit x = some b → freeOrbit y = some b → ∃ g, act g x = y := by decide

/-- Units do not merge free orbits, as used in Lemma 3.2. -/
theorem invertible_not_merges (T : CA) (hT : T ∈ ICA) : ¬ Merges T := by
  rintro ⟨b, h0, h1⟩
  obtain ⟨g, hg⟩ := same_free_translate _ _ b h0 h1
  have h := hT.1 ((equiv T g (.f false e)).trans hg)
  have : ∀ g, act g (.f false e) ≠ X.f true e := by decide
  exact this g h

theorem invertible_criterion (T : CA) (hT : T ∈ ICA) : Criterion T :=
  fun h => False.elim (invertible_not_merges T hT h)

/-- Lemma 3.1: check the finite neighborhood/pattern family, not all automata. -/
theorem lazy_criterion_check : ∀ (S : Finset G) (p : Bits),
    e ∈ S → Criterion (lazyMap S p) := by
  dsimp only [Criterion, Merges, Witness, lazyMap, ofRule]
  decide

theorem witness_postcompose (A B : CA) (hB : Witness B) : Witness (A * B) := by
  obtain ⟨s, b, h0, h1, hp0, hp1⟩ := hB
  obtain ⟨a, ha⟩ := constant_image A b
  exact ⟨s, a, by simp [h0, ha], by simp [h1, ha], by simp [hp0, ha], by simp [hp1, ha]⟩

theorem witness_precompose (A B : CA) (hA : Witness A) : Witness (A * B) := by
  obtain ⟨s, b, h0, h1, hp0, hp1⟩ := hA
  have hc : ∀ a, A (.c a) = .c b := by intro a; cases a <;> assumption
  have hp : ∀ a, A (.p s a) = .c b := by intro a; cases a <;> assumption
  have eval : ∀ d a, A (smallRun s d a) = .c b := by
    intro d a
    unfold smallRun
    split
    · exact hp _
    · exact hc _
  obtain ⟨a0, ha0⟩ := constant_image B false
  obtain ⟨a1, ha1⟩ := constant_image B true
  obtain ⟨d, hd⟩ := pair_image B s
  refine ⟨s, b, ?_, ?_, ?_, ?_⟩
  · simp [ha0, hc]
  · simp [ha1, hc]
  · simp [hd, eval]
  · rw [mul_apply, ← pair_rep s true, equiv, hd, smallRun_shift, eval]

/-- Structural composition argument from Lemma 3.2. -/
theorem criterion_mul (A B : CA) (hA : Criterion A) (hB : Criterion B) : Criterion (A * B) := by
  rintro ⟨b, h0, h1⟩
  simp only [mul_apply] at h0 h1
  obtain ⟨j0, g0, hj0⟩ := image_free_source A (B (.f false e)) b h0
  obtain ⟨j1, g1, hj1⟩ := image_free_source A (B (.f true e)) b h1
  by_cases h : j0 = j1
  · apply witness_postcompose
    apply hB
    exact ⟨j0, by simp [hj0, freeOrbit], by simp [hj1, h, freeOrbit]⟩
  · apply witness_precompose
    apply hA
    have h0' : freeOrbit (A (.f j0 e)) = some b := by
      rw [hj0, ← free_rep j0 g0, equiv, freeOrbit_act] at h0
      exact h0
    have h1' : freeOrbit (A (.f j1 e)) = some b := by
      rw [hj1, ← free_rep j1 g1, equiv, freeOrbit_act] at h1
      exact h1
    cases j0 <;> cases j1 <;> simp_all [Merges]

def criterionSubmonoid : Submonoid CA where
  carrier := {T | Criterion T}
  one_mem' := by decide
  mul_mem' := fun hA hB => criterion_mul _ _ hA hB

theorem membership_implies_criterion (T : CA) (hT : T ∈ M) : Criterion T := by
  have hle : M ≤ criterionSubmonoid := Submonoid.closure_le.mpr (by
    intro A hA
    rcases hA with hA | ⟨S, p, hS, rfl⟩
    · exact invertible_criterion A hA
    · exact lazy_criterion_check S p hS)
  exact hle hT

end KleinFour

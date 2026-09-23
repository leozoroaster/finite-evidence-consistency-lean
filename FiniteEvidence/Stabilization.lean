import FiniteEvidence.Core
import Mathlib.Tactic

namespace FiniteEvidence
universe u
variable {X : Type u}

theorem eventually_constant_of_relLE {α : Type*} {r : α → α → Prop} [IsTrans α r]
    (hwf : WellFounded r) (s : ℕ → α) (hstep : ∀ n, RelLE r (s (n + 1)) (s n)) :
    ∃ N, ∀ n, N ≤ n → s n = s N := by
  obtain ⟨a, ⟨N, rfl⟩, hmin⟩ := hwf.has_min (Set.range s) ⟨s 0, 0, rfl⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  rcases relLE_of_steps s hstep hn with heq | hlt
  · exact heq
  · exact (hmin (s n) ⟨n, rfl⟩ hlt).elim

theorem evidence_stabilizes {H : Set (Hypothesis X)} (O : EvidenceOrder H)
    (hwf : TargetWellFounded O) (h : Hypothesis X) (hh : h ∈ H) (xs : ℕ → X) :
    ∃ N, ∀ n, N ≤ n →
      O.select (observedTrace h hh xs n) = O.select (observedTrace h hh xs N) := by
  let s : ℕ → TraceOf H h := fun n ↦
    ⟨O.select (observedTrace h hh xs n), fun e he ↦
      historyAt_isTraceOf h xs n e (O.select_subset _ he)⟩
  let r : TraceOf H h → TraceOf H h → Prop := fun p q ↦ O.lt p.1 q.1
  letI : IsTrans (TraceOf H h) r := ⟨fun p q t ↦ O.strictTotal.trans p.1 q.1 t.1⟩
  have hstep (n : ℕ) : RelLE r (s (n + 1)) (s n) := by
    rcases select_antitone O (observedTrace_subset_succ h hh xs n) with heq | hlt
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hlt
  obtain ⟨N, hN⟩ := eventually_constant_of_relLE (hwf h hh) s hstep
  exact ⟨N, fun n hn ↦ congrArg Subtype.val (hN n hn)⟩

/-- The limiting predictor agrees with every example ever observed. -/
theorem stabilization_and_agreement {H : Set (Hypothesis X)} (O : EvidenceOrder H)
    (hsep : ConflictSeparating O) (hwf : TargetWellFounded O)
    (h : Hypothesis X) (hh : h ∈ H) (xs : ℕ → X) :
    ∃ N, (∀ n, N ≤ n →
        O.select (observedTrace h hh xs n) = O.select (observedTrace h hh xs N)) ∧
      ∀ i, decoded O (O.select (observedTrace h hh xs N)) (xs i) = h (xs i) := by
  classical
  obtain ⟨N, hN⟩ := evidence_stabilizes O hwf h hh xs
  refine ⟨N, hN, fun i ↦ ?_⟩
  rw [← hN (N + i + 1) (by omega)]
  apply decoded_agrees O hsep
  change (xs i, h (xs i)) ∈ (historyAt h xs (N + i + 1)).toFinset
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩

end FiniteEvidence

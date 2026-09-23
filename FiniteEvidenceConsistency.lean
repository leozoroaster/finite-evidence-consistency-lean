import FiniteEvidence.Converse
import FiniteEvidence.Minimum
import FiniteEvidence.Stabilization

namespace FiniteEvidence
universe u
variable {X : Type u}

/-- The finite-evidence characterization for arbitrary domains and target classes. -/
theorem finiteEvidence_characterization (H : Set (Hypothesis X)) :
    Consistent H ↔
      ∃ O : EvidenceOrder H, ConflictSeparating O ∧ TargetWellFounded O := by
  constructor
  · exact consistent_implies_order
  · rintro ⟨O, hsep, hwf⟩
    exact order_implies_consistent O hsep hwf

/-- The literal relation formulation: the only witness is a strict linear
order; its minimum map is derived from finiteness, not assumed. -/
theorem finiteEvidence_characterization_relation (H : Set (Hypothesis X)) :
    Consistent H ↔
      ∃ (r : Trace H → Trace H → Prop) (hr : IsStrictTotalOrder (Trace H) r),
        (∀ p q, Conflict p q → selectedMinimum r hr p ≠ selectedMinimum r hr q) ∧
        ∀ h ∈ H, WellFounded (fun p q : TraceOf H h ↦ r p.1 q.1) := by
  rw [finiteEvidence_characterization]
  constructor
  · rintro ⟨O, hsep, hwf⟩
    refine ⟨O.lt, O.strictTotal, ?_, hwf⟩
    intro p q hconf
    simpa only [← select_eq_selectedMinimum] using hsep p q hconf
  · rintro ⟨r, hr, hsep, hwf⟩
    exact ⟨evidenceOrderFromRelation r hr, hsep, hwf⟩

end FiniteEvidence

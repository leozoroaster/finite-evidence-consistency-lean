import FiniteEvidence.Core
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic

namespace FiniteEvidence
universe u
variable {X : Type u} {H : Set (Hypothesis X)}

/-- Every strict linear order has a unique least subtrace, including when the
least element is the empty trace. No well-foundedness assumption is needed. -/
theorem exists_leastSubtrace (r : Trace H → Trace H → Prop)
    (hr : IsStrictTotalOrder (Trace H) r) (p : Trace H) :
    ∃ s : Trace H, s.1 ⊆ p.1 ∧ ∀ t : Trace H, t.1 ⊆ p.1 → ¬ r t s := by
  classical
  letI := hr
  let S : Set (Trace H) := {s | s.1 ⊆ p.1}
  have hfin : S.Finite := Set.Finite.of_injOn
    (f := Subtype.val) (t := (p.1.powerset : Set (Finset (Example X))))
    (fun _ hs ↦ Finset.mem_powerset.mpr hs)
    Subtype.val_injective.injOn p.1.powerset.finite_toSet
  have hwf : S.WellFoundedOn r := hfin.wellFoundedOn
  obtain ⟨s, _, hmin⟩ := hwf.has_min Set.univ ⟨⟨p, Finset.Subset.refl _⟩, Set.mem_univ _⟩
  exact ⟨s.1, s.2, fun t ht ↦ hmin ⟨t, ht⟩ (Set.mem_univ _)⟩

noncomputable def selectedMinimum (r : Trace H → Trace H → Prop)
    (hr : IsStrictTotalOrder (Trace H) r) (p : Trace H) : Trace H :=
  Classical.choose (exists_leastSubtrace r hr p)

theorem selectedMinimum_spec (r : Trace H → Trace H → Prop)
    (hr : IsStrictTotalOrder (Trace H) r) (p : Trace H) :
    (selectedMinimum r hr p).1 ⊆ p.1 ∧
      ∀ t : Trace H, t.1 ⊆ p.1 → ¬ r t (selectedMinimum r hr p) :=
  Classical.choose_spec (exists_leastSubtrace r hr p)

noncomputable def evidenceOrderFromRelation (r : Trace H → Trace H → Prop)
    (hr : IsStrictTotalOrder (Trace H) r) : EvidenceOrder H where
  lt := r
  strictTotal := hr
  select := selectedMinimum r hr
  select_subset p := (selectedMinimum_spec r hr p).1
  select_least p := (selectedMinimum_spec r hr p).2

theorem select_eq_selectedMinimum (O : EvidenceOrder H) (p : Trace H) :
    O.select p = selectedMinimum O.lt O.strictTotal p := by
  exact O.strictTotal.trichotomous _ _
    ((selectedMinimum_spec O.lt O.strictTotal p).2 _ (O.select_subset p))
    (O.select_least p _ (selectedMinimum_spec O.lt O.strictTotal p).1)

/-- Deleting unselected evidence preserves the selected minimum. -/
theorem select_stable {O : EvidenceOrder H} {p q : Trace H}
    (hpq : (O.select p).1 ⊆ q.1) (hqp : q.1 ⊆ p.1) : O.select q = O.select p := by
  exact O.strictTotal.trichotomous _ _
    (O.select_least p _ (fun _ he ↦ hqp (O.select_subset q he)))
    (O.select_least q _ hpq)

end FiniteEvidence

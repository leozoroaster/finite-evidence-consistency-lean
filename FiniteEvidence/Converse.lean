import FiniteEvidence.MistakeTree
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Shortlex

namespace FiniteEvidence
universe u
variable {X : Type u} {H : Set (Hypothesis X)}
noncomputable section
local instance : DecidableEq X := Classical.decEq X

variable (r : Example X → Example X → Prop) [IsWellOrder (Example X) r]

/-- The increasing enumeration in the fixed alphabet order. -/
def increasingTrace (p : Trace H) : History X :=
  letI := IsWellOrder.linearOrder r
  p.1.sort (· ≤ ·)

theorem increasingTrace_finset (p : Trace H) : (increasingTrace r p).toFinset = p.1 := by
  letI := IsWellOrder.linearOrder r
  exact Finset.sort_toFinset p.1 (· ≤ ·)

theorem increasingTrace_length (p : Trace H) : (increasingTrace r p).length = p.1.card := by
  letI := IsWellOrder.linearOrder r
  exact Finset.length_sort (· ≤ ·)

theorem increasingTrace_injective : Function.Injective (increasingTrace r (H := H)) := by
  intro p q heq
  apply Subtype.ext
  simpa only [increasingTrace_finset] using congrArg List.toFinset heq

/-- Cardinality first, then lexicographic order of the increasing enumerations. -/
def traceTie (p q : Trace H) : Prop :=
  List.Shortlex r (increasingTrace r p) (increasingTrace r q)

instance traceTie_wellOrder : IsWellOrder (Trace H) (traceTie r) where
  wf := InvImage.wf (increasingTrace r) (List.Shortlex.wf (IsWellFounded.wf (r := r)))
  trichotomous _ _ hpq hqp := increasingTrace_injective r
    (Std.Trichotomous.trichotomous _ _ hpq hqp)

theorem traceTie_of_ssubset {p q : Trace H} (hpq : p.1 ⊂ q.1) : traceTie r p q := by
  apply List.Shortlex.of_length_lt
  simpa only [increasingTrace_length] using Finset.card_lt_card hpq

theorem traceTie_not_of_subset {p q : Trace H} (hpq : p.1 ⊆ q.1) : ¬ traceTie r q p := by
  by_cases heq : p = q
  · subst q
    exact irrefl_of (traceTie r) p
  · exact asymm_of (traceTie r) (traceTie_of_ssubset r
      (Finset.ssubset_iff_subset_ne.mpr ⟨hpq, fun h ↦ heq (Subtype.ext h)⟩))

variable (A : Learner X) (hA : Remembers H A)

/-- Lexicographic combination of transcript order and the inclusion-refining tie-break. -/
def converseLt (p q : Trace H) : Prop :=
  Prod.Lex (KB r) (traceTie r)
    (transcript A r hA p, p) (transcript A r hA q, q)

instance converseLt_strictTotal : IsStrictTotalOrder (Trace H) (converseLt r A hA) := by
  change IsStrictTotalOrder (Trace H)
    (InvImage (Prod.Lex (KB r) (traceTie r)) (fun p ↦ (transcript A r hA p, p)))
  letI : Std.Trichotomous
      (InvImage (Prod.Lex (KB r) (traceTie r)) (fun p : Trace H ↦ (transcript A r hA p, p))) :=
    InvImage.trichotomous (fun _ _ heq ↦ congrArg Prod.snd heq)
  exact { }

theorem transcriptTrace_least (p s : Trace H) (hsp : s.1 ⊆ p.1) :
    ¬ converseLt r A hA s (transcriptTrace A r hA p) := by
  intro hlt
  rw [converseLt, Prod.lex_def, transcript_idempotent] at hlt
  rcases hlt with hprimary | ⟨heq, htie⟩
  · rcases transcript_comparison A r hA hsp with heq | hrev
    · rw [heq] at hprimary
      exact irrefl_of (KB r) _ hprimary
    · exact asymm_of (KB r) hprimary hrev
  · have hsub : (transcriptTrace A r hA p).1 ⊆ s.1 := by
      change transcript A r hA s = transcript A r hA p at heq
      change (transcript A r hA p).toFinset ⊆ s.1
      rw [← heq]
      exact transcript_subset A r hA s
    exact traceTie_not_of_subset r hsub htie

def orderOfLearner : EvidenceOrder H where
  lt := converseLt r A hA
  strictTotal := inferInstance
  select := transcriptTrace A r hA
  select_subset := transcriptTrace_subset A r hA
  select_least := transcriptTrace_least r A hA

theorem orderOfLearner_separating : ConflictSeparating (orderOfLearner r A hA) := by
  intro p q hconf hsame
  have hT : transcript A r hA p = transcript A r hA q := by
    rw [← transcript_idempotent A r hA p, ← transcript_idempotent A r hA q]
    exact congrArg (transcript A r hA) hsame
  have hp := transcript_terminal A r hA p
  have hq := transcript_terminal A r hA q
  rw [← hT] at hq
  obtain ⟨x, hcase | hcase⟩ := hconf
  · exact Bool.false_ne_true ((hp _ hcase.1).symm.trans (hq _ hcase.2))
  · exact Bool.false_ne_true ((hq _ hcase.2).symm.trans (hp _ hcase.1))

theorem orderOfLearner_targetWellFounded
    (hcons : ∀ h ∈ H, ∀ xs : ℕ → X, (MistakeSet A h xs).Finite) :
    TargetWellFounded (orderOfLearner r A hA) := by
  intro h hh
  let W : Set (History X) := {τ | MistakeHistory A h τ}
  let f : TraceOf H h → W × Trace H := fun p ↦
    (⟨transcript A r hA p.1, transcript_in_mistakeTree A r hA p.1 p.2⟩, p.1)
  have hkb : WellFounded (fun s t : W ↦ KB r s.1 t.1) :=
    kb_wellFounded (mistakeHistory_prefix_closed A h) (mistakeHistory_noBranch (hcons h hh))
  have hwf := InvImage.wf f (hkb.prod_lex (IsWellFounded.wf (r := traceTie r)))
  apply hwf.mono
  intro p q hpq
  change converseLt r A hA p.1 q.1 at hpq
  rw [converseLt, Prod.lex_def] at hpq
  apply Prod.lex_def.mpr
  rcases hpq with hlt | ⟨heq, htie⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨Subtype.ext heq, htie⟩

theorem consistent_implies_order (hH : Consistent H) :
    ∃ O : EvidenceOrder H, ConflictSeparating O ∧ TargetWellFounded O := by
  obtain ⟨A, hA⟩ := hH
  let r : Example X → Example X → Prop := WellOrderingRel
  exact ⟨orderOfLearner r (normalize A) (normalize_remembers A),
    orderOfLearner_separating r (normalize A) (normalize_remembers A),
    orderOfLearner_targetWellFounded r (normalize A) (normalize_remembers A)
      (normalize_consistent hA)⟩

end
end FiniteEvidence

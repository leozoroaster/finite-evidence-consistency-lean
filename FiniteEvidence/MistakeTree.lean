import FiniteEvidence.Canonical

namespace FiniteEvidence
universe u
variable {X : Type u}

/-- Every example in this history has the target label and was a mistake. -/
def MistakeHistory (A : Learner X) (h : Hypothesis X) (τ : History X) : Prop :=
  ∀ σ e ρ, τ = σ ++ e :: ρ → InGraph h e ∧ A σ e.1 ≠ e.2

theorem mistakeHistory_prefix_closed (A : Learner X) (h : Hypothesis X) :
    PrefixClosed {τ | MistakeHistory A h τ} := by
  rintro s t ⟨rest, rfl⟩ ht σ e ρ rfl
  apply ht σ e (ρ ++ rest)
  simp [List.append_assoc]

theorem mistakeHistory_noBranch {A : Learner X} {h : Hypothesis X}
    (hA : ∀ xs : ℕ → X, (MistakeSet A h xs).Finite) :
    NoBranch {τ | MistakeHistory A h τ} := by
  rintro ⟨w, hw⟩
  have he (n : ℕ) : InGraph h (w n) ∧ A ((List.range n).map w) (w n).1 ≠ (w n).2 := by
    apply hw (n + 1) ((List.range n).map w) (w n) []
    simp [List.range_succ]
  let xs : ℕ → X := fun n ↦ (w n).1
  have hhist (n : ℕ) : historyAt h xs n = (List.range n).map w := by
    apply List.map_congr_left
    intro i _
    exact Prod.ext rfl (he i).1.symm
  have hmist (n : ℕ) : n ∈ MistakeSet A h xs := by
    change A (historyAt h xs n) (xs n) ≠ h (xs n)
    rw [hhist]
    exact fun heq ↦ (he n).2 (heq.trans (he n).1.symm)
  have hfinite : (Set.univ : Set ℕ).Finite := (hA xs).subset (fun n _ ↦ hmist n)
  exact Set.infinite_univ hfinite

theorem CanonicalRun.mistakes {A : Learner X} {r : Example X → Example X → Prop}
    {p : Finset (Example X)} {τ es : History X} (hrun : CanonicalRun A r p τ es)
    {h : Hypothesis X} (hp : IsTraceOf h p) :
    ∀ σ e ρ, es = σ ++ e :: ρ → InGraph h e ∧ A (τ ++ σ) e.1 ≠ e.2 := by
  induction hrun with
  | stop => simp
  | step τ f fs hf herr hmin rest ih =>
    intro σ e ρ heq
    cases σ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨hp _ hf, by simpa using herr⟩
    | cons a σ =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq⟩ := heq
      simpa [List.append_assoc] using ih σ e ρ heq

theorem transcript_in_mistakeTree {H : Set (Hypothesis X)}
    (A : Learner X) (r : Example X → Example X → Prop) [IsWellOrder (Example X) r]
    (hA : Remembers H A) (p : Trace H) {h : Hypothesis X} (hp : IsTraceOf h p.1) :
    MistakeHistory A h (transcript A r hA p) := by
  simpa [MistakeHistory] using (transcript_run A r hA p).mistakes hp

theorem target_transcripts_wellFounded {H : Set (Hypothesis X)}
    (A : Learner X) (r : Example X → Example X → Prop) [IsWellOrder (Example X) r]
    (hA : Remembers H A) {h : Hypothesis X}
    (hcons : ∀ xs : ℕ → X, (MistakeSet A h xs).Finite) :
    WellFounded (fun p q : TraceOf H h ↦
      KB r (transcript A r hA p.1) (transcript A r hA q.1)) := by
  let f : TraceOf H h → {τ | MistakeHistory A h τ} := fun p ↦
    ⟨transcript A r hA p.1, transcript_in_mistakeTree A r hA p.1 p.2⟩
  exact InvImage.wf f (kb_wellFounded (mistakeHistory_prefix_closed A h)
    (mistakeHistory_noBranch hcons))

end FiniteEvidence

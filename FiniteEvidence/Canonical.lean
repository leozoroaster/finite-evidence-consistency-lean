import FiniteEvidence.Core
import FiniteEvidence.KleeneBrouwer
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic

namespace FiniteEvidence
universe u
variable {X : Type u}

noncomputable section
local instance : DecidableEq X := Classical.decEq X

variable {H : Set (Hypothesis X)}

/-- Memory is required only on histories realizable by the class. -/
def Remembers (H : Set (Hypothesis X)) (A : Learner X) : Prop :=
  ∀ (τ : History X), IsRealizable H (by classical exact τ.toFinset) →
    ∀ e ∈ τ, A τ e.1 = e.2

theorem normalize_remembers (A : Learner X) : Remembers H (normalize A) := by
  classical
  intro τ hτ e he
  obtain ⟨h, _, hh⟩ := hτ
  apply normalize_seen A (hmem := he)
  intro c hc
  exact (hh _ (List.mem_toFinset.mpr hc)).trans
    (hh _ (List.mem_toFinset.mpr he)).symm

/-- A canonical continuation: repeatedly choose the least current mistake,
and stop precisely when the predictor agrees with the whole sample. -/
inductive CanonicalRun (A : Learner X) (r : Example X → Example X → Prop)
    (p : Finset (Example X)) : History X → History X → Prop
  | stop (τ) (h : ∀ e ∈ p, A τ e.1 = e.2) : CanonicalRun A r p τ []
  | step (τ e es) (he : e ∈ p) (herr : A τ e.1 ≠ e.2)
      (hmin : ∀ f ∈ p, A τ f.1 ≠ f.2 → ¬ r f e)
      (rest : CanonicalRun A r p (τ ++ [e]) es) : CanonicalRun A r p τ (e :: es)

namespace CanonicalRun

variable {A : Learner X} {r : Example X → Example X → Prop}
variable {p : Finset (Example X)} {τ es : History X}

theorem subset (hrun : CanonicalRun A r p τ es) : ∀ e ∈ es, e ∈ p := by
  induction hrun with
  | stop => simp
  | step τ e es he herr hmin rest ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact ih _ hf

theorem terminal (hrun : CanonicalRun A r p τ es) :
    ∀ e ∈ p, A (τ ++ es) e.1 = e.2 := by
  induction hrun with
  | stop τ h => simpa using h
  | step τ e es he herr hmin rest ih => simpa [List.append_assoc] using ih

theorem nodup (hrun : CanonicalRun A r p τ es) (hA : Remembers H A)
    (hp : IsRealizable H p) (hτ : ∀ e ∈ τ, e ∈ p) (hnd : τ.Nodup) :
    (τ ++ es).Nodup := by
  induction hrun with
  | stop => simpa using hnd
  | step τ e es he herr hmin rest ih =>
    have hreal : IsRealizable H τ.toFinset := by
      obtain ⟨h, hh, hg⟩ := hp
      exact ⟨h, hh, fun f hf ↦ hg f (hτ f (List.mem_toFinset.mp hf))⟩
    have hnew : e ∉ τ := fun hem ↦ herr (hA τ hreal e hem)
    have hsub : ∀ f ∈ τ ++ [e], f ∈ p := by
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hτ f hf
      · simpa only [List.mem_singleton.mp hf] using he
    have hnd' : (τ ++ [e]).Nodup := by
      simp only [List.nodup_append, List.nodup_singleton, true_and]
      exact ⟨hnd, fun a ha b hb ↦ by
        have hbe : b = e := List.mem_singleton.mp hb
        subst b
        exact fun hae ↦ hnew (hae ▸ ha)⟩
    simpa [List.append_assoc] using ih hsub hnd'

theorem exists_run [IsWellOrder (Example X) r] (hA : Remembers H A)
    (hp : IsRealizable H p) (τ : History X) (hτ : ∀ e ∈ τ, e ∈ p) :
    ∃ es, CanonicalRun A r p τ es := by
  classical
  by_cases hdone : ∀ e ∈ p, A τ e.1 = e.2
  · exact ⟨[], .stop τ hdone⟩
  · have hex : ∃ e ∈ p, A τ e.1 ≠ e.2 := by
      push Not at hdone
      exact hdone
    obtain ⟨e, he, hmin⟩ := (IsWellFounded.wf (r := r)).has_min
      {e | e ∈ p ∧ A τ e.1 ≠ e.2} hex
    have hreal : IsRealizable H τ.toFinset := by
      obtain ⟨h, hh, hgraph⟩ := hp
      exact ⟨h, hh, fun f hf ↦ hgraph f (hτ f (List.mem_toFinset.mp hf))⟩
    have hnew : e ∉ τ := fun hem ↦ he.2 (hA τ hreal e hem)
    have hτ' : ∀ f ∈ τ ++ [e], f ∈ p := by
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hτ f hf
      · have hfe := List.mem_singleton.mp hf
        exact hfe ▸ he.1
    obtain ⟨es, hrun⟩ := exists_run hA hp (τ ++ [e]) hτ'
    exact ⟨e :: es, .step τ e es he.1 he.2 (fun f hf herr ↦ hmin f ⟨hf, herr⟩) hrun⟩
termination_by p.card - τ.toFinset.card
decreasing_by
  have hc : τ.toFinset.card < p.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨fun f hf ↦ hτ f (List.mem_toFinset.mp hf), by
      intro hEq
      exact hnew (List.mem_toFinset.mp (hEq.symm ▸ he.1))⟩)
  simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
    Finset.union_insert, Finset.union_empty]
  rw [Finset.card_insert_of_notMem (by simpa using hnew)]
  omega

theorem unique [IsStrictTotalOrder (Example X) r]
    (hp : CanonicalRun A r p τ es) {fs : History X}
    (hq : CanonicalRun A r p τ fs) : es = fs := by
  induction hp generalizing fs with
  | stop τ hdone =>
    cases hq with
    | stop => rfl
    | step τ f fs hf herr => exact (herr (hdone f hf)).elim
  | step τ e es he herr hmin rest ih =>
    cases hq with
    | stop τ hdone => exact (herr (hdone e he)).elim
    | step τ f fs hf hferr hfmin frest =>
      have hef : e = f := Std.Trichotomous.trichotomous _ _
        (hfmin e he herr) (hmin f hf hferr)
      subst f
      exact congrArg (e :: ·) (ih frest)

theorem replay (hp : CanonicalRun A r p τ es) {q : Finset (Example X)}
    (heq : ∀ e ∈ es, e ∈ q) (hqp : q ⊆ p) : CanonicalRun A r q τ es := by
  induction hp with
  | stop τ hdone => exact .stop τ (fun e he ↦ hdone e (hqp he))
  | step τ e es he herr hmin rest ih =>
    exact .step τ e es (heq e (by simp)) herr
      (fun f hf hferr ↦ hmin f (hqp hf) hferr)
      (ih (fun f hf ↦ heq f (List.mem_cons_of_mem _ hf)))

theorem comparison [IsStrictTotalOrder (Example X) r]
    (hp : CanonicalRun A r p τ es) {q : Finset (Example X)} {fs : History X}
    (hq : CanonicalRun A r q τ fs) (hpq : p ⊆ q) : RelLE (KB r) fs es := by
  induction hp generalizing fs with
  | stop τ hdone =>
    cases fs with
    | nil => exact Or.inl rfl
    | cons f fs => exact Or.inr kb_nonempty_nil
  | step τ e es he herr hmin rest ih =>
    cases hq with
    | stop τ hdone => exact (herr (hdone e (hpq he))).elim
    | step τ f fs hf hferr hfmin frest =>
      by_cases hef : e = f
      · subst f
        rcases ih frest with heq | hlt
        · exact Or.inl (congrArg (e :: ·) heq)
        · exact Or.inr (kb_cons hlt)
      · have hfe : r f e := by
          by_contra hn
          exact hef (Std.Trichotomous.trichotomous e f (hfmin e (hpq he) herr) hn)
        exact Or.inr (kb_head hfe)

end CanonicalRun

variable (A : Learner X) (r : Example X → Example X → Prop)
variable [IsWellOrder (Example X) r] (hA : Remembers H A)

def transcript (p : Trace H) : History X :=
  Classical.choose (CanonicalRun.exists_run (r := r) hA p.2 [] (by simp))

theorem transcript_run (p : Trace H) : CanonicalRun A r p.1 [] (transcript A r hA p) :=
  Classical.choose_spec (CanonicalRun.exists_run (r := r) hA p.2 [] (by simp))

theorem transcript_subset (p : Trace H) : (transcript A r hA p).toFinset ⊆ p.1 := by
  intro e he
  exact (transcript_run A r hA p).subset e (List.mem_toFinset.mp he)

theorem transcript_nodup (p : Trace H) : (transcript A r hA p).Nodup := by
  simpa using (transcript_run A r hA p).nodup hA p.2 (by simp) (by simp)

theorem transcript_length_le (p : Trace H) : (transcript A r hA p).length ≤ p.1.card := by
  rw [← List.toFinset_card_of_nodup (transcript_nodup A r hA p)]
  exact Finset.card_le_card (transcript_subset A r hA p)

theorem transcript_terminal (p : Trace H) :
    ∀ e ∈ p.1, A (transcript A r hA p) e.1 = e.2 := by
  simpa using (transcript_run A r hA p).terminal

theorem transcript_replay {p q : Trace H}
    (hpq : (transcript A r hA p).toFinset ⊆ q.1) (hqp : q.1 ⊆ p.1) :
    transcript A r hA q = transcript A r hA p :=
  (transcript_run A r hA q).unique
    ((transcript_run A r hA p).replay (fun _ he ↦ hpq (List.mem_toFinset.mpr he)) hqp)

theorem transcript_comparison {p q : Trace H} (hpq : p.1 ⊆ q.1) :
    RelLE (KB r) (transcript A r hA q) (transcript A r hA p) :=
  (transcript_run A r hA p).comparison (transcript_run A r hA q) hpq

def transcriptTrace (p : Trace H) : Trace H :=
  ⟨(transcript A r hA p).toFinset, by
    obtain ⟨h, hh, hp⟩ := p.2
    exact ⟨h, hh, fun e he ↦ hp e (transcript_subset A r hA p he)⟩⟩

theorem transcriptTrace_subset (p : Trace H) : (transcriptTrace A r hA p).1 ⊆ p.1 :=
  transcript_subset A r hA p

theorem transcript_idempotent (p : Trace H) :
    transcript A r hA (transcriptTrace A r hA p) = transcript A r hA p :=
  transcript_replay A r hA (Finset.Subset.refl _) (transcript_subset A r hA p)
end
end FiniteEvidence

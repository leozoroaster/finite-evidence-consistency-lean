import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.WellFounded

/-!
# Finite evidence and consistent inductive inference

Formalization of the definitions and main characterization in the immutable
paper snapshot.  `Bool` is the binary label type.
-/

universe u

namespace FiniteEvidence

variable {X : Type u}

section Descent

variable {α : Type*} {r : α → α → Prop}

def RelLE (r : α → α → Prop) (a b : α) : Prop := a = b ∨ r a b

theorem relLE_trans [IsTrans α r] {a b c : α} :
    RelLE r a b → RelLE r b c → RelLE r a c := by
  rintro (rfl | hab) (rfl | hbc)
  · exact Or.inl rfl
  · exact Or.inr hbc
  · exact Or.inr hab
  · exact Or.inr (IsTrans.trans a b c hab hbc)

theorem relLE_of_steps [IsTrans α r] (s : ℕ → α)
    (hstep : ∀ n, RelLE r (s (n + 1)) (s n)) {i j : ℕ} (hij : i ≤ j) :
    RelLE r (s j) (s i) := by
  induction j, hij using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ j _ ih => exact relLE_trans (hstep j) ih

noncomputable def infiniteEnum (s : Set ℕ) (hs : s.Infinite) : ℕ → ℕ
  | 0 => Classical.choose hs.nonempty
  | n + 1 => Classical.choose (hs.exists_gt (infiniteEnum s hs n))

theorem infiniteEnum_mem (s : Set ℕ) (hs : s.Infinite) (n : ℕ) :
    infiniteEnum s hs n ∈ s := by
  cases n with
  | zero => exact (Classical.choose_spec hs.nonempty)
  | succ n => exact (Classical.choose_spec (hs.exists_gt (infiniteEnum s hs n))).1

theorem infiniteEnum_lt_succ (s : Set ℕ) (hs : s.Infinite) (n : ℕ) :
    infiniteEnum s hs n < infiniteEnum s hs (n + 1) :=
  (Classical.choose_spec (hs.exists_gt (infiniteEnum s hs n))).2

/-- A well-founded strict order admits only finitely many strict drops in a
pointwise nonincreasing sequence. -/
theorem finite_strictDrops [IsStrictOrder α r] (hwf : WellFounded r) (s : ℕ → α)
    (hstep : ∀ n, RelLE r (s (n + 1)) (s n)) :
    Set.Finite {n | r (s (n + 1)) (s n)} := by
  by_contra hinf
  have hInf : Set.Infinite {n | r (s (n + 1)) (s n)} := hinf
  let e := infiniteEnum {n | r (s (n + 1)) (s n)} hInf
  have he_drop (n : ℕ) : r (s (e n + 1)) (s (e n)) := infiniteEnum_mem _ hInf n
  have he_lt (n : ℕ) : e n < e (n + 1) := infiniteEnum_lt_succ _ hInf n
  have hdesc (n : ℕ) : r (s (e (n + 1))) (s (e n)) := by
    have hle : RelLE r (s (e (n + 1))) (s (e n + 1)) :=
      relLE_of_steps s hstep (Nat.succ_le_iff.mpr (he_lt n))
    rcases hle with heq | hlt
    · simpa [heq] using he_drop n
    · exact IsTrans.trans _ _ _ hlt (he_drop n)
  exact (RelEmbedding.natGT (fun n ↦ s (e n)) hdesc).not_wellFounded hwf

end Descent

abbrev Example (X : Type u) := X × Bool
abbrev History (X : Type u) := List (Example X)
abbrev Learner (X : Type u) := History X → X → Bool
abbrev Hypothesis (X : Type u) := X → Bool

def historyAt (h : Hypothesis X) (xs : ℕ → X) (n : ℕ) : History X :=
  (List.range n).map fun i ↦ (xs i, h (xs i))

def MistakeSet (A : Learner X) (h : Hypothesis X) (xs : ℕ → X) : Set ℕ :=
  {n | A (historyAt h xs n) (xs n) ≠ h (xs n)}

/-- One learner works for every fixed target and every input sequence. -/
def Consistent (H : Set (Hypothesis X)) : Prop :=
  ∃ A : Learner X, ∀ h ∈ H, ∀ xs : ℕ → X, (MistakeSet A h xs).Finite

def InGraph (h : Hypothesis X) (e : Example X) : Prop := e.2 = h e.1

def IsTraceOf (h : Hypothesis X) (p : Finset (Example X)) : Prop :=
  ∀ e ∈ p, InGraph h e

def IsRealizable (H : Set (Hypothesis X)) (p : Finset (Example X)) : Prop :=
  ∃ h ∈ H, IsTraceOf h p

abbrev Trace (H : Set (Hypothesis X)) :=
  {p : Finset (Example X) // IsRealizable H p}

def TraceOf (H : Set (Hypothesis X)) (h : Hypothesis X) :=
  {p : Trace H // IsTraceOf h p.1}

def Conflict {H : Set (Hypothesis X)} (p q : Trace H) : Prop :=
  ∃ x : X, ((x, false) ∈ p.1 ∧ (x, true) ∈ q.1) ∨
    ((x, true) ∈ p.1 ∧ (x, false) ∈ q.1)

/-- A strict linear order together with its (uniquely determined) least-subtrace map. -/
structure EvidenceOrder (H : Set (Hypothesis X)) where
  lt : Trace H → Trace H → Prop
  strictTotal : IsStrictTotalOrder (Trace H) lt
  select : Trace H → Trace H
  select_subset : ∀ p, (select p).1 ⊆ p.1
  select_least : ∀ p s, s.1 ⊆ p.1 → ¬ lt s (select p)

def ConflictSeparating {H : Set (Hypothesis X)} (O : EvidenceOrder H) : Prop :=
  ∀ p q, Conflict p q → O.select p ≠ O.select q

def TargetWellFounded {H : Set (Hypothesis X)} (O : EvidenceOrder H) : Prop :=
  ∀ h ∈ H, WellFounded (fun p q : TraceOf H h ↦ O.lt p.1 q.1)

section OrderToLearner

variable {H : Set (Hypothesis X)} (O : EvidenceOrder H)
noncomputable local instance : DecidableEq X := Classical.decEq X

/-- The fixed predictor decoded from a selected trace. -/
noncomputable def decoded (r : Trace H) (x : X) : Bool :=
  by
    classical
    exact if ∃ p : Trace H, O.select p = r ∧ (x, true) ∈ p.1 then true else false

theorem decoded_agrees (hsep : ConflictSeparating O) {p : Trace H} {x : X} {b : Bool}
    (hmem : (x, b) ∈ p.1) :
    decoded O (O.select p) x = b := by
  classical
  cases b with
  | false =>
      rw [decoded]
      split_ifs with hex
      · obtain ⟨q, hq, hqx⟩ := hex
        have hpq : Conflict p q := ⟨x, Or.inl ⟨hmem, hqx⟩⟩
        exact (hsep p q hpq hq.symm).elim
      · rfl
  | true =>
      rw [decoded]
      split_ifs with hex
      · rfl
      · exact (hex ⟨p, rfl, hmem⟩).elim

/-- The learner induced by the selected-evidence decoder. -/
noncomputable def learnerOfOrder : Learner X := fun τ x ↦
  by
    classical
    exact if hp : IsRealizable H τ.toFinset then
      decoded O (O.select ⟨τ.toFinset, hp⟩) x
    else false

theorem historyAt_isTraceOf (h : Hypothesis X) (xs : ℕ → X) (n : ℕ) :
    IsTraceOf h (historyAt h xs n).toFinset := by
  classical
  intro e he
  rw [List.mem_toFinset] at he
  simp only [historyAt, List.mem_map, List.mem_range] at he
  obtain ⟨i, _, rfl⟩ := he
  rfl

noncomputable def observedTrace (h : Hypothesis X) (hh : h ∈ H)
    (xs : ℕ → X) (n : ℕ) : Trace H := by
  classical
  exact ⟨(historyAt h xs n).toFinset, h, hh, historyAt_isTraceOf h xs n⟩

theorem observedTrace_subset_succ (h : Hypothesis X) (hh : h ∈ H)
    (xs : ℕ → X) (n : ℕ) :
    (observedTrace h hh xs n).1 ⊆ (observedTrace h hh xs (n + 1)).1 := by
  classical
  intro e he
  change e ∈ (historyAt h xs n).toFinset at he
  change e ∈ (historyAt h xs (n + 1)).toFinset
  rw [List.mem_toFinset] at he ⊢
  simp only [historyAt, List.mem_map, List.mem_range] at he ⊢
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

theorem select_antitone {p q : Trace H} (hpq : p.1 ⊆ q.1) :
    RelLE O.lt (O.select q) (O.select p) := by
  classical
  have hnforward : ¬ O.lt (O.select p) (O.select q) :=
    O.select_least q (O.select p) (fun _ he ↦ hpq (O.select_subset p he))
  by_cases heq : O.select q = O.select p
  · exact Or.inl heq
  · right
    by_contra hnbackward
    exact heq (O.strictTotal.trichotomous _ _ hnbackward hnforward)

theorem learnerOfOrder_at (h : Hypothesis X) (hh : h ∈ H)
    (xs : ℕ → X) (n : ℕ) :
    learnerOfOrder O (historyAt h xs n) (xs n) =
      decoded O (O.select (observedTrace h hh xs n)) (xs n) := by
  classical
  simp only [learnerOfOrder]
  rw [dif_pos ⟨h, hh, historyAt_isTraceOf h xs n⟩]
  congr

theorem mistake_forces_descent (hsep : ConflictSeparating O)
    (h : Hypothesis X) (hh : h ∈ H) (xs : ℕ → X) (n : ℕ)
    (herr : learnerOfOrder O (historyAt h xs n) (xs n) ≠ h (xs n)) :
    O.lt (O.select (observedTrace h hh xs (n + 1)))
      (O.select (observedTrace h hh xs n)) := by
  rcases select_antitone O (observedTrace_subset_succ h hh xs n) with heq | hlt
  · exfalso
    apply herr
    rw [learnerOfOrder_at O h hh xs n]
    rw [← heq]
    apply decoded_agrees O hsep
    have hmem : (xs n, h (xs n)) ∈ (observedTrace h hh xs (n + 1)).1 := by
      classical
      change (xs n, h (xs n)) ∈ (historyAt h xs (n + 1)).toFinset
      rw [List.mem_toFinset]
      simp only [historyAt, List.mem_map, List.mem_range]
      exact ⟨n, Nat.lt_succ_self n, rfl⟩
    exact hmem
  · exact hlt

end OrderToLearner

theorem order_implies_consistent {H : Set (Hypothesis X)} (O : EvidenceOrder H)
    (hsep : ConflictSeparating O) (hwf : TargetWellFounded O) : Consistent H := by
  letI : IsStrictOrder (Trace H) O.lt := O.strictTotal.toIsStrictOrder
  refine ⟨learnerOfOrder O, ?_⟩
  intro h hh xs
  let s : ℕ → TraceOf H h := fun n ↦
    ⟨O.select (observedTrace h hh xs n), fun e he ↦
      historyAt_isTraceOf h xs n e (O.select_subset _ he)⟩
  let r : TraceOf H h → TraceOf H h → Prop := fun p q ↦ O.lt p.1 q.1
  letI : Std.Irrefl r := ⟨fun p ↦ O.strictTotal.irrefl p.1⟩
  letI : IsTrans (TraceOf H h) r :=
    ⟨fun p q t ↦ O.strictTotal.trans p.1 q.1 t.1⟩
  letI : IsStrictOrder (TraceOf H h) r := inferInstance
  have hstep (n : ℕ) : RelLE r (s (n + 1)) (s n) := by
    rcases select_antitone O (observedTrace_subset_succ h hh xs n) with heq | hlt
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hlt
  have hdrops : Set.Finite {n | r (s (n + 1)) (s n)} :=
    finite_strictDrops (hwf h hh) s hstep
  apply hdrops.subset
  intro n hn
  exact mistake_forces_descent O hsep h hh xs n hn

section Normalization

/-- Modify a learner to return an already observed label whenever available. -/
noncomputable def normalize (A : Learner X) : Learner X := fun τ x ↦ by
  classical
  exact if hs : ∃ b : Bool, (x, b) ∈ τ then Classical.choose hs else A τ x

theorem normalize_seen (A : Learner X) {τ : History X} {x : X} {b : Bool}
    (hunique : ∀ c, (x, c) ∈ τ → c = b) (hmem : (x, b) ∈ τ) :
    normalize A τ x = b := by
  classical
  unfold normalize
  by_cases hs : ∃ c, (x, c) ∈ τ
  · rw [dif_pos hs]
    exact hunique _ (Classical.choose_spec hs)
  · exact (hs ⟨b, hmem⟩).elim

theorem normalize_mistakes_subset (A : Learner X) (h : Hypothesis X) (xs : ℕ → X) :
    MistakeSet (normalize A) h xs ⊆ MistakeSet A h xs := by
  classical
  intro n hn
  simp only [MistakeSet, Set.mem_setOf_eq] at hn ⊢
  unfold normalize at hn
  by_cases hseen : ∃ b, (xs n, b) ∈ historyAt h xs n
  · exfalso
    rw [dif_pos hseen] at hn
    let b := Classical.choose hseen
    have hb : (xs n, b) ∈ historyAt h xs n := Classical.choose_spec hseen
    have hlabel : b = h (xs n) := by
      simp only [historyAt, List.mem_map, List.mem_range] at hb
      obtain ⟨i, _, hpair⟩ := hb
      have hx : xs i = xs n := congrArg Prod.fst hpair
      have hl : h (xs i) = b := congrArg Prod.snd hpair
      exact hl.symm.trans (congrArg h hx)
    exact hn (by simpa [b] using hlabel)
  · rw [dif_neg hseen] at hn
    exact hn

theorem normalize_consistent {H : Set (Hypothesis X)} {A : Learner X}
    (hA : ∀ h ∈ H, ∀ xs : ℕ → X, (MistakeSet A h xs).Finite) :
    ∀ h ∈ H, ∀ xs : ℕ → X, (MistakeSet (normalize A) h xs).Finite := by
  intro h hh xs
  exact (hA h hh xs).subset (normalize_mistakes_subset A h xs)

end Normalization

end FiniteEvidence

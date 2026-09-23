import Mathlib.Data.List.Lex
import Mathlib.Order.WellFounded
import Mathlib.Tactic

namespace FiniteEvidence
universe u
variable {α : Type u}

/-- Kleene--Brouwer order: extensions precede prefixes, and the first
unequal entries are compared in the alphabet order. -/
def KB (r : α → α → Prop) (s t : List α) : Prop :=
  List.Lex (Function.swap r) t s

instance kb_strictTotal (r : α → α → Prop) [IsStrictTotalOrder α r] :
    IsStrictTotalOrder (List α) (KB r) := by
  letI : IsStrictTotalOrder (List α) (List.Lex (Function.swap r)) :=
    { isStrictWeakOrder_of_isOrderConnected with }
  change IsStrictTotalOrder (List α) (Function.swap (List.Lex (Function.swap r)))
  infer_instance

theorem kb_cons {r : α → α → Prop} {a : α} {s t : List α}
    (h : KB r s t) : KB r (a :: s) (a :: t) := List.Lex.cons h

theorem kb_head {r : α → α → Prop} {a b : α} {s t : List α}
    (h : r a b) : KB r (a :: s) (b :: t) := List.Lex.rel h

theorem kb_nonempty_nil {r : α → α → Prop} {a : α} {s : List α} :
    KB r (a :: s) [] := List.Lex.nil

theorem kb_append_left {r : α → α → Prop} {s t : List α}
    (h : KB r s t) (p : List α) : KB r (p ++ s) (p ++ t) :=
  List.Lex.append_left _ h p

theorem kb_append_left_iff {r : α → α → Prop} [Std.Irrefl r]
    {s t : List α} (p : List α) : KB r (p ++ s) (p ++ t) ↔ KB r s t := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change List.Lex (Function.swap r) (a :: (p ++ t)) (a :: (p ++ s)) ↔ _
    rw [List.lex_cons_iff]
    exact ih

/-- One-step extension, restricted to the tree. -/
def TreeChild (W : Set (List α)) (t s : List α) : Prop :=
  t ∈ W ∧ ∃ a, t = s ++ [a]

def PrefixClosed (W : Set (List α)) : Prop :=
  ∀ ⦃s t⦄, s <+: t → t ∈ W → s ∈ W

def NoBranch (W : Set (List α)) : Prop :=
  ¬ ∃ w : ℕ → α, ∀ n, (List.range n).map w ∈ W

/-- The branchless-tree hypothesis justifies induction from children to parents. -/
theorem tree_root_accessible {W : Set (List α)} (hclosed : PrefixClosed W)
    (hno : NoBranch W) :
    Acc (TreeChild W) [] := by
  classical
  by_contra hn
  obtain ⟨f, hf0, hf⟩ := not_acc_iff_exists_descending_chain.mp hn
  let w : ℕ → α := fun n ↦ Classical.choose (hf n).2
  have hstep (n : ℕ) : f (n + 1) = f n ++ [w n] :=
    Classical.choose_spec (hf n).2
  have heq (n : ℕ) : (List.range n).map w = f n := by
    induction n with
    | zero => simpa using hf0.symm
    | succ n ih => simpa [List.range_succ, ih] using (hstep n).symm
  apply hno
  refine ⟨w, fun n ↦ ?_⟩
  rw [heq n]
  cases n with
  | zero =>
    rw [hf0]
    exact hclosed List.nil_prefix (hf 0).1
  | succ n => exact (hf n).1

theorem kb_subtree_min {r : α → α → Prop} [IsWellOrder α r]
    {W : Set (List α)} (hclosed : PrefixClosed W) {p : List α}
    (hacc : Acc (TreeChild W) p) :
    ∀ S : Set (List α), S.Nonempty → S ⊆ W → (∀ s ∈ S, p <+: s) →
      ∃ s ∈ S, ∀ t ∈ S, ¬ KB r t s := by
  classical
  induction hacc with
  | intro p _ ih =>
    intro S hS hSW hpS
    by_cases hex : ∃ a ts, p ++ a :: ts ∈ S
    · let heads : Set α := {a | ∃ ts, p ++ a :: ts ∈ S}
      obtain ⟨a, ⟨ts, hts⟩, hmin⟩ := (IsWellFounded.wf (r := r)).has_min heads hex
      have hchild : TreeChild W (p ++ [a]) p := by
        refine ⟨hclosed ?_ (hSW hts), a, rfl⟩
        exact ⟨ts, by simp⟩
      let S' : Set (List α) := {s | s ∈ S ∧ p ++ [a] <+: s}
      have hS' : S'.Nonempty := ⟨p ++ a :: ts, hts, ⟨ts, by simp⟩⟩
      obtain ⟨s, hs, hleast⟩ := ih (p ++ [a]) hchild S' hS'
        (fun _ ht ↦ hSW ht.1) (fun _ ht ↦ ht.2)
      refine ⟨s, hs.1, fun t ht hlt ↦ ?_⟩
      obtain ⟨ss, hss⟩ := hs.2
      have hseq : s = p ++ a :: ss := by simpa using hss.symm
      obtain ⟨tt, htt⟩ := hpS t ht
      subst t
      rw [hseq, kb_append_left_iff] at hlt
      cases tt with
      | nil => cases hlt
      | cons b bs =>
        by_cases hba : b = a
        · subst b
          exact hleast _ ⟨ht, ⟨bs, by simp⟩⟩ (by
            rw [hseq, kb_append_left_iff]
            exact hlt)
        · cases hlt with
          | rel hrel => exact hmin b ⟨bs, ht⟩ hrel
          | cons _ => exact (hba rfl).elim
    · obtain ⟨s, hs⟩ := hS
      have heq : ∀ t ∈ S, t = p := by
        intro t ht
        obtain ⟨ts, hts⟩ := hpS t ht
        cases ts with
        | nil => simpa using hts.symm
        | cons a ts => exact (hex ⟨a, ts, hts ▸ ht⟩).elim
      refine ⟨s, hs, fun t ht hlt ↦ ?_⟩
      rw [heq s hs, heq t ht] at hlt
      exact irrefl_of (KB r) p hlt

/-- Kleene--Brouwer theorem for arbitrary well-ordered alphabets. -/
theorem kb_wellFounded {r : α → α → Prop} [IsWellOrder α r]
    {W : Set (List α)} (hclosed : PrefixClosed W) (hno : NoBranch W) :
    WellFounded (fun s t : W ↦ KB r s.1 t.1) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro S hS
  obtain ⟨s, hs, hmin⟩ := kb_subtree_min (r := r) hclosed
    (tree_root_accessible hclosed hno) (Subtype.val '' S) (hS.image _)
    (by rintro _ ⟨t, _, rfl⟩; exact t.2) (fun _ _ ↦ List.nil_prefix)
  obtain ⟨s, hs, rfl⟩ := hs
  exact ⟨s, hs, fun t ht ↦ hmin t.1 ⟨t, ht, rfl⟩⟩

end FiniteEvidence

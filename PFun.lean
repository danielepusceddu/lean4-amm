import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

structure PFun (α β: Type) where
  f: α → Option β
  supp: Finset α
  h: ∀ (a: α), a ∈ supp ↔ f a ≠ none

infixr:25 " ⇀ " => PFun

namespace PFun
open BigOperators

def fh {α β: Type} (f: α ⇀ β) (a:α) (h:a ∈ f.supp): β :=
  match m:f.f a with
  | some b => b
  | none => nomatch ((by 
      have h' := f.h a
      rw [h'] at h; contradiction): False)

def empty {α β: Type}: PFun α β :=
  ⟨λ _ => none,
   ∅,
   by intro a; apply Iff.intro
      . intro ainempty; contradiction
      . intro contra; contradiction
  ⟩

def update {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β): α ⇀ β :=
  ⟨λ a => if a=k then some v else f.f a,
   insert k f.supp,
   by intro a; have ind := f.h a; apply Iff.intro
      -- Prove f a ≠ none given a ∈ new supp
      . intro aininsert
        apply @Decidable.byCases (a=k)
        -- case a=k: we immediately see f a is not none. -/
        . intro aeqk; simp [aeqk]
        -- case a≠k: prove a ∈ old supp and use ind
        . intro aneqk; simp [aneqk]
          have ainsupp: a ∈ f.supp := 
            Finset.mem_of_mem_insert_of_ne aininsert aneqk
          rewrite [ind] at ainsupp
          exact ainsupp
      -- Prove a ∈ new supp given f a ≠ none
      . apply @Decidable.byCases (a=k)
        -- Trivial when a=k
        . intro eq; simp [eq]
        -- a≠k: use ind
        . intro neq; simp [neq, ind];
  ⟩

lemma update_of_self {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β)
  : (f.update k v).f k = some v := by simp [update]

lemma update_of_diff {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β) (k': α) (h: k≠k')
  : (f.update k v).f k' = f.f k' := by 
  simp [update]; intro contra; symm at contra; contradiction

lemma in_updated {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β) (k': α) (hin: k'∈f.supp)
  : k' ∈ (f.update k v).supp := by
  simp [update]; right; exact hin

lemma update_fh_of_diff {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β) (k': α) (hneq: k≠k') (hin: k'∈f.supp)
  : (f.update k v).fh k' (in_updated f k v k' hin) = f.fh k' hin := by 
  simp [fh]; split; next b m =>
    split; next b' m' =>
      rw [update_of_diff f k v k' hneq] at m
      simp [m] at m';  exact m'
    next contra => aesop
  aesop

lemma self_in_updated {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β)
  : k ∈ (f.update k v).supp := by simp [update]

lemma self_in_updated' {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β) (k': α) (heq: k = k')
  : k' ∈ (f.update k v).supp := by 
  simp [update]; left; symm; exact heq

lemma update_fh_of_self {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β)
  : (f.update k v).fh k (self_in_updated f k v) = v := by 
  simp [fh]; split; next v v' heq =>
    simp [update_of_self f k v] at heq; symm; exact heq
  next contra => aesop

/-
example update_fh_of_self_test' {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β) (k': α) (heq: k = k') (hin': k' ∈ (f.update k v).supp)
  : (f.update k v).fh k' hin' = v := by
  have hin: k ∈ (f.update k v).supp := by rw [← heq] at hin'; exact hin'
-/ 

lemma update_fh_of_self' {α β: Type} [DecidableEq α]
  (f: α ⇀ β) (k: α) (v: β) (k': α) (heq: k = k')
  : (f.update k v).fh k' (self_in_updated' f k v k' heq) = v := by 
  simp [fh]; split; next v v' heq' =>
    rw [heq] at heq'
    simp [update_of_self f k' v] at heq'; symm; exact heq'
  next contra => aesop

lemma psum_helper {α β: Type} {f: α ⇀ β} (a: α) (h: a ∈ f.supp.val): (f.f a ≠ none) := 
  by rewrite [← Finset.mem_def] at h; 
     rw [f.h a] at h; exact h

def sum {α β γ: Type} [CommMonoid γ]
  (f: α ⇀ β) (val: β → γ): γ := 
  let wrapper := λ (a: α) (h: f.f a ≠ none) => 
    val (f.fh a (by rw [f.h a]; exact h))
  (Multiset.pmap wrapper f.supp.val psum_helper).prod


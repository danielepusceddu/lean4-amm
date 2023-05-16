import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic.LibrarySearch

lemma Finsupp.update_undo {α β: Type} [e: DecidableEq α] [e2: Zero β]
  (f: α →₀ β) (k: α) (v: β):
  (f.update k v).update k (f k) = f := by ext; simp

lemma Finsupp.update_is_zero {α β: Type} [e: DecidableEq α] [e2: Zero β]
  (f: α →₀ β) (k: α) (v: β) (h2: f.update k v = 0):
  f = single k (f k) := by
  rw [← Finsupp.update_undo f k v]
  rw [h2]
  simp

def Finset.in_erase {α: Type} [DecidableEq α]
  (s: Finset α) (x: α) (y: α)
  : Prop := y ∈ s.erase x

def Finset.in_erase.decidablePred {α: Type} [DecidableEq α]
  (s: Finset α) (x: α)
  : DecidablePred (s.in_erase x) :=
  λ (y: α) => by unfold Finset.in_erase; infer_instance

def Finset.other {α: Type} [DecidableEq α]
  (s: Finset α) (c: s.card = 2)
  (x: α) (hin: x ∈ s): α :=
  @Finset.choose α (s.in_erase x) (in_erase.decidablePred s x) s (by
  unfold in_erase
  have sing: (s.erase x).card = 1 := by 
    rw [Finset.card_erase_of_mem hin]; simp [c]
  have ⟨y, hy⟩: ∃y, (s.erase x) = {y} := by
    rw [← Finset.card_eq_one]; exact sing
  have sAsInsert: insert x (s.erase x) = s :=
    Finset.insert_erase hin
  have yInErase: y ∈ s.erase x := by aesop
  have ⟨yNeqX, yInS⟩ := Finset.mem_erase.mp yInErase; 
  exists y; simp;
  simp

  apply And.intro
  . apply And.intro
    . exact yInS
    . apply And.intro
      . exact yNeqX
      . exact yInS
  . intro _ _ _ _
    aesop
  )

def Finset.other_in {α: Type} [DecidableEq α]
  (s: Finset α) (c: s.card = 2)
  (x: α) (hin: x ∈ s):
  Finset.other s c x hin ∈ s := by
  unfold other in_erase
  have help := @Finset.choose_mem α
  aesop

theorem Finset.other_diff {α: Type} [DecidableEq α]
  (s: Finset α) (c: s.card = 2)
  (x: α) (hin: x ∈ s):
  Finset.other s c x hin ≠ x := by
  have otherInErase: (Finset.other s c x hin) ∈ (s.erase x)
  := @Finset.choose_property _ _ (in_erase.decidablePred s x) _ _
  exact Finset.ne_of_mem_erase otherInErase
  
lemma Finset.pigeon {α: Type} [DecidableEq α]
  (s: Finset α) (hcard: s.card = 2)
  (a b c: α) 
  (ha: a ∈ s) (hb: b ∈ s) (hc: c ∈ s)
  (hab: a ≠ b) (hbc: b ≠ c): a = c
  := by
  apply Decidable.by_contradiction; intro contra
  
  have aInErase: a ∈ s.erase c :=
    Finset.mem_erase_of_ne_of_mem contra ha

  have bInErase: b ∈ s.erase c :=
    Finset.mem_erase_of_ne_of_mem hbc hb

  have aInEraseErase: a ∈ (s.erase c).erase b :=
    Finset.mem_erase_of_ne_of_mem hab aInErase

  have cardOfErase: (erase s c).card = 1 :=
    by simp [hc, hcard]

  have cardOfEraseErase: ((erase s c).erase b).card = 0 :=
    by rw [Finset.card_erase_of_mem bInErase]
       rw [cardOfErase];

  have eraseEraseIsSingleton: ((erase s c).erase b) = ∅ := 
    (Finset.card_eq_zero).mp cardOfEraseErase

  rw [eraseEraseIsSingleton] at aInEraseErase
  contradiction

/- we have
   x, other x, other other x
   we know all are in s
   we know x ≠ other x
   therefore we can use Finset.pigeon
-/
theorem Finset.other_inv {α: Type} [DecidableEq α]
  (s: Finset α) (c: s.card = 2)
  (x: α) (hin: x ∈ s):
  Finset.other s c (Finset.other s c x hin) (Finset.other_in _ _ _ _)
  =
  x := 
  (Finset.pigeon s c x (Finset.other s c x hin) (Finset.other s c (Finset.other s c x hin) (Finset.other_in _ _ _ _)) hin (Finset.other_in _ _ _ _) (Finset.other_in _ _ _ _) ((Finset.other_diff _ _ _ _).symm) ((Finset.other_diff _ _ _ _).symm)).symm
  

lemma Or.exclude_left {p q: Prop} (or: p ∨ q) (neg: ¬p)
  : q := by aesop

theorem or_eq_contra {α: Type} [DecidableEq α] (a b c: α) (h1: a=b ∨ a=c) (h2: (Decidable.decide (a=b)) = false) (h3: Decidable.decide (a=c) = false): False := by
  rcases h1 with hb|hc
  . have contra: ¬ a=b := of_decide_eq_false h2
    contradiction
  . have contra: ¬ a=c := of_decide_eq_false h3
    contradiction

theorem Sym2.notDiag_imp_diff (x y: α) (h: ¬Sym2.IsDiag ⟦(x, y)⟧): x ≠ y := by
  simp
  rw [← Sym2.mk''_isDiag_iff]
  exact h

def GT.gt.ne (x y: ℝ) (h: x > y): x ≠ y
  := Ne.symm (LT.lt.ne (GT.gt.lt h))

theorem mul_inv_self_R (x: ℝ) (h: x ≠ 0): x*x⁻¹ = 1 := by
  rewrite [← div_eq_mul_inv]
  rewrite [div_self]
  rfl
  apply h

theorem sub_eq_add_neg' : ∀ (x y: ℝ), x - y = x + -y := by
  intro x y
  change (x + -y = x + -y) 
  rfl

theorem pos_of_nonneg_neq_zero (x: ℝ) (h1: x ≠ 0) (h2: 0 ≤ x): 0 < x :=
  by exact Ne.lt_of_le (id (Ne.symm h1)) h2


theorem option_imply {α: Type} (o: Option α) (h: o ≠ none): ∃a, o = some a := by
  cases o with
  | none => contradiction
  | some a' => exists a'

theorem option_imply' {α: Type} (o: Option α) (h: ∃a, o = some a): o ≠ none := by
  let ⟨a,ah⟩ := h
  rw [ah]
  simp

def δ {α β: Type} (f: α → Option β) (a: α) (h: f a ≠ none): β
  := match m:f a with
  | some b => b
  | none => by contradiction

def δ_def {α β: Type} (f: α → Option β) (a: α) (b: β) (h: f a = some b): 
δ f a (option_imply' (f a) (⟨b,h⟩)) = b 
:= by unfold δ; split;
      next h1 h2 => simp [h] at h2; symm; trivial
      next h1 => simp [h] at h1
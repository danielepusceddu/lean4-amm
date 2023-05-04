import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.LibrarySearch

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
import Mathlib.Algebra.Group.Prod
import Mathlib.Logic.Embedding.Basic

theorem Prod.neq_zero_iff
{α β: Type} [Zero α] [Zero β] (p: α×β):
p ≠ 0 ↔ p.fst ≠ 0 ∨ p.snd ≠ 0 := by
  have bruh := (@Prod.mk_eq_zero _ _ _ _ p.fst p.snd).not
  simp only [not_and_or] at bruh
  exact bruh

@[simp] theorem Prod.swap_eq_zero
{α β: Type} [Zero α] [Zero β] (p: α×β):
p.swap = (0: β×α) ↔ p = (0: α×β) := by
  apply Iff.intro
  . intro swap0
    rw [← Prod.swap_swap p]
    simp [swap0]
  . intro p0
    simp [p0]

@[simp] theorem Prod.swap_ne_zero
{α β: Type} [Zero α] [Zero β] (p: α×β):
p.swap ≠ (0: β×α) ↔ p ≠ (0: α×β) := by
  apply Iff.intro
  . simp
  . simp

/- Product swaps as an embedding 
   (which are just a structure containing a function
    and a proof that it is injective)-/
def Prod.swap_emb {α β: Type}: α × β ↪ β × α :=
  ⟨Prod.swap, Prod.swap_injective⟩

/- Prod.swap_emb coerced to a function is the same as Prod -/
lemma Prod.swap_emb_coe {α β: Type}
: (Prod.swap_emb: (α × β → β × α)) = Prod.swap := by
  unfold swap_emb; simp
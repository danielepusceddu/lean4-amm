import AMMLib.Deposit
import AMMLib.State
import AMMLib.Tokens
import AMMLib.Swap.Basic
import AMMLib.Networth

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from Γ init and using configuration c -/
inductive Tx (o: 𝕆) (sx: SX) (init: Γ): Γ → Type where
  | empty: Tx o sx init init

  | dep0 (s': Γ) (rs: Tx o sx init s') (d: Deposit0 s'): 
      Tx o sx init d.apply

  | swap (s': Γ) (rs: Tx o sx init s') 
         (sw: Swap sx o s' a t0 t1 v0):
      Tx o sx init sw.apply

def reachableInit (s: Γ): Prop :=
  (s.amms = 𝕊ₐ.empty ∧ s.mints = 𝕊₁.empty)

def reachable (o: 𝕆) (sx: SX) (s: Γ): Prop :=
  ∃ (init: Γ) (tx: Tx o sx init s), reachableInit init

def concat {o: 𝕆} {sx: SX} {init s' s'': Γ} 
(t1: Tx o sx init s') (t2: Tx o sx s' s''): Tx o sx init s'' := match t2 with
  | Tx.empty => t1
  | Tx.dep0 ds rs d => Tx.dep0 ds (concat t1 rs) d
  | Tx.swap ds rs sw => Tx.swap ds (concat t1 rs) sw

/-
Proof that 
m ∈ (Trace c s).Γ.amms.map.supp → supply m > 0

by induction
empty (base case): hypothesis is a contradiction
dep0: trivial by cases on the deposited tokens:
      if the pair is the same, then the supply is positive.
      if the pair isn't the same, the supply is the same as
      before and we can use IH.
swap: use IH. 
      swaps don't change minted token supplies
-/
theorem Γ.mintsupply_samepair (s: Γ) (t0 t1 t0' t1': 𝕋) (samepair: samemint t0 t1 t0' t1'):
  s.mintsupply t0 t1 = s.mintsupply t0' t1' := by sorry

theorem AMMimpSupplyProp
{o: 𝕆} {sx: SX} {s: Γ} (r: reachable o sx s) {t0 t1: 𝕋}
(h: s.amms.init t0 t1)
: 0 < s.mintsupply t0 t1 := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [𝕊ₐ.init, 𝕊ₐ.empty, init_amms] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases (diffmint d.t0 d.t1 t0 t1)
    . intro diff;
      simp [diff] at h
      simp [Deposit0.apply, Γ.mintsupply, diff]
      have re: reachable o sx sprev := by
        exists init; exists tail
      exact ih re h
    
    . intro same
      rw [not_diffmint_iff_samemint _ _ _ _ d.hdif] at same
      rw [← Γ.mintsupply_samepair _ _ _ _ _ same]
      simp [Γ.mintsupply, Deposit0.apply]
      right
      exact d.r0.zero_lt_toNNReal
  
  | swap sprev tail sw ih =>
      rw [sw.mintsupply]
      simp at h
      have re: reachable o sx sprev := by
        exists init; exists tail
      exact ih re h

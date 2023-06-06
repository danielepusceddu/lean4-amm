import AMMLib.Deposit
import AMMLib.State
import AMMLib.Tokens
import AMMLib.Swap.Basic
import AMMLib.Price
import AMMLib.Networth

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from Γ init and using configuration c -/
inductive Tx (c: Cfg) (init: Γ): Γ → Type where
  | empty: Tx c init init

  | dep0 (s': Γ) (rs: Tx c init s') (d: Deposit0 s'): 
      Tx c init d.apply

  | swap (s': Γ) (rs: Tx c init s') (sw: Swap c s'):
      Tx c init sw.apply

def reachableInit (s: Γ): Prop :=
  (s.amms = 𝕊ₐ.empty ∧ ∀ (a: 𝔸) (m: 𝕋₁), s.mints a m = 0)

def reachable (c: Cfg) (s: Γ): Prop :=
  ∃ (init: Γ) (tx: Tx c init s), reachableInit init

def concat {c: Cfg} {init s' s'': Γ} 
(t1: Tx c init s') (t2: Tx c s' s''): Tx c init s'' := match t2 with
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

theorem AMMimpSupplyProp
{c: Cfg} {s: Γ} (r: reachable c s) {t0 t1: 𝕋₀}
(h: s.amms.f t0 t1 ≠ 0)
: 0 < s.mintsupply (𝕋₀.toMint (𝕊ₐ.exists_imp_dif h)) := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [init_amms, 𝕊ₐ.empty] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases ((𝕋₀.toMint (𝕊ₐ.exists_imp_dif h))=(𝕋₀.toMint d.hdif))
    . intro eq; rw [eq]
      simp [Deposit0.apply, Γ.mintsupply, eq]
      left
      exact d.r0.coe_pos
    
    . intro neq
      simp [neq]
      simp [𝕋₀.toMint_diff neq] at h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h
  
  | swap sprev tail sw ih =>
      rw [Swap.mintedSupply]
      have h' := Swap.amm_in_apply h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h'
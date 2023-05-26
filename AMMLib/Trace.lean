import AMMLib.Deposit
import AMMLib.State
import AMMLib.Tokens
import AMMLib.Swap
import AMMLib.Price

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from state init and using configuration c -/
inductive Tx (c: Config) (init: State): State → Type where
  | empty: Tx c init init

  | dep0 (s': State) (rs: Tx c init s') (d: Deposit0 s'): 
      Tx c init d.apply

  | swap (s': State) (rs: Tx c init s') (sw: Swap c s'):
      Tx c init sw.apply

def reachableInit (s: State): Prop :=
  (s.amms = AMMSet.empty ∧ ∀ (a: Account) (m: MintedTok), s.accs a m = 0)

def reachable (c: Config) (s: State): Prop :=
  ∃ (init: State) (tx: Tx c init s), reachableInit init

structure Reachable (c: Config) (s: State) where
  init: State
  tx: Tx c init s
  init_amms: init.amms = AMMSet.empty
  init_accs: ∀ (a: Account) (m: MintedTok), init.accs a m = 0

def concat {c: Config} {init s' s'': State} 
(t1: Tx c init s') (t2: Tx c s' s''): Tx c init s'' := match t2 with
  | Tx.empty => t1
  | Tx.dep0 ds rs d => Tx.dep0 ds (concat t1 rs) d
  | Tx.swap ds rs sw => Tx.swap ds (concat t1 rs) sw

/-
Proof that 
m ∈ (Trace c s).state.amms.map.supp → supply m > 0

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
{c: Config} {s: State} (r: reachable c s) {t0 t1: AtomicTok}
(h: s.amms.f t0 t1 ≠ 0)
: 0 < s.mintsupply (AtomicTok.toMint (AMMSet.exists_imp_dif h)) := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [init_amms, AMMSet.empty] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases ((AtomicTok.toMint (AMMSet.exists_imp_dif h))=(AtomicTok.toMint d.hdif))
    . intro eq; rw [eq]
      simp [Deposit0.apply, State.mintsupply, eq]
      left
      exact d.r0.coe_pos
    
    . intro neq
      simp [neq]
      simp [AtomicTok.toMint_diff neq] at h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h
  
  | swap sprev tail sw ih =>
      rw [Swap.mintedSupply]
      have h' := Swap.amm_in_apply h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h'

noncomputable def State.mintedPrice 
{s: State} {c: Config} (r: reachable c s)
(m: MintedTok) (h: s.amms.f m.choose m.other ≠ 0)
: ℝ+ :=
s.mintedTokPrice c m h (by have h' := AMMimpSupplyProp r h; simp at h'; exact h')

noncomputable def State.price 
  {s: State} {c: Config} (r: reachable c s) (t: Token)
  (h: if hm: t.isMinted then 
      s.amms.f (t.getMinted hm).choose (t.getMinted hm).other ≠ 0 else True)
: PReal :=
  match t with
  | Token.Atomic t' => c.o t'
  | Token.Minted m => mintedPrice r m (by simp [Token.isMinted] at h; exact h)
